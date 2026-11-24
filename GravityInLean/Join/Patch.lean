/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.SameSpacetime
public import GravityInLean.Join.Setting
public import GravityInLean.Join.NewTime
public import GravityInLean.Join.UsableSlope

import Mathlib.Tactic

/-!
# Birkhoff's theorem on a small patch around a point of the equator

Board item `task:join-patch`. Take a table `h` of sixteen functions on an open set `W` of
coordinate space, around a point `y₀` with the angles `(π / 2, 0)` of the equator point. Let `h`
be smooth, symmetric, unchanged by the three standard turns, empty, with one time direction and
with spheres of positive size, and let the size of the spheres be a usable distance at `y₀`. Then
on a smaller open set `W'` around `y₀` the table is Schwarzschild's table, for some mass `m`,
written in other coordinates `Θ`: new time and the radius of the spheres in place of time and
distance, the two angles as they are.

The steps:

* `exists_box_subset`: an open set around `y₀` contains a box of the kind of `ShapeBox.lean`;
* on that box the table has the general round shape (`shape_of_round_box`) and its four functions
  are in the setting of the general theorem (`setting_of_box`);
* the size of the spheres is a usable distance at `y₀` (`sizeSlopeOf_ne_zero_of_usable`), hence,
  being continuous, on a smaller box (`exists_intervals_of_eventually`);
* there the general theorem with smooth new labels (`birkhoff_general_smooth`) gives the mass and
  the new time;
* from lengths of steps to the entries of the table: `eq_of_stepLength_eq`.

That the new labels really are coordinates (the determinant of their table of slopes is not zero)
is not computed: the table `h` has an inverse, and it is `Jᵀ · G · J` for the table of slopes
`J`, so `J` cannot have determinant zero.
-/

@[expose] public section

namespace GravityInLean.Join

open Real Filter Topology Set

open scoped ContDiff

/-- A point with the two angles of the equator point is the equator point of its time and
distance. -/
theorem onEquator_self {y₀ : Coords 4} (h2 : y₀ 2 = π / 2) (h3 : y₀ 3 = 0) :
    onEquator (y₀ 0) (y₀ 1) = y₀ := by
  funext k
  fin_cases k <;> simp [onEquator, h2, h3]

/-- An open set around a point with the angles of the equator point contains a box around it:
open stretches of time and distance in one piece, and both angles closer than some `δ` to those
of the equator point. -/
theorem exists_box_subset {W : Set (Coords 4)} {y₀ : Coords 4} (hW : IsOpen W) (hy₀ : y₀ ∈ W)
    (h2 : y₀ 2 = π / 2) (h3 : y₀ 3 = 0) :
    ∃ (J I : Set ℝ) (δ : ℝ), IsOpen J ∧ IsPreconnected J ∧ IsOpen I ∧ IsPreconnected I ∧
      y₀ 0 ∈ J ∧ y₀ 1 ∈ I ∧ 0 < δ ∧ δ < π / 2 ∧ ∀ y, InBox J I δ y → y ∈ W := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW y₀ hy₀
  have hπ := Real.pi_pos
  have hδ : 0 < min ε (π / 4) := lt_min hε (by positivity)
  have hδε : min ε (π / 4) ≤ ε := min_le_left _ _
  have hδπ : min ε (π / 4) ≤ π / 4 := min_le_right _ _
  refine ⟨Ioo (y₀ 0 - min ε (π / 4)) (y₀ 0 + min ε (π / 4)),
    Ioo (y₀ 1 - min ε (π / 4)) (y₀ 1 + min ε (π / 4)), min ε (π / 4),
    isOpen_Ioo, isPreconnected_Ioo, isOpen_Ioo, isPreconnected_Ioo,
    ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, hδ, by linarith, fun y hy => hball ?_⟩
  obtain ⟨hy0, hy1, hy2, hy3⟩ := hy
  rw [abs_lt] at hy2 hy3
  have k0 : dist (y 0) (y₀ 0) < ε := by
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [hy0.1], by linarith [hy0.2]⟩
  have k1 : dist (y 1) (y₀ 1) < ε := by
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [hy1.1], by linarith [hy1.2]⟩
  have k2 : dist (y 2) (y₀ 2) < ε := by
    rw [Real.dist_eq, abs_lt, h2]
    exact ⟨by linarith [hy2.1], by linarith [hy2.2]⟩
  have k3 : dist (y 3) (y₀ 3) < ε := by
    rw [Real.dist_eq, abs_lt, h3]
    exact ⟨by linarith [hy3.1], by linarith [hy3.2]⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro i
  fin_cases i
  · exact k0
  · exact k1
  · exact k2
  · exact k3

/-- What holds near a pair of a time and a distance holds on a product of two open stretches, each
in one piece, around them. -/
theorem exists_intervals_of_eventually {P : ℝ × ℝ → Prop} {t₀ ρ₀ : ℝ}
    (h : ∀ᶠ q in 𝓝 (t₀, ρ₀), P q) :
    ∃ J I : Set ℝ, IsOpen J ∧ IsPreconnected J ∧ IsOpen I ∧ IsPreconnected I ∧ t₀ ∈ J ∧ ρ₀ ∈ I ∧
      ∀ t ∈ J, ∀ ρ ∈ I, P (t, ρ) := by
  obtain ⟨ε, hε, hP⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨Ioo (t₀ - ε) (t₀ + ε), Ioo (ρ₀ - ε) (ρ₀ + ε), isOpen_Ioo, isPreconnected_Ioo,
    isOpen_Ioo, isPreconnected_Ioo, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
    fun t ht ρ hρ => hP ?_⟩
  have e : dist (t, ρ) (t₀, ρ₀) = max (dist t t₀) (dist ρ ρ₀) := Prod.dist_eq
  rw [e, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt]
  exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ⟨by linarith [hρ.1], by linarith [hρ.2]⟩⟩

/-- New labels for time and distance that are smooth functions of time and distance give a smooth
map of coordinate space. -/
theorem contDiffOn_relabel {T R : ℝ → ℝ → ℝ} {J I : Set ℝ} {W' : Set (Coords 4)}
    (hT : ContDiffOn ℝ ∞ (Function.uncurry T) (J ×ˢ I))
    (hR : ContDiffOn ℝ ∞ (Function.uncurry R) (J ×ˢ I))
    (hW' : ∀ x ∈ W', x 0 ∈ J ∧ x 1 ∈ I) : ContDiffOn ℝ ∞ (relabel T R) W' := by
  have hpair : ContDiffOn ℝ ∞ (fun x : Coords 4 => (x 0, x 1)) W' :=
    ((contDiff_apply ℝ (fun _ : Fin 4 => ℝ) 0).prodMk
      (contDiff_apply ℝ (fun _ : Fin 4 => ℝ) 1)).contDiffOn
  have hmaps : MapsTo (fun x : Coords 4 => (x 0, x 1)) W' (J ×ˢ I) :=
    fun x hx => ⟨(hW' x hx).1, (hW' x hx).2⟩
  have h0 : ContDiffOn ℝ ∞ (fun x : Coords 4 => T (x 0) (x 1)) W' := hT.comp hpair hmaps
  have h1 : ContDiffOn ℝ ∞ (fun x : Coords 4 => R (x 0) (x 1)) W' := hR.comp hpair hmaps
  have h2 : ContDiffOn ℝ ∞ (fun x : Coords 4 => x 2) W' :=
    (contDiff_apply ℝ (fun _ : Fin 4 => ℝ) 2).contDiffOn
  have h3 : ContDiffOn ℝ ∞ (fun x : Coords 4 => x 3) W' :=
    (contDiff_apply ℝ (fun _ : Fin 4 => ℝ) 3).contDiffOn
  refine contDiffOn_pi.2 fun i => ?_
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- **Birkhoff's theorem on a patch.** A table on an open set around a point with the angles of
the equator point, that is smooth, symmetric, unchanged by the three turns, empty, with one time
direction and spheres of positive size, and for which the size of the spheres is a usable distance
at the point, is near the point Schwarzschild's table for some mass `m`, written in other
coordinates `Θ`. The other coordinates are smooth, they really are coordinates (the determinant of
their table of slopes is not zero), and they land off the rim, the centre and the poles. -/
theorem birkhoff_patch {h hinv : Fin 4 → Fin 4 → Coords 4 → ℝ} {W : Set (Coords 4)}
    {y₀ : Coords 4} (hW : IsOpen W) (hy₀ : y₀ ∈ W) (h2 : y₀ 2 = π / 2) (h3 : y₀ 3 = 0)
    (hsmooth : ∀ y ∈ W, ∀ i j, ContDiffAt ℝ ∞ (h i j) y)
    (hsymm : ∀ y ∈ W, ∀ i j, h i j y = h j i y)
    (hround : ∀ y ∈ W, IsRoundAt h y)
    (hinverse : ∀ y ∈ W, ∀ i k, ∑ j, h i j y * hinv j k y = if i = k then 1 else 0)
    (hflat : ∀ y ∈ W, IsRicciFlatAt h hinv y)
    (htime : ∀ y ∈ W, Curved.HasOneTimeDirection fun v w : Coords 4 ↦
      Curved.tableMeasure h y v w)
    (hpos : ∀ y ∈ W, 0 < h 2 2 y)
    (hu : Curved.UsableDistanceAt (Curved.flatMeasure (Curved.tableMeasure h)) Curved.turns y₀) :
    ∃ (m : ℝ) (Θ : Coords 4 → Coords 4) (W' : Set (Coords 4)), IsOpen W' ∧ y₀ ∈ W' ∧ W' ⊆ W ∧
      ContDiffOn ℝ ∞ Θ W' ∧ (∀ y ∈ W', (tab (jac Θ) y).det ≠ 0) ∧
      ∀ y ∈ W', (Θ y ∈ Curved.outside m ∨ Θ y ∈ Curved.inside m) ∧
        ∀ μ ν, h μ ν y = inNewCoords Θ (roundG (schwA m) (schwB m)) μ ν y := by
  have hy0 : onEquator (y₀ 0) (y₀ 1) = y₀ := onEquator_self h2 h3
  -- A first box inside `W`: the shape and the setting hold on it.
  obtain ⟨J₁, I₁, δ, hJ₁, hJ₁c, hI₁, hI₁c, ht₁, hρ₁, hδ, hδ', hbox⟩ :=
    exists_box_subset hW hy₀ h2 h3
  have hshape₁ := shape_of_round_box hδ hδ' (fun x hx => hsymm x (hbox x hx))
    (fun x hx i j => (hsmooth x (hbox x hx) i j).differentiableAt (by simp))
    (fun x hx => hround x (hbox x hx))
  obtain ⟨hset₁, -, hA₁, hB₁, hC₁, hS₁⟩ := setting_of_box (hinv := hinv) hJ₁ hJ₁c hI₁ hI₁c hδ hδ'
    (fun x hx => hsmooth x (hbox x hx)) (fun x hx => hsymm x (hbox x hx))
    (fun x hx => hround x (hbox x hx)) (fun x hx => hinverse x (hbox x hx))
    (fun x hx => hflat x (hbox x hx)) (fun x hx => htime x (hbox x hx))
    (fun x hx => hpos x (hbox x hx))
  -- The size of the spheres is a usable distance at `y₀`.
  have hy₀box : InBox J₁ I₁ δ y₀ := by
    have hb := inBox_onEquator (J := J₁) (I := I₁) hδ ht₁ hρ₁
    rwa [hy0] at hb
  have hnear : ∀ᶠ y in 𝓝 y₀, InBox J₁ I₁ δ y :=
    (isOpen_inBox hJ₁ hI₁ δ).mem_nhds hy₀box
  have hdet₀ : h 0 0 y₀ * h 1 1 y₀ - h 0 1 y₀ * h 0 1 y₀ ≠ 0 := by
    have hk := hset₁.spaceTime _ ht₁ _ hρ₁
    have e : det2 (clockOf h) (rulerOf h) (crossOf h) (y₀ 0) (y₀ 1)
        = -h 0 0 (onEquator (y₀ 0) (y₀ 1)) * h 1 1 (onEquator (y₀ 0) (y₀ 1))
          + h 0 1 (onEquator (y₀ 0) (y₀ 1)) * h 0 1 (onEquator (y₀ 0) (y₀ 1)) := rfl
    rw [e, hy0] at hk
    intro hzero
    linarith
  have hslope₀ : sizeSlopeOf h y₀ ≠ 0 :=
    sizeSlopeOf_ne_zero_of_usable (hnear.mono fun y hy => hshape₁ y hy) (hy₀box.sin_ne hδ')
      (hpos y₀ hy₀).ne' hdet₀ ((hsmooth y₀ hy₀ 2 2).differentiableAt (by simp)) hu
  have hn₀ : sizeSlopeSq (clockOf h) (rulerOf h) (crossOf h) (sizeOf h) (y₀ 0) (y₀ 1) ≠ 0 := by
    have e : sizeSlopeSq (clockOf h) (rulerOf h) (crossOf h) (sizeOf h) (y₀ 0) (y₀ 1)
        = sizeSlopeOf h (onEquator (y₀ 0) (y₀ 1)) := by
      simp only [sizeSlopeSq, sizeSlopeOf, slope_zero_onEquator, slope_one_onEquator]
      rfl
    rw [e, hy0]
    exact hslope₀
  -- It is continuous in time and distance, so it is usable on a smaller box.
  have hU₁ : IsOpen (J₁ ×ˢ I₁) := hJ₁.prod hI₁
  have dn : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ =>
      sizeSlopeSq (clockOf h) (rulerOf h) (crossOf h) (sizeOf h) q.1 q.2) (J₁ ×ˢ I₁) := by
    have dA : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => clockOf h q.1 q.2) (J₁ ×ˢ I₁) := hA₁
    have dB : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => rulerOf h q.1 q.2) (J₁ ×ˢ I₁) := hB₁
    have dC : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => crossOf h q.1 q.2) (J₁ ×ˢ I₁) := hC₁
    have dSt : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => dt (sizeOf h) q.1 q.2) (J₁ ×ˢ I₁) :=
      contDiffOn_dt hU₁ hS₁
    have dSr : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => dr (sizeOf h) q.1 q.2) (J₁ ×ˢ I₁) :=
      contDiffOn_dr hU₁ hS₁
    have d2 : ContDiffOn ℝ ∞ (fun _ : ℝ × ℝ => (2 : ℝ)) (J₁ ×ˢ I₁) := contDiffOn_const
    exact ((dA.mul (dSr.mul dSr)).add ((d2.mul dC).mul (dSt.mul dSr))).sub (dB.mul (dSt.mul dSt))
  have hq₀ : (y₀ 0, y₀ 1) ∈ J₁ ×ˢ I₁ := ⟨ht₁, hρ₁⟩
  have hev : ∀ᶠ q in 𝓝 (y₀ 0, y₀ 1), q ∈ J₁ ×ˢ I₁ ∧
      sizeSlopeSq (clockOf h) (rulerOf h) (crossOf h) (sizeOf h) q.1 q.2 ≠ 0 :=
    Filter.Eventually.and (hU₁.eventually_mem hq₀)
      ((dn.continuousOn.continuousAt (hU₁.mem_nhds hq₀)).eventually_ne hn₀)
  obtain ⟨J, I, hJ, hJc, hI, hIc, ht, hρ, hP⟩ := exists_intervals_of_eventually hev
  -- The smaller box: the shape, the setting, and the general theorem with smooth new labels.
  have hsub : ∀ y, InBox J I δ y → InBox J₁ I₁ δ y := fun y hy =>
    ⟨(hP _ hy.1 _ hy.2.1).1.1, (hP _ hy.1 _ hy.2.1).1.2, hy.2.2.1, hy.2.2.2⟩
  have hbox' : ∀ y, InBox J I δ y → y ∈ W := fun y hy => hbox y (hsub y hy)
  have hshape := shape_of_round_box hδ hδ' (fun x hx => hsymm x (hbox' x hx))
    (fun x hx i j => (hsmooth x (hbox' x hx) i j).differentiableAt (by simp))
    (fun x hx => hround x (hbox' x hx))
  obtain ⟨hset, hsize, hA, hB, hC, hS⟩ := setting_of_box (hinv := hinv) hJ hJc hI hIc hδ hδ'
    (fun x hx => hsmooth x (hbox' x hx)) (fun x hx => hsymm x (hbox' x hx))
    (fun x hx => hround x (hbox' x hx)) (fun x hx => hinverse x (hbox' x hx))
    (fun x hx => hflat x (hbox' x hx)) (fun x hx => htime x (hbox' x hx))
    (fun x hx => hpos x (hbox' x hx))
  have hn : ∀ t ∈ J, ∀ ρ ∈ I,
      sizeSlopeSq (clockOf h) (rulerOf h) (crossOf h) (sizeOf h) t ρ ≠ 0 :=
    fun t ht ρ hρ => (hP t ht ρ hρ).2
  obtain ⟨M, T, hTs, hRs, hall⟩ := birkhoff_general_smooth hset hA hB hC hS hsize hn
  have hy₀' : InBox J I δ y₀ := by
    have hb := inBox_onEquator (J := J) (I := I) hδ ht hρ
    rwa [hy0] at hb
  -- The entries of the table, from the lengths of steps.
  have hent : ∀ y, InBox J I δ y → ∀ μ ν, h μ ν y
      = inNewCoords (relabel T (radius (sizeOf h))) (roundG (schwA M) (schwB M)) μ ν y := by
    intro y hy
    obtain ⟨-, -, -, hlen⟩ := hall y hy.1 hy.2.1
    refine eq_of_stepLength_eq (hsymm y (hbox' y hy))
      (fun i j => inNewCoords_symm (fun α β => roundG_symm _ _ α β _) i j) (fun v => ?_)
    have e1 : stepLength h y v
        = stepLength (genG (clockOf h) (rulerOf h) (crossOf h) (sizeOf h)) y v := by
      simp only [stepLength, hshape y hy]
    rw [stepLength_inNewCoords, e1, hlen v]
    congr 1
    funext α
    exact relabelStep_eq_jac T (radius (sizeOf h)) y v α
  -- The new labels really are coordinates: the table has an inverse and is `Jᵀ · G · J`.
  have hdetJ : ∀ y, InBox J I δ y →
      (tab (jac (relabel T (radius (sizeOf h)))) y).det ≠ 0 := by
    intro y hy hzero
    have e : tab h y = Matrix.transpose (tab (jac (relabel T (radius (sizeOf h)))) y)
        * tab (roundG (schwA M) (schwB M)) (relabel T (radius (sizeOf h)) y)
        * tab (jac (relabel T (radius (sizeOf h)))) y := by
      rw [← tab_inNewCoords]
      ext μ ν
      exact hent y hy μ ν
    have hinvm : tab h y * tab hinv y = 1 := by
      ext i k
      rw [Matrix.mul_apply, Matrix.one_apply]
      exact hinverse y (hbox' y hy) i k
    have hne := Matrix.det_ne_zero_of_right_inverse hinvm
    rw [e, Matrix.det_mul, hzero, mul_zero] at hne
    exact hne rfl
  refine ⟨M, relabel T (radius (sizeOf h)), {x | InBox J I δ x}, isOpen_inBox hJ hI δ, hy₀',
    fun y hy => hbox' y hy, contDiffOn_relabel hTs hRs (fun x hx => ⟨hx.1, hx.2.1⟩),
    fun y hy => hdetJ y hy, fun y hy => ⟨?_, hent y hy⟩⟩
  -- Off the rim, the centre and the poles.
  have hy' : InBox J I δ y := hy
  obtain ⟨-, h2M, -, -⟩ := hall y hy'.1 hy'.2.1
  have hrpos : 0 < radius (sizeOf h) (y 0) (y 1) :=
    Real.sqrt_pos.mpr (hset.S_pos _ hy'.1 _ hy'.2.1)
  have hs : sin (y 2) ≠ 0 := hy'.sin_ne hδ'
  rcases lt_or_gt_of_ne h2M with hlt | hgt
  · left
    exact (show 0 < radius (sizeOf h) (y 0) (y 1) ∧ 2 * M < radius (sizeOf h) (y 0) (y 1)
      ∧ sin (y 2) ≠ 0 from ⟨hrpos, hlt, hs⟩)
  · right
    exact (show 0 < radius (sizeOf h) (y 0) (y 1) ∧ radius (sizeOf h) (y 0) (y 1) < 2 * M
      ∧ sin (y 2) ≠ 0 from ⟨hrpos, hgt, hs⟩)

end GravityInLean.Join
