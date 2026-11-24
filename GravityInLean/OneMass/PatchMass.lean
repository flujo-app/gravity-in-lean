/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Join.Patch

import Mathlib.Tactic

/-!
# Birkhoff's theorem on a patch, with the mass named

Board item `task:checks-mass-patch`. `birkhoff_patch` (`Join/Patch.lean`) gives some mass. Its
proof takes the mass from the mass function. This file proves the same theorem with that said:
the mass is the mass function of the table at the point.

The proof is the proof of `birkhoff_patch`, step for step, with the mass kept: the general
theorem with smooth new labels (`birkhoff_general_smooth`) says that the mass function equals
the mass at every point of the box, and the point `y₀` is one of them. `Join/Patch.lean` is not
to be changed, so its proof is repeated here; its helping lemmas are used as they are.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Mass

open GravityInLean.Curved GravityInLean.Join

open Real Filter Topology Set

open scoped ContDiff

/-- **Birkhoff's theorem on a patch, with the mass named.** As `birkhoff_patch`, and the mass is
the value of the table's mass function at the point `y₀`. -/
theorem birkhoff_patch_mass {h hinv : Fin 4 → Fin 4 → Coords 4 → ℝ} {W : Set (Coords 4)}
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
    ∃ (m : ℝ) (Θ : Coords 4 → Coords 4) (W' : Set (Coords 4)),
      m = massFn (clockOf h) (rulerOf h) (crossOf h) (sizeOf h) (y₀ 0) (y₀ 1) ∧
      IsOpen W' ∧ y₀ ∈ W' ∧ W' ⊆ W ∧
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
  -- The mass is the mass function at `y₀`: the general theorem says so at every point of the box.
  have hmass : M = massFn (clockOf h) (rulerOf h) (crossOf h) (sizeOf h) (y₀ 0) (y₀ 1) :=
    ((hall y₀ hy₀'.1 hy₀'.2.1).1).symm
  refine ⟨M, relabel T (radius (sizeOf h)), {x | InBox J I δ x}, hmass, isOpen_inBox hJ hI δ,
    hy₀', fun y hy => hbox' y hy, contDiffOn_relabel hTs hRs (fun x hx => ⟨hx.1, hx.2.1⟩),
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

end GravityInLean.Mass
