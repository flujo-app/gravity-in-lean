/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Rim.Core
public import GravityInLean.Rim.Table
public import GravityInLean.OneMass.PatchMass

import Mathlib.Tactic

/-!
# On a patch, a table of positive mass is Kruskal's

Board item `task:rim-patch`. The counterpart of `birkhoff_patch_mass` (`OneMass/PatchMass.lean`)
for a positive mass, with no usable distance assumed: a table on an open set around a point with
the angles of the equator point, that is smooth, symmetric, unchanged by the three turns, empty,
with one time direction and spheres of positive size, and whose mass function is `m > 0` at the
point, is near the point Kruskal's table of mass `m`, written in other coordinates `Θ`.

On paper: as in `birkhoff_patch` (`Join/Patch.lean`): a box, the round shape and the setting on
it (`shape_of_round_box`, `setting_of_box`); then `kruskal_core` (`Core.lean`) gives the two new
labels `T`, `X`; `Θ = relabel T X`; the entries of the table from the lengths of steps; the
determinant is not zero because the table has an inverse.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Rim

open GravityInLean.Curved GravityInLean.Join

open Real Filter Topology Set

open scoped ContDiff

/-- **A table of positive mass is Kruskal's, on a patch.** No usable distance is assumed: the
point may be on the rim. -/
theorem kruskal_patch {h hinv : Fin 4 → Fin 4 → Coords 4 → ℝ} {W : Set (Coords 4)}
    {y₀ : Coords 4} (hW : IsOpen W) (hy₀ : y₀ ∈ W) (h2 : y₀ 2 = π / 2) (h3 : y₀ 3 = 0)
    (hsmooth : ∀ y ∈ W, ∀ i j, ContDiffAt ℝ ∞ (h i j) y)
    (hsymm : ∀ y ∈ W, ∀ i j, h i j y = h j i y)
    (hround : ∀ y ∈ W, IsRoundAt h y)
    (hinverse : ∀ y ∈ W, ∀ i k, ∑ j, h i j y * hinv j k y = if i = k then 1 else 0)
    (hflat : ∀ y ∈ W, IsRicciFlatAt h hinv y)
    (htime : ∀ y ∈ W, Curved.HasOneTimeDirection fun v w : Coords 4 ↦
      Curved.tableMeasure h y v w)
    (hpos : ∀ y ∈ W, 0 < h 2 2 y) {m : ℝ}
    (hm : m = massFn (clockOf h) (rulerOf h) (crossOf h) (sizeOf h) (y₀ 0) (y₀ 1))
    (hmpos : 0 < m) :
    ∃ (Θ : Coords 4 → Coords 4) (W' : Set (Coords 4)),
      IsOpen W' ∧ y₀ ∈ W' ∧ W' ⊆ W ∧
      ContDiffOn ℝ ∞ Θ W' ∧ (∀ y ∈ W', (tab (jac Θ) y).det ≠ 0) ∧
      ∀ y ∈ W', Θ y ∈ Curved.kruskalRegion ∧
        ∀ μ ν, h μ ν y = inNewCoords Θ (Curved.kruskalG m) μ ν y := by
  have hy0 : onEquator (y₀ 0) (y₀ 1) = y₀ := onEquator_self h2 h3
  -- A first box inside `W`: the shape and the setting hold on it.
  obtain ⟨J₁, I₁, δ, hJ₁, hJ₁c, hI₁, hI₁c, ht₁, hρ₁, hδ, hδ', hbox⟩ :=
    exists_box_subset hW hy₀ h2 h3
  have hshape₁ := shape_of_round_box hδ hδ' (fun x hx => hsymm x (hbox x hx))
    (fun x hx i j => (hsmooth x (hbox x hx) i j).differentiableAt (by simp))
    (fun x hx => hround x (hbox x hx))
  obtain ⟨hset₁, -, hA₁, hB₁, hC₁, hS₁⟩ := setting_of_box (hinv := hinv) hJ₁ hJ₁c hI₁ hI₁c hδ
    hδ' (fun x hx => hsmooth x (hbox x hx)) (fun x hx => hsymm x (hbox x hx))
    (fun x hx => hround x (hbox x hx)) (fun x hx => hinverse x (hbox x hx))
    (fun x hx => hflat x (hbox x hx)) (fun x hx => htime x (hbox x hx))
    (fun x hx => hpos x (hbox x hx))
  -- Empty in the sense of the general round shape, at every angle off the poles: at the point
  -- of the equator with the same time and distance the table is the shape and is empty, and
  -- the four formulas for the curvature of the shape know only time and distance.
  have hE₁ : IsEmptyOnG (clockOf h) (rulerOf h) (crossOf h) (sizeOf h) J₁ I₁ := by
    intro x hx0 hx1 hxs
    have hx : InBox J₁ I₁ δ (onEquator (x 0) (x 1)) := inBox_onEquator hδ hx0 hx1
    have hnear : ∀ᶠ y in 𝓝 (onEquator (x 0) (x 1)), InBox J₁ I₁ δ y :=
      (isOpen_inBox hJ₁ hI₁ δ).mem_nhds hx
    have hg : ∀ i j, h i j
        =ᶠ[𝓝 (onEquator (x 0) (x 1))]
          genG (clockOf h) (rulerOf h) (crossOf h) (sizeOf h) i j :=
      fun i j => hnear.mono fun y hy => hshape₁ y hy i j
    have hgi : ∀ i j, hinv i j
        =ᶠ[𝓝 (onEquator (x 0) (x 1))]
          genGinv (clockOf h) (rulerOf h) (crossOf h) (sizeOf h) i j := by
      intro i j
      refine hnear.mono fun y hy => ?_
      have hu := inverse_unique (m := fun i j => h i j y) (a := fun i j => hinv i j y)
        (b := fun i j => genGinv (clockOf h) (rulerOf h) (crossOf h) (sizeOf h) i j y)
        (hinverse y (hbox y hy)) (fun i k => by
          simp only [hshape₁ y hy]
          exact genG_mul_genGinv (hset₁.spaceTime _ hy.1 _ hy.2.1).ne'
            (hset₁.S_pos _ hy.1 _ hy.2.1).ne' (hy.sin_ne hδ') i k)
      exact congrFun (congrFun hu i) j
    have hfl := (isRicciFlatAt_congr hg hgi).mp (hflat _ (hbox _ hx))
    have hreg := hset₁.regular (x := onEquator (x 0) (x 1)) hx0 hx1 (hx.sin_ne hδ')
    have hempty : IsEmptyG (clockOf h) (rulerOf h) (crossOf h) (sizeOf h) (x 0) (x 1) :=
      (gen_ricciFlat_iff hreg).mp hfl
    exact (gen_ricciFlat_iff (hset₁.regular hx0 hx1 hxs)).mpr hempty
  -- The core in two labels gives Kruskal's labels `T`, `X` near the point.
  obtain ⟨T, X, N, hN, h0N, hNsub, hTs, hXs, hall⟩ :=
    kruskal_core hset₁ hE₁ hA₁ hB₁ hC₁ hS₁ ht₁ hρ₁ hm hmpos
  -- A smaller box, inside the set on which the two labels are good.
  have hev : ∀ᶠ q in 𝓝 (y₀ 0, y₀ 1), q ∈ N := hN.eventually_mem h0N
  obtain ⟨J, I, hJ, -, hI, -, ht, hρ, hP⟩ := exists_intervals_of_eventually hev
  have hJI : J ×ˢ I ⊆ N := fun q hq => hP q.1 hq.1 q.2 hq.2
  have hsub : ∀ y, InBox J I δ y → InBox J₁ I₁ δ y := fun y hy =>
    ⟨(hNsub (hP _ hy.1 _ hy.2.1)).1, (hNsub (hP _ hy.1 _ hy.2.1)).2, hy.2.2.1, hy.2.2.2⟩
  have hbox' : ∀ y, InBox J I δ y → y ∈ W := fun y hy => hbox y (hsub y hy)
  have hy₀' : InBox J I δ y₀ := by
    have hb := inBox_onEquator (J := J) (I := I) hδ ht hρ
    rwa [hy0] at hb
  -- The entries of the table, from the lengths of steps.
  have hent : ∀ y, InBox J I δ y → ∀ μ ν, h μ ν y
      = inNewCoords (relabel T X) (Curved.kruskalG m) μ ν y := by
    intro y hy
    have hq : (y 0, y 1) ∈ N := hP _ hy.1 _ hy.2.1
    have hkS : kruskalS m (T (y 0) (y 1)) (X (y 0) (y 1)) = sizeOf h (y 0) (y 1) :=
      (hall _ hq).2.1
    have hAeq : clockOf h (y 0) (y 1) = kruskalA m (T (y 0) (y 1)) (X (y 0) (y 1))
        * (dt T (y 0) (y 1) ^ 2 - dt X (y 0) (y 1) ^ 2) := (hall _ hq).2.2.1
    have hCeq : crossOf h (y 0) (y 1) = kruskalA m (T (y 0) (y 1)) (X (y 0) (y 1))
        * (dt X (y 0) (y 1) * dr X (y 0) (y 1) - dt T (y 0) (y 1) * dr T (y 0) (y 1)) :=
      (hall _ hq).2.2.2.1
    have hBeq : rulerOf h (y 0) (y 1) = kruskalA m (T (y 0) (y 1)) (X (y 0) (y 1))
        * (dr X (y 0) (y 1) ^ 2 - dr T (y 0) (y 1) ^ 2) := (hall _ hq).2.2.2.2
    refine eq_of_stepLength_eq (hsymm y (hbox' y hy))
      (fun i j => inNewCoords_symm
        (fun α β => genG_symm (kruskalA m) (kruskalA m) zero2 (kruskalS m) α β _) i j)
      (fun v => ?_)
    have e1 : stepLength h y v
        = stepLength (genG (clockOf h) (rulerOf h) (crossOf h) (sizeOf h)) y v := by
      simp only [stepLength, hshape₁ y (hsub y hy)]
    have e2 : stepLength (Curved.kruskalG m) (relabel T X y) (relabelStep T X y v)
        = -kruskalA m (T (y 0) (y 1)) (X (y 0) (y 1))
            * (dt T (y 0) (y 1) * v 0 + dr T (y 0) (y 1) * v 1) ^ 2
          + kruskalA m (T (y 0) (y 1)) (X (y 0) (y 1))
            * (dt X (y 0) (y 1) * v 0 + dr X (y 0) (y 1) * v 1) ^ 2
          + sizeOf h (y 0) (y 1) * v 2 ^ 2 + sizeOf h (y 0) (y 1) * sin (y 2) ^ 2 * v 3 ^ 2 := by
      have ek : Curved.kruskalG m = genG (kruskalA m) (kruskalA m) zero2 (kruskalS m) := rfl
      have r0 : relabel T X y 0 = T (y 0) (y 1) := rfl
      have r1 : relabel T X y 1 = X (y 0) (y 1) := rfl
      have r2 : relabel T X y 2 = y 2 := rfl
      have s0 : relabelStep T X y v 0 = dt T (y 0) (y 1) * v 0 + dr T (y 0) (y 1) * v 1 := rfl
      have s1 : relabelStep T X y v 1 = dt X (y 0) (y 1) * v 0 + dr X (y 0) (y 1) * v 1 := rfl
      have s2 : relabelStep T X y v 2 = v 2 := rfl
      have s3 : relabelStep T X y v 3 = v 3 := rfl
      rw [ek, stepLength_gen, r0, r1, r2, s0, s1, s2, s3, hkS]
      simp only [zero2]
      ring
    have e3 : (fun α => ∑ μ, jac (relabel T X) α μ y * v μ) = relabelStep T X y v :=
      funext fun α => (relabelStep_eq_jac T X y v α).symm
    rw [stepLength_inNewCoords, e1, e3, e2, stepLength_gen, hAeq, hCeq, hBeq]
    ring
  -- The new labels really are coordinates: the table has an inverse and is `Jᵀ · G · J`.
  have hdetJ : ∀ y, InBox J I δ y → (tab (jac (relabel T X)) y).det ≠ 0 := by
    intro y hy hzero
    have e : tab h y = Matrix.transpose (tab (jac (relabel T X)) y)
        * tab (Curved.kruskalG m) (relabel T X y) * tab (jac (relabel T X)) y := by
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
  refine ⟨relabel T X, {x | InBox J I δ x}, isOpen_inBox hJ hI δ, hy₀',
    fun y hy => hbox' y hy,
    contDiffOn_relabel (hTs.mono hJI) (hXs.mono hJI) (fun x hx => ⟨hx.1, hx.2.1⟩),
    fun y hy => hdetJ y hy, fun y hy => ⟨?_, hent y hy⟩⟩
  -- In Kruskal's region: away from the centre and off the poles.
  have hy' : InBox J I δ y := hy
  have hq : (y 0, y 1) ∈ N := hP _ hy'.1 _ hy'.2.1
  exact (show -1 < X (y 0) (y 1) ^ 2 - T (y 0) (y 1) ^ 2 ∧ sin (y 2) ≠ 0 from
    ⟨(hall _ hq).1, hy'.sin_ne hδ'⟩)

end GravityInLean.Rim
