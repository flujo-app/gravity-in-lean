/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.Turns
public import GravityInLean.NewCoordinates
public import GravityInLean.Join.Mix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

import Mathlib.Tactic

/-!
# The table of functions in the coordinates that fit the turns

Board item `task:join-newtable` (part B, step 4 of the route to `birkhoffNoCoordinates`, second
half). `turnsCoordinates` gives new coordinates `Φ` on an open patch `W`. The table of functions
`g`, written in the new coordinates, is `inNewCoords Φ g`. `Mix.lean` shows that it looks the same
from every side. This file shows everything else that is needed about it, at every point `y` of
the patch:

* `tableMeasure_inNewCoords`: its length measure gives two steps the length that the old one
  gives to the two steps as `Φ` sees them;
* `newTable_smooth`, `newTable_symm`, `newTable_inverse`, `newTable_inverse_smooth`,
  `newTable_regular`: it is a good table on `W`, with the inverse table `invT`;
* `newTable_isRicciFlatAt`: it is empty where the old one is;
* `newTable_hasOneTimeDirection`: it has one time direction where the old one has;
* `newTable_pos_two_two`: its entry for the first angle is positive (the spheres have a
  positive size).

Only coordinates are used here; no curved spaces.
-/

@[expose] public section

namespace GravityInLean.Join

open Real Filter Topology Matrix

open scoped ContDiff

/-! ## Facts at one point, in any dimension -/

section Pointwise

variable {n : ℕ} {Φ : Coords n → Coords n} {g : Fin n → Fin n → Coords n → ℝ} {y : Coords n}

/-- The slope of a change of coordinates, applied to a step: part `α` of the result is the row
`α` of the table of slopes times the step. -/
theorem fderiv_apply_eq_sum_jac (hΦ : DifferentiableAt ℝ Φ y) (v : Coords n) (α : Fin n) :
    fderiv ℝ Φ y v α = ∑ μ, jac Φ α μ y * v μ := by
  have h := clm_apply_eq_sum
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) α).comp (fderiv ℝ Φ y)) v
  change fderiv ℝ Φ y v α = ∑ δ, v δ * fderiv ℝ Φ y (Pi.single δ 1) α at h
  rw [h]
  exact Finset.sum_congr rfl fun μ _ ↦ by rw [jac_eq_fderiv hΦ, mul_comm]

/-- The slope of a change of coordinates, applied to a step, is the table of slopes times the
step. -/
theorem fderiv_eq_mulVec (hΦ : DifferentiableAt ℝ Φ y) (v : Coords n) :
    fderiv ℝ Φ y v = (tab (jac Φ) y).mulVec v := by
  funext α
  rw [fderiv_apply_eq_sum_jac hΦ]
  rfl

/-- The new table measures two steps `v`, `w` the way the old table measures the two steps with
the parts `∑ μ, jac Φ α μ y * v μ` and `∑ ν, jac Φ β ν y * w ν`. (`length_inNewCoords` is the
case `v = w`.) -/
theorem bilin_inNewCoords (Φ : Coords n → Coords n) (g : Fin n → Fin n → Coords n → ℝ)
    (x v w : Coords n) :
    ∑ μ, ∑ ν, inNewCoords Φ g μ ν x * v μ * w ν
      = ∑ α, ∑ β, g α β (Φ x) * (∑ μ, jac Φ α μ x * v μ) * (∑ ν, jac Φ β ν x * w ν) := by
  have e1 : ∑ μ, ∑ ν, inNewCoords Φ g μ ν x * v μ * w ν
      = ∑ μ, ∑ ν, ∑ α, ∑ β, jac Φ α μ x * jac Φ β ν x * g α β (Φ x) * v μ * w ν := by
    simp only [inNewCoords, Finset.sum_mul]
  have e2 : ∑ α, ∑ β, g α β (Φ x) * (∑ μ, jac Φ α μ x * v μ) * (∑ ν, jac Φ β ν x * w ν)
      = ∑ α, ∑ β, ∑ μ, ∑ ν, g α β (Φ x) * (jac Φ α μ x * v μ) * (jac Φ β ν x * w ν) := by
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ν _ => by ring
  rw [e1, e2, sum4_swap]
  exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring

/-- **The length measure of the new table.** It gives two steps `v`, `w` at `y` the length that
the old table gives, at `Φ y`, to the two steps as the change of coordinates sees them. -/
theorem tableMeasure_inNewCoords (g : Fin n → Fin n → Coords n → ℝ)
    (hΦ : DifferentiableAt ℝ Φ y) (v w : Coords n) :
    Curved.tableMeasure (inNewCoords Φ g) y v w
      = Curved.tableMeasure g (Φ y) (fderiv ℝ Φ y v) (fderiv ℝ Φ y w) := by
  simp only [Curved.tableMeasure, Curved.formOf_apply, fderiv_apply_eq_sum_jac hΦ]
  exact bilin_inNewCoords Φ g y v w

/-- The table of slopes of a smooth change of coordinates is smooth. -/
theorem contDiffAt_jac_top (hΦ : ContDiffAt ℝ ∞ Φ y) (α κ : Fin n) :
    ContDiffAt ℝ ∞ (jac Φ α κ) y := by
  have hev : jac Φ α κ =ᶠ[𝓝 y] fun z ↦ fderiv ℝ Φ z (Pi.single κ 1) α :=
    ((hΦ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)).eventually (by simp)).mono fun z hz ↦
      jac_eq_fderiv (hz.differentiableAt (by simp)) α κ
  have hfd : ContDiffAt ℝ ∞ (fderiv ℝ Φ) y := hΦ.fderiv_right (m := ∞) ENat.coe_top_add_one.le
  have h1 : ContDiffAt ℝ ∞ (fun z ↦ fderiv ℝ Φ z (Pi.single κ 1)) y :=
    hfd.clm_apply contDiffAt_const
  exact ((contDiffAt_pi.1 h1) α).congr_of_eventuallyEq hev

/-- The new table is smooth where the change of coordinates and the old table are. -/
theorem contDiffAt_inNewCoords_top (hΦ : ContDiffAt ℝ ∞ Φ y)
    (hg : ∀ α β, ContDiffAt ℝ ∞ (g α β) (Φ y)) (μ ν : Fin n) :
    ContDiffAt ℝ ∞ (inNewCoords Φ g μ ν) y := by
  have hJ := contDiffAt_jac_top hΦ
  have hgc : ∀ α β, ContDiffAt ℝ ∞ (fun z => g α β (Φ z)) y := fun α β =>
    ContDiffAt.comp (g := g α β) y (hg α β) hΦ
  change ContDiffAt ℝ ∞ (fun z => ∑ α, ∑ β, jac Φ α μ z * jac Φ β ν z * g α β (Φ z)) y
  exact ContDiffAt.sum fun α _ => ContDiffAt.sum fun β _ =>
    ((hJ α μ).mul (hJ β ν)).mul (hgc α β)

/-- **One time direction does not depend on the coordinates.** If the change of coordinates
loses no direction at `y` and the old table has one time direction at `Φ y`, the new table has
one time direction at `y`. -/
theorem hasOneTimeDirection_inNewCoords (hΦ : DifferentiableAt ℝ Φ y)
    (hJ : (tab (jac Φ) y).det ≠ 0)
    (h : Curved.HasOneTimeDirection fun v w : Coords n ↦ Curved.tableMeasure g (Φ y) v w) :
    Curved.HasOneTimeDirection
      fun v w : Coords n ↦ Curved.tableMeasure (inNewCoords Φ g) y v w := by
  obtain ⟨t, ht, hpos⟩ := h
  have hU : IsUnit (tab (jac Φ) y).det := isUnit_iff_ne_zero.mpr hJ
  have hD : ∀ v, fderiv ℝ Φ y v = (tab (jac Φ) y).mulVec v := fderiv_eq_mulVec hΦ
  -- The slope of the change of coordinates hits the step through time ...
  have hsurj : fderiv ℝ Φ y ((tab (jac Φ) y)⁻¹.mulVec t) = t := by
    rw [hD, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]
  -- ... and sends no step to zero.
  have hinj : ∀ v, fderiv ℝ Φ y v = 0 → v = 0 := by
    intro v hv
    have e : (tab (jac Φ) y)⁻¹.mulVec ((tab (jac Φ) y).mulVec v) = v := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec]
    rw [← e, ← hD, hv, Matrix.mulVec_zero]
  refine ⟨(tab (jac Φ) y)⁻¹.mulVec t, ?_, fun v hv hne ↦ ?_⟩
  · change Curved.tableMeasure (inNewCoords Φ g) y ((tab (jac Φ) y)⁻¹.mulVec t)
      ((tab (jac Φ) y)⁻¹.mulVec t) < 0
    rw [tableMeasure_inNewCoords g hΦ, hsurj]
    exact ht
  · have hv2 : Curved.tableMeasure (inNewCoords Φ g) y ((tab (jac Φ) y)⁻¹.mulVec t) v = 0 := hv
    rw [tableMeasure_inNewCoords g hΦ, hsurj] at hv2
    have h3 := hpos (fderiv ℝ Φ y v) hv2 fun h0 ↦ hne (hinj v h0)
    change 0 < Curved.tableMeasure (inNewCoords Φ g) y v v
    rw [tableMeasure_inNewCoords g hΦ]
    exact h3

end Pointwise

/-! ## The table in the coordinates of `turnsCoordinates`, on the patch -/

section Patch

variable {g ginv : Fin 4 → Fin 4 → Coords 4 → ℝ} {ξ : Fin 3 → Fin 4 → Coords 4 → ℝ}
  {s : Set (Coords 4)} {Φ : Coords 4 → Coords 4} {R : Matrix (Fin 3) (Fin 3) ℝ}
  {W : Set (Coords 4)}

/-- On the patch the change of coordinates is smooth at every point. -/
theorem patch_contDiffAt (hW : IsOpen W) (hΦ : ContDiffOn ℝ ∞ Φ W) {y : Coords 4} (hy : y ∈ W) :
    ContDiffAt ℝ ∞ Φ y :=
  hΦ.contDiffAt (hW.mem_nhds hy)

/-- On the patch the change of coordinates can be differentiated at every point. -/
theorem patch_differentiableAt (hW : IsOpen W) (hΦ : ContDiffOn ℝ ∞ Φ W) {y : Coords 4}
    (hy : y ∈ W) : DifferentiableAt ℝ Φ y :=
  (patch_contDiffAt hW hΦ hy).differentiableAt (by simp)

/-- On the patch each part of the change of coordinates is three times smoothly
differentiable. -/
theorem patch_contDiffAt_three (hW : IsOpen W) (hΦ : ContDiffOn ℝ ∞ Φ W) {y : Coords 4}
    (hy : y ∈ W) (α : Fin 4) : ContDiffAt ℝ 3 (fun z ↦ Φ z α) y :=
  ((contDiffAt_pi.1 (patch_contDiffAt hW hΦ hy)) α).of_le (by norm_num)

/-- **The new table is smooth** at every point of the patch. -/
theorem newTable_smooth (hg : Curved.IsRegularTableOn g ginv s) (hW : IsOpen W)
    (hΦs : ∀ y ∈ W, Φ y ∈ s) (hΦ : ContDiffOn ℝ ∞ Φ W) :
    ∀ y ∈ W, ∀ i j, ContDiffAt ℝ ∞ (inNewCoords Φ g i j) y := fun y hy i j ↦
  contDiffAt_inNewCoords_top (patch_contDiffAt hW hΦ hy)
    (fun α β ↦ hg.contDiffAt (hΦs y hy) α β) i j

/-- **The new table is symmetric** at every point of the patch. -/
theorem newTable_symm (hg : Curved.IsRegularTableOn g ginv s) (hΦs : ∀ y ∈ W, Φ y ∈ s) :
    ∀ y ∈ W, ∀ i j, inNewCoords Φ g i j y = inNewCoords Φ g j i y := fun y hy i j ↦
  inNewCoords_symm (hg.symm (Φ y) (hΦs y hy)) i j

/-- The new table has the inverse table `invT` near every point of the patch. -/
theorem newTable_eventually_inverse (hg : Curved.IsRegularTableOn g ginv s) (hW : IsOpen W)
    (hΦs : ∀ y ∈ W, Φ y ∈ s) (hΦ : ContDiffOn ℝ ∞ Φ W)
    (hdet : ∀ y ∈ W, sin (y 2) ≠ 0 ∧ (tab (jac Φ) y).det ≠ 0) :
    ∀ y ∈ W, ∀ᶠ z in 𝓝 y, ∀ i k,
      ∑ j, inNewCoords Φ g i j z * invT (inNewCoords Φ g) j k z = if i = k then 1 else 0 :=
  fun y hy ↦ inverse_inNewCoords (ginv := ginv) (patch_contDiffAt_three hW hΦ hy)
    (fun α β ↦ (hg.contDiffAt (hΦs y hy) α β).of_le (by norm_num))
    (hg.inverse (Φ y) (hΦs y hy)) (hdet y hy).2

/-- **The new table has an inverse table,** `invT (inNewCoords Φ g)`, at every point of the
patch. -/
theorem newTable_inverse (hg : Curved.IsRegularTableOn g ginv s) (hW : IsOpen W)
    (hΦs : ∀ y ∈ W, Φ y ∈ s) (hΦ : ContDiffOn ℝ ∞ Φ W)
    (hdet : ∀ y ∈ W, sin (y 2) ≠ 0 ∧ (tab (jac Φ) y).det ≠ 0) :
    ∀ y ∈ W, ∀ i k,
      ∑ j, inNewCoords Φ g i j y * invT (inNewCoords Φ g) j k y = if i = k then 1 else 0 :=
  fun y hy ↦ (newTable_eventually_inverse hg hW hΦs hΦ hdet y hy).self_of_nhds

/-- **The inverse of the new table is smooth** at every point of the patch. -/
theorem newTable_inverse_smooth (hg : Curved.IsRegularTableOn g ginv s) (hW : IsOpen W)
    (hΦs : ∀ y ∈ W, Φ y ∈ s) (hΦ : ContDiffOn ℝ ∞ Φ W)
    (hdet : ∀ y ∈ W, sin (y 2) ≠ 0 ∧ (tab (jac Φ) y).det ≠ 0) :
    ∀ y ∈ W, ∀ i j, ContDiffAt ℝ ∞ (invT (inNewCoords Φ g) i j) y := fun y hy i j ↦
  contDiffAt_of_inverse (newTable_smooth hg hW hΦs hΦ y hy)
    (newTable_eventually_inverse hg hW hΦs hΦ hdet y hy) i j

/-- **The new table is a good table on the patch,** with the inverse table `invT`. -/
theorem newTable_regular (hg : Curved.IsRegularTableOn g ginv s) (hW : IsOpen W)
    (hΦs : ∀ y ∈ W, Φ y ∈ s) (hΦ : ContDiffOn ℝ ∞ Φ W)
    (hdet : ∀ y ∈ W, sin (y 2) ≠ 0 ∧ (tab (jac Φ) y).det ≠ 0) :
    Curved.IsRegularTableOn (inNewCoords Φ g) (invT (inNewCoords Φ g)) W where
  isOpen := hW
  smooth := fun a b y hy ↦ (newTable_smooth hg hW hΦs hΦ y hy a b).contDiffWithinAt
  symm := newTable_symm hg hΦs
  inverse := newTable_inverse hg hW hΦs hΦ hdet

/-- **The new table is empty** at every point of the patch, if the old one is empty on its
region. -/
theorem newTable_isRicciFlatAt (hg : Curved.IsRegularTableOn g ginv s) (hW : IsOpen W)
    (hΦs : ∀ y ∈ W, Φ y ∈ s) (hΦ : ContDiffOn ℝ ∞ Φ W)
    (hdet : ∀ y ∈ W, sin (y 2) ≠ 0 ∧ (tab (jac Φ) y).det ≠ 0)
    (hflat : ∀ x ∈ s, IsRicciFlatAt g ginv x) :
    ∀ y ∈ W, IsRicciFlatAt (inNewCoords Φ g) (invT (inNewCoords Φ g)) y := fun y hy ↦
  (isRicciFlatAt_changeOfCoords (patch_contDiffAt_three hW hΦ hy)
    (fun α β ↦ (hg.contDiffAt (hΦs y hy) α β).of_le (by norm_num))
    (hg.eventually_symm (hΦs y hy)) (hg.eventually_inverse (hΦs y hy)) (hdet y hy).2).2
    (hflat (Φ y) (hΦs y hy))

/-- **The new table has one time direction** at every point of the patch, if the old one has on
its region. -/
theorem newTable_hasOneTimeDirection (hW : IsOpen W) (hΦs : ∀ y ∈ W, Φ y ∈ s)
    (hΦ : ContDiffOn ℝ ∞ Φ W) (hdet : ∀ y ∈ W, sin (y 2) ≠ 0 ∧ (tab (jac Φ) y).det ≠ 0)
    (htime : ∀ x ∈ s,
      Curved.HasOneTimeDirection fun v w : Coords 4 ↦ Curved.tableMeasure g x v w) :
    ∀ y ∈ W, Curved.HasOneTimeDirection
      fun v w : Coords 4 ↦ Curved.tableMeasure (inNewCoords Φ g) y v w := fun y hy ↦
  hasOneTimeDirection_inNewCoords (patch_differentiableAt hW hΦ hy) (hdet y hy).2
    (htime (Φ y) (hΦs y hy))

/-- In the new coordinates the step along the first angle is, seen in the old coordinates, a
fixed mix of the three given fields: the step along the first angle is a mix of two standard
turns, and the change of coordinates turns each standard turn into a mix of the fields. -/
theorem jac_two_eq_mix {y : Coords 4}
    (h0 : ∀ α, ∑ μ, jac Φ α μ y * stdTurn 0 μ y = ∑ j, R 0 j * ξ j α (Φ y))
    (h1 : ∀ α, ∑ μ, jac Φ α μ y * stdTurn 1 μ y = ∑ j, R 1 j * ξ j α (Φ y)) (α : Fin 4) :
    jac Φ α 2 y = ∑ j, (cos (y 3) * R 0 j - sin (y 3) * R 1 j) * ξ j α (Φ y) := by
  have e : ∀ μ, (Pi.single 2 1 : Coords 4) μ = cos (y 3) * rotY μ y - sin (y 3) * rotX μ y :=
    fun μ ↦ congrFun (Curved.single_two_eq y) μ
  have hu1 : jac Φ α 2 y = ∑ μ, jac Φ α μ y * (Pi.single 2 1 : Coords 4) μ := by
    simp [Pi.single_apply]
  have h0' := h0 α
  have h1' := h1 α
  rw [stdTurn_zero] at h0'
  rw [stdTurn_one] at h1'
  calc jac Φ α 2 y
      = ∑ μ, jac Φ α μ y * (cos (y 3) * rotY μ y - sin (y 3) * rotX μ y) := by
        rw [hu1]
        exact Finset.sum_congr rfl fun μ _ ↦ by rw [e μ]
    _ = cos (y 3) * ∑ μ, jac Φ α μ y * rotY μ y - sin (y 3) * ∑ μ, jac Φ α μ y * rotX μ y := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun μ _ ↦ by ring
    _ = ∑ j, (cos (y 3) * R 0 j - sin (y 3) * R 1 j) * ξ j α (Φ y) := by
        rw [h0', h1', Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- **The spheres have a positive size in the new coordinates.** The entry of the new table for
the first angle is positive at every point of the patch: it is the squared length of a step
along the first angle, that step lies in the surface that the three fields sweep out, and there
all lengths are positive. -/
theorem newTable_pos_two_two (hξ : TurnsOn g ξ s) (hΦs : ∀ y ∈ W, Φ y ∈ s)
    (hdet : ∀ y ∈ W, sin (y 2) ≠ 0 ∧ (tab (jac Φ) y).det ≠ 0)
    (hturn : ∀ y ∈ W, ∀ i α, ∑ μ, jac Φ α μ y * stdTurn i μ y = ∑ j, R i j * ξ j α (Φ y)) :
    ∀ y ∈ W, 0 < inNewCoords Φ g 2 2 y := by
  intro y hy
  have hu2 := jac_two_eq_mix (ξ := ξ) (R := R) (fun α ↦ hturn y hy 0 α) (fun α ↦ hturn y hy 1 α)
  -- The step along the first angle, seen in the old coordinates, lies in the surface.
  have hmem : (fun α ↦ jac Φ α 2 y)
      ∈ Submodule.span ℝ (Set.range fun i ↦ (fun k ↦ ξ i k (Φ y) : Coords 4)) := by
    have e : (fun α ↦ jac Φ α 2 y)
        = ∑ j, (cos (y 3) * R 0 j - sin (y 3) * R 1 j) • (fun k ↦ ξ j k (Φ y) : Coords 4) := by
      funext α
      rw [hu2 α, Finset.sum_apply]
      rfl
    rw [e]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  -- It is not zero, because the change of coordinates loses no direction.
  have hne : (fun α ↦ jac Φ α 2 y) ≠ 0 := by
    intro h0
    exact (hdet y hy).2 (Matrix.det_eq_zero_of_column_eq_zero 2 fun α ↦ congrFun h0 α)
  have hpos := hξ.positive (Φ y) (hΦs y hy) (fun α ↦ jac Φ α 2 y) hmem hne
  have e : inNewCoords Φ g 2 2 y = ∑ a, ∑ b, g a b (Φ y) * jac Φ a 2 y * jac Φ b 2 y := by
    simp only [inNewCoords]
    exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring
  rw [e]
  exact hpos

end Patch

end GravityInLean.Join
