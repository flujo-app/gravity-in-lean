/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.Tests

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Tests, group 1: Eddington's coordinates give an empty space-time, rim included

Board item `task:checks-ef-empty`. Schwarzschild's space-time in Eddington's coordinates
(`Tests.efG`) is good at every positive distance, the rim of the black hole and its inside
included. This file proves two of the tests of group 1 in `Goals/Tests.lean`:

* `efIsSpaceTimeOn`: it is a space-time there: symmetric, smooth, with one time direction;
* `efIsEmptyOn`: space is empty there.

The mass `M` may be any real number. The steps on the way:

* `isOpen_efRegion`: the region is open;
* `smooth_sep2`, `smooth_efG`: every entry of the table is smooth away from the centre;
* `ef_regular`: so the table is good on the region, with the inverse `genGinv` of the general
  round shape;
* `ef_measure_apply`: the length measure written out;
* `ef_oneTime`: the step `(1, (A - 1) / 2, 0, 0)` has squared length `-1`, and every other step
  at right angles to it has a positive squared length. This table is not diagonal, so the time
  direction is not one of the four coordinate directions.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean

open Real Set

open scoped Manifold ContDiff

namespace Curved

namespace Tests

/-- The region of the test is open. -/
theorem isOpen_efRegion : IsOpen efRegion :=
  (isOpen_lt continuous_const (continuous_apply 1)).inter
    (isOpen_ne_fun (Real.continuous_sin.comp (continuous_apply 2)) continuous_const)

/-- A function of the form `F(t, ρ) · h(θ)` is as smooth as its two factors. -/
theorem smooth_sep2 {F : ℝ → ℝ → ℝ} {h : ℝ → ℝ} {x : Coords 4} {k : WithTop ℕ∞}
    (hF : ContDiffAt ℝ k (Function.uncurry F) (x 0, x 1)) (hh : ContDiffAt ℝ k h (x 2)) :
    ContDiffAt ℝ k (sep2 F h) x := by
  have hpair : ContDiffAt ℝ k (fun y : Coords 4 => (y 0, y 1)) x :=
    (contDiffAt_apply ℝ (fun _ : Fin 4 => ℝ) 0 x).prodMk
      (contDiffAt_apply ℝ (fun _ : Fin 4 => ℝ) 1 x)
  have h1 : ContDiffAt ℝ k (fun y : Coords 4 => F (y 0) (y 1)) x :=
    ContDiffAt.comp (g := Function.uncurry F) x hF hpair
  have h2 : ContDiffAt ℝ k (fun y : Coords 4 => h (y 2)) x :=
    ContDiffAt.comp (g := h) x hh (contDiffAt_apply ℝ (fun _ : Fin 4 => ℝ) 2 x)
  exact h1.mul h2

/-- Every entry of Eddington's table is smooth away from the centre, the rim included. -/
theorem smooth_efG (M : ℝ) {x : Coords 4} (hr : x 1 ≠ 0) (i j : Fin 4) {k : WithTop ℕ∞} :
    ContDiffAt ℝ k (efG M i j) x := by
  have hF : ContDiffAt ℝ k
      (Function.uncurry (gTR (onlyR (schwA M)) zero2 one2 (onlyR sqF) i j)) (x 0, x 1) := by
    unfold gTR
    split_ifs
    · exact (ContDiffAt.comp (g := schwA M) (x 0, x 1) (smooth_schwA M hr) contDiffAt_snd).neg
    · exact (contDiffAt_const : ContDiffAt ℝ k (fun _ : ℝ × ℝ => (1 : ℝ)) (x 0, x 1))
    · exact (contDiffAt_const : ContDiffAt ℝ k (fun _ : ℝ × ℝ => (0 : ℝ)) (x 0, x 1))
    · exact ContDiffAt.comp (g := sqF) (x 0, x 1) (contDiffAt_id.pow 2) contDiffAt_snd
    · exact (contDiffAt_const : ContDiffAt ℝ k (fun _ : ℝ × ℝ => (0 : ℝ)) (x 0, x 1))
  have hh : ContDiffAt ℝ k (gΘ i j) (x 2) := by
    unfold gΘ
    split_ifs
    · exact (Real.contDiff_sin.contDiffAt).pow 2
    · exact (contDiffAt_const : ContDiffAt ℝ k (fun _ : ℝ => (1 : ℝ)) (x 2))
  exact smooth_sep2 hF hh

/-- Eddington's table is good at every positive distance off the poles, the rim included: its
time-distance part has determinant `-1` whatever the clock function is. -/
theorem ef_regular (M : ℝ) :
    IsRegularTableOn (efG M) (genGinv (onlyR (schwA M)) zero2 one2 (onlyR sqF)) efRegion where
  isOpen := isOpen_efRegion
  smooth := fun a b _ hx ↦ (smooth_efG M hx.1.ne' a b).contDiffWithinAt
  symm := fun x _ a b ↦ genG_symm (onlyR (schwA M)) zero2 one2 (onlyR sqF) a b x
  inverse := fun x hx a c ↦
    genG_mul_genGinv (by rw [eddington_det2]; exact one_ne_zero)
      (pow_ne_zero 2 hx.1.ne' : x 1 ^ 2 ≠ 0) hx.2 a c

/-- The length measure of Eddington's table, written out: `-A dt² + 2 dt dρ + ρ² dθ² +
ρ² sin²θ dφ²`. -/
theorem ef_measure_apply (M : ℝ) (x v w : Coords 4) :
    tableMeasure (efG M) x v w
      = -schwA M (x 1) * v 0 * w 0 + v 0 * w 1 + v 1 * w 0 + x 1 ^ 2 * v 2 * w 2
        + x 1 ^ 2 * sin (x 2) ^ 2 * v 3 * w 3 := by
  simp only [tableMeasure, formOf_apply, Fin.sum_univ_four]
  simp [genG, sep2, gTR, gΘ, negA, onlyR, zero2, one2, sqF, sin2, constOne]

/-- **Eddington's table has one time direction, on the rim as well.** The step
`(1, (A - 1) / 2, 0, 0)` has squared length `-1`. A step at right angles to it has
`v 1 = (1 + A) / 2 · v 0`, and so the squared length `(v 0)² + ρ² (v 2)² + ρ² sin²θ (v 3)²`. -/
theorem ef_oneTime (M : ℝ) {x : Coords 4} (hr : 0 < x 1) (hs : sin (x 2) ≠ 0) :
    HasOneTimeDirection fun v w : Coords 4 ↦ tableMeasure (efG M) x v w := by
  have h0 : (![1, (schwA M (x 1) - 1) / 2, 0, 0] : Coords 4) 0 = 1 := rfl
  have h1 : (![1, (schwA M (x 1) - 1) / 2, 0, 0] : Coords 4) 1 = (schwA M (x 1) - 1) / 2 := rfl
  have h2 : (![1, (schwA M (x 1) - 1) / 2, 0, 0] : Coords 4) 2 = 0 := rfl
  have h3 : (![1, (schwA M (x 1) - 1) / 2, 0, 0] : Coords 4) 3 = 0 := rfl
  refine ⟨![1, (schwA M (x 1) - 1) / 2, 0, 0], ?_, ?_⟩
  · change tableMeasure (efG M) x ![1, (schwA M (x 1) - 1) / 2, 0, 0]
      ![1, (schwA M (x 1) - 1) / 2, 0, 0] < 0
    rw [ef_measure_apply, h0, h1, h2, h3]
    linarith
  · intro v hv hne
    have hv' : tableMeasure (efG M) x ![1, (schwA M (x 1) - 1) / 2, 0, 0] v = 0 := hv
    rw [ef_measure_apply, h0, h1, h2, h3] at hv'
    have hv1 : v 1 = (1 + schwA M (x 1)) / 2 * v 0 := by linear_combination hv'
    have key : tableMeasure (efG M) x v v
        = v 0 ^ 2 + x 1 ^ 2 * v 2 ^ 2 + x 1 ^ 2 * sin (x 2) ^ 2 * v 3 ^ 2 := by
      rw [ef_measure_apply, hv1]
      ring
    have hr2 : 0 < x 1 ^ 2 := pow_pos hr 2
    have hs2 : 0 < sin (x 2) ^ 2 := sq_pos_iff.mpr hs
    have hex : v 0 ≠ 0 ∨ v 2 ≠ 0 ∨ v 3 ≠ 0 := by
      by_contra hcon
      have hcon' : v 0 = 0 ∧ v 2 = 0 ∧ v 3 = 0 := by tauto
      obtain ⟨z0, z2, z3⟩ := hcon'
      have z1 : v 1 = 0 := by rw [hv1, z0, mul_zero]
      refine hne (funext fun i ↦ ?_)
      fin_cases i
      · exact z0
      · exact z1
      · exact z2
      · exact z3
    have p0 : 0 ≤ v 0 ^ 2 := sq_nonneg _
    have p2 : 0 ≤ x 1 ^ 2 * v 2 ^ 2 := mul_nonneg hr2.le (sq_nonneg _)
    have p3 : 0 ≤ x 1 ^ 2 * sin (x 2) ^ 2 * v 3 ^ 2 :=
      mul_nonneg (mul_pos hr2 hs2).le (sq_nonneg _)
    change 0 < tableMeasure (efG M) x v v
    rw [key]
    rcases hex with h | h | h
    · have q : 0 < v 0 ^ 2 := sq_pos_iff.mpr h
      linarith
    · have q : 0 < x 1 ^ 2 * v 2 ^ 2 := mul_pos hr2 (sq_pos_iff.mpr h)
      linarith
    · have q : 0 < x 1 ^ 2 * sin (x 2) ^ 2 * v 3 ^ 2 :=
        mul_pos (mul_pos hr2 hs2) (sq_pos_iff.mpr h)
      linarith

/-- **Test 1, first part.** In Eddington's coordinates Schwarzschild's is a space-time at every
positive distance off the poles, the rim and the inside of the black hole included, for every
mass. -/
theorem efIsSpaceTimeOn : EfIsSpaceTimeOn := fun M ↦
  { symm := fun _ hx v w ↦ (ef_regular M).measure_symm hx v w
    oneTime := fun _ hx ↦ ef_oneTime M hx.1 hx.2
    smooth := (ef_regular M).isSmoothOn }

/-- **Test 1, second part.** In Eddington's coordinates Schwarzschild's space-time is empty at
every positive distance off the poles, the rim and the inside of the black hole included, for
every mass. -/
theorem efIsEmptyOn : EfIsEmptyOn := fun M ↦
  (ef_regular M).isEmptyOn fun x hx ↦
    eddington_isEmptyOn M (I := Ioi 0) isOpen_Ioi isPreconnected_Ioi (fun _ h ↦ h) x
      (mem_univ _) hx.1 hx.2

end Tests

end Curved

end GravityInLean
