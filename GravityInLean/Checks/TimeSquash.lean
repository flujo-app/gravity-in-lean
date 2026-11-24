/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.Tests

import Mathlib.Tactic

/-!
# Tests 5 and 6: one time direction, and a squashed sphere

Board item `task:checks-time-squash`. Five of the tests fixed in `Goals/Tests.lean`, groups 5
and 6. Four of them are cases where a definition of `Curved/Basic.lean` should fail, and one is
a case where it should hold.

Group 5, "exactly one time direction":

* `twoTimeNotSpaceTime`: a flat table with two time directions is not a space-time. Whatever
  step `t` is offered as the time direction, the step with the first two parts of `t` swapped
  and one sign turned is at right angles to `t` and has no positive length.
* `flatDegNotOneTime`: a flat table that gives the last direction the length zero has not "one
  time direction": that last direction is at right angles to every step, and its length is zero,
  not positive.

Group 6, a sphere squashed along the angle around the axis:

* `squashNotUnchanged`: the turn through the equator changes the squashed table. Its change in
  the entry of the two angles is `r² cos φ`, and that is not zero.
* `squashUnchangedAxis`: the turn around the axis leaves it unchanged, since no entry depends
  on the angle around the axis.
* `squashNotRound`: so the squashed table does not look the same from every side by the three
  standard turns.

The helping lemmas live under the name `TimeSquash`.
-/

@[expose] public section

namespace GravityInLean

open Real Set

open scoped Manifold

namespace Curved

namespace TimeSquash

/-! ## The two flat tables of group 5, written out -/

/-- The table with two time directions measures two steps like this: the first two parts count
with a minus sign, the last two with a plus sign. -/
theorem twoTime_apply (x v w : Coords 4) :
    tableMeasure Tests.twoTimeG x v w = -(v 0 * w 0) - v 1 * w 1 + v 2 * w 2 + v 3 * w 3 := by
  simp only [tableMeasure, formOf_apply, Fin.sum_univ_four]
  simp [Tests.twoTimeG]
  ring

/-- Under the table with a direction of length zero, the last direction is at right angles to
every step. -/
theorem flatDeg_last (x v : Coords 4) :
    tableMeasure Tests.flatDegG x v (Pi.single 3 1) = 0 := by
  simp only [tableMeasure]
  rw [formOf_single_right]
  simp [Tests.flatDegG]

/-- Under that table the last direction has the length zero. -/
theorem flatDeg_last_last (x : Coords 4) :
    tableMeasure Tests.flatDegG x (Pi.single 3 1) (Pi.single 3 1) = 0 :=
  flatDeg_last x _

/-! ## The squashed table of group 6 -/

/-- The entries of the squashed table can be differentiated outside the rim. -/
theorem differentiableAt_squashG (M : ℝ) {x : Coords 4} (hx : x ∈ outside M) (a b : Fin 4) :
    DifferentiableAt ℝ (Tests.squashG M a b) x := by
  by_cases hab : a = b
  · subst hab
    have h1 := (schwarzschild_regularTable_outside M).differentiableAt hx a a
    have e : Tests.squashG M a a
        = fun y ↦ (if a = 3 then 2 else 1) * roundG (schwA M) (schwB M) a a y := by
      funext y
      simp [Tests.squashG, roundG, diag]
    rw [e]
    exact h1.const_mul _
  · have e : Tests.squashG M a b = fun _ ↦ 0 := by
      funext y
      simp [Tests.squashG, diag, hab]
    rw [e]
    exact differentiableAt_const _

/-- No entry of the squashed table changes with the angle around the axis. -/
theorem slope_three_squashG (M : ℝ) (a b : Fin 4) (x : Coords 4) :
    slope 3 (Tests.squashG M a b) x = 0 := by
  unfold Tests.squashG
  rw [slope_diag]
  by_cases hab : a = b
  · rw [ite_eq_left hab]
    simp [slope, roundDiag, sep]
  · rw [ite_eq_right hab]

/-- The change of the squashed table along the turn through the equator, in the entry of the two
angles: `r² cos φ`. For the table that is not squashed it is zero. -/
theorem lieD_squashG_rotX (M : ℝ) {x : Coords 4} (hs : sin (x 2) ≠ 0) :
    lieD (Tests.squashG M) rotX 2 3 x = x 1 ^ 2 * cos (x 3) := by
  have h23 : Tests.squashG M 2 3 = fun _ ↦ 0 := by
    funext y
    simp [Tests.squashG, diag]
  have h22 : Tests.squashG M 2 2 x = x 1 ^ 2 := by
    simp [Tests.squashG, diag, roundDiag, sep, gr, gθ, sqF, constOne]
  have h33 : Tests.squashG M 3 3 x = 2 * (x 1 ^ 2 * sin (x 2) ^ 2) := by
    simp [Tests.squashG, diag, roundDiag, sep, gr, gθ, sqF, sin2]
  have s22 : slope 2 (rotX 2) x = 0 := by rw [slope_rotX_two]; simp
  have s32 : slope 3 (rotX 2) x = -cos (x 3) := by rw [slope_rotX_two]; simp
  have s23 : slope 2 (rotX 3) x = (sin (x 2) ^ 2)⁻¹ * cos (x 3) := by
    rw [slope_rotX_three, ← deriv_negCot hs]; simp
  rw [lieD_rotX, h22, h33, s22, s32, s23, h23]
  simp only [slope_const]
  field_simp
  ring

end TimeSquash

namespace Tests

open TimeSquash

/-! ## 5. "Exactly one" time direction, and "strictly positive" -/

/-- **Two time directions are not one.** The flat table with two minus signs is not a
space-time. -/
theorem twoTimeNotSpaceTime : TwoTimeNotSpaceTime := by
  intro h
  obtain ⟨t, ht, hpos⟩ := h.oneTime (0 : Coords 4) (mem_univ _)
  -- The step `t`, seen as four numbers.
  set t' : Coords 4 := t with ht'
  have ht0 : tableMeasure twoTimeG 0 t' t' < 0 := ht
  rw [twoTime_apply] at ht0
  -- A second step: the first two parts of `t` swapped, one with its sign turned.
  let v : Coords 4 := ![t' 1, -t' 0, 0, 0]
  have hv0 : v 0 = t' 1 := rfl
  have hv1 : v 1 = -t' 0 := rfl
  have hv2 : v 2 = 0 := rfl
  have hv3 : v 3 = 0 := rfl
  have horth : tableMeasure twoTimeG 0 t' v = 0 := by
    rw [twoTime_apply, hv0, hv1, hv2, hv3]
    ring
  have hne : v ≠ 0 := by
    intro hv
    have e0 : t' 1 = 0 := by rw [← hv0, hv]; rfl
    have e1 : t' 0 = 0 := by
      have : -t' 0 = 0 := by rw [← hv1, hv]; rfl
      linarith
    rw [e0, e1] at ht0
    nlinarith [sq_nonneg (t' 2), sq_nonneg (t' 3)]
  have hlen : 0 < tableMeasure twoTimeG 0 v v := hpos v horth hne
  rw [twoTime_apply, hv0, hv1, hv2, hv3] at hlen
  nlinarith [sq_nonneg (t' 0), sq_nonneg (t' 1)]

/-- **A direction of length zero is not allowed next to the time direction.** The flat table
that gives the last direction the length zero has not "one time direction". -/
theorem flatDegNotOneTime : FlatDegNotOneTime := by
  intro x h
  obtain ⟨t, _, hpos⟩ := h
  have hne : (Pi.single 3 1 : Coords 4) ≠ 0 := by
    intro h0
    have h3 : (Pi.single 3 1 : Coords 4) 3 = 0 := by rw [h0]; rfl
    rw [Pi.single_eq_same] at h3
    exact one_ne_zero h3
  have hlen : 0 < tableMeasure flatDegG x (Pi.single 3 1) (Pi.single 3 1) :=
    hpos (Pi.single 3 1) (flatDeg_last x t) hne
  rw [flatDeg_last_last] at hlen
  exact lt_irrefl 0 hlen

/-! ## 6. A squashed sphere -/

/-- **The turn through the equator does not leave the squashed sphere unchanged,** wherever the
cosine of the angle around the axis is not zero. -/
theorem squashNotUnchanged : SquashNotUnchanged := by
  intro M x hx hcos h
  have hχ : turns 1 = fieldOf rotX := rfl
  rw [hχ, leavesUnchangedAt_table_iff (differentiableAt_squashG M hx)
    (differentiableAt_rotX hx.2.2)] at h
  have h23 : lieD (squashG M) rotX 2 3 x = 0 := h 2 3
  rw [lieD_squashG_rotX M hx.2.2] at h23
  exact mul_ne_zero (pow_ne_zero 2 hx.1.ne') hcos h23

/-- **The turn around the axis leaves the squashed sphere unchanged.** -/
theorem squashUnchangedAxis : SquashUnchangedAxis := by
  intro M x hx
  have hχ : turns 2 = fieldOf rotZ := rfl
  rw [hχ, leavesUnchangedAt_table_iff (differentiableAt_squashG M hx) (differentiableAt_rotZ x)]
  intro i j
  rw [lieD_rotZ, slope_three_squashG]

/-- **The squashed sphere is not "the same from every side" by the three standard turns.** -/
theorem squashNotRound : SquashNotRound := by
  intro M h
  -- A point outside the rim, on the equator, where the cosine of the last angle is one.
  let x : Coords 4 := ![0, 2 * |M| + 1, π / 2, 0]
  have hx1 : x 1 = 2 * |M| + 1 := rfl
  have hx2 : x 2 = π / 2 := rfl
  have hx3 : x 3 = 0 := rfl
  have hx : x ∈ outside M := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hx1]; positivity
    · rw [hx1]; linarith [le_abs_self M]
    · rw [hx2, sin_pi_div_two]; exact one_ne_zero
  have hcos : cos (x 3) ≠ 0 := by
    rw [hx3, cos_zero]; exact one_ne_zero
  exact squashNotUnchanged M x hx hcos (h.unchanged 1 x hx)

end Tests

end Curved

end GravityInLean
