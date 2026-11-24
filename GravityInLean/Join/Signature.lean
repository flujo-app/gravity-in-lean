/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Curved.Tables

import Mathlib.Tactic

/-!
# One time direction, read off a table that splits into a block and two positive entries

Board item `task:join-signature`. Plain linear algebra at one point. A length measure of the
round shape is, at each point, a `2 × 2` block for time and distance,

  `h00 * v 0 * w 0 + h01 * (v 0 * w 1 + v 1 * w 0) + h11 * v 1 * w 1`,

plus two positive entries for the two angles, `s2 * v 2 * w 2 + s3 * v 3 * w 3`. If such a
measure has one time direction (`Curved.HasOneTimeDirection`), then the determinant of the block
is negative: `h00 * h11 - h01 * h01 < 0`. With `h00 = -A`, `h11 = B`, `h01 = C` this is
`0 < det2 A B C = A * B + C * C`, the field `SettingG.spaceTime` of `BirkhoffGeneral.lean`.

The proof takes the step `t` through time, drops its two angle parts (they only add to the
squared length), and turns what is left by a quarter turn inside the block: the turned step `v`
is at right angles to `t`, and its squared length is the determinant times the squared length of
the block part of `t`. The second is negative and the first must be positive.

* `block_det_neg_of_oneTime`: the statement for any two-slot function of this form;
* `det2_pos_of_oneTime`: the same for the measure `formOf T` of a table of numbers.
-/

@[expose] public section

namespace GravityInLean.Join

open GravityInLean.Curved

/-- A two-slot function on steps of four parts that is a `2 × 2` block on the first two parts plus
positive multiples of the squares of the last two, and that has one time direction: the
determinant of the block is negative. -/
theorem block_det_neg_of_oneTime {b : Coords 4 → Coords 4 → ℝ} (h00 h01 h11 s2 s3 : ℝ)
    (hb : ∀ v w : Coords 4, b v w = h00 * v 0 * w 0 + h01 * (v 0 * w 1 + v 1 * w 0)
      + h11 * v 1 * w 1 + s2 * v 2 * w 2 + s3 * v 3 * w 3)
    (hs2 : 0 < s2) (hs3 : 0 < s3) (h : HasOneTimeDirection b) :
    h00 * h11 - h01 * h01 < 0 := by
  obtain ⟨t, ht, hpos⟩ := h
  rw [hb] at ht
  -- The block part of the step through time has negative squared length.
  have hq : h00 * t 0 * t 0 + h01 * (t 0 * t 1 + t 1 * t 0) + h11 * t 1 * t 1 < 0 := by
    nlinarith [mul_nonneg hs2.le (mul_self_nonneg (t 2)),
      mul_nonneg hs3.le (mul_self_nonneg (t 3))]
  -- The block part of `t`, turned by a quarter turn inside the block.
  have hv := hpos ![-(h01 * t 0 + h11 * t 1), h00 * t 0 + h01 * t 1, 0, 0]
    (by rw [hb]; simp; ring)
    (by
      intro h0
      have e0 : -(h01 * t 0 + h11 * t 1) = 0 := by simpa using congrFun h0 0
      have e1 : h00 * t 0 + h01 * t 1 = 0 := by simpa using congrFun h0 1
      have hq0 : h00 * t 0 * t 0 + h01 * (t 0 * t 1 + t 1 * t 0) + h11 * t 1 * t 1 = 0 := by
        linear_combination t 0 * e1 - t 1 * e0
      linarith)
  rw [hb] at hv
  have hv' : 0 < h00 * (-(h11 * t 1) + -(h01 * t 0)) * (-(h11 * t 1) + -(h01 * t 0))
      + h01 * ((-(h11 * t 1) + -(h01 * t 0)) * (h00 * t 0 + h01 * t 1)
        + (h00 * t 0 + h01 * t 1) * (-(h11 * t 1) + -(h01 * t 0)))
      + h11 * (h00 * t 0 + h01 * t 1) * (h00 * t 0 + h01 * t 1) := by
    simpa using hv
  -- Its squared length is the determinant times the squared length of the block part of `t`.
  have e : h00 * (h01 * t 0 + h11 * t 1) * (h01 * t 0 + h11 * t 1)
      + h01 * (-((h01 * t 0 + h11 * t 1) * (h00 * t 0 + h01 * t 1))
        + -((h00 * t 0 + h01 * t 1) * (h01 * t 0 + h11 * t 1)))
      + h11 * (h00 * t 0 + h01 * t 1) * (h00 * t 0 + h01 * t 1)
      = (h00 * h11 - h01 * h01)
        * (h00 * t 0 * t 0 + h01 * (t 0 * t 1 + t 1 * t 0) + h11 * t 1 * t 1) := by
    ring
  by_contra hD
  rw [not_lt] at hD
  nlinarith [mul_nonneg hD (neg_nonneg.mpr hq.le)]

/-- The measure of a table of numbers that is a `2 × 2` block for time and distance plus two
positive entries for the angles, with one time direction: the determinant of the block is
negative. With `h00 = -A`, `h11 = B`, `h01 = C` this says `0 < A * B + C * C`. -/
theorem det2_pos_of_oneTime {T : Fin 4 → Fin 4 → ℝ} (h00 h01 h11 s2 s3 : ℝ)
    (hT : ∀ v w : Coords 4, Curved.formOf T v w = h00 * v 0 * w 0
      + h01 * (v 0 * w 1 + v 1 * w 0) + h11 * v 1 * w 1 + s2 * v 2 * w 2 + s3 * v 3 * w 3)
    (hs2 : 0 < s2) (hs3 : 0 < s3)
    (h : Curved.HasOneTimeDirection fun v w : Coords 4 ↦ Curved.formOf T v w) :
    h00 * h11 - h01 * h01 < 0 :=
  block_det_neg_of_oneTime h00 h01 h11 s2 s3 hT hs2 hs3 h

end GravityInLean.Join
