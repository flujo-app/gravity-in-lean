/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.ExactlyWhen

import Mathlib.Tactic

/-!
# The assumptions of "exactly when" in coordinates can be met

Board item `task:bothways-met`. Birkhoff's theorem both ways, in coordinates
(`BirkhoffExactlyWhenInCoordinates`), is about a round table (`RoundSetting`) on a region where
the size of the spheres is a usable distance (`sizeSlopeOf` is not zero). This file shows that
such tables exist: Schwarzschild's own table, outside the rim and inside it.

* `roundG_isRound`: every table of the round, unchanging shape `roundG A B` looks the same from
  every side, off the poles.
* `sizeSlopeOf_roundG`: for such a table the slope of the size of the spheres, squared and
  measured by the table, is `4 A r²`.
* `roundSetting_roundG`: the table `roundG A B` is a round table on all times and a stretch `I`
  of positive distance labels, if `A` and `B` are smooth there and `A B` is positive there (so
  both are positive, or both negative).
* `sizeSlopeOf_roundG_ne_zero`: the size of its spheres is a usable distance where `A` and the
  distance label are not zero.
* `exactlyWhenAssumptionsMet`, `exactlyWhenAssumptionsMetInside`: the two statements of
  `Goals/ExactlyWhen.lean`, for Schwarzschild's table outside the rim and inside it.

Inside the rim both `A` and `B` of Schwarzschild's table are negative: the distance label is the
time there. The table still has one time direction, because `A B` stays positive.
-/

@[expose] public section

namespace GravityInLean

open Real Set

open scoped ContDiff

/-- A table of the round, unchanging shape looks the same from every side, away from the poles,
whatever its clock function `A` and its ruler function `B` are. -/
theorem roundG_isRound (A B : ℝ → ℝ) {p : Coords 4} (hs : sin (p 2) ≠ 0) :
    IsRoundAt (roundG A B) p := by
  have e : roundG A B = genG (fun _ r => A r) (fun _ r => B r) zero2 (onlyR sqF) := by
    rw [genG_diagonal, changingG_static]
  rw [e]
  exact genG_isRound _ _ _ _ hs

/-- For a table of the round, unchanging shape, the slope of the size of the spheres, squared
and measured by the table, is `4 A r²`: the size of the spheres is `r²`, it changes only along
the distance, at the rate `2 r`, and `sizeSlopeOf` multiplies the square of that rate by `A`. -/
theorem sizeSlopeOf_roundG (A B : ℝ → ℝ) (x : Coords 4) :
    sizeSlopeOf (roundG A B) x = 4 * A (x 1) * x 1 ^ 2 := by
  have e22 : roundG A B 2 2 = sep sqF constOne := by
    funext w
    simp [roundG, diag, roundDiag, gr, gθ]
  have h00 : roundG A B 0 0 x = -A (x 1) := by
    simp [roundG, diag, roundDiag, sep, gr, gθ, negF, constOne]
  have h01 : roundG A B 0 1 x = 0 := by
    simp [roundG, diag]
  unfold sizeSlopeOf
  rw [e22, slope_sep_t, slope_sep_r, deriv_sqF, h00, h01]
  simp only [constOne]
  ring

/-- The size of the spheres of a round, unchanging table is a usable distance wherever the clock
function and the distance label are not zero. -/
theorem sizeSlopeOf_roundG_ne_zero {A B : ℝ → ℝ} {x : Coords 4} (hA : A (x 1) ≠ 0)
    (hr : x 1 ≠ 0) : sizeSlopeOf (roundG A B) x ≠ 0 := by
  rw [sizeSlopeOf_roundG]
  exact mul_ne_zero (mul_ne_zero four_ne_zero hA) (pow_ne_zero 2 hr)

/-- `roundGinv` is the inverse of `roundG` where the distance label, the sine of the pole angle
and the two functions are not zero. Nothing is asked of the slopes of `A` and `B`. -/
theorem roundG_mul_roundGinv_of_ne {A B : ℝ → ℝ} {x : Coords 4} (hr : x 1 ≠ 0)
    (hs : sin (x 2) ≠ 0) (hA0 : A (x 1) ≠ 0) (hB0 : B (x 1) ≠ 0) (i k : Fin 4) :
    ∑ j, roundG A B i j x * roundGinv A B j k x = if i = k then 1 else 0 := by
  fin_cases i <;> fin_cases k <;>
    simp [roundG, roundGinv, diag, roundDiag, sep, gr, gθ, negF, sqF, sin2, constOne,
      hr, hA0, hB0]
  field_simp

/-- **A round, unchanging table is a round table in the sense of the "exactly when".** Take a
clock function `A` and a ruler function `B`, and a stretch `I` of distance labels that is open,
in one piece and positive. If `A` and `B` are smooth of every order on `I` and their product is
positive there (both positive, as outside a rim, or both negative, as inside one), then the
table `roundG A B` with the inverse `roundGinv A B` meets `RoundSetting` for all times and the
distance labels in `I`. -/
theorem roundSetting_roundG {A B : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I) (hc : IsPreconnected I)
    (hpos : ∀ r ∈ I, 0 < r) (hA : ∀ r ∈ I, ContDiffAt ℝ ∞ A r)
    (hB : ∀ r ∈ I, ContDiffAt ℝ ∞ B r) (hAB : ∀ r ∈ I, 0 < A r * B r) :
    RoundSetting (roundG A B) (roundGinv A B) univ I where
  openJ := isOpen_univ
  onePieceJ := isPreconnected_univ
  openI := hI
  onePieceI := hc
  smooth := fun x hx i j ↦ Curved.smooth_roundG (hA _ hx.2.1) (hB _ hx.2.1) i j
  symm := fun x _ i j ↦ roundG_symm A B i j x
  round := fun _ hx ↦ roundG_isRound A B hx.sin_ne
  spaceTime := by
    intro x hx
    have hr : 0 < x 1 := hpos _ hx.2.1
    have h22 : roundG A B 2 2 x = x 1 ^ 2 := by
      simp [roundG, diag, roundDiag, sep, gr, gθ, sqF, constOne]
    have h00 : roundG A B 0 0 x = -A (x 1) := by
      simp [roundG, diag, roundDiag, sep, gr, gθ, negF, constOne]
    have h11 : roundG A B 1 1 x = B (x 1) := by
      simp [roundG, diag, roundDiag, sep, gr, gθ, constOne]
    have h01 : roundG A B 0 1 x = 0 := by
      simp [roundG, diag]
    rw [h22, h00, h11, h01]
    refine ⟨pow_pos hr 2, ?_⟩
    have h := hAB _ hx.2.1
    linarith
  inverse := by
    intro x hx i k
    have h := hAB _ hx.2.1
    exact roundG_mul_roundGinv_of_ne (hpos _ hx.2.1).ne' hx.sin_ne (left_ne_zero_of_mul h.ne')
      (right_ne_zero_of_mul h.ne') i k

/-- Where Schwarzschild's clock function is not zero, the ruler function is one over it, so the
product of the two is one. -/
theorem schwA_mul_schwB_of_ne {M r : ℝ} (h : schwA M r ≠ 0) : schwA M r * schwB M r = 1 := by
  have e : schwB M r = (schwA M r)⁻¹ := rfl
  rw [e]
  exact mul_inv_cancel₀ h

/-- **The assumptions of the statement in coordinates can be met, outside the rim.**
Schwarzschild's own table for a positive mass, at all times and outside the rim, is a round
table, and the size of its spheres is a usable distance there. -/
theorem exactlyWhenAssumptionsMet : ExactlyWhenAssumptionsMet := by
  intro M hM
  have hpos : ∀ r ∈ Ioi (2 * M), (0 : ℝ) < r := fun r hr ↦ by
    have h : 2 * M < r := hr
    linarith
  have hA0 : ∀ r ∈ Ioi (2 * M), schwA M r ≠ 0 := fun r hr ↦
    (Curved.schwA_pos_outside (hpos r hr) hr).ne'
  refine ⟨roundSetting_roundG isOpen_Ioi isPreconnected_Ioi hpos
    (fun r hr ↦ Curved.smooth_schwA M (hpos r hr).ne')
    (fun r hr ↦ Curved.smooth_schwB M (hpos r hr).ne' (hA0 r hr))
    (fun r hr ↦ by rw [schwA_mul_schwB_of_ne (hA0 r hr)]; exact one_pos), ?_⟩
  intro x hx
  exact sizeSlopeOf_roundG_ne_zero (hA0 _ hx.2.1) (hpos _ hx.2.1).ne'

/-- **The assumptions can be met inside the rim as well.** Schwarzschild's own table for a
positive mass, at all times and for distance labels between the centre and the rim, is a round
table too, and the size of its spheres is a usable distance there. Both the clock function and
the ruler function are negative there, so the distance label is the time. -/
theorem exactlyWhenAssumptionsMetInside : ExactlyWhenAssumptionsMetInside := by
  intro M _
  have hpos : ∀ r ∈ Ioo 0 (2 * M), (0 : ℝ) < r := fun r hr ↦ hr.1
  have hA0 : ∀ r ∈ Ioo 0 (2 * M), schwA M r ≠ 0 := fun r hr ↦
    (Curved.schwA_neg_inside hr.1 hr.2).ne
  refine ⟨roundSetting_roundG isOpen_Ioo isPreconnected_Ioo hpos
    (fun r hr ↦ Curved.smooth_schwA M (hpos r hr).ne')
    (fun r hr ↦ Curved.smooth_schwB M (hpos r hr).ne' (hA0 r hr))
    (fun r hr ↦ by rw [schwA_mul_schwB_of_ne (hA0 r hr)]; exact one_pos), ?_⟩
  intro x hx
  exact sizeSlopeOf_roundG_ne_zero (hA0 _ hx.2.1) (hpos _ hx.2.1).ne'

end GravityInLean
