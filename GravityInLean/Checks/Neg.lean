/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.Tests
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Turning all signs of a length measure round

Board item `task:checks-neg`. Tests 12 and 4 of `Goals/Tests.lean`.

Some textbooks give time the sign minus and space the sign plus, others the other way round.
This project uses the first. What happens to its definitions when a length measure is written the
other way, with all signs turned round?

* **"Empty" does not notice** (`Tests.isEmptyOnNegIff`, on any curved space). The connection of a
  length measure is also the connection of the measure with all signs turned round
  (`IsConnectionOf.neg`): the rule "no twist" does not mention the length measure, and both sides
  of the rule "keeps lengths" change their sign together. The curvature is made from the
  connection alone.
* **Schwarzschild's table with all signs turned round is therefore still empty**
  (`Tests.schwFlippedIsEmpty`).
* **But it is not a space-time in the sense used here** (`Tests.schwFlippedNotSpaceTime`): it has
  three directions of negative squared length that are at right angles to each other, not one.
* **And it is not round** (`Tests.schwFlippedNotRound`): the lengths on the spheres are negative,
  and "round" asks for positive ones.

So the definitions "space-time" and "round" do fix which sign time gets, and "empty" does not.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean

open Real Set VectorField

open scoped Manifold ContDiff

namespace Curved

/-! ## On any curved space: the connection and "empty" -/

section AnySpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The connection of a length measure is also the connection of the same measure with all signs
turned round. -/
theorem IsConnectionOf.neg {g : LengthMeasure I M} {cov : Transport I M} {s : Set M}
    (h : IsConnectionOf g cov s) : IsConnectionOf (-g) cov s where
  isOpen := h.isOpen
  isConnection := h.isConnection
  noTwist := h.noTwist
  keepsLengths := by
    intro x hx Y Z hY hZ v
    have key := h.keepsLengths x hx Y Z hY hZ v
    have e : (fun y ↦ (-g) y (Y y) (Z y)) = -(fun y ↦ g y (Y y) (Z y)) := rfl
    rw [e, mvfderiv_neg]
    calc (-(d% (fun y ↦ g y (Y y) (Z y)) x)) v
        = -(d% (fun y ↦ g y (Y y) (Z y)) x v) := rfl
      _ = -(g x (cov Y x v) (Z x) + g x (Y x) (cov Z x v)) := by rw [key]
      _ = (-g) x (cov Y x v) (Z x) + (-g) x (Y x) (cov Z x v) := neg_add _ _

/-- A length measure and the same measure with all signs turned round have the same
connections. -/
theorem isConnectionOf_neg_iff {g : LengthMeasure I M} {cov : Transport I M} {s : Set M} :
    IsConnectionOf (-g) cov s ↔ IsConnectionOf g cov s :=
  ⟨fun h ↦ neg_neg g ▸ h.neg, IsConnectionOf.neg⟩

/-- Space is empty for a length measure exactly when it is empty for the same measure with all
signs turned round. -/
theorem isEmptyOn_neg_iff [FiniteDimensional ℝ E] {g : LengthMeasure I M} {s : Set M} :
    IsEmptyOn (-g) s ↔ IsEmptyOn g s :=
  ⟨fun ⟨cov, hc, hr⟩ ↦ ⟨cov, isConnectionOf_neg_iff.mp hc, hr⟩,
    fun ⟨cov, hc, hr⟩ ↦ ⟨cov, hc.neg, hr⟩⟩

end AnySpace

/-- **Test 12.** Turning all signs of a length measure round does not change whether space is
empty, on any curved space. -/
theorem Tests.isEmptyOnNegIff.{u, v, w} : Tests.IsEmptyOnNegIff.{u, v, w} := by
  intro E H _ _ _ _ I M _ _ _ g s
  exact isEmptyOn_neg_iff

/-! ## A round table with all signs turned round -/

section Flipped

/-- On flat space, turning the signs round before or after reading the two-slot function as a
length measure is the same. -/
theorem flatMeasure_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E → E →L[ℝ] E →L[ℝ] ℝ) : flatMeasure (-T) = -flatMeasure T := rfl

/-- The time entry of a round table: minus the clock function. -/
theorem roundDiag_zero (A B : ℝ → ℝ) (x : Coords 4) : roundDiag A B 0 x = -A (x 1) := by
  simp [roundDiag, sep, gr, gθ, negF, constOne]

/-- The distance entry of a round table: the ruler function. -/
theorem roundDiag_one (A B : ℝ → ℝ) (x : Coords 4) : roundDiag A B 1 x = B (x 1) := by
  simp [roundDiag, sep, gr, gθ, constOne]

/-- The entry of a round table for the angle from the pole: `r²`. -/
theorem roundDiag_two (A B : ℝ → ℝ) (x : Coords 4) : roundDiag A B 2 x = x 1 ^ 2 := by
  simp [roundDiag, sep, gr, gθ, sqF, constOne]

/-- The entry of a round table for the angle around the axis: `r² sin²θ`. -/
theorem roundDiag_three (A B : ℝ → ℝ) (x : Coords 4) :
    roundDiag A B 3 x = x 1 ^ 2 * sin (x 2) ^ 2 := by
  simp [roundDiag, sep, gr, gθ, sqF, sin2]

/-- A round table with all signs turned round, written out: `A dt² - B dr² - r² dθ² -
r² sin²θ dφ²`. -/
theorem flipped_apply (A B : ℝ → ℝ) (x v w : Coords 4) :
    flatMeasure (-tableMeasure (roundG A B)) x v w
      = A (x 1) * v 0 * w 0 - B (x 1) * v 1 * w 1 - x 1 ^ 2 * v 2 * w 2
        - x 1 ^ 2 * sin (x 2) ^ 2 * v 3 * w 3 := by
  have e : flatMeasure (-tableMeasure (roundG A B)) x v w
      = -tableMeasure (roundG A B) x v w := rfl
  rw [e, round_measure_apply, Fin.sum_univ_four, roundDiag_zero, roundDiag_one, roundDiag_two,
    roundDiag_three]
  ring

/-- A round table with all signs turned round and a positive ruler function does not have one
time direction: the distance direction and the direction of the angle from the pole both have
negative squared length and are at right angles to each other, so whatever step is offered as
"time", some step at right angles to it has a squared length that is not positive. -/
theorem flipped_not_oneTime {A B : ℝ → ℝ} {x : Coords 4} (hB : 0 < B (x 1)) (hr : x 1 ≠ 0) :
    ¬ HasOneTimeDirection fun v w : Coords 4 ↦
      flatMeasure (-tableMeasure (roundG A B)) x v w := by
  rintro ⟨t, -, hpos⟩
  have hr2 : 0 < x 1 ^ 2 := sq_pos_iff.mpr hr
  -- No step `(0, a, b, 0)` other than zero is at right angles to `t`.
  have key : ∀ a b : ℝ, a ≠ 0 ∨ b ≠ 0 → B (x 1) * t 1 * a + x 1 ^ 2 * t 2 * b = 0 → False := by
    intro a b hab hort
    have h0 : (![0, a, b, 0] : Coords 4) 0 = 0 := rfl
    have h1 : (![0, a, b, 0] : Coords 4) 1 = a := rfl
    have h2 : (![0, a, b, 0] : Coords 4) 2 = b := rfl
    have h3 : (![0, a, b, 0] : Coords 4) 3 = 0 := rfl
    have hne : (![0, a, b, 0] : Coords 4) ≠ 0 := by
      intro h
      rcases hab with ha | hb
      · exact ha (by rw [← h1, h]; rfl)
      · exact hb (by rw [← h2, h]; rfl)
    have hort' : flatMeasure (-tableMeasure (roundG A B)) x t ![0, a, b, 0] = 0 := by
      rw [flipped_apply, h0, h1, h2, h3]
      linarith
    have hvv : 0 < flatMeasure (-tableMeasure (roundG A B)) x ![0, a, b, 0] ![0, a, b, 0] :=
      hpos _ hort' hne
    rw [flipped_apply, h0, h1, h2, h3] at hvv
    nlinarith [mul_nonneg hB.le (mul_self_nonneg a), mul_nonneg hr2.le (mul_self_nonneg b)]
  by_cases h1 : t 1 = 0
  · exact key 1 0 (Or.inl one_ne_zero) (by rw [h1]; ring)
  · exact key (x 1 ^ 2 * t 2) (-(B (x 1) * t 1))
      (Or.inr (neg_ne_zero.mpr (mul_ne_zero hB.ne' h1))) (by ring)

/-- A point outside the rim and off the poles, for any mass: time `0`, distance `2|M| + 1`, on
the equator. -/
theorem witness_mem_outside (M : ℝ) : (![0, 2 * |M| + 1, π / 2, 0] : Coords 4) ∈ outside M := by
  refine ⟨?_, ?_, ?_⟩
  · change (0 : ℝ) < 2 * |M| + 1
    linarith [abs_nonneg M]
  · change 2 * M < 2 * |M| + 1
    linarith [le_abs_self M]
  · change sin (π / 2) ≠ 0
    rw [sin_pi_div_two]
    exact one_ne_zero

end Flipped

/-! ## Test 4: Schwarzschild's table with all signs turned round -/

/-- **Test 4, third part.** Schwarzschild's table with all signs turned round is still empty. -/
theorem Tests.schwFlippedIsEmpty : Tests.SchwFlippedIsEmpty := by
  intro M
  rw [flatMeasure_neg]
  exact isEmptyOn_neg_iff.mpr (schwarzschild_isEmptyOn M)

/-- **Test 4, first part.** Schwarzschild's table with all signs turned round is not a space-time
in the sense used here: it does not have one time direction. -/
theorem Tests.schwFlippedNotSpaceTime : Tests.SchwFlippedNotSpaceTime := by
  intro M h
  obtain ⟨x, hx⟩ : ∃ x : Coords 4, x ∈ outside M := ⟨_, witness_mem_outside M⟩
  have hB : 0 < schwB M (x 1) := inv_pos.mpr (schwA_pos_outside hx.1 hx.2.1)
  exact flipped_not_oneTime (A := schwA M) (B := schwB M) hB hx.1.ne' (h.oneTime x hx)

/-- **Test 4, second part.** Schwarzschild's table with all signs turned round is not round: the
step around the axis lies in the surface that the turns sweep out, and its squared length is
negative. -/
theorem Tests.schwFlippedNotRound : Tests.SchwFlippedNotRound := by
  intro M h
  obtain ⟨x, hx⟩ : ∃ x : Coords 4, x ∈ outside M := ⟨_, witness_mem_outside M⟩
  have hv : (Pi.single 3 1 : Coords 4)
      ∈ Submodule.span ℝ (Set.range fun i : Fin 3 ↦ (turns i x : Coords 4)) := by
    rw [← rotZ_eq x]
    exact Submodule.subset_span ⟨2, rfl⟩
  have h0 : (Pi.single 3 1 : Coords 4) 0 = 0 := Pi.single_eq_of_ne (by decide) 1
  have h1 : (Pi.single 3 1 : Coords 4) 1 = 0 := Pi.single_eq_of_ne (by decide) 1
  have h2 : (Pi.single 3 1 : Coords 4) 2 = 0 := Pi.single_eq_of_ne (by decide) 1
  have h3 : (Pi.single 3 1 : Coords 4) 3 = 1 := Pi.single_eq_same 3 1
  have hne : (Pi.single 3 1 : Coords 4) ≠ 0 := by
    intro h'
    rw [h'] at h3
    exact zero_ne_one h3
  have hpos : 0 < flatMeasure (-tableMeasure (roundG (schwA M) (schwB M))) x
      (Pi.single 3 1) (Pi.single 3 1) := h.positive x hx _ hv hne
  rw [flipped_apply, h0, h1, h2, h3] at hpos
  nlinarith [mul_pos (sq_pos_iff.mpr hx.1.ne') (sq_pos_iff.mpr hx.2.2)]

end Curved

end GravityInLean
