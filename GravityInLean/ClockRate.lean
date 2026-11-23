/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt

import Mathlib.Tactic

/-!
# Piece A: two ways of writing the same clock rate

Near one heavy mass `M` that does not spin, a clock standing still runs slower than a clock far
away.
There are two common ways to write how much slower.

* On a flat "map" of space, where the distance from the mass is called `ρ`, the rate is
  `(1 - s) / (1 + s)` with `s = M / (2 ρ)`. This is the form the interactive page
  "Slow Clocks, Bent Light" uses, because the map is easy to draw.
* In the textbooks the rate is `√(1 - 2 M / r)`, where `r` is the distance you get by measuring
  the length of a circle around the mass and dividing by `2 π`.

The two distances are related by `r = ρ (1 + s)²`. This file proves that the two formulas then give
exactly the same number, for every `ρ` outside the rim of a black hole (`ρ > M / 2`).

Units: lengths and the mass are measured so that the speed of light and Newton's constant are 1.
-/

@[expose] public section

namespace GravityInLean

/-- How deep a spot is, on the map: `s = M / (2 ρ)`. -/
noncomputable def depth (M ρ : ℝ) : ℝ := M / (2 * ρ)

/-- The textbook distance (length of a circle around the mass, divided by `2 π`)
belonging to the map distance `ρ`. -/
noncomputable def circleRadius (M ρ : ℝ) : ℝ := ρ * (1 + depth M ρ) ^ 2

/-- The clock rate as the page computes it, from the map distance. -/
noncomputable def clockRateMap (M ρ : ℝ) : ℝ := (1 - depth M ρ) / (1 + depth M ρ)

/-- The clock rate as the textbooks write it, from the circle distance. -/
noncomputable def clockRateTextbook (M r : ℝ) : ℝ := Real.sqrt (1 - 2 * M / r)

/-- Outside the rim (`ρ > M / 2`) the depth lies strictly between 0 and 1. -/
theorem depth_pos_lt_one {M ρ : ℝ} (hM : 0 < M) (hρ : M / 2 < ρ) :
    0 < depth M ρ ∧ depth M ρ < 1 := by
  have hρ0 : 0 < ρ := by linarith [half_pos hM]
  refine ⟨by unfold depth; positivity, ?_⟩
  unfold depth
  rw [div_lt_one (by positivity)]
  linarith

/-- **Piece A.** The page's formula and the textbook formula for the clock rate agree. -/
theorem clockRateMap_eq_clockRateTextbook {M ρ : ℝ} (hM : 0 < M) (hρ : M / 2 < ρ) :
    clockRateMap M ρ = clockRateTextbook M (circleRadius M ρ) := by
  obtain ⟨hs0, hs1⟩ := depth_pos_lt_one hM hρ
  have hρ0 : 0 < ρ := by linarith [half_pos hM]
  have hnonneg : 0 ≤ (1 - depth M ρ) / (1 + depth M ρ) := by
    apply div_nonneg <;> linarith
  -- the heart of it: `1 - 2 M / r` is the square of the page's rate
  have key : 1 - 2 * M / (ρ * (1 + depth M ρ) ^ 2) = ((1 - depth M ρ) / (1 + depth M ρ)) ^ 2 := by
    have h2 : 2 * M = 4 * depth M ρ * ρ := by unfold depth; field_simp; ring
    have h1 : (1 + depth M ρ) ≠ 0 := by linarith
    rw [h2]
    field_simp
    ring
  unfold clockRateMap clockRateTextbook circleRadius
  rw [key, Real.sqrt_sq hnonneg]

/-- The same fact with nothing hidden in definitions, for readers who want to see the formula. -/
theorem clockRate_identity {M ρ : ℝ} (hM : 0 < M) (hρ : M / 2 < ρ) :
    (1 - M / (2 * ρ)) / (1 + M / (2 * ρ))
      = Real.sqrt (1 - 2 * M / (ρ * (1 + M / (2 * ρ)) ^ 2)) := by
  simpa [clockRateMap, clockRateTextbook, circleRadius, depth] using
    clockRateMap_eq_clockRateTextbook hM hρ

/-- At the rim of a black hole (`ρ = M / 2`) the clock rate is zero: a clock held there does not
tick. -/
theorem clockRateMap_rim {M : ℝ} (hM : 0 < M) : clockRateMap M (M / 2) = 0 := by
  have : depth M (M / 2) = 1 := by unfold depth; field_simp
  simp [clockRateMap, this]

/-- Far away the textbook distance and the map distance differ by about `M`:
`r = ρ + M + M² / (4 ρ)`. Close in, there is more room than the map shows. -/
theorem circleRadius_eq {M ρ : ℝ} (hρ : ρ ≠ 0) :
    circleRadius M ρ = ρ + M + M ^ 2 / (4 * ρ) := by
  unfold circleRadius depth
  field_simp
  ring

end GravityInLean
