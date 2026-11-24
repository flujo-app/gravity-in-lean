/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Turns.Basic
public import GravityInLean.Turns.BracketFderiv

import Mathlib.Tactic

/-!
# From two relations to the three standard turns

Board item `task:turns-turn-algebra`. Step 5 of the route, the computation with sines, cosines
and the cotangent. Let `Φ` be a change of coordinates and `v₀`, `v₁`, `v₂` three arrows at `Φ y`.
If

* the slope of `Φ` along `y 3` is `v₂`,
* the slope of `Φ` along `y 2` is `cos (y 3) • v₀ - sin (y 3) • v₁`,
* and `sin (y 3) • v₀ + cos (y 3) • v₁ + (cos (y 2) / sin (y 2)) • v₂ = 0`,

then the table of slopes of `Φ` turns the three standard turns `stdTurn = ![rotY, rotX, rotZ]` at
`y` into `v₀`, `v₁`, `v₂`.
-/

@[expose] public section

namespace GravityInLean.Turns

open GravityInLean Real

/-- The table of slopes of `Φ` turns the standard turns into `v₀`, `v₁`, `v₂`, given the slopes
of `Φ` along `y 2` and `y 3` and one relation between the three arrows. -/
theorem turns_of_relations {Φ : Coords 4 → Coords 4} {y : Coords 4}
    (hΦ : DifferentiableAt ℝ Φ y) {v₀ v₁ v₂ : Coords 4}
    (h3 : fderiv ℝ Φ y (Pi.single 3 1) = v₂)
    (h2 : fderiv ℝ Φ y (Pi.single 2 1) = cos (y 3) • v₀ - sin (y 3) • v₁)
    (hrel : sin (y 3) • v₀ + cos (y 3) • v₁ + (cos (y 2) / sin (y 2)) • v₂ = 0) (α : Fin 4) :
    ∑ μ, jac Φ α μ y * stdTurn 0 μ y = v₀ α ∧ ∑ μ, jac Φ α μ y * stdTurn 1 μ y = v₁ α ∧
      ∑ μ, jac Φ α μ y * stdTurn 2 μ y = v₂ α := by
  have j2 : jac Φ α 2 y = cos (y 3) * v₀ α - sin (y 3) * v₁ α := by
    rw [jac_eq_fderiv hΦ, h2]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have j3 : jac Φ α 3 y = v₂ α := by rw [jac_eq_fderiv hΦ, h3]
  have hr : sin (y 3) * v₀ α + cos (y 3) * v₁ α + cos (y 2) / sin (y 2) * v₂ α = 0 := by
    have h := congrFun hrel α
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    exact h
  have e0 : ∑ μ, jac Φ α μ y * stdTurn 0 μ y
      = jac Φ α 2 y * cos (y 3) + jac Φ α 3 y * (-(cos (y 2) / sin (y 2)) * sin (y 3)) := by
    simp [Fin.sum_univ_four, stdTurn, rotY, sepA, constOne, negCot]
  have e1 : ∑ μ, jac Φ α μ y * stdTurn 1 μ y
      = jac Φ α 2 y * -sin (y 3) + jac Φ α 3 y * (-(cos (y 2) / sin (y 2)) * cos (y 3)) := by
    simp [Fin.sum_univ_four, stdTurn, rotX, sepA, constOne, negCot, negSin]
  have e2 : ∑ μ, jac Φ α μ y * stdTurn 2 μ y = jac Φ α 3 y := by
    simp [Fin.sum_univ_four, stdTurn, rotZ]
  refine ⟨?_, ?_, ?_⟩
  · rw [e0, j2, j3]
    linear_combination (-sin (y 3)) * hr + v₀ α * Real.sin_sq_add_cos_sq (y 3)
  · rw [e1, j2, j3]
    linear_combination (-cos (y 3)) * hr + v₁ α * Real.sin_sq_add_cos_sq (y 3)
  · rw [e2, j3]

end GravityInLean.Turns
