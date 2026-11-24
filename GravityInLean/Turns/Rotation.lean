/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.Real.Sqrt

import Mathlib.Tactic

/-!
# A rotation of three numbers with a given unit row

Board item `task:turns-rotation`. Given three numbers `n` whose squares add up to one, there is
a rotation `R` of three numbers (`R * Rᵀ = 1`, `det R = 1`) whose row `1` is `n`. Its rows are
`u`, `n` and `u × n`, where `u` is some unit vector at right angles to `n`.
-/

@[expose] public section

namespace GravityInLean.Turns

/-- For any three numbers `n` there are three numbers `u` whose squares add up to one, and which
are at right angles to `n`. -/
theorem exists_unit_orthogonal (n : Fin 3 → ℝ) :
    ∃ u : Fin 3 → ℝ, u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1 ∧
      u 0 * n 0 + u 1 * n 1 + u 2 * n 2 = 0 := by
  by_cases h : n 0 ^ 2 + n 1 ^ 2 = 0
  · have h0' : n 0 ^ 2 = 0 := by linarith [sq_nonneg (n 0), sq_nonneg (n 1)]
    have h0 : n 0 = 0 := by simpa using h0'
    refine ⟨![1, 0, 0], ?_, ?_⟩
    · change (1 : ℝ) ^ 2 + 0 ^ 2 + 0 ^ 2 = 1
      norm_num
    · change (1 : ℝ) * n 0 + 0 * n 1 + 0 * n 2 = 0
      rw [h0]
      ring
  · have hx : 0 < n 0 ^ 2 + n 1 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t ^ 2 * (n 0 ^ 2 + n 1 ^ 2) = 1 := by
      refine ⟨(Real.sqrt (n 0 ^ 2 + n 1 ^ 2))⁻¹, ?_⟩
      rw [inv_pow, Real.sq_sqrt hx.le]
      exact inv_mul_cancel₀ hx.ne'
    refine ⟨![n 1 * t, -(n 0 * t), 0], ?_, ?_⟩
    · change (n 1 * t) ^ 2 + (-(n 0 * t)) ^ 2 + (0 : ℝ) ^ 2 = 1
      linear_combination ht
    · change n 1 * t * n 0 + -(n 0 * t) * n 1 + 0 * n 2 = 0
      ring

/-- For three numbers `n` whose squares add up to one there is a rotation of three numbers
(a table `R` with `R * Rᵀ = 1` and `det R = 1`) whose row `1` is `n`. -/
theorem exists_rotation_row (n : Fin 3 → ℝ) (hn : ∑ j, n j ^ 2 = 1) :
    ∃ R : Matrix (Fin 3) (Fin 3) ℝ, R * R.transpose = 1 ∧ R.det = 1 ∧ ∀ j, R 1 j = n j := by
  rw [Fin.sum_univ_three] at hn
  obtain ⟨u, h1, h3⟩ := exists_unit_orthogonal n
  refine ⟨!![u 0, u 1, u 2; n 0, n 1, n 2;
    u 1 * n 2 - u 2 * n 1, u 2 * n 0 - u 0 * n 2, u 0 * n 1 - u 1 * n 0], ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_three]
      linear_combination h1
    · simp [Matrix.mul_apply, Fin.sum_univ_three]
      linear_combination h3
    · simp [Matrix.mul_apply, Fin.sum_univ_three]
      ring
    · simp [Matrix.mul_apply, Fin.sum_univ_three]
      linear_combination h3
    · simp [Matrix.mul_apply, Fin.sum_univ_three]
      linear_combination hn
    · simp [Matrix.mul_apply, Fin.sum_univ_three]
      ring
    · simp [Matrix.mul_apply, Fin.sum_univ_three]
      ring
    · simp [Matrix.mul_apply, Fin.sum_univ_three]
      ring
    · simp [Matrix.mul_apply, Fin.sum_univ_three]
      linear_combination (n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2) * h1 + hn -
        (u 0 * n 0 + u 1 * n 1 + u 2 * n 2) * h3
  · simp [Matrix.det_fin_three]
    linear_combination (n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2) * h1 + hn -
      (u 0 * n 0 + u 1 * n 1 + u 2 * n 2) * h3
  · intro j
    fin_cases j <;> rfl

end GravityInLean.Turns
