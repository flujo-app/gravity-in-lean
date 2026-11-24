/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Curvature
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import Mathlib.Tactic

/-!
# Coordinates that fit the turns: completing two arrows to four

Board item `task:turns-complete`. Two arrows of four numbers that point in different directions
can be completed, by two more arrows, to four arrows that point in four independent directions.
"Independent" is measured by the determinant of the table whose columns are the four arrows.

* `det_fin_four`: the determinant of a table of four rows and four columns, written out.
* `det_columns`: the same for a table given by its four columns.
* `exists_complete`: two independent arrows can be completed to four independent ones.
* `det_complete_add`: adding multiples of the last two columns to the first two does not change
  the determinant.
-/

@[expose] public section

namespace GravityInLean.Turns

open Matrix

/-- The determinant of a table of four rows and four columns, written out: the small
determinants of two rows in the first two columns, each times the small determinant of the
other two rows in the last two columns, with alternating signs. -/
theorem det_fin_four (M : Matrix (Fin 4) (Fin 4) ℝ) :
    M.det =
      (M 0 0 * M 1 1 - M 1 0 * M 0 1) * (M 2 2 * M 3 3 - M 3 2 * M 2 3)
      - (M 0 0 * M 2 1 - M 2 0 * M 0 1) * (M 1 2 * M 3 3 - M 3 2 * M 1 3)
      + (M 0 0 * M 3 1 - M 3 0 * M 0 1) * (M 1 2 * M 2 3 - M 2 2 * M 1 3)
      + (M 1 0 * M 2 1 - M 2 0 * M 1 1) * (M 0 2 * M 3 3 - M 3 2 * M 0 3)
      - (M 1 0 * M 3 1 - M 3 0 * M 1 1) * (M 0 2 * M 2 3 - M 2 2 * M 0 3)
      + (M 2 0 * M 3 1 - M 3 0 * M 2 1) * (M 0 2 * M 1 3 - M 1 2 * M 0 3) := by
  -- Which rows and columns are left when one is struck out.
  have hs : ∀ i : Fin 3, (Fin.succ i : Fin 4) = ![1, 2, 3] i := by decide
  have h0 : ∀ k : Fin 3, (0 : Fin 4).succAbove k = ![1, 2, 3] k := by decide
  have h1 : ∀ k : Fin 3, (1 : Fin 4).succAbove k = ![0, 2, 3] k := by decide
  have h2 : ∀ k : Fin 3, (2 : Fin 4).succAbove k = ![0, 1, 3] k := by decide
  have h3 : ∀ k : Fin 3, (3 : Fin 4).succAbove k = ![0, 1, 2] k := by decide
  -- Expand along the first row, then use the written-out determinant of three by three.
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply, hs, h0, h1, h2, h3]
  norm_num
  ring

/-- The determinant of the table whose columns are the four arrows `v₀`, `v₁`, `v₂`, `v₃`,
written out. -/
theorem det_columns (v₀ v₁ v₂ v₃ : Coords 4) :
    (Matrix.of fun α μ : Fin 4 ↦ (![v₀, v₁, v₂, v₃] μ) α).det =
      (v₀ 0 * v₁ 1 - v₀ 1 * v₁ 0) * (v₂ 2 * v₃ 3 - v₂ 3 * v₃ 2)
      - (v₀ 0 * v₁ 2 - v₀ 2 * v₁ 0) * (v₂ 1 * v₃ 3 - v₂ 3 * v₃ 1)
      + (v₀ 0 * v₁ 3 - v₀ 3 * v₁ 0) * (v₂ 1 * v₃ 2 - v₂ 2 * v₃ 1)
      + (v₀ 1 * v₁ 2 - v₀ 2 * v₁ 1) * (v₂ 0 * v₃ 3 - v₂ 3 * v₃ 0)
      - (v₀ 1 * v₁ 3 - v₀ 3 * v₁ 1) * (v₂ 0 * v₃ 2 - v₂ 2 * v₃ 0)
      + (v₀ 2 * v₁ 3 - v₀ 3 * v₁ 2) * (v₂ 0 * v₃ 1 - v₂ 1 * v₃ 0) := by
  rw [det_fin_four]
  simp only [Matrix.of_apply, Matrix.cons_val, Fin.isValue]

/-- Two independent arrows `a`, `b` of four numbers (independent: the square of the area they
span is positive) can be completed by two more arrows `e₁`, `e₂` to four independent arrows:
the determinant of the table with columns `e₁`, `e₂`, `a`, `b` is not zero. -/
theorem exists_complete (a b : Coords 4) (h : 0 < (a ⬝ᵥ a) * (b ⬝ᵥ b) - (a ⬝ᵥ b) ^ 2) :
    ∃ e₁ e₂ : Coords 4, (Matrix.of fun α μ : Fin 4 ↦ (![e₁, e₂, a, b] μ) α).det ≠ 0 := by
  -- The square of the area is the sum of the squares of the six small determinants.
  have key : (a ⬝ᵥ a) * (b ⬝ᵥ b) - (a ⬝ᵥ b) ^ 2 =
      (a 0 * b 1 - a 1 * b 0) ^ 2 + (a 0 * b 2 - a 2 * b 0) ^ 2 + (a 0 * b 3 - a 3 * b 0) ^ 2
        + (a 1 * b 2 - a 2 * b 1) ^ 2 + (a 1 * b 3 - a 3 * b 1) ^ 2
        + (a 2 * b 3 - a 3 * b 2) ^ 2 := by
    simp only [dotProduct, Fin.sum_univ_four]
    ring
  rw [key] at h
  -- So one of the six is not zero; complete by the two basic arrows of the other two places.
  by_cases h23 : a 2 * b 3 - a 3 * b 2 = 0; swap
  · refine ⟨![1, 0, 0, 0], ![0, 1, 0, 0], fun hz ↦ h23 ?_⟩
    rw [det_columns] at hz
    simp at hz
    linarith
  by_cases h13 : a 1 * b 3 - a 3 * b 1 = 0; swap
  · refine ⟨![1, 0, 0, 0], ![0, 0, 1, 0], fun hz ↦ h13 ?_⟩
    rw [det_columns] at hz
    simp at hz
    linarith
  by_cases h12 : a 1 * b 2 - a 2 * b 1 = 0; swap
  · refine ⟨![1, 0, 0, 0], ![0, 0, 0, 1], fun hz ↦ h12 ?_⟩
    rw [det_columns] at hz
    simp at hz
    linarith
  by_cases h03 : a 0 * b 3 - a 3 * b 0 = 0; swap
  · refine ⟨![0, 1, 0, 0], ![0, 0, 1, 0], fun hz ↦ h03 ?_⟩
    rw [det_columns] at hz
    simp at hz
    linarith
  by_cases h02 : a 0 * b 2 - a 2 * b 0 = 0; swap
  · refine ⟨![0, 1, 0, 0], ![0, 0, 0, 1], fun hz ↦ h02 ?_⟩
    rw [det_columns] at hz
    simp at hz
    linarith
  by_cases h01 : a 0 * b 1 - a 1 * b 0 = 0; swap
  · refine ⟨![0, 0, 1, 0], ![0, 0, 0, 1], fun hz ↦ h01 ?_⟩
    rw [det_columns] at hz
    simp at hz
    linarith
  -- All six zero: the area would be zero.
  rw [h01, h02, h03, h12, h13, h23] at h
  norm_num at h

/-- Adding multiples of the last two columns `a`, `b` to the first two columns `e₁`, `e₂` does
not change the determinant of the table with columns `e₁`, `e₂`, `a`, `b`. -/
theorem det_complete_add (e₁ e₂ a b : Coords 4) (c₁ d₁ c₂ d₂ : ℝ) :
    (Matrix.of fun α μ : Fin 4 ↦
        (![e₁ + c₁ • a + d₁ • b, e₂ + c₂ • a + d₂ • b, a, b] μ) α).det =
      (Matrix.of fun α μ : Fin 4 ↦ (![e₁, e₂, a, b] μ) α).det := by
  rw [det_columns, det_columns]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end GravityInLean.Turns
