/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Turns.Basic
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Analysis.Calculus.FDeriv.Add

import Mathlib.Tactic

/-!
# Fields that combine like turns still do so after a fixed rotation

Board item `task:turns-rotate-bracket`.

Three fields `X 0`, `X 1`, `X 2` combine like turns when the bracket of two of them is the
third. Mix them by a fixed rotation `R` (a table of three by three numbers with `R * Rᵀ = 1`
and `det R = 1`): the three new fields `∑ j, R i j • X j` combine like turns as well. The
reason: the bracket is linear in each field, and each row of a rotation is the cross product of
the other two.
-/

@[expose] public section

namespace GravityInLean.Turns

open Matrix

/-- Each row of a rotation is the cross product of the other two rows, in the order
`0 × 1 = 2`, `1 × 2 = 0`, `2 × 0 = 1`. -/
theorem rotation_rows_cross (R : Matrix (Fin 3) (Fin 3) ℝ) (h : R * R.transpose = 1)
    (hd : R.det = 1) :
    crossProduct (R 0) (R 1) = R 2 ∧ crossProduct (R 1) (R 2) = R 0 ∧
      crossProduct (R 2) (R 0) = R 1 := by
  have hadj : R.adjugate = R.transpose := by
    calc R.adjugate = R.adjugate * (R * R.transpose) := by rw [h, mul_one]
      _ = (R.adjugate * R) * R.transpose := by rw [mul_assoc]
      _ = R.transpose := by rw [Matrix.adjugate_mul, hd, one_smul, one_mul]
  rw [Matrix.adjugate_fin_three] at hadj
  have e : ∀ i j, _ = _ := fun i j ↦ congrFun (congrFun hadj i) j
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e10 := e 1 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  have e22 := e 2 2
  simp [Matrix.transpose_apply] at e00 e01 e02 e10 e11 e12 e20 e21 e22
  refine ⟨?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;> simp [cross_apply] <;> linarith

/-- The bracket of two mixes of three fields, written out: the mix whose three numbers are the
cross product of the numbers of the two mixes, when the three fields combine like turns at the
point `x`. -/
theorem lieB_mix {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Fin 3 → E → E) (u v : Fin 3 → ℝ)
    (x : E) (hX : ∀ i, DifferentiableAt ℝ (X i) x)
    (h01 : lieB (X 0) (X 1) x = X 2 x) (h12 : lieB (X 1) (X 2) x = X 0 x)
    (h20 : lieB (X 2) (X 0) x = X 1 x) :
    lieB (fun y ↦ ∑ j, u j • X j y) (fun y ↦ ∑ j, v j • X j y) x =
      (u 1 * v 2 - u 2 * v 1) • X 0 x + (u 2 * v 0 - u 0 * v 2) • X 1 x +
        (u 0 * v 1 - u 1 * v 0) • X 2 x := by
  have hY : ∀ w : Fin 3 → ℝ, HasFDerivAt (fun y ↦ ∑ j, w j • X j y)
      (∑ j, w j • fderiv ℝ (X j) x) x := fun w ↦
    HasFDerivAt.fun_sum fun j _ ↦ (hX j).hasFDerivAt.fun_const_smul (w j)
  unfold lieB at h01 h12 h20 ⊢
  rw [(hY u).fderiv, (hY v).fderiv]
  simp only [Fin.sum_univ_three, _root_.add_apply, _root_.smul_apply,
    map_add, map_smul]
  linear_combination (norm := module) (u 0 * v 1 - u 1 * v 0) • h01 +
    (u 1 * v 2 - u 2 * v 1) • h12 + (u 2 * v 0 - u 0 * v 2) • h20

/-- Three fields that combine like turns at the point `x` (the bracket of two is the third)
still do so after they are mixed by a fixed rotation `R`. -/
theorem likeTurns_rotate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Fin 3 → E → E) (R : Matrix (Fin 3) (Fin 3) ℝ) (h : R * R.transpose = 1) (hd : R.det = 1)
    (x : E) (hX : ∀ i, DifferentiableAt ℝ (X i) x)
    (h01 : lieB (X 0) (X 1) x = X 2 x) (h12 : lieB (X 1) (X 2) x = X 0 x)
    (h20 : lieB (X 2) (X 0) x = X 1 x) :
    lieB (fun y ↦ ∑ j, R 0 j • X j y) (fun y ↦ ∑ j, R 1 j • X j y) x = ∑ j, R 2 j • X j x ∧
    lieB (fun y ↦ ∑ j, R 1 j • X j y) (fun y ↦ ∑ j, R 2 j • X j y) x = ∑ j, R 0 j • X j x ∧
    lieB (fun y ↦ ∑ j, R 2 j • X j y) (fun y ↦ ∑ j, R 0 j • X j y) x = ∑ j, R 1 j • X j x := by
  have key : ∀ a b c : Fin 3, crossProduct (R a) (R b) = R c →
      lieB (fun y ↦ ∑ j, R a j • X j y) (fun y ↦ ∑ j, R b j • X j y) x = ∑ j, R c j • X j x := by
    intro a b c hc
    rw [lieB_mix X (R a) (R b) x hX h01 h12 h20, Fin.sum_univ_three, ← hc, cross_apply]
    rfl
  obtain ⟨c01, c12, c20⟩ := rotation_rows_cross R h hd
  exact ⟨key 0 1 2 c01, key 1 2 0 c12, key 2 0 1 c20⟩

end GravityInLean.Turns
