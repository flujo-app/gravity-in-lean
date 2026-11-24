/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.Kretschmann
public import GravityInLean.Global.RiemannGen

import Mathlib.Tactic

/-!
# The curvature scalar of the general round shape

The curvature scalar `kretschmann` of `Global/Kretschmann.lean`, computed for the round length
measure `-A dt² + B dρ² + S (dθ² + sin²θ dφ²)` without a cross term, from the six tables of the
full curvature in `Global/RiemannGen.lean`.

* `kretschmann_of_diagonal`: for an inverse table without entries off the diagonal, only the
  pairs of equal directions count in the sum that defines the scalar.
* `kretschmann_gen`: the scalar of the round shape without a cross term is minus the sum of
  three squares: of the curvature of the time-distance part, of how the radius of the spheres
  bends, and of the curvature of the spheres.
* `kretschmann_gen_empty`: in empty space the three squares are the same up to a number, and
  the scalar is `-12 (1 - |∇R|²)² / R⁴`, with `R` the radius of the spheres. For Schwarzschild's
  and Kruskal's space-times, where `1 - |∇R|² = 2m / R`, this is `-48 m² / R⁶`.

The sign: the textbooks' scalar `R_abcd R^abcd` is the sum of the squares; the trace of a product
of two tables of the full curvature, which `kretschmann` uses, is minus that.
-/

@[expose] public section

namespace GravityInLean

open Real

/-- The full curvature changes its sign when the two directions are swapped. -/
theorem riemM_antisymm {n : ℕ} (Γ : Fin n → Fin n → Fin n → Coords n → ℝ) (ρ μ : Fin n)
    (x : Coords n) : riemM Γ μ ρ x = -riemM Γ ρ μ x := by
  simp only [riemM]
  abel

/-- The full curvature for twice the same direction is zero. -/
theorem riemM_self {n : ℕ} (Γ : Fin n → Fin n → Fin n → Coords n → ℝ) (ρ : Fin n)
    (x : Coords n) : riemM Γ ρ ρ x = 0 := by
  simp only [riemM]
  abel

namespace Curved

/-- **For an inverse table without entries off the diagonal, only pairs of equal directions
count** in the sum that defines the curvature scalar. -/
theorem kretschmann_of_diagonal {n : ℕ} {g ginv : Fin n → Fin n → Coords n → ℝ} {x : Coords n}
    (hd : ∀ i j, i ≠ j → ginv i j x = 0) :
    kretschmann g ginv x = ∑ ρ, ∑ μ, ginv ρ ρ x * ginv μ μ x *
      (riemM (christoffel g ginv) ρ μ x * riemM (christoffel g ginv) ρ μ x).trace := by
  unfold kretschmann
  refine Finset.sum_congr rfl fun ρ _ ↦ Finset.sum_congr rfl fun μ _ ↦ ?_
  have inner : ∀ σ, ∑ τ, ginv ρ σ x * ginv μ τ x *
        (riemM (christoffel g ginv) ρ μ x * riemM (christoffel g ginv) σ τ x).trace
      = ginv ρ σ x * ginv μ μ x *
        (riemM (christoffel g ginv) ρ μ x * riemM (christoffel g ginv) σ μ x).trace := fun σ ↦
    Finset.sum_eq_single μ (fun τ _ hτ ↦ by rw [hd μ τ hτ.symm, mul_zero, zero_mul])
      (fun h ↦ absurd (Finset.mem_univ μ) h)
  simp only [inner]
  exact Finset.sum_eq_single ρ (fun σ _ hσ ↦ by rw [hd ρ σ hσ.symm, zero_mul, zero_mul])
    (fun h ↦ absurd (Finset.mem_univ ρ) h)

section Gen

variable {A B C S : ℝ → ℝ → ℝ} {x : Coords 4}

/-- Without a cross term the inverse of the round table has no entries off the diagonal. -/
theorem genGinv_diagonal (A B S : ℝ → ℝ → ℝ) (x : Coords 4) {i j : Fin 4} (hij : i ≠ j) :
    genGinv A B zero2 S i j x = 0 := by
  fin_cases i <;> fin_cases j <;> simp [genGinv, ginvTR, zero2] at hij ⊢

/-! ### The six tables, each multiplied with itself -/

/-- Time and distance: twice the square of the curvature of the time-distance part. -/
theorem trace_riemM_gen_tr (h : RegularG A B C S x) :
    (riemM (genΓ A B C S) 0 1 x * riemM (genΓ A B C S) 0 1 x).trace
      = 2 * curv2 A B C (x 0) (x 1) ^ 2 * det2 A B C (x 0) (x 1) := by
  rw [riemM_gen_tr h]
  conv_lhs => simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_four]
  simp only [det2]
  ring

/-- Time and pole angle. -/
theorem trace_riemM_gen_tθ (h : RegularG A B C S x) :
    (riemM (genΓ A B C S) 0 2 x * riemM (genΓ A B C S) 0 2 x).trace
      = -(2 * S (x 0) (x 1) * (-(B (x 0) (x 1) * bendTT A B C S (x 0) (x 1) ^ 2)
          + 2 * C (x 0) (x 1) * bendTT A B C S (x 0) (x 1) * bendTR A B C S (x 0) (x 1)
          + A (x 0) (x 1) * bendTR A B C S (x 0) (x 1) ^ 2) / det2 A B C (x 0) (x 1)) := by
  rw [riemM_gen_tθ h]
  conv_lhs => simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_four]
  ring

/-- Distance and pole angle. -/
theorem trace_riemM_gen_rθ (h : RegularG A B C S x) :
    (riemM (genΓ A B C S) 1 2 x * riemM (genΓ A B C S) 1 2 x).trace
      = -(2 * S (x 0) (x 1) * (-(B (x 0) (x 1) * bendTR A B C S (x 0) (x 1) ^ 2)
          + 2 * C (x 0) (x 1) * bendTR A B C S (x 0) (x 1) * bendRR A B C S (x 0) (x 1)
          + A (x 0) (x 1) * bendRR A B C S (x 0) (x 1) ^ 2) / det2 A B C (x 0) (x 1)) := by
  rw [riemM_gen_rθ h]
  conv_lhs => simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_four]
  ring

/-- Time and angle around the axis. -/
theorem trace_riemM_gen_tφ (h : RegularG A B C S x) :
    (riemM (genΓ A B C S) 0 3 x * riemM (genΓ A B C S) 0 3 x).trace
      = -(2 * S (x 0) (x 1) * sin (x 2) ^ 2
          * (-(B (x 0) (x 1) * bendTT A B C S (x 0) (x 1) ^ 2)
          + 2 * C (x 0) (x 1) * bendTT A B C S (x 0) (x 1) * bendTR A B C S (x 0) (x 1)
          + A (x 0) (x 1) * bendTR A B C S (x 0) (x 1) ^ 2) / det2 A B C (x 0) (x 1)) := by
  rw [riemM_gen_tφ h]
  conv_lhs => simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_four]
  ring

/-- Distance and angle around the axis. -/
theorem trace_riemM_gen_rφ (h : RegularG A B C S x) :
    (riemM (genΓ A B C S) 1 3 x * riemM (genΓ A B C S) 1 3 x).trace
      = -(2 * S (x 0) (x 1) * sin (x 2) ^ 2
          * (-(B (x 0) (x 1) * bendTR A B C S (x 0) (x 1) ^ 2)
          + 2 * C (x 0) (x 1) * bendTR A B C S (x 0) (x 1) * bendRR A B C S (x 0) (x 1)
          + A (x 0) (x 1) * bendRR A B C S (x 0) (x 1) ^ 2) / det2 A B C (x 0) (x 1)) := by
  rw [riemM_gen_rφ h]
  conv_lhs => simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_four]
  ring

/-- The two directions along the spheres. -/
theorem trace_riemM_gen_θφ (h : RegularG A B C S x) :
    (riemM (genΓ A B C S) 2 3 x * riemM (genΓ A B C S) 2 3 x).trace
      = -(2 * (1 - radiusSlopeSq A B C S (x 0) (x 1)) ^ 2 * sin (x 2) ^ 2) := by
  rw [riemM_gen_θφ h]
  conv_lhs => simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_four]
  ring

/-! ### The scalar -/

/-- **The curvature scalar of the round shape without a cross term** is minus the sum of three
squares: of the curvature of the time-distance part, of how the radius of the spheres bends
(measured with the time-distance part), and of the curvature of the spheres. -/
theorem kretschmann_gen (h : RegularG A B zero2 S x) :
    kretschmann (genG A B zero2 S) (genGinv A B zero2 S) x
      = -(4 * curv2 A B zero2 (x 0) (x 1) ^ 2
          + 8 * (bendTT A B zero2 S (x 0) (x 1) ^ 2 / A (x 0) (x 1) ^ 2
            - 2 * bendTR A B zero2 S (x 0) (x 1) ^ 2 / (A (x 0) (x 1) * B (x 0) (x 1))
            + bendRR A B zero2 S (x 0) (x 1) ^ 2 / B (x 0) (x 1) ^ 2)
          + 4 * (1 - radiusSlopeSq A B zero2 S (x 0) (x 1)) ^ 2 / S (x 0) (x 1) ^ 2) := by
  have hs := h.sin_ne
  have hS0 := h.S_ne
  have hD : det2 A B zero2 (x 0) (x 1) = A (x 0) (x 1) * B (x 0) (x 1) := by
    simp [det2, zero2]
  have hAB : A (x 0) (x 1) * B (x 0) (x 1) ≠ 0 := hD ▸ h.det_ne
  have hA : A (x 0) (x 1) ≠ 0 := left_ne_zero_of_mul hAB
  have hB : B (x 0) (x 1) ≠ 0 := right_ne_zero_of_mul hAB
  have g0 : genGinv A B zero2 S 0 0 x = -B (x 0) (x 1) / det2 A B zero2 (x 0) (x 1) := by
    simp [genGinv, ginvTR, ginvΘ, constOne]
  have g1 : genGinv A B zero2 S 1 1 x = A (x 0) (x 1) / det2 A B zero2 (x 0) (x 1) := by
    simp [genGinv, ginvTR, ginvΘ, constOne]
  have g2 : genGinv A B zero2 S 2 2 x = (S (x 0) (x 1))⁻¹ := by
    simp [genGinv, ginvTR, ginvΘ, constOne]
  have g3 : genGinv A B zero2 S 3 3 x = (S (x 0) (x 1))⁻¹ * (sin (x 2) ^ 2)⁻¹ := by
    simp [genGinv, ginvTR, ginvΘ]
  rw [kretschmann_of_diagonal (fun i j hij ↦ genGinv_diagonal A B S x hij), christoffel_gen_eq]
  simp only [Fin.sum_univ_four, riemM_self, riemM_antisymm (genΓ A B zero2 S) (0 : Fin 4) 1,
    riemM_antisymm (genΓ A B zero2 S) (0 : Fin 4) 2,
    riemM_antisymm (genΓ A B zero2 S) (0 : Fin 4) 3,
    riemM_antisymm (genΓ A B zero2 S) (1 : Fin 4) 2,
    riemM_antisymm (genΓ A B zero2 S) (1 : Fin 4) 3,
    riemM_antisymm (genΓ A B zero2 S) (2 : Fin 4) 3, neg_mul_neg, mul_zero, Matrix.trace_zero,
    trace_riemM_gen_tr h, trace_riemM_gen_tθ h, trace_riemM_gen_rθ h, trace_riemM_gen_tφ h,
    trace_riemM_gen_rφ h, trace_riemM_gen_θφ h, g0, g1, g2, g3, hD]
  simp only [zero2]
  field_simp
  ring

/-- **In empty space the curvature scalar of the round shape tells the radius and the mass:**
it is `-12 (1 - |∇R|²)² / R⁴`, with `R = √S` the radius of the spheres and `|∇R|²` how fast it
grows, squared. -/
theorem kretschmann_gen_empty (h : RegularG A B zero2 S x)
    (he : IsEmptyG A B zero2 S (x 0) (x 1)) :
    kretschmann (genG A B zero2 S) (genGinv A B zero2 S) x
      = -12 * (1 - radiusSlopeSq A B zero2 S (x 0) (x 1)) ^ 2 / S (x 0) (x 1) ^ 2 := by
  have hS0 := h.S_ne
  have hD : det2 A B zero2 (x 0) (x 1) = A (x 0) (x 1) * B (x 0) (x 1) := by
    simp [det2, zero2]
  have hAB : A (x 0) (x 1) * B (x 0) (x 1) ≠ 0 := hD ▸ h.det_ne
  have hA : A (x 0) (x 1) ≠ 0 := left_ne_zero_of_mul hAB
  have hB : B (x 0) (x 1) ≠ 0 := right_ne_zero_of_mul hAB
  obtain ⟨e1, e2, e3⟩ := sizeEquations h.det_ne hS0 he
  -- how the radius bends, in empty space
  have hTT : bendTT A B zero2 S (x 0) (x 1)
      = -(A (x 0) (x 1)) * (1 - radiusSlopeSq A B zero2 S (x 0) (x 1)) / (2 * S (x 0) (x 1)) := by
    rw [bendTT, e1]
    field_simp
    ring
  have hTR : bendTR A B zero2 S (x 0) (x 1) = 0 := by
    rw [bendTR, e2]
    simp only [zero2]
    field_simp
    ring
  have hRR : bendRR A B zero2 S (x 0) (x 1)
      = B (x 0) (x 1) * (1 - radiusSlopeSq A B zero2 S (x 0) (x 1)) / (2 * S (x 0) (x 1)) := by
    rw [bendRR, e3]
    field_simp
    ring
  -- the curvature of the time-distance part, in empty space
  have hK : curv2 A B zero2 (x 0) (x 1)
      = (1 - radiusSlopeSq A B zero2 S (x 0) (x 1)) / S (x 0) (x 1) := by
    have h1 := he.1
    rw [ricciTTg, e1] at h1
    have h2 : curv2 A B zero2 (x 0) (x 1) * A (x 0) (x 1)
        = (1 - radiusSlopeSq A B zero2 S (x 0) (x 1)) / S (x 0) (x 1) * A (x 0) (x 1) := by
      linear_combination (norm := skip) (-1 : ℝ) * h1
      field_simp
      ring
    exact mul_right_cancel₀ hA h2
  rw [kretschmann_gen h, hK, hTT, hTR, hRR]
  field_simp
  ring

end Gen

end Curved

end GravityInLean
