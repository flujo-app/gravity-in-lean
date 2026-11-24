/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Curvature
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

import Mathlib.Tactic

/-!
# Three arrows that span two directions

Board item `task:turns-kernel`. Plain linear algebra at one point, in the form in which
`TurnsOn.surfaces` gives it:

* `exists_unit_kernel`: three arrows that span only two directions have a mix of length one
  that is zero;
* `span_rotate`: rotating the three arrows among themselves does not change what they span.
-/

@[expose] public section

namespace GravityInLean.Turns

/-- Three arrows that span only two directions are not independent: there are three numbers
`n 0`, `n 1`, `n 2`, whose squares add up to one, such that the mix `∑ j, n j • v j` is the
zero arrow. -/
theorem exists_unit_kernel (v : Fin 3 → Coords 4)
    (h : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) = 2) :
    ∃ n : Fin 3 → ℝ, ∑ j, n j ^ 2 = 1 ∧ ∑ j, n j • v j = 0 := by
  -- Three independent arrows would span three directions.
  have hli : ¬ LinearIndependent ℝ v := by
    intro hli
    have h3 := finrank_span_eq_card hli
    rw [h] at h3
    simp at h3
  -- So some mix with a number that is not zero gives the zero arrow.
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hli
  have hc : 0 < ∑ j, g j ^ 2 := by
    have h1 : 0 < g i ^ 2 := by positivity
    have h2 : g i ^ 2 ≤ ∑ j, g j ^ 2 :=
      Finset.single_le_sum (f := fun j ↦ g j ^ 2) (fun j _ ↦ sq_nonneg (g j))
        (Finset.mem_univ i)
    exact lt_of_lt_of_le h1 h2
  -- Divide the mix by its length.
  refine ⟨fun j ↦ (Real.sqrt (∑ j, g j ^ 2))⁻¹ * g j, ?_, ?_⟩
  · simp only [mul_pow, inv_pow, Real.sq_sqrt hc.le, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hc.ne'
  · simp only [mul_smul, ← Finset.smul_sum, hg, smul_zero]

/-- Rotating three arrows among themselves (replacing them by the three mixes that the rows of
a table `R` with `R * Rᵀ = 1` give) does not change the set of all their mixes. -/
theorem span_rotate (R : Matrix (Fin 3) (Fin 3) ℝ) (h : R * R.transpose = 1)
    (v : Fin 3 → Coords 4) :
    Submodule.span ℝ (Set.range fun i ↦ ∑ j, R i j • v j) = Submodule.span ℝ (Set.range v) := by
  have h' : R.transpose * R = 1 := mul_eq_one_comm.mp h
  -- The columns of `R` are of length one and at right angles to each other.
  have hcol : ∀ k j, ∑ i, R i k * R i j = if k = j then 1 else 0 := by
    intro k j
    have := congrFun (congrFun h' k) j
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  apply le_antisymm
  · -- Every new arrow is a mix of the old ones.
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    change (∑ j, R i j • v j) ∈ Submodule.span ℝ (Set.range v)
    exact Submodule.sum_mem _ fun j _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · -- Every old arrow is a mix of the new ones, with the numbers of a column of `R`.
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    have hk : v k = ∑ i, R i k • ∑ j, R i j • v j := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul, hcol]
      simp
    change v k ∈ Submodule.span ℝ (Set.range fun i ↦ ∑ j, R i j • v j)
    rw [hk]
    exact Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GravityInLean.Turns
