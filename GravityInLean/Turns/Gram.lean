/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Curvature
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

import Mathlib.Tactic

/-!
# Two arrows are independent exactly when their Gram determinant is not zero

Board item `task:turns-gram`. Plain linear algebra with the ordinary dot product `u ⬝ᵥ v` of
lists of numbers. For two arrows `u`, `v` the number `(u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ 2` (their
Gram determinant) is never negative, and it is zero exactly when one arrow is a multiple of the
other. From this, for three arrows `η 0`, `η 1`, `η 2` that span two directions (the form of
`TurnsOn.surfaces`):

* `gram_pos_of_finrank`: if the middle one is zero, the outer two are independent;
* `eq_zero_of_dot_eq_zero`: if the outer two are independent and the middle one is at right
  angles to both, the middle one is zero.
-/

@[expose] public section

namespace GravityInLean.Turns

variable {n : Type*} [Fintype n]

/-- The dot product of an arrow with itself is not negative. -/
theorem dot_self_nonneg (w : n → ℝ) : 0 ≤ w ⬝ᵥ w := by
  unfold dotProduct
  exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (w i)

/-- Take from `u` its part along `v` (scaled by `v ⬝ᵥ v` to avoid a division). What is left has
squared length `v ⬝ᵥ v` times the Gram determinant of `u` and `v`. -/
theorem gram_smul_sub_self (u v : n → ℝ) :
    ((v ⬝ᵥ v) • u - (u ⬝ᵥ v) • v) ⬝ᵥ ((v ⬝ᵥ v) • u - (u ⬝ᵥ v) • v) =
      (v ⬝ᵥ v) * ((u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ 2) := by
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm v u]
  ring

/-- The Gram determinant of two arrows is never negative (the inequality of Cauchy and
Schwarz). -/
theorem gram_nonneg (u v : n → ℝ) : 0 ≤ (u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ 2 := by
  rcases (dot_self_nonneg v).eq_or_lt with hv | hv
  · have hv0 : v = 0 := dotProduct_self_eq_zero.mp hv.symm
    simp [hv0]
  · refine le_of_mul_le_mul_left (a := v ⬝ᵥ v) ?_ hv
    rw [mul_zero, ← gram_smul_sub_self]
    exact dot_self_nonneg _

/-- Two independent arrows have a positive Gram determinant. -/
theorem gram_pos_of_linearIndependent {u v : n → ℝ} (h : LinearIndependent ℝ ![u, v]) :
    0 < (u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ 2 := by
  refine lt_of_le_of_ne (gram_nonneg u v) fun h0 ↦ ?_
  rw [LinearIndependent.pair_iff] at h
  have hw : (v ⬝ᵥ v) • u - (u ⬝ᵥ v) • v = 0 :=
    dotProduct_self_eq_zero.mp (by rw [gram_smul_sub_self, ← h0, mul_zero])
  have h1 := h (v ⬝ᵥ v) (-(u ⬝ᵥ v)) (by rw [neg_smul, ← sub_eq_add_neg]; exact hw)
  have hv : v = 0 := dotProduct_self_eq_zero.mp h1.1
  have h2 := h 0 1 (by simp [hv])
  exact one_ne_zero h2.2

/-- Two arrows whose Gram determinant is not zero are independent. -/
theorem linearIndependent_of_gram_ne_zero {u v : n → ℝ}
    (hg : (u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ 2 ≠ 0) : LinearIndependent ℝ ![u, v] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hu : s * (u ⬝ᵥ u) + t * (u ⬝ᵥ v) = 0 := by
    have h : u ⬝ᵥ (s • u + t • v) = u ⬝ᵥ 0 := by rw [hst]
    simpa only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_zero] using h
  have hv : s * (u ⬝ᵥ v) + t * (v ⬝ᵥ v) = 0 := by
    have h : (s • u + t • v) ⬝ᵥ v = 0 ⬝ᵥ v := by rw [hst]
    simpa only [add_dotProduct, smul_dotProduct, smul_eq_mul, zero_dotProduct] using h
  have hs : s * ((u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ 2) = 0 := by
    linear_combination (v ⬝ᵥ v) * hu - (u ⬝ᵥ v) * hv
  have ht : t * ((u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ 2) = 0 := by
    linear_combination (u ⬝ᵥ u) * hv - (u ⬝ᵥ v) * hu
  exact ⟨(mul_eq_zero.mp hs).resolve_right hg, (mul_eq_zero.mp ht).resolve_right hg⟩

/-- If three arrows span two directions and the middle one is zero, then the other two are
independent: their Gram determinant is positive. -/
theorem gram_pos_of_finrank (η : Fin 3 → Coords 4)
    (h : Module.finrank ℝ (Submodule.span ℝ (Set.range η)) = 2) (h1 : η 1 = 0) :
    0 < (η 0 ⬝ᵥ η 0) * (η 2 ⬝ᵥ η 2) - (η 0 ⬝ᵥ η 2) ^ 2 := by
  apply gram_pos_of_linearIndependent
  rw [linearIndependent_iff_card_le_finrank_span]
  have hle : Submodule.span ℝ (Set.range η) ≤ Submodule.span ℝ (Set.range ![η 0, η 2]) := by
    refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i ↦ ?_)
    match i with
    | 0 => exact Submodule.subset_span ⟨0, rfl⟩
    | 1 => rw [h1]; exact SetLike.mem_coe.mpr (Submodule.zero_mem _)
    | 2 => exact Submodule.subset_span ⟨1, rfl⟩
  exact (Fintype.card_fin 2).trans_le (h.symm.le.trans (Submodule.finrank_mono hle))

/-- If three arrows span two directions, the outer two are independent (their Gram determinant
is not zero), and the middle one is at right angles to both, then the middle one is zero. -/
theorem eq_zero_of_dot_eq_zero (η : Fin 3 → Coords 4)
    (h : Module.finrank ℝ (Submodule.span ℝ (Set.range η)) = 2)
    (hg : (η 0 ⬝ᵥ η 0) * (η 2 ⬝ᵥ η 2) - (η 0 ⬝ᵥ η 2) ^ 2 ≠ 0)
    (h0 : η 0 ⬝ᵥ η 1 = 0) (h2 : η 2 ⬝ᵥ η 1 = 0) : η 1 = 0 := by
  have hli : LinearIndependent ℝ ![η 0, η 2] := linearIndependent_of_gram_ne_zero hg
  have hle : Submodule.span ℝ (Set.range ![η 0, η 2]) ≤ Submodule.span ℝ (Set.range η) := by
    refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i ↦ ?_)
    match i with
    | 0 => exact Submodule.subset_span ⟨0, rfl⟩
    | 1 => exact Submodule.subset_span ⟨2, rfl⟩
  have hfin : Module.finrank ℝ (Submodule.span ℝ (Set.range ![η 0, η 2])) =
      Module.finrank ℝ (Submodule.span ℝ (Set.range η)) := by
    rw [h, finrank_span_eq_card hli, Fintype.card_fin]
  have heq := Submodule.eq_of_le_of_finrank_eq hle hfin
  have hmem : η 1 ∈ Submodule.span ℝ (Set.range ![η 0, η 2]) := by
    rw [heq]
    exact Submodule.subset_span ⟨1, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  rw [Fin.sum_univ_two] at hc
  have key : (c 0 • η 0 + c 1 • η 2) ⬝ᵥ η 1 = η 1 ⬝ᵥ η 1 := congrArg (· ⬝ᵥ η 1) hc
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, h0, h2] at key
  exact dotProduct_self_eq_zero.mp (by rw [← key]; simp)

end GravityInLean.Turns
