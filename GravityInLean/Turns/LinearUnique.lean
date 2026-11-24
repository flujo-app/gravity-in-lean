/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import Mathlib.Analysis.ODE.ExistUnique

import Mathlib.Tactic

/-!
# Two solutions of one linear equation with the same start are equal

Board item `task:turns-linear-unique`. A linear equation here is `A' t = L t (A t)`, where the
linear map `L t` may change with the time `t`, continuously. If two paths solve it on a span of
times around `0` and agree at time `0`, they agree on the whole span. This is the library's
uniqueness for paths (Grönwall), used on a shorter closed span on which `L` is bounded.
-/

@[expose] public section

namespace GravityInLean.Turns

open Set

/-- Two paths `A`, `B` that solve the same linear equation `A' t = L t (A t)` for the times
between `-ε` and `ε`, with `L` continuous there, and that agree at time `0`, agree at all those
times. -/
theorem linear_ode_unique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ε : ℝ}
    (L : ℝ → E →L[ℝ] E) (hL : ContinuousOn L (Set.Ioo (-ε) ε)) (A B : ℝ → E)
    (hA : ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt A (L t (A t)) t)
    (hB : ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt B (L t (B t)) t)
    (h0 : A 0 = B 0) : ∀ t ∈ Set.Ioo (-ε) ε, A t = B t := by
  intro t ht
  -- a shorter closed span of times that still holds `t`
  have habs : |t| < ε := abs_lt.mpr ht
  obtain ⟨δ, h1, h2⟩ : ∃ δ : ℝ, |t| < δ ∧ δ < ε := ⟨(|t| + ε) / 2, by linarith, by linarith⟩
  have hsub : Icc (-δ) δ ⊆ Ioo (-ε) ε := fun r hr ↦ ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hIoo : ∀ r ∈ Ioo (-δ) δ, r ∈ Ioo (-ε) ε := fun r hr ↦ hsub (Ioo_subset_Icc_self hr)
  -- on it the size of `L` is bounded
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hL.mono hsub)
  have hv : ∀ r ∈ Ioo (-δ) δ, LipschitzOnWith (Real.toNNReal C) (fun x ↦ L r x) univ := by
    intro r hr
    have hle : ‖L r‖ ≤ (Real.toNNReal C : ℝ) := by
      rw [Real.coe_toNNReal']
      exact (hC r (Ioo_subset_Icc_self hr)).trans (le_max_left _ _)
    have hle' : ‖L r‖₊ ≤ Real.toNNReal C := NNReal.coe_le_coe.mp (by rw [coe_nnNorm]; exact hle)
    exact ((L r).lipschitzWith.weaken hle').lipschitzOnWith
  -- so the library's uniqueness for paths applies
  exact ODE_solution_unique_of_mem_Ioo (v := fun r x ↦ L r x) (s := fun _ ↦ univ) hv
    (t₀ := 0) ⟨by linarith [abs_nonneg t], by linarith [abs_nonneg t]⟩
    (fun r hr ↦ ⟨hA r (hIoo r hr), mem_univ _⟩) (fun r hr ↦ ⟨hB r (hIoo r hr), mem_univ _⟩) h0
    (abs_lt.mp h1)

end GravityInLean.Turns
