/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Flows.PathSpace

import Mathlib.Tactic

/-!
# Applying a path of linear maps to a path of vectors, point by point

Board item `task:flows-apply`.
-/

@[expose] public section

namespace GravityInLean.Flows

open Set Metric Topology

variable (K : Type*) [TopologicalSpace K] [CompactSpace K]
  (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Given a path `A` of linear maps and a path `h` of vectors, `t ↦ A t (h t)` is a path of
vectors. This is linear and continuous in `A` and in `h`. -/
theorem exists_appL :
    ∃ B : C(K, E →L[ℝ] F) →L[ℝ] C(K, E) →L[ℝ] C(K, F), ∀ A h t, B A h t = A t (h t) := by
  -- The map as a function of `A` and `h`, linear in each.
  let f : C(K, E →L[ℝ] F) →ₗ[ℝ] C(K, E) →ₗ[ℝ] C(K, F) :=
    LinearMap.mk₂ ℝ
      (fun (A : C(K, E →L[ℝ] F)) (h : C(K, E)) ↦
        (⟨fun t ↦ A t (h t), A.continuous.clm_apply h.continuous⟩ : C(K, F)))
      (fun A A' h ↦ by ext t; simp)
      (fun c A h ↦ by ext t; simp)
      (fun A h h' ↦ by ext t; simp)
      (fun c A h ↦ by ext t; simp)
  -- It is bounded: at each time, `‖A t (h t)‖ ≤ ‖A t‖ * ‖h t‖ ≤ ‖A‖ * ‖h‖`.
  have hf : ∀ A h, ‖f A h‖ ≤ 1 * ‖A‖ * ‖h‖ := by
    intro A h
    rw [ContinuousMap.norm_le _ (by positivity)]
    intro t
    calc ‖f A h t‖ = ‖A t (h t)‖ := rfl
      _ ≤ ‖A t‖ * ‖h t‖ := (A t).le_opNorm _
      _ ≤ ‖A‖ * ‖h‖ :=
        mul_le_mul (A.norm_coe_le_norm t) (h.norm_coe_le_norm t) (norm_nonneg _) (norm_nonneg _)
      _ = 1 * ‖A‖ * ‖h‖ := by ring
  exact ⟨f.mkContinuous₂ 1 hf, fun A h t ↦ rfl⟩

/-- **Apply a path of linear maps to a path of vectors, point by point,** as a map that is linear
and continuous in both. -/
noncomputable def appL : C(K, E →L[ℝ] F) →L[ℝ] C(K, E) →L[ℝ] C(K, F) :=
  Classical.choose (exists_appL K E F)

variable {K E F}

/-- `appL` at the time `t` applies the linear map at `t` to the vector at `t`. -/
@[simp]
theorem appL_apply (A : C(K, E →L[ℝ] F)) (h : C(K, E)) (t : K) : appL K E F A h t = A t (h t) :=
  Classical.choose_spec (exists_appL K E F) A h t

end GravityInLean.Flows
