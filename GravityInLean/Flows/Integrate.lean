/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Flows.PathSpace

import Mathlib.Tactic

/-!
# Adding up a path from time `0` on

Board item `task:flows-integrate`.
-/

@[expose] public section

namespace GravityInLean.Flows

open Set Metric Topology

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For a path `γ` on the times from `0` to `1`, the integral of `γ` from `0` to `t` is again a
path, and it depends on `γ` linearly and continuously. (Outside the times from `0` to `1` the
path is read at the nearest end; inside, `Set.projIcc` does nothing.) -/
theorem exists_primL :
    ∃ P : C(unitInterval, E) →L[ℝ] C(unitInterval, E), ∀ (γ : C(unitInterval, E))
      (t : unitInterval), P γ t = ∫ σ in (0 : ℝ)..(t : ℝ), γ (Set.projIcc 0 1 zero_le_one σ) := by
  -- A path, read at the nearest time between `0` and `1`, is continuous on all of the line,
  -- so it can be integrated over any stretch of time.
  have hint : ∀ (γ : C(unitInterval, E)) (a b : ℝ),
      IntervalIntegrable (fun σ : ℝ ↦ γ (Set.projIcc 0 1 zero_le_one σ)) MeasureTheory.volume a b :=
    fun γ a b ↦ (γ.continuous.comp continuous_projIcc).intervalIntegrable a b
  -- The integral from `0` to `t` is continuous in `t`: this is the new path.
  let F : C(unitInterval, E) → C(unitInterval, E) := fun γ ↦
    ⟨fun t ↦ ∫ σ in (0 : ℝ)..(t : ℝ), γ (Set.projIcc 0 1 zero_le_one σ),
      (intervalIntegral.continuous_primitive (hint γ) 0).comp continuous_subtype_val⟩
  have hF : ∀ (γ : C(unitInterval, E)) (t : unitInterval),
      F γ t = ∫ σ in (0 : ℝ)..(t : ℝ), γ (Set.projIcc 0 1 zero_le_one σ) := fun _ _ ↦ rfl
  -- It is linear in the path, because the integral is.
  let L : C(unitInterval, E) →ₗ[ℝ] C(unitInterval, E) :=
    { toFun := F
      map_add' := fun γ₁ γ₂ ↦ by
        ext t
        rw [ContinuousMap.add_apply, hF, hF, hF]
        simp only [ContinuousMap.add_apply]
        exact intervalIntegral.integral_add (hint γ₁ _ _) (hint γ₂ _ _)
      map_smul' := fun c γ ↦ by
        ext t
        rw [RingHom.id_apply, ContinuousMap.smul_apply, hF, hF]
        simp only [ContinuousMap.smul_apply]
        exact intervalIntegral.integral_smul c _ }
  have hL : ∀ (γ : C(unitInterval, E)) (t : unitInterval),
      L γ t = ∫ σ in (0 : ℝ)..(t : ℝ), γ (Set.projIcc 0 1 zero_le_one σ) := fun _ _ ↦ rfl
  -- It is continuous: the new path is nowhere longer than the old path's largest length,
  -- since the time `t` is at most `1`.
  have hbound : ∀ γ : C(unitInterval, E), ‖L γ‖ ≤ 1 * ‖γ‖ := fun γ ↦ by
    rw [one_mul]
    refine (ContinuousMap.norm_le _ (norm_nonneg γ)).2 fun t ↦ ?_
    have h : ‖∫ σ in (0 : ℝ)..(t : ℝ), γ (Set.projIcc 0 1 zero_le_one σ)‖
        ≤ ‖γ‖ * |(t : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun σ _ ↦ γ.norm_coe_le_norm _
    have ht : |(t : ℝ) - 0| ≤ 1 := by
      rw [sub_zero, abs_of_nonneg t.2.1]
      exact t.2.2
    calc ‖L γ t‖ = ‖∫ σ in (0 : ℝ)..(t : ℝ), γ (Set.projIcc 0 1 zero_le_one σ)‖ := by rw [hL]
      _ ≤ ‖γ‖ * |(t : ℝ) - 0| := h
      _ ≤ ‖γ‖ * 1 := mul_le_mul_of_nonneg_left ht (norm_nonneg γ)
      _ = ‖γ‖ := mul_one _
  exact ⟨L.mkContinuous 1 hbound, fun γ t ↦ hL γ t⟩

/-- **The integral of a path from time `0` on,** as a map of paths that is linear and
continuous. -/
noncomputable def primL : C(unitInterval, E) →L[ℝ] C(unitInterval, E) :=
  Classical.choose (exists_primL E)

variable {E}

/-- `primL` of `γ` at the time `t` is the integral of `γ` from `0` to `t`. -/
theorem primL_apply (γ : C(unitInterval, E)) (t : unitInterval) :
    primL E γ t = ∫ σ in (0 : ℝ)..(t : ℝ), γ (Set.projIcc 0 1 zero_le_one σ) :=
  Classical.choose_spec (exists_primL E) γ t

end GravityInLean.Flows
