/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Flows.Integrate

import Mathlib.Tactic

/-!
# A path of the field, run at another speed, solves the equation of a path

Board item `task:flows-rescale`.
-/

@[expose] public section

namespace GravityInLean.Flows

open Set Metric Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- If the time `t` lies strictly between `-ε` and `ε`, so does `t * τ` for every `τ` from `0`
to `1`. -/
theorem mul_mem_Ioo_of_mem {ε t τ : ℝ} (ht : t ∈ Ioo (-ε) ε) (hτ : τ ∈ Icc (0 : ℝ) 1) :
    t * τ ∈ Ioo (-ε) ε := by
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨h0, h1⟩ := hτ
  have hε : 0 < ε := by linarith
  constructor
  · nlinarith [mul_nonneg h0 (by linarith : (0 : ℝ) ≤ t + ε),
      mul_nonneg (sub_nonneg.2 h1) hε.le]
  · nlinarith [mul_nonneg h0 (by linarith : (0 : ℝ) ≤ ε - t),
      mul_nonneg (sub_nonneg.2 h1) hε.le]

/-- Let `α` be a path of the field `X` that starts at `x`, for times between `-ε` and `ε`, and
let `t` be one of these times. Run it at speed `t`: `γ τ = α (t * τ)` for `τ` from `0` to `1`.
Then `γ` is a continuous path and solves the equation of a path with factor `t`:
`γ = (the path that stays at x) + t • (integral of X along γ)`. -/
theorem exists_rescaled_path {X : E → E} {U : Set E} (hX : ContinuousOn X U) {α : ℝ → E}
    {ε : ℝ} {x : E} (h0 : α 0 = x)
    (hα : ∀ t ∈ Ioo (-ε) ε, α t ∈ U ∧ HasDerivAt α (X (α t)) t) {t : ℝ} (ht : t ∈ Ioo (-ε) ε) :
    ∃ γ : C(unitInterval, E), (∀ τ : unitInterval, γ τ = α (t * τ)) ∧
      γ = ContinuousMap.const unitInterval x + t • primL E (compMap X γ) := by
  -- All the times `t * τ` lie between `-ε` and `ε`.
  have hmem : ∀ τ : unitInterval, t * (τ : ℝ) ∈ Ioo (-ε) ε := fun τ ↦ mul_mem_Ioo_of_mem ht τ.2
  -- The path run at speed `t` is continuous.
  have hcont : Continuous (fun τ : unitInterval ↦ α (t * (τ : ℝ))) := by
    rw [continuous_iff_continuousAt]
    intro τ
    have h1 : ContinuousAt α (t * (τ : ℝ)) := (hα _ (hmem τ)).2.continuousAt
    have h2 : ContinuousAt (fun τ : unitInterval ↦ t * (τ : ℝ)) τ :=
      (continuous_const.mul continuous_subtype_val).continuousAt
    exact ContinuousAt.comp' (f := fun τ : unitInterval ↦ t * (τ : ℝ)) h1 h2
  obtain ⟨γ, hγ⟩ : ∃ γ : C(unitInterval, E), ∀ τ : unitInterval, γ τ = α (t * τ) :=
    ⟨⟨_, hcont⟩, fun _ ↦ rfl⟩
  refine ⟨γ, hγ, ?_⟩
  have hγU : γ ∈ pathsIn unitInterval U := fun τ ↦ by
    rw [hγ]
    exact (hα _ (hmem τ)).1
  ext τ
  -- The slope of `σ ↦ α (t * σ)` at the times `σ` from `0` to `τ`.
  have hderiv : ∀ σ ∈ uIcc (0 : ℝ) (τ : ℝ), HasDerivAt (fun σ : ℝ ↦ α (t * σ))
      (t • compMap X γ (projIcc 0 1 zero_le_one σ)) σ := by
    intro σ hσ
    rw [uIcc_of_le τ.2.1] at hσ
    have hσ1 : σ ∈ Icc (0 : ℝ) 1 := ⟨hσ.1, hσ.2.trans τ.2.2⟩
    rw [projIcc_of_mem zero_le_one hσ1, compMap_apply hX hγU, hγ]
    have h1 : HasDerivAt α (X (α (t * σ))) (t * σ) := (hα _ (hmem ⟨σ, hσ1⟩)).2
    have h2 : HasDerivAt (fun σ : ℝ ↦ t * σ) t σ := hasDerivAt_const_mul t
    exact HasDerivAt.scomp (h := fun σ : ℝ ↦ t * σ) σ h1 h2
  -- That slope can be integrated, since it is continuous.
  have hint : IntervalIntegrable (fun σ : ℝ ↦ t • compMap X γ (projIcc 0 1 zero_le_one σ))
      MeasureTheory.volume 0 τ :=
    Continuous.intervalIntegrable
      (((compMap X γ).continuous.comp continuous_projIcc).const_smul t) _ _
  -- So the integral of the slope is the change of the path.
  have hI : t • ∫ σ in (0 : ℝ)..(τ : ℝ), compMap X γ (projIcc 0 1 zero_le_one σ)
      = α (t * τ) - α (t * 0) := by
    rw [← intervalIntegral.integral_smul]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [ContinuousMap.add_apply, ContinuousMap.const_apply, ContinuousMap.smul_apply, primL_apply,
    hI, mul_zero, h0, hγ]
  abel

end GravityInLean.Flows
