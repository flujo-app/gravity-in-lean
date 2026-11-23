/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Flows.Apply

import Mathlib.Tactic

/-!
# The slope of "apply `f` along a path"

Board item `task:flows-compose-deriv`.
-/

@[expose] public section

namespace GravityInLean.Flows

open Set Metric Topology

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] in
/-- Let `g` be continuous on the open region `U`, and `γ` a path that stays in `U`. Then for
every tolerance `c` there is one distance `δ` that works along the whole path: any point `z`
closer than `δ` to some point `γ t` of the path is still in `U`, and `g z` is closer than `c`
to `g (γ t)`. -/
theorem exists_uniform_radius {G : Type*} [PseudoMetricSpace G] {g : E → G} {U : Set E}
    (hU : IsOpen U) (hg : ContinuousOn g U) {γ : C(K, E)} (hγ : γ ∈ pathsIn K U) {c : ℝ}
    (hc : 0 < c) :
    ∃ δ > 0, ∀ (t : K) (z : E), dist z (γ t) < δ → z ∈ U ∧ dist (g z) (g (γ t)) < c := by
  have hK : IsCompact (range γ) := isCompact_range γ.continuous
  have hsub : range γ ⊆ U := by
    rintro _ ⟨t, rfl⟩
    exact hγ t
  obtain ⟨δ₁, hδ₁, h₁⟩ := hK.exists_thickening_subset_open hU hsub
  have hu := hK.uniformContinuousAt_of_continuousAt g
    (fun a ha ↦ hg.continuousAt (hU.mem_nhds (hsub ha))) (Metric.dist_mem_uniformity hc)
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.mem_uniformity_dist.1 hu
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t z hz ↦ ⟨?_, ?_⟩⟩
  · exact h₁ (mem_thickening_iff.2 ⟨γ t, mem_range_self t, hz.trans_le (min_le_left _ _)⟩)
  · have hd : dist (γ t) z < δ₂ := by
      rw [dist_comm]
      exact hz.trans_le (min_le_right _ _)
    have h := h₂ hd (mem_range_self t)
    rw [dist_comm]
    exact h

/-- Let `f` be once continuously differentiable on the open region `U`, and `γ` a path that
stays in `U`. Then "apply `f` along a path" can be differentiated at `γ`, as a map from paths to
paths. Its slope there sends a path `h` to the path `t ↦ (slope of f at γ t) (h t)`. -/
theorem hasFDerivAt_compMap {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    {γ : C(K, E)} (hγ : γ ∈ pathsIn K U) :
    HasFDerivAt (compMap f : C(K, E) → C(K, F)) (appL K E F (compMap (fderiv ℝ f) γ)) γ := by
  have hfc : ContinuousOn f U := hf.continuousOn
  have hf'c : ContinuousOn (fderiv ℝ f) U := hf.continuousOn_fderiv_of_isOpen hU le_rfl
  have hfd : ∀ z ∈ U, DifferentiableAt ℝ f z := fun z hz ↦
    (hf.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hz)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hδU⟩ := exists_uniform_radius hU hf'c hγ hc
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ, fun h hh ↦ ?_⟩
  rw [dist_zero_right] at hh
  -- every point of the path `h` is shorter than `δ`
  have hht : ∀ t, ‖h t‖ < δ := fun t ↦ (ContinuousMap.norm_coe_le_norm h t).trans_lt hh
  -- so the moved path `γ + h` still stays in `U`
  have hγh : γ + h ∈ pathsIn K U := fun t ↦ by
    refine (hδU t _ ?_).1
    simpa [dist_eq_norm] using hht t
  rw [ContinuousMap.norm_le _ (mul_nonneg hc.le (norm_nonneg h))]
  intro t
  have hpt : (compMap f (γ + h) - compMap f γ - appL K E F (compMap (fderiv ℝ f) γ) h) t
      = f (γ t + h t) - f (γ t) - fderiv ℝ f (γ t) (γ t + h t - γ t) := by
    simp [compMap_apply hfc hγh, compMap_apply hfc hγ, compMap_apply hf'c hγ]
  rw [hpt]
  -- the mean value inequality on the ball of radius `δ` around `γ t`
  have hmv := (convex_ball (γ t) δ).norm_image_sub_le_of_norm_fderiv_le'
    (𝕜 := ℝ) (f := f) (φ := fderiv ℝ f (γ t)) (C := c)
    (fun z hz ↦ hfd z (hδU t z hz).1)
    (fun z hz ↦ by
      have := (hδU t z hz).2
      rw [dist_eq_norm] at this
      exact this.le)
    (mem_ball_self hδ) (show γ t + h t ∈ ball (γ t) δ by simpa [dist_eq_norm] using hht t)
  refine hmv.trans ?_
  rw [add_sub_cancel_left]
  exact mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm h t) hc.le

end GravityInLean.Flows
