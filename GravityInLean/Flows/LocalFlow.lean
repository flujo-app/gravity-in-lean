/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Topology.UnitInterval

import Mathlib.Tactic

/-!
# The paths of the standard library, with the facts we need about where they run

Board item `task:flows-local-flow`.
-/

@[expose] public section

namespace GravityInLean.Flows

open Set Metric Topology

open scoped ContDiff NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Picard and Lindelöf's theorem, with the place of the path said out loud. Under the library's
assumptions on a field `f` (bounded by `L` and Lipschitz on the closed ball of radius `a` round
`x₀`, for a short enough time span), every starting point `x` within `r` of `x₀` has a path that
starts at `x`, moves with the velocity the field gives, and never leaves the closed ball of
radius `a` round `x₀`. The library's own theorem gives the path but does not say where it runs. -/
theorem exists_path_mem_closedBall {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    {x₀ x : E} {a r L K : ℝ≥0} (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) :
    ∃ α : ℝ → E, α t₀ = x ∧ ∀ t ∈ Icc tmin tmax, α t ∈ closedBall x₀ a ∧
      HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t := by
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, by rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀],
    fun t ht ↦ ⟨α.compProj_mem_closedBall hf.mul_max_le, ?_⟩⟩
  apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
    α.continuous_compProj.continuousOn (fun _ _ ↦ α.compProj_mem_closedBall hf.mul_max_le)
    x ht |>.congr_of_mem _ ht
  intro t' ht'
  nth_rw 1 [← hα]
  rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]

/-- Let `X` be a smooth field on the open region `U`, `x₀` a point of `U`, and `ρ` any positive
size. Then there are a time span `ε` and paths `α · x`, one for each starting point `x` within
`ε` of `x₀`, such that for times `t` between `-ε` and `ε`: the path starts at `x`, stays in `U`
and within `ρ` of `x₀`, and moves with the velocity the field gives where it is. -/
theorem exists_local_flow {X : E → E} {U : Set E} (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U)
    {x₀ : E} (hx₀ : x₀ ∈ U) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (ε : ℝ) (α : ℝ → E → E), 0 < ε ∧ ∀ x ∈ ball x₀ ε, α 0 x = x ∧
      ∀ t ∈ Ioo (-ε) ε, α t x ∈ U ∧ α t x ∈ ball x₀ ρ ∧
        HasDerivAt (fun r ↦ α r x) (X (α t x)) t := by
  -- `X` is Lipschitz with some constant `K` on a neighbourhood `s` of `x₀`.
  have h1 : ContDiffAt ℝ 1 X x₀ := (hX.contDiffAt (hU.mem_nhds hx₀)).of_le (mod_cast le_top)
  obtain ⟨K, s, hs, hl⟩ := h1.exists_lipschitzOnWith
  obtain ⟨a₁, ha₁, has⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨a₂, ha₂, haU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  -- A radius `a` so small that the closed ball round `x₀` lies in `s`, in `U`, and within `ρ`.
  obtain ⟨a, ha, ha₁', ha₂', haρ⟩ : ∃ a : ℝ, 0 < a ∧ a < a₁ ∧ a < a₂ ∧ a < ρ := by
    have hm : 0 < min (min a₁ a₂) ρ := lt_min (lt_min ha₁ ha₂) hρ
    have h1 := min_le_left (min a₁ a₂) ρ
    have h2 := min_le_right (min a₁ a₂) ρ
    have h3 := min_le_left a₁ a₂
    have h4 := min_le_right a₁ a₂
    exact ⟨min (min a₁ a₂) ρ / 2, by linarith, by linarith, by linarith, by linarith⟩
  have hsubs : closedBall x₀ a ⊆ s := (closedBall_subset_ball ha₁').trans has
  have hsubU : closedBall x₀ a ⊆ U := (closedBall_subset_ball ha₂').trans haU
  have hsubρ : closedBall x₀ a ⊆ ball x₀ ρ := closedBall_subset_ball haρ
  -- A bound `L` for the length of `X` on that ball.
  obtain ⟨L, hL, hLdef⟩ : ∃ L : ℝ, 0 < L ∧ L = K * a + ‖X x₀‖ + 1 := ⟨_, by positivity, rfl⟩
  have hb : ∀ x ∈ closedBall x₀ a, ‖X x‖ ≤ L := by
    intro x hx
    have h1 : ‖X x - X x₀‖ ≤ K * ‖x - x₀‖ :=
      hl.norm_sub_le (hsubs hx) (hsubs (mem_closedBall_self ha.le))
    have h2 : ‖x - x₀‖ ≤ a := mem_closedBall_iff_norm.mp hx
    have h3 : ‖X x‖ ≤ ‖X x - X x₀‖ + ‖X x₀‖ := norm_le_norm_sub_add _ _
    have h4 : (K : ℝ) * ‖x - x₀‖ ≤ K * a := mul_le_mul_of_nonneg_left h2 K.coe_nonneg
    linarith
  -- A time span `ε` so short that a path of speed at most `L` cannot leave the ball.
  obtain ⟨ε, hε, hεL, hεa⟩ : ∃ ε : ℝ, 0 < ε ∧ L * ε ≤ a / 2 ∧ ε ≤ a / 2 := by
    refine ⟨min (a / 2 / L) (a / 2), lt_min (by positivity) (by positivity), ?_, min_le_right _ _⟩
    calc L * min (a / 2 / L) (a / 2) ≤ L * (a / 2 / L) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hL.le
      _ = a / 2 := by have := hL.ne'; field_simp
  -- The library's assumptions hold with these numbers.
  have h0 : (0 : ℝ) ∈ Icc (-ε) ε := ⟨by linarith, hε.le⟩
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : Icc (-ε) ε, (t₀ : ℝ) = 0 := ⟨⟨0, h0⟩, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a' : ℝ≥0, (a' : ℝ) = a := ⟨⟨a, ha.le⟩, rfl⟩
  obtain ⟨r', hr'⟩ : ∃ r' : ℝ≥0, (r' : ℝ) = a / 2 := ⟨⟨a / 2, by positivity⟩, rfl⟩
  obtain ⟨L', hL'⟩ : ∃ L' : ℝ≥0, (L' : ℝ) = L := ⟨⟨L, hL.le⟩, rfl⟩
  have hf : IsPicardLindelof (fun _ ↦ X) t₀ x₀ a' r' L' K := by
    apply IsPicardLindelof.of_time_independent
    · rw [ha', hL']
      exact hb
    · rw [ha']
      exact hl.mono hsubs
    · rw [ha', hr', hL', ht₀]
      simp only [sub_zero, zero_sub, neg_neg, max_self]
      linarith
  -- One path for every starting point; outside the ball of starting points, any path will do.
  have key : ∀ x : E, ∃ β : ℝ → E, x ∈ ball x₀ ε → (β 0 = x ∧ ∀ t ∈ Ioo (-ε) ε,
      β t ∈ U ∧ β t ∈ ball x₀ ρ ∧ HasDerivAt β (X (β t)) t) := by
    intro x
    by_cases hx : x ∈ ball x₀ ε
    · have hx' : x ∈ closedBall x₀ r' := by
        rw [hr']
        exact closedBall_subset_closedBall hεa (ball_subset_closedBall hx)
      obtain ⟨β, hβ0, hβ⟩ := exists_path_mem_closedBall hf hx'
      rw [ht₀] at hβ0
      refine ⟨β, fun _ ↦ ⟨hβ0, fun t ht ↦ ?_⟩⟩
      obtain ⟨hmem, hd⟩ := hβ t (Ioo_subset_Icc_self ht)
      rw [ha'] at hmem
      exact ⟨hsubU hmem, hsubρ hmem, hd.hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩
    · exact ⟨fun _ ↦ 0, fun h ↦ absurd h hx⟩
  choose α hα using key
  exact ⟨ε, fun t x ↦ α x t, hε, hα⟩

end GravityInLean.Flows
