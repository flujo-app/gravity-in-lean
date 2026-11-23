/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Flows.PathMap
public import GravityInLean.Flows.Implicit

import Mathlib.Tactic

/-!
# The path as a smooth function of the factor and the starting point

Board item `task:flows-path-equation`.
-/

@[expose] public section

namespace GravityInLean.Flows

open Set Metric Topology

open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Let `X` be a smooth field on the open region `U` and `x₀` a point of `U`. Then there are a
size `ρ` and a function `ψ` that gives a path for every factor `s` and starting point `x`, such
that

* `ψ` is smooth for `s` within `ρ` of `0` and `x` within `ρ` of `x₀`;
* whenever a path `γ` stays within `ρ` of `x₀` and follows `s • X` from `x` (written as the
  equation of a path), then `γ` is the path `ψ (s, x)`. -/
theorem exists_smooth_paths {X : E → E} {U : Set E} (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U)
    {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ (ρ : ℝ) (ψ : ℝ × E → C(unitInterval, E)), 0 < ρ ∧
      ContDiffOn ℝ ∞ ψ (Ioo (-ρ) ρ ×ˢ ball x₀ ρ) ∧
      ∀ (s : ℝ) (x : E) (γ : C(unitInterval, E)), s ∈ Ioo (-ρ) ρ → x ∈ ball x₀ ρ →
        (∀ τ, γ τ ∈ ball x₀ ρ) →
        γ = ContinuousMap.const unitInterval x + s • primL E (compMap X γ) → ψ (s, x) = γ := by
  -- Solve the equation of a path for the path, near factor `0` and the path that stays at `x₀`.
  have hopen : IsOpen ((univ : Set (ℝ × E)) ×ˢ pathsIn unitInterval U) :=
    isOpen_univ.prod (isOpen_pathsIn hU)
  have hmem : (((0 : ℝ), x₀), ContinuousMap.const unitInterval x₀) ∈
      (univ : Set (ℝ × E)) ×ˢ pathsIn unitInterval U :=
    ⟨mem_univ _, const_mem_pathsIn hx₀⟩
  obtain ⟨ψ, -, hψ, -, huniq⟩ := exists_implicit_smooth hopen (contDiffOn_pathMap hU hX) hmem
    (isInvertible_fderiv_pathMap hU hX hx₀)
  have hψ' : ∀ᶠ p in 𝓝 ((0 : ℝ), x₀), ContDiffAt ℝ ∞ ψ p := hψ
  -- At that point the equation holds: the value is `0`.
  have hfu : pathMap X (((0 : ℝ), x₀), ContinuousMap.const unitInterval x₀) = 0 := by
    simp [pathMap]
  -- Both facts hold within some distance; take the smaller of the two.
  obtain ⟨ε₁, hε₁, h₁⟩ := Metric.eventually_nhds_iff.1 hψ'
  obtain ⟨ε₂, hε₂, h₂⟩ := Metric.eventually_nhds_iff.1 huniq
  have hρ₁ : min ε₁ ε₂ ≤ ε₁ := min_le_left _ _
  have hρ₂ : min ε₁ ε₂ ≤ ε₂ := min_le_right _ _
  refine ⟨min ε₁ ε₂, ψ, lt_min hε₁ hε₂, ?_, ?_⟩
  · -- smooth at every point of the box, so smooth on the box
    rintro ⟨s, x⟩ ⟨hs', hx⟩
    refine (h₁ ?_).contDiffWithinAt
    simp only [Prod.dist_eq, max_lt_iff]
    refine ⟨?_, (mem_ball.1 hx).trans_le hρ₁⟩
    rw [Real.dist_0_eq_abs]
    exact abs_lt.2 ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
  · -- a path in the small ball that solves the equation is the one `ψ` gives
    intro s x γ hs' hx hγ hEq
    have hv : dist ((s, x), γ) (((0 : ℝ), x₀), ContinuousMap.const unitInterval x₀) < ε₂ := by
      simp only [Prod.dist_eq, max_lt_iff]
      refine ⟨⟨?_, (mem_ball.1 hx).trans_le hρ₂⟩, ?_⟩
      · rw [Real.dist_0_eq_abs]
        exact abs_lt.2 ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
      · exact (ContinuousMap.dist_lt_iff hε₂).2 fun τ ↦ (mem_ball.1 (hγ τ)).trans_le hρ₂
    have h0 : pathMap X ((s, x), γ) = 0 := by
      change γ - ContinuousMap.const unitInterval x - s • primL E (compMap X γ) = 0
      rw [sub_sub, sub_eq_zero]
      exact hEq
    exact (h₂ hv).1 (h0.trans hfu.symm)

end GravityInLean.Flows
