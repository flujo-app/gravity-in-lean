/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.Turns
public import GravityInLean.Flows.PathEquation
public import GravityInLean.Flows.LocalFlow
public import GravityInLean.Flows.Rescale

import Mathlib.Tactic

/-!
# Paths along a field depend smoothly on where they start

Board item `task:flows-smooth-flow`. This proves statement 1 of `Goals/Turns.lean`.

The route: the path that follows `X` for the time `t` from `x` is, read at its end, the path
that follows `t • X` for the time `1` from `x`. Such paths on the fixed time span from `0` to `1`
are the zeros of one smooth equation between complete spaces of paths (`PathMap.lean`), so the
theorem on solving smooth equations (`Implicit.lean`) makes them a smooth function of `t` and `x`
(`PathEquation.lean`). Reading a path at its end is linear and continuous. The paths themselves,
and that they follow the field, come from the standard library (`LocalFlow.lean`); that they are
the zeros of the equation is in `Rescale.lean`.
-/

@[expose] public section

namespace GravityInLean

open Set Metric Topology Flows

open scoped ContDiff

/-- **Paths along a field depend smoothly on where they start.** Following a smooth field of
arrows for a time `t` from a starting point `x` is a smooth function of `t` and `x` together, for
`t` near `0` and `x` near any given point. -/
theorem smoothFlow : SmoothFlowStatement := by
  intro E _ _ _ X U hU hX x₀ hx₀
  obtain ⟨ρ, ψ, hρ, hψ, huniq⟩ := exists_smooth_paths hU hX hx₀
  obtain ⟨ε₁, α, hε₁, hα⟩ := exists_local_flow hU hX hx₀ hρ
  have hε : 0 < min ε₁ ρ := lt_min hε₁ hρ
  have hsub₁ : ball x₀ (min ε₁ ρ) ⊆ ball x₀ ε₁ := ball_subset_ball (min_le_left _ _)
  have hsubρ : ball x₀ (min ε₁ ρ) ⊆ ball x₀ ρ := ball_subset_ball (min_le_right _ _)
  have hI₁ : Ioo (-(min ε₁ ρ)) (min ε₁ ρ) ⊆ Ioo (-ε₁) ε₁ :=
    Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
  have hIρ : Ioo (-(min ε₁ ρ)) (min ε₁ ρ) ⊆ Ioo (-ρ) ρ :=
    Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _)
  -- The path of the library, read at the time `t`, is the smooth family's path read at its end.
  have key : ∀ t ∈ Ioo (-(min ε₁ ρ)) (min ε₁ ρ), ∀ x ∈ ball x₀ (min ε₁ ρ),
      α t x = ψ (t, x) 1 := by
    intro t ht x hx
    have ht₁ := hI₁ ht
    obtain ⟨h0, hαx⟩ := hα x (hsub₁ hx)
    obtain ⟨γ, hγ, hγeq⟩ := exists_rescaled_path (X := X) (U := U) hX.continuousOn
      (α := fun r ↦ α r x) (ε := ε₁) h0 (fun r hr ↦ ⟨(hαx r hr).1, (hαx r hr).2.2⟩) ht₁
    have hin : ∀ τ, γ τ ∈ ball x₀ ρ := by
      intro τ
      rw [hγ τ]
      refine (hαx _ (abs_lt.mp ?_)).2.1
      rw [abs_mul, abs_of_nonneg τ.2.1]
      calc |t| * (τ : ℝ) ≤ |t| * 1 := mul_le_mul_of_nonneg_left τ.2.2 (abs_nonneg t)
        _ = |t| := mul_one _
        _ < ε₁ := abs_lt.mpr ht₁
    rw [huniq t x γ (hIρ ht) (hsubρ hx) hin hγeq, hγ 1]
    simp
  refine ⟨min ε₁ ρ, α, hε, ?_, fun x hx ↦ (hα x (hsub₁ hx)).1, fun x hx t ht ↦ ?_⟩
  · have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ ψ p 1)
        (Ioo (-(min ε₁ ρ)) (min ε₁ ρ) ×ˢ ball x₀ (min ε₁ ρ)) := by
      have h := (ContinuousMap.evalCLM ℝ (1 : unitInterval) :
        C(unitInterval, E) →L[ℝ] E).contDiff.comp_contDiffOn (n := ∞)
        (hψ.mono (prod_mono hIρ hsubρ))
      exact h
    exact h1.congr fun p hp ↦ key p.1 hp.1 p.2 hp.2
  · have h := (hα x (hsub₁ hx)).2 t (hI₁ ht)
    exact ⟨h.1, h.2.2⟩

end GravityInLean
