/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Turns.Chart

import Mathlib.Tactic

/-!
# The new coordinates are smooth

Board item `task:turns-chart-smooth`. Step 4 of the route: the chart of `Chart.lean`,
`chart σ χ ψ y = ψ (y 3) (χ (y 2 - π / 2) (σ (y 0, y 1)))`, is smooth on its domain, because the
surface `σ` is smooth and both flows are smooth in time and starting point together
(`IsLocalFlow.smooth`), and on `chartDomain` every piece is asked for only where it is smooth.
-/

@[expose] public section

namespace GravityInLean.Turns

open Set Metric Topology Real

open scoped ContDiff

variable {Z₀ Z₂ : Coords 4 → Coords 4} {U : Set (Coords 4)} {p : Coords 4} {δ ε₀ ε₂ : ℝ}
  {σ : ℝ × ℝ → Coords 4} {χ ψ : ℝ → Coords 4 → Coords 4}

/-- The chart is smooth on its domain. -/
theorem contDiffOn_chart (h : ChartData Z₀ Z₂ U p δ ε₀ ε₂ σ χ ψ) :
    ContDiffOn ℝ ∞ (chart σ χ ψ) (chartDomain σ χ p δ ε₀ ε₂) := by
  -- Each of the four new coordinates is a smooth function of the point.
  have c0 : ContDiff ℝ ∞ (fun y : Coords 4 ↦ y 0) := contDiff_apply ℝ (fun _ : Fin 4 ↦ ℝ) 0
  have c1 : ContDiff ℝ ∞ (fun y : Coords 4 ↦ y 1) := contDiff_apply ℝ (fun _ : Fin 4 ↦ ℝ) 1
  have c2 : ContDiff ℝ ∞ (fun y : Coords 4 ↦ y 2) := contDiff_apply ℝ (fun _ : Fin 4 ↦ ℝ) 2
  have c3 : ContDiff ℝ ∞ (fun y : Coords 4 ↦ y 3) := contDiff_apply ℝ (fun _ : Fin 4 ↦ ℝ) 3
  -- The point on the surface.
  have hσ : ContDiffOn ℝ ∞ (fun y : Coords 4 ↦ σ (y 0, y 1)) (chartDomain σ χ p δ ε₀ ε₂) :=
    h.σsmooth.comp (c0.prodMk c1).contDiffOn fun y hy ↦ hy.1
  -- Then along the first flow.
  have hχ : ContDiffOn ℝ ∞ (fun y : Coords 4 ↦ χ (y 2 - π / 2) (σ (y 0, y 1)))
      (chartDomain σ χ p δ ε₀ ε₂) :=
    h.flow₀.smooth.comp ((c2.sub contDiff_const).contDiffOn.prodMk hσ)
      fun y hy ↦ Set.mk_mem_prod hy.2.1 hy.2.2.1
  -- Then along the second flow.
  exact h.flow₂.smooth.comp (c3.contDiffOn.prodMk hχ)
    fun y hy ↦ Set.mk_mem_prod hy.2.2.2.1 hy.2.2.2.2.1

end GravityInLean.Turns
