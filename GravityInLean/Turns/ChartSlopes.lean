/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Turns.Chart
public import GravityInLean.Turns.ChartSmooth
public import GravityInLean.Turns.Variational
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.Deriv.Shift

import Mathlib.Tactic

/-!
# The slopes of the new coordinates

Board item `task:turns-chart-slopes`. Step 4 of the route, second half: the slope of
`chart σ χ ψ` (see `Chart.lean`) along each of the four basic steps `Pi.single μ 1`.

* along `y 3`: the field `Z₂` at the place reached (the flow equation of `ψ`);
* along `y 2`: the slope of `ψ (y 3)` in its starting point, applied to the field `Z₀` at the
  place reached by `χ` (the flow equation of `χ`, and the chain rule);
* along `y 0` and `y 1`, at the start only: the two directions of the surface `σ` (both flows do
  nothing at time zero: `fderiv_flow_zero`).
-/

@[expose] public section

namespace GravityInLean.Turns

open Set Metric Topology Real

open scoped ContDiff

variable {Z₀ Z₂ : Coords 4 → Coords 4} {U : Set (Coords 4)} {p : Coords 4} {δ ε₀ ε₂ : ℝ}
  {σ : ℝ × ℝ → Coords 4} {χ ψ : ℝ → Coords 4 → Coords 4}

/-- The slope of a map along the basic step `Pi.single μ 1` is the rate at which the map changes
when only the number `y μ` is moved. -/
theorem fderiv_single_of_update {Φ : Coords 4 → Coords 4} {y : Coords 4}
    (hΦ : DifferentiableAt ℝ Φ y) (μ : Fin 4) {v : Coords 4}
    (hd : HasDerivAt (fun r : ℝ ↦ Φ (Function.update y μ r)) v (y μ)) :
    fderiv ℝ Φ y (Pi.single μ 1) = v := by
  have h1 : HasDerivAt (Function.update y μ) (Pi.single μ (1 : ℝ)) (y μ) :=
    hasDerivAt_update y μ (y μ)
  have h2 : HasDerivAt (Φ ∘ Function.update y μ) (fderiv ℝ Φ y (Pi.single μ 1)) (y μ) :=
    hΦ.hasFDerivAt.comp_hasDerivAt_of_eq (y μ) h1 (Function.update_eq_self μ y).symm
  exact h2.unique hd

/-- The chart has a slope at every point of its domain. -/
theorem differentiableAt_chart (h : ChartData Z₀ Z₂ U p δ ε₀ ε₂ σ χ ψ) {y : Coords 4}
    (hy : y ∈ chartDomain σ χ p δ ε₀ ε₂) : DifferentiableAt ℝ (chart σ χ ψ) y :=
  ((contDiffOn_chart h).contDiffAt ((isOpen_chartDomain h).mem_nhds hy)).differentiableAt
    (by simp)

/-- Along `y 3` the chart moves with the field `Z₂`. -/
theorem fderiv_chart_three (h : ChartData Z₀ Z₂ U p δ ε₀ ε₂ σ χ ψ) {y : Coords 4}
    (hy : y ∈ chartDomain σ χ p δ ε₀ ε₂) :
    fderiv ℝ (chart σ χ ψ) y (Pi.single 3 1) = Z₂ (chart σ χ ψ y) := by
  refine fderiv_single_of_update (differentiableAt_chart h hy) 3 ?_
  obtain ⟨-, -, -, h3, hq, -⟩ := hy
  have hfun : (fun r : ℝ ↦ chart σ χ ψ (Function.update y 3 r))
      = fun r ↦ ψ r (χ (y 2 - π / 2) (σ (y 0, y 1))) := by
    funext r
    simp [chart]
  rw [hfun]
  exact h.flow₂.deriv _ hq (y 3) h3

/-- Along `y 2` the chart moves with the field `Z₀` at the place reached by the first flow,
carried on by the slope of the second flow. -/
theorem fderiv_chart_two (h : ChartData Z₀ Z₂ U p δ ε₀ ε₂ σ χ ψ) {y : Coords 4}
    (hy : y ∈ chartDomain σ χ p δ ε₀ ε₂) :
    fderiv ℝ (chart σ χ ψ) y (Pi.single 2 1) =
      fderiv ℝ (ψ (y 3)) (χ (y 2 - π / 2) (σ (y 0, y 1)))
        (Z₀ (χ (y 2 - π / 2) (σ (y 0, y 1)))) := by
  refine fderiv_single_of_update (differentiableAt_chart h hy) 2 ?_
  obtain ⟨-, h2, hx, h3, hq, -⟩ := hy
  have hfun : (fun r : ℝ ↦ chart σ χ ψ (Function.update y 2 r))
      = ψ (y 3) ∘ fun r ↦ χ (r - π / 2) (σ (y 0, y 1)) := by
    funext r
    simp [chart]
  rw [hfun]
  -- the first flow, with the time shifted by `π / 2`
  have hin : HasDerivAt (fun r : ℝ ↦ χ (r - π / 2) (σ (y 0, y 1)))
      (Z₀ (χ (y 2 - π / 2) (σ (y 0, y 1)))) (y 2) :=
    (h.flow₀.deriv _ hx (y 2 - π / 2) h2).comp_sub_const (y 2) (π / 2)
  -- the second flow at the fixed time `y 3` has a slope in its starting point
  have hS : IsOpen (Ioo (-ε₂) ε₂ ×ˢ ball p ε₂) := isOpen_Ioo.prod isOpen_ball
  have hG : DifferentiableAt ℝ (fun z : ℝ × Coords 4 ↦ ψ z.1 z.2)
      (y 3, χ (y 2 - π / 2) (σ (y 0, y 1))) :=
    (h.flow₂.smooth.contDiffAt (hS.mem_nhds ⟨h3, hq⟩)).differentiableAt (by simp)
  have hψ : DifferentiableAt ℝ (ψ (y 3)) (χ (y 2 - π / 2) (σ (y 0, y 1))) :=
    (hG.hasFDerivAt.comp _ (hasFDerivAt_prodMk_right (y 3) _)).differentiableAt
  exact hψ.hasFDerivAt.comp_hasDerivAt (y 2) hin

/-- At the start, moving one number of the new coordinates so that the chart runs along a line
`ℓ` on the surface (both flows rest at time zero), the chart moves as the surface does along
the direction of `ℓ`. -/
theorem fderiv_chart_start_of_line (h : ChartData Z₀ Z₂ U p δ ε₀ ε₂ σ χ ψ) (μ : Fin 4)
    {ℓ : ℝ → ℝ × ℝ} {w : ℝ × ℝ} (hℓ : HasDerivAt ℓ w 0) (hℓ0 : ℓ 0 = 0)
    (hμ : chartStart μ = 0)
    (hch : ∀ r : ℝ, chart σ χ ψ (Function.update chartStart μ r) = ψ 0 (χ 0 (σ (ℓ r)))) :
    fderiv ℝ (chart σ χ ψ) chartStart (Pi.single μ 1) = fderiv ℝ σ 0 w := by
  refine fderiv_single_of_update (differentiableAt_chart h (chartStart_mem h)) μ ?_
  rw [hμ]
  -- the surface along the line
  have hσd : DifferentiableAt ℝ σ 0 :=
    (h.σsmooth.contDiffAt (ball_mem_nhds 0 h.δpos)).differentiableAt (by simp)
  have hline : HasDerivAt (σ ∘ ℓ) (fderiv ℝ σ 0 w) 0 :=
    hσd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hℓ hℓ0.symm
  -- near the start the line stays where both flows rest at time zero
  have hp : (σ ∘ ℓ) 0 = p := by
    simp [hℓ0, h.σzero]
  have hev0 : ∀ᶠ r in 𝓝 (0 : ℝ), (σ ∘ ℓ) r ∈ ball p ε₀ :=
    hline.continuousAt.eventually_mem (by rw [hp]; exact ball_mem_nhds p h.flow₀.pos)
  have hev2 : ∀ᶠ r in 𝓝 (0 : ℝ), (σ ∘ ℓ) r ∈ ball p ε₂ :=
    hline.continuousAt.eventually_mem (by rw [hp]; exact ball_mem_nhds p h.flow₂.pos)
  refine hline.congr_of_eventuallyEq ?_
  filter_upwards [hev0, hev2] with r h0 h2
  have h0' : σ (ℓ r) ∈ ball p ε₀ := h0
  have h2' : σ (ℓ r) ∈ ball p ε₂ := h2
  rw [hch r, h.flow₀.zero _ h0', h.flow₂.zero _ h2']
  rfl

/-- At the start, along `y 0` the chart moves as the surface does along its first number. -/
theorem fderiv_chart_zero_start (h : ChartData Z₀ Z₂ U p δ ε₀ ε₂ σ χ ψ) :
    fderiv ℝ (chart σ χ ψ) chartStart (Pi.single 0 1) = fderiv ℝ σ 0 (1, 0) := by
  refine fderiv_chart_start_of_line h 0 (ℓ := fun r : ℝ ↦ (r, (0 : ℝ)))
    ((hasDerivAt_id' (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ))) rfl
    (by simp [chartStart]) fun r ↦ ?_
  simp [chart, chartStart]

/-- At the start, along `y 1` the chart moves as the surface does along its second number. -/
theorem fderiv_chart_one_start (h : ChartData Z₀ Z₂ U p δ ε₀ ε₂ σ χ ψ) :
    fderiv ℝ (chart σ χ ψ) chartStart (Pi.single 1 1) = fderiv ℝ σ 0 (0, 1) := by
  refine fderiv_chart_start_of_line h 1 (ℓ := fun r : ℝ ↦ ((0 : ℝ), r))
    ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk (hasDerivAt_id' (0 : ℝ))) rfl
    (by simp [chartStart]) fun r ↦ ?_
  simp [chart, chartStart]

end GravityInLean.Turns
