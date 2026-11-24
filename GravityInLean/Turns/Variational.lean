/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Turns.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod

import Mathlib.Tactic

/-!
# How the slope of a flow in its starting point changes with time

Board item `task:turns-variational`. A flow `flow t x` of a field `X` has, at every time `t`, a
slope in the starting point `x`: the linear map `fderiv ℝ (flow t) x`. This file says how that
slope changes with time (the "equation of variation"):

* at time zero the slope is the identity (`fderiv_flow_zero`);
* its rate of change in time is the slope of the field, taken at the place the path has reached,
  applied to the slope of the flow (`hasDerivAt_fderiv_flow`);
* the slope of the field along a path of the flow is continuous in time
  (`continuousOn_fderiv_along_flow`).

The middle one rests on the fact that for a smooth map of two variables the two orders of taking
slopes agree.
-/

@[expose] public section

namespace GravityInLean.Turns

open Set Metric Topology

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : E → E} {U : Set E} {x₀ : E}
  {ε : ℝ} {flow : ℝ → E → E}

/-- At time zero the flow moves nothing, so its slope in the starting point is the identity. -/
theorem fderiv_flow_zero (hf : IsLocalFlow X U x₀ ε flow) {x : E} (hx : x ∈ Metric.ball x₀ ε) :
    fderiv ℝ (flow 0) x = ContinuousLinearMap.id ℝ E := by
  have h : flow 0 =ᶠ[𝓝 x] id :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hx) fun y hy ↦ hf.zero y hy
  rw [h.fderiv_eq, fderiv_id]

/-- The slope of the field, taken along a path of the flow, is continuous in time. -/
theorem continuousOn_fderiv_along_flow (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U)
    (hf : IsLocalFlow X U x₀ ε flow) {x : E} (hx : x ∈ Metric.ball x₀ ε) :
    ContinuousOn (fun t ↦ fderiv ℝ X (flow t x)) (Set.Ioo (-ε) ε) := by
  have h1 : ContinuousOn (fderiv ℝ X) U := hX.continuousOn_fderiv_of_isOpen hU (by simp)
  have h2 : ContinuousOn (fun t ↦ flow t x) (Set.Ioo (-ε) ε) := fun t ht ↦
    (hf.deriv x hx t ht).continuousAt.continuousWithinAt
  exact h1.comp h2 fun t ht ↦ hf.mem x hx t ht

/-- The equation of variation: the slope of the flow in its starting point, taken along a fixed
arrow `w`, changes in time at the rate "slope of the field at the place reached, applied to the
slope of the flow along `w`". -/
theorem hasDerivAt_fderiv_flow (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U)
    (hf : IsLocalFlow X U x₀ ε flow) {x : E} (hx : x ∈ Metric.ball x₀ ε) {t : ℝ}
    (ht : t ∈ Set.Ioo (-ε) ε) (w : E) :
    HasDerivAt (fun r ↦ fderiv ℝ (flow r) x w)
      (fderiv ℝ X (flow t x) (fderiv ℝ (flow t) x w)) t := by
  -- the flow as one map of time and starting point together
  set G : ℝ × E → E := fun p ↦ flow p.1 p.2 with hG
  have hS : IsOpen (Ioo (-ε) ε ×ˢ ball x₀ ε) := isOpen_Ioo.prod isOpen_ball
  have hGat : ∀ p ∈ Ioo (-ε) ε ×ˢ ball x₀ ε, ContDiffAt ℝ ∞ G p := fun p hp ↦
    hf.smooth.contDiffAt (hS.mem_nhds hp)
  have hGd : ∀ p ∈ Ioo (-ε) ε ×ˢ ball x₀ ε, DifferentiableAt ℝ G p := fun p hp ↦
    (hGat p hp).differentiableAt (by simp)
  -- the slope in the starting point is the slope of `G` along `(0, v)`
  have hA : ∀ r ∈ Ioo (-ε) ε, ∀ y ∈ ball x₀ ε, ∀ v : E,
      fderiv ℝ (flow r) y v = fderiv ℝ G (r, y) (0, v) := by
    intro r hr y hy v
    have h1 : HasFDerivAt (fun z : E ↦ ((r, z) : ℝ × E)) (ContinuousLinearMap.inr ℝ ℝ E) y :=
      hasFDerivAt_prodMk_right r y
    have h2 : HasFDerivAt (flow r) ((fderiv ℝ G (r, y)).comp (ContinuousLinearMap.inr ℝ ℝ E)) y :=
      (hGd (r, y) ⟨hr, hy⟩).hasFDerivAt.comp y h1
    rw [h2.fderiv]
    simp
  -- the slope in time is the field at the place reached
  have hB : ∀ p ∈ Ioo (-ε) ε ×ˢ ball x₀ ε, fderiv ℝ G p (1, 0) = X (G p) := by
    rintro ⟨s, y⟩ ⟨hs, hy⟩
    have h1 : HasDerivAt (fun r : ℝ ↦ ((r, y) : ℝ × E)) ((1 : ℝ), (0 : E)) s :=
      (hasDerivAt_id s).prodMk (hasDerivAt_const s y)
    have h2 : HasDerivAt (G ∘ fun r : ℝ ↦ ((r, y) : ℝ × E)) (fderiv ℝ G (s, y) (1, 0)) s :=
      (hGd (s, y) ⟨hs, hy⟩).hasFDerivAt.comp_hasDerivAt s h1
    exact h2.unique (hf.deriv y hy s hs)
  have htx : (t, x) ∈ Ioo (-ε) ε ×ˢ ball x₀ ε := ⟨ht, hx⟩
  have hG2 : DifferentiableAt ℝ (fderiv ℝ G) (t, x) :=
    ((hGat _ htx).fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  -- the rate in time of the slope of `G` along `(0, w)`
  have hC : HasDerivAt (fun r ↦ fderiv ℝ G (r, x) (0, w))
      (fderiv ℝ (fderiv ℝ G) (t, x) (1, 0) (0, w)) t := by
    have h1 : HasDerivAt (fun r : ℝ ↦ ((r, x) : ℝ × E)) ((1 : ℝ), (0 : E)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
    have h2 : HasDerivAt (fun r ↦ fderiv ℝ G (r, x)) (fderiv ℝ (fderiv ℝ G) (t, x) (1, 0)) t :=
      hG2.hasFDerivAt.comp_hasDerivAt t h1
    simpa using h2.clm_apply (hasDerivAt_const t ((0 : ℝ), w))
  -- the two orders of taking slopes agree
  have hsymm : fderiv ℝ (fderiv ℝ G) (t, x) (1, 0) (0, w)
      = fderiv ℝ (fderiv ℝ G) (t, x) (0, w) (1, 0) :=
    ((hGat _ htx).isSymmSndFDerivAt (by simp)).eq _ _
  -- the other order: the slope in the starting point of "the field at the place reached"
  have hE : fderiv ℝ (fderiv ℝ G) (t, x) (0, w) (1, 0)
      = fderiv ℝ X (flow t x) (fderiv ℝ (flow t) x w) := by
    have h1 : HasFDerivAt (fun p ↦ fderiv ℝ G p (1, 0))
        ((fderiv ℝ (fderiv ℝ G) (t, x)).flip (1, 0)) (t, x) := by
      simpa using hG2.hasFDerivAt.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : E)) (t, x))
    have hXd : DifferentiableAt ℝ X (G (t, x)) :=
      (hX.contDiffAt (hU.mem_nhds (hf.mem x hx t ht))).differentiableAt (by simp)
    have h2 : HasFDerivAt (fun p ↦ X (G p)) ((fderiv ℝ X (G (t, x))).comp (fderiv ℝ G (t, x)))
        (t, x) := hXd.hasFDerivAt.comp (t, x) (hGd _ htx).hasFDerivAt
    have h3 : (fun p ↦ fderiv ℝ G p (1, 0)) =ᶠ[𝓝 (t, x)] fun p ↦ X (G p) :=
      Filter.eventually_of_mem (hS.mem_nhds htx) hB
    have h4 := (h2.congr_of_eventuallyEq h3).unique h1
    have h5 := congrArg (fun L : ℝ × E →L[ℝ] E ↦ L (0, w)) h4
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply] at h5
    rw [hA t ht x hx w]
    exact h5.symm
  rw [← hE, ← hsymm]
  refine hC.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr using hA r hr x hx w

end GravityInLean.Turns
