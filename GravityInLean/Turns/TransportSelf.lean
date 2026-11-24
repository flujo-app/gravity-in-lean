/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Turns.Basic
public import GravityInLean.Turns.LinearUnique
public import GravityInLean.Turns.Variational

import Mathlib.Tactic

/-!
# A flow carries its own field to itself

Board item `task:turns-transport-self`. Step 2 of the route, the simplest case. Let `flow` follow
the field `Z`. The slope of `flow t` in the starting point turns the arrow of `Z` at the start
into the arrow of `Z` at the place reached. Both sides solve the same linear equation
`A' = DZ(flow t x) A` (`hasDerivAt_fderiv_flow` for the left side, the chain rule and the flow
equation for the right side) with the same value at time zero (`fderiv_flow_zero`), so they are
equal (`linear_ode_unique`).
-/

@[expose] public section

namespace GravityInLean.Turns

open Set Metric Topology Real

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E} {x₀ : E} {ε : ℝ}
  {flow : ℝ → E → E}

/-- A flow carries its own field to itself: the slope of `flow t` in the starting point turns
the arrow of `Z` at the start into the arrow of `Z` at the place reached. -/
theorem fderiv_flow_self {Z : E → E} (hU : IsOpen U) (hZ : ContDiffOn ℝ ∞ Z U)
    (hf : IsLocalFlow Z U x₀ ε flow) {x : E} (hx : x ∈ ball x₀ ε) {t : ℝ}
    (ht : t ∈ Ioo (-ε) ε) :
    fderiv ℝ (flow t) x (Z x) = Z (flow t x) := by
  -- The slope of the field along the path is continuous in time.
  have hL := continuousOn_fderiv_along_flow hU hZ hf hx
  -- The left side solves the linear equation (the equation of variation).
  have hA : ∀ r ∈ Ioo (-ε) ε, HasDerivAt (fun r ↦ fderiv ℝ (flow r) x (Z x))
      (fderiv ℝ Z (flow r x) (fderiv ℝ (flow r) x (Z x))) r :=
    fun r hr ↦ hasDerivAt_fderiv_flow hU hZ hf hx hr (Z x)
  -- The right side solves it too (the chain rule and the flow equation).
  have hB : ∀ r ∈ Ioo (-ε) ε, HasDerivAt (fun r ↦ Z (flow r x))
      (fderiv ℝ Z (flow r x) (Z (flow r x))) r := by
    intro r hr
    have hd : DifferentiableAt ℝ Z (flow r x) :=
      (hZ.contDiffAt (hU.mem_nhds (hf.mem x hx r hr))).differentiableAt (by simp)
    exact hd.hasFDerivAt.comp_hasDerivAt r (hf.deriv x hx r hr)
  -- At time zero both are the arrow of `Z` at the start.
  have h0 : fderiv ℝ (flow 0) x (Z x) = Z (flow 0 x) := by
    simp [fderiv_flow_zero hf hx, hf.zero x hx]
  exact linear_ode_unique (fun r ↦ fderiv ℝ Z (flow r x)) hL
    (fun r ↦ fderiv ℝ (flow r) x (Z x)) (fun r ↦ Z (flow r x)) hA hB h0 t ht

end GravityInLean.Turns
