/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.OneMass.Mass
public import GravityInLean.Join.CarryUsable

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# The mass comes back along a chart

Board item `task:checks-mass-carry`. If, for the carried length measure and the carried fields,
the mass at the coordinates of a point `q` is `m`, then the mass at `q` is `m`. It is
`usableDistanceAt_carry` (`Join/CarryUsable.lean`) read the other way, for the mass.

* `massAt_of_carry_of_mem_target`: the same, with the point named by its coordinates `x`;
* `massAt_of_carry`: the statement for a point `q` of the chart's domain.

The step on the curved space is the chart's step, taken back by the slope of the inverse chart.
The squared size of the spheres carries over point by point (`sizeSq_carry`), and its slope by the
chain rule (`mvfderiv_eq_of_eventuallyEq_comp_symm`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Mass

open GravityInLean.Curved GravityInLean.Join

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {c : OpenPartialHomeomorph M E}
  {g : LengthMeasure 𝓘(ℝ, E) M} {ξ : Fin 3 → Arrows 𝓘(ℝ, E) M}

/-- If the mass at the coordinates `x` is `m`, for the carried length measure and the carried
fields, then the mass at the point with coordinates `x` is `m`. -/
theorem massAt_of_carry_of_mem_target (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {x : E} (hx : x ∈ c.target) {m : ℝ}
    (hm : MassAt (flatMeasure (carryMeasure c g)) (fun i ↦ carryField c (ξ i)) x m) :
    MassAt g ξ (c.symm x) m := by
  obtain ⟨n', hn', hm'⟩ := hm
  -- Near `x` the carried size of the spheres is the size of the spheres, read in the chart.
  have hev : sizeSq (flatMeasure (carryMeasure c g)) (fun i ↦ carryField c (ξ i))
      =ᶠ[𝓝 x] sizeSq g ξ ∘ c.symm := by
    filter_upwards [c.open_target.mem_nhds hx] with y hy
    exact sizeSq_carry hc g ξ hy
  refine ⟨mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x n', fun w ↦ ?_, ?_⟩
  · -- The step `w`, read by the chart and taken back, is `w`.
    have hback : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) w) = w :=
      mfderiv_comp_symm' hc hx w
    have h1 : g (c.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x n')
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) w))
        = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (sizeSq g ξ) (c.symm x)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) w)) :=
      (hn' (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) w)).trans
        (mvfderiv_eq_of_eventuallyEq_comp_symm hc hx hev _)
    exact ((congrArg (fun u ↦ g (c.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x n') u)
      hback).symm.trans h1).trans
        (congrArg (fun u ↦ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (sizeSq g ξ) (c.symm x) u) hback)
  · -- The carried measure of the chart's step is the measure of the step taken back.
    have h2 : massOf (sizeSq (flatMeasure (carryMeasure c g)) (fun i ↦ carryField c (ξ i)) x)
        (g (c.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x n')
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x n')) = m := hm'
    rw [sizeSq_carry hc g ξ hx] at h2
    exact h2

/-- **The mass comes back along a chart.** If the mass at the coordinates of a point `q` of the
chart's domain is `m`, for the carried length measure and the carried fields, then the mass at
`q` itself is `m`. -/
theorem massAt_of_carry [IsManifold 𝓘(ℝ, E) ∞ M]
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {q : M} (hq : q ∈ c.source) {m : ℝ}
    (hm : MassAt (flatMeasure (carryMeasure c g)) (fun i ↦ carryField c (ξ i)) (c q) m) :
    MassAt g ξ q m := by
  -- The point with the coordinates of `q` is `q`.
  have key : ∀ q' : M, q' = q → MassAt g ξ q' m → MassAt g ξ q m := by
    rintro q' rfl h
    exact h
  exact key _ (c.left_inv hq) (massAt_of_carry_of_mem_target hc (c.map_source hq) hm)

end GravityInLean.Mass
