/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Join.CarryPointwise
public import GravityInLean.Join.CarryConnection

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# "The size of the spheres is a usable distance" carries over along a chart

Board item `task:join-usable-carry`. The goal with no coordinates assumes that the size of the
spheres is a usable distance at the point `p` (`Curved.UsableDistanceAt`): there is a step at `p`
that the length measure turns into the slope of the squared size of the spheres, and its own
squared length is not zero. This file shows that the same then holds in a chart around `p`, for
the carried length measure and the carried fields, at the coordinates of `p`
(`usableDistanceAt_carry`).

The step in the chart is the step of the curved space, read by the slope of the chart. The squared
size of the spheres carries over point by point (`sizeSq_carry`), and its slope by the chain rule
(`mvfderiv_eq_of_eventuallyEq_comp_symm`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Join

open GravityInLean.Curved

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {c : OpenPartialHomeomorph M E}
  {g : LengthMeasure 𝓘(ℝ, E) M} {ξ : Fin 3 → Arrows 𝓘(ℝ, E) M}

/-- If the size of the spheres is a usable distance at the point with coordinates `x`, then in
the chart it is a usable distance at `x`. -/
theorem usableDistanceAt_carry_of_mem_target (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {x : E} (hx : x ∈ c.target) (hu : UsableDistanceAt g ξ (c.symm x)) :
    UsableDistanceAt (flatMeasure (carryMeasure c g)) (fun i ↦ carryField c (ξ i)) x := by
  obtain ⟨n, hn, hnn⟩ := hu
  -- Near `x` the carried size of the spheres is the size of the spheres, read in the chart.
  have hev : sizeSq (flatMeasure (carryMeasure c g)) (fun i ↦ carryField c (ξ i))
      =ᶠ[𝓝 x] sizeSq g ξ ∘ c.symm := by
    filter_upwards [c.open_target.mem_nhds hx] with y hy
    exact sizeSq_carry hc g ξ hy
  -- The step `n`, read by the chart and taken back, is `n`.
  have hback : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) n) = n :=
    mfderiv_comp_symm' hc hx n
  refine ⟨mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) n, fun w ↦ ?_, ?_⟩
  · refine Eq.trans ?_ (mvfderiv_eq_of_eventuallyEq_comp_symm hc hx hev w).symm
    refine Eq.trans ?_ (hn _)
    change g (c.symm x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) n))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x w) = _
    rw [hback]
  · change g (c.symm x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) n))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) n)) ≠ 0
    rw [hback]
    exact hnn

/-- **The usable distance carries over along a chart.** If the size of the spheres is a usable
distance at a point `p` of the chart's domain, then for the carried length measure and the carried
fields it is a usable distance at the coordinates of `p`. (That `g` is a space-time and round on a
region that contains the chart's domain is not used.) -/
theorem usableDistanceAt_carry [IsManifold 𝓘(ℝ, E) ∞ M] {s : Set M}
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (_hs : c.source ⊆ s) (_hg : IsSpaceTimeOn g s) (_hr : IsRoundOn g ξ s) {p : M}
    (hp : p ∈ c.source) (hu : UsableDistanceAt g ξ p) :
    UsableDistanceAt (flatMeasure (carryMeasure c g)) (fun i ↦ carryField c (ξ i)) (c p) := by
  have key : ∀ q : M, q = p → UsableDistanceAt g ξ q := by
    rintro q rfl
    exact hu
  exact usableDistanceAt_carry_of_mem_target hc (c.map_source hp) (key _ (c.left_inv hp))

end GravityInLean.Join
