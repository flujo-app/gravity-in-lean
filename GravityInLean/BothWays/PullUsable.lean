/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.BothWays.Pull
public import GravityInLean.Join.CarryUsable

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# "The size of the spheres is a usable distance" comes back along a chart

Board item `task:bothways-pull-usable`. `Join/CarryUsable.lean` takes the usable distance from the
curved space to a chart. This file goes the other way. The length measure `g` of the curved space
reads as `G` in the chart `c` (`ReadsAs c g G`), and three fields of arrows `ξ'` of coordinate
space are taken to the curved space by the chart (`pushField`). Then:

* `sizeSq_pull`: the squared size of the spheres on the curved space is the squared size of the
  spheres in the chart, point by point on the chart's domain;
* `mvfderiv_pull`: the chain rule along the chart, for a number at every point;
* `usableDistanceAt_pull`: if the size of the spheres is a usable distance in the chart at the
  coordinates of `p`, it is a usable distance on the curved space at `p`.

The step on the curved space is the chart's step, taken back by the slope of the inverse chart.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.BothWays

open GravityInLean.Curved GravityInLean.Join

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {c : OpenPartialHomeomorph M E}
  {g : LengthMeasure 𝓘(ℝ, E) M} {G : E → E →L[ℝ] E →L[ℝ] ℝ}

/-- The length of a field taken to the curved space, measured with `g`, is the length of the
field in the chart, measured with `G`: at every point of the chart's domain. -/
theorem readsAs_pushField (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hread : ReadsAs c g G)
    (X' Y' : Arrows 𝓘(ℝ, E) E) {q : M} (hq : q ∈ c.source) :
    g q (pushField c X' q) (pushField c Y' q) = flatMeasure G (c q) (X' (c q)) (Y' (c q)) := by
  have hX : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q (pushField c X' q) = X' (c q) :=
    chart_mfderiv_comp_symm' hc hq (X' (c q))
  have hY : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q (pushField c Y' q) = Y' (c q) :=
    chart_mfderiv_comp_symm' hc hq (Y' (c q))
  exact (hread q hq (pushField c X' q) (pushField c Y' q)).trans
    (congrArg₂ (fun a b ↦ flatMeasure G (c q) a b) hX hY)

/-- **The size of the spheres comes back along a chart.** The squared size of the spheres at a
point `q` of the chart's domain, for the fields taken to the curved space, is the squared size of
the spheres in the chart at the coordinates of `q`. -/
theorem sizeSq_pull (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hread : ReadsAs c g G)
    (ξ' : Fin 3 → Arrows 𝓘(ℝ, E) E) {q : M} (hq : q ∈ c.source) :
    sizeSq g (fun i ↦ pushField c (ξ' i)) q = sizeSq (flatMeasure G) ξ' (c q) := by
  have e := fun i ↦ readsAs_pushField hc hread (ξ' i) (ξ' i) hq
  change (g q (pushField c (ξ' 0) q) (pushField c (ξ' 0) q)
      + g q (pushField c (ξ' 1) q) (pushField c (ξ' 1) q)
      + g q (pushField c (ξ' 2) q) (pushField c (ξ' 2) q)) / 2
    = (flatMeasure G (c q) (ξ' 0 (c q)) (ξ' 0 (c q))
      + flatMeasure G (c q) (ξ' 1 (c q)) (ξ' 1 (c q))
      + flatMeasure G (c q) (ξ' 2 (c q)) (ξ' 2 (c q))) / 2
  rw [e 0, e 1, e 2]

/-- **The chain rule along the chart, for a number at every point.** If on the chart's domain the
function `F` of the curved space is the function `f'` of coordinate space after the chart, then
the slope of `F` at `p` along a step is the slope of `f'` at the coordinates of `p` along the
step as the chart sees it. Nothing is asked of `f'`: if it cannot be differentiated, both slopes
are zero. -/
theorem mvfderiv_pull (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {p : M}
    (hp : p ∈ c.source) (F : M → ℝ) (f' : E → ℝ) (hf : ∀ q ∈ c.source, F q = f' (c q))
    (w : TangentSpace 𝓘(ℝ, E) p) :
    d% F p w = d% f' (c p) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c p w) := by
  have hx : c p ∈ c.target := c.map_source hp
  -- Near the coordinates of `p`, `f'` is `F` read in the chart.
  have hev : f' =ᶠ[𝓝 (c p)] F ∘ c.symm := by
    filter_upwards [c.open_target.mem_nhds hx] with y hy
    have h := hf (c.symm y) (c.map_target hy)
    rw [c.right_inv hy] at h
    exact h.symm
  have e1 : d% f' (c p) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c p w)
      = d% F (c.symm (c p)) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c p)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c p w)) :=
    mvfderiv_eq_of_eventuallyEq_comp_symm hc hx hev (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c p w)
  -- The point with the coordinates of `p` is `p`.
  have key : ∀ q : M, c.symm (c p) = q → ∀ u : E,
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) F (c.symm (c p)) u : ℝ) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) F q u := by
    rintro q rfl u
    rfl
  have e2 := key p (c.left_inv hp)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c p) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c p w))
  -- The step, read by the chart and taken back, is the step.
  have e3 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c p) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c p w) = w :=
    mfderiv_comp_symm hc hp w
  exact ((e1.trans e2).trans (congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) F p) e3)).symm

/-- **The usable distance comes back along a chart.** If in the chart the size of the spheres is a
usable distance at the coordinates of a point `p` of the chart's domain, then on the curved space,
for the fields taken there by the chart, it is a usable distance at `p`. -/
theorem usableDistanceAt_pull (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hread : ReadsAs c g G) {ξ' : Fin 3 → Arrows 𝓘(ℝ, E) E} {p : M} (hp : p ∈ c.source)
    (h : UsableDistanceAt (flatMeasure G) ξ' (c p)) :
    UsableDistanceAt g (fun i ↦ pushField c (ξ' i)) p := by
  obtain ⟨n', hn', hnn'⟩ := h
  -- The chart's step, taken back to the curved space and read by the chart again, is itself.
  have hback : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c p (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c p) n') = n' :=
    chart_mfderiv_comp_symm' hc hp n'
  refine ⟨mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c p) n', fun w ↦ ?_, ?_⟩
  · have e1 := hread p hp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c p) n') w
    have e2 : flatMeasure G (c p)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c p (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c p) n'))
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c p w)
        = flatMeasure G (c p) n' (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c p w) :=
      congrArg (fun a ↦ flatMeasure G (c p) a (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c p w)) hback
    have e3 := hn' (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c p w)
    have e4 := mvfderiv_pull hc hp (sizeSq g (fun i ↦ pushField c (ξ' i)))
      (sizeSq (flatMeasure G) ξ') (fun q hq ↦ sizeSq_pull hc hread ξ' hq) w
    exact ((e1.trans e2).trans e3).trans e4.symm
  · have e1 := hread p hp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c p) n')
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c p) n')
    have e2 : flatMeasure G (c p)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c p (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c p) n'))
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c p (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c p) n'))
        = flatMeasure G (c p) n' n' :=
      congrArg₂ (fun a b ↦ flatMeasure G (c p) a b) hback hback
    rw [e1.trans e2]
    exact hnn'

end GravityInLean.BothWays
