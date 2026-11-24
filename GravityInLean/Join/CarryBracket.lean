/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Join.Carry
public import GravityInLean.Curved.Flat
public import Mathlib.Geometry.Manifold.VectorField.LieBracket

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Fields of arrows and their bracket carry over along a chart

Board item `task:join-bracket`. A chart `c` of the curved space `M` reads a field of arrows `X`
of `M` as a field of arrows `carryField c X` on coordinate space, and takes a field of arrows
`X'` on coordinate space to the field `pushField c X'` on `M` (`Carry.lean`). This file shows
that

* reading and taking back undo each other (`chart_carryField_pushField`,
  `chart_pushField_carryField`),
* a field that can be differentiated stays so, both ways (`mdiffAt_carryField`,
  `mdiffAt_pushField`),
* a smooth field stays smooth, both ways (`contMDiffOn_carryField`, `contDiffOn_carryField`,
  `contMDiffOn_pushField`),
* the bracket of two fields carries over, both ways (`carryField_mlieBracket`,
  `pushField_mlieBracket`).

The tool is the standard library's `VectorField.mpullback`: on the chart's range `carryField c`
is the pullback along `c.symm`, and on the chart's domain `pushField c` is the pullback along `c`
(`carryField_eq_mpullback`, `pushField_eq_mpullback`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Join

open GravityInLean.Curved VectorField

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {c : OpenPartialHomeomorph M E}

/-! ## The slopes of a chart and of its inverse undo each other -/

/-- A chart of the curved space can be differentiated, and so can its inverse. -/
theorem chart_mdifferentiable (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
    c.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
  ⟨(contMDiffOn_of_mem_maximalAtlas hc).mdifferentiableOn (by simp),
    (contMDiffOn_symm_of_mem_maximalAtlas hc).mdifferentiableOn (by simp)⟩

/-- At a point `x` of the chart's range: the slope of the chart after the slope of its inverse
changes nothing. -/
theorem chart_mfderiv_comp_symm (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {x : E}
    (hx : x ∈ c.target) (v : E) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x v) = v := by
  have h := (chart_mdifferentiable hc).comp_symm_deriv hx
  exact congrArg (fun L : E →L[ℝ] E ↦ L v) h

/-- At a point `q` of the chart's domain: the slope of the inverse after the slope of the chart
changes nothing. -/
theorem chart_mfderiv_symm_comp (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {q : M}
    (hq : q ∈ c.source) (v : E) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q v) = v := by
  have h := (chart_mdifferentiable hc).symm_comp_deriv hq
  exact congrArg (fun L : E →L[ℝ] E ↦ L v) h

/-- At a point `x` of the chart's range: the slope of the inverse after the slope of the chart,
both taken at the matching points, changes nothing. -/
theorem chart_mfderiv_symm_comp' (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {x : E}
    (hx : x ∈ c.target) (v : E) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) v) = v := by
  have h := chart_mfderiv_symm_comp hc (c.map_target hx) v
  rwa [c.right_inv hx] at h

/-- At a point `q` of the chart's domain: the slope of the chart after the slope of its inverse,
both taken at the matching points, changes nothing. -/
theorem chart_mfderiv_comp_symm' (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {q : M}
    (hq : q ∈ c.source) (v : E) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q) v) = v := by
  have h := chart_mfderiv_comp_symm hc (c.map_source hq) v
  rwa [c.left_inv hq] at h

/-- At a point of the chart's range, the library's inverse of the slope of `c.symm` is the slope
of `c`. -/
theorem chart_inverse_mfderiv_symm (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {x : E}
    (hx : x ∈ c.target) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x).inverse = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) :=
  ContinuousLinearMap.inverse_eq
    (ContinuousLinearMap.ext fun v ↦ chart_mfderiv_symm_comp' hc hx v)
    (ContinuousLinearMap.ext fun v ↦ chart_mfderiv_comp_symm hc hx v)

/-- At a point of the chart's domain, the library's inverse of the slope of `c` is the slope of
`c.symm`. -/
theorem chart_inverse_mfderiv (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {q : M}
    (hq : q ∈ c.source) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q).inverse = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q) :=
  ContinuousLinearMap.inverse_eq
    (ContinuousLinearMap.ext fun v ↦ chart_mfderiv_comp_symm' hc hq v)
    (ContinuousLinearMap.ext fun v ↦ chart_mfderiv_symm_comp hc hq v)

/-- At a point of the chart's range, the slope of `c.symm` can be undone. -/
theorem chart_isInvertible_mfderiv_symm (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {x : E}
    (hx : x ∈ c.target) : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x).IsInvertible :=
  ContinuousLinearMap.IsInvertible.of_inverse
    (g := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x))
    (ContinuousLinearMap.ext fun v ↦ chart_mfderiv_symm_comp' hc hx v)
    (ContinuousLinearMap.ext fun v ↦ chart_mfderiv_comp_symm hc hx v)

/-- At a point of the chart's domain, the slope of `c` can be undone. -/
theorem chart_isInvertible_mfderiv (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {q : M}
    (hq : q ∈ c.source) : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q).IsInvertible :=
  ContinuousLinearMap.IsInvertible.of_inverse
    (g := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q))
    (ContinuousLinearMap.ext fun v ↦ chart_mfderiv_comp_symm' hc hq v)
    (ContinuousLinearMap.ext fun v ↦ chart_mfderiv_symm_comp hc hq v)

/-! ## Reading in a chart is the library's pullback -/

/-- On the chart's range, a field read in the chart is the library's pullback of the field along
`c.symm`. -/
theorem carryField_eq_mpullback (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {x : E}
    (hx : x ∈ c.target) (X : Arrows 𝓘(ℝ, E) M) :
    carryField c X x = mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm X x := by
  rw [mpullback_apply, chart_inverse_mfderiv_symm hc hx]
  rfl

/-- On the chart's domain, a field taken to the curved space is the library's pullback of the
field along `c`. -/
theorem pushField_eq_mpullback (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {q : M}
    (hq : q ∈ c.source) (X' : Arrows 𝓘(ℝ, E) E) :
    pushField c X' q = mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) c X' q := by
  rw [mpullback_apply, chart_inverse_mfderiv hc hq]
  rfl

/-- Near a point of the chart's range, a field read in the chart is the library's pullback. -/
theorem carryField_eventuallyEq_mpullback (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {x : E}
    (hx : x ∈ c.target) (X : Arrows 𝓘(ℝ, E) M) :
    carryField c X =ᶠ[𝓝 x] mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm X :=
  Filter.eventuallyEq_of_mem (c.open_target.mem_nhds hx)
    fun _ hy ↦ carryField_eq_mpullback hc hy X

/-- Near a point of the chart's domain, a field taken to the curved space is the library's
pullback. -/
theorem pushField_eventuallyEq_mpullback (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {q : M}
    (hq : q ∈ c.source) (X' : Arrows 𝓘(ℝ, E) E) :
    pushField c X' =ᶠ[𝓝 q] mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) c X' :=
  Filter.eventuallyEq_of_mem (c.open_source.mem_nhds hq)
    fun _ hy ↦ pushField_eq_mpullback hc hy X'

/-! ## Reading and taking back undo each other -/

/-- A field on coordinate space, taken to the curved space and read in the chart again, is the
field one started from, on the chart's range. -/
theorem chart_carryField_pushField (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {x : E}
    (hx : x ∈ c.target) (X' : Arrows 𝓘(ℝ, E) E) :
    carryField c (pushField c X') x = X' x := by
  have h := chart_mfderiv_comp_symm' hc (c.map_target hx) (X' (c (c.symm x)))
  simp only [carryField, pushField]
  rw [h, c.right_inv hx]

/-- A field of the curved space, read in the chart and taken back, is the field one started
from, on the chart's domain. -/
theorem chart_pushField_carryField (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {q : M}
    (hq : q ∈ c.source) (X : Arrows 𝓘(ℝ, E) M) :
    pushField c (carryField c X) q = X q := by
  have h := chart_mfderiv_symm_comp' hc (c.map_source hq) (X (c.symm (c q)))
  simp only [carryField, pushField]
  rw [h, c.left_inv hq]

/-! ## The bracket carries over -/

section Bracket

variable [IsManifold 𝓘(ℝ, E) ∞ M] [CompleteSpace E]

/-- **The bracket carries over, read in the chart.** At a point `x` of the chart's range, the
bracket of two fields that can be differentiated at `c.symm x`, read in the chart, is the bracket
of the two fields read in the chart. -/
theorem carryField_mlieBracket (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {X Y : Arrows 𝓘(ℝ, E) M} {x : E} (hx : x ∈ c.target)
    (hX : MDiffAt (T% X) (c.symm x)) (hY : MDiffAt (T% Y) (c.symm x)) :
    carryField c (mlieBracket 𝓘(ℝ, E) X Y) x
      = mlieBracket 𝓘(ℝ, E) (carryField c X) (carryField c Y) x := by
  have hn : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out
  have : IsManifold 𝓘(ℝ, E) (minSmoothness ℝ 2) M := IsManifold.of_le hn
  rw [carryField_eq_mpullback hc hx,
    mpullback_mlieBracket (f := c.symm) (x₀ := x) hX hY
      (contMDiffAt_symm_of_mem_maximalAtlas hc hx) hn]
  exact ((carryField_eventuallyEq_mpullback hc hx X).mlieBracket_vectorField_eq
    (carryField_eventuallyEq_mpullback hc hx Y)).symm

/-- **The bracket carries over, taken to the curved space.** At a point `q` of the chart's
domain, the bracket of two fields on coordinate space that can be differentiated at `c q`, taken
to the curved space, is the bracket of the two fields taken to the curved space. -/
theorem pushField_mlieBracket (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {X' Y' : Arrows 𝓘(ℝ, E) E} {q : M} (hq : q ∈ c.source)
    (hX : MDiffAt (T% X') (c q)) (hY : MDiffAt (T% Y') (c q)) :
    mlieBracket 𝓘(ℝ, E) (pushField c X') (pushField c Y') q
      = pushField c (mlieBracket 𝓘(ℝ, E) X' Y') q := by
  have hn : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out
  have : IsManifold 𝓘(ℝ, E) (minSmoothness ℝ 2) M := IsManifold.of_le hn
  rw [pushField_eq_mpullback hc hq,
    mpullback_mlieBracket (f := c) (x₀ := q) hX hY
      (contMDiffAt_of_mem_maximalAtlas hc hq) hn]
  exact (pushField_eventuallyEq_mpullback hc hq X').mlieBracket_vectorField_eq
    (pushField_eventuallyEq_mpullback hc hq Y')

end Bracket

/-! ## Differentiability carries over -/

section Smooth

variable [IsManifold 𝓘(ℝ, E) ∞ M] [CompleteSpace E]

/-- A field that can be differentiated at `c.symm x` can, read in the chart, be differentiated
at `x`. -/
theorem mdiffAt_carryField_of_mem_target (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {X : Arrows 𝓘(ℝ, E) M} {x : E} (hx : x ∈ c.target) (hX : MDiffAt (T% X) (c.symm x)) :
    MDiffAt (T% (carryField c X)) x := by
  have h : MDiffAt (T% (mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm X)) x :=
    MDifferentiableAt.mpullback_vectorField (f := c.symm) (x₀ := x) (n := ∞) hX
      (contMDiffAt_symm_of_mem_maximalAtlas hc hx) (chart_isInvertible_mfderiv_symm hc hx)
      ENat.LEInfty.out
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [c.open_target.mem_nhds hx] with y hy
  simp only [carryField_eq_mpullback hc hy]

/-- A field that can be differentiated at a point `q` of the chart's domain can, read in the
chart, be differentiated at `c q`. -/
theorem mdiffAt_carryField (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {X : Arrows 𝓘(ℝ, E) M} {q : M} (hq : q ∈ c.source) (hX : MDiffAt (T% X) q) :
    MDiffAt (T% (carryField c X)) (c q) :=
  mdiffAt_carryField_of_mem_target hc (c.map_source hq) (by rwa [c.left_inv hq])

/-- A field on coordinate space that can be differentiated at `c q` can, taken to the curved
space, be differentiated at `q`. -/
theorem mdiffAt_pushField_of_mem_source (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {X' : Arrows 𝓘(ℝ, E) E} {q : M} (hq : q ∈ c.source) (hX : MDiffAt (T% X') (c q)) :
    MDiffAt (T% (pushField c X')) q := by
  have h : MDiffAt (T% (mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) c X')) q :=
    MDifferentiableAt.mpullback_vectorField (f := c) (x₀ := q) (n := ∞) hX
      (contMDiffAt_of_mem_maximalAtlas hc hq) (chart_isInvertible_mfderiv hc hq)
      ENat.LEInfty.out
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [c.open_source.mem_nhds hq] with y hy
  simp only [pushField_eq_mpullback hc hy]

/-- A field on coordinate space that can be differentiated at a point `x` of the chart's range
can, taken to the curved space, be differentiated at `c.symm x`. -/
theorem mdiffAt_pushField (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {X' : Arrows 𝓘(ℝ, E) E} {x : E} (hx : x ∈ c.target) (hX : MDiffAt (T% X') x) :
    MDiffAt (T% (pushField c X')) (c.symm x) :=
  mdiffAt_pushField_of_mem_source hc (c.map_target hx) (by rwa [c.right_inv hx])

/-! ## Smoothness carries over -/

/-- A field that is smooth on a region containing the chart's domain is, read in the chart,
smooth on the chart's range. -/
theorem contMDiffOn_carryField (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {X : Arrows 𝓘(ℝ, E) M} {s : Set M} (hs : c.source ⊆ s) (hX : CMDiff[s] ∞ (T% X)) :
    CMDiff[c.target] ∞ (T% (carryField c X)) := by
  intro x hx
  have h : CMDiffAt[c.symm ⁻¹' s] ∞ (T% (mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm X)) x :=
    ContMDiffWithinAt.mpullback_vectorField_preimage (f := c.symm) (x₀ := x) (n := ∞)
      (hX (c.symm x) (hs (c.map_target hx)))
      (contMDiffAt_symm_of_mem_maximalAtlas hc hx) (chart_isInvertible_mfderiv_symm hc hx)
      le_rfl
  refine (h.mono fun y hy ↦ hs (c.map_target hy)).congr (fun y hy ↦ ?_) ?_
  · simp only [carryField_eq_mpullback hc hy]
  · simp only [carryField_eq_mpullback hc hx]

/-- The same in ordinary words: a field that is smooth on a region containing the chart's domain
is, read in the chart, a smooth function on the chart's range. -/
theorem contDiffOn_carryField (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {X : Arrows 𝓘(ℝ, E) M} {s : Set M} (hs : c.source ⊆ s) (hX : CMDiff[s] ∞ (T% X)) :
    ContDiffOn ℝ ∞ (plain (carryField c X)) c.target :=
  contMDiffOn_arrows_iff.mp (contMDiffOn_carryField hc hs hX)

/-- A field on coordinate space that is smooth on a region containing the chart's range is,
taken to the curved space, smooth on the chart's domain. -/
theorem contMDiffOn_pushField (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {X' : Arrows 𝓘(ℝ, E) E} {s' : Set E} (hs : c.target ⊆ s') (hX : CMDiff[s'] ∞ (T% X')) :
    CMDiff[c.source] ∞ (T% (pushField c X')) := by
  intro q hq
  have h : CMDiffAt[c ⁻¹' s'] ∞ (T% (mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) c X')) q :=
    ContMDiffWithinAt.mpullback_vectorField_preimage (f := c) (x₀ := q) (n := ∞)
      (hX (c q) (hs (c.map_source hq)))
      (contMDiffAt_of_mem_maximalAtlas hc hq) (chart_isInvertible_mfderiv hc hq)
      le_rfl
  refine (h.mono fun y hy ↦ hs (c.map_source hy)).congr (fun y hy ↦ ?_) ?_
  · simp only [pushField_eq_mpullback hc hy]
  · simp only [pushField_eq_mpullback hc hq]

end Smooth

end GravityInLean.Join
