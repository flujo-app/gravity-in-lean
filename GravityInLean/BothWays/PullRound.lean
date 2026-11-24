/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.BothWays.Pull
public import GravityInLean.Join.CarryRound
public import GravityInLean.Join.CarryConnection

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# "Looks the same from every side" comes back from a chart to the curved space

Board item `task:bothways-pull-round`. This is `Join/CarryRound.lean` the other way round. There
a length measure of the curved space and three fields are read in a chart. Here the length
measure `g` of the curved space is known to read as `G` in the chart `c` (`ReadsAs c g G` of
`Pull.lean`), and the fields are given in coordinate space and taken to the curved space by the
chart (`pushField` of `Join/Carry.lean`):

* `readsAs_at_target`: what `ReadsAs` says at the point with coordinates `x`;
* `leavesUnchangedAt_pull`: a field of coordinate space that leaves `G` unchanged, taken to the
  curved space, leaves `g` unchanged;
* `isRoundOn_pull`: if `G` looks the same from every side on the range of the chart, with three
  fields, then `g` looks the same from every side on the domain of the chart, with the three
  fields taken to the curved space.

The tool for the second is the chain rule along the inverse chart,
`mvfderiv_eq_of_eventuallyEq_comp_symm` of `Join/CarryConnection.lean`. Each result is first
proved at the point `c.symm x` for coordinates `x` in the range of the chart, where the slopes of
the chart and of its inverse can be written down without a change of base point, and then said
for a point `q` of the domain.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.BothWays

open GravityInLean.Curved GravityInLean.Join VectorField

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {c : OpenPartialHomeomorph M E} {g : LengthMeasure 𝓘(ℝ, E) M} {G : E → E →L[ℝ] E →L[ℝ] ℝ}

/-! ## What `ReadsAs` says at the point with coordinates `x` -/

/-- **`ReadsAs` at the point with coordinates `x`.** The length of two steps at the point
`c.symm x`, measured with `g`, is what `G` gives at `x` for the two steps as the chart sees
them. -/
theorem readsAs_at_target (hread : ReadsAs c g G) {x : E} (hx : x ∈ c.target)
    (v w : TangentSpace 𝓘(ℝ, E) (c.symm x)) :
    g (c.symm x) v w = flatMeasure G x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) w) := by
  have key : ∀ y : E, y = x →
      flatMeasure G y (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) v)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) w)
        = flatMeasure G x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) v)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) w) := by
    rintro y rfl
    rfl
  exact (hread (c.symm x) (c.map_target hx) v w).trans (key (c (c.symm x)) (c.right_inv hx))

/-- For two fields of the curved space read in the chart, `G` gives at `x` what `g` gives for the
two fields at the point with coordinates `x`. -/
theorem readsAs_carryField (hread : ReadsAs c g G) (X Y : Arrows 𝓘(ℝ, E) M) {x : E}
    (hx : x ∈ c.target) :
    flatMeasure G x (carryField c X x) (carryField c Y x)
      = g (c.symm x) (X (c.symm x)) (Y (c.symm x)) :=
  (readsAs_at_target hread hx (X (c.symm x)) (Y (c.symm x))).symm

/-! ## Directions spanned by fields taken to the curved space -/

/-- Fields taken to the curved space span as many directions at the point with coordinates `x`
as the fields of coordinate space do at `x`. -/
theorem finrank_span_pushField {ι : Type*} (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (ξ' : ι → Arrows 𝓘(ℝ, E) E) {x : E} (hx : x ∈ c.target) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range fun i ↦ pushField c (ξ' i) (c.symm x)))
      = Module.finrank ℝ (Submodule.span ℝ (Set.range fun i ↦ ξ' i x)) := by
  have e : (fun i ↦ carryField c (pushField c (ξ' i)) x) = fun i ↦ ξ' i x :=
    funext fun i ↦ carryField_pushField hc (ξ' i) hx
  have h1 := finrank_span_carryField hc (fun i ↦ pushField c (ξ' i)) hx
  rw [e] at h1
  exact h1.symm

/-- If `G` is positive on the directions that the fields of coordinate space span at `x`, then
`g` is positive on the directions that the fields taken to the curved space span at the point
with coordinates `x`. -/
theorem pos_of_mem_span_pushField {ι : Type*} (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hread : ReadsAs c g G) (ξ' : ι → Arrows 𝓘(ℝ, E) E) {x : E} (hx : x ∈ c.target)
    (h : ∀ v ∈ Submodule.span ℝ (Set.range fun i ↦ ξ' i x), v ≠ 0 → 0 < flatMeasure G x v v) :
    ∀ v ∈ Submodule.span ℝ (Set.range fun i ↦ pushField c (ξ' i) (c.symm x)), v ≠ 0 →
      0 < g (c.symm x) v v := by
  intro v hv hv0
  have e : (fun i ↦ carryField c (pushField c (ξ' i)) x) = fun i ↦ ξ' i x :=
    funext fun i ↦ carryField_pushField hc (ξ' i) hx
  -- The step as the chart sees it lies in the span of the fields of coordinate space.
  have hmem : slopeEquiv hc hx v ∈ Submodule.span ℝ (Set.range fun i ↦ ξ' i x) := by
    have h1 : slopeEquiv hc hx v
        ∈ Submodule.span ℝ (Set.range fun i ↦ carryField c (pushField c (ξ' i)) x) := by
      rw [span_carryField hc (fun i ↦ pushField c (ξ' i)) hx]
      exact Submodule.mem_map_of_mem hv
    rw [e] at h1
    exact h1
  have hne : slopeEquiv hc hx v ≠ 0 := (LinearEquiv.map_ne_zero_iff _).mpr hv0
  exact lt_of_lt_of_eq (h _ hmem hne) (readsAs_at_target hread hx v v).symm

variable [IsManifold 𝓘(ℝ, E) ∞ M] [CompleteSpace E]

/-! ## "Unchanged along a field" comes back -/

/-- **"Unchanged along a field" comes back, at the point with coordinates `x`.** If moving along
the field `ξ'` of coordinate space leaves `G` unchanged at `x`, then moving along the field taken
to the curved space leaves `g` unchanged at the point with coordinates `x`. -/
theorem leavesUnchangedAt_pull_of_mem_target (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hread : ReadsAs c g G) {ξ' : Arrows 𝓘(ℝ, E) E} {x : E} (hx : x ∈ c.target)
    (h : Curved.LeavesUnchangedAt (flatMeasure G) ξ' x) :
    Curved.LeavesUnchangedAt g (pushField c ξ') (c.symm x) := by
  have hξ := mdiffAt_pushField hc hx h.1
  refine ⟨hξ, fun X Y hX hY ↦ ?_⟩
  -- The two fields of the curved space, read in the chart.
  have hX' := mdiffAt_carryField_of_mem_target hc hx hX
  have hY' := mdiffAt_carryField_of_mem_target hc hx hY
  have hmain := h.2 (carryField c X) (carryField c Y) hX' hY'
  -- The function whose slope is taken in the chart is `g` of the two fields, read in the chart.
  have hev : (fun y ↦ flatMeasure G y (carryField c X y) (carryField c Y y))
      =ᶠ[𝓝 x] (fun p ↦ g p (X p) (Y p)) ∘ c.symm :=
    Filter.eventuallyEq_of_mem (c.open_target.mem_nhds hx)
      fun y hy ↦ readsAs_carryField hread X Y hy
  have hslope : d% (fun y ↦ flatMeasure G y (carryField c X y) (carryField c Y y)) x (ξ' x)
      = d% (fun p ↦ g p (X p) (Y p)) (c.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x (ξ' x)) :=
    mvfderiv_eq_of_eventuallyEq_comp_symm hc hx hev (ξ' x)
  have hstep : d% (fun p ↦ g p (X p) (Y p)) (c.symm x) (pushField c ξ' (c.symm x))
      = d% (fun p ↦ g p (X p) (Y p)) (c.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x (ξ' x)) :=
    congrArg (fun u ↦ d% (fun p ↦ g p (X p) (Y p)) (c.symm x) u) (pushField_symm ξ' hx)
  -- The bracket with a field of the curved space, read in the chart, is the bracket in the chart.
  have hbr : ∀ Z : Arrows 𝓘(ℝ, E) M, MDiffAt (T% Z) (c.symm x) →
      carryField c (mlieBracket 𝓘(ℝ, E) (pushField c ξ') Z) x
        = mlieBracket 𝓘(ℝ, E) ξ' (carryField c Z) x := by
    intro Z hZ
    rw [carryField_mlieBracket hc hx hξ hZ]
    refine Filter.EventuallyEq.mlieBracket_vectorField_eq ?_ Filter.EventuallyEq.rfl
    filter_upwards [c.open_target.mem_nhds hx] with y hy
    exact carryField_pushField hc ξ' hy
  have t1 : g (c.symm x) (mlieBracket 𝓘(ℝ, E) (pushField c ξ') X (c.symm x)) (Y (c.symm x))
      = flatMeasure G x (mlieBracket 𝓘(ℝ, E) ξ' (carryField c X) x) (carryField c Y x) :=
    (readsAs_carryField hread (mlieBracket 𝓘(ℝ, E) (pushField c ξ') X) Y hx).symm.trans
      (congrArg (fun a ↦ flatMeasure G x a (carryField c Y x)) (hbr X hX))
  have t2 : g (c.symm x) (X (c.symm x)) (mlieBracket 𝓘(ℝ, E) (pushField c ξ') Y (c.symm x))
      = flatMeasure G x (carryField c X x) (mlieBracket 𝓘(ℝ, E) ξ' (carryField c Y) x) :=
    (readsAs_carryField hread X (mlieBracket 𝓘(ℝ, E) (pushField c ξ') Y) hx).symm.trans
      (congrArg (fun b ↦ flatMeasure G x (carryField c X x) b) (hbr Y hY))
  exact hstep.trans (hslope.symm.trans (hmain.trans (congrArg₂ (fun a b : ℝ ↦ a + b) t1 t2).symm))

/-- **"Unchanged along a field" comes back.** If moving along the field `ξ'` of coordinate space
leaves `G` unchanged at the coordinates of the point `q`, then moving along the field taken to
the curved space leaves `g` unchanged at `q`. -/
theorem leavesUnchangedAt_pull (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hread : ReadsAs c g G) {ξ' : Arrows 𝓘(ℝ, E) E} {q : M} (hq : q ∈ c.source)
    (h : Curved.LeavesUnchangedAt (flatMeasure G) ξ' (c q)) :
    Curved.LeavesUnchangedAt g (pushField c ξ') q := by
  have h' := leavesUnchangedAt_pull_of_mem_target hc hread (c.map_source hq) h
  rw [c.left_inv hq] at h'
  exact h'

/-! ## "Looks the same from every side" comes back -/

/-- **"Looks the same from every side" comes back from a chart.** If the length measure `g` of
the curved space reads as `G` in the chart `c`, and `G` looks the same from every side on the
range of the chart with the three fields `ξ'`, then `g` looks the same from every side on the
domain of the chart, with the three fields taken to the curved space. -/
theorem isRoundOn_pull (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hread : ReadsAs c g G)
    {ξ' : Fin 3 → Arrows 𝓘(ℝ, E) E} (h : Curved.IsRoundOn (flatMeasure G) ξ' c.target) :
    Curved.IsRoundOn g (fun i ↦ pushField c (ξ' i)) c.source where
  isOpen := c.open_source
  smooth := fun i ↦ contMDiffOn_pushField hc subset_rfl (h.smooth i)
  unchanged := fun i q hq ↦
    leavesUnchangedAt_pull hc hread hq (h.unchanged i _ (c.map_source hq))
  likeTurns := fun q hq ↦ by
    have hx := c.map_source hq
    have hd := fun i ↦ (h.unchanged i _ hx).1
    obtain ⟨h01, h12, h20⟩ := h.likeTurns _ hx
    exact ⟨(pushField_mlieBracket hc hq (hd 0) (hd 1)).trans
        (congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q)) h01),
      (pushField_mlieBracket hc hq (hd 1) (hd 2)).trans
        (congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q)) h12),
      (pushField_mlieBracket hc hq (hd 2) (hd 0)).trans
        (congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q)) h20)⟩
  surfaces := fun q hq ↦ by
    have hx := c.map_source hq
    have h1 := (finrank_span_pushField hc ξ' hx).trans (h.surfaces _ hx)
    rw [c.left_inv hq] at h1
    exact h1
  positive := fun q hq ↦ by
    have hx := c.map_source hq
    have h1 := pos_of_mem_span_pushField hc hread ξ' hx (h.positive _ hx)
    rw [c.left_inv hq] at h1
    exact h1

end GravityInLean.BothWays
