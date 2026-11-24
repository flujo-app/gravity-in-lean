/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Join.CarryPointwise
public import GravityInLean.Join.CarryBracket
public import GravityInLean.Join.CarrySmooth

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# "Space-time" and "looks the same from every side" carry over along a chart

Board item `task:join-round`. A chart `c` of the curved space `M` reads a length measure `g` and
fields of arrows in coordinates (`carryMeasure`, `carryField` of `Carry.lean`). This file shows
that two of the assumptions of the goal are still true for what the chart reads, on the range of
the chart:

* `isSpaceTimeOn_carry`: the carried measure is a space-time;
* `leavesUnchangedAt_carry`: a field that leaves `g` unchanged, read in the chart, leaves the
  carried measure unchanged;
* `isRoundOn_carry`: the carried measure looks the same from every side, with the three carried
  fields.

The tool for the second is the chain rule through the chart, `mvfderiv_read_in_chart`: the slope
of a function read in the chart, along a step as the chart sees it, is the slope of the function
along the step.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Join

open GravityInLean.Curved VectorField

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {c : OpenPartialHomeomorph M E} {g : LengthMeasure 𝓘(ℝ, E) M} {s : Set M}

/-! ## The chain rule through the chart -/

/-- **The slope of a function read in the chart.** If `f'` is the function `F` of the curved
space read in the chart (`f' y = F (c.symm y)` on the range of the chart), then the slope of `f'`
at `x` along a step as the chart sees it is the slope of `F` along the step itself. Nothing is
asked of `F`: if `F` has no slope at the point, `f'` has none either, and both sides are zero. -/
theorem mvfderiv_read_in_chart (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {x : E}
    (hx : x ∈ c.target) (F : M → ℝ) (f' : E → ℝ) (hf : ∀ y ∈ c.target, f' y = F (c.symm y))
    (v : TangentSpace 𝓘(ℝ, E) (c.symm x)) :
    d% f' x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) v) = d% F (c.symm x) v := by
  have hd := mdifferentiable_of_mem_maximalAtlas hc
  have hev : f' =ᶠ[𝓝 x] F ∘ c.symm :=
    Filter.eventuallyEq_of_mem (c.open_target.mem_nhds hx) hf
  have e1 : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f' x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) v) : ℝ)
      = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (F ∘ c.symm) x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) v) :=
    DFunLike.congr_fun hev.mfderiv_eq _
  have e2 : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (F ∘ c.symm) x
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) v) : ℝ)
      = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) F (c.symm x) v := by
    by_cases hF : MDiffAt F (c.symm x)
    · have e3 := mfderiv_comp x hF (hd.mdifferentiableAt_symm hx)
      exact (DFunLike.congr_fun e3 _).trans
        (congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) F (c.symm x)) (mfderiv_comp_symm' hc hx v))
    · have hF' : ¬ MDiffAt (F ∘ c.symm) x := by
        intro h
        apply hF
        have h2 : MDiffAt ((F ∘ c.symm) ∘ c) (c.symm x) :=
          MDifferentiableAt.comp_of_eq (c.symm x) h (hd.mdifferentiableAt (c.map_target hx))
            (c.right_inv hx)
        refine h2.congr_of_eventuallyEq ?_
        filter_upwards [c.open_source.mem_nhds (c.map_target hx)] with p hp
        simp [c.left_inv hp]
      have a1 : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (F ∘ c.symm) x
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) v) : ℝ) = 0 := by
        rw [mfderiv_zero_of_not_mdifferentiableAt hF']
        rfl
      have a2 : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) F (c.symm x) v : ℝ) = 0 := by
        rw [mfderiv_zero_of_not_mdifferentiableAt hF]
        rfl
      exact a1.trans a2.symm
  exact e1.trans e2

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-! ## A space-time, read in a chart, is a space-time -/

/-- **A space-time, read in a chart, is a space-time** on the range of the chart: the order of
the two steps does not matter, there is one time direction, and it depends smoothly on the
point. -/
theorem isSpaceTimeOn_carry [FiniteDimensional ℝ E]
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hs : c.source ⊆ s)
    (h : Curved.IsSpaceTimeOn g s) :
    Curved.IsSpaceTimeOn (flatMeasure (carryMeasure c g)) c.target where
  symm := fun _ hx v w ↦ carryMeasure_symm g (h.symm _ (hs (c.map_target hx))) v w
  oneTime := fun _ hx ↦
    hasOneTimeDirection_carryMeasure hc g hx (h.oneTime _ (hs (c.map_target hx)))
  smooth := isSmoothOn_carryMeasure hc hs h.smooth

/-! ## "Unchanged along a field" carries over -/

variable [CompleteSpace E]

/-- **"Unchanged along a field" carries over.** If moving along the field `ξ` leaves `g`
unchanged at the point with coordinates `x`, then moving along the field read in the chart leaves
the carried measure unchanged at `x`. -/
theorem leavesUnchangedAt_carry (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {ξ : Arrows 𝓘(ℝ, E) M} {x : E} (hx : x ∈ c.target)
    (h : Curved.LeavesUnchangedAt g ξ (c.symm x)) :
    Curved.LeavesUnchangedAt (flatMeasure (carryMeasure c g)) (carryField c ξ) x := by
  refine ⟨mdiffAt_carryField_of_mem_target hc hx h.1, fun X' Y' hX' hY' ↦ ?_⟩
  -- The two fields of coordinate space, taken to the curved space.
  have hX := mdiffAt_pushField hc hx hX'
  have hY := mdiffAt_pushField hc hx hY'
  have hmain := h.2 (pushField c X') (pushField c Y') hX hY
  -- The function whose slope is taken is `g` of the two fields, read in the chart.
  have hfun : ∀ y ∈ c.target, flatMeasure (carryMeasure c g) y (X' y) (Y' y)
      = g (c.symm y) (pushField c X' (c.symm y)) (pushField c Y' (c.symm y)) := fun y hy ↦
    (congrArg₂ (fun a b ↦ carryMeasure c g y a b) (carryField_pushField hc X' hy).symm
      (carryField_pushField hc Y' hy).symm).trans
      (carryMeasure_carryField hc g (pushField c X') (pushField c Y') hy)
  have hslope : d% (fun y ↦ flatMeasure (carryMeasure c g) y (X' y) (Y' y)) x
        (carryField c ξ x)
      = d% (fun p ↦ g p (pushField c X' p) (pushField c Y' p)) (c.symm x) (ξ (c.symm x)) :=
    mvfderiv_read_in_chart hc hx (fun p ↦ g p (pushField c X' p) (pushField c Y' p))
      (fun y ↦ flatMeasure (carryMeasure c g) y (X' y) (Y' y)) hfun (ξ (c.symm x))
  -- The bracket with a field of coordinate space is the carried bracket.
  have hbr : ∀ Z' : Arrows 𝓘(ℝ, E) E, MDiffAt (T% Z') x →
      mlieBracket 𝓘(ℝ, E) (carryField c ξ) Z' x
        = carryField c (mlieBracket 𝓘(ℝ, E) ξ (pushField c Z')) x := by
    intro Z' hZ'
    rw [carryField_mlieBracket hc hx h.1 (mdiffAt_pushField hc hx hZ')]
    refine Filter.EventuallyEq.mlieBracket_vectorField_eq Filter.EventuallyEq.rfl ?_
    filter_upwards [c.open_target.mem_nhds hx] with y hy
    exact (carryField_pushField hc Z' hy).symm
  have t1 : flatMeasure (carryMeasure c g) x (mlieBracket 𝓘(ℝ, E) (carryField c ξ) X' x) (Y' x)
      = g (c.symm x) (mlieBracket 𝓘(ℝ, E) ξ (pushField c X') (c.symm x))
          (pushField c Y' (c.symm x)) :=
    (congrArg₂ (fun a b ↦ carryMeasure c g x a b) (hbr X' hX')
      (carryField_pushField hc Y' hx).symm).trans
      (carryMeasure_carryField hc g (mlieBracket 𝓘(ℝ, E) ξ (pushField c X')) (pushField c Y') hx)
  have t2 : flatMeasure (carryMeasure c g) x (X' x) (mlieBracket 𝓘(ℝ, E) (carryField c ξ) Y' x)
      = g (c.symm x) (pushField c X' (c.symm x))
          (mlieBracket 𝓘(ℝ, E) ξ (pushField c Y') (c.symm x)) :=
    (congrArg₂ (fun a b ↦ carryMeasure c g x a b) (carryField_pushField hc X' hx).symm
      (hbr Y' hY')).trans
      (carryMeasure_carryField hc g (pushField c X') (mlieBracket 𝓘(ℝ, E) ξ (pushField c Y')) hx)
  exact hslope.trans (hmain.trans (congrArg₂ (fun a b : ℝ ↦ a + b) t1 t2).symm)

/-! ## "Looks the same from every side" carries over -/

/-- **A space-time that looks the same from every side, read in a chart, looks the same from
every side** on the range of the chart, with the three fields read in the chart. -/
theorem isRoundOn_carry (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {ξ : Fin 3 → Arrows 𝓘(ℝ, E) M} (hs : c.source ⊆ s) (h : Curved.IsRoundOn g ξ s) :
    Curved.IsRoundOn (flatMeasure (carryMeasure c g)) (fun i ↦ carryField c (ξ i)) c.target where
  isOpen := c.open_target
  smooth := fun i ↦ contMDiffOn_carryField hc hs (h.smooth i)
  unchanged := fun i _ hx ↦
    leavesUnchangedAt_carry hc hx (h.unchanged i _ (hs (c.map_target hx)))
  likeTurns := fun x hx ↦ by
    have hq := hs (c.map_target hx)
    have hd := fun i ↦ (h.unchanged i _ hq).1
    obtain ⟨h01, h12, h20⟩ := h.likeTurns _ hq
    exact ⟨(carryField_mlieBracket hc hx (hd 0) (hd 1)).symm.trans
        (congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x)) h01),
      (carryField_mlieBracket hc hx (hd 1) (hd 2)).symm.trans
        (congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x)) h12),
      (carryField_mlieBracket hc hx (hd 2) (hd 0)).symm.trans
        (congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x)) h20)⟩
  surfaces := fun _ hx ↦
    (finrank_span_carryField hc ξ hx).trans (h.surfaces _ (hs (c.map_target hx)))
  positive := fun _ hx ↦
    carryMeasure_pos_of_mem_span hc g ξ hx (h.positive _ (hs (c.map_target hx)))

end GravityInLean.Join
