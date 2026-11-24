/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.BothWays.Pull
public import GravityInLean.Join.CarrySmooth
public import GravityInLean.Join.CarryPointwise
public import Mathlib.Geometry.Manifold.VectorBundle.Hom

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# A space-time in a chart is a space-time on the chart's domain

Board item `task:bothways-pull-spacetime`. `Join/CarrySmooth.lean` and `Join/CarryRound.lean`
read a space-time of the curved space in a chart. This file goes the other way. The length
measure `g` of the curved space reads as `G` in the chart `c` (`ReadsAs c g G` of `Pull.lean`),
and `G` is known on the range of the chart. Then, on the domain of the chart:

* `carryMeasure_eq_of_readsAs`: what the chart reads of `g` is `G`;
* `isSmoothOn_pull`: if `G` is smooth, `g` is smooth;
* `isLengthMeasureOn_pull`: if `G` is a length measure, `g` is a length measure;
* `isSpaceTimeOn_pull`: if `G` is a space-time, `g` is a space-time.

The work is in `isSmoothOn_pull`. Smoothness of `g` is a statement in the charts that the curved
space comes with, not in the chart `c`. Near a point `x₀`, the chart of `x₀` turns `g` into a
two-slot function on plain vectors, and that function is `G` at the coordinates that `c` gives,
with the slope of `c` (as the chart of `x₀` sees it) put into both slots
(`trivializationAt_eq_of_readsAs`). The slope of a smooth map is smooth in this sense
(`ContMDiffAt.mfderiv_const` of the standard library).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.BothWays

open GravityInLean.Curved GravityInLean.Join

open Bundle ContinuousLinearMap

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {c : OpenPartialHomeomorph M E} {g : LengthMeasure 𝓘(ℝ, E) M}
  {G : E → E →L[ℝ] E →L[ℝ] ℝ}

/-! ## The slopes of a chart and of its inverse, at a point of the curved space -/

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- A step at the coordinates of the point `q`, taken to the curved space by the slope of the
inverse chart and read again by the slope of the chart, is the step one started with. -/
theorem mfderiv_symm_comp_at (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {q : M}
    (hq : q ∈ c.source) (u : E) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q) u) = u := by
  have key : ∀ q' : M, c.symm (c q) = q' →
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q' (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q) u) = u := by
    rintro q' rfl
    exact mfderiv_symm_comp hc (c.map_source hq) u
  exact key q (c.left_inv hq)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The slope of the chart sends only the zero step to zero. -/
theorem mfderiv_chart_eq_zero (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {q : M}
    (hq : q ∈ c.source) {v : TangentSpace 𝓘(ℝ, E) q}
    (hv : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q v = 0) : v = 0 := by
  have e := mfderiv_comp_symm hc hq v
  rw [hv, map_zero] at e
  exact e.symm

/-! ## What the chart reads is `G` -/

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- **What the chart reads of `g` is `G`**, on the range of the chart. -/
theorem carryMeasure_eq_of_readsAs (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hread : ReadsAs c g G) {x : E} (hx : x ∈ c.target) : carryMeasure c g x = G x := by
  refine ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext fun w ↦ ?_
  have e1 : carryMeasure c g x v w
      = G (c (c.symm x)) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x v))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x w)) :=
    hread (c.symm x) (c.map_target hx) _ _
  have e2 : G (c (c.symm x)) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x v))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x w))
      = G (c (c.symm x)) v w :=
    congrArg₂ (fun a b : E ↦ G (c (c.symm x)) a b) (mfderiv_symm_comp hc hx v)
      (mfderiv_symm_comp hc hx w)
  have e3 : G (c (c.symm x)) v w = G x v w := by rw [c.right_inv hx]
  exact e1.trans (e2.trans e3)

/-! ## Smoothness comes back -/

/-- Near a point `x₀` of the chart's domain, the chart that the curved space has at `x₀` turns
`g` into a two-slot function on plain vectors. That function is `G`, at the coordinates that `c`
gives, with the slope of `c` in both slots, the slope written as the chart of `x₀` sees it. -/
theorem trivializationAt_eq_of_readsAs (hread : ReadsAs c g G) {x₀ q : M} (hq : q ∈ c.source)
    (hq' : q ∈ (chartAt E x₀).source) :
    (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun q : M ↦ TangentSpace 𝓘(ℝ, E) q →L[ℝ] TangentSpace 𝓘(ℝ, E) q →L[ℝ] ℝ) x₀
        ⟨q, g q⟩).2
      = (G (c q)).bilinearComp
          (inTangentCoordinates 𝓘(ℝ, E) 𝓘(ℝ, E) id c (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c) x₀ q)
          (inTangentCoordinates 𝓘(ℝ, E) 𝓘(ℝ, E) id c (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c) x₀ q) := by
  have hb : q ∈ (trivializationAt (E →L[ℝ] ℝ)
      (fun q : M ↦ TangentSpace 𝓘(ℝ, E) q →L[ℝ] ℝ) x₀).baseSet := by
    simp [hom_trivializationAt_baseSet, hq']
  refine ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext fun w ↦ ?_
  rw [hom_trivializationAt_apply]
  simp only [inCoordinates, inTangentCoordinates, bilinearComp_apply, coe_comp,
    Function.comp_apply, id_eq]
  have e1 : ∀ ψ : TangentSpace 𝓘(ℝ, E) q →L[ℝ] ℝ,
      (trivializationAt (E →L[ℝ] ℝ) (fun q : M ↦ TangentSpace 𝓘(ℝ, E) q →L[ℝ] ℝ)
        x₀).continuousLinearMapAt ℝ q ψ
      = (trivializationAt (E →L[ℝ] ℝ) (fun q : M ↦ TangentSpace 𝓘(ℝ, E) q →L[ℝ] ℝ) x₀
          ⟨q, ψ⟩).2 := fun ψ ↦
    Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hb ψ
  rw [e1, hom_trivializationAt_apply]
  simp only [inCoordinates, coe_comp, Function.comp_apply,
    TangentBundle.continuousLinearMapAt_model_space]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.continuousLinearMapAt_trivialization,
    id_apply]
  exact hread q hq _ _

/-- **Smoothness comes back along a chart.** If `g` reads as `G` in the chart `c`, and `G` is
smooth on the range of the chart, then `g` is smooth on the domain of the chart. -/
theorem isSmoothOn_pull (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hread : ReadsAs c g G) (hG : IsSmoothOn (flatMeasure G) c.target) :
    IsSmoothOn g c.source := by
  have hG' : ContDiffOn ℝ ∞ G c.target := isSmoothOn_flat_iff.mp hG
  intro x₀ hx₀
  rw [contMDiffWithinAt_section_iff]
  -- The slope of `c`, as the chart of `x₀` sees it, depends smoothly on the point.
  have hA : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) ∞
      (inTangentCoordinates 𝓘(ℝ, E) 𝓘(ℝ, E) id c (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c) x₀) x₀ :=
    (contMDiffAt_of_mem_maximalAtlas hc hx₀).mfderiv_const le_rfl
  -- `G` at the coordinates that `c` gives depends smoothly on the point.
  have hGc : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ (fun q ↦ G (c q))
      c.source x₀ :=
    (hG'.contMDiffOn.comp (contMDiffOn_of_mem_maximalAtlas hc) c.mapsTo) x₀ hx₀
  have hflip : ContDiff ℝ ∞ (fun f : E →L[ℝ] E →L[ℝ] ℝ ↦ f.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).contDiff
  have h1 := hflip.comp_contMDiffWithinAt (hGc.clm_comp hA.contMDiffWithinAt)
  have h2 := hflip.comp_contMDiffWithinAt (h1.clm_comp hA.contMDiffWithinAt)
  have hmem : c.source ∩ (chartAt E x₀).source ∈ 𝓝[c.source] x₀ :=
    mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds (c.open_source.inter (chartAt E x₀).open_source)
      ⟨hx₀, mem_chart_source E x₀⟩)
  refine h2.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hmem] with q hq
    exact trivializationAt_eq_of_readsAs hread hq.1 hq.2
  · exact trivializationAt_eq_of_readsAs hread hx₀ (mem_chart_source E x₀)

/-! ## A length measure, and a space-time, come back -/

/-- **A length measure comes back along a chart.** If `g` reads as `G` in the chart `c`, and `G`
is a length measure on the range of the chart, then `g` is a length measure on the domain of the
chart. -/
theorem isLengthMeasureOn_pull (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hread : ReadsAs c g G) (hG : IsLengthMeasureOn (flatMeasure G) c.target) :
    IsLengthMeasureOn g c.source where
  symm := fun q hq v w ↦
    (hread q hq v w).trans ((hG.symm (c q) (c.map_source hq) _ _).trans (hread q hq w v).symm)
  nondegenerate := fun q hq v hv ↦ by
    refine mfderiv_chart_eq_zero hc hq (hG.nondegenerate (c q) (c.map_source hq) _ fun u ↦ ?_)
    have e := hread q hq v (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q) u)
    rw [mfderiv_symm_comp_at hc hq u] at e
    exact e.symm.trans (hv _)
  smooth := isSmoothOn_pull hc hread hG.smooth

/-- **A space-time comes back along a chart.** If `g` reads as `G` in the chart `c`, and `G` is
a space-time on the range of the chart, then `g` is a space-time on the domain of the chart: the
order of the two steps does not matter, there is one time direction, and it depends smoothly on
the point. -/
theorem isSpaceTimeOn_pull (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hread : ReadsAs c g G) (hG : IsSpaceTimeOn (flatMeasure G) c.target) :
    IsSpaceTimeOn g c.source where
  symm := fun q hq v w ↦
    (hread q hq v w).trans ((hG.symm (c q) (c.map_source hq) _ _).trans (hread q hq w v).symm)
  oneTime := fun q hq ↦ by
    obtain ⟨t, ht, hpos⟩ := hG.oneTime (c q) (c.map_source hq)
    refine ⟨mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q) t, ?_, fun v hv hv0 ↦ ?_⟩
    · have e := hread q hq (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q) t)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q) t)
      rw [mfderiv_symm_comp_at hc hq t] at e
      exact lt_of_eq_of_lt e ht
    · have e := hread q hq (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q) t) v
      rw [mfderiv_symm_comp_at hc hq t] at e
      have h0 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q v ≠ 0 := fun h ↦
        hv0 (mfderiv_chart_eq_zero hc hq h)
      exact lt_of_lt_of_eq (hpos _ (e.symm.trans hv) h0) (hread q hq v v).symm
  smooth := isSmoothOn_pull hc hread hG.smooth

end GravityInLean.BothWays
