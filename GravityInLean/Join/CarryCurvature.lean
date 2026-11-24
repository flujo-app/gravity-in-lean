/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Join.Carry
public import GravityInLean.Join.CarryBracket
public import GravityInLean.Join.FlatTensor

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# The full curvature carries over along a chart

Board item `task:join-curvature`. A chart `c` of the curved space `M` reads a connection `cov`
of `M` as a connection `carryTransport c cov` on coordinate space (`Carry.lean`). This file shows
that the full curvature of `cov`, read by the slope of the chart, is the full curvature of the
carried connection:

* `curvatureOfFields_carry`: for three fields of arrows;
* `curvatureAt_carry`: for three steps at a point.

What is assumed: `cov` is the connection of a length measure `g` on a region that contains the
chart's domain, the carried connection is a connection of the carried length measure on the
chart's range, and so is "the plain slope plus a correction `A`" for some `A` that can be
differentiated. The last assumption is what makes fields such as "`Z` carried along `Y`"
differentiable, and it lets the curvature at a point forget how steps were extended to fields
(`FlatTensor.lean`).

How the proof goes. The carried connection is, by its definition, `cov` applied to fields taken
back to the curved space. A field read in the chart and taken back is the field itself on the
chart's domain, and a connection only looks at a field near the point. So "`Z` carried along
`Y`, read in the chart, taken back" is "`Z` carried along `Y`" near the point, and the two outer
derivatives agree. The bracket term is `carryField_mlieBracket`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Join

open GravityInLean.Curved VectorField

open Bundle FiberBundle

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {c : OpenPartialHomeomorph M E}

/-! ## Reading a field at a point of the chart's domain -/

/-- A field of arrows read in the chart, at the coordinates of a point `q` of the chart's domain:
the arrow at `q`, read by the slope of the chart at `q`. -/
theorem carryField_apply_of_mem_source {q : M} (hq : q ∈ c.source) (X : Arrows 𝓘(ℝ, E) M) :
    carryField c X (c q) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q (X q) := by
  have key : ∀ q₁ : M, q₁ = q →
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q₁ (X q₁) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q (X q) := by
    rintro q₁ rfl
    rfl
  exact key (c.symm (c q)) (c.left_inv hq)

/-! ## The carried connection, taken back to the curved space -/

/-- At a point `y` of the chart's range: "the field `σ` carried along `Y`" for the carried
connection, taken back by the slope of the inverse chart, is `cov` applied to the field taken
back, along the arrow of `Y`. -/
theorem mfderiv_symm_carryTransport (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {y : E}
    (hy : y ∈ c.target) (cov : Transport 𝓘(ℝ, E) M) (Y : Arrows 𝓘(ℝ, E) M)
    (σ : Arrows 𝓘(ℝ, E) E) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm y (carryTransport c cov σ y (carryField c Y y))
      = cov (pushField c σ) (c.symm y) (Y (c.symm y)) := by
  rw [carryTransport_apply]
  exact (chart_mfderiv_symm_comp' hc hy _).trans
    (congrArg (fun v ↦ cov (pushField c σ) (c.symm y) v)
      (chart_mfderiv_symm_comp' hc hy (Y (c.symm y))))

/-- The same at a point `q` of the chart's domain: "the field `σ` carried along `Y`" for the
carried connection, taken back to the curved space, is `cov` applied to the field taken back,
along the arrow of `Y`. -/
theorem pushField_carryTransport (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {q : M}
    (hq : q ∈ c.source) (cov : Transport 𝓘(ℝ, E) M) (Y : Arrows 𝓘(ℝ, E) M)
    (σ : Arrows 𝓘(ℝ, E) E) :
    pushField c (fun y ↦ carryTransport c cov σ y (carryField c Y y)) q
      = cov (pushField c σ) q (Y q) := by
  have key : ∀ q₁ : M, c.symm (c q) = q₁ →
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q)
          (carryTransport c cov σ (c q) (carryField c Y (c q)))
        = cov (pushField c σ) q₁ (Y q₁) := by
    rintro q₁ rfl
    exact mfderiv_symm_carryTransport hc (c.map_source hq) cov Y σ
  exact key q (c.left_inv hq)

/-! ## Flat space: a field carried along another can be differentiated -/

section FlatSide

variable {G : E → E →L[ℝ] E →L[ℝ] ℝ} {A : E → E →L[ℝ] E →L[ℝ] E} {t : Set E}
  {cov' : Transport 𝓘(ℝ, E) E} {x : E}

/-- On coordinate space, for any connection of a length measure: "the field `Z` carried along the
field `W`" is a field that can be differentiated at `x`, when `W` can be differentiated there and
`Z` twice, with continuous second slope. -/
theorem mdiffAt_transport_along_of_isConnectionOf (hG : IsLengthMeasureOn (flatMeasure G) t)
    (h₀ : IsConnectionOf (flatMeasure G) (flatTransport A) t)
    (h' : IsConnectionOf (flatMeasure G) cov' t) (hx : x ∈ t) (hA : DifferentiableAt ℝ A x)
    {W Z : Arrows 𝓘(ℝ, E) E} (hW : DifferentiableAt ℝ (plain W) x)
    (hZ : ContDiffAt ℝ 2 (plain Z) x) :
    MDiffAt (T% fun y ↦ cov' Z y (W y)) x := by
  have ht : t ∈ 𝓝 x := h'.isOpen.mem_nhds hx
  have hZ1 : DifferentiableAt ℝ (plain Z) x := hZ.differentiableAt (by simp)
  have hZ2 : DifferentiableAt ℝ (fderiv ℝ (plain Z)) x :=
    (hZ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hZnear : ∀ᶠ y in 𝓝 x, y ∈ t ∧ DifferentiableAt ℝ (plain Z) y :=
    (Filter.eventually_of_mem ht fun y hy ↦ hy).and
      ((hZ.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by simp))
  have hnear : ∀ᶠ y in 𝓝 x, cov' Z y (W y) = flatTransport A Z y (W y) :=
    hZnear.mono fun y hy ↦ by rw [h'.unique hG h₀ hy.1 (mdiffAt_arrows_iff.mpr hy.2)]
  have h0 : MDiffAt (T% fun y ↦ flatTransport A Z y (W y)) x := by
    rw [mdiffAt_arrows_iff]
    have e : plain (fun y ↦ flatTransport A Z y (W y))
        = fun y ↦ fderiv ℝ (plain Z) y (plain W y) + A y (plain Z y) (plain W y) := rfl
    rw [e]
    exact (hZ2.clm_apply hW).add (differentiableAt_apply₂ hA hZ1 hW)
  exact h0.congr_of_eventuallyEq (hnear.mono fun y hy ↦ congrArg (TotalSpace.mk' E y) hy)

end FlatSide

variable [IsManifold 𝓘(ℝ, E) ∞ M] [CompleteSpace E]
  {g : LengthMeasure 𝓘(ℝ, E) M} {cov : Transport 𝓘(ℝ, E) M} {s : Set M}
  {A : E → E →L[ℝ] E →L[ℝ] E}

/-! ## Twice differentiable fields, read in the chart -/

/-- A field that is twice differentiable with continuous second slope at `c.symm x` is so, read
in the chart, at `x`. -/
theorem contMDiffAt_two_carryField (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {X : Arrows 𝓘(ℝ, E) M} {x : E} (hx : x ∈ c.target) (hX : CMDiffAt 2 (T% X) (c.symm x)) :
    CMDiffAt 2 (T% (carryField c X)) x := by
  have h : CMDiffAt 2 (T% (mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm X)) x :=
    ContMDiffAt.mpullback_vectorField_preimage (f := c.symm) (x₀ := x) (n := ∞) hX
      (contMDiffAt_symm_of_mem_maximalAtlas hc hx) (chart_isInvertible_mfderiv_symm hc hx)
      (le_trans (b := (3 : ℕ∞ω)) (by norm_num) ENat.LEInfty.out)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [c.open_target.mem_nhds hx] with y hy
  simp only [carryField_eq_mpullback hc hy]

/-- The same in ordinary words: the field read in the chart is a twice continuously
differentiable function at `x`. -/
theorem contDiffAt_two_carryField (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {X : Arrows 𝓘(ℝ, E) M} {x : E} (hx : x ∈ c.target) (hX : CMDiffAt 2 (T% X) (c.symm x)) :
    ContDiffAt ℝ 2 (plain (carryField c X)) x :=
  contMDiffAt_vectorSpace_iff_contDiffAt.mp (contMDiffAt_two_carryField hc hx hX)

/-! ## A connection only looks at a field near the point -/

/-- Near the point with coordinates `x`: the connection gives the same answer for a field `Z`
and for `Z` read in the chart and taken back. The field read in the chart is assumed twice
continuously differentiable at `x`. -/
theorem eventually_cov_pushField_carryField (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hs : c.source ⊆ s) (hcov : IsConnectionOf g cov s) {Z : Arrows 𝓘(ℝ, E) M} {x : E}
    (hx : x ∈ c.target) (hZ' : ContDiffAt ℝ 2 (plain (carryField c Z)) x) :
    ∀ᶠ q' in 𝓝 (c.symm x),
      q' ∈ c.source ∧ cov (pushField c (carryField c Z)) q' = cov Z q' := by
  have ht : Filter.Tendsto c (𝓝 (c.symm x)) (𝓝 x) := by
    have h := c.continuousAt (c.map_target hx)
    rwa [ContinuousAt, c.right_inv hx] at h
  have hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (plain (carryField c Z)) y :=
    (hZ'.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by simp)
  filter_upwards [ht.eventually hd, c.open_source.mem_nhds (c.map_target hx)] with q' hd' hq'
  have hp : MDiffAt (T% (pushField c (carryField c Z))) q' :=
    mdiffAt_pushField_of_mem_source hc hq' (mdiffAt_arrows_iff.mpr hd')
  have hev : ∀ᶠ q'' in 𝓝 q', pushField c (carryField c Z) q'' = Z q'' :=
    Filter.eventually_of_mem (c.open_source.mem_nhds hq')
      fun q'' h ↦ chart_pushField_carryField hc h Z
  have hZq : MDiffAt (T% Z) q' :=
    hp.congr_of_eventuallyEq (hev.mono fun q'' h ↦ congrArg (TotalSpace.mk' E q'') h.symm)
  exact ⟨hq', hcov.isConnection.congr_of_eventuallyEq hp hZq
    (hcov.isOpen.mem_nhds (hs hq')) hev⟩

/-- **The inner derivative, taken back.** At the point with coordinates `x`: the connection gives
the same answer for "`Z` carried along `Y`" and for the same field computed with the carried
connection in the chart and taken back to the curved space. -/
theorem cov_pushField_carryTransport (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hs : c.source ⊆ s) (hcov : IsConnectionOf g cov s)
    (hG : IsLengthMeasureOn (flatMeasure (carryMeasure c g)) c.target)
    (h₀ : IsConnectionOf (flatMeasure (carryMeasure c g)) (flatTransport A) c.target)
    (h' : IsConnectionOf (flatMeasure (carryMeasure c g)) (carryTransport c cov) c.target)
    {x : E} (hx : x ∈ c.target) (hA : DifferentiableAt ℝ A x) {Y Z : Arrows 𝓘(ℝ, E) M}
    (hY : MDiffAt (T% Y) (c.symm x)) (hZ : CMDiffAt 2 (T% Z) (c.symm x)) :
    cov (pushField c fun y ↦ carryTransport c cov (carryField c Z) y (carryField c Y y))
        (c.symm x)
      = cov (fun q' ↦ cov Z q' (Y q')) (c.symm x) := by
  have hq := c.map_target hx
  have hZ' := contDiffAt_two_carryField hc hx hZ
  have hY' : DifferentiableAt ℝ (plain (carryField c Y)) x :=
    mdiffAt_arrows_iff.mp (mdiffAt_carryField_of_mem_target hc hx hY)
  have hW : MDiffAt
      (T% fun y ↦ carryTransport c cov (carryField c Z) y (carryField c Y y)) x :=
    mdiffAt_transport_along_of_isConnectionOf hG h₀ h' hx hA hY' hZ'
  have hpW := mdiffAt_pushField hc hx hW
  have hnear : ∀ᶠ q' in 𝓝 (c.symm x),
      pushField c (fun y ↦ carryTransport c cov (carryField c Z) y (carryField c Y y)) q'
        = cov Z q' (Y q') := by
    filter_upwards [eventually_cov_pushField_carryField hc hs hcov hx hZ'] with q' hq'
    rw [← hq'.2]
    exact pushField_carryTransport hc hq'.1 cov Y (carryField c Z)
  have hR : MDiffAt (T% fun q' ↦ cov Z q' (Y q')) (c.symm x) :=
    hpW.congr_of_eventuallyEq (hnear.mono fun q' h ↦ congrArg (TotalSpace.mk' E q') h.symm)
  exact hcov.isConnection.congr_of_eventuallyEq hpW hR (hcov.isOpen.mem_nhds (hs hq)) hnear

/-! ## The full curvature carries over -/

/-- **The full curvature of three fields carries over,** at the point with coordinates `x` in the
chart's range: the full curvature of `cov` for the fields `X`, `Y`, `Z`, read by the slope of the
chart, is the full curvature of the carried connection for the three fields read in the chart.
`X` and `Y` can be differentiated at the point, `Z` twice with continuous second slope. -/
theorem curvatureOfFields_carry_of_mem_target (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hs : c.source ⊆ s) (hcov : IsConnectionOf g cov s)
    (hG : IsLengthMeasureOn (flatMeasure (carryMeasure c g)) c.target)
    (h₀ : IsConnectionOf (flatMeasure (carryMeasure c g)) (flatTransport A) c.target)
    (h' : IsConnectionOf (flatMeasure (carryMeasure c g)) (carryTransport c cov) c.target)
    (hA : ∀ x ∈ c.target, DifferentiableAt ℝ A x) {x : E} (hx : x ∈ c.target)
    {X Y Z : Arrows 𝓘(ℝ, E) M} (hX : MDiffAt (T% X) (c.symm x))
    (hY : MDiffAt (T% Y) (c.symm x)) (hZ : CMDiffAt 2 (T% Z) (c.symm x)) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) (curvatureOfFields cov X Y Z (c.symm x))
      = curvatureOfFields (carryTransport c cov) (carryField c X) (carryField c Y)
          (carryField c Z) x := by
  have hZ' := contDiffAt_two_carryField hc hx hZ
  have e1 := cov_pushField_carryTransport hc hs hcov hG h₀ h' hx (hA x hx) hY hZ
  have e2 := cov_pushField_carryTransport hc hs hcov hG h₀ h' hx (hA x hx) hX hZ
  have e3 : cov (pushField c (carryField c Z)) (c.symm x) = cov Z (c.symm x) :=
    (eventually_cov_pushField_carryField hc hs hcov hx hZ').self_of_nhds.2
  have eX : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x (carryField c X x) = X (c.symm x) :=
    chart_mfderiv_symm_comp' hc hx _
  have eY : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x (carryField c Y x) = Y (c.symm x) :=
    chart_mfderiv_symm_comp' hc hx _
  have eB : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x
        (mlieBracket 𝓘(ℝ, E) (carryField c X) (carryField c Y) x)
      = mlieBracket 𝓘(ℝ, E) X Y (c.symm x) := by
    rw [← carryField_mlieBracket hc hx hX hY]
    exact chart_mfderiv_symm_comp' hc hx _
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x)
      (cov (fun y ↦ cov Z y (Y y)) (c.symm x) (X (c.symm x))
        - cov (fun y ↦ cov Z y (X y)) (c.symm x) (Y (c.symm x))
        - cov Z (c.symm x) (mlieBracket 𝓘(ℝ, E) X Y (c.symm x)))
    = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x)
        (cov (pushField c fun y ↦ carryTransport c cov (carryField c Z) y (carryField c Y y))
          (c.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x (carryField c X x)))
      - mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x)
        (cov (pushField c fun y ↦ carryTransport c cov (carryField c Z) y (carryField c X y))
          (c.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x (carryField c Y x)))
      - mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x)
        (cov (pushField c (carryField c Z)) (c.symm x)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x
            (mlieBracket 𝓘(ℝ, E) (carryField c X) (carryField c Y) x)))
  rw [e1, e2, e3, eX, eY, eB, map_sub, map_sub]

/-- **The full curvature of three fields carries over,** at a point `q` of the chart's domain:
the full curvature of `cov` for the fields `X`, `Y`, `Z` at `q`, read by the slope of the chart,
is the full curvature of the carried connection for the three fields read in the chart, at the
coordinates of `q`. -/
theorem curvatureOfFields_carry (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hs : c.source ⊆ s) (hcov : IsConnectionOf g cov s)
    (hG : IsLengthMeasureOn (flatMeasure (carryMeasure c g)) c.target)
    (h₀ : IsConnectionOf (flatMeasure (carryMeasure c g)) (flatTransport A) c.target)
    (h' : IsConnectionOf (flatMeasure (carryMeasure c g)) (carryTransport c cov) c.target)
    (hA : ∀ x ∈ c.target, DifferentiableAt ℝ A x) {q : M} (hq : q ∈ c.source)
    {X Y Z : Arrows 𝓘(ℝ, E) M} (hX : MDiffAt (T% X) q) (hY : MDiffAt (T% Y) q)
    (hZ : CMDiffAt 2 (T% Z) q) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q (curvatureOfFields cov X Y Z q)
      = curvatureOfFields (carryTransport c cov) (carryField c X) (carryField c Y)
          (carryField c Z) (c q) := by
  have key : ∀ q₁ : M, c.symm (c q) = q₁ → MDiffAt (T% X) q₁ → MDiffAt (T% Y) q₁ →
      CMDiffAt 2 (T% Z) q₁ →
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q₁ (curvatureOfFields cov X Y Z q₁)
        = curvatureOfFields (carryTransport c cov) (carryField c X) (carryField c Y)
            (carryField c Z) (c q) := by
    rintro q₁ rfl hX hY hZ
    exact curvatureOfFields_carry_of_mem_target hc hs hcov hG h₀ h' hA (c.map_source hq)
      hX hY hZ
  exact key q (c.left_inv hq) hX hY hZ

/-- **The full curvature at a point carries over.** At a point `q` of the chart's domain, for
three steps `u`, `v`, `w` at `q`: the full curvature of `cov`, read by the slope of the chart, is
the full curvature of the carried connection for the three steps read by the slope of the
chart. -/
theorem curvatureAt_carry (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hs : c.source ⊆ s) (hcov : IsConnectionOf g cov s)
    (hG : IsLengthMeasureOn (flatMeasure (carryMeasure c g)) c.target)
    (h₀ : IsConnectionOf (flatMeasure (carryMeasure c g)) (flatTransport A) c.target)
    (h' : IsConnectionOf (flatMeasure (carryMeasure c g)) (carryTransport c cov) c.target)
    (hA : ∀ x ∈ c.target, DifferentiableAt ℝ A x) {q : M} (hq : q ∈ c.source)
    (u v w : TangentSpace 𝓘(ℝ, E) q) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q (curvatureAt cov q u v w)
      = curvatureAt (carryTransport c cov) (c q) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q u)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q v) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q w) := by
  have hx := c.map_source hq
  have hu : MDiffAt (T% (extend E u)) q := mdifferentiableAt_extend 𝓘(ℝ, E) E u
  have hv : MDiffAt (T% (extend E v)) q := mdifferentiableAt_extend 𝓘(ℝ, E) E v
  have hw : CMDiffAt 2 (T% (extend E w)) q :=
    (contMDiffAt_extend (k := ∞) 𝓘(ℝ, E) E w).of_le ENat.LEInfty.out
  have h1 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q (curvatureAt cov q u v w)
      = curvatureOfFields (carryTransport c cov) (carryField c (extend E u))
          (carryField c (extend E v)) (carryField c (extend E w)) (c q) :=
    curvatureOfFields_carry hc hs hcov hG h₀ h' hA hq hu hv hw
  have hu' : DifferentiableAt ℝ (plain (carryField c (extend E u))) (c q) :=
    mdiffAt_arrows_iff.mp (mdiffAt_carryField hc hq hu)
  have hv' : DifferentiableAt ℝ (plain (carryField c (extend E v))) (c q) :=
    mdiffAt_arrows_iff.mp (mdiffAt_carryField hc hq hv)
  have hw' : ContDiffAt ℝ 2 (plain (carryField c (extend E w))) (c q) :=
    contDiffAt_two_carryField hc hx (by rwa [c.left_inv hq])
  have h2 := curvatureOfFields_eq_curvatureAt_of_isConnectionOf hG h₀ h' hx (hA _ hx)
    hu' hv' hw'
  have eu : carryField c (extend E u) (c q) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q u := by
    rw [carryField_apply_of_mem_source hq, extend_apply_self]
  have ev : carryField c (extend E v) (c q) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q v := by
    rw [carryField_apply_of_mem_source hq, extend_apply_self]
  have ew : carryField c (extend E w) (c q) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q w := by
    rw [carryField_apply_of_mem_source hq, extend_apply_self]
  rw [h1, h2, eu, ev, ew]

end GravityInLean.Join
