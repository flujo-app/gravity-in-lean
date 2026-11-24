/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Join.Carry
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.LinearAlgebra.Dimension.Finrank

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Reading a curved space in a chart: what happens at one point

Board item `task:join-pointwise`. A chart `c` of the curved space `M` reads a length measure and
fields of arrows in coordinates (`carryMeasure`, `carryField`, `pushField` of `Carry.lean`). This
file shows the facts that only look at one point at a time:

* the slope of the chart and the slope of its inverse undo each other (`mfderiv_symm_comp`,
  `mfderiv_comp_symm`, `mfderiv_comp_symm'`);
* reading a field and taking it back undo each other (`carryField_pushField`,
  `pushField_carryField`);
* the formula of the goal: `g` at a point of the chart is the carried measure of the steps as the
  chart sees them (`carryMeasure_formula`), and the carried measure of two carried fields is `g`
  of the two fields (`carryMeasure_carryField`);
* "the order of the steps does not matter" and "one time direction" carry over
  (`carryMeasure_symm`, `hasOneTimeDirection_carryMeasure`);
* the directions that three fields span, and "all lengths are positive there", carry over
  (`finrank_span_carryField`, `carryMeasure_pos_of_mem_span`);
* the squared size of the spheres carries over (`sizeSq_carry`).

Nothing here differentiates a field: brackets, connections and curvature are in other files.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Join

open GravityInLean.Curved

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {c : OpenPartialHomeomorph M E}

/-! ## The slopes of a chart and of its inverse undo each other -/

/-- A chart of the curved space can be differentiated, and so can its inverse. -/
theorem mdifferentiable_of_mem_maximalAtlas
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
    c.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
  ⟨fun _ hx ↦ ((contMDiffAt_of_mem_maximalAtlas hc hx).mdifferentiableAt
      (by simp)).mdifferentiableWithinAt,
    fun _ hx ↦ ((contMDiffAt_symm_of_mem_maximalAtlas hc hx).mdifferentiableAt
      (by simp)).mdifferentiableWithinAt⟩

/-- A step at the point `x` of coordinate space, taken to the curved space by the slope of the
inverse chart and read again by the slope of the chart, is the step one started with. -/
theorem mfderiv_symm_comp (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {x : E}
    (hx : x ∈ c.target) (v : TangentSpace 𝓘(ℝ, E) x) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x v) = v :=
  DFunLike.congr_fun ((mdifferentiable_of_mem_maximalAtlas hc).comp_symm_deriv hx) v

/-- A step at the point `q` of the curved space, read by the slope of the chart and taken back by
the slope of the inverse chart, is the step one started with. -/
theorem mfderiv_comp_symm (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {q : M}
    (hq : q ∈ c.source) (v : TangentSpace 𝓘(ℝ, E) q) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q v) = v :=
  DFunLike.congr_fun ((mdifferentiable_of_mem_maximalAtlas hc).symm_comp_deriv hq) v

/-- The same as `mfderiv_comp_symm`, with the point of the curved space named by its
coordinates `x`. -/
theorem mfderiv_comp_symm' (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {x : E}
    (hx : x ∈ c.target) (v : TangentSpace 𝓘(ℝ, E) (c.symm x)) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) v) = v := by
  have key : ∀ y : E, c (c.symm x) = y →
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm y (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) v) = v := by
    rintro y rfl
    exact mfderiv_comp_symm hc (c.map_target hx) v
  exact key x (c.right_inv hx)

/-- The slope of the chart at the point with coordinates `x`, as a one-to-one linear map from the
steps at that point of the curved space onto the steps at `x`. -/
noncomputable def slopeEquiv (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {x : E}
    (hx : x ∈ c.target) :
    TangentSpace 𝓘(ℝ, E) (c.symm x) ≃ₗ[ℝ] TangentSpace 𝓘(ℝ, E) x where
  toFun := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x)
  map_add' := map_add _
  map_smul' := map_smul _
  invFun := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x
  left_inv := mfderiv_comp_symm' hc hx
  right_inv := mfderiv_symm_comp hc hx

theorem slopeEquiv_apply (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {x : E}
    (hx : x ∈ c.target) (v : TangentSpace 𝓘(ℝ, E) (c.symm x)) :
    slopeEquiv hc hx v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) v := rfl

theorem slopeEquiv_symm_apply (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {x : E}
    (hx : x ∈ c.target) (v : TangentSpace 𝓘(ℝ, E) x) :
    (slopeEquiv hc hx).symm v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x v := rfl

/-! ## Reading a field and taking it back -/

/-- A field of arrows on coordinate space, taken to the curved space and read in the chart again,
is the field one started with, on the image of the chart. -/
theorem carryField_pushField (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (X' : Arrows 𝓘(ℝ, E) E) {x : E} (hx : x ∈ c.target) :
    carryField c (pushField c X') x = X' x := by
  have key : ∀ y : E, y = x →
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm y (X' y))
        = X' x := by
    rintro y rfl
    exact mfderiv_symm_comp hc hx _
  exact key (c (c.symm x)) (c.right_inv hx)

/-- A field of arrows on the curved space, read in the chart and taken back, is the field one
started with, on the domain of the chart. -/
theorem pushField_carryField (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (X : Arrows 𝓘(ℝ, E) M) {q : M} (hq : q ∈ c.source) :
    pushField c (carryField c X) q = X q := by
  have key : ∀ q' : M, q' = q →
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q' (X q'))
        = X q := by
    rintro q' rfl
    exact mfderiv_comp_symm hc hq _
  exact key (c.symm (c q)) (c.left_inv hq)

/-! ## The formula of the goal -/

/-- **The formula of the goal.** At a point `q` of the chart, the length measure of two steps is
the carried measure, at the coordinates of `q`, of the two steps as the chart sees them. -/
theorem carryMeasure_formula (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (g : LengthMeasure 𝓘(ℝ, E) M) {q : M} (hq : q ∈ c.source)
    (v w : TangentSpace 𝓘(ℝ, E) q) :
    g q v w = carryMeasure c g (c q) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q w) := by
  have key : ∀ q' : M, q' = q →
      g q' (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q v))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q w)) = g q v w := by
    rintro q' rfl
    exact congrArg₂ (fun a b ↦ g q' a b) (mfderiv_comp_symm hc hq v) (mfderiv_comp_symm hc hq w)
  exact (key (c.symm (c q)) (c.left_inv hq)).symm

/-- The carried measure of two carried fields, at the coordinates `x`, is the length measure of
the two fields at the point with these coordinates. -/
theorem carryMeasure_carryField (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (g : LengthMeasure 𝓘(ℝ, E) M) (X Y : Arrows 𝓘(ℝ, E) M) {x : E} (hx : x ∈ c.target) :
    carryMeasure c g x (carryField c X x) (carryField c Y x)
      = g (c.symm x) (X (c.symm x)) (Y (c.symm x)) :=
  congrArg₂ (fun a b ↦ g (c.symm x) a b) (mfderiv_comp_symm' hc hx (X (c.symm x)))
    (mfderiv_comp_symm' hc hx (Y (c.symm x)))

/-! ## The order of the steps, and one time direction -/

/-- If the order of the two steps does not matter for `g`, it does not matter for the carried
measure. -/
theorem carryMeasure_symm (g : LengthMeasure 𝓘(ℝ, E) M) {x : E}
    (h : ∀ v w : TangentSpace 𝓘(ℝ, E) (c.symm x), g (c.symm x) v w = g (c.symm x) w v)
    (v w : E) : carryMeasure c g x v w = carryMeasure c g x w v :=
  h _ _

/-- If `g` has one time direction at the point with coordinates `x`, the carried measure has one
time direction at `x`. -/
theorem hasOneTimeDirection_carryMeasure (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (g : LengthMeasure 𝓘(ℝ, E) M) {x : E} (hx : x ∈ c.target)
    (h : HasOneTimeDirection (fun v w : TangentSpace 𝓘(ℝ, E) (c.symm x) ↦ g (c.symm x) v w)) :
    HasOneTimeDirection (fun v w : E ↦ carryMeasure c g x v w) := by
  obtain ⟨t, ht, hpos⟩ := h
  have et := mfderiv_comp_symm' hc hx t
  refine ⟨mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) t, ?_, fun v hv hv0 ↦ ?_⟩
  · have e : carryMeasure c g x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) t)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) t) = g (c.symm x) t t :=
      congrArg₂ (fun a b ↦ g (c.symm x) a b) et et
    exact lt_of_eq_of_lt e ht
  · have e : carryMeasure c g x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) t) v
        = g (c.symm x) t (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x v) :=
      congrArg (fun a ↦ g (c.symm x) a (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x v)) et
    have hv' : g (c.symm x) t (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x v) = 0 := e.symm.trans hv
    have hne : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x v ≠ 0 := by
      intro h0
      apply hv0
      have e2 := mfderiv_symm_comp hc hx v
      rw [h0, map_zero] at e2
      exact e2.symm
    exact hpos _ hv' hne

/-! ## The directions that three fields span -/

/-- The directions that carried fields span at `x` are the image, under the slope of the chart,
of the directions that the fields span at the point with coordinates `x`. -/
theorem span_carryField {ι : Type*} (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (ξ : ι → Arrows 𝓘(ℝ, E) M) {x : E} (hx : x ∈ c.target) :
    Submodule.span ℝ (Set.range fun i ↦ carryField c (ξ i) x)
      = (Submodule.span ℝ (Set.range fun i ↦ ξ i (c.symm x))).map
          ((slopeEquiv hc hx : TangentSpace 𝓘(ℝ, E) (c.symm x) ≃ₗ[ℝ] TangentSpace 𝓘(ℝ, E) x)
            : TangentSpace 𝓘(ℝ, E) (c.symm x) →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) x) := by
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

/-- Carried fields span as many directions at `x` as the fields do at the point with coordinates
`x`. (For three turning fields: they sweep out surfaces in the chart as well.) -/
theorem finrank_span_carryField {ι : Type*} (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (ξ : ι → Arrows 𝓘(ℝ, E) M) {x : E} (hx : x ∈ c.target) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range fun i ↦ carryField c (ξ i) x))
      = Module.finrank ℝ (Submodule.span ℝ (Set.range fun i ↦ ξ i (c.symm x))) := by
  rw [span_carryField hc ξ hx]
  exact LinearEquiv.finrank_map_eq _ _

/-- If all lengths are positive on the directions that the fields span at the point with
coordinates `x`, then the carried measure is positive on the directions that the carried fields
span at `x`. -/
theorem carryMeasure_pos_of_mem_span {ι : Type*}
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (g : LengthMeasure 𝓘(ℝ, E) M) (ξ : ι → Arrows 𝓘(ℝ, E) M) {x : E} (hx : x ∈ c.target)
    (h : ∀ v ∈ Submodule.span ℝ (Set.range fun i ↦ ξ i (c.symm x)), v ≠ 0 →
      0 < g (c.symm x) v v) :
    ∀ v ∈ Submodule.span ℝ (Set.range fun i ↦ carryField c (ξ i) x), v ≠ 0 →
      0 < carryMeasure c g x v v := by
  intro v hv hv0
  rw [span_carryField hc ξ hx] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hv0 (map_zero _)
  have e : carryMeasure c g x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) u)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) u) = g (c.symm x) u u :=
    congrArg₂ (fun a b ↦ g (c.symm x) a b) (mfderiv_comp_symm' hc hx u)
      (mfderiv_comp_symm' hc hx u)
  exact lt_of_lt_of_eq (h u hu hu0) e.symm

/-! ## The size of the spheres -/

/-- The squared size of the spheres, read in the chart at `x`, is the squared size of the spheres
at the point with coordinates `x`. -/
theorem sizeSq_carry (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (g : LengthMeasure 𝓘(ℝ, E) M) (ξ : Fin 3 → Arrows 𝓘(ℝ, E) M) {x : E} (hx : x ∈ c.target) :
    sizeSq (flatMeasure (carryMeasure c g)) (fun i ↦ carryField c (ξ i)) x
      = sizeSq g ξ (c.symm x) := by
  have e := fun i ↦ carryMeasure_carryField hc g (ξ i) (ξ i) hx
  change (carryMeasure c g x (carryField c (ξ 0) x) (carryField c (ξ 0) x)
      + carryMeasure c g x (carryField c (ξ 1) x) (carryField c (ξ 1) x)
      + carryMeasure c g x (carryField c (ξ 2) x) (carryField c (ξ 2) x)) / 2
    = (g (c.symm x) (ξ 0 (c.symm x)) (ξ 0 (c.symm x))
      + g (c.symm x) (ξ 1 (c.symm x)) (ξ 1 (c.symm x))
      + g (c.symm x) (ξ 2 (c.symm x)) (ξ 2 (c.symm x))) / 2
  rw [e 0, e 1, e 2]

end GravityInLean.Join
