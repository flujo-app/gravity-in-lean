/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Join.CarryBracket
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# The connection of a length measure carries over along a chart

Board item `task:join-connection`. A chart `c` of the curved space `M` reads a length measure `g`
of `M` as a length measure `carryMeasure c g` on coordinate space, and a connection `cov` of `M`
as a connection `carryTransport c cov` on coordinate space (`Carry.lean`). This file shows that if
`cov` is the connection that belongs to `g` on a region that contains the chart's domain, then
the carried connection is the connection that belongs to the carried length measure, on the
chart's range (`isConnectionOf_carry`).

The four parts of "the connection that belongs to a length measure":

* the chart's range is open;
* the sum rule and the product rule carry over (`isCovariantDerivativeOn_carry`);
* "no twist" carries over, because the bracket of fields does (`carryTransport_noTwist`);
* "keeps lengths" carries over, by the chain rule (`carryTransport_keepsLengths`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Join

open GravityInLean.Curved VectorField Bundle

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {c : OpenPartialHomeomorph M E}

/-- A field on coordinate space, taken to the curved space, at the point with coordinates `x`: the
arrow at `x`, taken along by the slope of the inverse chart at `x`. -/
theorem pushField_symm (X : Arrows 𝓘(ℝ, E) E) {x : E} (hx : x ∈ c.target) :
    pushField c X (c.symm x) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x (X x) := by
  have key : ∀ y : E, y = x →
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm y (X y) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x (X x) := by
    rintro y rfl
    rfl
  exact key (c (c.symm x)) (c.right_inv hx)

/-- Taking fields to the curved space respects sums. -/
theorem pushField_add (X Y : Arrows 𝓘(ℝ, E) E) :
    pushField c (X + Y) = pushField c X + pushField c Y := by
  funext q
  exact map_add (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q)) (X (c q)) (Y (c q))

/-- Taking a field to the curved space respects multiplying it by a function. -/
theorem pushField_smul (f : E → ℝ) (X : Arrows 𝓘(ℝ, E) E) :
    pushField c (f • X) = (f ∘ c) • pushField c X := by
  funext q
  exact map_smul (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q)) (f (c q)) (X (c q))

/-- **The chain rule along the inverse chart, for a number at every point.** If near `x` the
function `f` on coordinate space is the function `F` of the curved space read in the chart, then
the slope of `f` at `x` along a step is the slope of `F` along the step taken to the curved space.
Nothing is asked of `F`: if it cannot be differentiated, both slopes are zero. -/
theorem mvfderiv_eq_of_eventuallyEq_comp_symm (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {F : M → ℝ} {f : E → ℝ} {x : E} (hx : x ∈ c.target) (hev : f =ᶠ[𝓝 x] F ∘ c.symm) (v : E) :
    d% f x v = d% F (c.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x v) := by
  have hq : c.symm x ∈ c.source := c.map_target hx
  have hcs : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x :=
    (contMDiffAt_symm_of_mem_maximalAtlas hc hx).mdifferentiableAt (by simp)
  have hcm : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) :=
    (contMDiffAt_of_mem_maximalAtlas hc hq).mdifferentiableAt (by simp)
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x v
    = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) F (c.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x v)
  by_cases hFd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) F (c.symm x)
  · have h1 := hFd.hasMFDerivAt.comp x hcs.hasMFDerivAt
    have h2 := (h1.congr_of_eventuallyEq_abuse hev).mfderiv
    rw [h2]
    rfl
  · have hfd : ¬ MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x := by
      intro hf
      apply hFd
      have h3 : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (F ∘ c.symm) x :=
        hf.congr_of_eventuallyEq hev.symm
      have h4 : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ((F ∘ c.symm) ∘ c) (c.symm x) :=
        MDifferentiableAt.comp_of_eq (c.symm x) h3 hcm (c.right_inv hx)
      refine h4.congr_of_eventuallyEq ?_
      filter_upwards [c.open_source.mem_nhds hq] with q' hq'
      simp only [Function.comp_apply, c.left_inv hq']
    rw [mfderiv_zero_of_not_mdifferentiableAt hFd, mfderiv_zero_of_not_mdifferentiableAt hfd]
    rfl

variable [IsManifold 𝓘(ℝ, E) ∞ M] [CompleteSpace E]
  {g : LengthMeasure 𝓘(ℝ, E) M} {cov : Transport 𝓘(ℝ, E) M} {s : Set M}

/-- **The sum rule and the product rule carry over.** A connection of the curved space on a region
that contains the chart's domain, read in the chart, is a connection on the chart's range. -/
theorem isCovariantDerivativeOn_carry (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hs : c.source ⊆ s) (h : IsCovariantDerivativeOn E cov s) :
    IsCovariantDerivativeOn E (carryTransport c cov) c.target where
  add {σ σ' x} hσ hσ' hx := by
    have hq : c.symm x ∈ s := hs (c.map_target hx)
    have e := h.add (mdiffAt_pushField hc hx hσ) (mdiffAt_pushField hc hx hσ') hq
    ext v
    rw [carryTransport_apply, pushField_add, e]
    simp only [add_apply, map_add, carryTransport_apply]
  leibniz {σ f x} hσ hf hx := by
    have hq : c.symm x ∈ c.source := c.map_target hx
    have hcq : c (c.symm x) = x := c.right_inv hx
    have hcm : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) :=
      (contMDiffAt_of_mem_maximalAtlas hc hq).mdifferentiableAt (by simp)
    have hfc : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (f ∘ c) (c.symm x) :=
      MDifferentiableAt.comp_of_eq (c.symm x) hf hcm hcq
    -- The slope of `f ∘ c` along a step taken to the curved space is the slope of `f`.
    have hd : ∀ v : E,
        d% (f ∘ c) (c.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x v) = d% f x v := by
      intro v
      rw [mvfderiv_comp_apply_of_eq (c.symm x) hf hcm hcq, chart_mfderiv_comp_symm hc hx]
    have hσx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) (pushField c σ (c.symm x)) = σ x :=
      chart_carryField_pushField hc hx σ
    have e := h.leibniz (mdiffAt_pushField hc hx hσ) hfc (hs hq)
    ext v
    rw [carryTransport_apply, pushField_smul, e]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, map_add, map_smul, hd, hσx, Function.comp_apply, hcq,
      carryTransport_apply]

/-- **"No twist" carries over.** If the connection of the curved space has no twist on a region
that contains the chart's domain, the carried connection has no twist on the chart's range. -/
theorem carryTransport_noTwist (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hs : c.source ⊆ s)
    (h : ∀ q ∈ s, ∀ X Y : Arrows 𝓘(ℝ, E) M, MDiffAt (T% X) q → MDiffAt (T% Y) q →
      cov Y q (X q) - cov X q (Y q) = mlieBracket 𝓘(ℝ, E) X Y q)
    {x : E} (hx : x ∈ c.target) (X Y : Arrows 𝓘(ℝ, E) E)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    carryTransport c cov Y x (X x) - carryTransport c cov X x (Y x)
      = mlieBracket 𝓘(ℝ, E) X Y x := by
  have hq : c.symm x ∈ c.source := c.map_target hx
  have hcq : c (c.symm x) = x := c.right_inv hx
  have hX' : MDiffAt (T% X) (c (c.symm x)) := by rw [hcq]; exact hX
  have hY' : MDiffAt (T% Y) (c (c.symm x)) := by rw [hcq]; exact hY
  have h1 := h (c.symm x) (hs hq) (pushField c X) (pushField c Y)
    (mdiffAt_pushField hc hx hX) (mdiffAt_pushField hc hx hY)
  rw [pushField_mlieBracket hc hq hX' hY'] at h1
  calc carryTransport c cov Y x (X x) - carryTransport c cov X x (Y x)
      = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x)
          (cov (pushField c Y) (c.symm x) (pushField c X (c.symm x))
            - cov (pushField c X) (c.symm x) (pushField c Y (c.symm x))) := by
        rw [map_sub, pushField_symm X hx, pushField_symm Y hx]
        rfl
    _ = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x)
          (pushField c (mlieBracket 𝓘(ℝ, E) X Y) (c.symm x)) := by rw [h1]
    _ = mlieBracket 𝓘(ℝ, E) X Y x := chart_carryField_pushField hc hx _

/-- **"Keeps lengths" carries over.** If the connection of the curved space keeps the lengths of
`g` on a region that contains the chart's domain, the carried connection keeps the lengths of the
carried length measure on the chart's range. -/
theorem carryTransport_keepsLengths (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hs : c.source ⊆ s)
    (h : ∀ q ∈ s, ∀ Y Z : Arrows 𝓘(ℝ, E) M, MDiffAt (T% Y) q → MDiffAt (T% Z) q →
      ∀ v : TangentSpace 𝓘(ℝ, E) q,
        d% (fun y ↦ g y (Y y) (Z y)) q v = g q (cov Y q v) (Z q) + g q (Y q) (cov Z q v))
    {x : E} (hx : x ∈ c.target) (Y Z : Arrows 𝓘(ℝ, E) E)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (v : E) :
    d% (fun y ↦ flatMeasure (carryMeasure c g) y (Y y) (Z y)) x v
      = flatMeasure (carryMeasure c g) x (carryTransport c cov Y x v) (Z x)
        + flatMeasure (carryMeasure c g) x (Y x) (carryTransport c cov Z x v) := by
  have hq : c.symm x ∈ c.source := c.map_target hx
  -- Near `x` the function to differentiate is a function of the curved space, read in the chart.
  have hev : (fun y ↦ flatMeasure (carryMeasure c g) y (Y y) (Z y))
      =ᶠ[𝓝 x] (fun q ↦ g q (pushField c Y q) (pushField c Z q)) ∘ c.symm := by
    filter_upwards [c.open_target.mem_nhds hx] with y hy
    change g (c.symm y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm y (Y y))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm y (Z y))
      = g (c.symm y) (pushField c Y (c.symm y)) (pushField c Z (c.symm y))
    rw [pushField_symm Y hy, pushField_symm Z hy]
  refine (mvfderiv_eq_of_eventuallyEq_comp_symm hc hx hev v).trans ?_
  refine (h (c.symm x) (hs hq) _ _ (mdiffAt_pushField hc hx hY) (mdiffAt_pushField hc hx hZ)
    _).trans ?_
  change _ = g (c.symm x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x)
          (cov (pushField c Y) (c.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x v))))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x (Z x))
      + g (c.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x (Y x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x)
          (cov (pushField c Z) (c.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x v))))
  rw [chart_mfderiv_symm_comp' hc hx, chart_mfderiv_symm_comp' hc hx, pushField_symm Y hx,
    pushField_symm Z hx]

/-- **The connection of a length measure carries over along a chart.** If `cov` is the connection
that belongs to `g` on a region `s` that contains the chart's domain, then the carried connection
is the connection that belongs to the carried length measure, on the chart's range. (That `g` is
smooth is not used.) -/
theorem isConnectionOf_carry (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hs : c.source ⊆ s) (_hg : Curved.IsSmoothOn g s) (h : Curved.IsConnectionOf g cov s) :
    Curved.IsConnectionOf (Curved.flatMeasure (carryMeasure c g)) (carryTransport c cov)
      c.target where
  isOpen := c.open_target
  isConnection := isCovariantDerivativeOn_carry hc hs h.isConnection
  noTwist _ hx X Y hX hY := carryTransport_noTwist hc hs h.noTwist hx X Y hX hY
  keepsLengths _ hx Y Z hY hZ v := carryTransport_keepsLengths hc hs h.keepsLengths hx Y Z hY hZ v

end GravityInLean.Join
