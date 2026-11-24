/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.BothWays.Pull
public import GravityInLean.Join.CarryConnection
public import GravityInLean.Join.CarryCurvature
public import GravityInLean.Join.CarryRound

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# The connection of a length measure comes back along a chart

Board item `task:bothways-pull-connection`. This is `Join/CarryConnection.lean` the other way
round. A chart `c` of the curved space `M` reads the length measure `g` of `M` as the length
measure `G` of coordinate space (`ReadsAs c g G`, `Pull.lean`). A connection `cov'` of coordinate
space is taken to the curved space as `pullTransport c cov'`. This file shows that if `cov'` is
the connection that belongs to `G` on the chart's range, then the connection taken back is the
connection that belongs to `g`, on the chart's domain (`isConnectionOf_pull`).

The four parts of "the connection that belongs to a length measure":

* the chart's domain is open;
* the sum rule and the product rule come back (`isCovariantDerivativeOn_pull`);
* "no twist" comes back, because the bracket of fields carries over (`pullTransport_noTwist`);
* "keeps lengths" comes back, by the chain rule (`pullTransport_keepsLengths`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.BothWays

open GravityInLean.Curved GravityInLean.Join VectorField Bundle

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {c : OpenPartialHomeomorph M E}

/-- Reading fields in the chart respects sums. -/
theorem carryField_add (σ τ : Arrows 𝓘(ℝ, E) M) :
    carryField c (σ + τ) = carryField c σ + carryField c τ := by
  funext x
  exact map_add (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x)) (σ (c.symm x)) (τ (c.symm x))

/-- Reading a field in the chart respects multiplying it by a function. -/
theorem carryField_smul (f : M → ℝ) (σ : Arrows 𝓘(ℝ, E) M) :
    carryField c (f • σ) = (f ∘ c.symm) • carryField c σ := by
  funext x
  exact map_smul (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x)) (f (c.symm x)) (σ (c.symm x))

/-- **The chain rule through the chart, at a point of the chart's domain.** If `f'` is the
function `F` of the curved space read in the chart (`f' y = F (c.symm y)` on the range of the
chart), then the slope of `f'` at `c q` along a step as the chart sees it is the slope of `F` at
`q` along the step itself. -/
theorem mvfderiv_read_in_chart_of_mem_source (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {q : M} (hq : q ∈ c.source) (F : M → ℝ) (f' : E → ℝ)
    (hf : ∀ y ∈ c.target, f' y = F (c.symm y)) (v : TangentSpace 𝓘(ℝ, E) q) :
    d% f' (c q) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q v) = d% F q v := by
  have key : ∀ p : M, p = q → ∀ w : TangentSpace 𝓘(ℝ, E) p,
      d% f' (c q) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c p w) = d% F p w →
      d% f' (c q) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q w) = d% F q w := by
    rintro p rfl w h
    exact h
  exact key (c.symm (c q)) (c.left_inv hq) v
    (mvfderiv_read_in_chart hc (c.map_source hq) F f' hf v)

variable [IsManifold 𝓘(ℝ, E) ∞ M] [CompleteSpace E]
  {g : LengthMeasure 𝓘(ℝ, E) M} {G : E → E →L[ℝ] E →L[ℝ] ℝ} {cov' : Transport 𝓘(ℝ, E) E}

/-- **The sum rule and the product rule come back.** A connection of coordinate space on the
chart's range, taken to the curved space, is a connection on the chart's domain. -/
theorem isCovariantDerivativeOn_pull (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (h : IsCovariantDerivativeOn E cov' c.target) :
    IsCovariantDerivativeOn E (pullTransport c cov') c.source where
  add {σ σ' q} hσ hσ' hq := by
    have e := h.add (mdiffAt_carryField hc hq hσ) (mdiffAt_carryField hc hq hσ')
      (c.map_source hq)
    ext v
    rw [pullTransport_apply, carryField_add, e]
    simp only [add_apply, map_add, pullTransport_apply]
  leibniz {σ f q} hσ hf hq := by
    have hx : c q ∈ c.target := c.map_source hq
    have hcq : c.symm (c q) = q := c.left_inv hq
    have hcs : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q) :=
      (contMDiffAt_symm_of_mem_maximalAtlas hc hx).mdifferentiableAt (by simp)
    have hfc : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (f ∘ c.symm) (c q) :=
      MDifferentiableAt.comp_of_eq (c q) hf hcs hcq
    -- The slope of `f ∘ c.symm` along a step as the chart sees it is the slope of `f`.
    have hd : ∀ v : TangentSpace 𝓘(ℝ, E) q,
        d% (f ∘ c.symm) (c q) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q v) = d% f q v := by
      intro v
      rw [mvfderiv_comp_apply_of_eq (c q) hf hcs hcq, chart_mfderiv_symm_comp hc hq]
    have hσq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q) (carryField c σ (c q)) = σ q :=
      chart_pushField_carryField hc hq σ
    have e := h.leibniz (mdiffAt_carryField hc hq hσ) hfc hx
    ext v
    rw [pullTransport_apply, carryField_smul, e]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, map_add, map_smul, hd, hσq, Function.comp_apply, hcq,
      pullTransport_apply]

/-- **"No twist" comes back.** If the connection of coordinate space has no twist on the chart's
range, the connection taken to the curved space has no twist on the chart's domain. -/
theorem pullTransport_noTwist (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (h : ∀ x ∈ c.target, ∀ X Y : Arrows 𝓘(ℝ, E) E, MDiffAt (T% X) x → MDiffAt (T% Y) x →
      cov' Y x (X x) - cov' X x (Y x) = mlieBracket 𝓘(ℝ, E) X Y x)
    {q : M} (hq : q ∈ c.source) (X Y : Arrows 𝓘(ℝ, E) M)
    (hX : MDiffAt (T% X) q) (hY : MDiffAt (T% Y) q) :
    pullTransport c cov' Y q (X q) - pullTransport c cov' X q (Y q)
      = mlieBracket 𝓘(ℝ, E) X Y q := by
  have hx : c q ∈ c.target := c.map_source hq
  have hcq : c.symm (c q) = q := c.left_inv hq
  have hX' : MDiffAt (T% X) (c.symm (c q)) := by rw [hcq]; exact hX
  have hY' : MDiffAt (T% Y) (c.symm (c q)) := by rw [hcq]; exact hY
  have h1 := h (c q) hx (carryField c X) (carryField c Y)
    (mdiffAt_carryField hc hq hX) (mdiffAt_carryField hc hq hY)
  rw [← carryField_mlieBracket hc hx hX' hY'] at h1
  calc pullTransport c cov' Y q (X q) - pullTransport c cov' X q (Y q)
      = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q)
          (cov' (carryField c Y) (c q) (carryField c X (c q))
            - cov' (carryField c X) (c q) (carryField c Y (c q))) := by
        rw [map_sub, carryField_apply_of_mem_source hq X, carryField_apply_of_mem_source hq Y]
        rfl
    _ = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q)
          (carryField c (mlieBracket 𝓘(ℝ, E) X Y) (c q)) := by rw [h1]
    _ = mlieBracket 𝓘(ℝ, E) X Y q := chart_pushField_carryField hc hq _

/-- **"Keeps lengths" comes back.** If the length measure `g` of the curved space reads as `G` in
the chart, and the connection of coordinate space keeps the lengths of `G` on the chart's range,
then the connection taken to the curved space keeps the lengths of `g` on the chart's domain. -/
theorem pullTransport_keepsLengths (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hread : ReadsAs c g G)
    (h : ∀ x ∈ c.target, ∀ Y Z : Arrows 𝓘(ℝ, E) E, MDiffAt (T% Y) x → MDiffAt (T% Z) x →
      ∀ v : TangentSpace 𝓘(ℝ, E) x,
        d% (fun y ↦ flatMeasure G y (Y y) (Z y)) x v
          = flatMeasure G x (cov' Y x v) (Z x) + flatMeasure G x (Y x) (cov' Z x v))
    {q : M} (hq : q ∈ c.source) (Y Z : Arrows 𝓘(ℝ, E) M)
    (hY : MDiffAt (T% Y) q) (hZ : MDiffAt (T% Z) q) (v : TangentSpace 𝓘(ℝ, E) q) :
    d% (fun y ↦ g y (Y y) (Z y)) q v
      = g q (pullTransport c cov' Y q v) (Z q) + g q (Y q) (pullTransport c cov' Z q v) := by
  have hx : c q ∈ c.target := c.map_source hq
  -- On the chart's range, the function that the chart's connection differentiates is the
  -- function of the curved space, read in the chart.
  have hf : ∀ y ∈ c.target, (fun y ↦ flatMeasure G y (carryField c Y y) (carryField c Z y)) y
      = (fun p ↦ g p (Y p) (Z p)) (c.symm y) := by
    intro y hy
    have key : ∀ z : E, z = y → ∀ a b : E, flatMeasure G z a b = flatMeasure G y a b := by
      rintro z rfl a b
      rfl
    exact (key (c (c.symm y)) (c.right_inv hy) _ _).symm.trans
      (hread (c.symm y) (c.map_target hy) (Y (c.symm y)) (Z (c.symm y))).symm
  rw [← mvfderiv_read_in_chart_of_mem_source hc hq (fun p ↦ g p (Y p) (Z p))
    (fun y ↦ flatMeasure G y (carryField c Y y) (carryField c Z y)) hf v]
  refine (h (c q) hx _ _ (mdiffAt_carryField hc hq hY) (mdiffAt_carryField hc hq hZ) _).trans ?_
  rw [hread q hq (pullTransport c cov' Y q v) (Z q), hread q hq (Y q) (pullTransport c cov' Z q v),
    pullTransport_apply, pullTransport_apply, chart_mfderiv_comp_symm' hc hq,
    chart_mfderiv_comp_symm' hc hq, carryField_apply_of_mem_source hq Y,
    carryField_apply_of_mem_source hq Z]

/-- **The connection of a length measure comes back along a chart.** If the length measure `g` of
the curved space reads as `G` in the chart, and `cov'` is the connection that belongs to `G` on
the chart's range, then `cov'` taken to the curved space is the connection that belongs to `g`,
on the chart's domain. -/
theorem isConnectionOf_pull (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hread : ReadsAs c g G) (h : IsConnectionOf (flatMeasure G) cov' c.target) :
    IsConnectionOf g (pullTransport c cov') c.source where
  isOpen := c.open_source
  isConnection := isCovariantDerivativeOn_pull hc h.isConnection
  noTwist _ hq X Y hX hY := pullTransport_noTwist hc h.noTwist hq X Y hX hY
  keepsLengths _ hq Y Z hY hZ v :=
    pullTransport_keepsLengths hc hread h.keepsLengths hq Y Z hY hZ v

end GravityInLean.BothWays
