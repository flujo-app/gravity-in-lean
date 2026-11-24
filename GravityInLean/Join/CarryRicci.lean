/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Join.CarryBracket
public import GravityInLean.Curved.Flat
public import Mathlib.LinearAlgebra.Trace

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# The curvature carries over along a chart, given that the full curvature does

Board item `task:join-ricci`. The curvature (`Curved.ricciAt`, the Ricci tensor of the textbooks)
is the trace of the full curvature over its first slot. A trace does not change when a linear
function is read through a linear one-to-one correspondence, and the slope of a chart is such a
correspondence between the steps at a point of the curved space and the steps at its coordinates.

* `traceIn_conj`: the trace read off in a basis, of a function that a correspondence turns into a
  linear function, is the trace of that linear function.
* `ricciAt_carry`: if the full curvature carries over along the chart at a point, and is linear in
  its first step on the chart side, then the curvature carries over at that point.
* `isEmptyOn_carry_of`: so if the curved space is empty, its length measure read in the chart is
  empty on the range of the chart, once the carried connection is known to belong to it.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Join

open GravityInLean.Curved

open scoped Manifold ContDiff Topology

/-- A function `F` of a space of steps, and a linear function `L` of another space of steps, that
a linear one-to-one correspondence `D` between the two spaces turns into each other, have the
same trace, whatever the two bases in which the traces are read off. -/
theorem traceIn_conj {ι ι' V V' : Type*} [Fintype ι] [Fintype ι'] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup V'] [Module ℝ V'] (b : Module.Basis ι ℝ V) (b' : Module.Basis ι' ℝ V')
    (D : V →ₗ[ℝ] V') (Dinv : V' →ₗ[ℝ] V) (h1 : ∀ v, Dinv (D v) = v) (h2 : ∀ v', D (Dinv v') = v')
    (F : V → V) (L : V' →ₗ[ℝ] V') (hF : ∀ u, D (F u) = L (D u)) :
    traceIn b F = traceIn b' L := by
  have hF' : F = ⇑(Dinv ∘ₗ (L ∘ₗ D)) := by
    funext u
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [← hF, h1]
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  have := Module.Free.of_basis b'
  have := Module.Finite.of_basis b'
  rw [hF', traceIn_eq_trace, traceIn_eq_trace, LinearMap.trace_comp_comm']
  congr 1
  ext v'
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [h2]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {c : OpenPartialHomeomorph M E} {g : LengthMeasure 𝓘(ℝ, E) M} {cov : Transport 𝓘(ℝ, E) M}
  {s : Set M}

/-- **The curvature carries over along a chart at a point**, given two things at that point: the
full curvature carries over (`hcurv`), and on the chart side the full curvature is a linear
function of its first step (`hlin`). -/
theorem ricciAt_carry (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {q : M} (hq : q ∈ c.source)
    (hcurv : ∀ u v w : TangentSpace 𝓘(ℝ, E) q,
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q (Curved.curvatureAt cov q u v w)
        = Curved.curvatureAt (carryTransport c cov) (c q) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q u)
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q v) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q w))
    (hlin : ∀ v' w' : E, ∃ L : E →L[ℝ] E, ∀ u',
      Curved.curvatureAt (carryTransport c cov) (c q) u' v' w' = L u')
    (v w : TangentSpace 𝓘(ℝ, E) q) :
    Curved.ricciAt cov q v w
      = Curved.ricciAt (carryTransport c cov) (c q) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q v)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q w) := by
  obtain ⟨L, hL⟩ := hlin (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q v) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q w)
  unfold Curved.ricciAt
  have e : (fun u' : TangentSpace 𝓘(ℝ, E) (c q) ↦
      Curved.curvatureAt (carryTransport c cov) (c q) u' (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q w)) = ⇑L.toLinearMap := funext hL
  rw [e]
  exact traceIn_conj (stepBasis 𝓘(ℝ, E) q) (stepBasis 𝓘(ℝ, E) (c q))
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q).toLinearMap
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q)).toLinearMap
    (fun u ↦ chart_mfderiv_symm_comp hc hq u) (fun u' ↦ chart_mfderiv_comp_symm' hc hq u')
    (fun u ↦ Curved.curvatureAt cov q u v w) L.toLinearMap
    (fun u ↦ (hcurv u v w).trans (hL _))

/-- **Empty carries over along a chart**, given the three things the other files of `Join/`
provide: the carried connection belongs to the carried length measure (`hcov'`), the full
curvature carries over (`hcurv`), and on the chart side the full curvature is linear in its first
step (`hlin`). Then, if the curvature of `cov` vanishes on a region that contains the domain of
the chart, the length measure read in the chart is empty on the range of the chart. -/
theorem isEmptyOn_carry_of (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hs : c.source ⊆ s)
    (hcov' : Curved.IsConnectionOf (flatMeasure (carryMeasure c g)) (carryTransport c cov)
      c.target)
    (hric : ∀ q ∈ s, ∀ v w : TangentSpace 𝓘(ℝ, E) q, Curved.ricciAt cov q v w = 0)
    (hcurv : ∀ q ∈ c.source, ∀ u v w : TangentSpace 𝓘(ℝ, E) q,
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q (Curved.curvatureAt cov q u v w)
        = Curved.curvatureAt (carryTransport c cov) (c q) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q u)
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q v) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q w))
    (hlin : ∀ q ∈ c.source, ∀ v' w' : E, ∃ L : E →L[ℝ] E, ∀ u',
      Curved.curvatureAt (carryTransport c cov) (c q) u' v' w' = L u') :
    Curved.IsEmptyOn (flatMeasure (carryMeasure c g)) c.target := by
  refine ⟨carryTransport c cov, hcov', fun x hx v' w' ↦ ?_⟩
  have hq : c.symm x ∈ c.source := c.map_target hx
  have key : ∀ y : E, c (c.symm x) = y → ∀ v' w' : TangentSpace 𝓘(ℝ, E) y,
      Curved.ricciAt (carryTransport c cov) y v' w' = 0 := by
    rintro y rfl v' w'
    have h := ricciAt_carry hc hq (hcurv _ hq) (hlin _ hq)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c (c.symm x)) v')
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c (c.symm x)) w')
    have e1 := chart_mfderiv_comp_symm' hc hq v'
    have e2 := chart_mfderiv_comp_symm' hc hq w'
    rw [e1, e2] at h
    rw [← h]
    exact hric _ (hs hq) _ _
  exact key x (c.right_inv hx) v' w'

end GravityInLean.Join
