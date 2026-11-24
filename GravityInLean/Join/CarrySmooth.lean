/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Join.Carry
public import GravityInLean.Curved.Flat
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Smoothness carries over along a chart

Board item `task:join-smooth`. A length measure `g` on the curved space `M` that is smooth on a
region `s` (`Curved.IsSmoothOn`), read in a chart `c` whose domain lies in `s`, is a smooth
function on the chart's range:

* `contMDiffOn_slope_symm`: a fixed step of coordinate space, taken to the curved space by the
  slope of `c.symm`, is a smooth field of arrows along `c.symm`.
* `contDiffOn_carryMeasure`: every entry `carryMeasure c g x v w` is a smooth function of `x`.
* `contDiffOn_carryMeasure_full`: so is `carryMeasure c g` itself, as a function into the
  two-slot functions (coordinate space of finite dimension).
* `isSmoothOn_carryMeasure`: the same, said in the words of `Curved/Basic.lean`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Join

open GravityInLean.Curved

open Bundle

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {c : OpenPartialHomeomorph M E} {g : LengthMeasure 𝓘(ℝ, E) M} {s : Set M}

/-- A fixed step `v` of coordinate space, taken to the curved space by the slope of `c.symm`, is a
smooth field of arrows along `c.symm`, on the range of the chart. -/
theorem contMDiffOn_slope_symm (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (v : E) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
      (fun x ↦ TotalSpace.mk' E (E := TangentSpace 𝓘(ℝ, E)) (c.symm x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x v)) c.target := by
  have h1 : ContMDiffOn 𝓘(ℝ, E).tangent 𝓘(ℝ, E).tangent ∞
      (tangentMapWithin 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm c.target)
      (TotalSpace.proj ⁻¹' c.target) :=
    (contMDiffOn_symm_of_mem_maximalAtlas hc).contMDiffOn_tangentMapWithin (by simp)
      c.open_target.uniqueMDiffOn
  have h2 : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
      (fun x : E ↦ TotalSpace.mk' E (E := TangentSpace 𝓘(ℝ, E)) x v) c.target :=
    (contMDiffOn_vectorSpace_iff_contDiffOn (V := fun _ : E ↦ v)).mpr contDiffOn_const
  have h3 := h1.comp h2 (fun x hx ↦ hx)
  refine h3.congr fun x hx ↦ ?_
  simp only [Function.comp, tangentMapWithin]
  rw [mfderivWithin_of_isOpen c.open_target hx]

/-- **Every entry of the length measure read in a chart is smooth.** If `g` is smooth on a region
that contains the domain of the chart `c`, then for any two fixed steps `v`, `w` of coordinate
space the number `carryMeasure c g x v w` is a smooth function of the point `x`, on the range of
the chart. -/
theorem contDiffOn_carryMeasure (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hs : c.source ⊆ s) (hg : IsSmoothOn g s) (v w : E) :
    ContDiffOn ℝ ∞ (fun x ↦ carryMeasure c g x v w) c.target := by
  have hsymm := contMDiffOn_symm_of_mem_maximalAtlas hc
  have hψ : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun q : M ↦ TangentSpace 𝓘(ℝ, E) q →L[ℝ] TangentSpace 𝓘(ℝ, E) q →L[ℝ] ℝ)
        (c.symm x) (g (c.symm x))) c.target :=
    ContMDiffOn.comp (g := fun q ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun q : M ↦ TangentSpace 𝓘(ℝ, E) q →L[ℝ] TangentSpace 𝓘(ℝ, E) q →L[ℝ] ℝ)
        q (g q)) hg hsymm (fun x hx ↦ hs (c.map_target hx))
  have h : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞
      (fun x ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (c.symm x)
        (g (c.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x v)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x w))) c.target :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hψ (contMDiffOn_slope_symm hc v)
      (contMDiffOn_slope_symm hc w)
  intro x hx
  have hx' := h x hx
  simp only [contMDiffWithinAt_totalSpace_iff] at hx'
  exact hx'.2.contDiffWithinAt

/-- **The length measure read in a chart is smooth**, as a function from the range of the chart
into the two-slot functions on steps. Coordinate space has finite dimension here. -/
theorem contDiffOn_carryMeasure_full [FiniteDimensional ℝ E]
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hs : c.source ⊆ s) (hg : IsSmoothOn g s) :
    ContDiffOn ℝ ∞ (carryMeasure c g) c.target := by
  rw [contDiffOn_clm_apply]
  intro v
  rw [contDiffOn_clm_apply]
  intro w
  exact contDiffOn_carryMeasure hc hs hg v w

/-- **Smoothness carries over along a chart.** The length measure read in a chart, seen as a
length measure on flat coordinate space, is smooth on the range of the chart in the sense of
`Curved/Basic.lean`. -/
theorem isSmoothOn_carryMeasure [FiniteDimensional ℝ E]
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hs : c.source ⊆ s) (hg : IsSmoothOn g s) :
    IsSmoothOn (flatMeasure (carryMeasure c g)) c.target :=
  isSmoothOn_flat_iff.mpr (contDiffOn_carryMeasure_full hc hs hg)

end GravityInLean.Join
