/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.Kretschmann
public import GravityInLean.Global.UniqueFlat

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# The change of charts between two charts that read the length measure as tables

Take two charts `φ` and `φ'` of the curved space. In the first the length measure `g` is the
table `G`, in the second it is the table `H`. Then the change of charts `φ' ∘ φ.symm`, a map of
coordinate space, carries the table `G` to the table `H` near every point where it is defined
(`carriesTableAt_chartChange`): the length of two steps in `G` is the length in `H` of the
steps as the change of charts carries them, because both are the length that `g` gives.

This is the link between length-keeping maps of the curved space and maps of coordinate space
that keep a table. It is shared by the proofs that two length-keeping maps into Kruskal's, or
into Schwarzschild's whole space-time, differ by a symmetry.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  {g : LengthMeasure 𝓘(ℝ, Coords 4) M}

omit [ChartedSpace (Coords 4) M] in
/-- Where the change of charts from `φ` to `φ'` is defined, as a set of coordinate space: it is
open. -/
theorem isOpen_chartChange_domain (φ φ' : OpenPartialHomeomorph M (Coords 4)) :
    IsOpen (φ.target ∩ φ.symm ⁻¹' φ'.source) :=
  φ.isOpen_inter_preimage_symm φ'.open_source

/-- The change of charts between two charts of the curved space is smooth where it is
defined. -/
theorem contDiffOn_chartChange {φ φ' : OpenPartialHomeomorph M (Coords 4)}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M)
    (hφ' : φ' ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M) :
    ContDiffOn ℝ ∞ (φ' ∘ φ.symm) (φ.target ∩ φ.symm ⁻¹' φ'.source) := by
  have h1 : ContMDiffOn 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) ∞ (φ' ∘ φ.symm)
      (φ.target ∩ φ.symm ⁻¹' φ'.source) :=
    (contMDiffOn_of_mem_maximalAtlas hφ').comp
      ((contMDiffOn_symm_of_mem_maximalAtlas hφ).mono inter_subset_left) fun _ hy ↦ hy.2
  exact contMDiffOn_iff_contDiffOn.1 h1

/-- **The change of charts carries one table to the other.** If the length measure `g` is the
table `G` in the chart `φ` and the table `H` in the chart `φ'`, then `φ' ∘ φ.symm` carries `G`
to `H` near every point of coordinate space where it is defined. -/
theorem carriesTableAt_chartChange {G H : Fin 4 → Fin 4 → Coords 4 → ℝ}
    {φ φ' : OpenPartialHomeomorph M (Coords 4)}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M)
    (hφ' : φ' ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M)
    (hG : ∀ q ∈ φ.source ∩ φ'.source, ∀ v w : TangentSpace 𝓘(ℝ, Coords 4) q,
      g q v w = flatMeasure (tableMeasure G) (φ q)
        (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q v)
        (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q w))
    (hH : ∀ q ∈ φ.source ∩ φ'.source, ∀ v w : TangentSpace 𝓘(ℝ, Coords 4) q,
      g q v w = flatMeasure (tableMeasure H) (φ' q)
        (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ' q v)
        (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ' q w))
    {x : Coords 4} (hx : x ∈ φ.target) (hx' : φ.symm x ∈ φ'.source) :
    CarriesTableAt G H (φ' ∘ φ.symm) x := by
  have hW := isOpen_chartChange_domain φ φ'
  have hf := contDiffOn_chartChange hφ hφ'
  have hxW : x ∈ φ.target ∩ φ.symm ⁻¹' φ'.source := ⟨hx, hx'⟩
  have hφmd : φ.MDifferentiable 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas hφ).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas hφ).mdifferentiableOn (by simp)⟩
  refine ⟨hf.contDiffAt (hW.mem_nhds hxW), ?_⟩
  filter_upwards [hW.mem_nhds hxW] with y hy u v
  -- the point of the curved space that `y` describes in the chart `φ`
  have hp : φ.symm y ∈ φ.source := φ.map_target hy.1
  have hp' : φ.symm y ∈ φ'.source := hy.2
  have hyφ : φ (φ.symm y) = y := φ.right_inv hy.1
  obtain ⟨a, ha⟩ := hφmd.mfderiv_surjective hp u
  obtain ⟨b, hb⟩ := hφmd.mfderiv_surjective hp v
  have hφd : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ (φ.symm y) :=
    (contMDiffAt_of_mem_maximalAtlas hφ hp).mdifferentiableAt (by simp)
  have hfd : DifferentiableAt ℝ (φ' ∘ φ.symm) (φ (φ.symm y)) := by
    rw [hyφ]
    exact (hf.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp)
  -- near that point the second chart is the first chart followed by the change of charts
  have hev : φ' =ᶠ[𝓝 (φ.symm y)] (φ' ∘ φ.symm) ∘ φ :=
    Filter.eventuallyEq_of_mem (φ.open_source.mem_nhds hp) fun p hp ↦ by
      change φ' p = φ' (φ.symm (φ p))
      rw [φ.left_inv hp]
  have e1 : g (φ.symm y) a b = tableMeasure G y u v := by
    rw [hG _ ⟨hp, hp'⟩ a b, ha, hb, hyφ]
    rfl
  have e2 : g (φ.symm y) a b = tableMeasure H ((φ' ∘ φ.symm) y)
      (fderiv ℝ (φ' ∘ φ.symm) y u) (fderiv ℝ (φ' ∘ φ.symm) y v) := by
    rw [hH _ ⟨hp, hp'⟩ a b, mfderiv_apply_of_eventuallyEq_comp hfd hφd hev a,
      mfderiv_apply_of_eventuallyEq_comp hfd hφd hev b, ha, hb, hyφ]
    rfl
  exact e2.symm.trans e1

end GravityInLean.Curved
