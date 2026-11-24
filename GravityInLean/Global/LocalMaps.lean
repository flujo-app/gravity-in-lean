/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.Checks
public import GravityInLean.Goals.OneMass

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Near every point of a round, empty space-time there is a length-keeping map into the model

The charts of Birkhoff's theorem at every point, followed by wrapping round the sphere (or by
the change to ordinary space labels), are length-keeping maps on the chart's domain.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  [IsManifold 𝓘(ℝ, Coords 4) ∞ M] {m : ℝ} {g : LengthMeasure 𝓘(ℝ, Coords 4) M}

/-- **Kruskal's in a chart around `p` gives a length-keeping map into Kruskal's whole
space-time on an open set around `p`.** -/
theorem IsKruskalNear.exists_map {p : M} (h : IsKruskalNear m g p) :
    ∃ (U : Set M) (D : M → Coords 5), p ∈ U ∧ IsKruskalMapOn m g D U := by
  obtain ⟨φ, hφ, hp, hpt⟩ := h
  have hsm : ContMDiffOn 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) ∞ φ φ.source :=
    contMDiffOn_of_mem_maximalAtlas hφ
  refine ⟨φ.source, fun q ↦ kruskalWrap (φ q), hp, ⟨φ.open_source,
    contDiff_kruskalWrap.contMDiff.comp_contMDiffOn hsm,
    fun q hq ↦ ⟨kruskalWrap_mem (hpt q hq).1.1, fun v w ↦ ?_⟩⟩⟩
  have hφq : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q :=
    (hsm.contMDiffAt (φ.open_source.mem_nhds hq)).mdifferentiableAt (by simp)
  have hΦ : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 5) kruskalWrap (φ q) :=
    (contDiff_kruskalWrap.contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  change g q v w = flatMeasure (tableMeasure (kruskalWhole m)) (kruskalWrap (φ q))
    (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 5) (kruskalWrap ∘ φ) q v)
    (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 5) (kruskalWrap ∘ φ) q w)
  rw [mfderiv_comp_apply q hΦ hφq v, mfderiv_comp_apply q hΦ hφq w, mfderiv_eq_fderiv,
    (hpt q hq).2 v w]
  exact kruskalWrap_pullback m (φ q) _ _

/-- **Schwarzschild's in a chart around `p`, for a mass that is zero or negative, gives a
length-keeping map into Schwarzschild's whole space-time on an open set around `p`.** -/
theorem IsSchwarzschildWith.exists_map {p : M} (hm : m ≤ 0) (h : IsSchwarzschildWith m g p) :
    ∃ (U : Set M) (D : M → Coords 4), p ∈ U ∧ IsSchwarzschildMapOn m g D U := by
  obtain ⟨φ, hφ, hp, hpt⟩ := h
  have hsm : ContMDiffOn 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) ∞ φ φ.source :=
    contMDiffOn_of_mem_maximalAtlas hφ
  -- the chart lands off the centre and off the rim (for such a mass there is no inside)
  have hr : ∀ q ∈ φ.source, 0 < φ q 1 ∧ φ q 1 ≠ 2 * m := fun q hq ↦ by
    rcases (hpt q hq).1 with h | h
    · exact ⟨h.1, h.2.1.ne'⟩
    · exact absurd h.2.1 (by linarith [h.1, hm])
  refine ⟨φ.source, fun q ↦ sphericalToSpace (φ q), hp, ⟨φ.open_source,
    contDiff_sphericalToSpace.contMDiff.comp_contMDiffOn hsm,
    fun q hq ↦ ⟨Or.inr ?_, fun v w ↦ ?_⟩⟩⟩
  · rw [sphericalToSpace_sumSq]
    exact pow_pos (hr q hq).1 2
  have hφq : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q :=
    (hsm.contMDiffAt (φ.open_source.mem_nhds hq)).mdifferentiableAt (by simp)
  have hΦ : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) sphericalToSpace (φ q) :=
    (contDiff_sphericalToSpace.contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  change g q v w = flatMeasure (tableMeasure (schwSpaceG m)) (sphericalToSpace (φ q))
    (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) (sphericalToSpace ∘ φ) q v)
    (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) (sphericalToSpace ∘ φ) q w)
  rw [mfderiv_comp_apply q hΦ hφq v, mfderiv_comp_apply q hΦ hφq w, mfderiv_eq_fderiv,
    (hpt q hq).2 v w]
  exact sphericalToSpace_pullback m (hr q hq).1 (hr q hq).2 _ _

end GravityInLean.Curved
