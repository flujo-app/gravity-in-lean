/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.KruskalSection
public import GravityInLean.Join.Atlas

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# A length-keeping map into Kruskal's gives charts in which the length measure is Kruskal's table

Around every point of its region a length-keeping map `D` into Kruskal's whole space-time is,
up to a turn or mirror of the sphere, the wrapping map after a chart of the curved space; in
that chart the length measure is Kruskal's table.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

section KruskalChart

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  [IsManifold 𝓘(ℝ, Coords 4) ∞ M] {m : ℝ} {g : LengthMeasure 𝓘(ℝ, Coords 4) M} {s : Set M}

/-- **A length-keeping map into Kruskal's is, near each point, wrapping after a chart.** Around
`q` there are a chart `φ` of the curved space with domain inside the region, landing in the
region of Kruskal's table, and a turn or mirror `R` of the sphere, such that `D` is `φ`, then
wrapping, then `R`; and in the chart `φ` the length measure is Kruskal's table. -/
theorem IsKruskalMapOn.exists_chart {D : M → Coords 5} (hD : IsKruskalMapOn m g D s)
    (hg : IsSpaceTimeOn g s) {q : M} (hq : q ∈ s) :
    ∃ (R : Matrix (Fin 3) (Fin 3) ℝ) (φ : OpenPartialHomeomorph M (Coords 4)),
      R.transpose * R = 1 ∧ φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M ∧ q ∈ φ.source ∧
      φ.source ⊆ s ∧
      ∀ q' ∈ φ.source, φ q' ∈ kruskalRegion ∧ D q' = kruskalSym 1 R (kruskalWrap (φ q')) ∧
        ∀ v w : TangentSpace 𝓘(ℝ, Coords 4) q',
          g q' v w = flatMeasure (tableMeasure (kruskalG m)) (φ q')
            (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q' v)
            (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q' w) := by
  sorry

/-- **A space-time with a length-keeping map into Kruskal's is Kruskal's in a chart around
every point of the region.** -/
theorem IsKruskalMapOn.isKruskalNear {D : M → Coords 5} (hD : IsKruskalMapOn m g D s)
    (hg : IsSpaceTimeOn g s) {q : M} (hq : q ∈ s) : IsKruskalNear m g q := by
  obtain ⟨R, φ, -, hφ, hqφ, -, h⟩ := hD.exists_chart hg hq
  exact ⟨φ, hφ, hqφ, fun q' hq' ↦ ⟨(h q' hq').1, (h q' hq').2.2⟩⟩

end KruskalChart

end GravityInLean.Curved
