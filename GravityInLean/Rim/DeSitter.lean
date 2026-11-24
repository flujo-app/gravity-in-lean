/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.EveryPoint
public import GravityInLean.BothWays.NoCoordinates
public import GravityInLean.Checks.DeSitter

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# De Sitter's space-time is Kruskal's in no chart

Board item `task:rim-desitter`. Towards `Curved.DeSitterNotKruskal` of `Goals/EveryPoint.lean`:
"Kruskal's in a chart" can fail.

The argument is the one of `Checks/DeSitter.lean` for Schwarzschild's. If a length measure is
Kruskal's in a chart around a point, it is empty near that point: "empty" comes back from the
chart to the space (`isEmptyOn_pull`). De Sitter's space-time is not empty near any of its
points (`deSitter_not_isEmptyOn_near`). So de Sitter's is Kruskal's in no chart.

Two facts about Kruskal's table are taken as assumptions here, because they are proved in other
files of this folder: that the table is a good table on its region, and that it is empty there.

* `kruskalNear_isEmpty`: Kruskal's in a chart around a point is empty near the point, on any
  curved space.
* `deSitterNotKruskal_of`: the statement `DeSitterNotKruskal`, from the two facts.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean

open Real Set

open scoped Manifold ContDiff

namespace Curved

open GravityInLean.BothWays

/-- **Kruskal's in a chart is empty.** Suppose Kruskal's table for the mass `m` is a good table
on its region (with some table `ginv` as its inverse) and is empty there. Then a length measure
on a curved space that is Kruskal's of mass `m` in some chart around a point is empty on an open
region around that point: the domain of the chart. No symmetry is assumed. -/
theorem kruskalNear_isEmpty {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M] {m : ℝ} {ginv : Fin 4 → Fin 4 → Coords 4 → ℝ}
    (hreg : IsRegularTableOn (kruskalG m) ginv kruskalRegion)
    (hE : IsEmptyOn (flatMeasure (tableMeasure (kruskalG m))) kruskalRegion)
    {g : LengthMeasure 𝓘(ℝ, Coords 4) M} {p : M} (h : IsKruskalNear m g p) :
    ∃ u : Set M, IsOpen u ∧ p ∈ u ∧ IsEmptyOn g u := by
  obtain ⟨φ, hφ, hp, h⟩ := h
  -- The chart lands in Kruskal's region.
  have hsub : φ.target ⊆ kruskalRegion := by
    intro x hx
    have h1 := (h (φ.symm x) (φ.map_target hx)).1
    rw [φ.right_inv hx] at h1
    exact h1
  -- In coordinates, "empty" says that the formula for the curvature vanishes.
  have hflat : ∀ x ∈ kruskalRegion, IsRicciFlatAt (kruskalG m) ginv x := hreg.isEmptyOn_iff.mp hE
  exact ⟨φ.source, φ.open_source, hp,
    isEmptyOn_pull hφ (fun q hq ↦ (h q hq).2)
      (isRegularTableOn_mono hreg φ.open_target hsub) fun x hx ↦ hflat x (hsub hx)⟩

/-- **De Sitter's space-time is Kruskal's in no chart,** for any positive mass, as soon as
Kruskal's table is known to be a good table on its region and to be empty there, for every
positive mass. If there were such a chart around a point, de Sitter's space-time would be empty
near the point, and it is not empty near any of its points. -/
theorem deSitterNotKruskal_of
    (hreg : ∀ m : ℝ, 0 < m → IsRegularTableOn (kruskalG m)
      (genGinv (kruskalA m) (kruskalA m) zero2 (kruskalS m)) kruskalRegion)
    (hE : ∀ m : ℝ, 0 < m → IsEmptyOn (flatMeasure (tableMeasure (kruskalG m))) kruskalRegion) :
    DeSitterNotKruskal := by
  intro L hL m hm p hp hnear
  obtain ⟨u, hu, hpu, hempty⟩ := kruskalNear_isEmpty (hreg m hm) (hE m hm) hnear
  exact Checks.DeSitter.deSitter_not_isEmptyOn_near hL hp hu hpu hempty

end Curved

end GravityInLean
