/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.SphereSection

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Wrapping Kruskal's table round the sphere can be undone on small pieces

Every point of Kruskal's whole space-time has a neighbourhood on which the wrapping map
`kruskalWrap`, followed by a turn or mirror of the sphere, has a smooth inverse into the region
of Kruskal's table.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

/-- **Wrapping can be undone near every point of Kruskal's whole space-time.** There are a turn
or mirror `R` of the sphere, an open set `U` of lists of five numbers around `p` and a map `ψ`,
smooth on `U`, that sends the points of Kruskal's space-time in `U` into the region of Kruskal's
table, such that wrapping `ψ y` round the sphere and applying `R` gives back `y`. -/
theorem exists_kruskalWrap_section {p : Coords 5} (hp : p ∈ kruskalSpace) :
    ∃ (R : Matrix (Fin 3) (Fin 3) ℝ) (U : Set (Coords 5)) (ψ : Coords 5 → Coords 4),
      R.transpose * R = 1 ∧ IsOpen U ∧ p ∈ U ∧ ContDiffOn ℝ ∞ ψ U ∧
      ∀ y ∈ U, y ∈ kruskalSpace →
        ψ y ∈ kruskalRegion ∧ kruskalSym 1 R (kruskalWrap (ψ y)) = y := by
  sorry

end GravityInLean.Curved
