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
  sorry

/-- **Schwarzschild's in a chart around `p`, for a mass that is zero or negative, gives a
length-keeping map into Schwarzschild's whole space-time on an open set around `p`.** -/
theorem IsSchwarzschildWith.exists_map {p : M} (hm : m ≤ 0) (h : IsSchwarzschildWith m g p) :
    ∃ (U : Set M) (D : M → Coords 4), p ∈ U ∧ IsSchwarzschildMapOn m g D U := by
  sorry

end GravityInLean.Curved
