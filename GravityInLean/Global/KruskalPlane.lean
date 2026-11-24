/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.KruskalKept

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# A map that keeps Kruskal's table changes `(T, X)` by a matrix that keeps `-T² + X²`
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

variable {m : ℝ} {f : Coords 4 → Coords 4} {W : Set (Coords 4)} {x₀ : Coords 4}

/-- **The `(T, X)` part of a map that keeps Kruskal's table:** near every point of its region
the new `T` and `X` are the old ones changed by one matrix `L` that keeps `-T² + X²`. -/
theorem KeepsKruskalOn.plane (hm : 0 < m) (h : KeepsKruskalOn m f W) (hx₀ : x₀ ∈ W) :
    ∃ L : Matrix (Fin 2) (Fin 2) ℝ, L.transpose * lightSign2 * L = lightSign2 ∧
      ∀ᶠ x in 𝓝 x₀, f x 0 = L 0 0 * x 0 + L 0 1 * x 1 ∧ f x 1 = L 1 0 * x 0 + L 1 1 * x 1 := by
  sorry

end GravityInLean.Curved
