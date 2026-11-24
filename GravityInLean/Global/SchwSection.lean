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
# From ordinary space labels back to distance and angles, on small pieces

Every point of ordinary space and time off the centre has a neighbourhood on which the map
`sphericalToSpace`, followed by a turn or mirror of space, has a smooth inverse.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

/-- **Distance and angles near every point off the centre.** There are a turn or mirror `R` of
space, an open set `U` around `z` and a map `ψ`, smooth on `U`, into the region of
Schwarzschild's table (distance positive, off the poles), such that `sphericalToSpace (ψ y)`
followed by `R` gives back `y`. -/
theorem exists_sphericalToSpace_section {z : Coords 4} (hz : 0 < z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2) :
    ∃ (R : Matrix (Fin 3) (Fin 3) ℝ) (U : Set (Coords 4)) (ψ : Coords 4 → Coords 4),
      R.transpose * R = 1 ∧ IsOpen U ∧ z ∈ U ∧ ContDiffOn ℝ ∞ ψ U ∧
      ∀ y ∈ U, 0 < ψ y 1 ∧ sin (ψ y 2) ≠ 0 ∧ schwSym 1 0 R (sphericalToSpace (ψ y)) = y := by
  sorry

end GravityInLean.Curved
