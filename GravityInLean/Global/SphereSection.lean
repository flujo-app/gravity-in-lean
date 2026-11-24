/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.Checks

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Angles for the directions near a given direction

Near every direction of ordinary space, after a turn or mirror that takes the direction
`(1, 0, 0)` to it, the two angles of a direction are smooth functions of the direction.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

/-- **Angles near a direction.** For a vector `y₀` of ordinary space that is not zero there are
a turn or mirror `R`, an open set `U` around `y₀`, and two smooth functions `θ`, `φ` on `U`
such that every `y` in `U` is not zero and has, after `R`, the direction with the pole angle
`θ y` (off the poles) and the angle `φ y` around the axis. -/
theorem exists_sphere_section {y₀ : Fin 3 → ℝ} (hy : 0 < y₀ 0 ^ 2 + y₀ 1 ^ 2 + y₀ 2 ^ 2) :
    ∃ (R : Matrix (Fin 3) (Fin 3) ℝ) (U : Set (Fin 3 → ℝ)) (θ φ : (Fin 3 → ℝ) → ℝ),
      R.transpose * R = 1 ∧ IsOpen U ∧ y₀ ∈ U ∧ ContDiffOn ℝ ∞ θ U ∧ ContDiffOn ℝ ∞ φ U ∧
      ∀ y ∈ U, 0 < y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 ∧ sin (θ y) ≠ 0 ∧
        R.mulVec ![sin (θ y) * cos (φ y), sin (θ y) * sin (φ y), cos (θ y)]
          = (√(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2))⁻¹ • y := by
  sorry

end GravityInLean.Curved
