/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.Checks
public import GravityInLean.SlopeRules

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# A map of the two angles that keeps the lengths of the sphere is a turn or mirror of the sphere
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

/-- **A map of the angles that keeps the lengths of the unit sphere is a turn or mirror.** Let
`f` be smooth on the open set `W` of coordinate space, off the poles before and after, with new
angles `f x 2`, `f x 3` that do not depend on the first two coordinates, and such that the
length `dθ² + sin² θ dφ²` of steps along the angles is kept. Then near every point of `W` the
point of the unit sphere with the new angles is one fixed turn or mirror `R` applied to the
point with the old angles. -/
theorem sphere_rigid {f : Coords 4 → Coords 4} {W : Set (Coords 4)} {x₀ : Coords 4}
    (hW : IsOpen W) (hx₀ : x₀ ∈ W) (hf : ContDiffOn ℝ ∞ f W)
    (hsin : ∀ x ∈ W, sin (x 2) ≠ 0 ∧ sin (f x 2) ≠ 0)
    (hsplit : ∀ x ∈ W, jac f 2 0 x = 0 ∧ jac f 2 1 x = 0 ∧ jac f 3 0 x = 0 ∧ jac f 3 1 x = 0)
    (hkeep : ∀ x ∈ W, ∀ i j : Fin 4, 2 ≤ i.val → 2 ≤ j.val →
      jac f 2 i x * jac f 2 j x + sin (f x 2) ^ 2 * (jac f 3 i x * jac f 3 j x)
        = if i = j then (if i = 2 then 1 else sin (x 2) ^ 2) else 0) :
    ∃ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 ∧ ∀ᶠ x in 𝓝 x₀,
      (![sin (f x 2) * cos (f x 3), sin (f x 2) * sin (f x 3), cos (f x 2)] : Fin 3 → ℝ)
        = R.mulVec ![sin (x 2) * cos (x 3), sin (x 2) * sin (x 3), cos (x 2)] := by
  sorry

end GravityInLean.Curved
