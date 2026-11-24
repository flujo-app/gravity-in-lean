/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.Checks
public import GravityInLean.Global.TableHess

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# A map of coordinate space that keeps Schwarzschild's table of negative mass

`KeepsSchwOn m f W`: on the open set `W` of the region of Schwarzschild's table (distance
positive, off the poles), the map `f` of coordinate space lands in the region and keeps
Schwarzschild's table of mass `m`. For a negative mass such a map keeps the distance label, keeps
the split of the steps into the `(t, r)` plane and the sphere, and changes time by a shift,
possibly turned round.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

/-- **The map `f` keeps Schwarzschild's table of mass `m` on the open set `W`:** `W` lies in
the region `outside m`, `f` sends `W` into that region, and near every point of `W` the map `f`
is smooth and keeps the lengths of Schwarzschild's table. -/
def KeepsSchwOn (m : ℝ) (f : Coords 4 → Coords 4) (W : Set (Coords 4)) : Prop :=
  IsOpen W ∧ W ⊆ outside m ∧ (∀ x ∈ W, f x ∈ outside m) ∧
    ∀ x ∈ W, CarriesTableAt (roundG (schwA m) (schwB m)) (roundG (schwA m) (schwB m)) f x

variable {m : ℝ} {f : Coords 4 → Coords 4} {W : Set (Coords 4)} {x x₀ : Coords 4}

/-- **The distance label is kept** by a map that keeps Schwarzschild's table of negative mass. -/
theorem KeepsSchwOn.radius (hm : m < 0) (h : KeepsSchwOn m f W) (hx : x ∈ W) : f x 1 = x 1 := by
  sorry

/-- **The split is kept:** such a map carries steps in the `(t, r)` plane to steps in the
`(t, r)` plane, and steps along the sphere to steps along the sphere. -/
theorem KeepsSchwOn.split (hm : m < 0) (h : KeepsSchwOn m f W) (hx : x ∈ W)
    (a i : Fin 4) (hai : (a.val < 2 ∧ 2 ≤ i.val) ∨ (2 ≤ a.val ∧ i.val < 2)) :
    jac f a i x = 0 := by
  sorry

/-- **Time is shifted, possibly turned round:** near every point of the region the new time is
`ε t + c` with `ε = 1` or `ε = -1`. -/
theorem KeepsSchwOn.time (hm : m < 0) (h : KeepsSchwOn m f W) (hx₀ : x₀ ∈ W) :
    ∃ ε c : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ᶠ x in 𝓝 x₀, f x 0 = ε * x 0 + c := by
  sorry

end GravityInLean.Curved
