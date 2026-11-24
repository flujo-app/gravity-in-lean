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
# A map of coordinate space that keeps Kruskal's table keeps the radius and the split

`KeepsKruskalOn m f W`: on the open set `W` of the region of Kruskal's table, the map `f` of
coordinate space lands in the region and keeps Kruskal's table of mass `m`.

Such a map keeps the radius (so it keeps `X² - T²`), and it keeps the split of the steps into
the `(T, X)` plane and the sphere.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

/-- **The map `f` keeps Kruskal's table of mass `m` on the open set `W`:** `W` lies in the
region of Kruskal's table, `f` sends `W` into that region, and near every point of `W` the map
`f` is smooth and keeps the lengths of Kruskal's table. -/
def KeepsKruskalOn (m : ℝ) (f : Coords 4 → Coords 4) (W : Set (Coords 4)) : Prop :=
  IsOpen W ∧ W ⊆ kruskalRegion ∧ (∀ x ∈ W, f x ∈ kruskalRegion) ∧
    ∀ x ∈ W, CarriesTableAt (kruskalG m) (kruskalG m) f x

variable {m : ℝ} {f : Coords 4 → Coords 4} {W : Set (Coords 4)} {x : Coords 4}

/-- **The radius is kept:** a map that keeps Kruskal's table keeps `X² - T²`. -/
theorem KeepsKruskalOn.radius (hm : 0 < m) (h : KeepsKruskalOn m f W) (hx : x ∈ W) :
    f x 1 ^ 2 - f x 0 ^ 2 = x 1 ^ 2 - x 0 ^ 2 := by
  sorry

/-- **The split is kept:** a map that keeps Kruskal's table carries steps in the `(T, X)` plane
to steps in the `(T, X)` plane, and steps along the sphere to steps along the sphere. -/
theorem KeepsKruskalOn.split (hm : 0 < m) (h : KeepsKruskalOn m f W) (hx : x ∈ W)
    (a i : Fin 4) (hai : (a.val < 2 ∧ 2 ≤ i.val) ∨ (2 ≤ a.val ∧ i.val < 2)) :
    jac f a i x = 0 := by
  sorry

end GravityInLean.Curved
