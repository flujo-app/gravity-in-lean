/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.KruskalChart
public import GravityInLean.Global.SchwChart
public import GravityInLean.Global.TableHess

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# The mass is fixed by the space-time

A map of coordinate space that carries Kruskal's or Schwarzschild's table of one mass to the
table of another mass does not exist unless the masses agree (the curvature scalar and the
squared length of the slope of the radius are kept). So length-keeping maps into models of two
different masses never both exist: `globalMassUnique`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

/-- **Kruskal's tables of two positive masses:** a map that carries one to the other on an open
set that is not empty has equal masses. -/
theorem mass_eq_of_carries_kruskal {m m' : ℝ} (hm : 0 < m) (hm' : 0 < m')
    {f : Coords 4 → Coords 4} {W : Set (Coords 4)} (hW : IsOpen W) (hne : W.Nonempty)
    (hWsub : W ⊆ kruskalRegion) (hfW : ∀ x ∈ W, f x ∈ kruskalRegion)
    (hf : ∀ x ∈ W, CarriesTableAt (kruskalG m) (kruskalG m') f x) : m = m' := by
  sorry

/-- **Schwarzschild's tables of two masses that are zero or negative:** a map that carries one
to the other on an open set that is not empty has equal masses. -/
theorem mass_eq_of_carries_schw {m m' : ℝ} (hm : m ≤ 0) (hm' : m' ≤ 0)
    {f : Coords 4 → Coords 4} {W : Set (Coords 4)} (hW : IsOpen W) (hne : W.Nonempty)
    (hWsub : W ⊆ outside m) (hfW : ∀ x ∈ W, f x ∈ outside m')
    (hf : ∀ x ∈ W,
      CarriesTableAt (roundG (schwA m) (schwB m)) (roundG (schwA m') (schwB m')) f x) :
    m = m' := by
  sorry

/-- **Kruskal's table of a positive mass against Schwarzschild's of a mass that is zero or
negative:** no map carries the first to the second on an open set. -/
theorem not_carries_kruskal_schw {m m' : ℝ} (hm : 0 < m) (hm' : m' ≤ 0)
    {f : Coords 4 → Coords 4} {W : Set (Coords 4)} (hW : IsOpen W) (hne : W.Nonempty)
    (hWsub : W ⊆ kruskalRegion) (hfW : ∀ x ∈ W, f x ∈ outside m')
    (hf : ∀ x ∈ W, CarriesTableAt (kruskalG m) (roundG (schwA m') (schwB m')) f x) : False := by
  sorry

/-- **The mass is fixed by the space-time:** length-keeping maps into models of two different
masses never both exist on a region that is not empty. -/
theorem globalMassUnique : GlobalMassUnique := by
  sorry

end GravityInLean.Curved
