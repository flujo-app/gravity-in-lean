/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Rim.Empty
public import GravityInLean.Rim.DeSitter
public import GravityInLean.Rim.SchwOutside
public import GravityInLean.Rim.SchwInside

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Kruskal's table: the last two known answers, put together

Board item `task:rim-finish`. Two statements of `Goals/EveryPoint.lean` follow from the other
files of this folder in one step each:

* `deSitterNotKruskal`: de Sitter's space-time is Kruskal's in no chart. Kruskal's table is good
  (`kruskal_regular`) and empty (`kruskalIsEmpty`); de Sitter's is not empty
  (`deSitterNotKruskal_of`).
* `kruskalHoldsSchwarzschild_of`: Schwarzschild's space-time is, near each of its points, a
  piece of Kruskal's, given the part for the points inside the rim. The part for the points
  outside the rim is `kruskalHoldsSchwarzschild_outside`.
* `kruskalHoldsSchwarzschild`: the same with the part for the points inside the rim put in
  (`kruskalHoldsSchwarzschild_inside`).
-/

@[expose] public section

namespace GravityInLean

open Real Set

open scoped Manifold ContDiff

namespace Curved

/-- **De Sitter's space-time is Kruskal's in no chart,** for any positive mass: Kruskal's is
empty and de Sitter's is not. -/
theorem deSitterNotKruskal : DeSitterNotKruskal :=
  deSitterNotKruskal_of (fun _ hm ↦ kruskal_regular hm) kruskalIsEmpty

/-- **Schwarzschild's is, near each of its points, a piece of Kruskal's,** given that this holds
around the points inside the rim. Around the points outside the rim it is proved in
`Rim/SchwOutside.lean`. -/
theorem kruskalHoldsSchwarzschild_of
    (hin : ∀ m : ℝ, 0 < m → ∀ p ∈ inside m,
      IsKruskalNear m (flatMeasure (tableMeasure (roundG (schwA m) (schwB m)))) p) :
    KruskalHoldsSchwarzschild := fun m hm p hp ↦
  hp.elim (fun ho ↦ kruskalHoldsSchwarzschild_outside hm ho) (hin m hm p)

/-- **Schwarzschild's is, near each of its points, a piece of Kruskal's:** for a positive mass,
around every point outside the rim and around every point inside it, Schwarzschild's length
measure is Kruskal's in some chart. -/
theorem kruskalHoldsSchwarzschild : KruskalHoldsSchwarzschild :=
  kruskalHoldsSchwarzschild_of fun _ hm _ hp ↦ kruskalHoldsSchwarzschild_inside hm hp

end Curved

end GravityInLean
