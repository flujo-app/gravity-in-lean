/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.BothWays.EmptyOfRelabelled
public import GravityInLean.BothWays.RelabelledOfEmpty

import Mathlib.Tactic

/-!
# Birkhoff's theorem, both ways, in coordinates

Board item `task:bothways-incoordinates`. The statement `BirkhoffExactlyWhenInCoordinates` of
`Goals/ExactlyWhen.lean`, from its two directions: "empty, so Schwarzschild's after new labels"
(`relabelled_of_empty`) and "Schwarzschild's after new labels, so empty" (`empty_of_relabelled`).
-/

@[expose] public section

namespace GravityInLean

/-- **Birkhoff's theorem, both ways, in coordinates.** A round table whose spheres give a usable
distance is empty exactly when it is Schwarzschild's after new labels for time and distance. -/
theorem birkhoffExactlyWhenInCoordinates : BirkhoffExactlyWhenInCoordinates :=
  fun _ _ _ _ h husable ↦ ⟨relabelled_of_empty h husable, empty_of_relabelled h⟩

end GravityInLean
