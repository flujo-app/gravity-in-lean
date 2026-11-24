/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
import GravityInLean.Curved.Goal
import GravityInLean.Goals.Connection
import GravityInLean.Goals.EveryPoint
import GravityInLean.Goals.ExactlyWhen
import GravityInLean.Goals.Global
import GravityInLean.Goals.OneMass
import GravityInLean.Goals.Turns

/-!
# The question for `lake comparator`

The sixteen headline results of the project, each under the same full name as in the project and
with the statement fixed in `Goals/` or `Curved/Goal.lean`, but with `sorry` (a hole) in place of
a proof. This file imports the statement files only, none of the proofs.

`lake comparator` (configured in `comparator.json` at the top of the repository) builds this
file and `Audit.lean` inside its sandbox, and accepts only if each named result in `Audit.lean`
has exactly the statement written here, rests on no assumption beyond `propext`,
`Classical.choice` and `Quot.sound`, and passes the kernel.

Because of the holes, this file is not built by `lake build`, and nothing in the project imports
it: it lives in its own library (`Challenge` in `lakefile.toml`), outside the default targets.
-/

/-- Birkhoff's theorem with no coordinates (`Curved/Goal.lean`). -/
theorem GravityInLean.birkhoffNoCoordinates : GravityInLean.Curved.BirkhoffNoCoordinates :=
  sorry

/-- Birkhoff's theorem at every point, the horizon included (`Goals/EveryPoint.lean`). -/
theorem GravityInLean.Curved.birkhoffAtEveryPoint : GravityInLean.Curved.BirkhoffAtEveryPoint :=
  sorry

/-- The same, with one mass for a connected region (`Goals/EveryPoint.lean`). -/
theorem GravityInLean.Curved.birkhoffAtEveryPointOneMass :
    GravityInLean.Curved.BirkhoffAtEveryPointOneMass :=
  sorry

/-- Birkhoff's theorem for a whole space-time (`Goals/Global.lean`). -/
theorem GravityInLean.Curved.globalBirkhoff : GravityInLean.Curved.GlobalBirkhoff :=
  sorry

/-- The map of the global theorem is unique up to the symmetries (`Goals/Global.lean`). -/
theorem GravityInLean.Curved.globalBirkhoffUnique : GravityInLean.Curved.GlobalBirkhoffUnique :=
  sorry

/-- The converse of the global theorem (`Goals/Global.lean`). -/
theorem GravityInLean.Curved.globalBirkhoffConverse :
    GravityInLean.Curved.GlobalBirkhoffConverse :=
  sorry

/-- One mass for a whole space-time (`Goals/Global.lean`). -/
theorem GravityInLean.Curved.globalMassUnique : GravityInLean.Curved.GlobalMassUnique :=
  sorry

/-- Schwarzschild's outside region has a map into Kruskal's (`Goals/Global.lean`). -/
theorem GravityInLean.Curved.kruskalMapOfSchwarzschild :
    GravityInLean.Curved.KruskalMapOfSchwarzschild :=
  sorry

/-- Uniqueness needs a space-time in one piece (`Goals/Global.lean`). -/
theorem GravityInLean.Curved.globalUniqueNeedsOnePiece :
    GravityInLean.Curved.GlobalUniqueNeedsOnePiece :=
  sorry

/-- De Sitter's space-time has no such map (`Goals/Global.lean`). -/
theorem GravityInLean.Curved.globalDeSitterNoMap : GravityInLean.Curved.GlobalDeSitterNoMap :=
  sorry

/-- A length measure has a connection (`Goals/Connection.lean`). -/
theorem GravityInLean.connectionExists : GravityInLean.Curved.ConnectionExistsStatement :=
  sorry

/-- One mass for a connected region (`Goals/OneMass.lean`). -/
theorem GravityInLean.oneMass : GravityInLean.Curved.OneMassStatement :=
  sorry

/-- Schwarzschild's space-time exactly when empty and round (`Goals/ExactlyWhen.lean`). -/
theorem GravityInLean.schwarzschildExactlyWhen : GravityInLean.Curved.SchwarzschildExactlyWhen :=
  sorry

/-- The same in coordinates (`Goals/ExactlyWhen.lean`). -/
theorem GravityInLean.birkhoffExactlyWhenInCoordinates :
    GravityInLean.BirkhoffExactlyWhenInCoordinates :=
  sorry

/-- Paths along a field depend smoothly on where they start (`Goals/Turns.lean`). -/
theorem GravityInLean.smoothFlow : GravityInLean.SmoothFlowStatement :=
  sorry

/-- Coordinates that fit the turns exist (`Goals/Turns.lean`). -/
theorem GravityInLean.turnsCoordinates : GravityInLean.TurnsCoordinatesStatement :=
  sorry
