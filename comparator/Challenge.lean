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
import GravityInLean.Goals.GlobalComplete
import GravityInLean.Goals.OneMass
import GravityInLean.Goals.Tests
import GravityInLean.Goals.Turns

/-!
# The question for `lake comparator`

Every statement that `Audit.lean` checks against its proof: 58 in all. Each appears
under the same full name as its proof in the project and with the statement fixed in `Goals/`
or `Curved/Goal.lean`, but with `sorry` (a hole) in place of a proof. This file imports only
the statement files (which bring the definitions and a few checks with them). It is written
from the `example : Statement := proof` lines of `Audit.lean` by
`scripts/comparator/make_challenge.py`, which also writes `comparator.json`; the workflow
"Compare statements" fails when the two are out of date. `connectionUnique` is asked under
the second name `connectionUniqueForComparator`, which only `Audit.lean` declares: the
statement files already load its proof, so this file could not declare its own name.

`lake comparator` (configured in `comparator.json` at the top of the repository) builds this
file and `Audit.lean` inside its sandbox, and accepts only if each named result in `Audit.lean`
has exactly the statement written here, rests on no assumption beyond `propext`,
`Classical.choice` and `Quot.sound`, and passes the kernel and the other checkers.

Because of the holes, this file is not built by `lake build`, and nothing in the project imports
it: it lives in its own library (`Challenge` in `lakefile.toml`), outside the default targets.
-/

/-! ## Birkhoff's theorem with no coordinates (`Curved/Goal.lean`) -/

theorem GravityInLean.birkhoffNoCoordinates : GravityInLean.Curved.BirkhoffNoCoordinates :=
  sorry

/-! ## The two results the standard library did not have (`Goals/Turns.lean`) -/

theorem GravityInLean.smoothFlow : GravityInLean.SmoothFlowStatement :=
  sorry

theorem GravityInLean.turnsCoordinates : GravityInLean.TurnsCoordinatesStatement :=
  sorry

/-! ## Both directions, and checks of their assumptions (`Goals/ExactlyWhen.lean`) -/

theorem GravityInLean.schwarzschildExactlyWhen : GravityInLean.Curved.SchwarzschildExactlyWhen :=
  sorry

theorem GravityInLean.schwarzschildIsEmpty : GravityInLean.Curved.SchwarzschildIsEmptyStatement :=
  sorry

theorem GravityInLean.birkhoffExactlyWhenInCoordinates :
    GravityInLean.BirkhoffExactlyWhenInCoordinates :=
  sorry

theorem GravityInLean.exactlyWhenAssumptionsMet : GravityInLean.ExactlyWhenAssumptionsMet :=
  sorry

theorem GravityInLean.exactlyWhenAssumptionsMetInside :
    GravityInLean.ExactlyWhenAssumptionsMetInside :=
  sorry

theorem GravityInLean.exactlyWhenNotAlwaysEmpty : GravityInLean.ExactlyWhenNotAlwaysEmpty :=
  sorry

/-! ## The 25 tests in which a definition must fail or hold (`Goals/Tests.lean`) -/

theorem GravityInLean.Curved.Tests.efIsSpaceTimeOn : GravityInLean.Curved.Tests.EfIsSpaceTimeOn :=
  sorry

theorem GravityInLean.Curved.Tests.efIsEmptyOn : GravityInLean.Curved.Tests.EfIsEmptyOn :=
  sorry

theorem GravityInLean.Curved.Tests.efIsRoundOn : GravityInLean.Curved.Tests.EfIsRoundOn :=
  sorry

theorem GravityInLean.Curved.Tests.efNotUsableOnRim : GravityInLean.Curved.Tests.EfNotUsableOnRim :=
  sorry

theorem GravityInLean.Curved.Tests.cylIsRoundOn : GravityInLean.Curved.Tests.CylIsRoundOn :=
  sorry

theorem GravityInLean.Curved.Tests.cylNotUsable : GravityInLean.Curved.Tests.CylNotUsable :=
  sorry

theorem GravityInLean.Curved.Tests.cylNotEmpty : GravityInLean.Curved.Tests.CylNotEmpty :=
  sorry

theorem GravityInLean.Curved.Tests.zeroNotRound : GravityInLean.Curved.Tests.ZeroNotRound :=
  sorry

theorem GravityInLean.Curved.Tests.zeroMeetsOtherClauses :
    GravityInLean.Curved.Tests.ZeroMeetsOtherClauses :=
  sorry

theorem GravityInLean.Curved.Tests.schwFlippedNotSpaceTime :
    GravityInLean.Curved.Tests.SchwFlippedNotSpaceTime :=
  sorry

theorem GravityInLean.Curved.Tests.schwFlippedNotRound :
    GravityInLean.Curved.Tests.SchwFlippedNotRound :=
  sorry

theorem GravityInLean.Curved.Tests.schwFlippedIsEmpty :
    GravityInLean.Curved.Tests.SchwFlippedIsEmpty :=
  sorry

theorem GravityInLean.Curved.Tests.twoTimeNotSpaceTime :
    GravityInLean.Curved.Tests.TwoTimeNotSpaceTime :=
  sorry

theorem GravityInLean.Curved.Tests.flatDegNotOneTime :
    GravityInLean.Curved.Tests.FlatDegNotOneTime :=
  sorry

theorem GravityInLean.Curved.Tests.squashNotUnchanged :
    GravityInLean.Curved.Tests.SquashNotUnchanged :=
  sorry

theorem GravityInLean.Curved.Tests.squashUnchangedAxis :
    GravityInLean.Curved.Tests.SquashUnchangedAxis :=
  sorry

theorem GravityInLean.Curved.Tests.squashNotRound : GravityInLean.Curved.Tests.SquashNotRound :=
  sorry

theorem GravityInLean.Curved.Tests.deSitterIsRoundOn :
    GravityInLean.Curved.Tests.DeSitterIsRoundOn :=
  sorry

theorem GravityInLean.Curved.Tests.deSitterUsable : GravityInLean.Curved.Tests.DeSitterUsable :=
  sorry

theorem GravityInLean.Curved.Tests.deSitterNotSchwarzschild :
    GravityInLean.Curved.Tests.DeSitterNotSchwarzschild :=
  sorry

theorem GravityInLean.Curved.Tests.minkowskiIsRoundOn :
    GravityInLean.Curved.Tests.MinkowskiIsRoundOn :=
  sorry

theorem GravityInLean.Curved.Tests.minkowskiUsable : GravityInLean.Curved.Tests.MinkowskiUsable :=
  sorry

theorem GravityInLean.Curved.Tests.kinkNotUnchanged : GravityInLean.Curved.Tests.KinkNotUnchanged :=
  sorry

theorem GravityInLean.Curved.Tests.kinkNotSmooth : GravityInLean.Curved.Tests.KinkNotSmooth :=
  sorry

theorem GravityInLean.Curved.Tests.isEmptyOnNegIff.{u, v, w} :
    GravityInLean.Curved.Tests.IsEmptyOnNegIff.{u, v, w} :=
  sorry

/-! ## One mass for a connected region (`Goals/OneMass.lean`) -/

theorem GravityInLean.oneMass : GravityInLean.Curved.OneMassStatement :=
  sorry

/-! ## The connection of a length measure exists and is unique (`Goals/Connection.lean`) -/

theorem GravityInLean.connectionExists : GravityInLean.Curved.ConnectionExistsStatement :=
  sorry

theorem GravityInLean.Curved.connectionUniqueForComparator :
    GravityInLean.Curved.ConnectionUniqueStatement :=
  sorry

/-! ## Every point, the horizon included, and Kruskal's table (`Goals/EveryPoint.lean`) -/

theorem GravityInLean.Curved.kruskalRadiusSpec : GravityInLean.Curved.KruskalRadiusSpec :=
  sorry

theorem GravityInLean.Curved.kruskalRadiusSmooth : GravityInLean.Curved.KruskalRadiusSmooth :=
  sorry

theorem GravityInLean.Curved.kruskalIsSpaceTime : GravityInLean.Curved.KruskalIsSpaceTime :=
  sorry

theorem GravityInLean.Curved.kruskalIsEmpty : GravityInLean.Curved.KruskalIsEmpty :=
  sorry

theorem GravityInLean.Curved.kruskalIsRound : GravityInLean.Curved.KruskalIsRound :=
  sorry

theorem GravityInLean.Curved.kruskalNotUsableOnRim : GravityInLean.Curved.KruskalNotUsableOnRim :=
  sorry

theorem GravityInLean.Curved.kruskalMeetsConclusion : GravityInLean.Curved.KruskalMeetsConclusion :=
  sorry

theorem GravityInLean.Curved.deSitterNotKruskal : GravityInLean.Curved.DeSitterNotKruskal :=
  sorry

theorem GravityInLean.Curved.kruskalHoldsSchwarzschild :
    GravityInLean.Curved.KruskalHoldsSchwarzschild :=
  sorry

theorem GravityInLean.Curved.birkhoffAtEveryPoint : GravityInLean.Curved.BirkhoffAtEveryPoint :=
  sorry

theorem GravityInLean.Curved.birkhoffAtEveryPointOneMass :
    GravityInLean.Curved.BirkhoffAtEveryPointOneMass :=
  sorry

/-! ## The whole space-time (`Goals/Global.lean`) -/

theorem GravityInLean.Curved.globalBirkhoff : GravityInLean.Curved.GlobalBirkhoff :=
  sorry

theorem GravityInLean.Curved.globalBirkhoffUnique : GravityInLean.Curved.GlobalBirkhoffUnique :=
  sorry

theorem GravityInLean.Curved.globalBirkhoffConverse : GravityInLean.Curved.GlobalBirkhoffConverse :=
  sorry

theorem GravityInLean.Curved.globalMassUnique : GravityInLean.Curved.GlobalMassUnique :=
  sorry

theorem GravityInLean.Curved.kruskalMapOfSchwarzschild :
    GravityInLean.Curved.KruskalMapOfSchwarzschild :=
  sorry

theorem GravityInLean.Curved.globalDeSitterNoMap : GravityInLean.Curved.GlobalDeSitterNoMap :=
  sorry

theorem GravityInLean.Curved.globalUniqueNeedsOnePiece :
    GravityInLean.Curved.GlobalUniqueNeedsOnePiece :=
  sorry

/-! ## The proved statements of the classification file (`Goals/GlobalComplete.lean`) -/

theorem GravityInLean.Curved.freeFallAnyChart : GravityInLean.Curved.FreeFallAnyChart :=
  sorry

theorem GravityInLean.Curved.turnFixesPoint : GravityInLean.Curved.TurnFixesPoint :=
  sorry

theorem GravityInLean.Curved.sphereFreeInvolution : GravityInLean.Curved.SphereFreeInvolution :=
  sorry
