/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
import GravityInLean
import Lean

/-!
# The judge: what do the results rest on?

Lean accepts a proof with a hole in it (written `sorry`) and only warns. It also lets anyone add
a new assumption (an `axiom`) and then "prove" anything from it. So "it builds" is not enough.

This file closes both doors. It asks Lean what every result in the project rests on, and fails the
build unless the answer is: nothing but Lean's own three standard assumptions
(`propext`, `Classical.choice`, `Quot.sound`), the same three almost all of mathlib uses.
A hole would show up here as `sorryAx`, a made-up assumption under its own name.

It is part of `lake build`, so a green build means: proved, no holes, no extra assumptions.

Careful: this checks the *proofs*. It cannot check that a statement says what we mean it to say.
That part still needs a reader.
-/

open Lean Elab Command

namespace Audit

/-- The only assumptions a result may rest on: the three that Lean and mathlib use everywhere. -/
def allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Everything the declaration `n` rests on that is not on the allowed list. -/
def extraAxioms (n : Name) : CommandElabM (Array Name) := do
  let axs ← collectAxioms n
  return axs.filter fun a => !allowed.contains a

/-- `#audit a b c` fails the build unless each named result exists and rests on nothing but the
allowed assumptions. -/
elab "#audit " ids:ident+ : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let extra ← extraAxioms n
    unless extra.isEmpty do
      throwErrorAt id "{n} rests on more than the standard assumptions: {extra}"
  logInfo m!"{ids.size} named results checked: none rests on more than {allowed}"

/-- `#audit_namespace Foo` fails the build unless every declaration whose name starts with `Foo`
rests on nothing but the allowed assumptions. -/
elab "#audit_namespace " ns:ident : command => do
  let nsName := ns.getId
  let env ← getEnv
  let names := env.constants.fold
    (fun acc n _ => if nsName.isPrefixOf n then acc.push n else acc) (#[] : Array Name)
  if names.isEmpty then
    throwErrorAt ns "nothing found under {nsName}"
  let mut bad : Array MessageData := #[]
  for n in names do
    let extra ← extraAxioms n
    unless extra.isEmpty do
      bad := bad.push m!"{n} rests on {extra}"
  unless bad.isEmpty do
    throwError "audit failed:{indentD (MessageData.joinSep bad.toList Format.line)}"
  logInfo
    m!"all {names.size} declarations under {nsName} checked: none rests on more than {allowed}"

end Audit

/-! ## The headline results, by name

If one of these is renamed or removed, the build fails here, so the tables in the README cannot
quietly go stale. -/

-- Piece A: two ways of writing the same clock rate
#audit GravityInLean.clockRateMap_eq_clockRateTextbook GravityInLean.clockRate_identity
  GravityInLean.clockRateMap_rim GravityInLean.circleRadius_eq

-- Piece B: Schwarzschild's solution makes the three curvature formulas vanish
#audit GravityInLean.schwarzschild_isEmptySpace GravityInLean.schwA_eq_clockRate_sq
  GravityInLean.schwA_mul_schwB

-- Piece C: the clock on a round orbit, and the budget
#audit GravityInLean.orbit_clockRate_sq GravityInLean.roundOrbit_clockRate
  GravityInLean.roundOrbit_kepler GravityInLean.roundOrbit_exists
  GravityInLean.roundOrbit_needs_room GravityInLean.budget GravityInLean.budget_light

-- Probes: curvature from the general formulas, on a sphere and for de Sitter's space-time
#audit GravityInLean.christoffel_sphere GravityInLean.sphereG_mul_sphereGinv
  GravityInLean.ricci_sphere GravityInLean.ricci_deSitter

-- Step 1: the round space-time and free fall, from the general definitions
#audit GravityInLean.christoffel_round GravityInLean.round_ricciFlat_iff
  GravityInLean.schwarzschild_ricciFlat GravityInLean.roundG_mul_roundGinv
  GravityInLean.roundOrbit_isFreeFall_iff GravityInLean.roundOrbit_keepsOwnTime_iff
  GravityInLean.roundOrbit_clockRate_of_freeFall GravityInLean.roundOrbit_freeFall_exists

-- Step 2: a round space-time that may change in time, and Birkhoff's theorem
#audit GravityInLean.TwiceSmooth.swap GravityInLean.const_of_hasDerivAt_zero
  GravityInLean.christoffel_changing GravityInLean.changing_ricciFlat_iff
  GravityInLean.changingG_mul_changingGinv GravityInLean.changingG_static
  GravityInLean.static_unique GravityInLean.birkhoff GravityInLean.birkhoff_nothingChanges
  GravityInLean.birkhoff_resetClocks GravityInLean.birkhoff_mass_unique
  GravityInLean.schwarzschild_setting
  GravityInLean.schwarzschild_isEmptyOn GravityInLean.relabelled_isEmptyOn

-- Step 2, from symmetry: the general round shape, and Birkhoff's theorem without a starting shape
#audit GravityInLean.christoffel_gen GravityInLean.genG_mul_genGinv GravityInLean.genG_diagonal
  GravityInLean.gen_ricciFlat_iff GravityInLean.sizeEquations GravityInLean.exists_potential
  GravityInLean.massFn_const GravityInLean.usable_somewhere GravityInLean.massFn_schwarzschild
  GravityInLean.newTime_closed GravityInLean.relabel_path
  GravityInLean.birkhoff_general GravityInLean.rotX_turns GravityInLean.rotY_turns
  GravityInLean.rotZ_turns GravityInLean.shape_of_round GravityInLean.genG_isRound
  GravityInLean.birkhoff_of_round GravityInLean.roundEmpty_genG
  GravityInLean.eddington_isEmptyOn GravityInLean.eddington_mass
  GravityInLean.eddington_roundEmpty GravityInLean.eddington_outside
  GravityInLean.eddington_inside

-- The curvature formula does not depend on the coordinates
#audit GravityInLean.slope_comp GravityInLean.slope_slope_comm
  GravityInLean.christoffel_inNewCoords_at GravityInLean.riemann_inNewCoords
  GravityInLean.contDiffAt_of_inverse GravityInLean.ricci_inNewCoords
  GravityInLean.isRicciFlatAt_inNewCoords GravityInLean.inverse_inNewCoords
  GravityInLean.isRicciFlatAt_changeOfCoords
  GravityInLean.schwarzschild_ricciFlat_inNewCoords GravityInLean.inNewCoords_toSchw
  GravityInLean.eddington_ricciFlat_from_schwarzschild GravityInLean.stepLength_inNewCoords
  GravityInLean.birkhoff_general_inNewCoords

-- Free fall and "unchanged by a turn" do not depend on the coordinates either
#audit GravityInLean.hasDerivAt_along_path GravityInLean.freeFallExpr_inNewCoords
  GravityInLean.isFreeFallAt_inNewCoords GravityInLean.keepsOwnTimeAt_inNewCoords
  GravityInLean.eddington_orbit_freeFall GravityInLean.lieD_inNewCoords
  GravityInLean.leavesUnchangedAt_inNewCoords GravityInLean.schwarzschild_isRound
  GravityInLean.eddington_isRound_from_schwarzschild

-- Curved spaces: the definitions with no coordinates, tested on known answers
#audit GravityInLean.Curved.HasOneTimeDirection.not_orthogonal
  GravityInLean.Curved.isCovariantDerivativeOn_flatTransport
  GravityInLean.Curved.curvatureOfFields_flat
  GravityInLean.Curved.curvatureOfFields_flat_eq_curvatureAt
  GravityInLean.Curved.leavesUnchangedAt_flat_iff GravityInLean.Curved.isSmoothOn_flat_iff
  GravityInLean.Curved.isConnectionOf_table GravityInLean.Curved.ricciAt_table
  GravityInLean.Curved.leavesUnchangedAt_table_iff GravityInLean.Curved.mlieBracket_fieldOf
  GravityInLean.Curved.IsRegularTableOn.isEmptyOn
  GravityInLean.Curved.flat_isSpaceTimeOn GravityInLean.Curved.flat_isEmptyOn
  GravityInLean.Curved.sphere_noTime GravityInLean.Curved.sphere_curvature
  GravityInLean.Curved.deSitter_isSpaceTimeOn GravityInLean.Curved.deSitter_curvature
  GravityInLean.Curved.schwarzschild_isSpaceTimeOn_outside
  GravityInLean.Curved.schwarzschild_isSpaceTimeOn_inside
  GravityInLean.Curved.schwarzschild_isEmptyOn GravityInLean.Curved.schwarzschild_isRoundOn
  GravityInLean.Curved.schwarzschild_sizeSq GravityInLean.Curved.schwarzschild_usable
  GravityInLean.Curved.schwarzschild_meets_goal GravityInLean.Curved.schwarzschild_meets_conclusion
  GravityInLean.Curved.IsConnectionOf.koszul GravityInLean.Curved.IsConnectionOf.unique
  GravityInLean.Curved.connectionUnique GravityInLean.Curved.ricciAt_eq_of_isConnectionOf
  GravityInLean.Curved.IsRegularTableOn.isEmptyOn_iff GravityInLean.Curved.deSitter_not_isEmptyOn

-- Statements to prove (not proofs of them), and the checks that they are not about nothing
#audit GravityInLean.Curved.BirkhoffNoCoordinates GravityInLean.SmoothFlowStatement
  GravityInLean.TurnsCoordinatesStatement GravityInLean.Curved.ConnectionExistsStatement
  GravityInLean.Curved.ConnectionUniqueStatement GravityInLean.smoothFlow_const
  GravityInLean.schwarzschild_turnsOn GravityInLean.turnsCoordinates_schwarzschild

-- Proved by a team of workers (the first fleet trial): paths along a field depend smoothly on
-- where they start. The first line checks that what was proved is the statement as it was fixed
-- beforehand in `Goals/Turns.lean`, and not a statement of the team's own.
example : GravityInLean.SmoothFlowStatement := GravityInLean.smoothFlow

#audit GravityInLean.smoothFlow GravityInLean.Flows.exists_smooth_paths
  GravityInLean.Flows.exists_local_flow GravityInLean.Flows.exists_rescaled_path
  GravityInLean.Flows.exists_implicit_smooth GravityInLean.Flows.exists_primL
  GravityInLean.Flows.exists_appL

-- Proved by the second team of workers: coordinates that fit the turns exist. Again the first
-- line checks that what was proved is the statement as it was fixed in `Goals/Turns.lean`.
example : GravityInLean.TurnsCoordinatesStatement := GravityInLean.turnsCoordinates

#audit GravityInLean.turnsCoordinates GravityInLean.Turns.exists_unit_kernel
  GravityInLean.Turns.exists_rotation_row GravityInLean.Turns.likeTurns_rotate
  GravityInLean.Turns.linear_ode_unique GravityInLean.Turns.fderiv_flow_pair
  GravityInLean.Turns.exists_restSurface GravityInLean.Turns.contDiffOn_chart
  GravityInLean.Turns.chart_relations GravityInLean.Turns.turns_of_relations

-- Proved by the third team of workers: Birkhoff's theorem with no coordinates at all, the goal
-- that was fixed in `Curved/Goal.lean` before any of the teams started. The first line checks
-- that what was proved is that statement.
example : GravityInLean.Curved.BirkhoffNoCoordinates := GravityInLean.birkhoffNoCoordinates

#audit GravityInLean.birkhoffNoCoordinates GravityInLean.Join.resultA GravityInLean.Join.resultB
  GravityInLean.Join.isEmptyOn_carry_of GravityInLean.Join.ricciAt_carry
  GravityInLean.Join.isRicciFlatAt_of_isEmptyOn GravityInLean.Join.shape_of_round_box
  GravityInLean.Join.birkhoff_patch GravityInLean.Join.birkhoff_general_smooth
  GravityInLean.Join.exists_chart_of_localDiffeo

-- Proved by the fourth team of workers: Birkhoff's theorem both ways. Each first line checks
-- that what was proved is the statement as it was fixed in `Goals/ExactlyWhen.lean`.
example : GravityInLean.Curved.SchwarzschildExactlyWhen := GravityInLean.schwarzschildExactlyWhen
example : GravityInLean.Curved.SchwarzschildIsEmptyStatement := GravityInLean.schwarzschildIsEmpty
example : GravityInLean.BirkhoffExactlyWhenInCoordinates :=
  GravityInLean.birkhoffExactlyWhenInCoordinates
example : GravityInLean.ExactlyWhenAssumptionsMet := GravityInLean.exactlyWhenAssumptionsMet
example : GravityInLean.ExactlyWhenAssumptionsMetInside :=
  GravityInLean.exactlyWhenAssumptionsMetInside
example : GravityInLean.ExactlyWhenNotAlwaysEmpty := GravityInLean.exactlyWhenNotAlwaysEmpty

#audit GravityInLean.schwarzschildExactlyWhen GravityInLean.schwarzschildIsEmpty
  GravityInLean.birkhoffExactlyWhenInCoordinates GravityInLean.exactlyWhenAssumptionsMet
  GravityInLean.exactlyWhenAssumptionsMetInside GravityInLean.exactlyWhenNotAlwaysEmpty

-- Proved by the fifth team of workers. First, the tests that three independent reviewers of the
-- definitions asked for (`Goals/Tests.lean`): most of them cases where a definition must fail.
-- Each line checks that what was proved is the test as it was fixed.
example : GravityInLean.Curved.Tests.EfIsSpaceTimeOn := GravityInLean.Curved.Tests.efIsSpaceTimeOn
example : GravityInLean.Curved.Tests.EfIsEmptyOn := GravityInLean.Curved.Tests.efIsEmptyOn
example : GravityInLean.Curved.Tests.EfIsRoundOn := GravityInLean.Curved.Tests.efIsRoundOn
example : GravityInLean.Curved.Tests.EfNotUsableOnRim := GravityInLean.Curved.Tests.efNotUsableOnRim
example : GravityInLean.Curved.Tests.CylIsRoundOn := GravityInLean.Curved.Tests.cylIsRoundOn
example : GravityInLean.Curved.Tests.CylNotUsable := GravityInLean.Curved.Tests.cylNotUsable
example : GravityInLean.Curved.Tests.CylNotEmpty := GravityInLean.Curved.Tests.cylNotEmpty
example : GravityInLean.Curved.Tests.ZeroNotRound := GravityInLean.Curved.Tests.zeroNotRound
example : GravityInLean.Curved.Tests.ZeroMeetsOtherClauses :=
  GravityInLean.Curved.Tests.zeroMeetsOtherClauses
example : GravityInLean.Curved.Tests.SchwFlippedNotSpaceTime :=
  GravityInLean.Curved.Tests.schwFlippedNotSpaceTime
example : GravityInLean.Curved.Tests.SchwFlippedNotRound :=
  GravityInLean.Curved.Tests.schwFlippedNotRound
example : GravityInLean.Curved.Tests.SchwFlippedIsEmpty :=
  GravityInLean.Curved.Tests.schwFlippedIsEmpty
example : GravityInLean.Curved.Tests.TwoTimeNotSpaceTime :=
  GravityInLean.Curved.Tests.twoTimeNotSpaceTime
example : GravityInLean.Curved.Tests.FlatDegNotOneTime :=
  GravityInLean.Curved.Tests.flatDegNotOneTime
example : GravityInLean.Curved.Tests.SquashNotUnchanged :=
  GravityInLean.Curved.Tests.squashNotUnchanged
example : GravityInLean.Curved.Tests.SquashUnchangedAxis :=
  GravityInLean.Curved.Tests.squashUnchangedAxis
example : GravityInLean.Curved.Tests.SquashNotRound := GravityInLean.Curved.Tests.squashNotRound
example : GravityInLean.Curved.Tests.DeSitterIsRoundOn :=
  GravityInLean.Curved.Tests.deSitterIsRoundOn
example : GravityInLean.Curved.Tests.DeSitterUsable := GravityInLean.Curved.Tests.deSitterUsable
example : GravityInLean.Curved.Tests.DeSitterNotSchwarzschild :=
  GravityInLean.Curved.Tests.deSitterNotSchwarzschild
example : GravityInLean.Curved.Tests.MinkowskiIsRoundOn :=
  GravityInLean.Curved.Tests.minkowskiIsRoundOn
example : GravityInLean.Curved.Tests.MinkowskiUsable := GravityInLean.Curved.Tests.minkowskiUsable
example : GravityInLean.Curved.Tests.KinkNotUnchanged := GravityInLean.Curved.Tests.kinkNotUnchanged
example : GravityInLean.Curved.Tests.KinkNotSmooth := GravityInLean.Curved.Tests.kinkNotSmooth
example : GravityInLean.Curved.Tests.IsEmptyOnNegIff.{0, 0, 0} :=
  GravityInLean.Curved.Tests.isEmptyOnNegIff

-- One mass for a whole region, and: a length measure has a connection (proved from the textbook).
example : GravityInLean.Curved.OneMassStatement := GravityInLean.oneMass
example : GravityInLean.Curved.ConnectionExistsStatement := GravityInLean.connectionExists

#audit GravityInLean.oneMass GravityInLean.connectionExists
  GravityInLean.Curved.Tests.efNotUsableOnRim GravityInLean.Curved.Tests.zeroNotRound
  GravityInLean.Curved.Tests.deSitterNotSchwarzschild GravityInLean.Curved.Tests.minkowskiIsRoundOn
  GravityInLean.Curved.Tests.isEmptyOnNegIff

-- Proved by the sixth team of workers: Birkhoff's theorem at every point, the rim included, and
-- the known answers for Kruskal's table (`Goals/EveryPoint.lean`). Each line checks that what
-- was proved is the statement as it was fixed.
example : GravityInLean.Curved.KruskalRadiusSpec := GravityInLean.Curved.kruskalRadiusSpec
example : GravityInLean.Curved.KruskalRadiusSmooth := GravityInLean.Curved.kruskalRadiusSmooth
example : GravityInLean.Curved.KruskalIsSpaceTime := GravityInLean.Curved.kruskalIsSpaceTime
example : GravityInLean.Curved.KruskalIsEmpty := GravityInLean.Curved.kruskalIsEmpty
example : GravityInLean.Curved.KruskalIsRound := GravityInLean.Curved.kruskalIsRound
example : GravityInLean.Curved.KruskalNotUsableOnRim := GravityInLean.Curved.kruskalNotUsableOnRim
example : GravityInLean.Curved.KruskalMeetsConclusion := GravityInLean.Curved.kruskalMeetsConclusion
example : GravityInLean.Curved.DeSitterNotKruskal := GravityInLean.Curved.deSitterNotKruskal
example : GravityInLean.Curved.KruskalHoldsSchwarzschild :=
  GravityInLean.Curved.kruskalHoldsSchwarzschild
example : GravityInLean.Curved.BirkhoffAtEveryPoint := GravityInLean.Curved.birkhoffAtEveryPoint
example : GravityInLean.Curved.BirkhoffAtEveryPointOneMass :=
  GravityInLean.Curved.birkhoffAtEveryPointOneMass

#audit GravityInLean.Curved.birkhoffAtEveryPoint GravityInLean.Curved.birkhoffAtEveryPointOneMass
  GravityInLean.Curved.kruskalIsEmpty GravityInLean.Curved.kruskalNotUsableOnRim
  GravityInLean.Curved.kruskalHoldsSchwarzschild GravityInLean.Curved.kruskalRadiusSmooth

/-! ## Everything else, without exception -/

#audit_namespace GravityInLean
