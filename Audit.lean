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

-- Probe: curvature from the general formulas, on a sphere
#audit GravityInLean.christoffel_sphere GravityInLean.sphereG_mul_sphereGinv
  GravityInLean.ricci_sphere

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
  GravityInLean.birkhoff_resetClocks GravityInLean.schwarzschild_setting
  GravityInLean.schwarzschild_isEmptyOn GravityInLean.relabelled_isEmptyOn

/-! ## Everything else, without exception -/

#audit_namespace GravityInLean
