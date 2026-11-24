/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.ExactlyWhen
public import GravityInLean.Eddington

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Statements to prove: tests that the definitions can fail

**Nothing in this file is a proof of the statements it names.** It fixes, in exact form, tests
of the definitions in `Curved/Basic.lean` and `Curved/Goal.lean`. The definitions were so far
tested on cases where they should hold. Almost all of these tests are cases where one of them
should **fail**, and say which one. A definition that cannot fail says nothing.

The tests were proposed by three independent reviewers of the definitions (`REVIEW.md`,
`review/lean-conventions.md`, section "Proposed failure tests"). They are copied here as
statements of type `Prop`, so that whoever proves them cannot quietly change them.

**Rule for anyone proving these: this file is not to be changed.** A test that turns out to be
false as written is reported with the reason. That is a finding about the definitions or about
the test, and both are worth knowing.

What each group is for:

1. `Ef…`: on the rim of a black hole, in coordinates that are good there (Eddington's), every
   assumption of Birkhoff's theorem holds except "usable distance". So that assumption is needed.
2. `Cyl…`: spheres of one fixed size (a flat plane times a sphere) look the same from every
   side, but their size is no distance at all, and space is not empty.
3. `Zero…`: three fields that are zero everywhere are not "the same from every side", although
   they pass every other clause of that definition.
4. `SchwFlipped…`: Schwarzschild's table with all signs turned round is empty, but it is not a
   space-time in the sense used here and not round.
5. `TwoTime…`, `FlatDeg…`: two time directions are not "one time direction", and neither is a
   length measure that gives one direction the length zero.
6. `Squash…`: a sphere squashed along one angle is not left unchanged by the turn through the
   equator, only by the turn around the axis.
7. `DeSitter…`: de Sitter's space-time meets every assumption except "empty".
8. `DeSitterNotSchwarzschild`: de Sitter's space-time is Schwarzschild's in no chart at all. The
   first test across a real change of charts.
9. `Minkowski…`: flat space-time with the turns written in ordinary `x`, `y`, `z` is round and
   has a usable distance, poles included. The first test not written in angles.
10. `KinkNotUnchanged`: a field with a kink does not "leave lengths unchanged" at the kink.
11. `KinkNotSmooth`: a length measure with a kink is not smooth.
12. `IsEmptyOnNegIff`: turning all signs of a length measure round does not change whether
    space is empty, on any curved space.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean

open Real Set VectorField

open scoped Manifold ContDiff

namespace Curved

namespace Tests

/-! ## 1. The rim fails "usable distance", and nothing else fails there -/

/-- Schwarzschild's space-time in Eddington's coordinates, which are good on the rim. -/
noncomputable abbrev efG (M : ℝ) : Fin 4 → Fin 4 → Coords 4 → ℝ :=
  genG (onlyR (schwA M)) zero2 one2 (onlyR sqF)

/-- Everywhere off the centre and off the poles; the rim is included. -/
def efRegion : Set (Coords 4) := {x | 0 < x 1 ∧ sin (x 2) ≠ 0}

/-- In Eddington's coordinates Schwarzschild's is a space-time, rim included. -/
def EfIsSpaceTimeOn : Prop :=
  ∀ M : ℝ, IsSpaceTimeOn (flatMeasure (tableMeasure (efG M))) efRegion

/-- ... and it is empty, rim included. -/
def EfIsEmptyOn : Prop :=
  ∀ M : ℝ, IsEmptyOn (flatMeasure (tableMeasure (efG M))) efRegion

/-- ... and it looks the same from every side, rim included. -/
def EfIsRoundOn : Prop :=
  ∀ M : ℝ, IsRoundOn (flatMeasure (tableMeasure (efG M))) turns efRegion

/-- ... but on the rim the size of the spheres is not a usable distance. -/
def EfNotUsableOnRim : Prop :=
  ∀ M : ℝ, 0 < M → ∀ x : Coords 4, x 1 = 2 * M → sin (x 2) ≠ 0 →
    ¬ UsableDistanceAt (flatMeasure (tableMeasure (efG M))) turns x

/-! ## 2. Spheres of one fixed size -/

/-- A flat plane of time and distance, times a sphere of size one. -/
noncomputable abbrev cylG : Fin 4 → Fin 4 → Coords 4 → ℝ :=
  genG (fun _ _ ↦ 1) (fun _ _ ↦ 1) zero2 (fun _ _ ↦ 1)

/-- It looks the same from every side. -/
def CylIsRoundOn : Prop :=
  IsRoundOn (flatMeasure (tableMeasure cylG)) turns {x : Coords 4 | sin (x 2) ≠ 0}

/-- The size of its spheres is nowhere a usable distance: it does not change at all. -/
def CylNotUsable : Prop :=
  ∀ x : Coords 4, sin (x 2) ≠ 0 → ¬ UsableDistanceAt (flatMeasure (tableMeasure cylG)) turns x

/-- It is not empty. -/
def CylNotEmpty : Prop :=
  ¬ IsEmptyOn (flatMeasure (tableMeasure cylG)) {x : Coords 4 | sin (x 2) ≠ 0}

/-! ## 3. Zero fields are not "round" -/

/-- Three fields that are zero everywhere do not make flat space-time "the same from every
side". -/
def ZeroNotRound : Prop :=
  ¬ IsRoundOn (flatMeasure (tableMeasure flatG)) (fun _ ↦ 0) (Set.univ : Set (Coords 4))

/-- ... although the zero field leaves lengths unchanged, and its bracket with itself is zero.
Only the clause "they span two directions" stops them. -/
def ZeroMeetsOtherClauses : Prop :=
  ∀ x : Coords 4, LeavesUnchangedAt (flatMeasure (tableMeasure flatG)) 0 x
    ∧ mlieBracket 𝓘(ℝ, Coords 4) (0 : Arrows 𝓘(ℝ, Coords 4) (Coords 4)) 0 x = 0

/-! ## 4. Schwarzschild's with all signs turned round -/

/-- With all signs turned round it is not a space-time in the sense used here (one time
direction, three of space). -/
def SchwFlippedNotSpaceTime : Prop :=
  ∀ M : ℝ,
    ¬ IsSpaceTimeOn (flatMeasure (-tableMeasure (roundG (schwA M) (schwB M)))) (outside M)

/-- ... and not round: lengths on the spheres are negative. -/
def SchwFlippedNotRound : Prop :=
  ∀ M : ℝ,
    ¬ IsRoundOn (flatMeasure (-tableMeasure (roundG (schwA M) (schwB M)))) turns (outside M)

/-- ... but it is still empty. -/
def SchwFlippedIsEmpty : Prop :=
  ∀ M : ℝ, IsEmptyOn (flatMeasure (-tableMeasure (roundG (schwA M) (schwB M)))) (outside M)

/-! ## 5. "Exactly one" time direction, and "strictly positive" -/

/-- A flat table with two time directions. -/
noncomputable def twoTimeG (a b : Fin 4) : Coords 4 → ℝ :=
  fun _ ↦ if a = b then (if a = 0 ∨ a = 1 then -1 else 1) else 0

/-- Two time directions are not one. -/
def TwoTimeNotSpaceTime : Prop :=
  ¬ IsSpaceTimeOn (flatMeasure (tableMeasure twoTimeG)) (Set.univ : Set (Coords 4))

/-- A flat table that gives one direction of space the length zero. -/
noncomputable def flatDegG (a b : Fin 4) : Coords 4 → ℝ :=
  fun _ ↦ if a = b then (if a = 0 then -1 else if a = 3 then 0 else 1) else 0

/-- A direction of length zero is not allowed next to the time direction. -/
def FlatDegNotOneTime : Prop :=
  ∀ x : Coords 4, ¬ HasOneTimeDirection fun v w : Coords 4 ↦ tableMeasure flatDegG x v w

/-! ## 6. A squashed sphere -/

/-- Schwarzschild's table with the sphere squashed: lengths around the axis count double. -/
noncomputable def squashG (M : ℝ) : Fin 4 → Fin 4 → Coords 4 → ℝ :=
  diag fun i x ↦ (if i = 3 then 2 else 1) * roundDiag (schwA M) (schwB M) i x

/-- The turn through the equator does not leave it unchanged. -/
def SquashNotUnchanged : Prop :=
  ∀ M : ℝ, ∀ x ∈ outside M, cos (x 3) ≠ 0 →
    ¬ LeavesUnchangedAt (flatMeasure (tableMeasure (squashG M))) (turns 1) x

/-- The turn around the axis does. -/
def SquashUnchangedAxis : Prop :=
  ∀ M : ℝ, ∀ x ∈ outside M,
    LeavesUnchangedAt (flatMeasure (tableMeasure (squashG M))) (turns 2) x

/-- So it is not "the same from every side" by the three standard turns. -/
def SquashNotRound : Prop :=
  ∀ M : ℝ, ¬ IsRoundOn (flatMeasure (tableMeasure (squashG M))) turns (outside M)

/-! ## 7. De Sitter's space-time meets every assumption except "empty" -/

/-- De Sitter's space-time looks the same from every side. -/
def DeSitterIsRoundOn : Prop :=
  ∀ L : ℝ, IsRoundOn (flatMeasure (tableMeasure (roundG (dsA L) (dsB L)))) turns
    (deSitterRegion L)

/-- The size of its spheres is a usable distance. -/
def DeSitterUsable : Prop :=
  ∀ L : ℝ, ∀ x ∈ deSitterRegion L,
    UsableDistanceAt (flatMeasure (tableMeasure (roundG (dsA L) (dsB L)))) turns x

/-! ## 8. A real change of charts: de Sitter's is Schwarzschild's in no chart -/

/-- There is no chart around any point in which de Sitter's length measure is Schwarzschild's,
for any mass. -/
def DeSitterNotSchwarzschild : Prop :=
  ∀ L : ℝ, 0 < L → ∀ p ∈ deSitterRegion L,
    ¬ IsSchwarzschildNear (flatMeasure (tableMeasure (roundG (dsA L) (dsB L)))) p

/-! ## 9. Flat space-time in ordinary `x`, `y`, `z`, poles included -/

/-- The turns about the `y`-, `x`- and `z`-axis, written on the coordinates `(t, x, y, z)`. -/
noncomputable def cartTurns : Fin 3 → Arrows 𝓘(ℝ, Coords 4) (Coords 4) :=
  ![fieldOf ![fun _ ↦ 0, fun p ↦ p 3, fun _ ↦ 0, fun p ↦ -p 1],
    fieldOf ![fun _ ↦ 0, fun _ ↦ 0, fun p ↦ -p 3, fun p ↦ p 2],
    fieldOf ![fun _ ↦ 0, fun p ↦ -p 2, fun p ↦ p 1, fun _ ↦ 0]]

/-- Everywhere except the line through the centre. -/
def awayFromCentre : Set (Coords 4) := {x | x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 ≠ 0}

/-- Flat space-time looks the same from every side by these turns, poles included. -/
def MinkowskiIsRoundOn : Prop :=
  IsRoundOn (flatMeasure (tableMeasure flatG)) cartTurns awayFromCentre

/-- The size of the spheres is a usable distance there. -/
def MinkowskiUsable : Prop :=
  ∀ x ∈ awayFromCentre, UsableDistanceAt (flatMeasure (tableMeasure flatG)) cartTurns x

/-! ## 10 and 11. Kinks -/

/-- A field with a kink does not "leave lengths unchanged" at the kink. -/
def KinkNotUnchanged : Prop :=
  ¬ LeavesUnchangedAt (flatMeasure (tableMeasure flatG))
    (fieldOf ![fun p ↦ |p 1|, fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0]) 0

/-- A flat table with a kink in its distance entries. -/
noncomputable def kinkG (a b : Fin 4) : Coords 4 → ℝ :=
  fun x ↦ if a = b then (if a = 0 then -1 else 1 + |x 1|) else 0

/-- A length measure with a kink is not smooth. -/
def KinkNotSmooth : Prop :=
  ¬ IsSmoothOn (flatMeasure (tableMeasure kinkG)) (Set.univ : Set (Coords 4))

/-! ## 12. Empty does not depend on which sign time gets -/

/-- Turning all signs of a length measure round does not change whether space is empty, on any
curved space. -/
def IsEmptyOnNegIff : Prop :=
  ∀ (E H : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : LengthMeasure I M) (s : Set M), IsEmptyOn (-g) s ↔ IsEmptyOn g s

end Tests

end Curved

end GravityInLean
