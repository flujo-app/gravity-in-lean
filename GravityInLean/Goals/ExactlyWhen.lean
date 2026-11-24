/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Curved.Goal
public import GravityInLean.BirkhoffFromSymmetry

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Statements to prove: Birkhoff's theorem as one "exactly when"

**Nothing in this file is a proof of the statements it names.** It fixes, in exact form, what has
to be proved to turn Birkhoff's theorem into a statement that runs both ways (issue 41). The
statements are definitions of type `Prop`. A proof of one of them is a theorem of that type,
written in another file.

**Rule for anyone proving these: this file is not to be changed.** A statement that is too hard,
or false, is reported, not weakened.

So far the project has the two directions as separate theorems: "empty and round, so
Schwarzschild's" (`birkhoff_of_round`, `birkhoffNoCoordinates`) and "Schwarzschild's is empty"
(`schwarzschild_ricciFlat`, `schwarzschild_ricciFlat_inNewCoords`,
`Curved.schwarzschild_isEmptyOn`, all three outside the rim only). Six statements:

* `Curved.SchwarzschildIsEmptyStatement`: with no coordinates. A length measure that is
  Schwarzschild's in some chart around a point is empty near that point, outside the rim and
  inside it. No symmetry is assumed.
* `Curved.SchwarzschildExactlyWhen`: with no coordinates, both ways. Around a point, a length
  measure is a round, empty space-time whose spheres give a usable distance **exactly when** it
  is Schwarzschild's in some chart.
* `BirkhoffExactlyWhenInCoordinates`: in coordinates, both ways. A round table whose spheres
  give a usable distance is empty **exactly when** it is Schwarzschild's after new labels for
  time and distance.
* `ExactlyWhenAssumptionsMet`, `ExactlyWhenAssumptionsMetInside`: the assumptions of the
  statement in coordinates can be met, by Schwarzschild's own table outside the rim and inside
  it. (For the statements with no coordinates the same is already proved:
  `Curved.schwarzschild_meets_goal`, `Curved.schwarzschild_meets_conclusion`.)
* `ExactlyWhenNotAlwaysEmpty`: "empty" can fail under the same assumptions. De Sitter's table
  meets them and is not empty, so the statement in coordinates does not hold for a silly reason.

A mass may be any real number in all of this: zero gives flat space-time, and negative masses
are not ruled out. Asking for a positive mass would make the statements false.

One thing is proved here, because it costs nothing: `Curved.birkhoffNoCoordinates_iff` shows
that the new word `IsSchwarzschildNear` is exactly the conclusion of the goal that is already
proved.
-/

@[expose] public section

namespace GravityInLean

open Real Set

open scoped Manifold ContDiff

namespace Curved

/-- **Schwarzschild's in a chart around the point `p`.** There are a mass `m` (any real number:
zero and negative masses are allowed) and a chart `φ` of the curved space, around `p`, that
lands off the rim, off the centre and off the poles, in which
`g` is Schwarzschild's length measure for the mass `m`: the length of any two steps at a point
`q`, measured with `g`, is what Schwarzschild's table gives at the point `φ q` for the two steps
as the chart sees them. This is, word for word, the conclusion of `BirkhoffNoCoordinates`. -/
def IsSchwarzschildNear {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M] (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (p : M) : Prop :=
  ∃ (m : ℝ) (φ : OpenPartialHomeomorph M (Coords 4)),
    φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M ∧ p ∈ φ.source ∧
    ∀ q ∈ φ.source, (φ q ∈ outside m ∨ φ q ∈ inside m) ∧
      ∀ v w : TangentSpace 𝓘(ℝ, Coords 4) q,
        g q v w = flatMeasure (tableMeasure (roundG (schwA m) (schwB m))) (φ q)
          (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q v)
          (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q w)

/-- **The new word says what the proved goal concludes.** `BirkhoffNoCoordinates` is the
statement "round, empty, usable distance at `p`, so `IsSchwarzschildNear g p`", with nothing
added and nothing left out. -/
theorem birkhoffNoCoordinates_iff :
    BirkhoffNoCoordinates ↔
      ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
        [IsManifold 𝓘(ℝ, Coords 4) ∞ M]
        (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M) (s : Set M),
        IsOpen s → IsSpaceTimeOn g s → IsEmptyOn g s → IsRoundOn g ξ s →
        ∀ p ∈ s, UsableDistanceAt g ξ p → IsSchwarzschildNear g p :=
  Iff.rfl

/-- **Statement: Schwarzschild's in a chart is empty.** If a length measure on a curved space is
Schwarzschild's in some chart around `p`, outside the rim or inside it, then it is empty on an
open region around `p`. No symmetry is assumed, and none is needed. -/
def SchwarzschildIsEmptyStatement : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M]
    (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (p : M), IsSchwarzschildNear g p →
    ∃ u : Set M, IsOpen u ∧ p ∈ u ∧ IsEmptyOn g u

/-- **Statement: Birkhoff's theorem, both ways, with no coordinates.** Around a point `p` of a
curved space with four dimensions, the following say the same about a length measure `g`:

* there are an open region around `p` and three fields of arrows such that, on the region, `g`
  is a space-time, empty, and looks the same from every side by these fields, and at `p` the
  size of the spheres is a usable distance;
* `g` is Schwarzschild's in some chart around `p`.

From the first to the second is the proved theorem `birkhoffNoCoordinates`. From the second to
the first, the region and the three fields have to be built from the chart. -/
def SchwarzschildExactlyWhen : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M]
    (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (p : M),
    (∃ (s : Set M) (ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M),
        IsOpen s ∧ p ∈ s ∧ IsSpaceTimeOn g s ∧ IsEmptyOn g s ∧ IsRoundOn g ξ s ∧
          UsableDistanceAt g ξ p) ↔
      IsSchwarzschildNear g p

end Curved

/-- **A round table, with "empty" left out.** What `RoundEmpty` asks of a table of functions `g`
with inverse `ginv` on the region of times in `J`, distance labels in `I` and all angles off the
poles, except that space is empty; and with every entry smooth of every order. -/
structure RoundSetting (g ginv : Fin 4 → Fin 4 → Coords 4 → ℝ) (J I : Set ℝ) : Prop where
  /-- The stretch of times is open. -/
  openJ : IsOpen J
  /-- The stretch of times is in one piece. -/
  onePieceJ : IsPreconnected J
  /-- The stretch of distance labels is open. -/
  openI : IsOpen I
  /-- The stretch of distance labels is in one piece. -/
  onePieceI : IsPreconnected I
  /-- Every entry is smooth of every order. -/
  smooth : ∀ x, InRegion J I x → ∀ i j, ContDiffAt ℝ ∞ (g i j) x
  /-- The table is symmetric, as every length measure is. -/
  symm : ∀ x, InRegion J I x → ∀ i j, g i j x = g j i x
  /-- It looks the same from every side. -/
  round : ∀ x, InRegion J I x → IsRoundAt g x
  /-- It is of the space-time kind: the spheres have a positive size, and the rest has one time
  direction and one space direction. -/
  spaceTime : ∀ x, InRegion J I x → 0 < g 2 2 x ∧ g 0 0 x * g 1 1 x - g 0 1 x * g 0 1 x < 0
  /-- `ginv` is the inverse of `g`. -/
  inverse : ∀ x, InRegion J I x → ∀ i k, ∑ j, g i j x * ginv j k x = if i = k then 1 else 0

/-- **Schwarzschild's after new labels for time and distance.** There are a mass `M` and a new
time label `T`, smooth of every order, such that with `T` for time and "radius of the sphere"
for distance:

* the radius is smooth of every order as well;
* the table of slopes of the two new labels can be inverted at every point of the region;
* the radius is nowhere `2 M` (the region stays off the rim);
* the length of every step equals Schwarzschild's length of the same step.

The mass `M` may be zero or negative. This is what `birkhoff_of_round` concludes, with both
new labels smooth and the rim named. -/
def IsSchwarzschildRelabelled (g : Fin 4 → Fin 4 → Coords 4 → ℝ) (J I : Set ℝ) : Prop :=
  ∃ (M : ℝ) (T : ℝ → ℝ → ℝ), ContDiffOn ℝ ∞ (Function.uncurry T) (J ×ˢ I) ∧
    ContDiffOn ℝ ∞ (Function.uncurry (radius (sizeOf g))) (J ×ˢ I) ∧
    ∀ x, InRegion J I x →
      dt T (x 0) (x 1) * dr (radius (sizeOf g)) (x 0) (x 1)
        - dr T (x 0) (x 1) * dt (radius (sizeOf g)) (x 0) (x 1) ≠ 0 ∧
      radius (sizeOf g) (x 0) (x 1) ≠ 2 * M ∧
      ∀ v : Coords 4, stepLength g x v
        = stepLength (roundG (schwA M) (schwB M)) (relabel T (radius (sizeOf g)) x)
            (relabelStep T (radius (sizeOf g)) x v)

/-- **Statement: Birkhoff's theorem, both ways, in coordinates.** Take a round table
(`RoundSetting`) on a region where the size of the spheres is a usable distance. Then space is
empty on the region **exactly when** the table is Schwarzschild's after new labels for time and
distance. -/
def BirkhoffExactlyWhenInCoordinates : Prop :=
  ∀ (g ginv : Fin 4 → Fin 4 → Coords 4 → ℝ) (J I : Set ℝ), RoundSetting g ginv J I →
    (∀ x, InRegion J I x → sizeSlopeOf g x ≠ 0) →
    ((∀ x, InRegion J I x → IsRicciFlatAt g ginv x) ↔ IsSchwarzschildRelabelled g J I)

/-- **Statement: the assumptions of the statement in coordinates can be met.** Schwarzschild's
own table for a positive mass, at all times and outside the rim, is a round table, and the size
of its spheres is a usable distance there. -/
def ExactlyWhenAssumptionsMet : Prop :=
  ∀ M : ℝ, 0 < M →
    RoundSetting (roundG (schwA M) (schwB M)) (roundGinv (schwA M) (schwB M)) univ (Ioi (2 * M)) ∧
      ∀ x, InRegion univ (Ioi (2 * M)) x → sizeSlopeOf (roundG (schwA M) (schwB M)) x ≠ 0

/-- **Statement: the same inside the rim.** Schwarzschild's own table for a positive mass, at
all times and for distance labels between the centre and the rim, is a round table too, and the
size of its spheres is a usable distance there. (Inside the rim the distance label is the time.) -/
def ExactlyWhenAssumptionsMetInside : Prop :=
  ∀ M : ℝ, 0 < M →
    RoundSetting (roundG (schwA M) (schwB M)) (roundGinv (schwA M) (schwB M)) univ
        (Ioo 0 (2 * M)) ∧
      ∀ x, InRegion univ (Ioo 0 (2 * M)) x → sizeSlopeOf (roundG (schwA M) (schwB M)) x ≠ 0

/-- **Statement: "empty" can fail.** De Sitter's table (an empty universe with a cosmological
constant, radius `L`) is a round table inside its horizon, and the size of its spheres is a
usable distance there, but space is not empty in the sense used here. So the "exactly when" in
coordinates is not true for the silly reason that its left side always holds. -/
def ExactlyWhenNotAlwaysEmpty : Prop :=
  ∀ L : ℝ, 0 < L →
    RoundSetting (roundG (dsA L) (dsB L)) (roundGinv (dsA L) (dsB L)) univ (Ioo 0 L) ∧
      (∀ x, InRegion univ (Ioo 0 L) x → sizeSlopeOf (roundG (dsA L) (dsB L)) x ≠ 0) ∧
      ¬ ∀ x, InRegion univ (Ioo 0 L) x →
        IsRicciFlatAt (roundG (dsA L) (dsB L)) (roundGinv (dsA L) (dsB L)) x

end GravityInLean
