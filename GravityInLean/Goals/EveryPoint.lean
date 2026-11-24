/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.OneMass

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Statements to prove: Birkhoff's theorem at every point, the rim included

**Nothing in this file is a proof of the statements it names.**

`birkhoffNoCoordinates` speaks only about points where the size of the spheres is a usable
distance. The rim of a black hole is left out, because Schwarzschild's own coordinates are no
good there. This file states the theorem at **every** point (issue 39, first step).

For that it needs a form of Schwarzschild's space-time that is good on the rim. Eddington's
form is good on the rim but not at the places where the rims of the black hole and of its
mirror image cross. Kruskal's form is good everywhere away from the centre. So Kruskal's it is:

* two labels `T` and `X` in place of time and distance, with `X² - T² > -1`;
* the radius `r` is the positive number with `(r / 2m - 1) · exp (r / 2m) = X² - T²`
  (`kruskalF`, `kruskalR`); on the rim `X² = T²` and `r = 2m`;
* the length measure is `(32 m³ / r) · exp (-r / 2m) · (-dT² + dX²)` plus `r²` times the
  length measure of the unit sphere (`kruskalG`).

Statements, in the order in which they build on each other:

* `KruskalRadiusSpec`: the radius is well defined: for a positive mass and `X² - T² > -1` there
  is exactly the one positive `r`, and `kruskalR` is it.
* `KruskalIsSpaceTime`, `KruskalIsEmpty`, `KruskalIsRound`: known answers. Kruskal's table, for a
  positive mass, is a space-time, is empty, and looks the same from every side, on all of its
  region, the rim included.
* `KruskalHoldsSchwarzschild`: Schwarzschild's space-time, outside the rim and inside it, is a
  piece of Kruskal's: around each of its points there is a chart into Kruskal's.
* `BirkhoffAtEveryPoint`: the theorem. Around **every** point of a round, empty space-time there
  is a chart in which it is Kruskal's for a positive mass, or Schwarzschild's for a mass that is
  zero or negative (where there is no rim). "Usable distance" is not assumed.
* `BirkhoffAtEveryPointOneMass`: the same with one mass for a whole region in one piece.

**Rule for anyone proving these: this file is not to be changed.** A statement that is too hard,
or false, is reported, not weakened.
-/

@[expose] public section

namespace GravityInLean

open Real Set

open scoped Manifold ContDiff

namespace Curved

/-- The function that ties the radius to Kruskal's two labels: `(r / 2m - 1) · exp (r / 2m)`.
For a positive mass it grows with `r`, from `-1` at the centre through `0` at the rim. -/
noncomputable def kruskalF (m r : ℝ) : ℝ := (r / (2 * m) - 1) * Real.exp (r / (2 * m))

/-- The radius that belongs to the number `u = X² - T²` in Kruskal's form: the positive `r` with
`kruskalF m r = u`. (Written as the smallest such `r`; `KruskalRadiusSpec` says there is exactly
one when the mass is positive and `u > -1`. Outside that range the value means nothing.) -/
noncomputable def kruskalR (m u : ℝ) : ℝ := sInf {r : ℝ | 0 < r ∧ kruskalF m r = u}

/-- The factor in front of `-dT² + dX²` in Kruskal's form: `(32 m³ / r) · exp (-r / 2m)`. -/
noncomputable def kruskalA (m T X : ℝ) : ℝ :=
  32 * m ^ 3 / kruskalR m (X ^ 2 - T ^ 2) * Real.exp (-(kruskalR m (X ^ 2 - T ^ 2)) / (2 * m))

/-- The size of the spheres in Kruskal's form: `r²`. -/
noncomputable def kruskalS (m T X : ℝ) : ℝ := kruskalR m (X ^ 2 - T ^ 2) ^ 2

/-- **Kruskal's table** for the mass `m`: `-A dT² + A dX² + r² (dθ² + sin² θ dφ²)` with
`A = kruskalA m` and `r = kruskalR m (X² - T²)`. The four coordinates are `T`, `X` and the two
angles. -/
noncomputable def kruskalG (m : ℝ) : Fin 4 → Fin 4 → Coords 4 → ℝ :=
  genG (kruskalA m) (kruskalA m) zero2 (kruskalS m)

/-- Where Kruskal's table lives: away from the centre (`X² - T² > -1`) and off the poles. The
rim, `X² = T²`, is inside. -/
def kruskalRegion : Set (Coords 4) := {x | -1 < x 1 ^ 2 - x 0 ^ 2 ∧ sin (x 2) ≠ 0}

/-- **Kruskal's of mass `m` in a chart around the point `p`.** There is a chart of the curved
space, around `p`, that lands in Kruskal's region, in which `g` is Kruskal's length measure for
the mass `m`. -/
def IsKruskalNear {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M] (m : ℝ) (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (p : M) :
    Prop :=
  ∃ φ : OpenPartialHomeomorph M (Coords 4),
    φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M ∧ p ∈ φ.source ∧
    ∀ q ∈ φ.source, φ q ∈ kruskalRegion ∧
      ∀ v w : TangentSpace 𝓘(ℝ, Coords 4) q,
        g q v w = flatMeasure (tableMeasure (kruskalG m)) (φ q)
          (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q v)
          (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q w)

/-! ## The radius is well defined -/

/-- **Statement: the radius is well defined.** For a positive mass and a number `u > -1` there
is exactly one positive `r` with `kruskalF m r = u`, and `kruskalR m u` is that `r`. -/
def KruskalRadiusSpec : Prop :=
  ∀ m : ℝ, 0 < m → ∀ u : ℝ, -1 < u →
    0 < kruskalR m u ∧ kruskalF m (kruskalR m u) = u ∧
      ∀ r : ℝ, 0 < r → kruskalF m r = u → r = kruskalR m u

/-! ## Known answers for Kruskal's table -/

/-- **Statement: Kruskal's is a space-time,** rim included. -/
def KruskalIsSpaceTime : Prop :=
  ∀ m : ℝ, 0 < m → IsSpaceTimeOn (flatMeasure (tableMeasure (kruskalG m))) kruskalRegion

/-- **Statement: Kruskal's is empty,** rim included. -/
def KruskalIsEmpty : Prop :=
  ∀ m : ℝ, 0 < m → IsEmptyOn (flatMeasure (tableMeasure (kruskalG m))) kruskalRegion

/-- **Statement: Kruskal's looks the same from every side,** rim included, by the three standard
turns. -/
def KruskalIsRound : Prop :=
  ∀ m : ℝ, 0 < m → IsRoundOn (flatMeasure (tableMeasure (kruskalG m))) turns kruskalRegion

/-- **Statement: Schwarzschild's is a piece of Kruskal's.** For a positive mass, around every
point outside the rim and around every point inside it, Schwarzschild's length measure is
Kruskal's in some chart. -/
def KruskalHoldsSchwarzschild : Prop :=
  ∀ m : ℝ, 0 < m → ∀ p : Coords 4, p ∈ outside m ∨ p ∈ inside m →
    IsKruskalNear m (flatMeasure (tableMeasure (roundG (schwA m) (schwB m)))) p

/-! ## The theorem at every point -/

/-- **Statement: Birkhoff's theorem at every point, the rim included.** Take a curved space of
four dimensions with a length measure that, on an open region, is a space-time, is empty, and
looks the same from every side. Then around **every** point `p` of the region, with nothing
asked of the size of the spheres there, one of two things holds:

* there is a positive mass `m` such that the length measure is Kruskal's of mass `m` in some
  chart around `p`; or
* there is a mass `m` that is zero or negative such that the length measure is Schwarzschild's
  of mass `m` in some chart around `p` (for such a mass there is no rim, and Schwarzschild's
  own form is good everywhere away from the centre). -/
def BirkhoffAtEveryPoint : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M]
    (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M) (s : Set M),
    IsOpen s → IsSpaceTimeOn g s → IsEmptyOn g s → IsRoundOn g ξ s →
    ∀ p ∈ s, (∃ m : ℝ, 0 < m ∧ IsKruskalNear m g p) ∨
      (∃ m : ℝ, m ≤ 0 ∧ IsSchwarzschildWith m g p)

/-- **Statement: the same, with one mass for a whole region.** If the region is in one piece,
the mass is the same at all of its points: either one positive mass, and Kruskal's of that mass
around every point; or one mass that is zero or negative, and Schwarzschild's of that mass
around every point. -/
def BirkhoffAtEveryPointOneMass : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M]
    (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M) (s : Set M),
    IsOpen s → IsPreconnected s → IsSpaceTimeOn g s → IsEmptyOn g s → IsRoundOn g ξ s →
    (∃ m : ℝ, 0 < m ∧ ∀ p ∈ s, IsKruskalNear m g p) ∨
      (∃ m : ℝ, m ≤ 0 ∧ ∀ p ∈ s, IsSchwarzschildWith m g p)

end Curved

end GravityInLean
