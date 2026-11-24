/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.ExactlyWhen

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Statement to prove: one mass for a whole region

**Nothing in this file is a proof of the statement it names.**

`birkhoffNoCoordinates` gives, around every point where the size of the spheres is a usable
distance, a mass and a chart. As it stands, the mass is chosen point by point: nothing says
that two points of the same space-time get the same mass. The reviewers of the definitions
asked for that (`REVIEW.md`).

`OneMassStatement`: on a region in one piece, one mass serves every point. The region may
contain points where the size of the spheres is not a usable distance (the rim of a black hole
is such a place); at those points no chart is promised, but the points on both sides of them
still get the same mass.

**Rule for anyone proving this: this file is not to be changed.** A statement that is too hard,
or false, is reported, not weakened.
-/

@[expose] public section

namespace GravityInLean

open Real Set

open scoped Manifold ContDiff

namespace Curved

/-- **Schwarzschild's of mass `m` in a chart around the point `p`.** The same as
`IsSchwarzschildNear`, with the mass named. -/
def IsSchwarzschildWith {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M] (m : ℝ) (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (p : M) :
    Prop :=
  ∃ φ : OpenPartialHomeomorph M (Coords 4),
    φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M ∧ p ∈ φ.source ∧
    ∀ q ∈ φ.source, (φ q ∈ outside m ∨ φ q ∈ inside m) ∧
      ∀ v w : TangentSpace 𝓘(ℝ, Coords 4) q,
        g q v w = flatMeasure (tableMeasure (roundG (schwA m) (schwB m))) (φ q)
          (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q v)
          (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q w)

/-- **The word with the mass named says the same as the word without.** -/
theorem isSchwarzschildNear_iff {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M] (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (p : M) :
    IsSchwarzschildNear g p ↔ ∃ m : ℝ, IsSchwarzschildWith m g p :=
  Iff.rfl

/-- **Statement: one mass for a whole region.** Take a curved space of four dimensions with a
length measure that, on an open region in one piece, is a space-time, is empty, and looks the
same from every side. Then there is one mass `m` such that around every point of the region
where the size of the spheres is a usable distance, the length measure is Schwarzschild's of
that mass `m` in some chart. -/
def OneMassStatement : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M]
    (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M) (s : Set M),
    IsOpen s → IsPreconnected s → IsSpaceTimeOn g s → IsEmptyOn g s → IsRoundOn g ξ s →
    ∃ m : ℝ, ∀ p ∈ s, UsableDistanceAt g ξ p → IsSchwarzschildWith m g p

end Curved

end GravityInLean
