/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.EveryPoint
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Statements to prove: Birkhoff's theorem for a whole space-time

**Nothing in this file is a proof of the statements it names.**

Every result so far speaks about the neighbourhood of one point: near each point where the
size of the spheres is a usable distance, a round, empty space-time is a piece of
Schwarzschild's (`birkhoffNoCoordinates`, proved); near every point, the rim included, it is a
piece of Kruskal's (`BirkhoffAtEveryPoint`, issue 39, first step, a statement still to prove).
This file says what follows for a whole space-time (issue 39, second step).

**In plain words.** Kruskal's space-time is the whole of Schwarzschild's: the outside of the
black hole, a second outside beyond it, the inside, and the inside of a white hole. Take a round,
empty space-time that is in one piece and has no holes that a loop could wind round (it is
*simply connected*: every loop in it can be pulled together to a point inside it). Then it can be
laid onto Kruskal's space-time (if its mass is positive), onto flat space-time (mass zero), or
onto Schwarzschild's space-time of negative mass, by a map that keeps every length. The map need
not be one-to-one: the space-time may cover parts of Kruskal's more than once. And the map is
unique up to a symmetry of the model space-time.

## The model space-times, whole

**Kruskal's space-time, whole** (`kruskalSpace`, `kruskalWhole`). The table of
`Goals/EveryPoint.lean` describes the spheres with two angles, so it leaves out the two poles of
every sphere. A statement about a whole space-time must not leave anything out. So here the
sphere is the unit sphere of ordinary space: a point of Kruskal's whole space-time is a list of
five numbers `(T, X, y₁, y₂, y₃)` with `X² - T² > -1` and `y₁² + y₂² + y₃² = 1`, and its length
measure is

  `A · (-dT² + dX²) + r² · (dy₁² + dy₂² + dy₃²)`,

with `A = kruskalA m T X` and `r = kruskalR m (X² - T²)` from the same table. For steps along the
sphere, `dy₁² + dy₂² + dy₃²` is the usual length measure of the unit sphere, poles included. The
check `kruskalWrap_isKruskalMapOn` (`Global/Checks.lean`) shows that wrapping the table of
`Goals/EveryPoint.lean` round the sphere gives exactly this.

The table `kruskalWhole` is a table on lists of five numbers; only its values on steps along
Kruskal's space-time matter. A map into Kruskal's space-time has all its steps there.

**Schwarzschild's space-time for a mass that is zero or negative, whole** (`schwSpaceG`,
`schwSpaceRegion`). Such a mass has no rim, and Schwarzschild's space-time can be written with
three ordinary space labels `(t, x₁, x₂, x₃)` in place of distance and angles:

  `-(1 - 2m/ρ) dt² + dx₁² + dx₂² + dx₃² + (2m / (ρ² (ρ - 2m))) · (x₁ dx₁ + x₂ dx₂ + x₃ dx₃)²`,

with `ρ` the distance from the centre. For mass zero this is flat space-time, centre included;
for a negative mass the centre is left out. The check `sphericalToSpace_isSchwarzschildMapOn`
shows that Schwarzschild's table of distance and angles is exactly this in new labels.

**A length-keeping map** (`IsKruskalMapOn`, `IsSchwarzschildMapOn`). A smooth map `D` from an
open region `s` of the curved space into the model space-time such that the length of any two
steps at a point of `s`, measured with `g`, is the model's length of the two steps as `D` carries
them. In the textbooks: `D` is a local isometry, `D* g_model = g`. Such a map carries no step
to zero (`IsKruskalMapOn.mfderiv_injective`), so it is one-to-one on small pieces, and near each
point it is a chart of the model space-time; on the whole region it need not be one-to-one.

## The statements

* `GlobalBirkhoff` (G1): every round, empty space-time on a simply connected region has a
  length-keeping map into Kruskal's (positive mass) or into Schwarzschild's whole space-time of
  mass zero or negative.
* `GlobalBirkhoffUnique`: two such maps on a region in one piece differ by a symmetry of the
  model: for Kruskal's, a change of `T` and `X` that keeps `-T² + X²` together with a turn or
  mirror of the sphere; for a negative mass, a shift of time, possibly turned round, together
  with a turn or mirror of space; for flat space-time, a Lorentz transformation and a shift.
* `GlobalBirkhoffConverse`: the other way. A space-time with such a map is round and empty
  (for mass zero: if the map misses the centre). So on a simply connected region, for a mass
  that is not zero, "round and empty" holds **exactly when** such a map exists.
* `GlobalMassUnique`: the mass is fixed by the space-time: maps into models of two different
  masses never both exist on the same region.

Checks, as statements for the team:

* `KruskalMapOfSchwarzschild`: known answer. Schwarzschild's table, outside the rim and inside
  it, maps into Kruskal's by the textbook formulas of Kruskal and Szekeres.
* `GlobalDeSitterNoMap`: the conclusion can fail. De Sitter's space-time on a simply connected
  region meets every assumption except "empty", and has no such map.
* `GlobalUniqueNeedsOnePiece`: `GlobalBirkhoffUnique` needs its region in one piece. On a
  region in two pieces, two maps can differ by a different symmetry on each piece.

Checks proved now, in `Global/Checks.lean`: the assumptions of `GlobalBirkhoff` can be met (by
Schwarzschild's table on a region in one piece without holes, for every mass; and, assuming the
known answers of `Goals/EveryPoint.lean`, by Kruskal's table on a region that contains the rim
and the place where the two rims cross); the conclusion holds for these with explicit maps; the
symmetries named in `GlobalBirkhoffUnique` really carry length-keeping maps to length-keeping
maps.

## Why each assumption is there

* **Simply connected.** Without it, the statement is false. Example (not checked in Lean): the
  outside of Schwarzschild's black hole with time wound into a circle (`t` and `t + c` the same
  point, for a fixed `c ≠ 0`) is round and empty. A length-keeping map into Kruskal's, unwound
  along the circle, would be a map on the unwound outside that does not change under the boost
  that shifts `t` by `c`. By `GlobalBirkhoffUnique` the map and the map after the boost differ
  by a symmetry of Kruskal's, which would then leave an open piece of Kruskal's unchanged point
  by point; only the trivial symmetry does that, and the boost is not trivial.
* **A space-time, empty, round:** as in `BirkhoffAtEveryPoint`, on the whole region.

## What is not claimed

* **One-to-one.** Kruskal's space-time with the sphere where the two rims cross removed,
  unwrapped so that it has no holes (its universal cover), is round, empty and simply connected;
  its map into Kruskal's covers points infinitely often. So the map cannot be asked to be
  one-to-one.
* **Which space-times are exactly Kruskal's** or Kruskal's folded in two (the RP³ geon and its
  three relatives). That needs a condition on paths of free fall (G2 of the research notes). It
  is not stated here: this project has no paths of free fall on a curved space yet.

**Earlier work.** In the research notes (`review/global-birkhoff.md`) G1 was not found written
down as a theorem; Hawking and Ellis, Chruściel, Schleich and Witt, and Chamblin and Gibbons treat
pieces of it. A referee may well see it as a short consequence of the local theorem at every
point and the classical extension theorem for maps that keep lengths (Kobayashi and Nomizu,
vol. I, VI.6.3; Chruściel's lecture notes, Theorem 1.4.4), which those sources state for
analytic space-times; experts may regard it as folklore. Here nothing is assumed analytic. Say
"not found written down", never "new" or "first".

**A stronger form, not stated here:** the map could also be asked to carry the three fields to
the three standard turns of the sphere. For mass zero that would make the map miss the centre,
and close the "exactly when" for mass zero too.

**Rule for anyone proving these: this file is not to be changed.** A statement that is too hard,
or false, is reported, not weakened.
-/

@[expose] public section

namespace GravityInLean

open Real Set

open scoped Manifold ContDiff

namespace Curved

/-! ## Kruskal's space-time, whole -/

/-- **Where Kruskal's whole space-time lies** among the lists of five numbers
`(T, X, y₁, y₂, y₃)`: away from the centre (`X² - T² > -1`), and with `y` on the unit sphere. -/
def kruskalSpace : Set (Coords 5) :=
  {p | -1 < p 1 ^ 2 - p 0 ^ 2 ∧ p 2 ^ 2 + p 3 ^ 2 + p 4 ^ 2 = 1}

/-- The five diagonal entries of Kruskal's whole table: `-A`, `A`, `r²`, `r²`, `r²`, with `A` and
`r²` taken from Kruskal's table of `Goals/EveryPoint.lean` at the labels `T = p 0`, `X = p 1`. -/
noncomputable def kruskalWholeDiag (m : ℝ) : Fin 5 → Coords 5 → ℝ :=
  ![fun p ↦ -kruskalA m (p 0) (p 1), fun p ↦ kruskalA m (p 0) (p 1),
    fun p ↦ kruskalS m (p 0) (p 1), fun p ↦ kruskalS m (p 0) (p 1),
    fun p ↦ kruskalS m (p 0) (p 1)]

/-- **Kruskal's whole table** for the mass `m`: `A · (-dT² + dX²) + r² · (dy₁² + dy₂² + dy₃²)`.
Only its values on steps along `kruskalSpace` matter. -/
noncomputable def kruskalWhole (m : ℝ) : Fin 5 → Fin 5 → Coords 5 → ℝ :=
  diag (kruskalWholeDiag m)

/-- **A length-keeping map from the region `s` into Kruskal's whole space-time of mass `m`.**
The region is open; `D` is smooth on it; `D` sends every point of it into Kruskal's space-time;
and the length of any two steps at a point `q` of the region, measured with `g`, is Kruskal's
length of the two steps as `D` carries them. (Textbooks: a local isometry into the Kruskal
space-time.) -/
def IsKruskalMapOn {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M] (m : ℝ) (g : LengthMeasure 𝓘(ℝ, Coords 4) M)
    (D : M → Coords 5) (s : Set M) : Prop :=
  IsOpen s ∧ ContMDiffOn 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 5) ∞ D s ∧
    ∀ q ∈ s, D q ∈ kruskalSpace ∧
      ∀ v w : TangentSpace 𝓘(ℝ, Coords 4) q,
        g q v w = flatMeasure (tableMeasure (kruskalWhole m)) (D q)
          (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 5) D q v)
          (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 5) D q w)

/-! ## Schwarzschild's space-time for a mass that is zero or negative, whole -/

/-- The distance from the centre of the point `(t, x₁, x₂, x₃)` of ordinary space and time. -/
noncomputable def centreDist (x : Coords 4) : ℝ := √(x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2)

/-- **Schwarzschild's table in ordinary space labels** `(t, x₁, x₂, x₃)`:
`-(1 - 2m/ρ) dt² + dx₁² + dx₂² + dx₃² + (2m / (ρ² (ρ - 2m))) · (x₁ dx₁ + x₂ dx₂ + x₃ dx₃)²`,
with `ρ = centreDist x`. Meant for a mass that is zero or negative; for mass zero it is flat
space-time, `-dt² + dx₁² + dx₂² + dx₃²`, at every point. -/
noncomputable def schwSpaceG (m : ℝ) (a b : Fin 4) (x : Coords 4) : ℝ :=
  if a = 0 ∧ b = 0 then -schwA m (centreDist x)
  else if a = 0 ∨ b = 0 then 0
  else (if a = b then 1 else 0)
    + 2 * m / (centreDist x ^ 2 * (centreDist x - 2 * m)) * x a * x b

/-- **Where it lives:** everywhere for mass zero (flat space-time), and away from the centre
otherwise. -/
def schwSpaceRegion (m : ℝ) : Set (Coords 4) :=
  {x | m = 0 ∨ 0 < x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2}

/-- **A length-keeping map from the region `s` into Schwarzschild's whole space-time of mass
`m`** (meant for `m ≤ 0`), written in ordinary space labels. The same as `IsKruskalMapOn`, with
`schwSpaceG` in place of Kruskal's table. -/
def IsSchwarzschildMapOn {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M] (m : ℝ) (g : LengthMeasure 𝓘(ℝ, Coords 4) M)
    (D : M → Coords 4) (s : Set M) : Prop :=
  IsOpen s ∧ ContMDiffOn 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) ∞ D s ∧
    ∀ q ∈ s, D q ∈ schwSpaceRegion m ∧
      ∀ v w : TangentSpace 𝓘(ℝ, Coords 4) q,
        g q v w = flatMeasure (tableMeasure (schwSpaceG m)) (D q)
          (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D q v)
          (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D q w)

/-! ## The symmetries of the model space-times -/

/-- The signs of `-T² + X²`. -/
def lightSign2 : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![-1, 1]

/-- The signs of `-t² + x₁² + x₂² + x₃²`. -/
def lightSign4 : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![-1, 1, 1, 1]

/-- **A symmetry of Kruskal's whole space-time:** the labels `(T, X)` are changed by the matrix
`L`, and the point `y` of the sphere by the matrix `R`. It is a symmetry when `L` keeps
`-T² + X²` (`Lᵀ · lightSign2 · L = lightSign2`: a boost, possibly with `T ↦ -T` or `X ↦ -X`) and
`R` is a turn or a mirror of ordinary space (`Rᵀ R = 1`). -/
noncomputable def kruskalSym (L : Matrix (Fin 2) (Fin 2) ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (p : Coords 5) : Coords 5 :=
  ![L 0 0 * p 0 + L 0 1 * p 1, L 1 0 * p 0 + L 1 1 * p 1,
    R 0 0 * p 2 + R 0 1 * p 3 + R 0 2 * p 4,
    R 1 0 * p 2 + R 1 1 * p 3 + R 1 2 * p 4,
    R 2 0 * p 2 + R 2 1 * p 3 + R 2 2 * p 4]

/-- **A symmetry of Schwarzschild's whole space-time of negative mass:** time `t` becomes
`ε t + c` with `ε = 1` or `ε = -1` (a shift of time, possibly turned round), and the space
labels are changed by the matrix `R`, a turn or a mirror when `Rᵀ R = 1`. -/
noncomputable def schwSym (ε c : ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) (x : Coords 4) : Coords 4 :=
  ![ε * x 0 + c, R 0 0 * x 1 + R 0 1 * x 2 + R 0 2 * x 3,
    R 1 0 * x 1 + R 1 1 * x 2 + R 1 2 * x 3, R 2 0 * x 1 + R 2 1 * x 2 + R 2 2 * x 3]

/-! ## The statements -/

/-- **Statement G1: Birkhoff's theorem for a whole space-time.** Take a curved space of four
dimensions with a length measure `g` that, on an open region `s` in one piece without holes
(simply connected), is a space-time, is empty, and looks the same from every side. Then at least
one of two things holds:

* there are a positive mass `m` and a length-keeping map from the region into Kruskal's whole
  space-time of mass `m`; or
* there are a mass `m` that is zero or negative and a length-keeping map from the region into
  Schwarzschild's whole space-time of mass `m` (flat space-time for `m = 0`).

For the whole curved space take `s = univ`. The map need not be one-to-one. -/
def GlobalBirkhoff : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M]
    (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M) (s : Set M),
    IsOpen s → IsSimplyConnected s → IsSpaceTimeOn g s → IsEmptyOn g s → IsRoundOn g ξ s →
    (∃ m : ℝ, 0 < m ∧ ∃ D : M → Coords 5, IsKruskalMapOn m g D s) ∨
      (∃ m : ℝ, m ≤ 0 ∧ ∃ D : M → Coords 4, IsSchwarzschildMapOn m g D s)

/-- **Statement: the map is unique up to a symmetry.** Take a space-time on a region in one
piece. Two length-keeping maps from the region into the same model space-time differ by a
symmetry of that model, the same symmetry at every point of the region:

* into Kruskal's whole space-time of a positive mass: a change of `(T, X)` that keeps
  `-T² + X²`, together with a turn or a mirror of the sphere;
* into Schwarzschild's whole space-time of a negative mass: a shift of time, possibly turned
  round, together with a turn or a mirror of space;
* into flat space-time (mass zero): a Lorentz transformation `Λ` (`Λᵀ · lightSign4 · Λ =
  lightSign4`) followed by a shift `b`.

With `GlobalBirkhoff`, this is what the research notes call the developing map of a round,
empty space-time. The region need not be simply connected here. -/
def GlobalBirkhoffUnique : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M] (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (s : Set M),
    IsPreconnected s → IsSpaceTimeOn g s →
    (∀ m : ℝ, 0 < m → ∀ D D' : M → Coords 5,
      IsKruskalMapOn m g D s → IsKruskalMapOn m g D' s →
      ∃ (L : Matrix (Fin 2) (Fin 2) ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ),
        L.transpose * lightSign2 * L = lightSign2 ∧ R.transpose * R = 1 ∧
          ∀ q ∈ s, D' q = kruskalSym L R (D q)) ∧
    (∀ m : ℝ, m < 0 → ∀ D D' : M → Coords 4,
      IsSchwarzschildMapOn m g D s → IsSchwarzschildMapOn m g D' s →
      ∃ (ε c : ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ), (ε = 1 ∨ ε = -1) ∧ R.transpose * R = 1 ∧
        ∀ q ∈ s, D' q = schwSym ε c R (D q)) ∧
    (∀ D D' : M → Coords 4, IsSchwarzschildMapOn 0 g D s → IsSchwarzschildMapOn 0 g D' s →
      ∃ (Λ : Matrix (Fin 4) (Fin 4) ℝ) (b : Coords 4),
        Λ.transpose * lightSign4 * Λ = lightSign4 ∧ ∀ q ∈ s, D' q = Λ.mulVec (D q) + b)

/-- **Statement: the other way round.** A space-time on an open region that has a length-keeping
map into Kruskal's whole space-time (positive mass), or into Schwarzschild's whole space-time of
a mass that is zero or negative and misses the centre there, is empty and looks the same from
every side on that region, by three fields of arrows found from the map.

(For mass zero the centre must be missed: flat space-time with its centre has no three fields
that sweep out surfaces at every point.) With `GlobalBirkhoff`: on a simply connected open
region, for a mass that is not zero, a space-time is round and empty **exactly when** it has
such a map. For mass zero, `GlobalBirkhoff` does not promise a map that misses the centre. -/
def GlobalBirkhoffConverse : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M] (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (s : Set M),
    IsSpaceTimeOn g s →
    ((∃ m : ℝ, 0 < m ∧ ∃ D : M → Coords 5, IsKruskalMapOn m g D s) ∨
      (∃ m : ℝ, m ≤ 0 ∧ ∃ D : M → Coords 4, IsSchwarzschildMapOn m g D s ∧
        ∀ q ∈ s, 0 < D q 1 ^ 2 + D q 2 ^ 2 + D q 3 ^ 2)) →
    ∃ ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M, IsEmptyOn g s ∧ IsRoundOn g ξ s

/-- **Statement: the mass is fixed by the space-time.** On a region that is not empty, where `g`
is a space-time, length-keeping maps into models of two different masses never both exist:
two maps into Kruskal's have the same mass, two maps into Schwarzschild's whole space-time of
mass zero or negative have the same mass, and a map into Kruskal's (positive mass) and one into
Schwarzschild's of mass zero or negative never both exist. -/
def GlobalMassUnique : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M] (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (s : Set M),
    s.Nonempty → IsSpaceTimeOn g s →
    (∀ m m' : ℝ, 0 < m → 0 < m' → ∀ D D' : M → Coords 5,
      IsKruskalMapOn m g D s → IsKruskalMapOn m' g D' s → m = m') ∧
    (∀ m m' : ℝ, m ≤ 0 → m' ≤ 0 → ∀ D D' : M → Coords 4,
      IsSchwarzschildMapOn m g D s → IsSchwarzschildMapOn m' g D' s → m = m') ∧
    (∀ m m' : ℝ, 0 < m → m' ≤ 0 → ∀ (D : M → Coords 5) (D' : M → Coords 4),
      IsKruskalMapOn m g D s → ¬ IsSchwarzschildMapOn m' g D' s)

/-! ## Checks, as statements for the team -/

/-- **The textbook map from Schwarzschild's space-time outside the rim into Kruskal's**
(Kruskal and Szekeres): with `κ = √(r / 2m - 1) · exp (r / 4m)`, `T = κ sinh (t / 4m)` and
`X = κ cosh (t / 4m)`; the angles go to the point of the unit sphere they describe. -/
noncomputable def kruskalOutside (m : ℝ) (x : Coords 4) : Coords 5 :=
  ![√(x 1 / (2 * m) - 1) * exp (x 1 / (4 * m)) * sinh (x 0 / (4 * m)),
    √(x 1 / (2 * m) - 1) * exp (x 1 / (4 * m)) * cosh (x 0 / (4 * m)),
    sin (x 2) * cos (x 3), sin (x 2) * sin (x 3), cos (x 2)]

/-- **The same inside the rim:** with `κ = √(1 - r / 2m) · exp (r / 4m)`, `T = κ cosh (t / 4m)`
and `X = κ sinh (t / 4m)` (the inside of the black hole, `T > |X|`). -/
noncomputable def kruskalInside (m : ℝ) (x : Coords 4) : Coords 5 :=
  ![√(1 - x 1 / (2 * m)) * exp (x 1 / (4 * m)) * cosh (x 0 / (4 * m)),
    √(1 - x 1 / (2 * m)) * exp (x 1 / (4 * m)) * sinh (x 0 / (4 * m)),
    sin (x 2) * cos (x 3), sin (x 2) * sin (x 3), cos (x 2)]

/-- **Statement (known answer): Schwarzschild's table maps into Kruskal's by the textbook
formulas,** outside the rim and inside it, for every positive mass. (Checked with a computer
algebra system before it was written here; that is not a proof.) -/
def KruskalMapOfSchwarzschild : Prop :=
  ∀ m : ℝ, 0 < m →
    IsKruskalMapOn m (flatMeasure (tableMeasure (roundG (schwA m) (schwB m))))
        (kruskalOutside m) (outside m) ∧
      IsKruskalMapOn m (flatMeasure (tableMeasure (roundG (schwA m) (schwB m))))
        (kruskalInside m) (inside m)

/-- A region of Schwarzschild's or de Sitter's table: distance label between `a` and `b`, pole
angle strictly between `0` and `π`; time and the angle around the axis are free. It is convex,
so it is in one piece and has no holes. -/
def shellBox (a b : ℝ) : Set (Coords 4) :=
  {x | a < x 1} ∩ {x | x 1 < b} ∩ {x | 0 < x 2} ∩ {x | x 2 < π}

/-- **Statement (the conclusion can fail): de Sitter's space-time has no length-keeping map
into any of the models.** On the region `shellBox 0 L` inside its horizon, de Sitter's table (an
empty universe with a cosmological constant, so not empty in the sense used here) is a
space-time and looks the same from every side, and the region is simply connected; but there is
no length-keeping map into Kruskal's whole space-time for any positive mass, nor into
Schwarzschild's whole space-time for any mass that is zero or negative. -/
def GlobalDeSitterNoMap : Prop :=
  ∀ L : ℝ, 0 < L →
    IsSimplyConnected (shellBox 0 L) ∧
    IsSpaceTimeOn (flatMeasure (tableMeasure (roundG (dsA L) (dsB L)))) (shellBox 0 L) ∧
    IsRoundOn (flatMeasure (tableMeasure (roundG (dsA L) (dsB L)))) turns (shellBox 0 L) ∧
    (¬ ∃ m : ℝ, 0 < m ∧ ∃ D : Coords 4 → Coords 5,
      IsKruskalMapOn m (flatMeasure (tableMeasure (roundG (dsA L) (dsB L)))) D (shellBox 0 L)) ∧
    (¬ ∃ m : ℝ, m ≤ 0 ∧ ∃ D : Coords 4 → Coords 4,
      IsSchwarzschildMapOn m (flatMeasure (tableMeasure (roundG (dsA L) (dsB L)))) D
        (shellBox 0 L))

/-- **Statement (the region must be in one piece): uniqueness fails on a region in two pieces.**
For every positive mass there are an open region of Kruskal's table (where the table is a
space-time) and two length-keeping maps from it into Kruskal's whole space-time that differ by
no single symmetry. -/
def GlobalUniqueNeedsOnePiece : Prop :=
  ∀ m : ℝ, 0 < m → ∃ (s : Set (Coords 4)) (D D' : Coords 4 → Coords 5),
    s ⊆ kruskalRegion ∧
    IsKruskalMapOn m (flatMeasure (tableMeasure (kruskalG m))) D s ∧
    IsKruskalMapOn m (flatMeasure (tableMeasure (kruskalG m))) D' s ∧
    ¬ ∃ (L : Matrix (Fin 2) (Fin 2) ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ),
        L.transpose * lightSign2 * L = lightSign2 ∧ R.transpose * R = 1 ∧
          ∀ q ∈ s, D' q = kruskalSym L R (D q)

end Curved

end GravityInLean
