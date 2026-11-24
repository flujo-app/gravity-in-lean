/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.Checks

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Statements to prove: which whole space-times are round and empty (G2)

**Nothing in this file is a proof of the statements it names**, except where a statement's own
comment names its proof. The definitions are tested in `Global/FreeFallChecks.lean`.

`GlobalBirkhoff` (`Goals/Global.lean`, proved) lays a round, empty space-time into Kruskal's (for
a positive mass) by a length-keeping map, but only a region without holes, and the map need not
be one-to-one. This file says which whole space-times there are: under one condition on paths of
free fall, a round, empty space-time with a positive mass, in one piece and Hausdorff, is
Kruskal's whole space-time or Kruskal's folded in two in one of four ways (G2 of the research
notes, `review/global-birkhoff.md`, sections 2.3 and 3).

## Paths of free fall on a curved space

A **path of free fall** (a geodesic of the textbooks) is a smooth curve on an open interval whose
velocity does not change along itself. On a curved space this is said through charts, in the way
the standard library says "smooth" and "slope" through the chart at the point:

* `chartTable g φ`: the table of the length measure `g` read in the chart `φ` (entry `(a, b)` at
  the point with coordinates `y` is the length of the `a`-th and `b`-th coordinate steps there);
  `chartTableInv g φ` is its inverse table.
* `FallsFreelyIn g φ γ τ`: read in the chart `φ`, the curve `γ` obeys the equation of free fall
  at the time `τ`, with the connection (Christoffel symbols) of the chart's table. The equation
  is the project's own coordinate equation `IsFreeFallAt` of `Curvature.lean`, tested on orbits
  around Schwarzschild's mass since step 1.
* `IsFreeFallPath g γ J`: `J` is an open interval, `γ` is smooth on it, and at every time `τ` in
  `J` it obeys the equation in the chart that the curved space provides at `γ τ`.

That the equation does not depend on the chart is the statement `FreeFallAnyChart` below, proved
in `Global/FreeFallChart.lean` (`freeFallAnyChart`; in coordinates it is `isFreeFallAt_inNewCoords`
of `SamePath.lean`). Asking it in the provided chart is how the standard library itself defines
slopes (`mfderiv` reads the map in the charts at the point).

**The clock is fixed by the path.** The equation fixes the clock along the path up to a shift
and a constant rate (for a path through time this clock is its own time; for light and for paths
through space there is no own time): a path of free fall run at a varying rate is no longer one
(`inRaySlow_not_isFreeFallPath`).

**Smooth, and why it is asked.** Lean gives every function a slope, zero where there is none. A
path with a kink, such as `τ ↦ |τ|`, passes the equation in flat space-time at every time with
these made-up slopes; only the smoothness clause rules it out (`kink_falls`,
`kink_not_isFreeFallPath`).

## The completeness condition

* `IsInextendibleFreeFall g γ J`: a path of free fall that no path of free fall on a longer open
  interval continues.
* `FreeFallComplete g ξ`: every such path either runs for all times, or at each end where it stops
  after a finite time the size of the spheres shrinks to zero (`sizeSq` of `Curved/Goal.lean`,
  read off from the three turning fields `ξ`). In Kruskal's space-time the paths that stop are
  exactly those that run into the centre `r = 0`, where the curvature grows without bound. The
  research notes call this s-completeness, with "a curvature invariant grows without bound" in
  place of "the spheres shrink to zero". The condition here asks a little more: that the size
  tends to zero, not only that it comes as close to zero as one likes. On a round, empty
  space-time with a positive mass the two agree: Kretschmann's invariant is `48 m² / r⁶`, and
  along a path of free fall `r` cannot come close to zero and move away again (part of the
  analysis behind `GlobalCompleteConverse`).

## Kruskal's space-time and its four foldings, with no quotient taken

`IsKruskalOnto m g F`: a map `F` from Kruskal's whole space-time (`kruskalSpace`, five numbers
`(T, X, y₁, y₂, y₃)`, `Goals/Global.lean`) onto the curved space that is smooth and keeps lengths.
Kruskal's whole space-time is not a curved space of the standard library here, so smooth and
length-keeping are said through its wrap charts `kruskalChart R`: wrap Kruskal's table of
`Goals/EveryPoint.lean` round the sphere (`kruskalWrap`, `Global/Checks.lean`) and turn the sphere
by `R`. These charts reach every point of Kruskal's whole space-time, poles included
(`kruskalChart_covers`), and keep its lengths (`kruskalChart_isKruskalMapOn`).

`IsKruskalOrFolded m g`: there is such a map, and the points it sends to the same point are
exactly

* each point alone: the curved space is Kruskal's whole space-time; or
* each point `p` and its partner `kruskalFold L p` for one of the four `L` in `kruskalFolds`:
  the curved space is Kruskal's folded in two. The fold sends the point `y` of the sphere to the
  opposite point `-y`, and changes `(T, X)` by `L`:

  | `L` | name in Chamblin and Gibbons | can tell future from past | orientable |
  |---|---|---|---|
  | `1` | `P` (RP² Schwarzschild) | yes | no |
  | `diag(-1, 1)`, `T ↦ -T` | `R_T P` | no | yes |
  | `diag(1, -1)`, `X ↦ -X` | `R_Z P` (the RP³ geon) | yes | yes |
  | `-1` | `R_T R_Z P` (elliptic interpretation) | no | no |

  Orientable here means the whole space-time. Chamblin and Gibbons list whether space is
  orientable, which differs from this exactly for the two foldings that cannot tell future from
  past (`kruskalFolds_table` checks the arithmetic behind the two columns).

  Each fold keeps lengths, sends Kruskal's whole space-time to itself, undoes itself, moves every
  point, and commutes with the turns of the sphere (`Global/FreeFallChecks.lean`). So "a map onto
  `M` whose fibres are the pairs `{p, fold p}`" says "`M` is Kruskal's divided by the fold": the
  map is a local diffeomorphism (it keeps lengths), so it is open, and an open, continuous map onto
  `M` makes `M` the quotient. A fold that differs from one of the four by a boost gives the same
  space-time, through a map put after that boost (`KruskalOntoSym`, `FoldsUpToSymmetry`).

## The statements

* `GlobalComplete` (G2): a curved space of four dimensions that is in one piece and Hausdorff,
  round, empty and a space-time everywhere, with a positive mass `m` (Kruskal's of mass `m` in a
  chart around some point), and that meets the completeness condition, is Kruskal's whole
  space-time of mass `m` or one of its four foldings.
* `GlobalCompleteOriented` (corollary): if it is also orientable and can tell future from past,
  it is Kruskal's or the RP³ geon.
* `GlobalCompleteConverse`: the other way round. Kruskal's whole space-time and each folding meet
  every assumption, the completeness condition included, for every three turning fields. (This
  holds the analysis of the paths of free fall of Kruskal's space-time, the hardest piece by the
  research notes.)
* `KruskalWholeExists`, `KruskalFoldsExist`: Kruskal's whole space-time and each of its four
  foldings exist as curved spaces of the standard library. With `GlobalCompleteConverse` they
  show that the assumptions of `GlobalComplete` can be met, and that every case of its conclusion
  occurs. `KruskalFoldsDistinct`: no space-time is two different foldings.
* `FreeFallAnyChart`: the equation of free fall does not depend on the chart (proved).

Steps of the route, as statements: `SizeSqIsRadius` (any three turning fields read off `r²`, so
the choice of `ξ` does no harm), `FreeFallMaximal` (every path of free fall lies in one that
cannot be continued), `FreeFallUnique` (two paths of free fall with the same start and the same
velocity agree; this is where "Hausdorff" enters), `KruskalOntoSym`, `FoldsUpToSymmetry`,
`TurnFixesPoint` and `SphereFreeInvolution` (proved: a turn of the sphere leaves a point where it
is, and the only symmetry of the sphere of order two that moves every point is the opposite-point
map).

Failure tests, as statements:

* `GlobalCompleteNeedsHausdorff`: without "Hausdorff" the statement is false. Example: two copies
  of Kruskal's space-time glued along one outside region. It is in one piece and has no holes,
  is round and empty, every path of free fall in it is carried to one of Kruskal's by the map
  that forgets the copy, and meets the condition (shown with the same analysis of Kruskal's paths
  as `GlobalCompleteConverse`); but next to the glued region the two copies of the rim cannot be
  told apart by open sets, and it is no folding of Kruskal's.
* `GlobalCompleteNeedsCompleteness`: without the completeness condition the statement is false.
  Example: Kruskal's table on `kruskalBox`, an open region in one piece (`Global/Checks.lean`). It
  meets every other assumption (`kruskal_meets_global` and the proved known answers); but a
  length-keeping map from Kruskal's whole space-time onto it would keep `X² - T²`
  (`globalBirkhoffUnique` on small pieces), and Kruskal's reaches `X² - T² = -1/2`, while the box
  has `X² - T² > -1/4`. (Kruskal's space-time with the sphere where the two rims cross removed,
  unwrapped so that it has no holes, is another example: the size of its spheres has no critical
  point, while Kruskal's and every folding have one, the sphere where the rims cross.)
* `GlobalCompleteNeedsConnected`: without "in one piece" the statement is false (two copies of
  Kruskal's side by side).

## Earlier work and route

The four foldings are in Chamblin and Gibbons (Phys. Rev. D 55 (1997) 2177, Table 1), who do not
claim the list is complete. That the list is complete, and G2 as a whole for round, empty
space-times, was not found written down (research notes, sections 2.3 and 3). Route on paper,
not checked: G1 on the universal cover (`globalBirkhoff`; the universal cover must first be built
as a curved space, the standard library has none), then the completeness condition lifts every
path of free fall of Kruskal's (this needs `SizeSqIsRadius`, `FreeFallMaximal` and
`FreeFallUnique`), so the developing map is a covering and, Kruskal's being simply connected, a
diffeomorphism; the group of the cover then acts on Kruskal's freely and properly by symmetries;
every symmetry fixes the sphere where the two rims cross, so the group acts freely on that
sphere, has order at most two (`TurnFixesPoint`), and its element is one of the four folds up to
a boost (`SphereFreeInvolution`, `FoldsUpToSymmetry`). Paths of free fall on a curved space were
not in this project, nor in the standard library (v4.36), before this file.

**Rule for anyone proving these: this file is not to be changed,** nor the definitions it uses
from `Global/Checks.lean` (`kruskalWrap`). A statement that is too hard, or false, is reported,
not weakened.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set Filter Topology

open scoped Manifold ContDiff

/-! ## Paths of free fall -/

section FreeFall

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Coords n) M]
  [IsManifold 𝓘(ℝ, Coords n) ∞ M]

/-- **The table of the length measure `g` in the chart `φ`.** Entry `(a, b)` at the point with
coordinates `y`: the length that `g` gives to the `a`-th and the `b`-th coordinate step at that
point, both taken to the curved space by the slope of the inverse chart. -/
noncomputable def chartTable (g : LengthMeasure 𝓘(ℝ, Coords n) M)
    (φ : OpenPartialHomeomorph M (Coords n)) : Fin n → Fin n → Coords n → ℝ :=
  fun a b y ↦ g (φ.symm y)
    (mfderiv 𝓘(ℝ, Coords n) 𝓘(ℝ, Coords n) φ.symm y (Pi.single a 1))
    (mfderiv 𝓘(ℝ, Coords n) 𝓘(ℝ, Coords n) φ.symm y (Pi.single b 1))

/-- **The inverse table** of the length measure in the chart: the inverse matrix of `chartTable`
at each point. (Where the table has no inverse, Lean's inverse matrix is zero; for a space-time
the table always has one.) -/
noncomputable def chartTableInv (g : LengthMeasure 𝓘(ℝ, Coords n) M)
    (φ : OpenPartialHomeomorph M (Coords n)) : Fin n → Fin n → Coords n → ℝ :=
  fun a b y ↦ (Matrix.of fun i j ↦ chartTable g φ i j y)⁻¹ a b

/-- **The curve `γ` falls freely at the time `τ`, read in the chart `φ`:** its coordinates in the
chart obey the equation of free fall `IsFreeFallAt` of `Curvature.lean` at `τ`, with the
connection (Christoffel symbols) of the chart's table. Only the curve near `τ` matters, so this
means something only when `γ τ` lies in the domain of the chart. -/
def FallsFreelyIn (g : LengthMeasure 𝓘(ℝ, Coords n) M) (φ : OpenPartialHomeomorph M (Coords n))
    (γ : ℝ → M) (τ : ℝ) : Prop :=
  IsFreeFallAt (christoffel (chartTable g φ) (chartTableInv g φ)) (fun s ↦ φ (γ s)) τ

/-- **A path of free fall on the open interval `J`** (a geodesic of the textbooks): `J` is open and
an interval (possibly unbounded), the curve `γ` is smooth on `J`, and at every time `τ` in `J` it
falls freely, read in the chart that the curved space provides at `γ τ`. The values of `γ` outside
`J` do not matter. -/
structure IsFreeFallPath (g : LengthMeasure 𝓘(ℝ, Coords n) M) (γ : ℝ → M) (J : Set ℝ) :
    Prop where
  /-- The interval is open. -/
  isOpen : IsOpen J
  /-- It is an interval: with two times it holds every time between them. -/
  interval : J.OrdConnected
  /-- The curve is smooth on it. -/
  smooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, Coords n) ∞ γ J
  /-- At every time it falls freely. -/
  falls : ∀ τ ∈ J, FallsFreelyIn g (chartAt (Coords n) (γ τ)) γ τ

/-- **A path of free fall that cannot be continued:** no path of free fall on a larger open
interval agrees with it on `J`. -/
def IsInextendibleFreeFall (g : LengthMeasure 𝓘(ℝ, Coords n) M) (γ : ℝ → M) (J : Set ℝ) :
    Prop :=
  IsFreeFallPath g γ J ∧
    ∀ (γ' : ℝ → M) (J' : Set ℝ), IsFreeFallPath g γ' J' → J ⊆ J' → EqOn γ' γ J → J' = J

/-- **The completeness condition.** Every path of free fall that cannot be continued either runs
for all times, or at each end where it stops after a finite time, the size of the spheres
(`sizeSq`, read off from the three turning fields `ξ`) shrinks to zero along it. An end that is a
finite time `b` is exactly a least upper bound `b` of the interval (or a greatest lower bound
`a`); an interval that is unbounded above has none, and asks nothing there. -/
def FreeFallComplete (g : LengthMeasure 𝓘(ℝ, Coords n) M) (ξ : Fin 3 → Arrows 𝓘(ℝ, Coords n) M) :
    Prop :=
  ∀ (γ : ℝ → M) (J : Set ℝ), IsInextendibleFreeFall g γ J →
    (∀ b : ℝ, IsLUB J b → Tendsto (fun t ↦ sizeSq g ξ (γ t)) (𝓝[<] b) (𝓝 0)) ∧
      ∀ a : ℝ, IsGLB J a → Tendsto (fun t ↦ sizeSq g ξ (γ t)) (𝓝[>] a) (𝓝 0)

end FreeFall

/-! ## Telling future from past, and orientation -/

section Orientation

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Coords n) M]
  [IsManifold 𝓘(ℝ, Coords n) ∞ M]

/-- **The space-time can tell future from past** (it is time-orientable): there is a continuous
field of arrows that is a step through time at every point. -/
def IsTimeOrientable (g : LengthMeasure 𝓘(ℝ, Coords n) M) : Prop :=
  ∃ X : Arrows 𝓘(ℝ, Coords n) M,
    Continuous (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, Coords n) M)) ∧
      ∀ x : M, g x (X x) (X x) < 0

variable (n M) in
/-- **The curved space is orientable:** it has an atlas of charts, smoothly compatible with its
own, that reach every point and whose changes of chart all have a positive determinant. -/
def IsOrientable : Prop :=
  ∃ A : Set (OpenPartialHomeomorph M (Coords n)),
    A ⊆ IsManifold.maximalAtlas 𝓘(ℝ, Coords n) ∞ M ∧ (∀ x : M, ∃ φ ∈ A, x ∈ φ.source) ∧
      ∀ φ ∈ A, ∀ ψ ∈ A, ∀ y ∈ φ.target, φ.symm y ∈ ψ.source →
        0 < LinearMap.det (fderiv ℝ (fun z ↦ ψ (φ.symm z)) y : Coords n →ₗ[ℝ] Coords n)

end Orientation

/-! ## Kruskal's whole space-time and its four foldings -/

/-- **The wrap chart turned by `R`:** Kruskal's table of `Goals/EveryPoint.lean`, wrapped round
the unit sphere by `kruskalWrap`, then the sphere turned (or mirrored) by the matrix `R`. -/
noncomputable def kruskalChart (R : Matrix (Fin 3) (Fin 3) ℝ) (x : Coords 4) : Coords 5 :=
  kruskalSym 1 R (kruskalWrap x)

/-- The four ways of folding: `L` changes the labels `(T, X)` (`1`: kept; `-1`: both turned round;
`diag(-1, 1)`: `T` turned round; `diag(1, -1)`: `X` turned round). -/
def kruskalFolds : Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  {1, -1, Matrix.diagonal ![-1, 1], Matrix.diagonal ![1, -1]}

/-- **The fold `L`:** the labels `(T, X)` are changed by `L`, and the point `y` of the sphere goes
to the opposite point `-y`. -/
noncomputable def kruskalFold (L : Matrix (Fin 2) (Fin 2) ℝ) : Coords 5 → Coords 5 :=
  kruskalSym L (-1)

section Onto

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  [IsManifold 𝓘(ℝ, Coords 4) ∞ M]

/-- **A length-keeping map from Kruskal's whole space-time of mass `m` onto the curved space.**
Read through each wrap chart `kruskalChart R` (with `Rᵀ R = 1`), the map is smooth on Kruskal's
region, and Kruskal's length of any two steps there is the length that `g` gives to the two steps
as the map carries them; and every point of the curved space is the image of a point of Kruskal's
whole space-time. The values of `F` off `kruskalSpace` do not matter. -/
def IsKruskalOnto (m : ℝ) (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (F : Coords 5 → M) : Prop :=
  (∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 →
    ContMDiffOn 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) ∞ (fun x ↦ F (kruskalChart R x)) kruskalRegion ∧
      ∀ x ∈ kruskalRegion, ∀ v w : TangentSpace 𝓘(ℝ, Coords 4) x,
        flatMeasure (tableMeasure (kruskalG m)) x v w
          = g (F (kruskalChart R x))
            (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) (fun y ↦ F (kruskalChart R y)) x v)
            (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) (fun y ↦ F (kruskalChart R y)) x w)) ∧
    ∀ q : M, ∃ p ∈ kruskalSpace, F p = q

/-- **The curved space is Kruskal's whole space-time of mass `m`, or one of its four foldings.**
There is a length-keeping map from Kruskal's whole space-time onto it that sends two points of
Kruskal's to the same point exactly when they are equal, or else exactly when they are equal or
partners under one of the four folds. -/
def IsKruskalOrFolded (m : ℝ) (g : LengthMeasure 𝓘(ℝ, Coords 4) M) : Prop :=
  ∃ F : Coords 5 → M, IsKruskalOnto m g F ∧
    ((∀ p ∈ kruskalSpace, ∀ q ∈ kruskalSpace, F p = F q ↔ q = p) ∨
      ∃ L ∈ kruskalFolds, ∀ p ∈ kruskalSpace, ∀ q ∈ kruskalSpace,
        F p = F q ↔ (q = p ∨ q = kruskalFold L p))

/-- **The curved space is Kruskal's whole space-time of mass `m` or the RP³ geon** (Kruskal's
folded by `X ↦ -X` together with the opposite point of the sphere). -/
def IsKruskalOrGeon (m : ℝ) (g : LengthMeasure 𝓘(ℝ, Coords 4) M) : Prop :=
  ∃ F : Coords 5 → M, IsKruskalOnto m g F ∧
    ((∀ p ∈ kruskalSpace, ∀ q ∈ kruskalSpace, F p = F q ↔ q = p) ∨
      ∀ p ∈ kruskalSpace, ∀ q ∈ kruskalSpace,
        F p = F q ↔ (q = p ∨ q = kruskalFold (Matrix.diagonal ![1, -1]) p))

end Onto

/-! ## The statements -/

/-- **Statement G2: which whole space-times are round and empty.** Take a curved space of four
dimensions that is in one piece and Hausdorff (two different points have neighbourhoods that do
not meet), with a length measure `g` and three fields of arrows `ξ` such that, on all of it,

* `g` is a space-time, space is empty, and the space-time looks the same from every side;
* the mass is positive: around some point, `g` is Kruskal's of mass `m > 0` in a chart (by
  `birkhoffAtEveryPointOneMass` and the uniqueness of the mass, `globalMassUnique`, the
  space-time is then Kruskal's of this same mass `m` around every point);
* every path of free fall that cannot be continued runs for all times, or the spheres shrink to
  zero at each end where it stops.

Then the curved space is Kruskal's whole space-time of mass `m`, or one of its four foldings. -/
def GlobalComplete : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M] [T2Space M] [ConnectedSpace M]
    (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M) (m : ℝ),
    0 < m → IsSpaceTimeOn g univ → IsEmptyOn g univ → IsRoundOn g ξ univ →
    (∃ p : M, IsKruskalNear m g p) → FreeFallComplete g ξ →
    IsKruskalOrFolded m g

/-- **Statement (corollary of G2): orientable and able to tell future from past gives Kruskal's
or the RP³ geon.** The assumptions of `GlobalComplete`, and the space is orientable and can tell
future from past. Then it is Kruskal's whole space-time of mass `m` or the RP³ geon. -/
def GlobalCompleteOriented : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M] [T2Space M] [ConnectedSpace M]
    (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M) (m : ℝ),
    0 < m → IsSpaceTimeOn g univ → IsEmptyOn g univ → IsRoundOn g ξ univ →
    (∃ p : M, IsKruskalNear m g p) → FreeFallComplete g ξ →
    IsOrientable 4 M → IsTimeOrientable g →
    IsKruskalOrGeon m g

/-- **Statement: the other way round.** A curved space in one piece and Hausdorff that is
Kruskal's whole space-time of a positive mass `m`, or one of its four foldings, meets every
assumption of `GlobalComplete`: it is a space-time, it is empty, it is Kruskal's of mass `m` in a
chart around each point, there are three turning fields for which it is round, and for every
three turning fields for which it is round it meets the completeness condition. -/
def GlobalCompleteConverse : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M] [T2Space M] [ConnectedSpace M]
    (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (m : ℝ),
    0 < m → IsKruskalOrFolded m g →
    IsSpaceTimeOn g univ ∧ IsEmptyOn g univ ∧ (∀ p : M, IsKruskalNear m g p) ∧
      (∃ ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M, IsRoundOn g ξ univ) ∧
      ∀ ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M, IsRoundOn g ξ univ → FreeFallComplete g ξ

/-- **Statement: Kruskal's whole space-time exists as a curved space,** for every positive mass:
a curved space of four dimensions, Hausdorff and in one piece, with a length measure and a
length-keeping map from Kruskal's whole space-time onto it that is one-to-one there. -/
def KruskalWholeExists : Prop :=
  ∀ m : ℝ, 0 < m →
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (Coords 4) M)
      (_ : IsManifold 𝓘(ℝ, Coords 4) ∞ M) (_ : T2Space M) (_ : ConnectedSpace M)
      (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (F : Coords 5 → M),
      IsKruskalOnto m g F ∧ ∀ p ∈ kruskalSpace, ∀ q ∈ kruskalSpace, F p = F q ↔ q = p

/-- **Statement: each of the four foldings exists as a curved space,** for every positive mass. -/
def KruskalFoldsExist : Prop :=
  ∀ m : ℝ, 0 < m → ∀ L ∈ kruskalFolds,
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (Coords 4) M)
      (_ : IsManifold 𝓘(ℝ, Coords 4) ∞ M) (_ : T2Space M) (_ : ConnectedSpace M)
      (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (F : Coords 5 → M),
      IsKruskalOnto m g F ∧
        ∀ p ∈ kruskalSpace, ∀ q ∈ kruskalSpace, F p = F q ↔ (q = p ∨ q = kruskalFold L p)

/-- **Statement: the equation of free fall does not depend on the chart** (proved:
`freeFallAnyChart`, `Global/FreeFallChart.lean`). On a curved space of four dimensions, where `g`
is a length measure (on an open region around the point) and the curve is smooth at the time `τ`,
the curve falls freely at `τ` read in any chart of the curved space's smooth structure whose
domain holds `γ τ` exactly when it does in the chart that the curved space provides there. -/
def FreeFallAnyChart : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M] (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (s : Set M)
    (γ : ℝ → M) (τ : ℝ) (φ : OpenPartialHomeomorph M (Coords 4)),
    IsOpen s → γ τ ∈ s → IsLengthMeasureOn g s →
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Coords 4) ∞ γ τ →
    φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M → γ τ ∈ φ.source →
    (FallsFreelyIn g φ γ τ ↔ FallsFreelyIn g (chartAt (Coords 4) (γ τ)) γ τ)

/-! ## Steps of the route, as statements -/

/-- **Statement: any three turning fields read off `r²`.** Where the space-time is Kruskal's of
a positive mass `m` in a chart, the squared size of the spheres read off from any three fields
that make it round is Kruskal's `r²` at the point. So the choice of the three fields in
`FreeFallComplete` does no harm. -/
def SizeSqIsRadius : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M] (g : LengthMeasure 𝓘(ℝ, Coords 4) M)
    (ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M) (s : Set M) (m : ℝ)
    (φ : OpenPartialHomeomorph M (Coords 4)),
    0 < m → IsRoundOn g ξ s → φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M →
    (∀ q ∈ φ.source, φ q ∈ kruskalRegion ∧ ∀ v w : TangentSpace 𝓘(ℝ, Coords 4) q,
      g q v w = flatMeasure (tableMeasure (kruskalG m)) (φ q)
        (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q v)
        (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q w)) →
    ∀ q ∈ φ.source ∩ s, sizeSq g ξ q = kruskalS m (φ q 0) (φ q 1)

/-- **Statement: every path of free fall lies in one that cannot be continued.** -/
def FreeFallMaximal : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Coords n) M]
    [IsManifold 𝓘(ℝ, Coords n) ∞ M] (g : LengthMeasure 𝓘(ℝ, Coords n) M)
    (γ : ℝ → M) (J : Set ℝ), IsLengthMeasureOn g univ → IsFreeFallPath g γ J →
    ∃ (γ' : ℝ → M) (J' : Set ℝ), J ⊆ J' ∧ EqOn γ' γ J ∧ IsInextendibleFreeFall g γ' J'

/-- **Statement: two paths of free fall with the same start agree.** On a Hausdorff curved space
where `g` is a length measure, two paths of free fall on the same interval that are at the same
point with the same velocity at one time agree at all times of the interval. -/
def FreeFallUnique : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Coords n) M]
    [IsManifold 𝓘(ℝ, Coords n) ∞ M] [T2Space M] (g : LengthMeasure 𝓘(ℝ, Coords n) M)
    (γ γ' : ℝ → M) (J : Set ℝ) (τ₀ : ℝ),
    IsLengthMeasureOn g univ → IsFreeFallPath g γ J → IsFreeFallPath g γ' J → τ₀ ∈ J →
    γ τ₀ = γ' τ₀ →
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Coords n) γ τ₀ (1 : ℝ) : Coords n)
      = (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Coords n) γ' τ₀ (1 : ℝ) : Coords n) →
    EqOn γ γ' J

/-- **Statement: a symmetry may be put before the map.** A length-keeping map from Kruskal's whole
space-time onto the curved space, put after a symmetry of Kruskal's, is again one. -/
def KruskalOntoSym : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M] (m : ℝ) (g : LengthMeasure 𝓘(ℝ, Coords 4) M)
    (F : Coords 5 → M) (L : Matrix (Fin 2) (Fin 2) ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ),
    IsKruskalOnto m g F → L.transpose * lightSign2 * L = lightSign2 → R.transpose * R = 1 →
    IsKruskalOnto m g (fun p ↦ F (kruskalSym L R p))

/-- **Statement: every change of `(T, X)` of order two that keeps `-T² + X²` is one of the four,
up to such a change.** -/
def FoldsUpToSymmetry : Prop :=
  ∀ L' : Matrix (Fin 2) (Fin 2) ℝ, L'.transpose * lightSign2 * L' = lightSign2 → L' * L' = 1 →
    ∃ B L : Matrix (Fin 2) (Fin 2) ℝ, B.transpose * lightSign2 * B = lightSign2 ∧
      L ∈ kruskalFolds ∧ B * L' = L * B

/-- **Statement: a turn of the sphere leaves a point where it is** (proved:
`turnFixesPoint`). -/
def TurnFixesPoint : Prop :=
  ∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 → R.det = 1 →
    ∃ y : Fin 3 → ℝ, dotProduct y y = 1 ∧ R.mulVec y = y

/-- **Statement: the only symmetry of the sphere of order two that moves every point is the
opposite-point map** (proved: `sphereFreeInvolution`). -/
def SphereFreeInvolution : Prop :=
  ∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 → R * R = 1 →
    (∀ y : Fin 3 → ℝ, dotProduct y y = 1 → R.mulVec y ≠ y) → R = -1

/-- **Statement: the four foldings are different.** No curved space is Kruskal's folded in two
ways: two length-keeping maps onto it whose points meet in pairs under the folds `L` and `L'`
have `L = L'`. -/
def KruskalFoldsDistinct : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M] (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (m : ℝ)
    (F F' : Coords 5 → M) (L L' : Matrix (Fin 2) (Fin 2) ℝ),
    0 < m → IsKruskalOnto m g F → IsKruskalOnto m g F' → L ∈ kruskalFolds → L' ∈ kruskalFolds →
    (∀ p ∈ kruskalSpace, ∀ q ∈ kruskalSpace, F p = F q ↔ (q = p ∨ q = kruskalFold L p)) →
    (∀ p ∈ kruskalSpace, ∀ q ∈ kruskalSpace, F' p = F' q ↔ (q = p ∨ q = kruskalFold L' p)) →
    L = L'

/-- **Statement ("in one piece" is needed).** `GlobalComplete` with "in one piece" left out is
false. Intended example: two copies of Kruskal's space-time side by side. -/
def GlobalCompleteNeedsConnected : Prop :=
  ¬ ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M] [T2Space M]
    (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M) (m : ℝ),
    0 < m → IsSpaceTimeOn g univ → IsEmptyOn g univ → IsRoundOn g ξ univ →
    (∃ p : M, IsKruskalNear m g p) → FreeFallComplete g ξ → IsKruskalOrFolded m g

/-! ## Failure tests, as statements -/

/-- **Statement (Hausdorff is needed).** `GlobalComplete` with "Hausdorff" left out is false.
Intended example: two copies of Kruskal's space-time glued along one outside region. -/
def GlobalCompleteNeedsHausdorff : Prop :=
  ¬ ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M] [ConnectedSpace M]
    (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M) (m : ℝ),
    0 < m → IsSpaceTimeOn g univ → IsEmptyOn g univ → IsRoundOn g ξ univ →
    (∃ p : M, IsKruskalNear m g p) → FreeFallComplete g ξ →
    IsKruskalOrFolded m g

/-- **Statement (the completeness condition is needed).** `GlobalComplete` with the completeness
condition left out is false. Intended example: Kruskal's table on `kruskalBox`, an open region in
one piece (`Global/Checks.lean`). It meets every other assumption (`kruskal_meets_global` and the
proved known answers); but a length-keeping map from Kruskal's whole space-time onto it would
keep `X² - T²` (`globalBirkhoffUnique` on small pieces), and Kruskal's reaches `X² - T² = -1/2`,
while the box has `X² - T² > -1/4`. -/
def GlobalCompleteNeedsCompleteness : Prop :=
  ¬ ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M] [T2Space M] [ConnectedSpace M]
    (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M) (m : ℝ),
    0 < m → IsSpaceTimeOn g univ → IsEmptyOn g univ → IsRoundOn g ξ univ →
    (∃ p : M, IsKruskalNear m g p) →
    IsKruskalOrFolded m g

end GravityInLean.Curved
