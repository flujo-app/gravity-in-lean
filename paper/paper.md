# Birkhoff's theorem without coordinates, machine-checked in Lean 4, and how teams of AI workers built it

**Mario Andreschak, Claude Fable 5.2 and Claude Opus 5.5**

*Claude Fable 5.2 and Claude Opus 5.5 are AI systems made by Anthropic. Section 10 sets out
what each author did.*

*Draft of 24 November 2026. Not submitted. Every number below is a measurement recorded in
`PLAN.md` or in the run logs of the repository; nothing is estimated unless it says so.*

## Abstract

We describe a formalisation in Lean 4 with mathlib of Birkhoff's theorem in a form that does not
start from coordinates: a smooth Lorentzian metric on a 4-manifold that is Ricci-flat and
carries three Killing fields with the brackets of so(3) and two-dimensional spacelike orbits is
locally Schwarzschild. Around every point where the gradient of the area radius is not null,
the formal statement gives a Schwarzschild chart, and it is proved together with its converse,
as one "if and only if". A second statement drops that condition and holds at every point,
including the horizon and the bifurcation sphere, where the target is the Kruskal–Szekeres
form; it gives one mass on each connected region. For a simply connected region the local
charts are glued into one local isometry, not necessarily one-to-one, into the Kruskal–Szekeres
space-time (or into Minkowski or negative-mass Schwarzschild space-time), unique up to a
symmetry of the model. The Levi-Civita connection of a metric of arbitrary signature is shown
to exist and to be unique, so "Ricci-flat" carries no hidden assumption. The definitions were
reviewed against the textbooks by three AI reviewers and are pinned by 25 tests in which a
definition must fail; no person who works in gravity has checked them yet. The development has
about 1,550 theorems (2,605 declarations in the axiom audit, about 39,400 lines of Lean) and
was produced in about 27 hours from the repository's first commit (23 November 2026, 01:08 UTC,
to 24 November, 04:13 UTC). Most of the proofs were written by teams of ten AI workers in seven
runs of 11 to 46 minutes each; the groundwork in coordinates, the definitions and the
statements were written by single AI sessions. The statements were fixed in advance, read by a
second AI instance that had not written them, and checked afterwards by a rebuild from scratch,
an audit of axioms and independent kernel checkers. We report what this cost, where the time
went, and what is not checked; there was no comparison run, the workers could reach the
network, and the costs are upper bounds. To our knowledge no earlier machine-checked Birkhoff
theorem starts from symmetry assumptions without coordinates; the mathematics itself is
classical, except that we found no complete written proof for the bifurcation sphere or for
the global statement.

## 1. Introduction

Birkhoff's theorem (Jebsen 1921, Birkhoff 1923) says that a spherically symmetric solution of
Einstein's vacuum equations is locally a piece of Schwarzschild's solution; in particular it
is static outside the horizon, whether or not the source moves. Textbook proofs choose
coordinates adapted to the symmetry at the outset and then solve the equations for the
remaining functions. The choice of coordinates is where the geometric content is hidden: that
such coordinates exist is a statement about a Lie algebra of Killing fields acting with
two-dimensional orbits, and it is usually taken for granted.

Machine-checked versions that start from a coordinate form exist (Section 2). This paper is
about a version that starts one step earlier, from a manifold, a metric and three vector
fields. What is machine-checked:

1. **The local theorem without coordinates** (`birkhoffNoCoordinates`): around every point
   where the gradient of the area radius is not null, a chart in the maximal atlas in which the
   metric is Schwarzschild's, exterior or interior, for some real mass.
2. **Every point, the horizon included** (`birkhoffAtEveryPoint`): with no condition on the
   gradient of the area radius, a chart onto an open piece of the Kruskal–Szekeres form for a
   positive mass, or of Schwarzschild's form for a mass that is zero or negative. This covers
   horizon points and the bifurcation sphere.
3. **One mass per connected region** (`oneMass`, `birkhoffAtEveryPointOneMass`).
4. **The converse of item 1, and the two directions as one statement**
   (`schwarzschildExactlyWhen`, `birkhoffExactlyWhenInCoordinates`), at points where the
   gradient of the area radius is not null. Item 2 has no such local converse.
5. **Existence and uniqueness of the Levi-Civita connection** for a non-degenerate metric of any
   signature on a manifold (`connectionExists`, `connectionUnique`). mathlib v4.36.0 has both
   for Riemannian metrics.
6. **The whole space-time** (`globalBirkhoff`, `globalBirkhoffUnique`,
   `globalBirkhoffConverse`, `globalMassUnique`): on a simply connected open region, one
   local isometry (not necessarily one-to-one) into Kruskal–Szekeres space-time for a positive
   mass, or into Schwarzschild space-time (Minkowski for mass zero) for a mass that is zero or
   negative; unique up to a symmetry of the model when the region is in one piece; and a
   converse, which assumes the metric Lorentzian on the region and, for mass zero, asks the map
   to miss the centre of Minkowski space, where the rotation fields vanish (Section 4).
7. **Two results the above needed that mathlib v4.36.0 does not have:** smooth dependence of a
   flow on time and initial point jointly (`smoothFlow`), and adapted coordinates for three
   vector fields with so(3) brackets and two-dimensional orbits (`turnsCoordinates`).

The second subject of the paper is the method. The proofs were not written by a person. They
were written by teams of AI workers against statements that were fixed beforehand and could not
be changed by the teams. Section 7 reports the measurements, and Section 8 says plainly what
this method does and does not establish.

## 2. Related work

**On paper.** The theorem goes back to Jebsen (1921) and Birkhoff (1923). Hawking and Ellis
(1973, Appendix B) give the standard modern proof, which distinguishes cases by the character
of the gradient of the area radius. A proof that avoids introducing coordinates is due to
Schmidt (1997, arXiv:gr-qc/9709071). Schleich and Witt (2010, arXiv:0908.4110) assume, as we
do, local so(3) Killing fields rather than a group action; their companion note (arXiv:0910.5194)
discusses what the theorem does and does not say globally. Chruściel's lecture notes state the
theorem near points where the gradient is not null. For horizon points with non-vanishing
gradient, an explicit Eddington–Finkelstein form is given by An and Wong (2018,
arXiv:1707.01483, Theorem 3.2) under a global warped-product assumption. For the bifurcation
sphere, where the gradient vanishes, we did not find a complete written proof in the sources we
read (Hawking and Ellis treat it in one sentence; see `review/global-birkhoff.md` in the
repository for what was read and how). We say "not found written down"; we do not say the
argument is new.

**In proof assistants.** All of the following were found by searches in November 2026 and are
documented with dates in `SURVEY.md` and `TARGETS.md`.

- *ProjectAinos* (`x-oai/ProjectAinos`) proved Birkhoff's theorem in Lean 4 from a fixed
  diagonal form −A(t,r)dt² + B(t,r)dr² + r²dΩ² with A, B > 0 (so outside the horizon only)
  on 19 November 2026, four days before the coordinate version in this repository. The coordinate result here is therefore not a first.
- *grlab* (`BrandonMYates/grlab`, August 2026) has the last step of the static case.
- *Lightlike* (`LightLikeProject/lightlike`) builds orbit charts from a Killing algebra and uses
  them for homogeneous and isotropic 3-metrics (the cosmological case), not for so(3) with
  two-dimensional orbits. It also develops Lorentzian metrics, the Levi-Civita connection and
  curvature on manifolds (reported by a research helper; we read its orbit-chart files). Its
  file list, read on 24 November 2026, also shows the Kruskal–Szekeres space-time as a manifold,
  geodesics on it, and a proof, added on 19 November 2026, that it has no extension with a
  smooth metric (`Lightlike/GR/KruskalMaximal.lean`, whose header we read). It has no file on
  Birkhoff's theorem.
- *TauCeti* (`TauCetiProject/TauCeti`) proved, earlier than this repository and independently,
  that a non-degenerate metric of any signature has a Levi-Civita connection; mathlib v4.36.0
  has existence and uniqueness for Riemannian metrics
  (`Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean`). The proof here was
  made from the textbook (Koszul's formula; O'Neill 1983, Chapter 3) by workers instructed not to
  read any other project's proof, and the run's log shows no access to the network. An
  earlier team run had begun to port TauCeti's proof; it was stopped before anything was merged
  and its files were discarded, so the proof in the repository comes from a later, fresh team.
- Schwarzschild's solution itself had been verified in Lean at least twice before: in
  `BishopWolf/physics` (folder `gravitation/`, from 21 November 2026), at one point in one set of
  coordinates, and in a 2026 preprint on a Schwarzschild curvature pipeline in Lean 4, whose
  code we did not find (both in `SURVEY.md`).
- The community physics library *physlib* (`leanprover-community/physlib`, formerly HepLean)
  has special relativity and tensors, and in its experimental part the interior of a star of
  constant density; general relativity proper sits in open pull requests.
- *Other proof assistants.* Isabelle/HOL has special relativity from axioms (Stannett and
  Németi, arXiv:1211.6468), Minkowski space-time from Schutz's axioms (Schmoetten, Palmer and
  Fleuriot 2022), and a first-order axiomatic version of general relativity without curvature
  (the AFP entry `No_FTL_observers_Gen_Rel`, 2023). We found no curvature-based general
  relativity in Isabelle, Coq/Rocq or HOL.

**Side by side.** The two earlier Birkhoff statements, read in their source files on 24 November
2026 (ProjectAinos: `theorem birkhoff` in `ProjectAinos/GeneralRelativity/Birkhoff.lean`;
grlab: `theorem exists_mass_of_areal_vacuum` in `GRLab/Birkhoff.lean`), against the two main
statements here:

| | ProjectAinos, `birkhoff` | grlab, `exists_mass_of_areal_vacuum` | here, `birkhoffNoCoordinates` | here, `birkhoffAtEveryPoint` |
|---|---|---|---|---|
| Space | an open box of (t, r, θ, φ) in ℝ⁴ | an open interval of r in ℝ | any smooth 4-manifold | any smooth 4-manifold |
| Metric | −A(t,r)dt² + B(t,r)dr² + r²dΩ², smooth, A, B > 0 | one function f(r); the metric −f dt² + f⁻¹dr² + r²dΩ² appears only in comments | any smooth Lorentzian metric | the same |
| Symmetry | built into the formula | built into the formula, and static | three Killing fields with so(3) brackets and two-dimensional spacelike orbits | the same |
| Vacuum | every Ricci component of the coordinate table vanishes | the single equation 1 − f − r f′ = 0 | the Ricci tensor of the Levi-Civita connection vanishes; the connection is proved to exist | the same |
| Coordinates in the hypotheses | yes | yes | none | none |
| Conclusion | B = r/(r−2M) and A = f(t)(r−2M)/r, with r > 2M | f = 1 − 2M/r | a chart around p in which the metric is Schwarzschild's, r > 2m or 0 < r < 2m | a chart around p onto Kruskal's form (m > 0) or Schwarzschild's (m ≤ 0) |
| Where | outside the horizon | an interval avoiding r = 0 | every point where the gradient of the area radius is not null; includes the inside of the horizon | every point |

The row that matters is the fifth. In both earlier theorems the coordinates, and the symmetry
with them, are part of the hypothesis; here they are part of the conclusion. ProjectAinos's
theorem is comparable to the coordinate version in this repository, which is four days younger
and is not claimed as new; its companion `birkhoff_timeChange` also removes the factor f(t) by a
new time T with T′ = √f, giving the exterior Schwarzschild form. grlab's file says of itself that it is the calculus core of the
static case and not the full theorem.

**To our knowledge**, no machine-checked Birkhoff theorem in any proof assistant starts from
symmetry assumptions without coordinates, or covers the horizon. This is a statement about what
we found, on the dates given, and must be re-checked on the day of submission.

## 3. Definitions

The base is Lean 4 (de Moura and Ullrich 2021) and mathlib's (mathlib Community 2020)
manifolds, tangent bundle, Lie bracket of vector fields (`mlieBracket`, with
[X, Y] = XY − YX) and covariant derivatives on vector bundles (`IsCovariantDerivativeOn`). On
top of these the project defines, in `GravityInLean/Curved/Basic.lean` and `Curved/Goal.lean`
(the metric has signature (−, +, +, +)):

| Notion | Lean name | Definition, in short |
|---|---|---|
| Metric | `LengthMeasure I M` | a continuous bilinear form on each tangent space |
| Lorentzian | `HasOneTimeDirection`, `IsSpaceTimeOn g s` | symmetric, smooth, and there is a timelike vector whose orthogonal complement is positive definite |
| Levi-Civita connection | `IsConnectionOf g cov s` | on an open set: a covariant derivative, torsion-free, metric-compatible |
| Curvature, Ricci | `curvatureAt`, `ricciAt` | R(X,Y)Z on extensions of vectors; trace over the first slot in a basis |
| Vacuum | `IsEmptyOn g s` | there is a connection of g on s whose Ricci tensor vanishes |
| Killing field | `LeavesUnchangedAt g ξ x` | ξ is differentiable at x and ξ(g(X,Y)) = g([ξ,X],Y) + g(X,[ξ,Y]) |
| Spherical symmetry | `IsRoundOn g ξ s` | three smooth Killing fields with [ξ₀,ξ₁]=ξ₂ and cyclic, spanning a 2-plane at each point, on which g is positive |
| Area radius squared | `sizeSq g ξ` | (g(ξ₀,ξ₀)+g(ξ₁,ξ₁)+g(ξ₂,ξ₂))/2 |
| Non-null gradient | `UsableDistanceAt g ξ p` | the gradient of `sizeSq` at p exists as a vector and is not null |

Three design decisions matter for what follows.

*Regions are open by definition.* The connection and symmetry predicates carry `IsOpen s`. An
early version did not, and the second reader found that "vacuum" could then be satisfied on a
single point by any metric.

*Vacuum is existential in the connection.* This is harmless because the connection is unique
(`connectionUnique`) and exists (`connectionExists`); before the latter was proved, a reviewer
correctly noted that the theorem read "assuming the Levi-Civita connection exists".

*Symmetry is infinitesimal.* No group action is assumed, only the three fields.

```lean
structure IsRoundOn (g : LengthMeasure I M) (ξ : Fin 3 → Arrows I M) (s : Set M) : Prop where
  isOpen : IsOpen s
  smooth : ∀ i, CMDiff[s] ∞ (T% (ξ i))
  unchanged : ∀ i, ∀ x ∈ s, LeavesUnchangedAt g (ξ i) x
  likeTurns : ∀ x ∈ s, mlieBracket I (ξ 0) (ξ 1) x = ξ 2 x ∧
    mlieBracket I (ξ 1) (ξ 2) x = ξ 0 x ∧ mlieBracket I (ξ 2) (ξ 0) x = ξ 1 x
  surfaces : ∀ x ∈ s, Module.finrank ℝ (Submodule.span ℝ (Set.range fun i ↦ ξ i x)) = 2
  positive : ∀ x ∈ s, ∀ v ∈ Submodule.span ℝ (Set.range fun i ↦ ξ i x), v ≠ 0 → 0 < g x v v
```

## 4. Statements

All final statements are definitions of type `Prop` in `GravityInLean/Goals/` and
`Curved/Goal.lean`, written before any proof existed. The first one:

```lean
def BirkhoffNoCoordinates : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M] [IsManifold 𝓘(ℝ, Coords 4) ∞ M]
    (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M) (s : Set M),
    IsOpen s → IsSpaceTimeOn g s → IsEmptyOn g s → IsRoundOn g ξ s →
    ∀ p ∈ s, UsableDistanceAt g ξ p →
      ∃ (m : ℝ) (φ : OpenPartialHomeomorph M (Coords 4)),
        φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M ∧ p ∈ φ.source ∧
        ∀ q ∈ φ.source, (φ q ∈ outside m ∨ φ q ∈ inside m) ∧
          ∀ v w : TangentSpace 𝓘(ℝ, Coords 4) q,
            g q v w = flatMeasure (tableMeasure (roundG (schwA m) (schwB m))) (φ q)
              (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q v)
              (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q w)
```

Here `roundG (schwA m) (schwB m)` is the Schwarzschild metric in (t, r, θ, φ),
−(1 − 2m/r)dt² + (1 − 2m/r)⁻¹dr² + r²(dθ² + sin²θ dφ²), and `outside m`,
`inside m` are r > 2m and 0 < r < 2m with r > 0 and sin θ ≠ 0. The mass is any real number:
m = 0 is Minkowski space, and negative masses are not excluded.

The statement at every point drops the gradient condition and changes the target:

```lean
def BirkhoffAtEveryPoint : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M] [IsManifold 𝓘(ℝ, Coords 4) ∞ M]
    (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M) (s : Set M),
    IsOpen s → IsSpaceTimeOn g s → IsEmptyOn g s → IsRoundOn g ξ s →
    ∀ p ∈ s, (∃ m : ℝ, 0 < m ∧ IsKruskalNear m g p) ∨
      (∃ m : ℝ, m ≤ 0 ∧ IsSchwarzschildWith m g p)
```

`IsKruskalNear m g p` asks for a chart around p into the region X² − T² > −1, sin θ ≠ 0, in
which g is (32m³/r)e^{−r/2m}(−dT² + dX²) + r²dΩ², with r defined by
(r/2m − 1)e^{r/2m} = X² − T². The radius is defined in Lean as an infimum and proved to be the
unique positive root and smooth (`kruskalRadiusSpec`, `kruskalRadiusSmooth`).

The global statement glues the local charts on a simply connected region:

```lean
def GlobalBirkhoff : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M]
    (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M) (s : Set M),
    IsOpen s → IsSimplyConnected s → IsSpaceTimeOn g s → IsEmptyOn g s → IsRoundOn g ξ s →
    (∃ m : ℝ, 0 < m ∧ ∃ D : M → Coords 5, IsKruskalMapOn m g D s) ∨
      (∃ m : ℝ, m ≤ 0 ∧ ∃ D : M → Coords 4, IsSchwarzschildMapOn m g D s)
```

Here Kruskal–Szekeres space-time is written with the sphere as the unit sphere in ℝ³, so that
no pole is left out: points (T, X, y) with X² − T² > −1 and |y| = 1, and the metric
A(r)(−dT² + dX²) + r²(dy₁² + dy₂² + dy₃²). The map D is a local isometry and is not required to
be one-to-one: it keeps lengths, and that is all. Companion statements say that D is unique up
to a symmetry of the model on a region in one piece (`GlobalBirkhoffUnique`), that the mass is
fixed by the space-time (`GlobalMassUnique`), and that the converse holds
(`GlobalBirkhoffConverse`): a Lorentzian metric with such a map is Ricci-flat and spherically
symmetric on the region. For mass zero the converse also asks the map to miss the centre
x₁ = x₂ = x₃ = 0 of Minkowski space, where the rotation fields vanish and so span no surface;
`GlobalBirkhoff` does not promise such a map. So the two directions match exactly for a mass
that is not zero.
Three checks show the statements are not empty or too easy: Schwarzschild's exterior and
interior map into Kruskal's by the textbook formulas (`KruskalMapOfSchwarzschild`), de Sitter
space has no such map (`GlobalDeSitterNoMap`), and uniqueness fails on a region in two pieces
(`GlobalUniqueNeedsOnePiece`).

What we did not prove: a classification of all maximal or inextendible such space-times. At
tag `paper-1-numbers` none was stated, because it needs geodesics on a manifold, which neither
the project nor mathlib had (Lightlike has them, Section 2). Since then the statements have
been written, not proved (`Goals/GlobalComplete.lean`): a connected, Hausdorff space-time that
is spherically symmetric, Ricci-flat, of positive mass and complete in a sense defined through
geodesics is Kruskal–Szekeres or one of its four quotients by a reflection. The Hausdorff
condition is needed: Lean's manifolds need not be Hausdorff, and two copies of Kruskal–Szekeres
glued along one exterior region form a connected manifold, not Hausdorff at the horizon, that
meets every other condition and is none of the five (`GlobalCompleteNeedsHausdorff`, also a
statement, not yet proved).

The other statements, with their proofs' names:

| Statement | Content | Proof |
|---|---|---|
| `SchwarzschildExactlyWhen` | (∃ open s ∋ p and ξ: Lorentzian, vacuum, round, non-null gradient at p) ⇔ Schwarzschild in a chart around p | `schwarzschildExactlyWhen` |
| `SchwarzschildIsEmptyStatement` | Schwarzschild in a chart ⇒ vacuum near p, exterior and interior, no symmetry assumed | `schwarzschildIsEmpty` |
| `BirkhoffExactlyWhenInCoordinates` | for a spherically symmetric table: Ricci-flat ⇔ Schwarzschild after a smooth relabelling of (t, r) | `birkhoffExactlyWhenInCoordinates` |
| `OneMassStatement` | on an open connected region: one m for all points with non-null gradient, also across a horizon | `oneMass` |
| `BirkhoffAtEveryPointOneMass` | the statement at every point with one m on a connected region | `birkhoffAtEveryPointOneMass` |
| `ConnectionExistsStatement`, `ConnectionUniqueStatement` | Levi-Civita connection of a non-degenerate smooth metric on an open set: exists, is unique on differentiable fields | `connectionExists`, `connectionUnique` |
| `SmoothFlowStatement` | the local flow of a smooth vector field on a Banach space is jointly smooth in time and initial point | `smoothFlow` |
| `TurnsCoordinatesStatement` | three smooth Killing fields of a regular metric table on an open subset of ℝ⁴, with so(3) brackets, rank 2 and positive on their span, are, in suitable coordinates and after one fixed rotation, the standard rotation fields (the proof uses only that the region is open, smoothness, the brackets and the rank) | `turnsCoordinates` |

## 5. Proof architecture

The development has three layers.

**Coordinates.** Christoffel symbols and the Ricci tensor of a table of functions; Schwarzschild
is Ricci-flat; a spherically symmetric table has the general form −A dt² + 2C dt dρ + B dρ² +
S dΩ² (`shape_of_round`); for that form the vacuum equations make the mass function constant
and give a new time coordinate by a Poincaré-lemma argument (`birkhoff_general`). Curvature,
geodesics and Killing's equation are proved invariant under changes of coordinates.

**Two missing library results.** *Smooth flows:* the integral curves are the zeros of one
smooth map on the Banach space of continuous paths, with the time as a scaling parameter; the
implicit function theorem then gives joint smoothness (11 files, about 980 lines). *Adapted
coordinates:* a rotation of the three fields makes one of them vanish at the base point;
transport of one field along the flow of another is computed by uniqueness for linear ODEs; the
zero set of the vanishing field is a transversal surface, obtained from two dot products and
the implicit function theorem; the chart is a composition of two flows (20 files, about 2,070
lines). The team that proved this found that neither the Killing property nor positivity is
needed for it.

**The join.** Every notion of Section 3 is carried along a chart to an open subset of ℝ⁴ and
there to tables. For curvature this is done without computing in the chart: the carried
connection is a connection of the carried metric, the table has its own, and uniqueness
identifies them. In the adapted coordinates the table has the general form on a box around the
equatorial point (the textbook argument evaluates one rotation a quarter turn away, outside
any small box; a worker noticed this and re-proved the shape lemma at the base point). The
coordinate theorem then gives the mass and a smooth new time, and the composed map is shown to
be a chart in the maximal atlas (24 files, about 4,500 lines).

**The horizon.** In the time–radius plane two null coordinates u, v are constructed as first
integrals of the two null direction fields. In them the vacuum equations integrate once each.
The paper route then reparametrised u and v by solving an ODE with a regular singular point.
The team replaced this by a lemma that needs no singular ODE:

```lean
theorem product_form {Ω : ℝ → ℝ → ℝ} {J I : Set ℝ} (hJ : IsOpen J) (hJc : IsPreconnected J)
    (hI : IsOpen I) (hIc : IsPreconnected I)
    (hΩ : ContDiffOn ℝ ∞ (Function.uncurry Ω) (J ×ˢ I))
    (heq : ∀ u ∈ J, ∀ v ∈ I, Ω u v * dt (dr Ω) u v = dt Ω u v * dr Ω u v)
    (hne : ∀ u ∈ J, ∀ v ∈ I, dt (dr Ω) u v ≠ 0) :
    ∀ u ∈ J, ∀ v ∈ I, ∀ u₀ ∈ J, ∀ v₀ ∈ I,
      Ω u v * dt (dr Ω) u₀ v₀ = dr Ω u v₀ * dt Ω u₀ v
```

Here `dt` and `dr` are the partial derivatives in the first and the second argument, so
`dt (dr Ω)` is Ω_uv. A smooth Ω with Ω·Ω_uv = Ω_u·Ω_v and Ω_uv ≠ 0 is a product of a function of u and a function of
v on the whole box, across its zeros. Applied to Ω = (r/2m − 1)e^{r/2m}, the two factors are the
Kruskal null coordinates. The same argument covers points off the horizon, so for positive mass
no case distinction on the gradient is needed. For m ≤ 0 the gradient is never null and the
first theorem applies (24 files, about 4,700 lines).

**The whole space-time.** The local theorem at every point gives charts into the model. Two
such charts differ, on their overlap, by a map of coordinate space that carries the model's
table to itself. The team did not use the ordinary differential equation of the route on paper.
Instead such a map keeps the Kretschmann invariant R_abcd R^abcd = 48m²/r⁶, hence the radius
(the project's `kretschmann` contracts R^a_bρμ R^b_aστ g^ρσ g^μτ, which is the same invariant
with the opposite sign, −48m²/r⁶). It keeps the covariant Hessian of the radius, which is m/r²
times the metric on the (T, X) plane and (r − 2m)/r² times it on the sphere; where r ≠ 3m these
differ, so the map keeps the split into plane and sphere, and the points with r ≠ 3m are dense,
so the split is kept everywhere. On the plane the map keeps a constant quadratic form, hence it
is affine, and since it keeps X² − T² it has no shift; on the sphere it is a rotation or a
reflection. For m < 0 the same steps run in Schwarzschild's form (`Global/UniqueSchw.lean`). For
m = 0 the invariant vanishes and the step is simpler: a map that keeps the flat metric is affine,
a Lorentz transformation and a shift (`Global/UniqueFlat.lean`). So two charts
differ by a symmetry of the model, a region in
one piece has one symmetry, and on a simply connected region the local maps are glued by
continuation (40 files, about 9,400 lines).

## 6. How the definitions were checked

Lean checks that a proof proves its statement, not that the statement means what is intended.
Four things were done about that.

1. **Known answers before use.** Minkowski space, the round sphere, de Sitter space and
   Schwarzschild's exterior and interior were run through the definitions before any theorem
   was stated on them; later also Kruskal's table on its whole region.
2. **An independent second reader before each statement was fixed.** A separate model instance,
   given only the files, was asked for a counterexample or a proof sketch for every clause. For
   the first set of definitions this found six gaps, all closed before use (Section 3 names two).
3. **A review against the textbooks.** Three independent reviewers (a relativist's reading, an
   adversary's, and one on Lean conventions) compared each definition with the standard
   textbooks: `REVIEW.md` and the folder `review/`. Verdict: no definition wrong, no way found for the statement to
   hold for the wrong reason, and a list of limits, most of which the later runs removed.
4. **Failure tests.** The reviewers proposed 25 tests, most of them cases where a definition
   must fail. All 25 are proved; none turned out false. Examples: in Eddington–Finkelstein
   coordinates every hypothesis holds on the horizon except the non-null gradient; three zero
   fields are not "spherically symmetric"; a metric with two time directions is not Lorentzian;
   a squashed sphere is not symmetric under the standard rotations; de Sitter space is
   Schwarzschild in no chart; Minkowski space with Cartesian rotation fields is symmetric,
   poles included.

None of the reviewers is a human expert. That remains to be done.

## 7. The method and its measurements

**Set-up.** Each proving job was given to a team of ten AI agents in one Docker container on a
single desktop PC (8 threads, 32 GB): one lead and nine workers, all Claude Fable 5.2 at
reasoning effort "high", run by the FACTORY framework (version 0.11.0) with Claude Code as the
worker program. The lead reads, plans, writes the statements of intermediate lemmas and hands
them out; workers prove one lemma each in their own copy of the repository. One Lean run at a
time for the whole team, through a queue; the copies share one build of the project.

**Protocol.** (i) The final statement is a `def … : Prop` in a file the team may not edit.
(ii) A second reader judges it before the run. (iii) The brief gives a proof route worked out
on paper and marked as unchecked. (iv) The team's branches come back as a git bundle. (v) The
supervisor diffs the bundle against the starting commit, adds
`example : Statement := theorem` to the audit file, rebuilds the whole project from scratch and
checks that every declaration rests only on `propext`, `Classical.choice` and `Quot.sound`.

**What the workers could see and reach.** Each worker had the repository at the starting
commit (all earlier proofs, the definitions and the fixed statements), the brief (the
statement, the rules and the route on paper) and the source of mathlib in the image. The
container was not cut off from the internet, because the agents reach the model through it.
The briefs limited its use: in runs 1 to 3 to reading documentation; in run 4 to reading
documentation and the one file of another project named in a side job that was later
withdrawn (see below); in run 5 no web search and no other project's proof. The briefs of runs
6 and 7 forbade only sending anything out; they pointed the workers to mathlib's files for
looking things up but did not forbid reading the web. Only run 5's record was checked for use
of the network, and none was found. For the other runs the records do not show that the network
went unused.

**Measurements.** Times run from "all ten agents ready" to "whole project builds with the
proof".

| Run | Job | Files | Lines | Theorems | Minutes | Lean runs (failed) | Tokens read / written (millions) |
|---|---|---|---|---|---|---|---|
| 1 | `smoothFlow` | 11 | 980 | 24 | 14 | 20 (1) | 9.4 / 0.18 |
| 2 | `turnsCoordinates` | 20 | 2,070 | 62 | 17 | 52 (9) | 16.6 / 0.32 |
| 3 | `birkhoffNoCoordinates` | 24 | 4,500 | 168 | 21 | 79 (17) | 39.2 / 0.57 |
| 4 | both directions (6 statements) | 14 | 2,000 | 83 | 11 | 46 (10) | 23.4 / 0.36 |
| 5 | 25 failure tests, one mass, the connection | 29 | 3,800 | 134 | 14 | 80 (10) | 37.6 / 0.41 |
| 6 | every point, horizon included (11 statements) | 24 | 4,700 | 155 | 29 | 72 (13) | 47.4 / 0.75 |
| 7 | the whole space-time (7 statements) | 40 | 9,400 | 350 | 46 | 132 (19) | 102 / 1.23 |

Notes on the table. Run 7's figures leave out `Global/Checks.lean` (707 lines, 52 theorems),
which the supervisor wrote with the statements before the run. For runs 1 to 6 the Lean runs are
counted until the goal's build; run 7's record counts them from 03:11 to 03:59, two minutes past
its goal's build. Tokens are counted until each team was stopped, a few minutes after its goal;
where the record splits them, 95 to 96 percent of the tokens read came from the prompt cache.

Together: about 27,400 lines of checked proof in 152 minutes of team time, for about 276
million tokens read and 3.8 million written. The cost was also measured as the change of the
subscription's two weekly usage meters ("all models" and "Fable") over each run; these are upper
bounds, because other sessions ran at the same time. Runs 1 to 6 took 2 to 5 points of the "all
models" meter and 3 to 11 points of the "Fable" meter each; run 7 took 11 and 22 points (62% to
73% and 72% to 94%; details in `PLAN.md`).

**What these numbers show, and what they do not.** All 54 statements fixed before the runs
were proved without a change to any of them, and no person wrote or repaired a proof. Of 481
Lean runs, 79 failed and were repaired by the teams. There is no comparison point: the same job
was not run by one agent instead of ten, nor without the route in the brief, nor by a person.
Lines and theorems depend on style and are given for scale only.

**Where the time went.** Not into proving. The definitions and the first goal took one
supervising agent 57 minutes to a first green build and 80 minutes including the second
reading; each later set of statements took about 20 minutes to write and 12 to 13 minutes to
read. Setting up the worker fleet and finding its faults took about an hour. A rebuild from
scratch to check a result took 2 to 6 minutes. The estimate made beforehand for the coordinate-free theorem was
one to three weeks; it took about four hours from the start of that work. Every estimate in
the project was too high by a factor of ten or more. These estimates were made beforehand by
the supervising agent; they show that its estimates were poor, not that the method is fast
compared with anything measured.

**What went wrong.**
- A small test run before the first real run found three set-up faults that would have cost
  each of ten workers twenty minutes.
- In run 1, three files imported all of mathlib; a full rebuild rose from under 2 minutes to
  7 minutes 35 seconds until the imports were trimmed.
- The route on paper was changed in four runs. In run 2 the team replaced one step by a simpler
  one and found that two assumptions (Killing's equation and positivity) are not needed. In
  run 3 the route was wrong in one place (the shape lemma, Section 5); a worker found and fixed
  it. In run 6 the team replaced the singular ODE by `product_form`. In run 7 the lead dropped
  the route's ODE steps for the argument through curvature invariants (Section 5).
- In run 4 a side job (porting another project's proof of the connection's existence) was
  withdrawn at the owner's request, after a worker had already read that proof; nothing of it
  was merged, and run 5 proved the result from the textbook.
- Work done twice. Once, in run 5, a lead gave the same lemma to two workers by mistake. Five
  times, in runs 3, 4 and 6, a lead gave a step to a second worker on purpose, as a hedge
  against a stalled one. In run 7 the lead split six pieces out of files whose owners then
  finished them themselves, so each was proved twice; the second copies were not merged.
- No statement fixed in advance had to be changed, and no team reported a statement false.

**What was changed after a run, and by whom.** No person edited a Lean file. The supervising
agent made small changes before merging after two runs: after run 1 it trimmed three files to
load only the parts of mathlib they used and tidied the eleven files; after run 3 it rewrote
three loosely written steps in one file that gave style warnings. After runs 4 and 7 it changed
no file of the team's (after run 7 it added only the audit lines); for runs 2, 5 and 6 the
record lists no change. Within run 7 the lead changed workers' files twice (a helper declared
in two files, a missing comment).

## 8. What is and is not established

**Established.** Each final theorem has the type that was fixed before its proof, by a check
that is part of every build; the whole development compiles from scratch on a clean machine
(the repository's CI) and uses only Lean's three standard axioms.

**Not established.**
- That the definitions mean what a relativist means. Supported by Section 6; not confirmed by a
  human expert.
- That the roughly 1,500 intermediate lemmas (all theorems but the 54 fixed statements) say
  what their comments say. They were read by nobody but their authors. This does not affect the
  final theorems.
- Anything beyond the stated hypotheses: the metric is C^∞ (the textbook theorem needs C²);
  there is no cosmological constant and no charge; symmetry is assumed as three Killing fields,
  not as a group action; manifolds live in universe 0. The local theorems give a chart around
  each point, and those charts' images avoid the poles of the angular coordinates, although no
  point of the manifold is excluded; the global theorem writes the sphere in ℝ³ and avoids no
  pole, but it needs a simply connected region.
- That the textbook's assumption gives ours. Hawking and Ellis, Wald and O'Neill assume an
  isometric action of SO(3) with two-dimensional spacelike orbits. Such an action yields three
  fields as in `IsRoundOn`, so the theorem here is at least as strong; but that step is an
  argument on paper and is not proved in Lean. Two details of it: with mathlib's bracket
  [X, Y] = XY − YX, the fields of a left action satisfy [X₁, X₂] = −X₃, so one takes their
  negatives or an odd reordering (the project's own rotation fields are ordered (y, x, z) for
  this reason); and two-dimensional orbits exclude fixed points, such as the centre of Minkowski
  space, which the textbooks allow outside the region considered.
- A classification of all maximal or inextendible spherically symmetric vacuum space-times.
  The global theorem proved here maps every simply connected one into a model space-time; the
  classification is stated but not proved (Section 4).
- What Section 9 leaves open: `lake check --paranoid` over the whole project ran on the author's
  PC, in a Linux container, not on a second machine or in public CI (`lake comparator` now runs
  in public CI); `nanoda` has not checked the whole export; and `connectionUnique`, one of the
  fixed statements, cannot be put to `lake comparator` (item 3 of Section 9).

## 9. Reproducibility

- Repository: `github.com/flujo-app/gravity-in-lean`, public since 24 November 2026. The
  numbers in this draft refer to commit `3b816ea` (pull request 55), tagged `paper-1-numbers`.
- Lean 4.36.0, mathlib v4.36.0 (pinned). To check: `lake exe cache get`, then `lake build`.
  A full rebuild of the project (not of mathlib) takes 2 to 6 minutes on the PC described.
- The build ends with lines of the form "all 2605 declarations under GravityInLean checked:
  none rests on more than [propext, Classical.choice, Quot.sound]" (`Audit.lean`).
- CI: the workflow "Check the proofs" runs the same build on a clean machine on every push.
- The briefs given to the teams, the scripts that ran them, and each team's own record
  (`STATUS.md` in `Flows/`, `Turns/`, `Join/`, `BothWays/`, `Checks/`, `Rim/`, `Global/`; run 5's
  record in `Checks/` also covers `OneMass/` and `Connection/`) are in the repository.
- The Xena blog (12 November 2026) asks four questions of a Lean proof written by AI: does the
  Lean statement match the informal statement; does the code compile; does it prove the theorem
  as stated; does it exploit a bug in Lean's kernel. What was done for each, at commit `3b816ea`
  with the tools that ship with Lean 4.36.0:
  1. *The statement.* Each Lean excerpt in this paper was compared with the source by a script;
     they agree up to line breaks, and the field comments of `IsRoundOn` are left out.
     Whether the definitions say what the textbooks mean was checked by three AI reviewers
     (Section 6), not yet by a person who works in gravity.
  2. *It compiles*, on a clean machine (CI) and from scratch on the PC described.
  3. *It proves the theorem as stated.* Each final statement is a definition (in
     `GravityInLean/Goals/` and `Curved/Goal.lean`), and `Audit.lean` holds
     `example : Statement := theorem` for each, checked by every build together with the axioms
     of all 2,605 declarations. Lean's own tool for this question, `lake comparator`, gives the
     same answer from outside the build. Its question, `comparator/Challenge.lean`, states each
     result under its full name with a hole (`sorry`) in place of the proof, and imports only
     the statement files; `comparator.json` names the results, the three permitted axioms, and
     `Audit` as the answer. The question sits in a library of its own, so `lake build` and the
     audit never see its holes. `lake comparator --paranoid` builds question and answer inside
     Lake's sandbox on Linux (described in item 4) and accepts only if each named result has
     exactly the question's statement, every definition those statements use is the same on
     both sides, no axiom beyond the three is used, and all six checkers of item 4 accept the
     answer's export. It ran twice.
     - *Sixteen headline results, on the PC described,* at commit `73816cc` (`3b816ea` plus the
       question): accepted ("Your solution is okay!", in 9 minutes; export 546 MB, as in item 4
       (a)).
     - *Every statement the audit checks, on GitHub's machine.* The question is now written from
       the audit's `example : Statement := theorem` lines by `scripts/comparator/make_challenge.py`,
       which also fails the workflow when the question is out of date. It holds 57 statements:
       the 54 of this paper and three proved since. One more fixed statement cannot be asked:
       that of `connectionUnique`, whose own type is its statement. The statement files already
       import its proof, so the question cannot declare its name; the build checks its type and
       the audit its axioms. The workflow "Compare statements" ran `lake comparator --paranoid` at
       commit `e30d888` on a standard Linux machine of GitHub (bubblewrap installed, Ubuntu's
       limit on unprivileged namespaces lifted): accepted, in 12.5 minutes; all six checkers
       accepted the export, about 56,000 declarations. The log is public (workflow run
       45483949294). Between `3b816ea` and `e30d888` no Lean file of this paper's proofs
       changed; files were only added, and lines added to the audit.

     To see that the tool is not a rubber stamp, the question was changed by hand twice. Once
     `oneMass` was given the statement of `connectionExists`, and once the failure test
     `cylNotEmpty` was given the statement of `cylNotUsable`: each time the comparator rejected
     it ("statement do not match").
  4. *Lean's kernel.* Three re-checks outside the build:
     - `leanchecker` (Lean's built-in successor of `lean4checker`) re-checked the project's
       200 modules (`Audit` included) one by one against their imports, in 101 minutes: 199
       passed. On one, `GravityInLean.OneMass` (145 lines from the first step: Schwarzschild's
       functions make the three curvature formulas vanish), the checker crashed twice, after
       about three minutes and 15 GB of memory, without giving a verdict. The declarations of
       that file passed every checker below, Lean's own kernel included.
     - `lake check --paranoid` runs an export through Lean's kernel and the five other
       checkers bundled with the toolchain: `leanchecker-paranoid`, `lean4lean`, `nanoda`,
       `con-leche` and `con-ron`. We exported with `leanexport` (lean4export 3.1.0) (a) the
       sixteen headline theorems and everything they depend on, mathlib included (546 MB,
       58,081 declarations), and (b) the twelve declarations of `GravityInLean.OneMass` with
       everything they depend on (81 MB, 18,166 declarations). All six accepted both exports,
       in about eight minutes and one minute, and both rest only on `propext`,
       `Classical.choice` and `Quot.sound`. `nanoda` 0.4.17 was also run on its own over both
       exports, with any other axiom counted as an error: no errors.
     - *Inside Lake's sandbox, over the whole project.* Lake's sandbox (`bwrap`) runs only on
       Linux, and this PC runs Windows, so the two exports above were made, and checked,
       outside it, with `--inadvisably-no-sandbox`, a run Lake itself labels "not
       trustworthy": code that misbehaved while being built or exported could in principle
       have changed what was checked. We repeated the check inside the sandbox, in a Linux
       container (Debian 12, bubblewrap 0.8.0, Lean 4.36.0 from elan, run as an ordinary
       user) under Docker on the same PC; the recipe is `scripts/sandbox-check/`. Inside the
       sandbox the code has no network, can write nothing but the build folder `.lake`, and
       cannot see the home folders. From a fresh copy of tag `paper-1-numbers`, after
       mathlib's prebuilt files were fetched (`lake exe cache get`, the one step outside the
       sandbox; the project itself was not built outside it), `lake check --paranoid` built
       the project inside the sandbox (the audit line above came out again), exported every
       declaration in scope, Lean's own library and the parts of mathlib the project imports
       included (3.1 GB, 464,847 declarations), and gave the export to all six checkers.
       Five accepted all of it: `leanchecker-paranoid` (16 minutes), `lean4lean` (18),
       `con-leche` (6), `con-ron` (12) and Lean's own kernel (12). `nanoda` 0.4.17 gave no
       verdict: after 43 minutes, using all 24 GB of memory the container had plus about
       30 GB of swap, one of its worker threads overflowed its stack and the program aborted.
       Lake counts any non-zero exit as a rejection, so the run ended with "error: nanoda
       exited with 134" after 2 hours 21 minutes (27 of them spent writing `nanoda`'s crash
       dump). The stack size is fixed inside `nanoda`; we found no way to raise it from
       outside. Because Lake stops at that error before it lists the axioms, we ran
       `lake check --from-export` (Lean's own kernel only) on the same export, made inside
       the sandbox: the kernel accepted it again, and Lake reported "Uses axioms: propext,
       Quot.sound, Classical.choice". Finally `nanoda`, under the same sandbox settings that
       Lake uses for its checkers, was given an export of the project's own 2,605
       declarations with everything they depend on (576 MB): "Checked 58865 declarations with
       no typechecker errors", in 24 seconds. So `nanoda` accepts all that the project uses;
       where in the rest of the environment it stumbled was not found. Without `nanoda`, the
       peak memory of the run was 19 GB.
     - *What weakens these runs.* Docker's own filter on system calls forbids the namespaces
       the sandbox needs, so the container ran with `--security-opt seccomp=unconfined`. That
       was the only flag: no added capabilities, not privileged, not run as root. It weakens
       the wall between the container and the PC, not the sandbox inside the container. The
       container ran on the PC described, not on a second machine (only the comparator of item 3
       has also run on another machine, GitHub's, with no container). mathlib's prebuilt files
       were fetched outside the sandbox, but each of their declarations in the export was
       checked again by the checkers. And `nanoda` has not checked the whole export.

## 10. Use of AI

All Lean code, all proofs, the definitions, the statements, the second readings, the reviews
and the first draft of this text were written by AI systems: Claude Fable 5.2 (supervisor and
workers) and Claude Opus 5.5 (second readers, the review in `REVIEW.md`, and the literature
research), through Claude Code and the FACTORY framework. No Lean proof in the repository was
written or edited by hand.

The human author, Mario Andreschak, chose the goal and its order of priority and decided the
working rules (one build at a time; no porting of another project's recent proof; when to make
the repository public). The human author has read the manuscript in full but is not a
specialist in general relativity, differential geometry or interactive theorem proving, and
has not independently verified the mathematical arguments or the formal proofs; no claim of
personal verification is made. The human author's approval of the manuscript rests on the
machine verification described in Section 9 and on the AI reviews described in Section 6, not
on a personal assessment of its mathematical content. Readers should weigh the results
accordingly: the correctness of the proofs rests on Lean's kernel and the independent checkers,
whereas the agreement between the formal statements and their description in this text has so
far been checked only by AI reviewers (Section 8).

## References

*Bibliographic details are to be verified against the sources before submission.*

- G. D. Birkhoff, *Relativity and Modern Physics*, Harvard University Press, 1923.
- J. T. Jebsen, "Über die allgemeinen kugelsymmetrischen Lösungen der Einsteinschen
  Gravitationsgleichungen im Vakuum", *Arkiv för Matematik, Astronomi och Fysik* 15, 1921.
- S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Cambridge
  University Press, 1973, Appendix B.
- M. D. Kruskal, "Maximal extension of Schwarzschild metric", *Physical Review* 119, 1960.
- G. Szekeres, "On the singularities of a Riemannian manifold", *Publicationes Mathematicae
  Debrecen* 7, 1960.
- B. O'Neill, *Semi-Riemannian Geometry*, Academic Press, 1983.
- R. M. Wald, *General Relativity*, University of Chicago Press, 1984.
- H.-J. Schmidt, "A new proof of Birkhoff's theorem", *Gravitation & Cosmology* 3, 1997,
  arXiv:gr-qc/9709071.
- X. An and W. W. Y. Wong, "Warped product space-times", *Classical and Quantum Gravity* 35,
  2018, arXiv:1707.01483.
- P. T. Chruściel, *Geometry of Black Holes*, lecture notes.
- K. Schleich and D. M. Witt, "A simple proof of Birkhoff's theorem for cosmological constant",
  *Journal of Mathematical Physics* 51, 2010, arXiv:0908.4110.
- K. Schleich and D. M. Witt, "What does Birkhoff's theorem really tell us?", arXiv:0910.5194.
- M. Stannett and I. Németi, "Using Isabelle/HOL to verify first-order relativity theory",
  *Journal of Automated Reasoning*, 2014, arXiv:1211.6468.
- R. Schmoetten, J. E. Palmer and J. D. Fleuriot, "Towards formalising Schutz' axioms for
  Minkowski spacetime in Isabelle/HOL", *Journal of Automated Reasoning*, 2022.
- Archive of Formal Proofs, entry `No_FTL_observers_Gen_Rel`, 2023.
- The mathlib Community, "The Lean mathematical library", CPP 2020.
- L. de Moura and S. Ullrich, "The Lean 4 theorem prover and programming language", CADE 2021.
- Xena Project blog, "…and the proof is checked in Lean", 12 November 2026,
  xenaproject.wordpress.com.
- Repositories named in Section 2, with the dates on which they were read: see `SURVEY.md`.
