# Birkhoff's theorem without coordinates, machine-checked in Lean 4, and how teams of AI workers built it

**[author]**

*Draft of 24 November 2026. Not submitted. Every number below is a measurement recorded in
`PLAN.md` or in the run logs of the repository; nothing is estimated unless it says so.*

## Abstract

We describe a formalisation in Lean 4 with mathlib of Birkhoff's theorem in a form that does not
start from coordinates: a smooth Lorentzian metric on a 4-manifold that is Ricci-flat and
carries three Killing fields with the brackets of so(3), two-dimensional spacelike orbits, is
locally Schwarzschild. The formal statement holds at every point of the region, including the
horizon and the bifurcation sphere, where the target is the Kruskal–Szekeres form; it gives one
mass on each connected region; and it comes with its converse, as one "if and only if". The
Levi-Civita connection of a metric of arbitrary signature is shown to exist and to be unique,
so "Ricci-flat" carries no hidden assumption. The definitions were reviewed against the
textbooks and are pinned by 25 tests in which a definition must fail. The development has
1,151 theorems and was produced within about a day. The proofs were written by teams of ten AI
workers in six runs of 11 to 29 minutes each. The statements were fixed in advance, read by an
independent second reader, and checked afterwards by a rebuild from scratch and an audit of
axioms. We report what this cost, where the time went, and what is not checked. To our
knowledge no earlier machine-checked Birkhoff theorem starts from symmetry assumptions without
coordinates; the mathematics itself is classical.

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
4. **The converse, and the two directions as one statement** (`schwarzschildExactlyWhen`,
   `birkhoffExactlyWhenInCoordinates`).
5. **Existence and uniqueness of the Levi-Civita connection** for a non-degenerate metric of any
   signature on a manifold (`connectionExists`, `connectionUnique`).
6. **Two results the above needed that mathlib v4.36.0 does not have:** smooth dependence of a
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
Schmidt (1997, arXiv:gr-qc/9709071). For horizon points with non-vanishing gradient, an explicit
Eddington–Finkelstein form is given by An and Wong (2018, arXiv:1707.01483, Theorem 3.2) under
a global warped-product assumption. For the bifurcation sphere, where the gradient vanishes, we
did not find a complete written proof in the sources we read (Hawking and Ellis treat it in one
sentence; see `review/global-birkhoff.md` in the repository for what was read and how). We say
"not found written down"; we do not say the argument is new.

**In proof assistants.** All of the following were found by searches in November 2026 and are
documented with dates in `SURVEY.md` and `TARGETS.md`.

- *ProjectAinos* (`x-oai/ProjectAinos`) proved Birkhoff's theorem in Lean 4 from a fixed
  diagonal form −A(t,r)dt² + B(t,r)dr² + r²dΩ² on 19 November 2026, four days before the
  coordinate version in this repository. The coordinate result here is therefore not a first.
- *grlab* (`BrandonMYates/grlab`, August 2026) has the last step of the static case.
- *Lightlike* (`LightLikeProject/lightlike`) builds orbit charts from a Killing algebra and uses
  them for homogeneous and isotropic 3-metrics (the cosmological case), not for so(3) with
  two-dimensional orbits.
- *TauCeti* (`TauCetiProject/TauCeti`) proved, earlier than this repository and independently,
  that a non-degenerate metric of any signature has a Levi-Civita connection. The proof here was
  made from the textbook (Koszul's formula; O'Neill 1983, Chapter 3) by workers instructed not to
  read any other project's proof, and the run's log shows no access to the network.
- Schwarzschild's solution itself had been verified in Lean at least twice before.

**To our knowledge**, no machine-checked Birkhoff theorem in any proof assistant starts from
symmetry assumptions without coordinates, or covers the horizon. This is a statement about what
we found, on the dates given, and must be re-checked on the day of submission.

## 3. Definitions

The base is mathlib's manifolds, tangent bundle, Lie bracket of vector fields (`mlieBracket`)
and covariant derivatives on vector bundles (`IsCovariantDerivativeOn`). On top of these the
project defines, in `GravityInLean/Curved/Basic.lean` and `Curved/Goal.lean`:

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

Here `roundG (schwA m) (schwB m)` is the Schwarzschild metric in (t, r, θ, φ), and `outside m`,
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
| `TurnsCoordinatesStatement` | three fields on an open subset of ℝ⁴ with so(3) brackets and rank 2 are, in suitable coordinates and after one fixed rotation, the standard rotation fields | `turnsCoordinates` |

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

A smooth Ω with Ω·Ω_uv = Ω_u·Ω_v and Ω_uv ≠ 0 is a product of a function of u and a function of
v on the whole box, across its zeros. Applied to Ω = (r/2m − 1)e^{r/2m}, the two factors are the
Kruskal null coordinates. The same argument covers points off the horizon, so for positive mass
no case distinction on the gradient is needed. For m ≤ 0 the gradient is never null and the
first theorem applies (24 files, about 4,700 lines).

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

**Measurements.** Times run from "all ten agents ready" to "whole project builds with the
proof".

| Run | Job | Files | Lines | Theorems | Minutes | Lean runs (failed) |
|---|---|---|---|---|---|---|
| 1 | `smoothFlow` | 11 | 980 | 24 | 14 | 20 (1) |
| 2 | `turnsCoordinates` | 20 | 2,070 | 62 | 17 | 52 (9) |
| 3 | `birkhoffNoCoordinates` | 24 | 4,500 | 168 | 21 | 79 (17) |
| 4 | both directions (6 statements) | 14 | 2,000 | 83 | 11 | 46 (10) |
| 5 | 25 failure tests, one mass, the connection | 29 | 3,800 | 134 | 14 | 80 (10) |
| 6 | every point, horizon included (11 statements) | 24 | 4,700 | 155 | 29 | 72 (13) |

Together: about 18,000 lines of checked proof in 106 minutes of team time. The cost was
measured as the change of the subscription's weekly usage meter over each run; these are upper
bounds, because other sessions ran at the same time: between 2 and 11 percentage points per
run (details in `PLAN.md`).

**Where the time went.** Not into proving. The definitions and the first goal took one
supervising agent 57 minutes to a first green build and 80 minutes including the second
reading; each later set of statements took about 20 minutes to write and 12 to 13 minutes to
read. Setting up the worker fleet and finding its faults took about an hour. A rebuild from
scratch to check a result took 2 to 6 minutes. The estimate made beforehand for the coordinate-free theorem was
one to three weeks; it took about four hours from the start of that work. Every estimate in
the project was too high by a factor of ten or more.

**What went wrong.**
- A small test run before the first real run found three set-up faults that would have cost
  each of ten workers twenty minutes.
- In run 1, three files imported all of mathlib; a full rebuild rose from under 2 minutes to
  7 minutes 35 seconds until the imports were trimmed.
- In run 3 the paper route was wrong in one place (the shape lemma, Section 5); a worker found
  and fixed it. In run 6 the team replaced a step of the route by a better one.
- In run 4 a side job (porting another project's proof of the connection's existence) was
  withdrawn at the owner's request, after a worker had already read that proof; nothing of it
  was merged, and run 5 proved the result from the textbook.
- Twice a lead gave the same lemma to two workers.
- No statement fixed in advance had to be changed, and no team reported a statement false.

## 8. What is and is not established

**Established.** Each final theorem has the type that was fixed before its proof, by a check
that is part of every build; the whole development compiles from scratch on a clean machine
(the repository's CI) and uses only Lean's three standard axioms.

**Not established.**
- That the definitions mean what a relativist means. Supported by Section 6; not confirmed by a
  human expert.
- That the roughly 630 intermediate lemmas say what their comments say. They were read by
  nobody but their authors. This does not affect the final theorems.
- Anything beyond the stated hypotheses: the metric is C^∞ (the textbook theorem needs C²);
  there is no cosmological constant and no charge; symmetry is assumed as three Killing fields,
  not as a group action; manifolds live in universe 0; the theorems are local (a chart around
  each point), and the charts' images avoid the poles of the angular coordinates, although no
  point of the manifold is excluded.
- A global statement. [If the global theorem of issue 39, second step, is proved before
  submission, it becomes a section here; otherwise it is future work.]
- The independent checks 3 and 4 of Section 9.

## 9. Reproducibility

- Repository: `github.com/flujo-app/gravity-in-lean`, public since 24 November 2026. The
  numbers in this draft refer to commit `3f4e818` (pull request 49).
- Lean 4.36.0, mathlib v4.36.0 (pinned). To check: `lake exe cache get`, then `lake build`.
  A full rebuild of the project (not of mathlib) takes 2 to 6 minutes on the PC described.
- The build ends with lines of the form "all 2004 declarations under GravityInLean checked:
  none rests on more than [propext, Classical.choice, Quot.sound]" (`Audit.lean`).
- CI: the workflow "Check the proofs" runs the same build on a clean machine on every push.
- The briefs given to the teams, the scripts that ran them, and each team's own record
  (`STATUS.md` in `Flows/`, `Turns/`, `Join/`, `BothWays/`, `Checks/`, `Rim/`) are in the
  repository.
- Of the four checks proposed for AI-written formal proofs (the statement matches the paper;
  it builds; an external kernel re-check such as `lean4checker`; an independent checker), the
  first two are done. **The last two are open.**

## 10. Use of AI

All Lean code, all proofs, the definitions, the statements, the second readings, the reviews
and the first draft of this text were written by AI systems: Claude Fable 5.2 (supervisor and
workers) and Claude Opus 5.5 (second readers), through Claude Code and the FACTORY framework.
The human author chose the goal and its order of priority, decided the working rules (one build
at a time; no porting of another project's recent proof; when to make the repository public),
[the author describes here what he read, checked and decided, and confirms that he stands
behind the claims]. No Lean proof in the repository was written or edited by hand.

## References

*Bibliographic details are to be verified against the sources before submission.*

- G. D. Birkhoff, *Relativity and Modern Physics*, Harvard University Press, 1923.
- J. T. Jebsen, "Über die allgemeinen kugelsymmetrischen Lösungen der Einsteinschen
  Gravitationsgleichungen im Vakuum", *Arkiv för Matematik, Astronomi och Fysik* 15, 1921.
- S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Cambridge
  University Press, 1973, Appendix B.
- M. D. Kruskal, "Maximal extension of Schwarzschild metric", *Physical Review* 119, 1960.
- B. O'Neill, *Semi-Riemannian Geometry*, Academic Press, 1983.
- H.-J. Schmidt, "A new proof of Birkhoff's theorem", *Gravitation & Cosmology* 3, 1997,
  arXiv:gr-qc/9709071.
- X. An and W. W. Y. Wong, "Warped product space-times", *Classical and Quantum Gravity* 35,
  2018, arXiv:1707.01483.
- P. T. Chruściel, *Geometry of Black Holes*, lecture notes.
- K. Schleich and D. M. Witt, "What does Birkhoff's theorem really tell us?", arXiv:0910.5194.
- The mathlib Community, "The Lean mathematical library", CPP 2020.
- L. de Moura and S. Ullrich, "The Lean 4 theorem prover and programming language", CADE 2021.
- Repositories named in Section 2, with the dates on which they were read: see `SURVEY.md`.
