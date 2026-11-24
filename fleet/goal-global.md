# Goal for the team: Birkhoff's theorem for a whole space-time

You are a team of ten in one container: the lead `m0-a0` and nine workers `m0-a1` to `m0-a9`.
You work in the repository `flujo-app/gravity-in-lean`: Einstein's gravity, checked by the proof
checker Lean 4 (version 4.36.0, with its standard library mathlib v4.36.0). Each of you has a
copy of the repository of your own (your work folder). All copies share one store of branches,
so a branch that one of you commits is at once visible to the others.

So far every theorem of the project speaks about the neighbourhood of one point. This job is
about a whole space-time: a round, empty space-time without holes can be laid onto Kruskal's
space-time (or flat space-time, or Schwarzschild's of negative mass) by a map that keeps every
length, and that map is unique up to a symmetry. Read `README.md`, then
`GravityInLean/Goals/Global.lean` (the statements, with the reasons for each word) and
`GravityInLean/Global/Checks.lean` (checks that are already proved, and tools you will want).
Earlier teams' records are the `STATUS.md` files.

## What to prove

The seven statements of `GravityInLean/Goals/Global.lean`. For each `def Name : Prop` there, a
theorem of that type with the same name, first letter small, in the same namespace:

```lean
theorem Curved.kruskalMapOfSchwarzschild : Curved.KruskalMapOfSchwarzschild
theorem Curved.globalDeSitterNoMap : Curved.GlobalDeSitterNoMap
theorem Curved.globalUniqueNeedsOnePiece : Curved.GlobalUniqueNeedsOnePiece
theorem Curved.globalBirkhoffConverse : Curved.GlobalBirkhoffConverse
theorem Curved.globalMassUnique : Curved.GlobalMassUnique
theorem Curved.globalBirkhoffUnique : Curved.GlobalBirkhoffUnique
theorem Curved.globalBirkhoff : Curved.GlobalBirkhoff
```

`GlobalBirkhoff` needs the theorem at every point, `Curved.birkhoffAtEveryPointOneMass`
(`Goals/EveryPoint.lean`). If it is in the repository when you start, use it. If it is not,
prove `Curved.BirkhoffAtEveryPointOneMass → Curved.GlobalBirkhoff` under the name
`Curved.globalBirkhoff_of_everyPoint`, and say so on the board; that is a full result for this
run.

## A route, as a suggestion

Worked out on paper by the supervisor; every statement was judged true as written by a second
reader. **Not checked in Lean.** Check each step before you build on it. Parts 1, 2 and 3 can
start at once and do not depend on each other; part 4 needs part 3, part 5 needs parts 3 and 4.

**Part 1. Known answers (two statements). Ready to hand out.**

1. *`KruskalMapOfSchwarzschild`.* Outside the rim, `X² - T² = kruskalF m r`, so
   `kruskalR m (X² - T²) = r` by `KruskalRadiusSpec`; the angle part is `kruskalWrap`'s
   (`fderiv_kruskalWrap`, `kruskalWrap_pullback`). For the `(t, r)` part, sympy gives
   `A · (-dT² + dX²) = -(1 - 2m/r) dt² + (1 - 2m/r)⁻¹ dr²` inside and outside (check it again
   in this project's conventions). Read the tables with `kruskalWhole_apply` and `schw_apply`;
   take derivatives part by part as in `fderiv_sphericalToSpace`.
2. *Charts of Kruskal's whole space-time.* On `sin θ ≠ 0`, `kruskalWrap` is one-to-one on small
   pieces with a smooth inverse onto an open piece of `kruskalSpace` (θ = arccos y₃,
   φ from (y₁, y₂)); near the poles, compose with `kruskalSym 1 R` for a turn `R`
   (`turnToPole`, `IsKruskalMapOn.sym`). So every point of Kruskal's whole space-time has a
   neighbourhood that the table of `Goals/EveryPoint.lean` describes. The same for
   `sphericalToSpace` and `schwSpaceG`.

**Part 2. From a map to the space-time (three statements).**

3. *A map gives charts.* If `D` is a length-keeping map on `s` and `q ∈ s`, then composing `D`
   with the inverse of a chart of step 2 gives a map from a neighbourhood of `q` into
   `kruskalRegion` with one-to-one derivative (`IsKruskalMapOn.mfderiv_injective`), so a chart
   of the curved space (`Join/Atlas.lean`, `exists_chart_of_localDiffeo`) in which `g` is
   Kruskal's table: `IsKruskalNear m g q`.
4. *`GlobalBirkhoffConverse`.* Empty: from step 3, `KruskalIsEmpty` and the pull-back lemmas
   (`BothWays/PullEmpty.lean`, `isEmptyOn_pull`). Round: define the three fields through `D`
   itself, not chart by chart: at `q`, the step that `D` carries to the turn of the sphere at
   `D q` (the turns of the unit sphere are `y ↦ eᵢ × y` in the last three numbers). They are
   Killing fields with the brackets of turns because `D` keeps lengths and brackets. For a mass
   that is zero or negative, the same with the turns of ordinary space; the centre is missed by
   assumption.
5. *`GlobalDeSitterNoMap`.* The first three parts: `isSimplyConnected_shellBox`,
   `deSitter_isSpaceTimeOn`, `round_isRoundOn` (`Checks/DeSitter.lean`). The last two: a map
   would make de Sitter's table empty (step 4), and it is not (`deSitter_not_isEmptyOn_near`).
6. *`GlobalUniqueNeedsOnePiece`.* Two disjoint boxes; `D = kruskalWrap` on both; `D'` the same
   on the first and `kruskalSym 1 R ∘ kruskalWrap` on the second, `R` a turn about the axis by a
   quarter. A single symmetry would have to fix an open piece of the sphere point by point on
   the first box, so be trivial, and then cannot match the second box.

**Part 3. The symmetries are all (one statement): `GlobalBirkhoffUnique`.** This is the heart.

7. *A map is fixed by its value and derivative at one point.* Two length-keeping maps on a
   region in one piece that agree, with their derivatives, at one point agree everywhere. Near
   the point, `f = D' ∘ D⁻¹` (in a chart of step 2) keeps the table, so it keeps the connection
   (`Join/CarryConnection.lean` carries connections along charts), so in coordinates
   `∂² f = Γ(f)(∂f, ∂f) - ∂f · Γ`: along each straight line from the point, `(f, ∂f)` solves a
   first-order ordinary equation with the same start as the map that does nothing; uniqueness
   (mathlib: `ODE_solution_unique`) gives `f = id` near the point. Then: the set where two maps
   agree near the point is open and closed.
8. *The radius is kept.* A map that keeps Kruskal's table keeps its full curvature, so it keeps
   `R_abcd R^abcd = 48 m² / r⁶` (compute the full curvature of `kruskalG` with sympy first; how
   the full curvature changes with coordinates: `riemann_inNewCoords`). For `m ≠ 0` this fixes
   `r`. For flat space-time skip this.
9. *The spheres are kept.* With `r` kept, its second slope (Hessian) is kept. For Kruskal's it
   is `(m / r²) · g` on the `(T, X)` plane and `((r - 2m) / r²) · g` on the sphere: two
   different numbers except at `r = 3m`. So the map keeps the split into `(T, X)` plane and
   sphere wherever `r ≠ 3m`, and everywhere by continuity.
10. *Every allowed start is a symmetry.* Given `D q`, `D' q` with the same `r` and derivatives
    that keep the split, `dr` and the length measure, write down `L` (from where `(T, X)` goes
    and how its plane is turned) and `R` (from where `y` goes and how its plane is turned) with
    `kruskalSym L R` doing the same at `q`. With step 7, `D' = kruskalSym L R ∘ D`.
11. The same for a negative mass (symmetries `schwSym`) and for flat space-time (every start is
    a Lorentz transformation and a shift).

**Part 4. One mass (one statement): `GlobalMassUnique`.** From steps 8 and 9: `r` and the
split are fixed by `g`, so `1 - 2m/r = g(dr, dr)` fixes `m`; flat against curved settles the
rest.

**Part 5. The theorem (one statement): `GlobalBirkhoff`.**

12. *Maps near every point.* From `birkhoffAtEveryPointOneMass`: around every point of `s`, a
    chart in which `g` is Kruskal's table (or Schwarzschild's, mass zero or negative), the same
    mass everywhere. Compose with `kruskalWrap` (or `sphericalToSpace`): a length-keeping map
    on the chart's domain (chain rule, `kruskalWrap_pullback`, `sphericalToSpace_pullback`).
13. *Continue along paths.* By part 3, two maps near a point differ by one symmetry on each
    piece of their common domain. Build the space of germs of length-keeping maps over `s`
    (pairs of a point and a map near it, two pairs the same when the maps agree near the
    point), with the topology in which the germs of one map near nearby points form an open
    set; its projection to `s` is a local homeomorphism with unique path lifting. On a simply
    connected region it has a continuous section: mathlib's lifting theorems in
    `Mathlib/Topology/Homotopy/Lifting.lean` (`IsCoveringMap.existsUnique_continuousMap_lifts`,
    `IsLocalHomeomorph.existsUnique_continuousMap_lifts`). Evaluating the section's germ at its
    own point gives `D`. If the space of germs is heavy, a simpler space works too: pairs of a
    point and a symmetry, glued by the symmetries of part 3.

If a part cannot be finished in this run, a clean statement of each finished link, in its own
file, is the result the next team builds on.

## Rules that are not negotiable

1. **Do not change the statements.** `GravityInLean/Goals/`, `GravityInLean/Curved/` and
   `GravityInLean/Global/Checks.lean` are not to be edited, by anyone. If you come to think
   that a statement is false or cannot be proved as written, say so on the board with your
   argument, and stop work on that statement. Do not prove a weaker statement instead. A report
   "this is false, here is why" is a good result.
2. **Do not change existing files** outside your own new ones. New files go in
   `GravityInLean/Global/`. Only the lead adds them to `GravityInLean.lean`, and only when they
   are finished.
3. **The build is the judge.** A file is finished when it builds without a hole (`sorry`), with
   no new assumption (`axiom`), and with no warnings. Build only through
   `scripts/queued-build.sh` (one Lean build at a time on this machine).
4. **Files in the project's form:** `module`, then `public import` of only what is needed (never
   `import Mathlib`), `@[expose] public section`, a short comment in plain words at the top.
5. **Hand out work early.** The lead wakes every two minutes, a worker only when a message
   arrives: the lead gives every worker a piece in the first minutes, and gives the next piece
   as soon as one is finished.
6. **Write down what you learned** in `GravityInLean/Global/STATUS.md`: what is proved, what is
   not, what failed and why.
