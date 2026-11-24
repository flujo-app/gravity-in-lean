# Global: status of the team's work on Birkhoff's theorem for a whole space-time

Goals: the seven statements of `Goals/Global.lean`. Times are UTC on 24 November 2026, read
from the queue's log and the branch commits. Lead: `m0-a0`, first step at about 03:11 (the
set-up script ran until 03:14). Working branch: `global`; each item has a branch
`global-<item>` (board claim `task:global-<item>`).

## Result (04:04)

**All seven targets are proved, and none was found false as written.** The whole project builds
with them through the queue (`scripts/queued-build.sh`: `Build completed successfully
(7821 jobs)`, first at 03:57:17, again after the last form fix at 04:03), `Audit.lean` included: "all 2605 declarations under GravityInLean
checked: none rests on more than [propext, Classical.choice, Quot.sound]" (2004 before). That
run printed no warning. All 40 new Lean files are imported by `GravityInLean.lean`. A scratch
check `example : <statement> := <theorem>` passes for each of the seven targets, and
`#print axioms` names the same three for each. `GravityInLean/Goals/`, `GravityInLean/Curved/`,
`GravityInLean/Global/Checks.lean` and `Audit.lean` are unchanged; the only existing file
changed is `GravityInLean.lean` (40 import lines). No new file has a `sorry` or an `axiom`.

| target | state | file |
|---|---|---|
| `kruskalMapOfSchwarzschild` | proved | `DeSitterNoMap.lean` (halves: `KSOutside.lean`, `KSInside.lean`) |
| `globalDeSitterNoMap` | proved | `DeSitterNoMap.lean` |
| `globalUniqueNeedsOnePiece` | proved | `TwoPieces.lean` |
| `globalBirkhoffConverse` | proved | `Converse.lean` (from `ConverseEmpty.lean`, `ConverseRoundKruskal.lean`, `ConverseRoundSchw.lean`) |
| `globalMassUnique` | proved | `MassUnique.lean` |
| `globalBirkhoffUnique` | proved | `Unique.lean` (from `UniqueKruskal.lean`, `UniqueSchw.lean`, `UniqueFlat.lean`) |
| `globalBirkhoff` | proved | `Glue.lean` (from `Develop.lean`, `LocalMaps.lean` and the three uniqueness files) |

Honest numbers:

* Lead's first step about 03:11. First three items given out at 03:13, six more at 03:16 to
  03:17; from then on no worker waited for more than a few minutes until 03:47.
* Whole-project builds: 03:36 (three targets), 03:53 (four targets), 03:57 (all seven).
  From the lead's first step to the last whole build: about 46 minutes.
* Queue runs from 03:11 to 03:59: 132, of them 19 failed (one by the lead: the name clash
  below). Longest wait in the queue: 144 s (behind a whole-project build).
* 9385 lines of Lean in 40 files, 393 named results and definitions.
* No statement of `Goals/Global.lean` had to be read differently, and none was reported false.
  Of the lead's own lemma statements one was changed before it was given out: the one-mass
  statements about tables first asked for the map near one point; a worker pointed out that
  "smooth of every order at a point" does not hand smoothness to the points nearby, so they
  now ask for the map on an open set.
* **The route was changed in one place, by the lead, before Part 3 was given out: step 7 (a map
  is fixed by its value and derivative at one point, by an ordinary differential equation along
  lines) and step 10 (every allowed start is a symmetry) are not done at all.** See below. No
  step of the supervisor's route was found false; these two were not tried.
* Work done twice. To keep nine workers busy near the end the lead gave out pieces of files
  that their owners then finished themselves: `KruskalLocal.lean` (the same statement was
  already proved inside `UniqueKruskal.lean`), `SchwSplit.lean`, `SchwTime.lean`,
  `SchwRadius.lean` (all three proved inside `SchwKept.lean`), `MassMixed.lean` (proved inside
  `MassUnique.lean`), `HessSchw.lean` (proved inside `SchwScalars.lean`). All six built on
  their branches (`global-kruskal-local`, `global-schw-split`, `global-schw-time`,
  `global-schw-radius`, `global-mass-mixed`, `global-hess-kruskal`); none is on `global`.
  `MassCharts.lean` is on `global` and builds, but `MassUnique.lean` does not use it.
* The lead changed workers' files twice: one helper declared in two files
  (`mulVec_three`, removed from `UniqueKruskal.lean`), and one missing comment
  (`SphereRigid.lean`).
* A check of the form of all new files was run by script by one worker (copyright, `module`,
  imports, header comment, `@[expose] public section`, a comment before every named result,
  no line over 100, no name declared in two files, no worker id or outside folder in files or
  commit messages). Findings: one missing comment (fixed), two instances without comment in
  `Develop.lean` (fixed), and one `simp ... at` followed by `linarith` in
  `ConverseRoundKruskal.lean` (given back to its author and fixed, see the last row of the
  table). Not checked: whether every `public import` is needed.
* Not done: a second reading of each proof text, or a check by a second person that each
  comment says what its Lean statement says. The build and the audit are the judge of the
  proofs. `Audit.lean` was not touched; it does not hold a line per target that checks the
  theorem against its statement (the scratch check above did that once, outside the build).
* The commits of this run carry the e-mail address that the container's git was set up with;
  the brief asked only for the name `flujo-app`. Nobody changed it.

## The route chosen

**Parts 1 and 2** as the supervisor's route. Charts of the model space-times:
`SphereSection.lean` (angles near a direction), `KruskalSection.lean`, `SchwSection.lean`
(wrapping can be undone near every point), `KruskalChart.lean`, `SchwChart.lean` (a
length-keeping map is, near each point, wrapping after a chart of the curved space, up to a
turn or mirror; so `IsKruskalNear`, `IsSchwarzschildWith`), `SchwSym.lean` (the symmetries of
Schwarzschild's whole space-time keep lengths). The converse: "empty" through these charts and
one connection for the region (`ConverseEmpty.lean`); "round" with three fields defined through
the map itself (`RoundTools.lean`, `ConverseRoundKruskal.lean`, `ConverseRoundSchw.lean`).

**Part 3, changed.** No ordinary differential equation is used. Everything is said for a map `f`
of coordinate space that carries one table to another (`CarriesTableAt`, `Kretschmann.lean`);
the change of charts between two length-keeping maps is such a map (`ChartChange.lean`).

1. The curvature scalar (the full curvature contracted with itself, `kretschmann`) is carried
   (`KretschmannKept.lean`); for the general round shape it is computed once (`RiemannGen.lean`,
   `KretschmannGen.lean`), and for Kruskal's and Schwarzschild's tables it is `-48 m² / r⁶` in
   this project's signs (`KretschmannKruskal.lean`, `SchwScalars.lean`). So `f` keeps the
   radius; for Kruskal's it keeps `X² - T²`.
2. The squared slope length and the second slope of a function are carried (`TableHess.lean`,
   `HessKept.lean`). The second slope of the radius is `(m / r²) g` on the `(T, X)` plane and
   `((r - 2m) / r²) g` on the sphere (`HessKruskal.lean`, `SchwScalars.lean`), so `f` keeps the
   split, at `r = 3m` by continuity (`KruskalKept.lean`, `SchwKept.lean`).
3. So `f` is a map of `(T, X)` times a map of the angles. The first keeps `-dT² + dX²`
   (Kruskal's factor depends on the kept radius only), so it is a matrix and a shift: a map
   that keeps a constant form has second derivative zero (`FlatRigid.lean`); the shift is zero
   because `X² - T²` is kept (`KruskalPlane.lean`). For the negative mass: time is `±t + c`
   (`SchwKept.lean`).
4. The second keeps the lengths of the unit sphere. With a time and a distance put next to it,
   it is a length-keeping map of flat space-time written in distance and angles, so a Lorentz
   transformation by the flat case; it fixes time and distance, so it is a turn or mirror
   (`SphereRigid.lean`).
5. So two length-keeping maps differ by a symmetry near every point; the symmetry is fixed by
   what it does near one point; a region in one piece has one symmetry
   (`UniqueKruskal.lean`, `SchwLocal.lean`, `UniqueSchw.lean`).

The flat case (`UniqueFlat.lean`) is direct: a length-keeping map into flat space-time is a
chart, and the change of charts keeps a constant form.

**Part 4** (`MassUnique.lean`): the curvature scalar gives `m² r'⁶ = m'² r⁶`, so the two radii
differ by a constant factor; the squared slope lengths `1 - 2m/r` then force the factor to be
one when the masses have the same sign, and cannot both hold on an open set when they have
opposite signs.

**Part 5.** `Develop.lean` is an abstract statement of pure topology: maps that exist near
every point, differ by one of a set of symmetries on connected open sets, and whose symmetry is
fixed by an open piece, can be glued to one map on a simply connected, locally path connected
space. Proved with the simpler space of step 13: pairs of a point and a symmetry, glued by the
symmetries, as a fibre bundle core of the library with a discrete fibre; its projection is a
covering map and the library's lifting theorem gives the section. `LocalMaps.lean`: the charts
of Birkhoff's theorem at every point give maps near every point. `Glue.lean` puts in the three
uniqueness statements.

## The pieces

| item (`task:global-…`) | file | who | given | built | note |
|---|---|---|---|---|---|
| `ks-outside` | `KSOutside.lean` | m0-a1 | 03:13 | 03:18 | merged |
| `ks-inside` | `KSInside.lean` | m0-a2 | 03:13 | 03:16 | merged |
| `two-pieces` | `TwoPieces.lean` | m0-a4 | 03:13 | 03:17 | merged; target |
| `sphere-section` | `SphereSection.lean` | m0-a3 | 03:16 | 03:20 | merged |
| `kruskal-section` | `KruskalSection.lean` | m0-a5 | 03:16 | 03:18 | merged |
| `schw-section` | `SchwSection.lean` | m0-a6 | 03:16 | 03:18 | merged |
| `schw-sym` | `SchwSym.lean` | m0-a7 | 03:16 | 03:19 | merged |
| `kruskal-chart` | `KruskalChart.lean` | m0-a8 | 03:17 | 03:21 | merged |
| `schw-chart` | `SchwChart.lean` | m0-a9 | 03:17 | 03:23 | merged |
| `desitter` | `DeSitterNoMap.lean` | m0-a1 | 03:24 | 03:27 | merged; two targets |
| `converse-empty` | `ConverseEmpty.lean` | m0-a2 | 03:24 | 03:28 | merged |
| `converse-round-kruskal` | `RoundTools.lean`, `ConverseRoundKruskal.lean` | m0-a4 | 03:24 | 03:44 | merged |
| `converse-round-schw` | `ConverseRoundSchw.lean` | m0-a5 | 03:24 | 03:39 | merged |
| `unique-flat` | `FlatRigid.lean`, `UniqueFlat.lean` | m0-a3 | 03:24 | 03:36 | merged |
| `develop` | `Develop.lean` | m0-a6 | 03:24 | 03:32 | merged |
| `kretschmann-kept` | `KretschmannKept.lean` | m0-a7 | 03:27 | 03:32 | merged |
| `kretschmann-kruskal` | `RiemannGen.lean`, `KretschmannGen.lean`, `KretschmannKruskal.lean` | m0-a8 | 03:27 | 03:39 | merged |
| `hess-kept` | `HessKept.lean` | m0-a9 | 03:30 | 03:33 | merged |
| `hess-kruskal` | `HessKruskal.lean` | m0-a1 | 03:30 | 03:41 | merged (`HessSchw.lean` on the branch: not merged) |
| `sphere-rigid` | `SphereRigid.lean` | m0-a2 | 03:33 | 03:42 | merged |
| `glue` | `LocalMaps.lean`, `Glue.lean` | m0-a6 | 03:34 | 03:40 | merged; target `globalBirkhoff`, open inputs closed at 03:55 |
| `kruskal-kept` | `KruskalKept.lean` | m0-a7 | 03:34 | 03:46 | merged |
| `unique-kruskal` | `UniqueKruskal.lean` | m0-a9 | 03:37 | 03:46 | merged |
| `kruskal-plane` | `KruskalPlane.lean` | m0-a3 | 03:38 | 03:46 | merged |
| `schw-kept` | `SchwScalars.lean`, `SchwKept.lean` | m0-a8 | 03:41 | 03:54 | merged; the last open link |
| `mass-unique` | `MassUnique.lean` | m0-a5 | 03:41 | 03:54 | merged; target |
| `unique-schw` | `ChartChange.lean`, `UniqueSchw.lean` | m0-a1 | 03:43 | 03:53 | merged |
| `kruskal-local` | `KruskalLocal.lean` | m0-a2 | 03:45 | 03:46 | built; not merged (proved twice) |
| `schw-local` | `SchwLocal.lean` | m0-a4 | 03:47 | 03:49 | merged |
| `schw-split` | `SchwSplit.lean` | m0-a7 | 03:49 | 03:53 | built; not merged (proved twice) |
| `schw-time` | `SchwTime.lean` | m0-a3 | 03:49 | 03:52 | built; not merged (proved twice) |
| `mass-charts` | `MassCharts.lean` | m0-a9 | 03:50 | 03:52 | merged; not used by `MassUnique.lean` |
| `mass-mixed` | `MassMixed.lean` | m0-a2 | 03:50 | 03:55 | built; not merged (proved twice) |
| `form-check` | (read only), `Develop.lean` | m0-a6 | 03:50 | 03:55 | merged |
| `schw-radius` | `SchwRadius.lean` | m0-a7 | 03:54 | 03:56 | built; not merged (proved twice) |
| lead | `Kretschmann.lean`, `TableHess.lean` (definitions), `Unique.lean`, `Converse.lean` (joining lines) | m0-a0 | | 03:27, 03:29, 03:38, 03:46 | |
| `form-fix-round` | `ConverseRoundKruskal.lean` | m0-a4 | 03:59 | 04:01 | merged; the nine equations that the `simp ... at` produced are now stated |
