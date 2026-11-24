# Rim: status of the team's work on Birkhoff's theorem at every point

Goals: the eleven statements of `Goals/EveryPoint.lean`. Times are UTC on 24 November 2026, read
from the queue's log and the branch commits. Lead: `m0-a0`. The lead started at about 02:20.
Working branch: `rim`; each item has a branch `rim-<item>` (board claim `task:rim-<item>`).

## Result (02:53)

**All eleven targets are proved, and none was found false as written.** The whole project builds
with them through the queue (`scripts/queued-build.sh`: `Build completed successfully
(7689 jobs)`, ended 02:50:48), `Audit.lean` included: "all 2004 declarations under GravityInLean
checked: none rests on more than [propext, Classical.choice, Quot.sound]" (1798 before). All 24
new Lean files are imported by `GravityInLean.lean`. A scratch check
`example : <statement> := <theorem>` passes for each of the eleven targets, and `#print axioms`
names the same three for each. `GravityInLean/Goals/`, `GravityInLean/Curved/` and `Audit.lean`
are unchanged; the only existing file changed is `GravityInLean.lean` (24 import lines). No new
file has a `sorry` or an `axiom`. Each new file, run on its own through the queue
(`lake env lean`), prints nothing: no warning.

| target | state | file |
|---|---|---|
| `kruskalRadiusSpec` | proved | `Rim/Radius.lean` |
| `kruskalRadiusSmooth` | proved | `Rim/RadiusSmooth.lean` |
| `kruskalIsSpaceTime` | proved | `Rim/Table.lean` |
| `kruskalIsEmpty` | proved | `Rim/Empty.lean` |
| `kruskalIsRound`, `kruskalMeetsConclusion` | proved | `Rim/Round.lean` |
| `kruskalNotUsableOnRim` | proved | `Rim/NotUsable.lean` |
| `kruskalHoldsSchwarzschild` | proved | `Rim/Finish.lean` (halves: `Rim/SchwOutside.lean`, `Rim/SchwInside.lean`) |
| `deSitterNotKruskal` | proved | `Rim/Finish.lean` (from `Rim/DeSitter.lean`) |
| `birkhoffAtEveryPoint`, `birkhoffAtEveryPointOneMass` | proved | `Rim/Goal.lean` |

Honest numbers:

* The lead's first step was at about 02:20; the set-up script ran until about 02:24.
* Part 1 (nine statements): nine items given out 02:23 to 02:24, built 02:25 to 02:36; the two
  joining lines (`Finish.lean`) 02:37. Whole project with the nine: 02:40:36.
* Part 2: the lead read `Join/` and `OneMass/` and worked out the product form on paper from
  02:24 to 02:30. The statements went out in four rounds, each compiled with the proofs open
  before it was given out: 02:31 (product form, function constant along a field, two labels
  along the paths of light), 02:34 (core, patch, point of positive mass, goals), 02:37 to 02:38
  (equations and Kruskal's labels in the labels along the paths of light, the shape in those
  labels, the core's assembly), 02:39 (two helpers for the shape). Last link built 02:49;
  the chain to the two goals built at 02:50:32; whole project 02:50:48.
* From the lead's start to the last goal: about 31 minutes.
* Queue runs from 02:20 to 02:53: 79, of them 13 failed (2 by the lead: the name clashes
  below). Longest wait in the queue after the set-up builds: 38 s (behind the lead's run of all 24 files
  one by one). 4689 lines of Lean in 24
  files, 173 named results and definitions.
* No statement fixed by the lead had to be changed. No worker reported a statement false or a
  constant wrong.
* The route was changed in one place, by the lead, before anything was given out: steps 10 and
  11 (the zeros of `f` and `h`, the number `κ`, the equation `V' / V = κ / f` with its singular
  point) are not done at all. `Product.lean` does their work. No step of the supervisor's route
  was found false; these two were not tried.
* The lead changed a worker's file once: three helper names in `NullMass.lean` that another
  file declared too (`clm_apply_pair`, `hasDerivAt_dt_of_differentiableAt`,
  `hasDerivAt_dr_of_differentiableAt`; now `clm_apply_two`, `hasDerivAt_dt_of_slope`,
  `hasDerivAt_dr_of_slope`). One more clash (`kruskalA_pos`, `kruskalS_pos` in `Empty.lean` and
  `Table.lean`) was removed by the worker when asked.
* Given out as a hedge, and not needed: while the last link (`NullForm.lean`) showed no commit
  for ten minutes, the lead gave two more helpers (`NullCongr.lean` to m0-a3,
  `NullSlopes.lean` to m0-a1) and a second assembly (`NullAssembly.lean` to m0-a2) at 02:47 to
  02:48. The first worker's proof built at 02:49. `NullCongr.lean` and
  `NullSlopes.lean` build on their branches (`rim-null-congr`, `rim-null-slopes`); the second
  assembly was not finished; none of the three is merged.
* Idle: m0-a4 and m0-a9 had no item after 02:37; m0-a5, m0-a6, m0-a7 none after 02:40 to 02:42.
  There was nothing left to give that the goals needed.
* Not done: a second reading of each proof text, or a check by a second person that each
  comment says what its Lean statement says. Checked by script only: every new file has the
  required form (copyright, `module`, no whole-library import, `import Mathlib.Tactic`, a header
  comment, `@[expose] public section`), every named result has a comment before it, no proof
  has a `simp at` without a list, and no name is declared in two files. The build and the audit
  are the judge of the proofs.
* `Audit.lean` was not touched; it does not hold a line per target that checks the theorem
  against its statement (the scratch check above did that once, outside the build).

## The route chosen for the theorem (Part 2)

The supervisor's route, with one change in steps 10 to 12 (no ordinary equation with a
singular point is solved; see `Rim/Product.lean`).

* **Mass, with no usable distance** (step 6): taken from `OneMass/` as it stands: `MassAt`,
  `localMass`, `resultA_mass`, `patch_box_mass`.
* **Mass zero or negative** (step 7), `Rim/LowMass.lean`, proved: a point of mass `m ≤ 0` has a
  usable distance (`usable_of_massAt_nonpos`: the squared length of the slope of the size is at
  least four times the size), and `localMass` gives Schwarzschild's chart of that same mass.
* **Positive mass** (steps 8 to 13), a chain of lemmas, each in its own file:
  1. `FirstIntegral.lean` (proved): a function constant along a field of arrows in the plane.
  2. `NullLabels.lean` (proved): two labels `u`, `v` along the paths of light.
  3. `NullInverse.lean`, `NullForm.lean`: in these labels the table is the round shape
     `genG zero2 zero2 F S` (time-distance part `2 F du dv`), again empty, with the same mass.
  4. `NullEquations.lean`: with `r = √S` and `Ω = kruskalF m r`:
     `(32 m³ / r) exp (-r / 2m) Ω_uv = 2 F` and `Ω Ω_uv = Ω_u Ω_v`.
  5. `Product.lean`: a smooth `Ω` on a box with `Ω Ω_uv = Ω_u Ω_v` and `Ω_uv ≠ 0` is a product
     on the whole box, across its zeros: `Ω(u, v) Ω_uv(u₀, v₀) = Ω_v(u, v₀) Ω_u(u₀, v)`.
     (Where `Ω ≠ 0` is dense; `Ω_u / Ω_uv` does not depend on `u`; `Ω_uv` is a product.) This
     replaces steps 10 and 11 of the route: `U = -Ω_v(·, v₀) / Ω_uv(u₀, v₀)`, `V = Ω_u(u₀, ·)`
     are Kruskal's labels at once, rim or not.
  6. `NullKruskal.lean`: `T = (U + V) / 2`, `X = (V - U) / 2` make the null shape Kruskal's.
  7. `Core.lean`: 2, 3 and 6 put together for the shape `genG A B C S` (`kruskal_core`).
  8. `Patch.lean`: the table on a patch is Kruskal's in other coordinates (`kruskal_patch`).
  9. `HighMass.lean`: `tableKruskal`, `kruskalNear_of_massAt_pos`.
* **The goals** (steps 13, 14), `Rim/Goal.lean`: split on the sign of the mass;
  one mass on a region in one piece by `exists_const_of_locally`.

## The pieces

| item (`task:rim-…`) | file | who | given | built | note |
|---|---|---|---|---|---|
| `radius` | `Radius.lean` | m0-a1 | 02:23 | 02:25 | merged |
| `radius-smooth` | `RadiusSmooth.lean` | m0-a2 | 02:23 | 02:26 | merged |
| `table` | `Table.lean` | m0-a3 | 02:23 | 02:27 | merged |
| `empty` | `Empty.lean` | m0-a4 | 02:24 | 02:34, 02:36 | merged; second round to drop two names declared in `Table.lean` too |
| `round` | `Round.lean` | m0-a5 | 02:23 | 02:25 | merged |
| `not-usable` | `NotUsable.lean` | m0-a6 | 02:23 | 02:27 | merged |
| `schw-outside` | `SchwOutside.lean` | m0-a7 | 02:24 | 02:33 | merged |
| `schw-inside` | `SchwInside.lean` | m0-a8 | 02:24 | 02:36 | merged |
| `desitter` | `DeSitter.lean` | m0-a9 | 02:24 | 02:26 | merged |
| `finish` | `Finish.lean` | m0-a4 | 02:35 | 02:37 | merged; joining lines for two targets |
| `product` | `Product.lean` | m0-a1 | 02:31 | 02:37 | merged; the heart of steps 10 to 12 |
| `first-integral` | `FirstIntegral.lean` | m0-a2 | 02:31 | 02:36 | merged |
| `null-labels` | `NullLabels.lean` | m0-a9 | 02:31 | 02:37 | merged |
| `patch` | `Patch.lean` | m0-a3 | 02:34 | 02:37 | merged; from `kruskal_core` |
| `high-mass` | `HighMass.lean` | m0-a6 | 02:34 | 02:35 | merged; from `kruskal_patch` |
| `goal` | `LowMass.lean`, `Goal.lean` | m0-a5 | 02:34 | 02:36 | merged; `Goal.lean` from `kruskalNear_of_massAt_pos` |
| `null-equations` | `NullEquations.lean` | m0-a7 | 02:37 | 02:42 | merged; 1 failed run |
| `null-kruskal` | `NullKruskal.lean` | m0-a6 | 02:38 | 02:40 | merged; from `product` and `null-equations` |
| `core` | `Core.lean` | m0-a2 | 02:38 | 02:40 | merged; from `null-form` and `null-kruskal` |
| `null-inverse` | `NullInverse.lean` | m0-a5 | 02:38 | 02:40 | merged; helper for `null-form` |
| `null-table` | `NullTable.lean` | m0-a3 | 02:39 | 02:43 | merged; helper for `null-form` |
| `null-mass` | `NullMass.lean` | m0-a1 | 02:39 | 02:42 | merged; helper for `null-form` |
| `null-form` | `NullForm.lean` | m0-a8 | 02:38 | 02:49 | merged; 1 failed run; the last link |
| `null-congr` | `NullCongr.lean` | m0-a3 | 02:47 | 02:49 | hedge; builds on its branch, not merged, not needed |
| `null-slopes` | `NullSlopes.lean` | m0-a1 | 02:47 | 02:52 | hedge; builds on its branch, not merged, not needed |
| `null-assembly` | `NullAssembly.lean` | m0-a2 | 02:48 | | hedge; not finished, not needed |

"Built" means: the file builds through the queue with no hole of its own. Statements of the
lemmas were fixed by the lead and compiled with their proofs left open before they were given
out.

## What a next team could do

The goals are reached; nothing of them is open. Not asked here and not done: that the two cases
of `BirkhoffAtEveryPoint` never hold together (the statement's comment says "in fact never
both"); a global form of the theorem (one map of a whole region into Kruskal's space-time, not
a chart around each point); and a line per target in `Audit.lean`.

## Added by the supervisor, after the run

The text above is the team's own record, left as the lead wrote it. Checked afterwards on the
supervisor's PC:

- The clock of the run started at 02:22:05 UTC, when all ten agents were ready. The whole
  project built with all eleven results at 02:50:48 (the queue's log): 28 minutes 43 seconds.
- Only `GravityInLean/Rim/` and the import lines in `GravityInLean.lean` differ from the commit
  the team started from.
- Rebuilt from nothing through the queue, no warnings; `Audit.lean` now holds, for each of the
  eleven results, a line that checks it proves the statement as it was fixed.
- Not checked by anyone but its author: whether each lemma's comment says what its Lean
  statement says.

