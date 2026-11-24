# Join: status of the team's work on `birkhoffNoCoordinates`

Goal: `theorem birkhoffNoCoordinates : Curved.BirkhoffNoCoordinates` (`Curved/Goal.lean`).
Times are UTC on 24 November 2026, read from the queue's log and the branch commits. Lead:
`m0-a0`. The lead started at about 00:07.

## Result

**Goal reached at 00:30 UTC.** `theorem birkhoffNoCoordinates : Curved.BirkhoffNoCoordinates` is
in `Join/Goal.lean` (full name `GravityInLean.birkhoffNoCoordinates`), all twenty-four files of
`Join/` are imported by `GravityInLean.lean`, and the whole project builds through the queue
(`scripts/queued-build.sh`: `Build completed successfully (7531 jobs)`, ended 00:30:08),
`Audit.lean` included: "all 1436 declarations under GravityInLean checked: none rests on more
than [propext, Classical.choice, Quot.sound]" (1243 before). A scratch check
`example : GravityInLean.Curved.BirkhoffNoCoordinates := GravityInLean.birkhoffNoCoordinates`
passes, and `#print axioms` names the same three. `GravityInLean/Goals/`, `GravityInLean/Curved/`
and `Audit.lean` are unchanged; the only existing file changed is `GravityInLean.lean`
(twenty-four import lines). No file of `Join/` has a `sorry` or an `axiom`.

Honest numbers:

* The lead's first step (the set-up script) started at about 00:08:50. Reading took until 00:12.
* First round, ten items that do not depend on each other, statements written in the messages
  (the workers made the files): given out 00:12 to 00:15, built 00:14 to 00:18.
* The goal proved from `resultA` and `resultB` with both open: built 00:17 (second run; the
  first failed on a name that exists in two namespaces, `IsEmptyOn`).
* Second round, eight items: given out 00:17 to 00:21, built 00:20 to 00:24. `resultA` from its
  lemmas with stubs: built 00:23 on the first run.
* Third round, the last five items (`patch`, `curvature`, `curvature-at`, `usable-carry`,
  `usable-new`): given out 00:19 to 00:24, built 00:25 to 00:29.
* Whole project with the audit: 00:30:08. From the lead's start to the goal: about 21 minutes.
* Queue runs up to the goal: 70, of them 17 failed (3 by the lead). Longest wait in the queue:
  34 s. 4524 lines of Lean in 24 files, 176 named results and definitions.
* No statement fixed by the lead had to be changed. Two workers found that the paper route
  needed a change: `shape` (the old proof reads a turn at `φ = π/2`, outside any small box; redone
  at `φ = 0`) and `signature` (a shorter proof than the three cases suggested).
* The lead changed workers' files twice, by two words each: two lemma names of `CarryBracket.lean`
  clashed with `CarryPointwise.lean` (`carryField_pushField`, `pushField_carryField`; now with
  the prefix `chart_`), and `CarryConnection.lean` used the old names.
* Given out twice as a hedge: the step from fields to steps in the curvature item went to m0-a3
  as `curvature-at` while m0-a2 had the whole item. m0-a2 delivered both halves first; m0-a3's
  file `CarryCurvatureAt.lean` builds on branch `join-curvature-at` and is not merged (not
  needed).
* Idle: m0-a1, m0-a5, m0-a8 and m0-a9 had no item after 00:23 to 00:25. There was nothing left
  to give that the goal needed. `ConnectionExistsStatement` was not attempted (it is stated for
  any model with corners, a job of its own).
* Not clean: `Signature.lean` builds with linter warnings (`simp at` without a list).
* Not done by the lead: a separate reading of each worker's proof text, or a check that each
  comment says what its Lean statement says. The build and the audit are the check.

## The route chosen, and why

The supervisor's route, in three parts, with one intermediate stop added in Part A.

**Part A (`resultA`).** Chart `c` = the chart at `p`, cut down to the region `s`. `Carry.lean`
reads the curved space in the chart: `carryMeasure c g`, `carryField c ξ`, `pushField c X'`,
`carryTransport c cov`. First stop: everything is shown for the *flat curved space* `Coords 4`
with the length measure `flatMeasure (carryMeasure c g)` (the words of `Curved/Basic.lean` again,
now on coordinate space). Second stop: `FlatToTable.lean` turns these words into tables
(`tableOf`, `partsOf`, `invT`). Why two stops: the chart lemmas need no tables, and the table
dictionary needs no chart.

"Empty" carries over like this, with no curvature computed in the chart:
the carried connection belongs to the carried length measure (`isConnectionOf_carry`); a good
table has the connection `flatTransport A`; any connection of a length measure on flat space has
a full curvature that only looks at the three steps (`FlatTensor.lean`, by uniqueness of the
connection); the full curvature of fields carries over (`curvatureOfFields_carry`), hence
that of steps (`curvatureAt_carry`); the trace does not see the change of basis
(`ricciAt_carry`).

**Part B (`resultB`).** `turnsCoordinates` gives `Φ`. The table `inNewCoords Φ g'` is round
(`Mix.lean`), good, empty, with one time direction and positive spheres (`NewTable.lean`). On a
box of angles around the equator point it has the general round shape (`ShapeBox.lean`; the old
proof read one turn at `φ = π/2`, outside the box, so it was redone at `φ = 0`). The setting of
the general theorem and the size equations follow (`Setting.lean`, `Signature.lean`). The usable
distance becomes `sizeSlopeOf ≠ 0` (`UsableNew.lean`, `UsableSlope.lean`). A smooth version
of `birkhoff_general_of_sizeEquations` gives the mass and a new time that is smooth of every
order (`NewTime.lean`). `Patch.lean` puts these together on a small box. `ResultB.lean`
composes the inverse of `Φ` with the relabelling (`exists_localDiffeo_of_det` in `Atlas.lean`).

**Part C (`Goal.lean`).** The chart of the goal is `c.trans Ψ` (`trans_mem_maximalAtlas`,
`mfderiv_trans_apply` in `Atlas.lean`).

## The lemmas

| item (`task:join-…`) | file | what it says | who | given | built | note |
|---|---|---|---|---|---|---|
| `carry` | `Carry.lean` | the words | m0-a0 | — | 00:13 | lead |
| `mix` | `Mix.lean` | a fixed mix of unchanged fields; the new table is round | m0-a5 | 00:12 | 00:15 | merged |
| `shape` | `ShapeBox.lean` | the round shape on a box | m0-a6 | 00:12 | 00:15 | merged; proof redone at φ = 0 |
| `signature` | `Signature.lean` | one time direction gives `det2 > 0` | m0-a7 | 00:12 | 00:14 | merged |
| `newtime` | `NewTime.lean` | mass and smooth new time | m0-a8 | 00:12 | 00:17 | merged |
| `atlas` | `Atlas.lean` | chart after a change of coordinates; inverse function theorem | m0-a9 | 00:12 | 00:18 | merged |
| `pointwise` | `CarryPointwise.lean` | carry-over at one point | m0-a1 | 00:14 | 00:17 | merged |
| `bracket` | `CarryBracket.lean` | fields and brackets carry over | m0-a2 | 00:14 | 00:18 | merged; two names changed by the lead (clash) |
| `smooth` | `CarrySmooth.lean` | smoothness of the measure carries over | m0-a3 | 00:14 | 00:17 | merged |
| `flattensor` | `FlatTensor.lean` | flat space: curvature of fields is curvature of steps | m0-a4 | 00:15 | 00:16 | merged |
| `connection` | `CarryConnection.lean` | the connection carries over | m0-a4 | 00:17 | 00:22 | merged |
| `newtable` | `NewTable.lean` | the new table is good, empty, one time, positive spheres | m0-a5 | 00:17 | 00:22 | merged |
| `setting` | `Setting.lean` | `SettingG` and size equations on a box | m0-a6 | 00:17 | 00:20 | merged |
| `usable-slope` | `UsableSlope.lean` | usable distance gives `sizeSlopeOf ≠ 0` | m0-a7 | 00:17 | 00:22 | merged |
| `round` | `CarryRound.lean` | space-time, unchanged, round carry over | m0-a1 | 00:19 | 00:23 | merged |
| `ricci` | `CarryRicci.lean` | the trace carries over; empty carries over (given curvature) | m0-a3 | 00:19 | 00:23 | merged |
| `flat-table` | `FlatToTable.lean` | from flat words to tables | m0-a8 | 00:19 | 00:23 | merged |
| `result-b` | `ResultB.lean` | Result B from the lemmas | m0-a9 | 00:20 | 00:24 | merged; its two stubs swapped for imports by the lead 00:27, 00:29 |
| `result-a` | `ResultA.lean` | Result A from the lemmas | m0-a0 | — | 00:23 | from the lemmas; last stub gone 00:29 |
| `goal` | `Goal.lean` | the goal from A and B | m0-a0 | — | 00:17 | closed for good with the whole build at 00:30 |
| `curvature` | `CarryCurvature.lean` | full curvature carries over: fields, and steps at a point | m0-a2 | 00:19 | 00:25 | merged; the hardest item |
| `curvature-at` | `CarryCurvatureAt.lean` | from fields to steps | m0-a3 | 00:24 | 00:27 | not merged, not needed (hedge) |
| `usable-carry` | `CarryUsable.lean` | usable distance carries over | m0-a4 | 00:24 | 00:25 | merged 00:29 |
| `usable-new` | `UsableNew.lean` | usable distance in the turns' coordinates | m0-a7 | 00:24 | 00:28 | merged; 1 failed run |
| `patch` | `Patch.lean` | Birkhoff on the patch | m0-a6 | 00:21 | 00:26 | merged |

"Built" means: the file builds through the queue with no hole of its own. Branches are
`join-<item>`.

## What a next team could do

The goal is reached; nothing of it is open. Still unproved in the project and not needed here:
`ConnectionExistsStatement` (`Goals/Connection.lean`). `Join/CarryConnection.lean` and
`Join/FlatToTable.lean` give a connection in every chart of a space modelled on a vector space;
gluing these over a space with a general model (corners) is the missing part.
