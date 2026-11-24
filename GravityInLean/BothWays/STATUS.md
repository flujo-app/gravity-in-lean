# BothWays: status of the team's work on Birkhoff's theorem as one "exactly when"

Goals: the six statements of `Goals/ExactlyWhen.lean` and `ConnectionExistsStatement` of
`Goals/Connection.lean`. Times are UTC on 24 November 2026, read from the branch commits. Lead:
`m0-a0`. The lead started at about 01:05.

## Where things stand (01:20)

**Six of the seven goals are proved**, and the whole project builds with them through the queue
(`scripts/queued-build.sh`: `Build completed successfully (7561 jobs)`, 01:19), `Audit.lean`
included: "all 1557 declarations under GravityInLean checked: none rests on more than [propext,
Classical.choice, Quot.sound]" (1436 before). A scratch check `example : <statement> := <theorem>`
passes for each of the six, and `#print axioms` names the same three for each. `Goals/`,
`Curved/`, `Join/` and `Audit.lean` are unchanged; the only existing file changed is
`GravityInLean.lean` (import lines). No file of `BothWays/` on the branch `bothways` has a
`sorry` or an `axiom`, and the build shows no warning.

| goal | state |
|---|---|
| `exactlyWhenAssumptionsMet` | proved, `AssumptionsMet.lean` |
| `exactlyWhenAssumptionsMetInside` | proved, `AssumptionsMet.lean` |
| `exactlyWhenNotAlwaysEmpty` | proved, `NotAlwaysEmpty.lean` |
| `birkhoffExactlyWhenInCoordinates` | proved, `InCoordinates.lean` |
| `schwarzschildIsEmpty` | proved, `NoCoordinates.lean` |
| `schwarzschildExactlyWhen` | proved, `NoCoordinates.lean` |
| `connectionExists` | **open**; withdrawn from this run, see the note at the end |

## The route chosen, and why

The supervisor's route, with these choices.

**Part 1, in coordinates.** As suggested. Step 1 (`OffRim.lean`): the old proofs use `2M < r`
only for `r ≠ 0` and `1 - 2M/r ≠ 0`. Step 2 (`EmptyOfRelabelled.lean`): the Jacobian condition
of `IsSchwarzschildRelabelled` is not needed in this direction, the inverse of the carried table
is `ginv` itself. Step 3 (`RelabelledOfEmpty.lean`): `birkhoff_general_smooth` gives everything;
nothing of `Join/Patch.lean` or `Join/ResultB.lean` was needed.

**Part 2, with no coordinates.** The region is the whole domain of the chart `φ` of
`IsSchwarzschildNear` (no smaller region is needed: the chart lands off the rim everywhere), and
the three fields are `pushField φ (turns i)`. `Pull.lean` has two words: `ReadsAs c g G` (the
length measure `g` is `G` in the chart `c`) and `pullTransport c cov'` (a connection of
coordinate space taken to the curved space). Each notion of `Curved/Basic.lean` comes back along
the chart in a file of its own (`Pull*.lean`). "Empty" comes back with no new curvature
computation: the connection is `pullTransport` of the textbooks' connection of the table
(`PullConnection.lean`); then the lemmas of `Join/` are used forward, as in `resultA`, to read
its curvature in the chart, where it is the coordinate formula. Schwarzschild's table is treated
on the one set `offRim m` (radius positive and not `2m`, off the poles), both sides of the rim at
once (`OffRimKnown.lean`).

**Part 3, `connectionExists`.** Withdrawn from this run by the supervisor (see the note at the
end). Nothing of it is on the branch `bothways`.

## The lemmas

| item (`task:bothways-…`) | file | what it says | who | given | built | note |
|---|---|---|---|---|---|---|
| `offrim` | `OffRim.lean` | Schwarzschild's table is empty for `0 < r`, `r ≠ 2M`, also after new coordinates | m0-a1 | 01:07 | 01:11 | merged |
| `met` | `AssumptionsMet.lean` | goals 1 and 2 | m0-a4 | 01:07 | 01:12 | merged |
| `notempty` | `NotAlwaysEmpty.lean` | goal 3 | m0-a5 | 01:07 | 01:13 | merged |
| `coords-backward` | `EmptyOfRelabelled.lean` | Schwarzschild's after new labels is empty | m0-a2 | 01:09 | 01:12 | merged |
| `coords-forward` | `RelabelledOfEmpty.lean` | empty gives Schwarzschild's after new labels | m0-a3 | 01:09 | 01:11 | merged |
| `incoordinates` | `InCoordinates.lean` | goal 4 from the two directions | m0-a0 | — | 01:15 | lead |
| `known` | `OffRimKnown.lean` | the known answers on `offRim m` | m0-a6 | 01:10 | 01:13 | merged |
| `pull` | `Pull.lean` | the words `ReadsAs`, `pullTransport` | m0-a0 | — | 01:12 | lead |
| `pull-connection` | `PullConnection.lean` | the connection comes back along a chart | m0-a7 | 01:12 | 01:15 | merged |
| `pull-spacetime` | `PullSpaceTime.lean` | smooth, length measure, space-time come back | m0-a8 | 01:12 | 01:18 | merged; smoothness by the trivialisation of the bundle at a point |
| `pull-smooth` | `PullSmooth.lean` | smoothness comes back (the hard part of the item above, as a hedge) | m0-a7 | 01:17 | — | stopped 01:19, nothing written: m0-a8 was first |
| `pull-round` | `PullRound.lean` | unchanged along a field, round come back | m0-a1 | 01:13 | 01:16 | merged |
| `pull-usable` | `PullUsable.lean` | the usable distance comes back | m0-a2 | 01:13 | 01:16 | merged |
| `pull-empty` | `PullEmpty.lean` | empty comes back | m0-a4 | 01:13 | 01:18 | merged; did not need `isLengthMeasureOn_pull` |
| `nocoordinates` | `NoCoordinates.lean` | goals 5 and 6 from the lemmas | m0-a0 | — | 01:19 | lead; checked 01:15 with all lemmas open (scratch file), built 01:19 with all of them proved |
| `connection` | `ConnectionExists.lean` | goal 7 | m0-a9 | 01:07 | | withdrawn from this run; not merged |
| `connection-pieces` | `ConnectionPieces.lean` | three pieces for goal 7 | m0-a3 | 01:14 | 01:18 | withdrawn from this run; not merged |
| `review-part1`, `review-part2` | — | a second reading of the merged files: comments against statements, form | m0-a2, m0-a1 | 01:17 | | in work |

"Built" means: the file builds through the queue with no hole of its own. Branches are
`bothways-<item>`.

## Added by the supervisor, after the run

The text above is the team's own record, left as the lead wrote it, except for the part on
`connectionExists`, which is shortened. Checked afterwards on the supervisor's PC:

- The clock of the run started at 01:08:35 UTC, when all ten agents were ready. The whole
  project built with the six theorems at 01:19 (the queue's log): about 11 minutes.
- Only `GravityInLean/BothWays/` and the import lines in `GravityInLean.lean` differ from the
  commit the team started from. `GravityInLean/Goals/`, `GravityInLean/Curved/`,
  `GravityInLean/Join/` and `Audit.lean` were not touched.
- Rebuilt from nothing through the queue; `Audit.lean` now holds, for each of the six
  theorems, a line that checks it proves the statement as it was fixed.
- **Why `connectionExists` was withdrawn.** The brief told the team to port another project's
  proof of it. During the run the project's owner asked for it to be proved from the textbook
  instead, without reading that proof. A worker had already read it, so the item was stopped
  and its files were left out: they are on no branch of this repository. The statement stays
  open and goes to a later team with that instruction.
- Not checked by anyone but its author: whether each lemma's comment says what its Lean
  statement says.

