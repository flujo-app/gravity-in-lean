# Checks: status of the team's work on the tests, one mass, and the connection

Goals: the twenty-five tests of `Goals/Tests.lean` (Part 1), `OneMassStatement` of
`Goals/OneMass.lean` (Part 2) and `ConnectionExistsStatement` of `Goals/Connection.lean`
(Part 3). Times are UTC on 24 November 2026, read from the queue's log and the branch commits.
Lead: `m0-a0`. The lead started at about 01:48. Working branch: `checks`; each item has a branch
`checks-<item>` (board claim `task:checks-<item>`).

## Result (02:04)

**All twenty-seven targets are proved, and none was found false as written.** The whole project
builds with them through the queue (`scripts/queued-build.sh`: `Build completed successfully
(7635 jobs)`, ended 02:01:53), `Audit.lean` included: "all 1798 declarations under GravityInLean
checked: none rests on more than [propext, Classical.choice, Quot.sound]" (1557 before). All 29
new Lean files are imported by `GravityInLean.lean`. A scratch check
`example : <statement> := <theorem>` passes for each of the 27 targets (the test on any curved
space with its three universes), and `#print axioms` names the same three for `oneMass`,
`connectionExists` and the two tests asked. `GravityInLean/Goals/`, `GravityInLean/Curved/`,
`GravityInLean/Join/`, `GravityInLean/BothWays/` and `Audit.lean` are unchanged; the only existing
file changed is `GravityInLean.lean` (29 import lines). No new file has a `sorry` or an `axiom`.
Each new file, run on its own through the queue (`lake env lean`), prints nothing: no warning.

Honest numbers:

* The lead's first step was at about 01:48; the set-up script ran until 01:50.
* Part 1: eight items given out 01:49 to 01:50, built 01:52 to 01:56. Whole project with 23
  tests: 01:57:39; with all 25: 02:00:05.
* Part 2: the lead wrote the definition and nine statements; `oneMass` from the lemmas with all
  proofs open built at 01:55 on the first run. Eight items given out at 01:56, built 01:57 to
  01:59. Whole project with `oneMass`: 02:01:29.
* Part 3: the skeleton (the words, the candidate, eight statements, the goal from the lemmas)
  was written by a worker from the lead's plan, given 01:51, built 01:58. Six items given out
  01:58 to 01:59, built 01:59 to 02:01. Whole project with `connectionExists`: 02:01:53.
* From the lead's start to the last goal: about 14 minutes.
* Queue runs up to 02:04: 121, of them 10 failed. Longest wait: 118 s (the set-up builds at
  the start). 3761 lines of Lean in 29 files, 146 named results and definitions.
* No statement fixed by the lead had to be changed. One hypothesis fixed by the lead turned out
  not to be needed: `hS : 0 < S` in `massAt_of_genG` (the proof names it once so that the
  statement could stay as given out).
* Given out twice by mistake: `exists_koszulCov` (`Connection/Candidate.lean`). The skeleton's
  author took it on after reporting, and the lead gave it to m0-a5 before reading that report.
  Both proved it. Merged: m0-a9's. m0-a5's builds on branch `checks-connection-candidate` and is
  not merged.
* The lead changed a worker's file once, by one word: `isOpen_efRegion` in `EfRound.lean` is now
  `efRegion_isOpen` (the same name was in `EfEmpty.lean`).
* A worker changed more than the open proof once, and said so: in `Connection/Sharp.lean` two
  `omit … in` lines were added so that `flat_bijective` and `sharp_apply` do not carry two unused
  instance arguments (the linter warns otherwise). The statements are otherwise as given out.
* Part 3 rule: every worker on Part 3 was told the rule in the message that gave the item, and
  each reported having used only the textbook formula, this repository and the standard library's
  files; none reported having seen another project's proof.
* Idle: after 02:01 nothing was left to give out.
* Not done: a second reading of each proof text, or a check by a second person that each
  comment says what its Lean statement says. Checked by script only: every new file has the
  required form (copyright, `module`, no whole-library import, `import Mathlib.Tactic`,
  `@[expose] public section`), every named result has a comment before it, and no proof has a
  `simp at` without a list. The build and the audit are the judge of the proofs.
* `Audit.lean` was not touched; it does not yet hold a line per target that checks the theorem
  against its statement (the scratch check above did that once, outside the build).

## The twenty-seven targets

| target | state | file |
|---|---|---|
| `efIsSpaceTimeOn`, `efIsEmptyOn` | proved | `Checks/EfEmpty.lean` |
| `efIsRoundOn`, `efNotUsableOnRim` | proved | `Checks/EfRound.lean` |
| `cylIsRoundOn`, `cylNotUsable`, `cylNotEmpty` | proved | `Checks/Cyl.lean` |
| `zeroNotRound`, `zeroMeetsOtherClauses`, `kinkNotUnchanged`, `kinkNotSmooth` | proved | `Checks/ZeroKink.lean` |
| `schwFlippedNotSpaceTime`, `schwFlippedNotRound`, `schwFlippedIsEmpty`, `isEmptyOnNegIff` | proved | `Checks/Neg.lean` |
| `twoTimeNotSpaceTime`, `flatDegNotOneTime`, `squashNotUnchanged`, `squashUnchangedAxis`, `squashNotRound` | proved | `Checks/TimeSquash.lean` |
| `deSitterIsRoundOn`, `deSitterUsable`, `deSitterNotSchwarzschild` | proved | `Checks/DeSitter.lean` |
| `minkowskiIsRoundOn`, `minkowskiUsable` | proved | `Checks/Minkowski.lean` |
| `oneMass` | proved | `OneMass/Goal.lean` |
| `connectionExists` | proved | `Connection/Exists.lean` |

No test was found false as written.

## The routes chosen

**Part 1.** Each group of tests to one worker, the statements as they stand.

**Part 2.** The supervisor's route. The mass of a point is said without coordinates
(`OneMass/Mass.lean`): `MassAt g ξ p m` says that there is a step `n` at `p` that the length
measure turns into the slope of `sizeSq` (as in `UsableDistanceAt`, but its squared length may be
zero), and that `massOf (sizeSq g ξ p) (g p n n) = m`, with `massOf σ N = (√σ / 2)(1 - N / (4σ))`.
It is a relation, not a function, so no step has to be chosen; where no step is at right angles
to all steps a point has at most one mass (`massAt_unique`).

* In a table of the general round shape the mass is the mass function `massFn`
  (`MassGenG.lean`), which is the same on a whole box (`PatchBox.lean`, from `setting_of_box`
  and `massFn_const_of_sizeEquations`; no usable distance).
* The mass comes back from the coordinates that fit the turns (`MassNewCoords.lean`) and along a
  chart (`MassCarry.lean`): the transfers of `Join/UsableNew.lean` and `Join/CarryUsable.lean`,
  read the other way.
* `birkhoff_patch` again with the mass named: it is the mass function at the point
  (`PatchMass.lean`). Results A and B again with the mass (`ResultAMass.lean`, `TableMass.lean`).
* `Local.lean`: every point of the region has a mass that all points near it have; where the
  distance is usable, the chart is Schwarzschild's of that mass. `Connected.lean`: the same near
  every point gives the same on a region in one piece. `Goal.lean`: `oneMass`.

**Part 3.** From the textbook (Koszul's formula), with the standard library's file for positive
lengths as the model (`Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean`).
No other project's proof was read (each worker was told the rule; the skeleton's author states
it). `koszulExpr g X Y Z x` is the right-hand side of `IsConnectionOf.koszul`. It is tensorial in
`X` and in `Z` (`Tensorial1.lean`, `Tensorial3.lean`), so for fixed `Y` it is a two-slot function
of steps; because no step is at right angles to all steps, it is "apply a linear map, then
measure" for one linear map (`Sharp.lean`: a count of dimensions in place of Riesz). Half of
that map is the candidate `koszulCov g Y x` (`Candidate.lean`; chosen by `Classical.choose`, zero
where there is none, so the definition needs neither the region nor a proof). The rules of
`IsConnectionOf` follow from `koszulCov_spec` alone (`IsConnection.lean` with `Middle.lean`,
`NoTwist.lean`, `KeepsLengths.lean`).

## The pieces

| item (`task:checks-…`) | file | what it says | who | given | built | note |
|---|---|---|---|---|---|---|
| `ef-round` | `Checks/EfRound.lean` | tests 1c, 1d | m0-a1 | 01:49 | 01:53 | merged; lemma `isOpen_efRegion` renamed `efRegion_isOpen` by the lead (clash with `EfEmpty`) |
| `ef-empty` | `Checks/EfEmpty.lean` | tests 1a, 1b | m0-a2 | 01:49 | 01:52 | merged |
| `cyl` | `Checks/Cyl.lean` | tests 2 | m0-a3 | 01:49 | 01:54 | merged |
| `zero-kink` | `Checks/ZeroKink.lean` | tests 3, 10, 11 | m0-a4 | 01:49 | 01:52 | merged |
| `neg` | `Checks/Neg.lean` | tests 4, 12 | m0-a5 | 01:49 | 01:54 | merged |
| `time-squash` | `Checks/TimeSquash.lean` | tests 5, 6 | m0-a6 | 01:49 | 01:53 | merged |
| `desitter` | `Checks/DeSitter.lean` | tests 7, 8 | m0-a7 | 01:49 | 01:53 | merged |
| `minkowski` | `Checks/Minkowski.lean` | tests 9 | m0-a8 | 01:50 | 01:56 | merged |
| `mass-def` | `OneMass/Mass.lean` | `massOf`, `MassAt`, `massAt_unique` | m0-a0 | — | 01:54 | lead |
| `mass-geng` | `OneMass/MassGenG.lean` | mass of the round shape is `massFn` | m0-a1 | 01:56 | 01:59 | merged; `hS` not needed |
| `mass-box` | `OneMass/PatchBox.lean` | the mass is the same near the equator point | m0-a6 | 01:56 | 01:58 | merged |
| `mass-patch` | `OneMass/PatchMass.lean` | `birkhoff_patch` with the mass named | m0-a3 | 01:56 | 01:57 | merged |
| `mass-newcoords` | `OneMass/MassNewCoords.lean` | the mass comes back from the turns' coordinates | m0-a2 | 01:56 | 01:57 | merged |
| `mass-carry` | `OneMass/MassCarry.lean` | the mass comes back along a chart | m0-a4 | 01:56 | 01:57 | merged |
| `mass-connected` | `OneMass/Connected.lean` | same near every point, so same everywhere | m0-a5 | 01:56 | 01:58 | merged |
| `mass-result-a` | `OneMass/ResultAMass.lean` | Result A with the mass | m0-a5 | 01:56 | 01:58 | merged |
| `mass-table` | `OneMass/TableMass.lean` | Result B with the mass | m0-a7 | 01:56 | 01:58 | merged |
| `mass-local` | `OneMass/Local.lean` | one mass near every point | m0-a0 | — | 01:55 | lead; from the lemmas |
| `mass-goal` | `OneMass/Goal.lean` | `oneMass` | m0-a0 | — | 01:55 | lead; from the lemmas; closed for good with the whole build at 02:01 |
| `connection-skeleton` | `Connection/Koszul.lean`, `Candidate.lean`, `Exists.lean` | the words, the candidate, the goal from the lemmas | m0-a9 | 01:51 | 01:58 | merged |
| `connection-tensorial1` | `Connection/Tensorial1.lean` | tensorial in the first field | m0-a8 | 01:58 | 02:01 | merged |
| `connection-tensorial3` | `Connection/Tensorial3.lean` | tensorial in the third field | m0-a3 | 01:58 | 02:01 | merged |
| `connection-middle` | `Connection/Middle.lean` | sum and product rule in the middle field | m0-a2 | 01:58 | 02:00 | merged |
| `connection-sharp` | `Connection/Sharp.lean` | a linear rule is "measure against one step" | m0-a4 | 01:59 | 01:59 | merged; two `omit` lines added |
| `connection-candidate` | `Connection/Candidate.lean` | the linear map that Koszul's expression names exists | m0-a9, and m0-a5 | 01:58, 01:59 | 01:59, 02:00 | given out twice by mistake; m0-a9's merged, m0-a5's not |
| `connection-isconnection` | `Connection/IsConnection.lean` | the candidate is a connection | m0-a7 | 01:59 | 02:01 | merged |
| `connection-notwist` | `Connection/NoTwist.lean` | no twist | m0-a9 | 01:58 | 01:58 | merged (on branch `checks-connection-skeleton`) |
| `connection-keepslengths` | `Connection/KeepsLengths.lean` | keeps lengths | m0-a9 | 01:58 | 01:58 | merged (on branch `checks-connection-skeleton`) |

"Built" means: the file builds through the queue with no hole of its own.

## What a next team could do

Nothing of the three parts is open. Not done here, and worth a reader: a second reading of the
comments against the statements; a line in `Audit.lean` for each of the 27 targets that checks
the theorem against its fixed statement; dropping the unused hypothesis `hS` of
`massAt_of_genG`. The mass said without coordinates (`MassAt`) could serve further statements,
for example that the mass of a region does not depend on which three fields show it to be round.

## Added by the supervisor, after the run

The text above is the team's own record, left as the lead wrote it. Checked afterwards on the
supervisor's PC:

- The clock of the run started at 01:48:23 UTC, when all ten agents were ready. The whole
  project built with all 27 results at 02:01:53 (the queue's log): 13 minutes 30 seconds.
- Only `GravityInLean/Checks/`, `GravityInLean/OneMass/`, `GravityInLean/Connection/` and the
  import lines in `GravityInLean.lean` differ from the commit the team started from.
- Rebuilt from nothing through the queue, no warnings; `Audit.lean` now holds, for each of the
  27 results, a line that checks it proves the statement as it was fixed.
- The brief asked that the connection be proved from the textbook without reading any other
  project's proof. The record of the run holds no call that reaches the network and none that
  names another project.
- Not checked by anyone but its author: whether each lemma's comment says what its Lean
  statement says.

