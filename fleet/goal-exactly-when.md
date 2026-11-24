# Goal for the team: Birkhoff's theorem as one "exactly when"

You are a team of ten in one container: the lead `m0-a0` and nine workers `m0-a1` to `m0-a9`.
You work in the repository `flujo-app/gravity-in-lean`: Einstein's gravity, checked by the proof
checker Lean 4 (version 4.36.0, with its standard library mathlib v4.36.0). Each of you has a
copy of the repository of your own (your work folder). All copies share one store of branches,
so a branch that one of you commits is at once visible to the others.

## What to prove

Six statements, exactly as they are written in `GravityInLean/Goals/ExactlyWhen.lean`, and a
seventh from `GravityInLean/Goals/Connection.lean`:

```lean
theorem exactlyWhenAssumptionsMet : ExactlyWhenAssumptionsMet
theorem exactlyWhenAssumptionsMetInside : ExactlyWhenAssumptionsMetInside
theorem exactlyWhenNotAlwaysEmpty : ExactlyWhenNotAlwaysEmpty
theorem birkhoffExactlyWhenInCoordinates : BirkhoffExactlyWhenInCoordinates
theorem schwarzschildIsEmpty : Curved.SchwarzschildIsEmptyStatement
theorem schwarzschildExactlyWhen : Curved.SchwarzschildExactlyWhen
theorem connectionExists : Curved.ConnectionExistsStatement   -- lower priority, see below
```

In words. The project has Birkhoff's theorem in one direction: a round, empty space-time is
Schwarzschild's (`birkhoff_of_round` in coordinates, `birkhoffNoCoordinates` with none). The
other direction, "Schwarzschild's is empty", exists only outside the rim and only as a separate
theorem. The job is to make them one statement that runs both ways, in coordinates and with no
coordinates, outside the rim and inside it. Read the goals file for the exact form; every word
counts. Three teams before you worked the same way; read `GravityInLean/Join/STATUS.md`.

## A route, as a suggestion

Worked out on paper by the supervisor. It is **not checked in Lean**. Check each step before you
build on it, and take another route if you find a better one. Parts 1, 2 and 3 do not depend on
each other: work on all three from the first minute.

A second reader went through the six statements before they were fixed and judged every one
true as written. Two things that reader checked in Lean: Schwarzschild's table is empty inside
the rim with the same tables `roundG` and `roundGinv` (the old proof uses `2 * M < r` only to
get `r ≠ 0` and `1 - 2 M / r ≠ 0`), and every name in the goals file means what it should.

**Part 1. In coordinates. No curved-space library needed.**

1. *Schwarzschild's is empty inside the rim too.* `schwarzschild_ricciFlat`
   (`RoundSpacetime.lean`) and `schwarzschild_ricciFlat_inNewCoords` (`SameSpacetime.lean`) ask
   for `2 * M < r`. Prove both for `0 < r` and `r ≠ 2 * M`, with the same tables `roundG` and
   `roundGinv`. Find out what the old proofs really use of `2 * M < r`.
2. *From "Schwarzschild's after new labels" to "empty".* The lengths of all steps agree, so the
   tables agree (`eq_of_stepLength_eq`, `relabelStep_eq_jac`, `stepLength_inNewCoords`): the
   table is `inNewCoords (relabel T R) (roundG ...)` on the region. The new labels are smooth
   (the new time by assumption, the radius because the size of the spheres is positive), and
   their table of slopes has an inverse. Then step 1, and `isRicciFlatAt_congr` to pass from
   the carried table and its inverse to `g` and `ginv`.
3. *From "empty" to "Schwarzschild's after new labels".* `RoundSetting` plus "empty" is
   `RoundEmpty`. `birkhoff_general_smooth` (`Join/NewTime.lean`) gives the mass and a smooth new
   time. That the radius stays off `2 M` is done in `Join/Patch.lean` and `Join/ResultB.lean`.
4. *The assumptions can be met, and "empty" can fail.* Schwarzschild's own table outside the
   rim and inside it: the pieces are there (`schwarzschild_isRound`, `schwarzschild_regular`,
   `schwarzschild_regular_inside`, and the files of the known answers). De Sitter's table:
   `Probe/DeSitter.lean` has its curvature, `deSitter_not_isEmptyOn` in
   `Curved/KnownAnswers.lean` shows the kind of argument.

**Part 2. With no coordinates.**

5. *Carry-over, the other way.* `GravityInLean/Join/Carry*.lean` and `FlatToTable.lean` carry
   each notion from the curved space to a chart. Now the notions are known in the chart and
   wanted on the space: one time direction, smoothness, a connection of the length measure and
   its curvature ("empty"), fields, their brackets, "unchanged along a field", the size of the
   spheres and the usable distance. Where a carry-over lemma is an equation, it may serve both
   ways as it stands. A field of arrows on the space has to be given everywhere: use zero
   outside the chart's domain. A connection has to be given for all fields, too.
6. *The known answers off the rim, on both sides at once.* A chart may land outside the rim at
   some points and inside at others. So prove what is needed for Schwarzschild's table on the
   whole set "radius positive and not `2 m`, angle off the poles": good table, one time
   direction, empty (step 1), looks the same from every side (`schwarzschild_isRoundOn` is for
   outside only), usable distance (`schwarzschild_usable`, `schwarzschild_usable_inside`).
7. `schwarzschildIsEmpty` from 5 and 6. `schwarzschildExactlyWhen`: one direction is
   `birkhoffNoCoordinates`, the other is 5 and 6.

**Part 3. A length measure has a connection (`connectionExists`).** This part was withdrawn
during the run and is not part of this brief any more: see `GravityInLean/BothWays/STATUS.md`.

Things that are easy to get wrong: the statements with no coordinates are about a small region
around one point, so choose regions small. Inside the rim the time label and the distance label
of Schwarzschild's table swap roles, and signs change. `m` may be any real number.

## Rules that are not negotiable

1. **Do not change the statements.** `GravityInLean/Goals/` and `GravityInLean/Curved/` are not
   to be edited, by anyone. If you come to think that a statement is false or cannot be proved
   as written, say so on the board with your argument, and stop work on that statement. Do not
   prove a weaker statement instead. A report "this is false, here is why" is a good result.
2. **Do not change existing files** outside your own new ones. New files go in
   `GravityInLean/BothWays/`. Only the lead adds them to `GravityInLean.lean`, and only when they
   are finished.
3. **The build is the judge.** A file is finished when it builds without a hole (`sorry`),
   without a new assumption (`axiom`) and without warnings. The goal is reached when the whole
   project builds with all of it: `scripts/queued-build.sh` ends with `Build completed
   successfully`. That build includes `Audit.lean`, which fails on any hole and on any new
   assumption. Do not weaken `Audit.lean`.
4. **One Lean run at a time, for the whole team.** Never call `lake` or `lean` directly. Always
   go through the queue, which waits for the others' runs to finish:
   - one file: `scripts/queued-build.sh lake build GravityInLean.BothWays.YourFile`
   - a quick try of a scratch file: `scripts/queued-build.sh lake env lean path/to/Scratch.lean`
   - the whole project: `scripts/queued-build.sh`
   Think before you run, and try several ideas in one scratch file rather than one idea per
   run. Never build the standard library from source: if a run starts compiling files under
   `Mathlib/`, stop it and report.
5. **Set up your copy once,** before anything else: `scripts/setup-worktree.sh`. It links the
   ready-built standard library into your copy and gives it the project's build, so that only
   your new files have to be built. It can take three minutes the first time.
6. **One file, one worker.** Two of you never edit the same file.
7. **The form of a file.** As in `GravityInLean/Join/`: the copyright lines, then `module`,
   then `public import` lines naming only the parts of the library that the file needs (never
   all of `Mathlib`), then `import Mathlib.Tactic`, a comment that says in plain words what the
   file is for, then `@[expose] public section`. Every theorem gets a short comment in plain
   language that says what it means. No `simp at h` followed by a step that depends on the
   exact result: say what the step produces.
8. **Nothing leaves the container,** except reading: do not push to GitHub, do not open pull
   requests or issues. Reading documentation and the one file named in Part 3 is allowed. The
   supervisor collects the branches at the end.
9. **The repository is public.** Write nothing into files or commit messages that names a
   person, a machine or a folder outside the repository.

## How turns work here

A worker gets a new turn only when a message arrives in its inbox. Writing on the board alone
wakes nobody. The lead gets a new turn every two minutes by itself.

- **Workers, on your first turn:** run `scripts/setup-worktree.sh`, check your inbox, and if the
  lead has sent you nothing yet, end your turn. Do not start reading or proving on your own.
- **Lead:** nine workers waiting is the costliest thing here. In your first minutes, before you
  have a full plan, send each worker something useful: one step of the route to check on paper
  and against the library, with the question "is this true as stated, what does the library
  have for it, and what would the Lean statement be?" Give out every job by a message to one
  named worker. The message says which board item it is, which file, and the exact statement.
  Keep the pieces small: a lemma that one worker can prove in ten to twenty minutes.
- **Workers, at the end of a job:** send the lead a message (what is done, the branch, what is
  left), and end your turn. If you are stuck for more than about fifteen minutes on one step,
  say so to the lead with the exact goal Lean shows, and end your turn: a smaller lemma, or a
  second pair of eyes, is cheaper than an hour alone.

## How to work as a team

- **The lead** checks the route, splits the proofs into lemmas, and writes each lemma's exact
  statement into its own file under `GravityInLean/BothWays/`, with the proof left open
  (`sorry`). The lead commits these files on the branch `bothways` and makes one board item per
  lemma, claimed as `task:bothways-<item>`. Before giving a statement out, the lead checks that
  it compiles with the proof left open, and, as soon as possible, that the lemmas together give
  each of the goals (the final theorems proved from the lemmas while they are still open).
  Statements that later lemmas depend on are fixed by the lead and not changed by workers. If a
  worker finds a lemma's statement wrong or too hard, the worker says so to the lead, and the
  lead decides.
- **A worker** claims the item it was given (`task:bothways-<item>`), starts a branch
  `bothways-<item>` from the branch `bothways`, proves the lemma in that item's file, builds
  the file through the queue, commits, and reports to the lead.
- **Git.** Commit often, at least after every step that builds: the run can be stopped at any
  time, and only what is committed is collected. Before your first commit run
  `git config user.name flujo-app` in your copy. No lines that credit an AI or a tool in commits.
- **The lead merges** finished branches into `bothways` and keeps a short file
  `GravityInLean/BothWays/STATUS.md` on that branch, updated at least every twenty minutes: the
  route chosen and why, the list of lemmas, and for each one who has it, when it was given out,
  when it built, or why it is stuck. If the run is stopped before the goals are reached, this
  file is what the next team starts from: say plainly what is proved, what is open, and what
  you would do next.
- **When the goals are reached,** the lead makes sure that the branch `bothways` builds as a
  whole through the queue, with the theorems named above in it and imported by
  `GravityInLean.lean`, says so on the board with the claim `task:bothways-goal-reached`
  (naming which of the seven are proved), and then stops: no further turns are needed.

## What the supervisor measures

This run is measured: how much such a team gets done per hour, and at what cost. It will be
stopped after a set time, possibly before the goals are reached. Honest numbers matter more
than good ones: an item that turned out too hard is a result too, and so is "this step of the
route is false".
