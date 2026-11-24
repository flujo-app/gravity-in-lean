# Goal for the team: Birkhoff's theorem with no coordinates at all

You are a team of ten in one container: the lead `m0-a0` and nine workers `m0-a1` to `m0-a9`.
You work in the repository `flujo-app/gravity-in-lean`: Einstein's gravity, checked by the proof
checker Lean 4 (version 4.36.0, with its standard library mathlib v4.36.0). Each of you has a
copy of the repository of your own (your work folder). All copies share one store of branches,
so a branch that one of you commits is at once visible to the others.

## What to prove

One statement, exactly as it is written in `GravityInLean/Curved/Goal.lean`:

```lean
theorem birkhoffNoCoordinates : Curved.BirkhoffNoCoordinates
```

In words: take a curved space of four dimensions with a length measure `g` that has one time
direction on an open region `s`, is empty there (`IsEmptyOn`), and looks the same from every
side (`IsRoundOn`, three fields `ξ`). Then around every point `p` of `s` where the size of the
spheres is a usable distance (`UsableDistanceAt`) there are a mass `m` and a chart `φ` of the
space in which `g` is Schwarzschild's length measure. Read `Curved/Basic.lean` and
`Curved/Goal.lean` for the exact form; every word counts. `README.md` says what the project
already has.

This is the goal of the whole project so far. Two teams before you proved what it needs from
analysis: `smoothFlow` (`GravityInLean/Flows/`) and `turnsCoordinates` (`GravityInLean/Turns/`),
each in a quarter of an hour. Read their `STATUS.md` files to see how they worked. This job is
larger, and it has a part the others did not have: the library's curved spaces (manifolds),
whose tangent spaces are awkward to work with. `Curved/Flat.lean` shows what worked there.

## A route, as a suggestion

Worked out on paper by the supervisor. It is **not checked in Lean**. Check each step before you
build on it, and take another route if you find a better one. Parts A and B do not depend on
each other: work on both from the first minute.

**Part A. From the curved space to a table of functions (a chart at `p`).**

1. Take a chart `c` of the space at `p`, cut down to an open set inside `s`. Read `g` and the
   three fields in it: a table `g' a b x` and parts `ξ' i k x` on an open set `s'` of
   `Coords 4`. On coordinate space the project already has the dictionary between the two
   languages: `Curved/Flat.lean` and `Curved/Tables.lean` (`flatMeasure`, `tableMeasure`,
   `fieldOf`, `leavesUnchangedAt_table_iff`, `mlieBracket_fieldOf`, `IsRegularTableOn`,
   `IsRegularTableOn.isEmptyOn_iff`, `ricciAt_eq_of_isConnectionOf`).
2. Show that each notion of `Curved/Basic.lean` carries over along a chart: one time
   direction, smoothness, the bracket of fields, "unchanged along a field", the size of the
   spheres and its slope, and "empty". For "empty", do not compute a curvature in the chart.
   Carry the connection over, show that the carried connection belongs to the carried length
   measure, and then use that a length measure has only one connection
   (`IsConnectionOf.unique`, `ricciAt_eq_of_isConnectionOf`, `isEmptyOn_iff`). The curvature
   and its trace must be shown to carry over too.
3. **Result A:** an open `s'`, a point `x₀` in it, tables `g'`, `g'inv`, `ξ'` with
   `IsRegularTableOn g' g'inv s'`, `TurnsOn g' ξ' s'`, `IsRicciFlatAt g' g'inv x` on `s'`, one
   time direction at every point, the usable distance at `x₀`, and the formula that gives `g`
   at a point of the chart from `g'` and the chart's slope (`mfderiv`).

**Part B. Inside coordinates. No curved-space library needed.**

4. `turnsCoordinates` gives new coordinates `Φ` in which the fields are the standard turns
   (after a fixed rotation). The table in the new coordinates is `inNewCoords Φ g'`. It is
   still empty (`isRicciFlatAt_inNewCoords`) and still left unchanged by the fields
   (`leavesUnchangedAt_inNewCoords`). Needed and not there yet: a fixed mix of fields that
   leave a table unchanged leaves it unchanged.
5. **The shape on a small patch.** `shape_of_round` (`Symmetry.lean`) says that a table left
   unchanged by the three standard turns is `genG` of four functions of time and distance. It
   assumes this for all angles; the new coordinates only cover a box around the equator
   point. Prove the same on a box.
6. **Birkhoff on the patch.** Follow the proof of `birkhoff_of_round`
   (`BirkhoffFromSymmetry.lean`) from the point where it has the shape: it only uses points on
   the equator. It needs `SettingG` (from "one time direction" and "positive on the spheres"),
   the size equations (from "empty"), and that the size of the spheres is a usable distance
   (true at `x₀`, hence nearby). Then `birkhoff_general_of_sizeEquations` gives the mass and
   the new time, and the lengths of steps agree with Schwarzschild's. From lengths of steps to
   the length measure itself: `eq_of_stepLength_eq` (`SameSpacetime.lean`).
7. **Result B:** a mass `m` and a map `Ψ`, smooth with a smooth inverse near `x₀`, into
   `outside m ∪ inside m`, such that `g'` is Schwarzschild's table carried back along `Ψ`.

**Part C. Joining.** `Ψ` after the chart `c`, on a small open set around `p`, is a chart of the
space in the sense the goal asks for (`IsManifold.maximalAtlas`: smooth with a smooth inverse).
The formula of the goal follows from Results A and B and the chain rule for `mfderiv`.

Things that are easy to get wrong: the goal asks its formula for every point of the chart's
domain, so make the domain small. `m` may be any real number. The radius must stay off `2 m`
and positive, and the angle off the poles, on the whole domain. Which way round slopes go
(`jac`, `mfderiv`): `schwarzschild_meets_conclusion` in `Curved/Goal.lean` is a worked case with
the chart that does nothing.

If a worker is free and nothing else is open: `ConnectionExistsStatement`
(`Goals/Connection.lean`) is still unproved. It is not needed for the goal.

## Rules that are not negotiable

1. **Do not change the statement.** `GravityInLean/Goals/` and `GravityInLean/Curved/` are not
   to be edited, by anyone. If you come to think that the goal is false or cannot be proved as
   written, say so on the board with your argument, and stop work on it. Do not prove a weaker
   statement instead. A report "this is false, here is why" is a good result.
2. **Do not change existing files** outside your own new ones. New files go in
   `GravityInLean/Join/`. Only the lead adds them to `GravityInLean.lean`, and only when they are
   finished.
3. **The build is the judge.** A file is finished when it builds without a hole (`sorry`) and
   without a new assumption (`axiom`). The whole goal is reached when the whole project builds
   with it: `scripts/queued-build.sh` ends with `Build completed successfully`. That build
   includes `Audit.lean`, which fails on any hole and on any new assumption. Do not weaken
   `Audit.lean`.
4. **One Lean run at a time, for the whole team.** Never call `lake` or `lean` directly. Always
   go through the queue, which waits for the others' runs to finish:
   - one file: `scripts/queued-build.sh lake build GravityInLean.Join.YourFile`
   - a quick try of a scratch file: `scripts/queued-build.sh lake env lean path/to/Scratch.lean`
   - the whole project: `scripts/queued-build.sh`
   Think before you run, and try several ideas in one scratch file rather than one idea per
   run. Never build the standard library from source: if a run starts compiling files under
   `Mathlib/`, stop it and report.
5. **Set up your copy once,** before anything else: `scripts/setup-worktree.sh`. It links the
   ready-built standard library into your copy and gives it the project's build, so that only
   your new files have to be built. It can take three minutes the first time.
6. **One file, one worker.** Two of you never edit the same file.
7. **The form of a file.** As in `GravityInLean/Turns/`: the copyright lines, then `module`,
   then `public import` lines naming only the parts of the library that the file needs (never
   all of `Mathlib`), then `import Mathlib.Tactic`, a comment that says in plain words what the
   file is for, then `@[expose] public section`. Every theorem gets a short comment in plain
   language that says what it means.
8. **Nothing leaves the container.** Do not push to GitHub, do not open pull requests or issues,
   do not use the network for anything but reading documentation. The supervisor collects the
   branches at the end.

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

- **The lead** checks the route, splits the proof into lemmas, and writes each lemma's exact
  statement into its own file under `GravityInLean/Join/`, with the proof left open (`sorry`).
  The lead commits these files on the branch `join` and makes one board item per lemma,
  claimed as `task:join-<item>`. Before giving a statement out, the lead checks that it
  compiles with the proof left open, and, as soon as possible, that the lemmas together give
  the goal (the final theorem proved from the lemmas while they are still open). Statements
  that later lemmas depend on are fixed by the lead and not changed by workers. If a worker
  finds a lemma's statement wrong or too hard, the worker says so to the lead, and the lead
  decides.
- **A worker** claims the item it was given (`task:join-<item>`), starts a branch
  `join-<item>` from the branch `join`, proves the lemma in that item's file, builds the file
  through the queue, commits, and reports to the lead.
- **Git.** Commit often, at least after every step that builds: the run can be stopped at any
  time, and only what is committed is collected. `scripts/setup-worktree.sh` sets the name and the
  address that your commits carry; do not change them. No lines that credit an AI or a tool in commits.
- **The lead merges** finished branches into `join` and keeps a short file
  `GravityInLean/Join/STATUS.md` on that branch, updated at least every twenty minutes: the
  route chosen and why, the list of lemmas, and for each one who has it, when it was given out,
  when it built, or why it is stuck. If the run is stopped before the goal is reached, this
  file is what the next team starts from: say plainly what is proved, what is open, and what
  you would do next.
- **When the goal is reached,** the lead makes sure that the branch `join` builds as a whole
  through the queue, with `theorem birkhoffNoCoordinates : Curved.BirkhoffNoCoordinates` in it
  and imported by `GravityInLean.lean`, says so on the board with the claim
  `task:join-goal-reached`, and then stops: no further turns are needed.

## What the supervisor measures

This run is measured: how much such a team gets done per hour, and at what cost. It will be
stopped after a set time or when a set share of the weekly allowance is used, whichever comes
first, possibly before the goal is reached. Honest numbers matter more than good ones: an item
that turned out too hard is a result too, and so is "this step of the route is false".
