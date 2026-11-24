# Goal for the team: tests that can fail, one mass, and the connection from the textbook

You are a team of ten in one container: the lead `m0-a0` and nine workers `m0-a1` to `m0-a9`.
You work in the repository `flujo-app/gravity-in-lean`: Einstein's gravity, checked by the proof
checker Lean 4 (version 4.36.0, with its standard library mathlib v4.36.0). Each of you has a
copy of the repository of your own (your work folder). All copies share one store of branches,
so a branch that one of you commits is at once visible to the others.

The project has proved Birkhoff's theorem with no coordinates given (`birkhoffNoCoordinates`)
and both ways (`schwarzschildExactlyWhen`). Three independent reviewers then read the
definitions against the textbooks (`REVIEW.md`, `review/`). They found no definition wrong, and
asked for three things. Those are this job. Four teams before you worked the same way; read
`GravityInLean/BothWays/STATUS.md` to see how.

## What to prove

**Part 1. Twenty-five tests** in `GravityInLean/Goals/Tests.lean`. Each statement there is a
`def … : Prop` in the namespace `GravityInLean.Curved.Tests`. For each, prove a theorem of that
type with the same name, first letter small, in the same namespace. For example:

```lean
theorem Curved.Tests.efNotUsableOnRim : Curved.Tests.EfNotUsableOnRim
```

Most of them say that a definition **fails** on a case where it should. The reviewers' reasons
and hints for each test are in `review/lean-conventions.md`, section "Proposed failure tests".

**Part 2. One mass for a whole region** (`GravityInLean/Goals/OneMass.lean`):

```lean
theorem oneMass : Curved.OneMassStatement
```

**Part 3. A length measure has a connection** (`GravityInLean/Goals/Connection.lean`):

```lean
theorem connectionExists : Curved.ConnectionExistsStatement
```

The three parts do not depend on each other. Work on all three from the first minute.

## Routes, as suggestions

Worked out on paper. **Not checked in Lean.** Check each step before you build on it.

**Part 1.** Each test stands alone, and most are short once the right existing lemma is found.
Give each group of tests (the file numbers them 1 to 12) to one worker. Useful: the dictionary
between tables and curved-space notions (`Curved/Flat.lean`, `Curved/Tables.lean`,
`leavesUnchangedAt_table_iff`, `mlieBracket_fieldOf`, `IsRegularTableOn.isEmptyOn_iff`,
`ricciAt_eq_of_isConnectionOf`), the known answers (`Curved/KnownAnswers.lean`,
`Curved/Goal.lean`, `BothWays/OffRimKnown.lean`), Eddington's form (`Eddington.lean`,
`SameSpacetime.lean`), `genG_isRound`, and for test 8 the carry-over lemmas in both
directions (`Join/`, `BothWays/Pull*.lean`). A test that is **false as written** is a finding:
report it to the lead with the reason, and the lead records it. Do not prove a changed test.

**Part 2.** The mass is `(r / 2) · (1 - |slope of r|²)`, where `r²` is the size of the spheres
(`sizeSq`) and the slope is measured with the length measure.

1. Around every point of the region, usable distance or not, there are coordinates in which the
   table has the general round shape and meets `SettingG` and the size equations: this is the
   path of `Join/ResultA.lean`, `Join/NewTable.lean`, `Join/ShapeBox.lean`, `Join/Setting.lean`
   up to the point where the usable distance is first used.
2. `massFn_const` (`BirkhoffGeneral.lean`): in such coordinates the mass function is the same at
   all points of the patch. It does not need a usable distance.
3. Give every point of the region its mass, in a way that does not depend on the coordinates
   chosen. Then it is the same near every point, hence the same on a region in one piece.
4. At a point with a usable distance, the chart that `birkhoffNoCoordinates` builds has this
   mass (`Join/ResultB.lean`, `Join/Patch.lean` take it from the mass function).

**Part 3. From the textbook, and only from there.** This is the first theorem of the subject:
Koszul's formula (for example O'Neill, *Semi-Riemannian Geometry*, chapter 3). For fields `X`,
`Y`, `Z`, twice "the change of `Y` along `X`, measured against `Z`" is fixed by the length
measure and brackets alone: the exact expression, with this project's signs, is the right-hand
side of `IsConnectionOf.koszul` in `Curved/Unique.lean`. Because no step is at right angles to
all steps, that expression names exactly one step at each point; take it as the value of the
connection. Then show the rules of `IsConnectionOf`: it is a connection, it has no twist, it
keeps lengths. The standard library has this construction for length measures with all lengths
positive (`Mathlib/Geometry/Manifold/Riemannian/`, the Levi-Civita connection); read it.

**Do not read any other project's proof of this theorem, in Lean or any other proof checker.**
Other projects have proved it (the README credits one), and this project's owner wants an
independent proof from the textbook. Do not search the web for it. If you have seen such a
proof before, say so to the lead, who gives the item to someone else.

## Rules that are not negotiable

1. **Do not change the statements.** `GravityInLean/Goals/` and `GravityInLean/Curved/` are not
   to be edited, by anyone. If you come to think that a statement is false or cannot be proved
   as written, say so on the board with your argument, and stop work on that statement. Do not
   prove a weaker statement instead. A report "this is false, here is why" is a good result.
2. **Do not change existing files** outside your own new ones. New files go in
   `GravityInLean/Checks/` (Part 1), `GravityInLean/OneMass/` (Part 2) and
   `GravityInLean/Connection/` (Part 3). Only the lead adds them to `GravityInLean.lean`, and
   only when they are finished.
3. **The build is the judge.** A file is finished when it builds without a hole (`sorry`),
   without a new assumption (`axiom`) and without warnings. The goal is reached when the whole
   project builds with all of it: `scripts/queued-build.sh` ends with `Build completed
   successfully`. That build includes `Audit.lean`, which fails on any hole and on any new
   assumption. Do not weaken `Audit.lean`.
4. **One Lean run at a time, for the whole team.** Never call `lake` or `lean` directly. Always
   go through the queue, which waits for the others' runs to finish:
   - one file: `scripts/queued-build.sh lake build GravityInLean.Checks.YourFile`
   - a quick try of a scratch file: `scripts/queued-build.sh lake env lean path/to/Scratch.lean`
   - the whole project: `scripts/queued-build.sh`
   Think before you run, and try several ideas in one scratch file rather than one idea per
   run. Never build the standard library from source: if a run starts compiling files under
   `Mathlib/`, stop it and report.
5. **Set up your copy once,** before anything else: `scripts/setup-worktree.sh`. It links the
   ready-built standard library into your copy and gives it the project's build, so that only
   your new files have to be built. It can take four minutes the first time.
6. **One file, one worker.** Two of you never edit the same file.
7. **The form of a file.** As in `GravityInLean/BothWays/`: the copyright lines, then `module`,
   then `public import` lines naming only the parts of the library that the file needs (never
   all of `Mathlib`), then `import Mathlib.Tactic`, a comment that says in plain words what the
   file is for, then `@[expose] public section`. Every theorem gets a short comment in plain
   language that says what it means. No `simp at h` followed by a step that depends on the
   exact result: say what the step produces.
8. **Nothing leaves the container,** and for Part 3 nothing comes in: do not push to GitHub, do
   not open pull requests or issues, do not search the web. Reading the standard library's
   files in your copy is the way to look things up.
9. **The repository is public.** Write nothing into files or commit messages that names a
   person, a machine or a folder outside the repository.

## How turns work here

A worker gets a new turn only when a message arrives in its inbox. Writing on the board alone
wakes nobody. The lead gets a new turn every two minutes by itself.

- **Workers, on your first turn:** run `scripts/setup-worktree.sh`, check your inbox, and if the
  lead has sent you nothing yet, end your turn. Do not start reading or proving on your own.
- **Lead:** nine workers waiting is the costliest thing here. In your first minutes give every
  worker a piece: the tests are ready to hand out as they stand. Give out every job by a
  message to one named worker. The message says which board item it is, which file, and the
  exact statement or the names of the statements. Keep the pieces small: what one worker can
  prove in ten to twenty minutes. A worker who finishes gets the next piece at once.
- **Workers, at the end of a job:** send the lead a message (what is done, the branch, what is
  left), and end your turn. If you are stuck for more than about fifteen minutes on one step,
  say so to the lead with the exact goal Lean shows, and end your turn: a smaller lemma, or a
  second pair of eyes, is cheaper than an hour alone.

## How to work as a team

- **The lead** splits Parts 2 and 3 into lemmas and writes each lemma's exact statement into
  its own file, with the proof left open (`sorry`), commits these files on the branch `checks`
  and makes one board item per piece, claimed as `task:checks-<item>`. Before giving a
  statement out, the lead checks that it compiles with the proof left open, and, as soon as
  possible, that the lemmas together give the goal. Statements that later lemmas depend on are
  fixed by the lead and not changed by workers. If a worker finds a lemma's statement wrong or
  too hard, the worker says so to the lead, and the lead decides.
- **A worker** claims the item it was given (`task:checks-<item>`), starts a branch
  `checks-<item>` from the branch `checks`, proves it in that item's file, builds the file
  through the queue, commits, and reports to the lead.
- **Git.** Commit often, at least after every step that builds: the run can be stopped at any
  time, and only what is committed is collected. `scripts/setup-worktree.sh` sets the name and the
  address that your commits carry; do not change them. No lines that credit an AI or a tool in commits.
- **The lead merges** finished branches into `checks` and keeps a short file
  `GravityInLean/Checks/STATUS.md` on that branch, updated at least every twenty minutes: for
  each of the twenty-seven targets whether it is proved, open, or reported false (with the
  reason); the routes chosen for Parts 2 and 3; and for each piece who has it, when it was
  given out, when it built, or why it is stuck. If the run is stopped before the goals are
  reached, this file is what the next team starts from.
- **When all is done that can be done,** the lead makes sure that the branch `checks` builds as
  a whole through the queue, with every proved theorem imported by `GravityInLean.lean`, says
  so on the board with the claim `task:checks-goal-reached` (naming what is proved, what is
  open and what is reported false), and then stops: no further turns are needed.

## What the supervisor measures

This run is measured: how much such a team gets done per hour, and at what cost. It will be
stopped after a set time, possibly before the goals are reached. Honest numbers matter more
than good ones: a test that turned out false is a result, and so is an item that was too hard.
