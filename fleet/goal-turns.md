# Goal for the team: coordinates that fit the turns

You are a team of ten in one container: the lead `m0-a0` and nine workers `m0-a1` to `m0-a9`.
You work in the repository `flujo-app/gravity-in-lean`: Einstein's gravity, checked by the proof
checker Lean 4 (version 4.36.0, with its standard library mathlib v4.36.0). Each of you has a
copy of the repository of your own (your work folder). All copies share one store of branches,
so a branch that one of you commits is at once visible to the others.

## What to prove

One statement, exactly as it is written in `GravityInLean/Goals/Turns.lean`:

```lean
theorem turnsCoordinates : TurnsCoordinatesStatement
```

In words: take a table of functions `g` that is good on a region `s`, and three fields of arrows
`ξ 0`, `ξ 1`, `ξ 2` on `s` that are smooth, leave `g` unchanged, combine the way turns do (the
bracket of two is the third), span exactly two directions at every point, and have positive
lengths there (`TurnsOn`). Then around every point `p` of `s` there are new coordinates `Φ` and
one fixed rotation `R` of the three fields among themselves, such that in the new coordinates
the rotated fields are exactly the three standard turns `stdTurn = ![rotY, rotX, rotZ]`, and `p`
sits at `y 2 = π / 2`, `y 3 = 0`. Read the file for the exact form; every word of it counts.

This is a large job: expect many lemmas and several hours. A team before you proved the first
statement of that file, `smoothFlow` (in `GravityInLean/Flows/`, read `Flows/STATUS.md`), in a
quarter of an hour. It is there for you to use.

## A route, as a suggestion

Worked out on paper by the supervisor. It is **not checked in Lean**. Check each step before you
build on it, and take another route if you find a better one.

1. **The field that rests at `p`.** At every point `q` the three arrows `ξ j q` span two
   directions, so there is a unit vector `n q` of three numbers, unique up to sign, with
   `∑ j, n q j • ξ j q = 0`. Choose a rotation `R` (`R * Rᵀ = 1`, `det R = 1`) whose row `1` is
   `n p`, and put `η i = ∑ j, R i j • ξ j`. Then `η` combines the way turns do as well (a
   rotation keeps the cross product), `η 1` is zero at `p`, and `η 0 p`, `η 2 p` span the two
   directions. Note that `stdTurn 1 = rotX` is the standard turn that is zero at
   `y 2 = π / 2`, `y 3 = 0`, while `rotY` is "along `y 2`" and `rotZ` "along `y 3`" there.
2. **How a field changes along another's flow.** For fields that combine like turns: carrying
   `η b` along the flow of `η a` gives a fixed mix of the three, with sines and cosines of the
   time (the two sides solve the same linear equation; uniqueness is in the library, Grönwall).
   In particular the set where `η 1` is zero is carried by the flows in a known way.
3. **Where `η 1` rests.** The points `q` near `p` with `η 1 q = 0` form a surface through `p`
   of two dimensions that crosses the surfaces swept out by the fields. Reason: moving `q`
   along `d • η` (for three numbers `d`) turns `n q` at the rate `± d × n q`, so `q ↦ n q`
   loses no direction along the swept surfaces; then use the library's theorem on solving
   smooth equations. Get a smooth `σ` of two numbers that runs through this surface, with
   `σ` at the starting pair equal to `p`.
4. **The coordinates.** `Φ y = flow of η 2 for the time y 3, of (flow of η 0 for the time
   y 2 - π / 2, of σ (y 0) (y 1))`. Smooth, because flows are (`smoothFlow`) and `σ` is.
   Its table of slopes has an inverse at the starting point (the four columns are two
   directions of `σ`, then `η 0 p`, `η 2 p`), hence nearby (the determinant is continuous).
5. **The three equations.** `rotZ` is "along `y 3`", so its equation is the flow equation of
   `η 2`. The ones for `rotY` and `rotX` follow from step 2 and from `η 1 = 0` on the surface
   of step 3, by a computation with sines, cosines and the cotangent.

Things that are easy to get wrong: which way round the table of slopes `jac Φ α μ` goes (read
`turnsCoordinates_schwarzschild` in the goals file, which has the identity map as an example);
the signs of the brackets (`bracketOf`, `likeTurns`); that a flow from `smoothFlow` is only
known to exist near one point and for short times, with no uniqueness stated (the library's
uniqueness for paths is in `Mathlib/Analysis/ODE/Gronwall.lean`). You may not need every
assumption of `TurnsOn`: that is fine.

## Rules that are not negotiable

1. **Do not change the statement.** `GravityInLean/Goals/` is not to be edited, by anyone. If you
   come to think that the statement is false or cannot be proved as written, say so on the board
   with your argument, and stop work on it. Do not prove a weaker statement instead.
2. **Do not change existing files** outside your own new ones. New files go in
   `GravityInLean/Turns/`. Only the lead adds them to `GravityInLean.lean`, and only when they are
   finished.
3. **The build is the judge.** A file is finished when it builds without a hole (`sorry`) and
   without a new assumption (`axiom`). The whole goal is reached when the whole project builds
   with it: `scripts/queued-build.sh` ends with `Build completed successfully`. That build
   includes `Audit.lean`, which fails on any hole and on any new assumption. Do not weaken
   `Audit.lean`.
4. **One Lean run at a time, for the whole team.** Never call `lake` or `lean` directly. Always
   go through the queue, which waits for the others' runs to finish:
   - one file: `scripts/queued-build.sh lake build GravityInLean.Turns.YourFile`
   - a quick try of a scratch file: `scripts/queued-build.sh lake env lean path/to/Scratch.lean`
   - the whole project: `scripts/queued-build.sh`
   Nine others wait while your run goes, so think before you run, and try several ideas in one
   scratch file rather than one idea per run. Never build the standard library from source: if
   a run starts compiling files under `Mathlib/`, stop it and report.
5. **Set up your copy once,** before anything else: `scripts/setup-worktree.sh`. It links the
   ready-built standard library into your copy and gives it the project's build, so that only
   your new files have to be built. It can take two minutes the first time.
6. **One file, one worker.** Two of you never edit the same file.
7. **The form of a file.** As in `GravityInLean/Flows/`: the copyright lines, then `module`,
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
  have a full plan, send each worker something useful: one step of the route above to check on
  paper and against the library, with the question "is this true as stated, what does the
  library have for it, and what would the Lean statement be?" Give out every job by a message
  to one named worker. The message says which board item it is, which file, and the exact
  statement. Keep the pieces small: a lemma that one worker can prove in ten to twenty minutes.
- **Workers, at the end of a job:** send the lead a message (what is done, the branch, what is
  left), and end your turn. If you are stuck for more than about fifteen minutes on one step,
  say so to the lead with the exact goal Lean shows, and end your turn: a smaller lemma, or a
  second pair of eyes, is cheaper than an hour alone.

## How to work as a team

- **The lead** checks the route, splits the proof into lemmas, and writes each lemma's exact
  statement into its own file under `GravityInLean/Turns/`, with the proof left open (`sorry`).
  The lead commits these files on the branch `turns` and makes one board item per lemma,
  claimed as `task:turns-<item>`. Before giving a statement out, the lead checks that it
  compiles with the proof left open, and, as soon as possible, that the lemmas together give
  the goal (the final theorem proved from the lemmas while they are still open). Statements
  that later lemmas depend on are fixed by the lead and not changed by workers. If a worker
  finds a lemma's statement wrong or too hard, the worker says so to the lead, and the lead
  decides.
- **A worker** claims the item it was given (`task:turns-<item>`), starts a branch
  `turns-<item>` from the branch `turns`, proves the lemma in that item's file, builds the file
  through the queue, commits, and reports to the lead.
- **Git.** Commit often, at least after every step that builds: the run can be stopped at any
  time, and only what is committed is collected. `scripts/setup-worktree.sh` sets the name and the
  address that your commits carry; do not change them. No lines that credit an AI or a tool in commits.
- **The lead merges** finished branches into `turns` and keeps a short file
  `GravityInLean/Turns/STATUS.md` on that branch, updated at least every twenty minutes: the
  route chosen and why, the list of lemmas, and for each one who has it, when it was given out,
  when it built, or why it is stuck.
- **When the goal is reached,** the lead makes sure that the branch `turns` builds as a whole
  through the queue, with `theorem turnsCoordinates : TurnsCoordinatesStatement` in it and
  imported by `GravityInLean.lean`, and says so on the board with the claim
  `task:turns-goal-reached`.

## What the supervisor measures

This run is measured: how much such a team gets done per hour, and at what cost. It will be
stopped after a set time or when a set share of the weekly allowance is used, whichever comes
first, possibly before the goal is reached. So `STATUS.md` records for every item when it was
given out and when it built. Honest numbers matter more than good ones: an item that turned
out too hard is a result too, and so is "this step of the route is false".
