# Goal for the team: paths along a field depend smoothly on where they start

You are a team of ten working in the repository `flujo-app/gravity-in-lean`: Einstein's gravity,
checked by the proof checker Lean 4 (version 4.36.0, with its standard library mathlib v4.36.0).
Read `README.md` first, then `PLAN.md`, section "Next: Birkhoff's theorem with no coordinates at
all".

## What to prove

One statement, exactly as it is written in `GravityInLean/Goals/Turns.lean`:

```lean
theorem smoothFlow : SmoothFlowStatement
```

In words: let `X` be a smooth field of arrows on an open region `U` of a complete space of
vectors, and `x₀` a point of `U`. Then following `X` for a time `t` from a starting point `x` is a
smooth function of `t` and `x` together, for `t` near `0` and `x` near `x₀`.

Lean's standard library has the paths themselves (`Mathlib/Analysis/ODE/`, Picard and Lindelöf's
theorem, Grönwall's inequality) and that they depend continuously on the starting point. It does
not have that they depend smoothly on it. That is what this team adds. The textbooks prove it
either by differentiating under the equation (the slope of the path with respect to its starting
point solves a second, linear equation) or with the inverse function theorem on a space of paths.
Choose the route that fits the standard library best. Look at what the library has before you
decide: read its files, do not guess.

## Rules that are not negotiable

1. **Do not change the statement.** `GravityInLean/Goals/` is not to be edited, by anyone. If you
   come to think that the statement is false or cannot be proved as written, say so on the board
   with your argument, and stop work on it. Do not prove a weaker statement instead.
2. **Do not change existing files** outside your own new ones. New files go in
   `GravityInLean/Flows/`. Only the lead adds them to `GravityInLean.lean`, and only when they are
   finished.
3. **The build is the judge.** A file is finished when the whole project builds with it:
   `scripts/queued-build.sh` ends with `Build completed successfully`. That build includes
   `Audit.lean`, which fails on any hole (`sorry`) and on any new assumption (`axiom`). Do not
   weaken `Audit.lean`. A hole in a file that is not yet imported by `GravityInLean.lean` is fine
   while you work.
4. **One build at a time.** Never call `lake build` directly. Always build through
   `scripts/queued-build.sh`, for one file as `scripts/queued-build.sh lake build
   GravityInLean.Flows.YourFile`. It waits for other workers' builds to finish.
   Never build the standard library from source: if a build starts compiling files under
   `Mathlib/`, stop it and report.
5. **Set up your copy once:** `scripts/setup-worktree.sh` links the ready-built standard library
   into your copy of the repository.
6. **One file, one worker.** Two workers never edit the same file.
7. **Plain words.** Every theorem gets a short comment in plain language that says what it means.

## How to work as a team

- **The lead** reads the library, chooses the route, and splits the proof into lemmas. The lead
  writes each lemma's exact statement into its own file under `GravityInLean/Flows/`, with the
  proof left open, and puts one item per lemma on the board. Statements that later lemmas depend
  on are fixed by the lead and not changed by workers. If a worker finds a lemma's statement
  wrong, the worker says so on the board and the lead decides.
- **A worker** claims one item, proves it in that item's file, builds it through the queue, and
  reports on the board when it builds: the file, and how long it took from claim to green build.
- **Git.** Each worker commits on a branch of its own, named `flows/<item>`, and pushes it. The
  lead merges finished branches into the branch `flows`. Commit as `flujo-app`. No lines that
  credit an AI or a tool in commits. Do not push to `main` and do not open pull requests; the
  supervisor does that.
- **When the goal is reached,** the lead makes sure that the branch `flows` builds as a whole
  through the queue, with `theorem smoothFlow : SmoothFlowStatement` in it and imported by
  `GravityInLean.lean`, and says so on the board.

## What the supervisor measures

This is a trial. It is run to learn how much such a team gets done per hour. So for every item,
record on the board when it was claimed and when it built. Honest numbers matter more than good
ones: an item that turned out too hard is a result too.
