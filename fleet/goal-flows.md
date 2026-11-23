# Goal for the team: paths along a field depend smoothly on where they start

You are a team of ten in one container: the lead `m0-a0` and nine workers `m0-a1` to `m0-a9`.
You work in the repository `flujo-app/gravity-in-lean`: Einstein's gravity, checked by the proof
checker Lean 4 (version 4.36.0, with its standard library mathlib v4.36.0). Each of you has a
copy of the repository of your own (your work folder). All copies share one store of branches,
so a branch that one of you commits is at once visible to the others.

## What to prove

One statement, exactly as it is written in `GravityInLean/Goals/Turns.lean`:

```lean
theorem smoothFlow : SmoothFlowStatement
```

In words: let `X` be a smooth field of arrows on an open region `U` of a complete space of
vectors, and `x₀` a point of `U`. Then following `X` for a time `t` from a starting point `x` is a
smooth function of `t` and `x` together, for `t` near `0` and `x` near `x₀`.

Lean's standard library has the paths themselves (`Mathlib/Analysis/ODE/`, Picard and Lindelöf's
theorem, Grönwall's inequality) and that they depend continuously on the starting point. As far
as a text search showed, it does not have that they depend smoothly on it. That is what this team
adds. The textbooks prove it either by differentiating under the equation (the slope of the path
with respect to its starting point solves a second, linear equation) or with the inverse function
theorem on a space of paths. Choose the route that fits the standard library best. Look at what
the library has before you decide: read its files (they are under `.lake/packages/mathlib/`), do
not guess. If the library already has the result or most of it, say so and use it.

## Rules that are not negotiable

1. **Do not change the statement.** `GravityInLean/Goals/` is not to be edited, by anyone. If you
   come to think that the statement is false or cannot be proved as written, say so on the board
   with your argument, and stop work on it. Do not prove a weaker statement instead.
2. **Do not change existing files** outside your own new ones. New files go in
   `GravityInLean/Flows/`. Only the lead adds them to `GravityInLean.lean`, and only when they are
   finished.
3. **The build is the judge.** A file is finished when it builds without a hole (`sorry`) and
   without a new assumption (`axiom`). The whole goal is reached when the whole project builds
   with it: `scripts/queued-build.sh` ends with `Build completed successfully`. That build
   includes `Audit.lean`, which fails on any hole and on any new assumption. Do not weaken
   `Audit.lean`.
4. **One Lean run at a time, for the whole team.** Never call `lake` or `lean` directly. Always
   go through the queue, which waits for the others' runs to finish:
   - one file: `scripts/queued-build.sh lake build GravityInLean.Flows.YourFile`
   - a quick try of a scratch file: `scripts/queued-build.sh lake env lean path/to/Scratch.lean`
   - the whole project: `scripts/queued-build.sh`
   Nine others wait while your run goes, so think before you run, and try several ideas in one
   scratch file rather than one idea per run. Never build the standard library from source: if
   a run starts compiling files under `Mathlib/`, stop it and report.
5. **Set up your copy once,** before anything else: `scripts/setup-worktree.sh`. It links the
   ready-built standard library into your copy.
6. **One file, one worker.** Two of you never edit the same file.
7. **Plain words.** Every theorem gets a short comment in plain language that says what it means.
8. **Nothing leaves the container.** Do not push to GitHub, do not open pull requests or issues,
   do not use the network for anything but reading documentation. The supervisor collects the
   branches at the end.

## How turns work here

A worker gets a new turn only when a message arrives in its inbox. Writing on the board alone
wakes nobody. The lead gets a new turn every two minutes by itself.

- **Workers, on your first turn:** run `scripts/setup-worktree.sh`, check your inbox, and if the
  lead has sent you nothing yet, end your turn. Do not start reading or proving on your own.
- **Lead:** give out every job by a message to one named worker. The message says which board
  item it is, which file, and the exact statement. While you are still planning, you can send
  workers to read a part of the library each and report back in twenty lines.
- **Workers, at the end of a job:** send the lead a message (what is done, the branch, what is
  left), and end your turn. If you are stuck for more than about fifteen minutes on one step,
  say so to the lead with the exact goal Lean shows, and end your turn: a smaller lemma, or a
  second pair of eyes, is cheaper than an hour alone.

## How to work as a team

- **The lead** reads the library, chooses the route, and splits the proof into lemmas. The lead
  writes each lemma's exact statement into its own file under `GravityInLean/Flows/`, with the
  proof left open (`sorry`), commits these files on the branch `flows`, and makes one board item
  per lemma, claimed as `task:flows-<item>`. Before giving a statement out, the lead checks that
  it at least compiles with the proof left open. Statements that later lemmas depend on are fixed
  by the lead and not changed by workers. If a worker finds a lemma's statement wrong, the worker
  says so to the lead, and the lead decides.
- **A worker** claims the item it was given (`task:flows-<item>`), starts a branch
  `flows/<item>` from the branch `flows`, proves the lemma in that item's file, builds the file
  through the queue, commits, and reports to the lead.
- **Git.** Commit often, at least after every step that builds: the trial can be stopped at any
  time, and only what is committed is collected. Before your first commit run
  `git config user.name flujo-app` in your copy. No lines that credit an AI or a tool in commits.
- **The lead merges** finished branches into `flows` and keeps a short file
  `GravityInLean/Flows/STATUS.md` on that branch: the route chosen and why, the list of lemmas,
  and for each one who has it, when it was given out, when it built, or why it is stuck.
- **When the goal is reached,** the lead makes sure that the branch `flows` builds as a whole
  through the queue, with `theorem smoothFlow : SmoothFlowStatement` in it and imported by
  `GravityInLean.lean`, and says so on the board with the claim `task:flows-goal-reached`.

## What the supervisor measures

This is a trial. It is run to learn how much such a team gets done per hour, and at what cost.
It will be stopped after a set time, probably before the goal is reached. So for every item,
`STATUS.md` records when it was given out and when it built. Honest numbers matter more than
good ones: an item that turned out too hard is a result too, and so is "the library already had
this".
