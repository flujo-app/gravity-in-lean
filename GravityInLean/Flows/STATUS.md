# Flows: status of the team's work on `smoothFlow`

Goal: `theorem smoothFlow : SmoothFlowStatement` (statement 1 of `Goals/Turns.lean`).
Times are UTC on 23 November 2026. Lead: `m0-a0`.

## Result

**Goal reached at 22:50 UTC.** `theorem smoothFlow : SmoothFlowStatement` is in
`SmoothFlow.lean`, all eleven files of `Flows/` are imported by `GravityInLean.lean`, and the
whole project builds through the queue (`scripts/queued-build.sh`: `Build completed
successfully (18339 jobs)`, 33 s), `Audit.lean` included: "all 1147 declarations under
GravityInLean checked: none rests on more than [propext, Classical.choice, Quot.sound]".
`GravityInLean/Goals/` and `Audit.lean` are unchanged; the only existing file changed is
`GravityInLean.lean` (eleven import lines).

Honest numbers: the lead started at about 22:33, the statements of all lemmas compiled at 22:42,
the nine jobs went out at 22:44 to 22:45, the first came back at 22:46 and the last at 22:49.
Every worker's proof passed on its first Lean run. No item turned out too hard and no statement
had to be changed. About 910 lines in all, 30 named results and definitions. The queue was the
only place anyone waited (up to about 2 min 50 s for one run).

## What the library has, and what it lacks

Read in `.lake/packages/mathlib/Mathlib/Analysis/ODE/` and `Analysis/Calculus/`:

* It has the paths (`IsPicardLindelof`, `ODE.FunSpace`), that they are unique (Grönwall), and that
  they depend continuously (Lipschitz) on the starting point.
* It does **not** have that they depend smoothly on the starting point. A search for `ContDiff`
  in `Analysis/ODE/` finds only smoothness in time.
* It has the theorem on solving smooth equations between complete spaces
  (`ContDiffAt.implicitFunction`, `ImplicitContDiff.lean`), with the answer smooth **at the one
  point**. For "infinitely smooth" that is weaker than smooth on a neighbourhood, so one lemma
  (`Implicit.lean`) is needed on top.
* It has the complete space of continuous paths `C(K, E)`, but not that "apply `f` along a path"
  is a smooth map of that space (`ComposeDeriv.lean`, `ComposeSmooth.lean`).

## The route chosen, and why

The inverse-function route, on the space of continuous paths over the fixed time span from `0`
to `1`, with the time as a factor: the path of `X` for the time `t` from `x`, read at its end, is
the path of `t • X` for the time `1` from `x`. These paths are the zeros of one smooth map
`pathMap X (t, x, γ) = γ - x - t • ∫ X ∘ γ`, whose slope in `γ` at `t = 0` is the identity. The
theorem on solving smooth equations then gives the path as a smooth function of `(t, x)`, and
reading a path at its end is linear and continuous, so smoothness in `t` and `x` *together* comes
at once.

Why not "differentiate under the equation": it needs paths of a second, linear equation on the
whole time span, a Grönwall estimate to show that they are the slope, and an induction with a
bigger system for every further derivative, none of which the library has ready. The route
chosen uses the library's theorem on solving equations as it stands; the only new analysis is
that composition is smooth on `C(K, E)`.

The paths themselves and the equation they obey are taken from the library (`LocalFlow.lean`);
`Rescale.lean` shows that they are zeros of `pathMap`, and the uniqueness part of the theorem on
solving equations identifies them with the smooth family.

## The lemmas

| item (`task:flows-…`) | file | what it says | who | given out | built | note |
|---|---|---|---|---|---|---|
| `path-space` | `PathSpace.lean` | words: `pathsIn`, `compMap`; paths inside an open region form an open set | m0-a0 | — | 22:42 | done by the lead |
| `apply` | `Apply.lean` | applying a path of linear maps to a path of vectors is linear and continuous in both | m0-a8 | 22:45 | 22:47 | merged; first Lean run passed |
| `integrate` | `Integrate.lean` | the integral of a path from `0` on is a linear, continuous map of paths | m0-a9 | 22:45 | 22:48 | merged; first Lean run passed |
| `compose-deriv` | `ComposeDeriv.lean` | "apply `f` along a path" has a slope, and which | m0-a1 | 22:45 | 22:49 | merged; first Lean run passed; helper `exists_uniform_radius` |
| `compose-smooth` | `ComposeSmooth.lean` | "apply `f` along a path" is smooth if `f` is | m0-a2 | 22:45 | 22:47 | merged; first Lean run passed |
| `implicit` | `Implicit.lean` | solving a smooth equation: the answer is smooth on a neighbourhood | m0-a3 | 22:45 | 22:46 | merged; first Lean run passed |
| `path-map` | `PathMap.lean` | the equation of a path is smooth, and its slope in the path has an inverse | m0-a4 | 22:45 | 22:47 | merged; first Lean run passed |
| `path-equation` | `PathEquation.lean` | the path is a smooth function of factor and starting point, and the only solution nearby | m0-a5 | 22:45 | 22:46 | merged; first Lean run passed |
| `local-flow` | `LocalFlow.lean` | the library's paths, with where they run | m0-a6 | 22:45 | 22:47 | merged; first Lean run passed |
| `rescale` | `Rescale.lean` | a path run at speed `t` solves the equation of a path | m0-a7 | 22:45 | 22:48 | merged; first Lean run passed |
| `smooth-flow` | `SmoothFlow.lean` | the goal, from the lemmas above | m0-a0 | 22:45 | 22:49 | built by the lead on the second Lean run (first: one elaboration error) |

"Built" means: the file builds through the queue with no hole of its own. Times of the workers'
rows are those of their reports and of the queue's log. Branches: git does not allow
`flows/<item>` next to a branch called `flows`, so the workers' branches are `flows-<item>`.

## Added by the supervisor, after the run

The text above is the team's own record, left as the lead wrote it. Checked afterwards on the
supervisor's PC:

- The clock of the trial started at 22:36:03 UTC, when all ten agents were ready (the lead's
  "about 22:33" is a guess). The whole project built with the proof at 22:50:14: 14 minutes.
- The queue's log agrees that every worker's file passed its first Lean run. The one failed run
  was the lead's first try of `SmoothFlow.lean`.
- Only `GravityInLean/Flows/` and eleven import lines in `GravityInLean.lean` differ from the
  commit the team started from. `GravityInLean/Goals/` and `Audit.lean` were not touched.
- Changed afterwards, without changing any statement's meaning: all eleven files got the
  project's usual form (`module`, `public import`); three files that loaded the whole standard
  library now load only what they need; `Integrate.lean` and `PathMap.lean` no longer assume
  that the space is complete, because nothing in them uses it.
- `Audit.lean` now holds `example : SmoothFlowStatement := smoothFlow`, so the build fails if
  the theorem ever stops proving the statement as it was fixed.

