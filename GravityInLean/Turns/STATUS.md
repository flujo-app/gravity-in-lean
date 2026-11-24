# Turns: status of the team's work on `turnsCoordinates`

Goal: `theorem turnsCoordinates : TurnsCoordinatesStatement` (statement 2 of `Goals/Turns.lean`).
Times are UTC on 23 November 2026, read from the queue's log and the message times. Lead: `m0-a0`.

## Result

**Goal reached at 23:41 UTC.** `theorem turnsCoordinates : TurnsCoordinatesStatement` is in
`TurnsCoordinates.lean`, all twenty files of `Turns/` are imported by `GravityInLean.lean`, and
the whole project builds through the queue (`scripts/queued-build.sh`: `Build completed
successfully (7481 jobs)`, 18 s, ended 23:41:18), `Audit.lean` included: "all 1243 declarations
under GravityInLean checked: none rests on more than [propext, Classical.choice, Quot.sound]"
(1147 before). A scratch check `example : GravityInLean.TurnsCoordinatesStatement :=
GravityInLean.turnsCoordinates` passes, and `#print axioms` names the same three.
`GravityInLean/Goals/` and `Audit.lean` are unchanged; the only existing file changed is
`GravityInLean.lean` (twenty import lines). No file has a `sorry` or an `axiom`.

Honest numbers:

* The lead started at 23:24:30. Reading and the paper check of the route took until 23:28.
* First round, nine lemmas that do not depend on each other, with the statements written in the
  messages (the workers made the files): given out 23:29 to 23:30, built 23:30:47 to 23:33:25,
  merged 23:35.
* The goal proved from the lemmas, second-round proofs still open: built 23:36:05 (third run;
  the first two failed on a missing import in a stub of the lead's, not in the proof).
* Second round, nine lemmas with statements fixed in files by the lead: given out 23:37 to
  23:38, built 23:38:55 to 23:40:20, merged 23:40:54.
* Whole project with the audit: 23:41:18. From the lead's start to the goal: 17 minutes.
* No statement had to be changed, no item turned out too hard, nobody reported being stuck.
  Failed Lean runs (queue log, 9 of 74 runs up to 23:43): 6 in the first round (5 workers), 1 in the second,
  2 by the lead. 2067 lines of Lean in 20 files, 71 named results and definitions. The longest wait in the queue was 12 s.
* Not done by the lead: a separate reading of each worker's proof text. The build and the audit
  are the check.

## The route chosen, and why

The supervisor's route, with step 3 done differently.

1. **Rotation.** At `p` the three arrows span two directions, so a unit mix `n` of them is zero
   (`exists_unit_kernel`). A rotation `R` with middle row `n` (`exists_rotation_row`) gives
   `η i = ∑ j, R i j • ξ j` (`rotated`), still combining like turns (`likeTurns_rotate`), with
   `η 1 p = 0`, spanning two directions everywhere (`span_rotate`).
2. **Carrying a field along a flow.** For the flow of `Z`: `A t = D(flow t)(x) (Y x)` solves
   `A' = DZ(flow t x) A` (`hasDerivAt_fderiv_flow`, from the symmetry of second slopes of the
   jointly smooth flow). A mix of fields at the place reached solves the same equation, by the
   brackets. Linear equations have one solution (`linear_ode_unique`, Grönwall). This gives
   `fderiv_flow_self` and `fderiv_flow_pair`. Only the direct form (slope of the flow applied to
   a field at the start) is used, so no inverse of the flow and no uniqueness of flows is needed.
3. **Where `η 1` rests: changed.** The route's unit vector `n q` (smooth, unique up to sign) is
   not used. Instead: `η 1 q = 0` as soon as `η 1 q` is at right angles (ordinary dot product)
   to `η 0 q` and `η 2 q`, while these two are independent (`eq_zero_of_dot_eq_zero`, uses the
   two directions). So the surface is the zero set of the two smooth functions
   `restMap η = (η 0 ⬝ η 1, η 2 ⬝ η 1)`: no division, no choice of sign. Their slopes at `p`
   along `η 0 p`, `η 2 p` come from the brackets (`D η 1 (p) η 0 p = η 2 p`,
   `D η 1 (p) η 2 p = -η 0 p`, because `η 1 p = 0`), and the 2×2 determinant is the Gram
   determinant of `η 0 p`, `η 2 p`, positive. The theorem on solving smooth equations
   (`Flows/Implicit.lean`) gives the surface `σ` (`exists_levelSurface`, `exists_restSurface`).
4. **Coordinates.** `chart σ χ ψ y = ψ (y 3) (χ (y 2 - π / 2) (σ (y 0, y 1)))` with `χ`, `ψ` the
   flows of `η 0`, `η 2` from `smoothFlow`; start `(0, 0, π / 2, 0)`.
5. **Equations.** Two relations (`chart_relations`): the slope along `y 2` is
   `cos (y 3) • η 0 - sin (y 3) • η 1`, and
   `sin (y 3) • η 0 + cos (y 3) • η 1 + cot (y 2) • η 2 = 0` at the place reached. The three
   equations of the standard turns follow by algebra (`turns_of_relations`).

Not used from `TurnsOn`: `unchanged` (Killing's equation) and `positive`. Not used: `ginv` and
the table `g`, except that the region is open.

## The lemmas

| item (`task:turns-…`) | file | what it says | who | given out | built | note |
|---|---|---|---|---|---|---|
| `basic` | `Basic.lean` | words: `vec`, `lieB`, `IsLocalFlow`; a flow exists (`smoothFlow`) | m0-a0 | — | 23:29 | lead |
| `rotation` | `Rotation.lean` | a rotation with a given unit middle row | m0-a1 | 23:29 | 23:31 | merged 23:35; first run passed (a later edit failed once, then passed 23:32) |
| `rotate-bracket` | `RotateBracket.lean` | rotated fields still combine like turns | m0-a2 | 23:29 | 23:31 | merged 23:35; 2 failed runs |
| `kernel` | `Kernel.lean` | a unit mix of the three arrows is zero; rotation keeps the span | m0-a3 | 23:29 | 23:30 | merged 23:35; first run passed |
| `gram` | `Gram.lean` | independence of two arrows by the Gram determinant; right angles force zero | m0-a4 | 23:30 | 23:32 | merged 23:35; 1 failed run |
| `complete` | `Complete.lean` | two independent arrows completed to four; column operations | m0-a5 | 23:30 | 23:33 | merged 23:35; first run passed |
| `level-set` | `LevelSet.lean` | the zero set of two smooth functions is a surface | m0-a6 | 23:30 | 23:33 | merged 23:35; first run passed |
| `linear-unique` | `LinearUnique.lean` | a linear equation has one solution | m0-a7 | 23:30 | 23:31 | merged 23:35; first run passed |
| `variational` | `Variational.lean` | how the slope of a flow changes with time | m0-a8 | 23:30 | 23:32 | merged 23:35; 1 failed run |
| `bracket-fderiv` | `BracketFderiv.lean` | the goal file's bracket and table of slopes in the library's words | m0-a9 | 23:30 | 23:32 | merged 23:35; 1 failed run |
| `goal` | `TurnsCoordinates.lean` | the goal, from the lemmas | m0-a0 | — | 23:36 | from the lemmas; closed for good with the whole build at 23:41 |
| `chart` | `Chart.lean` | the chart: domain open, start, stays in the region | m0-a1 | 23:37 | 23:39 | merged 23:40; first run passed |
| `chart-smooth` | `ChartSmooth.lean` | the chart is smooth | m0-a5 | 23:37 | 23:38 | merged 23:39; 1 failed run |
| `chart-slopes` | `ChartSlopes.lean` | the slopes of the chart along the four steps | m0-a7 | 23:37 | 23:40 | merged 23:40; first run passed |
| `transport` | `Transport.lean` | two fields carried by a flow: cosine and sine mix | m0-a8 | 23:37 | 23:39 | merged 23:39; first run passed; helper `fderiv_flow_mix` |
| `transport-self` | `TransportSelf.lean` | a flow carries its own field to itself | m0-a3 | 23:37 | 23:38 | merged 23:39; first run passed |
| `rest-map` | `RestMap.lean` | the two dot products: smooth, slope, Gram continuous | m0-a4 | 23:37 | 23:39 | merged 23:40; first run passed |
| `surface` | `Surface.lean` | the surface where `η 1` rests | m0-a6 | 23:37 | 23:40 | merged 23:40; first run passed |
| `turn-algebra` | `TurnAlgebra.lean` | from two relations to the three standard turns | m0-a9 | 23:37 | 23:39 | merged 23:40; first run passed |
| `relations` | `Relations.lean` | the two relations of the chart | m0-a2 | 23:37 | 23:39 | merged 23:40; first run passed |

"Built" means: the file builds through the queue with no hole of its own. Branches are
`turns-<item>`.

## Added by the supervisor, after the run

The text above is the team's own record, left as the lead wrote it. Checked afterwards on the
supervisor's PC:

- The clock of the run started at 23:24:36 UTC, when all ten agents were ready. The whole
  project built with the proof at 23:41:18 (the queue's log): 16 minutes 42 seconds.
- The queue's log agrees with the counts above: 52 runs until the goal, 9 of them failed.
- Only `GravityInLean/Turns/` and twenty import lines in `GravityInLean.lean` differ from the
  commit the team started from. `GravityInLean/Goals/` and `Audit.lean` were not touched.
- Rebuilt from nothing through the queue: no warnings, all 1,243 declarations pass the audit.
  Nothing in the files was changed afterwards.
- `Audit.lean` now holds `example : TurnsCoordinatesStatement := turnsCoordinates`, so the
  build fails if the theorem ever stops proving the statement as it was fixed.
- Not checked by anyone but its author: whether each lemma's comment says what its Lean
  statement says.

