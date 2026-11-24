# Do the words mean what physicists mean?

A review of the definitions and of the final statement of the coordinate-free Birkhoff theorem
(`birkhoffNoCoordinates`, PR #40), made on 24 November 2026 at commit 600b6a2.

**Why this is needed.** Lean checks that every step of the proof is right. It cannot check that the
definitions ("empty", "looks the same from every side", "space-time", ...) and the final statement
mean what a physicist means by those words. That part needs reading.

**Who read it.** Three independent AI reviewers who were given only the files, each with one task:

| Reviewer | Task | Notes |
|---|---|---|
| The relativist | Compare every definition and the final statement with the standard textbooks (Wald, O'Neill, Hawking and Ellis, Carroll). | [review/relativist.md](review/relativist.md) |
| The adversary | Look for any way the statement could be true for the wrong reasons, or say less than it seems to. | [review/adversary.md](review/adversary.md) |
| The Lean expert | Check the conventions the definitions rely on, and which tests would catch a wrong definition. | [review/lean-conventions.md](review/lean-conventions.md) |

No human expert has read it. AI reviewers can share blind spots with the AI that wrote the
definitions, so a human reading is still welcome (issue #34).

## The verdict

**No definition was found wrong, and no way was found for the statement to be true for the wrong
reasons.** All three reviewers agree that it deserves the name *Birkhoff's theorem, in its local
form, away from the horizon, from symmetry assumptions without coordinates*, with the limits
below stated wherever it is claimed.

The claim, in the words a paper should use (the relativist's wording, with the adversary's
limit added):

> Let g be a smooth Lorentzian metric on a 4-manifold that is Ricci-flat, with its Levi-Civita
> connection, on an open set carrying three Killing fields with the commutation relations of
> so(3), whose orbits are 2-dimensional and spacelike. Then every point of that set at which the
> gradient of the area radius is not null has a neighbourhood isometric to an open subset of the
> Schwarzschild exterior (r > 2m) or interior (0 < r < 2m), for some real m (m ≤ 0 included).

## Checked and found right

| What | Finding |
|---|---|
| Space-time | Exactly one time direction and three space directions (signature −+++). |
| Coordinates | The same order everywhere: time, distance, then the two angles. |
| Schwarzschild's formula | Exactly −(1−2m/r)dt² + (1−2m/r)⁻¹dr² + r²dθ² + r² sin²θ dφ². |
| Curvature and its trace | The textbook sign and the standard trace. "Empty" comes out the same whatever sign conventions are used; the one wrong choice that would matter gives zero for every space-time, and the de Sitter test would catch it. |
| "Empty" | Means: there is a connection of the right kind (shown to be the only one), and its curvature trace is zero. Einstein's equation without matter and without a cosmological constant. |
| "Unchanged along a field" | The textbook condition for a symmetry (a Killing field). |
| "Looks the same from every side" | Asks only for the small turns, not a whole group of rotations. That makes the theorem slightly *stronger* than the textbook version. |
| Size of the spheres | A neat definition without coordinates (half the sum of the squared lengths of the three fields), which gives r². |
| "Usable distance" | Means: the area radius does not grow along a path of light. In empty space this fails only on the horizon, r = 2m. |
| The conclusion | Really says that around the point, the metric *is* Schwarzschild's, for every pair of directions, on an open neighbourhood (never just one point). |
| Meaningless values | Where Lean gives a meaningless value (dividing by zero, a derivative that does not exist), the definitions guard against it or the statement fails. Nothing can be made true by accident. |
| The poles | Not left out of the space-time; only the map avoids them. The README undersold this. |
| Mass | Any real number, including zero (flat space-time) and negative, as it should be. |

## What the theorem does not say

These limits must be stated wherever the theorem is claimed.

1. **Away from the horizon.** Points on r = 2m are excluded. Covering them is issue #39.
2. **Local.** Each point gets its own mass m. That one m serves a whole connected region is not
   shown. (Cheap to add: the quantity (r/2)(1 − |grad r|²) is constant on a connected region.)
3. **"Empty" includes "the connection exists".** That a metric has such a connection is proved
   so far only on plain coordinate space with its standard chart (`ConnectionExistsStatement` is
   still open). Nothing is false, but until it is proved, the honest reading on a general curved
   space is "assuming the Levi-Civita connection exists". The next team run is to close it, by
   porting TauCeti's proof with credit.
4. **Infinitely smooth.** The metric is assumed infinitely differentiable; the textbook theorem
   needs only two derivatives.
5. **No cosmological constant**, no charge. (Hawking and Ellis also treat the charged case.)
6. **One direction.** Schwarzschild meets the assumptions; the converse ("exactly when") is the
   next piece of work.

**Earlier work on paper.** A proof of Birkhoff's theorem that avoids coordinates already exists on
paper: H.-J. Schmidt, [A new proof of Birkhoff's theorem](https://arxiv.org/abs/gr-qc/9709071)
(1997). So what is new here is the machine check, not a coordinate-free proof as such.

## To do before any claim

Handed to the work on the Lean files:

- **Comments that are out of date** (no change to any statement): `Curved/Goal.lean` still says
  the goal is "not proved anywhere"; `Curved/Basic.lean` says uniqueness of the connection is
  "not shown here"; the comment of `schwarzschild_usable_inside` says usable distance fails "only
  on the rim itself", which is proved nowhere; a comment credits `Flat.lean` for a fact that comes
  from `Join/`.
- **Close limit 3:** prove `ConnectionExistsStatement`.
- **Close limit 2:** one mass for a connected region.
- **Tests that show the definitions can fail.** So far several conditions have never been shown
  to fail on any example. Proposed, most important first (exact Lean statements in
  [review/lean-conventions.md](review/lean-conventions.md)):
  1. On the horizon, in Eddington–Finkelstein coordinates, every assumption holds except usable
     distance.
  2. A sphere of fixed size times a flat plane is round, but not usable and not empty.
  3. Three zero fields fail "looks the same from every side".
  4. Schwarzschild written with the opposite sign convention fails "space-time" but is still
     empty.
  5. A metric with two time directions fails "space-time"; a degenerate one fails "one time
     direction".
  6. A squashed sphere fails "unchanged" for one standard turn while another still works.
  7. De Sitter is round and usable, so emptiness is the only assumption it breaks.
  8. De Sitter is not Schwarzschild in any chart: the first real test across a change of charts.
  9. Flat space-time with ordinary rotations is round and usable, poles included.
  10. A field that cannot be differentiated fails "unchanged".
  11. A metric with a kink fails "smooth".
  12. "Empty" is the same for g and −g.
