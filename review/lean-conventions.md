# Review: Lean conventions behind `birkhoffNoCoordinates`

Reviewer focus: do the Lean/mathlib conventions give the definitions in `Curved/Basic.lean` and
`Curved/Goal.lean` their intended meaning, and would the tests catch a wrong definition?
Snapshot read: the repository at commit 600b6a2. mathlib read at `.lake/packages/mathlib` (read only). For the proof
route I also read (read only) `GravityInLean/Join/ResultA.lean`, `Join/Carry*.lean` in the live
repo, since the snapshot's `Join/Goal.lean` imports them.

**Bottom line.** I found no definition that means something other than what is intended. The
conventions are consistent from start to end: signature, index order, curvature sign, which
slot the trace uses, bracket and torsion signs, and C^∞ smoothness. The main weaknesses are in
the **tests**: four of the goal's notions (`IsRoundOn`, `UsableDistanceAt`,
`LeavesUnchangedAt`, `IsSmoothOn`) have no failure test, and two parts of `HasOneTimeDirection`
are untested. In one case, `IsRoundOn.surfaces`, a single clause is the only thing that stops
every metric from counting as "round". Two comments are out of date, one of them in the goal file.

---

## 1. Conventions

**Signature and "one time direction".** `HasOneTimeDirection b := ∃ t, b t t < 0 ∧ ∀ v, b t v = 0 → v ≠ 0 → 0 < b v v`.
For a symmetric bilinear `b` on a finite-dimensional space this is exactly Lorentzian signature
in the (−,+,+,+) convention: `b t t ≠ 0` splits `V = ℝt ⊕ t^⊥`, and `t^⊥` is positive definite.
`HasOneTimeDirection.not_orthogonal` proves "exactly one" (no two orthogonal timelike vectors).
The same (−+++) convention is used in `roundG` (`-A dt² + B dr² + r² dθ² + r² sin²θ dφ²`), in
`IsRoundOn.positive` (the spheres are spacelike) and in the conclusion. They are consistent.
- Caveat: `not_orthogonal`'s proof only uses `0 ≤ b v v` on `t^⊥`. So it would still go through
  if the definition were weakened from `<` to `≤`, and it does not pin down the strictness.
  The strictness is load-bearing (it gives `nondegenerate`). Only a degenerate test would catch
  a `≤` slip (test 5b).

**Index order.** `Coords 4 = Fin 4 → ℝ` with index 0 = t, 1 = r, 2 = θ, 3 = φ (`gr`, `gθ`,
`roundDiag`, `sep`, rot fields acting on slots 2 and 3, `outside/inside` reading `x 1` as r and
`x 2` as θ). The goal's chart `φ : OpenPartialHomeomorph M (Coords 4)` lands in the same
`Coords 4`, and the conclusion feeds `φ q` to the same `roundG`/`outside`/`inside`. So the chart's
components are (t, r, θ, φ) by construction. Consistent. Minor: `outside`/`inside` require
`sin θ ≠ 0`, not `0 < θ < π`. That is harmless, because it is a statement about a chart patch.

**Curvature sign and trace slot.** `curvatureOfFields cov X Y Z = ∇_X∇_Y Z − ∇_Y∇_X Z − ∇_[X,Y] Z`
(with `cov σ x v = ∇_v σ`), the textbook `R(X,Y)Z`. `ricciAt cov x v w = tr(u ↦ R(u,v)w)`, the
standard contraction (Lee, do Carmo). Pinned by known answers that are not zero: unit 2-sphere
`Ric = g` (`sphere_curvature`), de Sitter `Ric = (3/L²) g` (`deSitter_curvature`), both via
`ricciAt_table`, which equates the Basic-level `ricciAt` with the coordinate formula `ricci`.
**"Ric = 0" does not depend on** the overall sign of R, on first-slot versus second-slot
contraction (they differ by a sign), on transposing Ric (symmetric for Levi-Civita), or on the
signature convention (g → −g leaves Γ, R^a_bcd and R_bd unchanged). **It does depend on** not
contracting the output with the third slot. `tr(u ↦ R(v,w)u)` is identically 0 for a
metric-compatible connection, which would make "empty" hold for every metric. The code contracts
the correct slot, and `deSitter_not_isEmptyOn` would catch the wrong one.

**Bracket, torsion, Killing signs.** mathlib `lieBracket V W x = DW(x)(V x) − DV(x)(W x)` is the
textbook `[V,W]`. `mlieBracket` pulls it back through `extChartAt I x₀`. `IsConnectionOf.noTwist`
(`∇_X Y − ∇_Y X = [X,Y]`) has exactly mathlib's `torsionAux` sign
(`CovariantDerivative/Torsion.lean`). `keepsLengths` is `X(g(Y,Z)) = g(∇_X Y,Z) + g(Y,∇_X Z)`.
`LeavesUnchangedAt` is `(L_ξ g)(X,Y) = ξ(g(X,Y)) − g([ξ,X],Y) − g(X,[ξ,Y]) = 0`. All are
correctly signed.

**`likeTurns` orientation.** `[ξ0,ξ1]=ξ2, [ξ1,ξ2]=ξ0, [ξ2,ξ0]=ξ1` is so(3) with one orientation.
The opposite orientation is reached by negating all three fields, and the theorem quantifies
over ξ. So no rotation-symmetric space-time is excluded by the sign. The relations also fix the
normalization, which is what makes `sizeSq = r²` (the sum of `g(ξᵢ,ξᵢ)` is invariant under the
SO(3) automorphisms of the basis).

**Basis independence of `ricciAt`.** `traceIn b F = Σ b.repr (F (b i)) i` equals
`LinearMap.trace` for linear `F` (`traceIn_eq_trace`, any basis). `stepBasis` is built with
`tangentSpaceCastModel`, which mathlib documents as "no mathematical meaning" (a definitional
bookkeeping device). That is fine here: it is only a basis, and the trace of a linear map does
not depend on the basis. Linearity of `u ↦ curvatureAt cov x u v w` is proven on flat space
(`ricciAt_flat`). On a general manifold it is supplied in the proof as the `hlin` hypothesis of
`Join.ricciAt_carry`, together with `traceIn_conj` (change of basis through `mfderiv c`). The
docstring of `stepBasis` points only to `Flat.lean` (finding D3).

**`TangentSpace` and `mfderiv φ q`.** `TangentSpace I x := E` is a definition (not reducible), so
on `M` a tangent vector at q is "components in `chartAt q`". `g q`, `mfderiv φ q` and every other
object use that same identification. So `mfderiv 𝓘 𝓘 φ q v` is `D(φ ∘ (chartAt q)⁻¹)(v)`, the
components of `v` in φ's chart (the target `Coords 4` has the identity chart). The conclusion
therefore says exactly `g = φ*(g_Schw)` on `φ.source`. Junk values cannot make it true
vacuously. If `φ` were not differentiable at `q`, `mfderiv` would be `0`, forcing `g q = 0`,
which contradicts nondegeneracy. In any case `φ ∈ maximalAtlas ∞` with `q ∈ φ.source` gives
differentiability. The option `backward.isDefEq.respectTransparency false` only affects
elaboration (it exploits `TangentSpace 𝓘(ℝ,E) x = E`). The kernel still checks everything.

**Smoothness level.** `∞` under `open scoped ContDiff` is `((⊤ : ℕ∞) : WithTop ℕ∞)`, i.e. C^∞,
not analytic `ω` (`FTaylorSeries.lean:120`). The manifold is `IsManifold 𝓘 ∞`. The metric is a
C^∞ section of the hom bundle on `s` (`IsSmoothOn`, checked against ordinary `ContDiffOn` by
`isSmoothOn_flat_iff`). The fields `ξ` are `CMDiff[s] ∞`.

**Where non-smooth data or junk could leak in, and why it does not:**
- `IsCovariantDerivativeOn` (mathlib) has only the sum and product rules on fields that are
  differentiable at the point. It does not require `cov` to send smooth fields to smooth fields,
  and it leaves `cov` free on non-differentiable fields. `IsEmptyOn` is `∃ cov`. This is safe:
  `IsConnectionOf.unique` (Koszul) pins `cov` on differentiable fields. `curvatureAt` only feeds
  `cov` with `extend` fields, which are smooth near x (`contMDiffAt_extend`), and with
  `y ↦ cov (extend w) y (extend v y)`, whose differentiability for any valid `cov` is
  `Join.mdiffAt_transport_along_of_isConnectionOf`. A convenient junk connection cannot make a
  curved metric "empty" (on flat space this is `ricciAt_eq_of_isConnectionOf`).
- `curvatureAt` depends on how mathlib's `extend` continues a vector. mathlib calls the details
  "mostly unspecified" (currently constant in `trivializationAt x`). The value of R is correct for
  any extension that is C² near x (tensoriality), so the definition is robust. The docstring
  describes an implementation detail (finding D3).
- `d%` of a non-differentiable function is `0`. In `UsableDistanceAt` this is conservative:
  `d% sizeSq = 0` forces `n = 0` by nondegeneracy, so the property fails. In `keepsLengths` and
  `LeavesUnchangedAt` the fields carry `MDiffAt` guards, and in the goal `g` is C^∞ on `s`.
- `schwB M r = (1 − 2M/r)⁻¹` is Lean's `0⁻¹ = 0` at the rim, so the Schwarzschild table is
  degenerate there. All Schwarzschild tests stay off the rim, which is correct.
- `ConnectionExistsStatement` is not proven. It is not needed for the theorem (`IsEmptyOn`
  asserts existence), but it means "empty" on a general manifold is only known to be satisfiable
  through examples.

## 2. The bridge

`IsRegularTableOn.isEmptyOn_iff` (Tables.lean) proves:
`IsEmptyOn (flatMeasure (tableMeasure g)) s ↔ ∀ x ∈ s, IsRicciFlatAt g ginv x`.
- Assumptions: `IsRegularTableOn g ginv s`, i.e. `s` open, every entry `C^∞` on `s`, symmetric on
  `s`, and `ginv` a two-sided inverse on `s` (the left inverse is stated, which suffices in finite
  dimensions). No signature assumption.
- Chart: only `M = Coords n` with its own identity chart (`𝓘(ℝ, Coords n)`), where a tangent
  vector *is* a coordinate vector. The `→` direction uses `ricciAt_eq_of_isConnectionOf` (any
  connection has the Christoffel curvature on flat space). The `←` direction uses the Christoffel
  transport.
- The same holds for `leavesUnchangedAt_table_iff`, `mlieBracket_fieldOf` and `ricciAt_table`:
  all on the identity chart.

**Is the final theorem affected by the "no real change of charts" gap? No, for soundness.** The
goal quantifies over every `M` with every atlas. The proof (`Join.resultA`) takes the genuine
chart `(chartAt p).restrOpen s` of an arbitrary `M` and carries each hypothesis through it:
`isSpaceTimeOn_carry`, `isRoundOn_carry`, `isEmptyOn_carry_of` with `curvatureAt_carry` and
`ricciAt_carry`, and `usableDistanceAt_carry`. Only then does it use the identity-chart bridge.
`birkhoffNoCoordinates` then composes with a second change of coordinates `Ψ` via
`mfderiv_trans_apply`. All of this is Lean-checked, so the M-to-chart direction across a real
chart is proven, not assumed.

**What the gap still leaves open: whether the hypotheses can be met on a manifold whose charts
are not the identity.** All known-answer tests, and `schwarzschild_meets_goal`, live on
`Coords 4` with the identity chart. If some definition only behaved well on the model space,
the theorem would still be true but empty for other manifolds. I rate this risk low. Every
definition is assembled from chart-invariant mathlib notions (`mfderiv`, `mlieBracket`,
`ContMDiffOn` of sections, `finrank` of spans, pointwise algebra on `TangentSpace`), and
`ricciAt_carry` is an equality, not just one direction. Tests 8 and 9 below close the gap
cheaply. This belongs in the paper as a stated limitation until then.

## 3. Test coverage

| Definition | Positive test (meets it) | Negative test (fails it) |
|---|---|---|
| `HasOneTimeDirection` | flat, de Sitter, Schwarzschild outside/inside (`hasOneTimeDirection_diag`, `round_oneTime_of_pos/neg`) | `sphere_noTime` (2-D, all positive), `not_hasOneTimeDirection_of_nonneg`. **Missing:** two time directions, (+−−−), degenerate (the `<` vs `≤` slip) |
| `Nondegenerate`, `IsLengthMeasureOn` | every regular table, `sphere_isLengthMeasureOn` | none |
| `IsSmoothOn` | every regular table (`isSmoothOn`) | none |
| `IsSpaceTimeOn` | flat, de Sitter, Schwarzschild in/out | none in 4-D |
| `IsConnectionOf` | Christoffel transport of any regular table | indirect only: `IsConnectionOf.unique` |
| `curvatureAt` / `ricciAt` | values: sphere `Ric = g`, de Sitter `Ric = 3/L² g`, flat and Schwarzschild 0 | (values themselves are the test) |
| `IsEmptyOn` | flat, Schwarzschild outside | `deSitter_not_isEmptyOn` |
| `LeavesUnchangedAt` | three turns on Schwarzschild | **none** |
| `IsRoundOn` | Schwarzschild outside only | **none** |
| `sizeSq` | value: `= r²` for round tables | n/a |
| `UsableDistanceAt` | Schwarzschild outside and inside (`round_usable`) | **none** |
| goal hypotheses | `schwarzschild_meets_goal` | none (no case where exactly one hypothesis fails) |
| goal conclusion | `schwarzschild_meets_conclusion` (identity chart) | none |

Two observations that sharpen the need for tests:
- **`IsRoundOn.surfaces` is the only clause that stops `ξ = 0` from making every metric round.**
  Zero fields are smooth, are Killing (`mlieBracket 0 X = 0`, `d% f x 0 = 0`), satisfy the bracket
  relations (`0 = 0`) and satisfy `positive` vacuously. Untested.
- A "non-round factor" such as `2 r² sin²θ dφ²` is **still locally round** (a cone-sphere has
  constant curvature 1) with respect to other fields. A failure test must therefore be phrased
  for the standard turns. A `∀ ξ, ¬ IsRoundOn` test needs a 2-surface whose curvature is not
  constant and is much harder (not proposed).

## 4. Comments that differ from the code

| # | Where | Comment says | Code / project says |
|---|---|---|---|
| D1 | `Curved/Goal.lean` module doc and `BirkhoffNoCoordinates` doc | "**It is a statement, not a theorem: `BirkhoffNoCoordinates` is not proved anywhere in this project yet.**" / "A statement, not yet a theorem." | Proved: `GravityInLean.birkhoffNoCoordinates` (`Join/Goal.lean`), checked in `Audit.lean`. Out of date. A comment-only fix leaves the statement and the `example` check in Audit untouched. |
| D2 | `IsConnectionOf` doc | "exactly one such connection. That is not shown here" | Uniqueness is proven (`IsConnectionOf.unique`, `connectionUnique`). Existence is still unproven (`ConnectionExistsStatement`). Half out of date. |
| D3 | `curvatureAt`, `stepBasis` docs | extension and basis independence "shown for flat coordinate space in `Flat.lean`"; `stepBasis` "Which basis it is does not matter" | True only when `u ↦ curvatureAt …` is linear. On a curved space that is provided in the proof by `Join` (`hlin`, `traceIn_conj`, `curvatureAt_carry`). "Same parts in the chart" describes mathlib's `extend` implementation, which mathlib calls unspecified. |
| D4 | `schwarzschild_usable_inside` doc | "Only on the rim itself it is not." | Not proved anywhere. At the rim the Schwarzschild *table* is degenerate in Lean (`0⁻¹ = 0`), so the claim is not even about a space-time there. Test 1 proves the real statement. |
| D5 | `IsRoundOn` doc | "the bracket of two of them is the third" | Only in cyclic order. `[ξ1,ξ0] = −ξ2`. Wording only. |
| D6 | goal doc | "there are a mass `m`" | `m : ℝ` of any sign. `m = 0` is Minkowski; for `m ≤ 0`, `inside m = ∅`. Correct for Birkhoff, but say "a real number m" in the paper. |

## Findings table

| # | Finding | Severity |
|---|---|---|
| F1 | Goal file says the goal is not proved (D1) | **must fix** (comment only) |
| F2 | No failure test for `IsRoundOn`; `surfaces` alone stops `ξ = 0` from making every metric round | **should test** (tests 3, 4, 6) |
| F3 | No failure test for `UsableDistanceAt`; the "rim" claim in D4 is unproved | **should test** (tests 1, 2) |
| F4 | `HasOneTimeDirection` strictness (`<`) not pinned: `not_orthogonal` survives `≤`; no (2,2) or (+−−−) test | **should test** (test 5) |
| F5 | Hypotheses only shown satisfiable on the identity chart; no non-vacuity test on a non-trivial chart or in non-adapted coordinates | **should test** (tests 8, 9), **mention in paper** until then |
| F6 | No failure test for `LeavesUnchangedAt` (including the differentiability guard) or for `IsSmoothOn` | should test (tests 6, 10, 11), low priority |
| F7 | `IsConnectionOf` doc half out of date (D2); `curvatureAt`/`stepBasis` docs point only to flat space (D3) | should fix (comments) |
| F8 | `IsCovariantDerivativeOn` imposes no smoothness on `cov` and `IsEmptyOn` is existential; safe because of Koszul uniqueness plus the Join differentiability lemma | mention in paper |
| F9 | Connection existence on a general manifold unproved (`ConnectionExistsStatement`) | mention in paper |
| F10 | Goal fine print: `M : Type` (universe 0), no Hausdorff or second-countable assumptions (more general), `m ∈ ℝ` of any sign, `φ.source` not required to lie in `s` (stronger), symmetry infinitesimal (Killing fields), statement local | mention in paper |
| F11 | Signature (−+++), index order (t,r,θ,φ), `R(X,Y)Z` sign, first-slot Ricci trace, bracket/torsion/Lie-derivative signs, C^∞ = `⊤ : ℕ∞`, `TangentSpace`/`mfderiv` identification | fine |
| F12 | "Ric = 0" independent of R sign, slot 1 vs 2, transpose and g → −g; the wrong slot (3) is excluded by the de Sitter test | fine (test 12 documents it) |
| F13 | `stepBasis` uses `tangentSpaceCastModel` ("no mathematical meaning" in mathlib); harmless for a trace of a linear map | fine |
| F14 | Junk values (`d%` = 0, `0⁻¹ = 0`, `cov` on non-differentiable fields) either guarded or conservative | fine |

## Proposed failure tests (and two positive controls), in priority order

Vocabulary from the project: `genG A B C S` (`-A dt² + 2C dt dρ + B dρ² + S dΩ²`), `onlyR`,
`zero2`, `one2`, `sqF`, `schwA`, `schwB`, `dsA`, `dsB`, `roundG`, `flatG`, `turns`, `fieldOf`,
`outside`, `deSitterRegion`, `genG_isRound`, `lieD_rotX`. Helper definitions are given where a
test needs one.

1. **The horizon fails "usable distance", and nothing else fails there** (Eddington-Finkelstein).
   ```lean
   noncomputable abbrev efG (M : ℝ) := genG (onlyR (schwA M)) zero2 one2 (onlyR sqF)
   def efRegion : Set (Coords 4) := {x | 0 < x 1 ∧ sin (x 2) ≠ 0}
   theorem ef_isSpaceTimeOn (M : ℝ) : IsSpaceTimeOn (flatMeasure (tableMeasure (efG M))) efRegion
   theorem ef_isEmptyOn (M : ℝ) : IsEmptyOn (flatMeasure (tableMeasure (efG M))) efRegion
   theorem ef_isRoundOn (M : ℝ) : IsRoundOn (flatMeasure (tableMeasure (efG M))) turns efRegion
   theorem ef_not_usable_on_rim {M : ℝ} (hM : 0 < M) {x : Coords 4} (hr : x 1 = 2 * M)
       (hs : sin (x 2) ≠ 0) : ¬ UsableDistanceAt (flatMeasure (tableMeasure (efG M))) turns x
   ```
   (Gradient of r² is `n = (2r, 2rA, 0, 0)` and `g(n,n) = 4r²A`, which is 0 at `A = 0`. The table
   has determinant `−r⁴ sin²θ ≠ 0`, so `n` is unique.) Catches: `UsableDistanceAt` without
   the non-null clause, or with `n` not tied to `d% sizeSq`. It also shows the hypothesis is
   *needed*: every other assumption of the goal holds at the rim. It is also the first test of
   `HasOneTimeDirection` and `IsEmptyOn` on a non-diagonal table (timelike `t = e₀ − ((1−A)/2) e₁`
   gives `g(t,t) = −1`), and it reuses `eddington_isEmptyOn`/`genG_isRound`.

2. **Spheres of fixed size: zero gradient** (flat 2-D times a unit sphere).
   ```lean
   noncomputable abbrev cylG := genG (fun _ _ ↦ 1) (fun _ _ ↦ 1) zero2 (fun _ _ ↦ 1)
   theorem cyl_isRoundOn : IsRoundOn (flatMeasure (tableMeasure cylG)) turns {x : Coords 4 | sin (x 2) ≠ 0}
   theorem cyl_not_usable {x : Coords 4} (hs : sin (x 2) ≠ 0) :
       ¬ UsableDistanceAt (flatMeasure (tableMeasure cylG)) turns x
   theorem cyl_not_isEmptyOn : ¬ IsEmptyOn (flatMeasure (tableMeasure cylG)) {x : Coords 4 | sin (x 2) ≠ 0}
   ```
   Catches: `UsableDistanceAt` accepting a zero gradient (`n = 0`). The first is also a positive
   `IsRoundOn` test where `sizeSq` (= 1) is not a coordinate.

3. **Zero fields are not "round"**, although they meet every other clause.
   ```lean
   theorem zero_not_isRoundOn :
       ¬ IsRoundOn (flatMeasure (tableMeasure flatG)) (fun _ ↦ 0) (Set.univ : Set (Coords 4))
   theorem zero_meets_other_clauses (x : Coords 4) :
       LeavesUnchangedAt (flatMeasure (tableMeasure flatG)) 0 x
         ∧ mlieBracket 𝓘(ℝ, Coords 4) (0 : Arrows 𝓘(ℝ, Coords 4) (Coords 4)) 0 x = 0
   ```
   Catches: `surfaces` dropped or weakened (for example `≤ 2`). Without it, every metric is round.

4. **Schwarzschild written in the (+,−,−,−) convention** fails both "space-time" and "round", but
   is still empty.
   ```lean
   theorem schw_flipped_not_isSpaceTimeOn (M : ℝ) :
       ¬ IsSpaceTimeOn (flatMeasure (-tableMeasure (roundG (schwA M) (schwB M)))) (outside M)
   theorem schw_flipped_not_isRoundOn (M : ℝ) :
       ¬ IsRoundOn (flatMeasure (-tableMeasure (roundG (schwA M) (schwB M)))) turns (outside M)
   theorem schw_flipped_isEmptyOn (M : ℝ) :
       IsEmptyOn (flatMeasure (-tableMeasure (roundG (schwA M) (schwB M)))) (outside M)
   ```
   Catches: a sign-convention mix-up between `HasOneTimeDirection`, `IsRoundOn.positive` and the
   Schwarzschild table, and a `positive` clause written as `≠ 0` or with a flipped sign. The third
   documents that emptiness does not depend on the convention. (Witness point:
   `![0, 2 * |M| + 1, π / 2, 0] ∈ outside M`.)

5. **"Exactly one" and "strictly positive".**
   ```lean
   noncomputable def twoTimeG (a b : Fin 4) : Coords 4 → ℝ :=
     fun _ ↦ if a = b then (if a = 0 ∨ a = 1 then -1 else 1) else 0
   theorem twoTime_not_isSpaceTimeOn :
       ¬ IsSpaceTimeOn (flatMeasure (tableMeasure twoTimeG)) (Set.univ : Set (Coords 4))
   noncomputable def flatDegG (a b : Fin 4) : Coords 4 → ℝ :=
     fun _ ↦ if a = b then (if a = 0 then -1 else if a = 3 then 0 else 1) else 0
   theorem flatDeg_not_hasOneTimeDirection (x : Coords 4) :
       ¬ HasOneTimeDirection fun v w : Coords 4 ↦ tableMeasure flatDegG x v w
   ```
   (5a: direct from `not_orthogonal` with `e₀`, `e₁`. 5b: take `v = e₃`.) Catches: "at least one
   time direction", and `0 < b v v` weakened to `0 ≤ b v v`, which `not_orthogonal` does not
   catch.

6. **A non-round factor fails for the standard turns** (a squashed sphere), while the axial turn
   survives.
   ```lean
   noncomputable def squashG (M : ℝ) : Fin 4 → Fin 4 → Coords 4 → ℝ :=
     diag fun i x ↦ (if i = 3 then 2 else 1) * roundDiag (schwA M) (schwB M) i x
   theorem squash_not_leavesUnchanged (M : ℝ) {x : Coords 4} (hx : x ∈ outside M)
       (hφ : cos (x 3) ≠ 0) :
       ¬ LeavesUnchangedAt (flatMeasure (tableMeasure (squashG M))) (turns 1) x
   theorem squash_leavesUnchanged_axis (M : ℝ) {x : Coords 4} (hx : x ∈ outside M) :
       LeavesUnchangedAt (flatMeasure (tableMeasure (squashG M))) (turns 2) x
   theorem squash_not_isRoundOn (M : ℝ) :
       ¬ IsRoundOn (flatMeasure (tableMeasure (squashG M))) turns (outside M)
   ```
   (`(L_{rotX} g)_{θφ} = r² cos φ (c − 1)` with `c = 2`; use `leavesUnchangedAt_table_iff` and
   `lieD_rotX`.) Catches: a Killing condition that is too weak, for example missing a bracket
   term, or only constraining `g(ξ,ξ)`. Note: the squashed sphere is still locally round for
   *other* fields, so do not phrase this as `∀ ξ`.

7. **Positive control: de Sitter meets every hypothesis except emptiness.**
   ```lean
   theorem deSitter_isRoundOn (L : ℝ) :
       IsRoundOn (flatMeasure (tableMeasure (roundG (dsA L) (dsB L)))) turns (deSitterRegion L)
   theorem deSitter_usable {L : ℝ} {x : Coords 4} (hx : x ∈ deSitterRegion L) :
       UsableDistanceAt (flatMeasure (tableMeasure (roundG (dsA L) (dsB L)))) turns x
   ```
   With the existing `deSitter_isSpaceTimeOn` and `deSitter_not_isEmptyOn`. Catches: an
   `IsRoundOn` proof that only works for Schwarzschild's A, B, and it shows that emptiness is the
   hypothesis doing the work. (Best done as one lemma `round_isRoundOn A B s`.)

8. **A real change of coordinates: de Sitter is not Schwarzschild in any chart.**
   ```lean
   theorem deSitter_not_locally_schwarzschild {L : ℝ} (hL : 0 < L) {p : Coords 4}
       (hp : p ∈ deSitterRegion L) :
       ¬ ∃ (m : ℝ) (φ : OpenPartialHomeomorph (Coords 4) (Coords 4)),
           φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ (Coords 4) ∧ p ∈ φ.source ∧
           ∀ q ∈ φ.source, (φ q ∈ outside m ∨ φ q ∈ inside m) ∧
             ∀ v w : TangentSpace 𝓘(ℝ, Coords 4) q,
               flatMeasure (tableMeasure (roundG (dsA L) (dsB L))) q v w
                 = flatMeasure (tableMeasure (roundG (schwA m) (schwB m))) (φ q)
                     (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q v)
                     (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q w)
   ```
   Catches: a conclusion that can be met trivially, an `mfderiv` used the wrong way round, and
   "empty" depending on the chart. It needs emptiness carried *back* from a chart (chart to
   space), the direction no test has exercised. The coordinate lemma `isRicciFlatAt_changeOfCoords`
   plus `CarryPointwise.slopeEquiv` should suffice.

9. **Positive control in non-adapted coordinates: Minkowski with Cartesian rotations, poles included.**
   ```lean
   /-- Turns about the y-, x- and z-axes as linear fields on (t, x, y, z). -/
   noncomputable def cartTurns : Fin 3 → Arrows 𝓘(ℝ, Coords 4) (Coords 4) :=
     ![fieldOf ![fun _ ↦ 0, fun p ↦ p 3, fun _ ↦ 0, fun p ↦ -p 1],
       fieldOf ![fun _ ↦ 0, fun _ ↦ 0, fun p ↦ -p 3, fun p ↦ p 2],
       fieldOf ![fun _ ↦ 0, fun p ↦ -p 2, fun p ↦ p 1, fun _ ↦ 0]]
   def awayFromCentre : Set (Coords 4) := {x | x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 ≠ 0}
   theorem minkowski_isRoundOn :
       IsRoundOn (flatMeasure (tableMeasure flatG)) cartTurns awayFromCentre
   theorem minkowski_usable {x : Coords 4} (hx : x ∈ awayFromCentre) :
       UsableDistanceAt (flatMeasure (tableMeasure flatG)) cartTurns x
   ```
   (Order chosen so that `[ξ0,ξ1]=ξ2` with mathlib's bracket. `sizeSq = x²+y²+z²`.) Catches:
   definitions that secretly rely on the spherical-coordinate form of the turns (`surfaces`,
   `positive`, `sizeSq` normalization), and it covers the poles that every current test cuts out.
   Feeding it to `birkhoffNoCoordinates` is an end-to-end smoke test.

10. **The differentiability guard in "unchanged" matters.**
    ```lean
    theorem kink_not_leavesUnchangedAt :
        ¬ LeavesUnchangedAt (flatMeasure (tableMeasure flatG))
          (fieldOf ![fun p ↦ |p 1|, fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0]) 0
    ```
    Catches: removal of the `MDiffAt (T% ξ) x` conjunct. Without it, a non-differentiable field
    vanishing at `x` passes, because `mlieBracket` junk is 0 (the bug the second reading found).

11. **Smoothness can fail.**
    ```lean
    noncomputable def kinkG (a b : Fin 4) : Coords 4 → ℝ :=
      fun x ↦ if a = b then (if a = 0 then -1 else 1 + |x 1|) else 0
    theorem kink_not_isSmoothOn :
        ¬ IsSmoothOn (flatMeasure (tableMeasure kinkG)) (Set.univ : Set (Coords 4))
    ```
    Catches: an `IsSmoothOn` that is vacuous (wrong bundle, or smoothness order 0).

12. **Documentation lemma: emptiness does not depend on the signature convention** (any manifold).
    ```lean
    theorem isEmptyOn_neg_iff {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
        {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        {g : LengthMeasure I M} {s : Set M} :
        IsEmptyOn (-g) s ↔ IsEmptyOn g s
    ```
    (The same `cov` works: `noTwist` does not mention `g`, and `keepsLengths` is linear in `g`.)
    Pins the claim in F12 inside Lean.
