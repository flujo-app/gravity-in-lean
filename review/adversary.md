# Adversarial review: `birkhoffNoCoordinates`

Snapshot: the repository at commit 600b6a2 (checked byte for byte). I read
Curved/Basic, Goal, Tables, Flat (in part), KnownAnswers (in part), Unique, Goals/Connection,
Goals/Turns (in part), Join/Goal, Audit, and for one question Join/ResultA and Join/CarrySmooth
in the repo (read only). I built nothing and ran nothing that changes state.

## How to read the risk (this decides which findings matter)

Lean has proved `∀ M g ξ s, Hyp → Concl`. A proved implication can mislead in only three ways:

1. **The hypotheses are too strong.** Real spherically symmetric vacuum space-times fail them, so
   the theorem says nothing about those cases. At worst they are unsatisfiable and the theorem
   says nothing at all.
2. **The conclusion is too weak.** Junk values, a tiny domain, an equation that holds for every
   metric.
3. **The words do not match the formulas.** Wrong signature, wrong coordinate order, wrong
   Schwarzschild formula.

A hypothesis that is too *weak* (too easy to satisfy) cannot make a proved theorem misleading: it
only makes it stronger. If, say, `IsEmptyOn` were true of some non-vacuum metric, Lean would have
proved that metric is Schwarzschild, which is false. That cannot happen with a sound proof, so it
would point to a soundness problem, not a meaning problem. So the brief's item 1 ("a metric with no
connection would count as empty for free") is the *harmless* direction. The dangerous direction is
the reverse: a genuine vacuum metric on some manifold for which no `cov` in the project's sense can
be shown to exist. Then `IsEmptyOn` (which is existential) is false for it and the theorem is silent
about it. That is finding 1.

## Findings, most serious first

### 1. Should mention in the paper, prominently (borderline must fix): "empty" includes "a connection exists", and that is proved only on flat coordinate space with its standard chart

- `Curved/Basic.lean:310-312`: `IsEmptyOn g s := ∃ cov, IsConnectionOf g cov s ∧ ∀ x ∈ s, ∀ v w,
  ricciAt cov x v w = 0`. It is **existential** (answer to the brief's question 1). Together with
  `IsConnectionOf.unique` (`Curved/Unique.lean:339`) it means "the Levi-Civita connection exists in
  our sense, and its Ricci tensor vanishes". The vanishing cannot be got by picking a convenient
  `cov`: two connections agree on every field that can be differentiated at the point, and
  `curvatureAt` only feeds `cov` fields that are smooth near `x` (`extend`, which is smooth on a
  trivialization domain, mathlib `VectorBundle/MDifferentiable.lean:715`). So there is no loophole.
- But `ConnectionExistsStatement` (`Goals/Connection.lean:244`) is **open**. The only proofs that
  some `cov` exists are for tables on `Coords 4` with the identity atlas
  (`IsRegularTableOn.isEmptyOn`, `isEmptyOn_iff`, used by `schwarzschild_isEmptyOn`). For a
  general `M` (the whole point of "no coordinates") nobody has shown that a single Ricci-flat
  metric satisfies `IsEmptyOn`.
- My own check: mathematically the genuine Levi-Civita connection *does* satisfy `IsConnectionOf`
  on any `M`. Take `cov σ x v = Dσ(v) + Γ(v, σ)` in the chart at `x` when `σ` is differentiable at
  `x`, and anything (say 0) otherwise. Mathlib's `IsCovariantDerivativeOn`
  (`CovariantDerivative/Basic.lean:92-100`) only constrains differentiable sections. `noTwist` and
  `keepsLengths` only need differentiability at `x`, and `mlieBracket` is the standard bracket
  (`lieBracket V W x = DW(V) − DV(W)`, `Analysis/Calculus/VectorField.lean:58`). So nothing is
  false here. The issue is one missing formal step, not a wrong idea.
- Why a referee would care: as it stands the honest reading is "Birkhoff's theorem, *assuming the
  Levi-Civita connection exists*". The README's trust list (`README.md:117-160`) does not say
  this. `ConnectionExistsStatement` appears only in the table of open statements (line 102),
  with no link to the headline theorem.
- How to close it, in order of effort:
  1. Prove `ConnectionExistsStatement` for nondegenerate (not only positive) metrics. The project
     notes that mathlib's `LeviCivita.lean` does the positive case.
  2. Cheaper: prove the converse of Result A's carry step. If a chart `c` turns `g` into a regular
     table that is Ricci-flat on `c.target`, then `IsEmptyOn g c.source`. Glue `cov` chart by
     chart; by uniqueness the pieces agree.
  3. Smallest test that shows the hypotheses can be met off flat space: a type synonym
     `M := Coords 4` with a *non-identity* `ChartedSpace` (charts given by a nonlinear
     diffeomorphism such as `t ↦ t + r³`), Schwarzschild's metric pushed onto it, and a proof of
     `IsSpaceTimeOn ∧ IsEmptyOn ∧ IsRoundOn ∧ UsableDistanceAt` there.

### 2. Should mention: what the statement does *not* say (all true of the classical theorem, none claimed here)

- **Local only.** `∃ m φ` is chosen per point `p` (`Curved/Goal.lean:171-178`). The theorem does
  not say that `m` is the same at two points of a connected `s`. That is mathematically true
  (`1 − 2m/r = g(∇r, ∇r)` is intrinsic) but not stated. The coordinate theorem `massFn_const`
  has it; the no-coordinates one does not.
- **Horizon left out.** `UsableDistanceAt g ξ p` (`Goal.lean:68-70`) exactly says "∇(r²) is not
  null at p" (if `d(sizeSq) = 0` then `n = 0` and `g n n = 0`, so a critical point is excluded too).
  Points on `r = 2m` are never covered. The classical theorem (local isometry to Kruskal) covers
  them. The README says this, and the paper must too.
- **Only one direction.** Schwarzschild satisfies the hypotheses (`schwarzschild_meets_goal`), but
  there is no theorem "Concl ⇒ the metric is empty and round near p". The untracked
  `Goals/ExactlyWhen.lean` seems to be about this.
- **Any real `m`.** `m ≤ 0` is allowed: `inside m = ∅` then (`KnownAnswers.lean:391`), so the chart
  lands in `outside m`. `m = 0` is Minkowski space in polar coordinates, `m < 0` is
  negative-mass Schwarzschild. Both are genuinely vacuum and round, so this is *correct* and no
  weakness, but a reader will ask. Say it.
- **Smooth of every order.** `IsSmoothOn` asks for `C^∞` (`Basic.lean:201-203`). Classical Birkhoff
  needs about `C²`. This is a narrower class, so it is fair to mention.
- The chart's domain may be disconnected and may hit both `outside m` and `inside m`. That is fine:
  one `m`, and the equation holds pointwise.

### 3. Should mention: the sanity checks are weaker than they look

- `schwarzschild_meets_goal` (`Goal.lean:183`) does use the *exact* predicates of the goal (not
  simplified copies), instantiated at `M = Coords 4` with the identity atlas. Good. But that is the
  one manifold on which "no coordinates" means nothing. See finding 1 for the test that fixes this.
- `schwarzschild_meets_conclusion` (`Goal.lean:197`) uses the identity chart (`ofSet`), so
  `mfderiv φ = id`. It cannot tell `g = φ* S` (right) from `g = (φ⁻¹)* S` or a transposed
  derivative. I checked by reading: `g q v w = S(φ q)(Dφ_q v, Dφ_q w)` is the pullback, the right
  way round. A test with teeth: the conclusion for Schwarzschild written in Eddington–Finkelstein
  coordinates on `Coords 4`, with `φ` the change back to Schwarzschild's labels (the project
  already has `inNewCoords_toSchw` and `eddington_*`). There `Dφ ≠ id`.
- No test shows the conclusion is *false* for a non-Schwarzschild metric (for example de Sitter
  near a point). The converse in finding 2 would give that for free, through `deSitter_not_isEmptyOn`.

### 4. Harmless (checked and ruled out, or cosmetic)

- **Smoothness uses the right bundle.** `IsSmoothOn` (`Basic.lean:201`) builds a `TotalSpace.mk'`
  whose fibre family is `fun x ↦ TangentSpace I x →L (TangentSpace I x →L ℝ)`. I worried that
  instance search might pick the trivial bundle, which would make the condition depend on the
  chart and too strong on a general `M`. It does not: `Join/CarrySmooth.lean:86` uses
  `ContMDiffOn.clm_bundle_apply₂` on `hg.smooth`, which only typechecks for the Hom bundle built
  over the tangent bundle. `isSmoothOn_flat_iff` (`Flat.lean:200`) checks the flat case.
- **Signature.** `HasOneTimeDirection` (`Basic.lean:81`): there is a `t` with `b t t < 0`, and the
  form is positive definite on `t^⊥` (3-dimensional, because `b t t ≠ 0`). That is signature (1,3)
  exactly. Nondegeneracy is derived.
- **Schwarzschild formula and coordinate order.** `roundG A B = diag(−A(r), B(r), r², r² sin²θ)`
  with `x 0 = t`, `x 1 = r`, `x 2 = θ`, `x 3 = φ` (`RoundSpacetime.lean:146-157`). `schwA m r =
  1 − 2m/r` and `schwB m r = (1 − 2m/r)⁻¹` (`OneMass.lean:72-75`). `tableMeasure` gives
  `Σ g_ab v_a w_b` (`Tables.lean:70`). So it is exactly
  −(1−2m/r)dt² + (1−2m/r)⁻¹dr² + r²dθ² + r² sin²θ dφ².
- **Junk values in the conclusion are fenced off.** `outside m = {0 < r, 2m < r, sin θ ≠ 0}` and
  `inside m = {0 < r < 2m, sin θ ≠ 0}` (`KnownAnswers.lean:388-391`). These exclude `r = 0` (where
  `2m/0 = 0` would give the junk value `A = 1`), `r = 2m` (where `0⁻¹ = 0`) and `sin θ = 0`. The
  conclusion has no `sqrt`, no `Classical.choose`, and no derivative of a non-differentiable map:
  `φ ∈ maximalAtlas`, so `φ` is smooth on its open `φ.source` and `mfderiv φ q` is the real
  derivative.
- **The domain is not degenerate.** `φ.source` is open in a 4-manifold and contains `p`, so it is
  never `{p}`.
- **Curvature conventions.** `curvatureOfFields` is `∇_X∇_Y Z − ∇_Y∇_X Z − ∇_[X,Y] Z`, and
  `ricciAt` traces the first slot. That is standard. The trace is independent of the basis, and
  `tangentSpaceCastModel` is the identity map (mathlib `IsManifold/Basic.lean:1054`). Tested:
  sphere `Ric = g`, de Sitter `Ric = 3/L² g`, so de Sitter is not empty (`KnownAnswers.lean:205,
  346, 363`).
- **Spherical symmetry.** `IsRoundOn` (`Basic.lean:338`): Killing fields (`LeavesUnchangedAt` is
  `L_ξ g = 0` in bracket form, correct for fields differentiable only at `x`), the so(3) brackets
  (either sign convention is reachable by negating all three), 2-dimensional spacelike orbits.
  That is the standard local definition. It is weaker than assuming a group action, which only
  helps. The normalization behind `sizeSq` is fixed by the brackets: every basis with these
  structure constants is an `SO(3)` rotation of every other, so `Σ g(ξᵢ, ξᵢ)/2` is basis-free.
- **Poles.** The hypotheses do not exclude the poles of the spheres. Only the chart avoids
  `sin θ = 0`, and it can always do so by rotating. So the README's "poles left out of every
  statement" is too pessimistic for this theorem.
- **Project hygiene.** No `instance`, `axiom`, `notation`, `macro`, `unsafe`, `implemented_by`,
  `native_decide`, `sorry` or kernel-skipping options anywhere under `GravityInLean/`
  (grep). `Audit.lean:185` checks `example : Curved.BirkhoffNoCoordinates :=
  birkhoffNoCoordinates`, so the proved statement is the fixed one, and audits its axioms.
- **Cosmetic.**
  - `M : Type` (universe 0 only).
  - The model is `Coords 4 = Fin 4 → ℝ` with the sup norm, not `EuclideanSpace`. This does not
    matter mathematically, but formally it is a different type.
  - `IsOpen s` is assumed twice (also inside `IsRoundOn`).
  - Hausdorff and second countable are not assumed, which makes the theorem more general.
  - The conclusion does not say `φ.source ⊆ s` (true in the proof, `ResultA.lean`, and a stronger
    conclusion without it).

## Verdict

The most serious finding is no. 1. "Empty" contains "a Levi-Civita connection exists in the
project's sense", and that has been shown only for metrics on flat coordinate space with its
standard chart. Mathematically it always holds, so the theorem is not wrong and not vacuous.
But until `ConnectionExistsStatement` (or a chart-gluing converse of Result A) is proved, the
honest formal reading on a general manifold is "Birkhoff's theorem, assuming the Levi-Civita
connection exists", and the trust list must say so.

Apart from that I found no way for the statement to be true for the wrong reasons. The
hypotheses are the standard ones, the conclusion is a genuine local isometry onto
Schwarzschild's outside or inside region, with no junk values and the right signature and order.
It deserves the name **"Birkhoff's theorem (local form, away from the horizon)"**, with the
qualifiers of finding 2 stated: local, horizon excluded, `m` not yet shown constant on connected
regions, only one direction, and `C^∞`.
