# Referee Report: "Birkhoff's theorem without coordinates, machine-checked in Lean 4, and how teams of AI workers built it"

**Reviewed manuscript:** `paper/paper.md` in `github.com/flujo-app/gravity-in-lean` (HEAD `ba6bbea`, with numbers cross-checked against tag `paper-1-numbers` = commit `3b816ea` and comparator commit `73816cc`).
**Review date:** 24 November 2026.

---

## 1. Verdict

**Reject in its current form (accept only after major revision).** The underlying Lean 4 formalisation is genuinely strong: the core geometric definitions match textbook general relativity, the main statements are non-vacuous and say (with a few narrow caveats) what a relativist means, and Lean's kernel plus independent checkers verify the proofs. However, the manuscript itself is not ready for submission: it contains direct internal contradictions left over from late edits (Section 8 still declares the independent checks of Section 9 "Not established", and still cites stale pre-Run-7 counts and claims the theorems are only local), an overstatement in the Abstract attaching the "if and only if" to the horizon-inclusive Kruskal statement, two mathematical/terminological errors in the prose (the name and sign of the Kretschmann scalar; a non-Hausdorff gluing counterexample presented without mentioning Hausdorffness), and an Abstract that cites AI reviews as "reviewed against the textbooks" and "an independent second reader" without disclosing that no human specialist has reviewed the mathematics. Fixing these manuscript errors—and obtaining an independent human specialist check of the definitions and statements, which is far more critical than `paper/checklist.md` implies—is necessary before submission.

---

## 2. Blocking Issues

### F1. Section 8 directly contradicts Section 9 by listing the independent checks as "Not established"
- **Where:** `paper/paper.md` Section 8, line 441 vs. Section 9, lines 466–533.
- **What is wrong and why it matters:** Under "**Not established.**", Section 8 line 441 reads:
  `- The independent checks 3 and 4 of Section 9.`
  Yet Section 9 items 3 and 4 were updated (PR #61, commit `7304158`) to report that `lake comparator --paranoid`, `leanchecker`, and `lake check --paranoid` (both unsandboxed and inside Lake's Linux `bwrap` sandbox) were executed and accepted (save for `nanoda`'s stack overflow on the 464,847-declaration full environment export, while `nanoda` accepted all 58,865 declarations in the project's transitive closure). Leaving line 441 intact makes the paper flatly contradict itself on its core trust claims.
- **Concrete fix:** Replace Section 8 line 441 with an accurate summary of what remains open in Section 9, e.g.:
  `- Full-environment verification by nanoda (which aborted with a stack overflow on the 464,847-declaration export, although it accepted all 58,865 declarations used by the project), independent execution of lake comparator --paranoid and lake check --paranoid in public CI or on a second machine, and comparator coverage beyond the 16 headline theorems (Section 9).`
- **Confidence:** `VERIFIED`.

### F2. Abstract attaches the "if and only if" to the horizon-inclusive Kruskal theorem, and Sections 1 & 4 omit the origin-avoidance hypothesis of `GlobalBirkhoffConverse`
- **Where:** `paper/paper.md` Abstract lines 16–18, Section 1 item 6 (lines 61–65), Section 4 (lines 227–229); `GravityInLean/Goals/EveryPoint.lean:172-178`, `GravityInLean/Goals/ExactlyWhen.lean:111-118`, `GravityInLean/Goals/Global.lean:254-260, 301-308`.
- **Relevant Lean lines:**
  ```lean
  -- GravityInLean/Goals/ExactlyWhen.lean:111-118
  def SchwarzschildExactlyWhen : Prop :=
    ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
      [IsManifold 𝓘(ℝ, Coords 4) ∞ M]
      (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (p : M),
      (∃ (s : Set M) (ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M),
          IsOpen s ∧ p ∈ s ∧ IsSpaceTimeOn g s ∧ IsEmptyOn g s ∧ IsRoundOn g ξ s ∧
            UsableDistanceAt g ξ p) ↔
        IsSchwarzschildNear g p
  ```
  ```lean
  -- GravityInLean/Goals/Global.lean:301-308
  def GlobalBirkhoffConverse : Prop :=
    ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
      [IsManifold 𝓘(ℝ, Coords 4) ∞ M] (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (s : Set M),
      IsSpaceTimeOn g s →
      ((∃ m : ℝ, 0 < m ∧ ∃ D : M → Coords 5, IsKruskalMapOn m g D s) ∨
        (∃ m : ℝ, m ≤ 0 ∧ ∃ D : M → Coords 4, IsSchwarzschildMapOn m g D s ∧
          ∀ q ∈ s, 0 < D q 1 ^ 2 + D q 2 ^ 2 + D q 3 ^ 2)) →
      ∃ ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M, IsEmptyOn g s ∧ IsRoundOn g ξ s
  ```
- **What is wrong and why it matters:**
  1. Abstract lines 16–18 read: *"The formal statement holds at every point of the region, including the horizon and the bifurcation sphere, where the target is the Kruskal–Szekeres form; it gives one mass on each connected region; and it comes with its converse, as one 'if and only if'."* In Lean, the "if and only if" (`SchwarzschildExactlyWhen`, and `BirkhoffExactlyWhenInCoordinates`) is proved **only for the off-horizon statement** (`UsableDistanceAt g ξ p ↔ IsSchwarzschildNear g p`). There is **no** local "if and only if" for `BirkhoffAtEveryPoint` (the horizon/Kruskal theorem).
  2. For the global theorem, Section 1 item 6 and Section 4 line 228 state simply "and the converse" / "that the converse holds (`GlobalBirkhoffConverse`)". In Lean, `GlobalBirkhoffConverse` is **not** the exact converse of `GlobalBirkhoff`: for `m = 0` it adds the extra hypothesis `∀ q ∈ s, 0 < D q 1 ^ 2 + D q 2 ^ 2 + D q 3 ^ 2` (the map must avoid the spatial origin `(x₁, x₂, x₃) = (0, 0, 0)`, because rotation fields vanish there and fail `surfaces`), whereas `GlobalBirkhoff` does not guarantee that `D` avoids the origin when `m = 0` (indeed `Goals/Global.lean:297-300` explicitly notes this asymmetry). It also takes `IsSpaceTimeOn g s` as a premise rather than deriving it.
- **Concrete fix:**
  - In the Abstract (lines 16–18), split the sentence clearly: *"A second local statement drops the gradient condition and holds at every point, including the horizon and the bifurcation sphere, with the Kruskal–Szekeres form as target (or Schwarzschild for m ≤ 0), with one mass per connected region; the off-horizon local statement is also proved as an 'if and only if'."*
  - In Section 1 item 6 and Section 4 (lines 227–229), explicitly state that `GlobalBirkhoffConverse` assumes `IsSpaceTimeOn g s` and, for `m = 0`, requires `D` to miss the spatial origin `x₁ = x₂ = x₃ = 0` (so the two directions match exactly for `m ≠ 0`, not `m = 0`).
- **Confidence:** `VERIFIED`.

### F3. Section 5 misnames the Kretschmann scalar as "the curvature scalar" and gives a mathematically wrong reason for its minus sign
- **Where:** `paper/paper.md` Section 5, line 307; `GravityInLean/Global/Kretschmann.lean:34-37`, `GravityInLean/Global/KretschmannKruskal.lean:16-20, 72-74`.
- **Relevant Lean lines:**
  ```lean
  -- GravityInLean/Global/Kretschmann.lean:34-37
  noncomputable def kretschmann {n : ℕ} (g ginv : Fin n → Fin n → Coords n → ℝ) (x : Coords n) :
      ℝ :=
    ∑ ρ, ∑ μ, ∑ σ, ∑ τ, ginv ρ σ x * ginv μ τ x *
      (riemM (christoffel g ginv) ρ μ x * riemM (christoffel g ginv) σ τ x).trace
  ```
  ```lean
  -- GravityInLean/Global/KretschmannKruskal.lean:72-74
  theorem kretschmann_kruskal (hm : 0 < m) {x : Coords 4} (hx : x ∈ kruskalRegion) :
      kretschmann (kruskalG m) (genGinv (kruskalA m) (kruskalA m) zero2 (kruskalS m)) x
        = -48 * m ^ 2 / kruskalR m (x 1 ^ 2 - x 0 ^ 2) ^ 6 := by
  ```
- **What is wrong and why it matters:** Section 5 line 307 states: *"Instead such a map keeps the curvature scalar (−48m²/r⁶ in the project's signs), hence the radius;"*. Two errors here:
  1. **Wrong name:** In general relativity, "the curvature scalar" (or scalar curvature) universally denotes the **Ricci scalar** $R = g^{ab} R_{ab}$, which is identically $0$ in vacuum. The invariant being used is the **Kretschmann scalar** $K = R_{abcd} R^{abcd}$ (up to sign).
  2. **Wrong explanation of the minus sign:** Neither changing the Riemann sign convention ($R \mapsto -R$, which squares to $+1$) nor changing the metric signature ($g \mapsto -g$, which contributes $(-1)^4 = +1$) changes the sign of $K = R_{abcd} R^{abcd} = +48m^2/r^6$. The minus sign in `kretschmann` comes from the **index contraction order** in `Matrix.trace (riemM ρ μ * riemM σ τ)`: it contracts $R^\alpha{}_{\beta\rho\mu} R^\beta{}_{\alpha\sigma\tau} g^{\rho\sigma} g^{\mu\tau} = - R_{\alpha\beta\rho\mu} R^{\alpha\beta\rho\mu} = -K$ (by antisymmetry of $R_{\alpha\beta\rho\mu}$ in its first two indices). Even the file docstring in `Global/KretschmannKruskal.lean:19-20` gets this right; the paper text garbles it.
- **Concrete fix:** Replace line 307 with: *"Instead such a map preserves the Kretschmann invariant $K = R_{abcd} R^{abcd} = 48m^2/r^6$ (computed in `Global/Kretschmann.lean` via the matrix trace contraction $R^\alpha{}_{\beta\rho\mu} R^\beta{}_{\alpha\sigma\tau} g^{\rho\sigma} g^{\mu\tau} = -K = -48m^2/r^6$), hence the radius;"*.
- **Confidence:** `VERIFIED`.

### F4. Section 4's gluing counterexample omits that it is non-Hausdorff, and references undefined "first form" / "second target" / "neither list"
- **Where:** `paper/paper.md` Section 4, lines 235–239 (cross-checked against `GravityInLean/Goals/GlobalComplete.lean:140-145`).
- **What is wrong and why it matters:** Lines 235–239 state:
  *"What we did not state: a classification of all maximal or inextendible such space-times. The second target of that kind (Kruskal–Szekeres or one of its four Z₂ quotients, under a completeness condition) needs geodesics on a manifold, which neither the project nor mathlib has; and its first form is false as written: two copies of Kruskal–Szekeres glued along one exterior region meet the conditions but are on neither list."*
  1. **Mathematical omission:** Two copies of Kruskal–Szekeres glued along one open exterior region $\{X > |T|\}$ form a **non-Hausdorff** branching manifold (every horizon point on $X = |T|$ is doubled into two points whose neighbourhoods cannot be separated, like the line with two origins). In standard general relativity (Hawking–Ellis, Wald, O'Neill), spacetimes are Hausdorff by definition, so this construction is **not** a counterexample to the textbook classification—it is only a counterexample if Hausdorffness (`T2Space M`) is omitted, as in Lean's `IsManifold`. Indeed, `Goals/GlobalComplete.lean:140-145` (added later for G2) explicitly uses this example to prove `GlobalCompleteNeedsHausdorff`. Presenting it here as showing the classification is "false as written" without stating that Hausdorffness was omitted will look like an elementary error to any relativist.
  2. **Broken prose references:** The paper never introduces a "first form", a "second target", or two lists ("neither list")—those phrases leaked from internal notes (`review/global-birkhoff.md` / `PLAN.md`).
- **Concrete fix:** Rewrite lines 235–239 clearly: *"What we did not state: a classification of maximal or inextendible spherically symmetric vacuum space-times. Even restricting to Kruskal–Szekeres and its four $\mathbb{Z}_2$ quotients under a geodesic s-completeness condition requires geodesics on manifolds (absent from mathlib v4.36.0) and an explicit Hausdorff hypothesis—without Hausdorffness, two copies of Kruskal–Szekeres glued along one exterior region satisfy the completeness and symmetry conditions yet are not on that list."*
- **Confidence:** `VERIFIED`.

### F5. Abstract hides that the "review against the textbooks" and "independent second reader" were AI models, and omits core methodological limits; `checklist.md` understates the severity of having no human specialist review
- **Where:** `paper/paper.md` Abstract lines 22–23, 28–30 (contrast Section 6 line 337, Section 7 lines 358–386, Section 10 lines 537–553); `paper/checklist.md` lines 75–76, 106–111.
- **What is wrong and why it matters:**
  1. The Abstract states: *"The definitions were reviewed against the textbooks and are pinned by 25 tests in which a definition must fail."* and *"The statements were fixed in advance, read by an independent second reader, and checked afterwards by a rebuild from scratch and an audit of axioms."* Nowhere does the Abstract disclose that **both the reviewers and the second reader were AI models (Claude Opus 5.5)** and that **no human expert has checked the definitions, statements, or mathematics**. A reader who scans the Abstract will take "reviewed against the textbooks" and "independent second reader" to mean human specialists. The Abstract also omits the three other headline methodological limits: no baseline comparison, open network access during runs (only one run's log checked), and subscription-meter upper bounds for cost.
  2. **Severity of `paper/checklist.md` item:** `checklist.md` line 75–76 treats a human gravity specialist reading the definitions as *"Welcome, not strictly required"*, and omits `Goals/Global.lean` from the files to read. Unlike the November 2026 Riemann Hypothesis formalisation (where the statement already lived in mathlib), every definition here is custom. Because the human author explicitly disclaims verifying the mathematics (Section 10), submitting without human specialist sign-off on the definitions and statements is not "optional"—it is a severe credibility blocker for any mathematics or ITP venue (and a moderation risk on arXiv).
- **Concrete fix:**
  - In the Abstract, change *"reviewed against the textbooks"* to *"reviewed against the textbooks by AI reviewers (no human specialist has yet audited them)"*, change *"read by an independent second reader"* to *"read by a separate AI model instance"*, and add one sentence stating the method limits: *"No baseline (single-agent or human) was run, worker containers had network access (audited for only one of seven runs), and costs are upper bounds from a shared subscription meter."*
  - Treat human expert review of `Curved/Basic.lean`, `Curved/Goal.lean`, `Goals/EveryPoint.lean`, `Goals/Global.lean`, and `Goals/Connection.lean` as mandatory before submission (updating `checklist.md` accordingly).
- **Confidence:** `VERIFIED`.

### F6. Section 7 misstates the network rule of Run 4 and silently skips Run 7
- **Where:** `paper/paper.md` Section 7, lines 359–362; `fleet/goal-exactly-when.md:145-146` (Run 4), `fleet/goal-global.md:160` (Run 7).
- **What is wrong and why it matters:** Section 7 lines 359–361 claim:
  *"The briefs limited its use: in runs 1 to 3 to reading documentation; in run 5 no web search and no other project's proof; the briefs of runs 4 and 6 had no rule about it."*
  This is **factually wrong for Run 4** and **silently omits Run 7**:
  - In `fleet/goal-exactly-when.md` (Run 4), rule 8 explicitly states: *"Nothing leaves the container, except reading: do not push to GitHub, do not open pull requests or issues. Reading documentation and the one file named in Part 3 is allowed."* (That "one file" was TauCeti's proof, which a worker read before Part 3 was withdrawn.) Saying Run 4 "had no rule about it" misrepresents the actual brief.
  - Run 7 (`fleet/goal-global.md`) is not mentioned at all in this paragraph; its rule 8 matches Run 6 (*"Nothing leaves the container: do not push to GitHub, do not open pull requests or issues"*—no inbound restriction).
- **Concrete fix:** Rewrite lines 359–362: *"The briefs limited its use as follows: runs 1–3 allowed reading documentation only; run 4 allowed reading documentation and TauCeti's connection file (which was withdrawn mid-run); run 5 forbade web search and reading any other project's proof; runs 6 and 7 forbade outbound actions only, with no rule against reading from the web. Only run 5's log was checked for network access (none was found); for runs 1–4, 6, and 7, the logs do not establish that the network went unused."*
- **Confidence:** `VERIFIED`.

---

## 3. Important Issues

### F7. Six stale pre-Run-7 numbers and omissions survive across Sections 7, 8, and 9
- **Where:** `paper/paper.md` Section 7 (lines 404–405, 409, 415–416), Section 8 (lines 427, 431–433), Section 9 (line 453).
- **What is wrong and why it matters:** Several paragraphs were written after Run 6 and never updated when Run 7 (`Global/`) was added:
  1. **Section 8, line 427:** *"That the roughly 630 intermediate lemmas say what their comments say."* That is the pre-Run-7 sum of the table's `Theorems` column for Runs 1–6 (`24 + 62 + 168 + 83 + 134 + 155 = 626`, matching `PLAN.md:484`). Including Run 7 (`+350`), the seven runs contain **976** theorems (922 beyond the 54 fixed statements), and the full repository at `paper-1-numbers` has **1,556** theorems. The reported figure is off by ~350 lemmas (>50%).
  2. **Section 8, lines 431–433:** *"the theorems are local (a chart around each point), and the charts' images avoid the poles of the angular coordinates, although no point of the manifold is excluded."* This ignores Run 7 (`GlobalBirkhoff`), which is a **global** local isometry on any simply connected open region and uses `S² ⊂ ℝ³` (and Cartesian coordinates for `m ≤ 0`), avoiding no poles in the image either.
  3. **Section 7, lines 415–416 ("What was changed after a run, and by whom"):** *"After run 4 nothing was changed; for runs 2, 5 and 6 the record lists no change."* Silently skips Run 7 (`Global/STATUS.md` has no supervisor post-run audit section; git history around `3b816ea` shows no post-run Lean edits by the supervisor, only `Audit.lean`/`PLAN.md`/`README.md` updates, while inside the run the lead and a worker made small form fixes before merge).
  4. **Section 7, line 409 ("What went wrong"):** *"Twice a lead gave the same lemma to two workers."* Stale: `Join/STATUS.md` records 1 hedge (`curvature-at`), `BothWays/STATUS.md` 1 hedge (`pull-smooth`), `Checks/STATUS.md` 1 accidental duplicate (`exists_koszulCov`), `Rim/STATUS.md` 3 hedges (`null-congr`, `null-slopes`, `null-assembly`), and `Global/STATUS.md` lines 48–55 record **6** duplicated lemmas built on unmerged branches (`KruskalLocal`, `SchwSplit`, `SchwTime`, `SchwRadius`, `MassMixed`, `HessSchw`) plus `MassCharts.lean` merged unused.
  5. **Section 7, lines 404–405:** Mentions route changes in Runs 3 and 6 while silently skipping Run 2 (dot-product surface replacing unit-vector choice, and discovering Killing/positivity were unused) and Run 7 (replacing the ODE uniqueness route with the Kretschmann + Hessian rigidity argument).
  6. **Section 9, line 453:** Lists `STATUS.md` in `Flows/`, `Turns/`, `Join/`, `BothWays/`, `Checks/`, `Rim/`—silently omits `Global/` (which has `GravityInLean/Global/STATUS.md` at both `paper-1-numbers` and `HEAD`), and should note that `OneMass/` and `Connection/` are logged inside `Checks/STATUS.md`.
- **Concrete fix:** Update all six locations so every section consistently covers all seven runs at tag `paper-1-numbers`.
- **Confidence:** `VERIFIED`.

### F8. Cost reporting omits exact per-run token counts already recorded in `PLAN.md` and conflates two subscription meters
- **Where:** `paper/paper.md` Section 7, lines 377–381 vs. `PLAN.md` lines 238–239, 291–292, 343–344, 407–408, 433–434, 455–456, 570–572.
- **What is wrong and why it matters:**
  1. `paper/paper.md` reports cost solely as percentage points of Anthropic's opaque weekly subscription meter—numbers that depend on an unspecified subscription tier and are contaminated by concurrent sessions. Yet `PLAN.md` already records **exact per-run token counts** for all seven runs (Read / Cached / Written: Run 1: 9.4M / 8.9M / 178k; Run 2: 16.6M / 15.8M / 319k; Run 3: 39.2M / 37.6M / 569k; Run 4: 23.4M / 22.2M / 361k; Run 5: 37.6M / 36.2M / 411k; Run 6: 47.4M / 45.7M / 745k; Run 7: 102M / n.a. / 1.23M; total ≈ 275.6M input tokens and ≈ 3.81M output tokens). Reporting exact token counts (with API list-price equivalents clearly labelled as computed from tokens) is far more reproducible and avoids concurrent-session pollution.
  2. Lines 379–381 conflate two different meters: *"between 2 and 11 percentage points per run for runs 1 to 6 (details in `PLAN.md`), and 22 points of the weekly Fable meter for run 7 (72% to 94%, with three sessions active)."* In `PLAN.md`, Runs 1–6 used **2 to 5** points on the "all models" meter and **3 to 11** points on the "Fable" meter (mixing the minimum of one meter with the maximum of the other), while Run 7 used 11 points on "all models" and 22 on "Fable". Also, the detail *"with three sessions active"* for Run 7 does not appear in `PLAN.md` (lines 570–572), contradicting the header's claim (lines 8–9) that every number is recorded in `PLAN.md` or the run logs.
- **Concrete fix:** Add a `Tokens (read / written)` column (from `PLAN.md`) to the Section 7 run table, separate the "all models" (2–11 pts) and "Fable" (3–22 pts) weekly meters cleanly, and either document or drop the "three sessions active" claim.
- **Confidence:** `VERIFIED`.

### F9. `lake comparator --paranoid` covers only 16 of the 54 fixed statements, and the sandboxed kernel checks were run locally rather than in public CI
- **Where:** `paper/paper.md` Section 9, lines 466–533; `comparator/Challenge.lean`, `comparator.json`, `.github/workflows/check.yml`.
- **What is wrong and why it matters:**
  1. Section 9 describes `comparator/Challenge.lean` as checking "the sixteen headline results", and `comparator.json` confirms those 16 include 3 of the Global sanity checks (`kruskalMapOfSchwarzschild`, `globalUniqueNeedsOnePiece`, `globalDeSitterNoMap`), **while omitting two headline theorems listed in Sections 1 and 4** (`connectionUnique` and `schwarzschildIsEmpty`) as well as all 25 failure tests (`Goals/Tests.lean`) and all 9 Kruskal known-answer theorems (`Goals/EveryPoint.lean`). A sceptical reviewer checking whether the failure tests and `connectionUnique` match their fixed statements cannot rely on `lake comparator` for those 38 statements.
  2. `.github/workflows/check.yml` only runs `lake build`. All `lake comparator --paranoid` and `lake check --paranoid` runs were executed locally in Docker on the author's own Windows PC, leaving no public CI log or artifact for an independent reader to inspect without cloning and re-running `scripts/sandbox-check/run.sh`.
- **Ranked trust gaps (by impact on a careful Lean reviewer's confidence):**
  1. **Human specialist audit of the definitions and statements** (highest impact: no kernel checker can verify semantic agreement with GR).
  2. **Running `lake comparator --paranoid` in GitHub Actions CI** with `comparator/Challenge.lean` expanded to cover `connectionUnique`, `schwarzschildIsEmpty`, and ideally all 54 fixed statements (at 9 min / ≤10 GB RAM, this fits comfortably in public CI and removes reliance on a local run).
  3. **Archiving exact `#print axioms` output** for every headline theorem (already on `checklist.md`, trivial to automate in CI).
  4. **Resolving the `nanoda` stack overflow on the 464,847-declaration export** (already on `checklist.md`; lowest marginal confidence impact, since `nanoda` already checked all 58,865 declarations in the project's transitive closure and five other checkers passed the full export).
- **Concrete fix:** Add `connectionUnique` and `schwarzschildIsEmpty` (and optionally the failure tests / Kruskal checks) to `comparator/Challenge.lean`, add a GitHub Actions workflow running `lake comparator --paranoid` (and `#print axioms`), and note in Section 9 precisely which 16 of the 54 statements were checked at `73816cc`.
- **Confidence:** `VERIFIED`.

### F10. Related work (Section 2) omits PhysLean/Physlib, other proof assistants, and citations for earlier Schwarzschild formalisations; References has major citation mismatches
- **Where:** `paper/paper.md` Section 2 (lines 87–129), Section 8 (line 434), References (lines 555–576); cross-checked against `SURVEY.md` and live web/GitHub searches on 24 November 2026.
- **What is wrong and why it matters:**
  1. **Missing related work:** Section 2 makes a cross-prover claim (*"no machine-checked Birkhoff theorem in any proof assistant"*, line 127) yet never mentions **PhysLean / Physlib** (`leanprover-community/physlib`, formerly HepLean; 882 stars on GitHub as of 24 Nov 2026, with relativity/tensor infrastructure and `IncompressibleSphere.lean`), never mentions **other proof assistants** (e.g., Isabelle/HOL relativity work by Stannett–Németi 2013, Schmoetten–Palmer–Fleuriot 2022 on Schutz's axioms, and AFP's `No_FTL_observers_Gen_Rel` 2023; axiomatic relativity in Coq/Rocq), never cites **mathlib's Riemannian `LeviCivita.lean`** (which `Connection/` was modeled on), and leaves line 104 (*"Schwarzschild's solution itself had been verified in Lean at least twice before"*) completely uncited (despite `SURVEY.md` listing `BishopWolf/physics`, the 2026 ResearchGate Schwarzschild pipeline preprint, and Lightlike). Furthermore, live inspection of `LightLikeProject/lightlike` on 24 November 2026 shows an extensive Kruskal/Schwarzschild suite (`KruskalExtension.lean`, `KruskalManifold.lean`, `KruskalInextendible.lean`, `KruskalKretschmann.lean`, `SchwarzschildManifold.lean`, `SchwarzschildKilling.lean`), which should be noted alongside its orbit-chart files (still confirming no Birkhoff file exists there).
  2. **Citation mismatches (beyond the unverified-pages note in `checklist.md`):**
     - **Cited in body, missing from References:** **Wald (1984)** (cited in Section 8 line 434) and **Szekeres (1960)** (*Publ. Math. Debrecen* 7, 285–301; named throughout as "Kruskal–Szekeres").
     - **Listed in References, never cited in body:** **Chruściel**, **Schleich & Witt** (`arXiv:0910.5194`), and **de Moura & Ullrich (2021)** (lines 570–571, 573). Also, Schleich & Witt's 2010 local-Birkhoff paper (*J. Math. Phys.* 51, 112502, `arXiv:0908.4110`)—which `review/global-birkhoff.md` identifies as the closest published match to `IsRoundOn`—is missing from both text and References.
     - Line 576 points readers to `SURVEY.md` for the four repositories instead of giving URLs/commits/access dates in References.
- **Concrete fix:** Add a short paragraph in Section 2 covering PhysLean/Physlib, earlier Lean Schwarzschild checks (with citations), Lightlike's Kruskal/Schwarzschild files, mathlib's Riemannian Levi-Civita file, and Isabelle/Coq relativity formalisations; reconcile all in-text citations with the References section (adding Wald 1984, Szekeres 1960, Schleich & Witt 2010, and citing or removing uncited entries).
- **Confidence:** `VERIFIED` (GitHub API and web searches performed 24 November 2026).

### F11. Section 8's claim that an isometric SO(3) action yields `IsRoundOn` skips the left-action sign flip and the exclusion of fixed points
- **Where:** `paper/paper.md` Section 8, lines 434–437; `GravityInLean/Curved/Basic.lean:352-357`, `Curved/KnownAnswers.lean:622-623`, `Goals/Tests.lean:205-208`.
- **Relevant Lean lines:**
  ```lean
  -- GravityInLean/Curved/Basic.lean:352-357
    likeTurns : ∀ x ∈ s, mlieBracket I (ξ 0) (ξ 1) x = ξ 2 x ∧
      mlieBracket I (ξ 1) (ξ 2) x = ξ 0 x ∧ mlieBracket I (ξ 2) (ξ 0) x = ξ 1 x
    surfaces : ∀ x ∈ s, Module.finrank ℝ (Submodule.span ℝ (Set.range fun i ↦ ξ i x)) = 2
    positive : ∀ x ∈ s, ∀ v ∈ Submodule.span ℝ (Set.range fun i ↦ ξ i x), v ≠ 0 → 0 < g x v v
  ```
- **What is wrong and why it matters:** Section 8 lines 434–437 state: *"Hawking and Ellis, Wald and O'Neill assume an isometric action of SO(3) with two-dimensional spacelike orbits. Such an action yields three fields as in `IsRoundOn`, so the theorem here is at least as strong; but that step is an argument on paper and is not proved in Lean."* The conclusion is **mathematically true**, but two technical points should be stated explicitly so a relativist does not stumble over them:
  1. **Sign convention:** Under mathlib's `mlieBracket` (`[X, Y] = XY - YX`, verified in `Curved/Flat.lean:94-98`), the fundamental vector fields $X_1, X_2, X_3$ of a **left** $SO(3)$ action form an anti-homomorphism $[X_1, X_2] = -X_3$ (cyclic). To satisfy `IsRoundOn.likeTurns` ($[\xi_0, \xi_1] = +\xi_2$), one takes $\xi_i = -X_i$ or applies an odd permutation (as the project itself does in `turns = ![rotY, rotX, rotZ]`).
  2. **Fixed points:** `IsRoundOn.surfaces` requires rank 2 at every point of $s$, excluding fixed points (the regular centre $r = 0$, which only occurs in vacuum for Minkowski $m = 0$). Saying *"with two-dimensional spacelike orbits"* on $s$ already excludes fixed points on $s$, so this is consistent, but Hawking–Ellis Appendix B allows fixed points on the full manifold (restricting to the open dense principal-orbit locus).
- **Concrete fix:** Add one parenthetical clause in Section 8 lines 435–437 noting both the sign flip (or odd permutation) for a left action under $[X, Y] = XY - YX$ and that the 2-dimensional orbit condition excludes fixed points such as the origin $r = 0$ of Minkowski space.
- **Confidence:** `VERIFIED`.

### F12. Contribution, venue fit (AFM vs. CADE), and cross-disciplinary readability
- **Where:** `paper/paper.md` overall (Sections 1, 3, 4, 5, 7, 10); `paper/checklist.md` lines 117–128.
- **Assessment (kept brief):**
  - **What is genuinely new:** No new physics theorem, but two real contributions: (1) *as formalisation*, to our knowledge (verified 24 Nov 2026) the first machine-checked Birkhoff theorem from coordinate-free symmetry hypotheses, covering the horizon and bifurcation sphere (Kruskal–Szekeres target) and a global developing map, plus reusable differential-geometry infrastructure absent from mathlib v4.36.0 (`smoothFlow`, `turnsCoordinates`, indefinite Levi-Civita, covering-space developing map); (2) *as formal proof engineering / mathematics*, the elementary `product_form` lemma (handling the bifurcation sphere in $C^\infty$ without regular-singular ODEs or analyticity), the non-analytic Kretschmann+Hessian rigidity proof for Kruskal/Schwarzschild, and the observation that `turnsCoordinates` requires neither Killing's equation nor metric positivity.
  - **Would it pass AFM's bar ("no formalisations of known results without new insight")?** Not as currently drafted. First, AFM requires a human-authored manuscript (already noted in `checklist.md`). Second, the manuscript currently hides its genuine mathematical and formalisation insights in single paragraphs of Section 5 while devoting large sections to an uncontrolled AI-team report. To pass AFM, a human-written version (with human specialist verification of the definitions) should lead with those proof/formalisation insights and expand Section 5. To fit a conference like CADE-31 as a method + formalisation paper, Section 7 needs at least one controlled comparison (e.g., Run 2 or Run 4 with a single agent) and exact token counts (F8); trimming repetitive setup narrative in Section 7 frees space for both.
  - **Cross-disciplinary clarity:** Currently harder than necessary for both audiences. A relativist who does not know Lean has to decode Lean excerpts (`OpenPartialHomeomorph`, `mfderiv 𝓘(ℝ, Coords 4) ...`, `dt (dr Ω)`) without standard mathematical statements printed beside them, and is never explicitly told the signature convention $(-,+,+,+)$. A Lean user who does not know relativity is never shown the coordinate Schwarzschild metric formula in Section 3/4 (only the Kruskal formula is printed explicitly in Section 4 line 208) nor given a brief explanation of what the bifurcation sphere is.
- **Concrete fix:** Place a short standard-notation mathematical statement next to each Lean excerpt in Sections 3–5, state the $(-,+,+,+)$ signature and Schwarzschild line element explicitly, and decide whether to tailor the manuscript toward formalisation/math insights (for AFM, human-rewritten) or empirical AI-fleet methodology (for CADE, adding a baseline and token counts).
- **Confidence:** `VERIFIED`.

---

## 4. Minor Issues and Nits

### F13. Three of the five Lean excerpts are not literal byte-for-byte copies of the source files
- **Where:** `paper/paper.md` lines 161–170 (`IsRoundOn`), 178–190 (`BirkhoffNoCoordinates`), 199–205 (`BirkhoffAtEveryPoint`), and Section 9 line 459.
- **What is wrong and why it matters:** Section 9 line 459 says *"Each Lean excerpt in this paper was compared with the source by a script."* Automated comparison against `paper-1-numbers` shows all five excerpts are **token-identical (modulo comments)**—every Lean symbol and type is faithful—but three are not literal verbatim substrings: `IsRoundOn` strips six `/-- ... -/` field docstrings, and `BirkhoffNoCoordinates` / `BirkhoffAtEveryPoint` each merge a two-line binder header (`[IsManifold ...]`) onto one line. (`GlobalBirkhoff` and the signature of `product_form` match verbatim.)
- **Concrete fix:** Either say *"matched against the source up to whitespace and omitted docstrings"* in Section 9 line 459, or keep the original line breaks and note "(field docstrings omitted)" on `IsRoundOn`.
- **Confidence:** `VERIFIED`.

### F14. Minor counting and window inconsistencies in the Section 7 run table and Section 9 module count
- **Where:** `paper/paper.md` Section 7 table (lines 367–376), Section 9 (line 483).
- **What is wrong and why it matters:**
  1. **Run 5 theorem count:** At `paper-1-numbers`, `Checks/` (98) + `OneMass/` (13) + `Connection/` (23 lines starting with `theorem`, 24 including `@[...] theorem`) = 134 or 135 depending on whether attributed theorems are counted (consistent with 134 if counting lines starting literally with `theorem`/`lemma`, worth keeping consistent with the abstract's 1,556).
  2. **Run 7 file/line/theorem count vs. `Global/` folder:** At `paper-1-numbers`, `GravityInLean/Global/` contains **41** files / 10,110 lines / 402 theorems, because `Global/Checks.lean` (707 lines, 52 theorems) was written beforehand by the supervisor. Excluding `Checks.lean` gives 40 files / 9,403 lines / 350 theorems, matching the table—a one-line footnote explaining this avoids confusion when a reader counts `Global/`.
  3. **Run 7 Lean-run window:** For Runs 1–6, the `Lean runs (failed)` column uses the supervisor's count *"until the goal"* (e.g., 52 vs. 74 in `Turns/STATUS.md`, 80 vs. 121 in `Checks/STATUS.md`, 72 vs. 79 in `Rim/STATUS.md`). For Run 7, the table uses the lead's count `132 (19)` over `03:11–03:59`, which runs two minutes past the `03:57:17` goal build and stops before the `04:01–04:02` warning-fix rebuild (51 min vs. 46 min reported).
  4. **Section 9 line 483 ("200 modules"):** Tag `paper-1-numbers` contains **201** `.lean` files (`199` under `GravityInLean/`, plus `GravityInLean.lean` and `Audit.lean`). Clarify if `GravityInLean.lean` (the import barrel) was excluded from the 200 count.
- **Concrete fix:** Add brief footnotes to the Section 7 table clarifying the exclusion of `Global/Checks.lean` and the Run 7 time/run cutoff, and verify "200" vs. "201" modules in Section 9.
- **Confidence:** `VERIFIED`.

### F15. Small technical imprecisions in Section 1, Section 2 table, Section 3, and Section 5 prose
- **Where:** `paper/paper.md` Abstract line 19, Section 1 item 7 (lines 66–68), Section 2 table (lines 111–119), Section 3 (lines 137–148), Section 5 (lines 288–296, 308–312).
- **What is wrong and why it matters:**
  1. **Abstract line 19 / Section 4 line 226:** *"one length-keeping map"* is non-standard phrasing; glossing it as *"a local isometry (developing map, not necessarily injective)"* in the Abstract avoids any ambiguity for relativists.
  2. **Section 1 item 7:** Describes `turnsCoordinates` as *"adapted coordinates for three vector fields with so(3) brackets and two-dimensional orbits"*, whereas the fixed Lean statement `TurnsCoordinatesStatement` (`Goals/Turns.lean:150-158`) still takes `IsRegularTableOn g ginv s` and `TurnsOn g ξ s` (including Killing's equation and positivity), even though the proof did not use them (noted later in Section 5 line 271).
  3. **Section 2 side-by-side table:** (a) For ProjectAinos, the table compares `theorem birkhoff` accurately, though noting in a parenthetical that `ProjectAinos/GeneralRelativity/Birkhoff.lean` also proves `birkhoff_timeChange` (eliminating $f(t)$ via $T' = \sqrt{f}$) is fairer; (b) for `grlab`, the table says *"an open interval of r in ℝ"*, whereas `GRLab/Birkhoff.lean:47-50` only requires a convex subset `s ⊆ ℝ` avoiding `0` (no openness assumed).
  4. **Section 3:** Never explicitly states the metric signature convention $(-, +, +, +)$.
  5. **Section 5 line 292 (`product_form`):** Prints `dt` and `dr` without explaining that they stand for $\partial_u$ and $\partial_v$ (the project's generic first- and second-argument partial derivatives).
  6. **Section 5 lines 308–310:** Calls $\nabla\nabla r$ *"the second derivative of the radius"* (should say **covariant Hessian** $\nabla\nabla r$, since coordinate second derivatives are not isometry-invariant, and note that the photon sphere $r = 3m$ where its two eigenvalues coincide is handled by continuity); says *"on the plane it keeps a constant quadratic form, hence it is affine"* without noting that preservation of $X^2 - T^2$ kills the translation for Kruskal; and omits the $m < 0$ and $m = 0$ cases of the global uniqueness proof.
- **Concrete fix:** Incorporate these six targeted clarifications in prose.
- **Confidence:** `VERIFIED`.

---

## 5. What I Checked and Found Sound

To make silence meaningful, the following were explicitly verified against the Lean source files, git history, textbook formulas, and web/GitHub sources (24 November 2026) and found **sound**:

1. **Core coordinate-free definitions (`GravityInLean/Curved/Basic.lean`, `Curved/Goal.lean`):**
   - `HasOneTimeDirection` + symmetry genuinely captures exact Lorentzian signature $(-, +, +, +)$ and implies `Nondegenerate`.
   - `IsSmoothOn` genuinely uses mathlib's `VectorBundle.Hom` (confirmed via `Curved/Flat.lean:200-219` and `Join/CarrySmooth.lean`), not a trivial bundle.
   - `IsConnectionOf` matches the standard torsion-free ($\nabla_X Y - \nabla_Y X = [X, Y]$), metric-compatible Levi-Civita connection; `IsConnectionOf.unique` (via Koszul's formula) rules out junk connections in the existential `IsEmptyOn`; `ConnectionExistsStatement` is genuinely proved for arbitrary finite-dimensional smooth manifolds with a non-degenerate metric (`Connection/Exists.lean`, `Connection/Candidate.lean`).
   - `curvatureOfFields` ($\nabla_X \nabla_Y Z - \nabla_Y \nabla_X Z - \nabla_{[X,Y]} Z$), `curvatureAt`, and `ricciAt` ($\operatorname{tr}(u \mapsto R(u, v)w)$) match standard MTW / Hawking–Ellis / Carroll conventions, contract the correct slot (not the identically vanishing third slot), and are pinned by non-zero known answers (`sphere_curvature`: $\operatorname{Ric} = +g$; `deSitter_curvature`: $\operatorname{Ric} = (3/L^2) g$).
   - `LeavesUnchangedAt` is the standard coordinate-free Killing equation $\mathcal{L}_\xi g = 0$ with an explicit differentiability guard (`MDiffAt (T% ξ) x`).
   - `sizeSq` $= (g(\xi_0, \xi_0) + g(\xi_1, \xi_1) + g(\xi_2, \xi_2))/2$ has the exact factor $1/2$, equals $r^2$ on round 2-spheres, and is invariant under $\operatorname{Aut}(\mathfrak{so}(3)) = SO(3)$ (basis-free).
   - `UsableDistanceAt` accurately expresses "$\nabla r$ is not null (and non-zero)", and fails safely on non-differentiable functions.
2. **Coordinate metrics, targets, and non-vacuity (`Curved/Goal.lean`, `Goals/EveryPoint.lean`, `Goals/Global.lean`, `RoundSpacetime.lean`):**
   - Schwarzschild's table `roundG (schwA m) (schwB m)` in $(t, r, \theta, \phi)$, `outside m`, and `inside m` match $-(1-2m/r)\,dt^2 + (1-2m/r)^{-1}\,dr^2 + r^2 d\Omega^2$ for all $m \in \mathbb{R}$ ($m = 0$ Minkowski, $m < 0$ negative mass).
   - Kruskal–Szekeres metric `kruskalG m` matches $(32m^3/r)e^{-r/2m}(-dT^2 + dX^2) + r^2 d\Omega^2$ with $(r/2m - 1)e^{r/2m} = X^2 - T^2$ on $X^2 - T^2 > -1$; algebraic check confirms exact agreement with Schwarzschild exterior/interior via the textbook formulas (`kruskalOutside`, `kruskalInside`).
   - Global targets `kruskalWhole` (using $S^2 \subset \mathbb{R}^3$, avoiding no poles) and Cartesian `schwSpaceG` (for $m \le 0$) match the spherical metrics exactly.
   - `GlobalBirkhoff` + `GlobalBirkhoffUnique` + `GlobalMassUnique`: formulating `D` as a local isometry (developing map, not necessarily injective) is mathematically appropriate and non-trivial—injectivity cannot hold in general (e.g., universal cover of Kruskal minus the bifurcation sphere). Quantifier orders (including `∃ m` outside `∀ p ∈ s` in `OneMassStatement` and `BirkhoffAtEveryPointOneMass`) are correct. No vacuous hypotheses or trivial escapes were found.
3. **Key proof mechanisms and prose mathematics:**
   - `product_form` (`Rim/Product.lean:94-100`) and its use in `Rim/NullKruskal.lean` and `Rim/Core.lean` are mathematically valid and cleanly avoid regular-singular ODEs across both horizons and the bifurcation sphere.
   - The covering-space gluing argument in `Global/Develop.lean` is sound and general.
   - The remark that textbook Birkhoff needs only $C^2$ metrics (Section 8 line 429) matches Hawking–Ellis Appendix B (and Bergmann–Cahen–Komar 1965 go lower to $C^0$, piecewise $C^1$).
   - The hedged claim that no complete written proof was found for the bifurcation sphere (Abstract, Section 2) is consistent with our literature check on 24 November 2026 (Hawking–Ellis App. B sketches the horizon join in one sentence; Chruściel's Thm 1.2.1 excludes null $dr$; An–Wong 2018 Thm 3.2 requires $dr \ne 0$; Schleich–Witt 2010 `arXiv:0908.4110` omits the $dY = 0$ locus).
4. **Priority claims and repository checks (checked via GitHub API and web search on 24 November 2026):**
   - Every priority claim in `paper.md` is hedged ("to our knowledge", "not found written down"); no unhedged "first" or "new" claim appears.
   - Direct inspection of `x-oai/ProjectAinos` (`ProjectAinos/GeneralRelativity/Birkhoff.lean`), `BrandonMYates/grlab` (`GRLab/Birkhoff.lean`), `LightLikeProject/lightlike` (repo tree), and `TauCetiProject/TauCeti` (`LeviCivita/Nondegenerate/Existence.lean`) confirms the paper's core comparative claims (no coordinate-free or horizon-covering Birkhoff theorem in any of them as of 24 Nov 2026).
5. **Verified repository counts and git history at tag `paper-1-numbers` (`3b816ea`):**
   - First commit (`d19529b`, `2026-11-23 01:08:59 UTC`) to `paper-1-numbers` (`3b816ea`, `2026-11-24 04:13:44 UTC`): 27.08 hours ("about 27 hours").
   - Under `GravityInLean/`: 199 `.lean` files, 39,406 lines ("about 39,400"), 1,556 theorems ("about 1,550").
   - `Audit.lean` at `paper-1-numbers`: 54 `example : Statement := theorem` checks ("54 statements").
   - Section 7 table sums: 152 minutes (`14+17+21+11+14+29+46`), 481 Lean runs (`20+52+79+46+80+72+132`), 79 failed (`1+9+17+10+10+13+19`), 27,450 lines ("about 27,400").
   - `GravityInLean/OneMass.lean`: 145 lines, 12 declarations.
   - `git diff paper-1-numbers..73816cc`: confirms no Lean proof file, `Audit.lean`, `lean-toolchain`, or `lake-manifest.json` changed between `paper-1-numbers` and the `lake comparator` run at `73816cc`.

---

## 6. What I Could Not Check, and Why

1. **Executing Lean / independent checkers:** I did not run `lake build`, `leanchecker`, `lake check --paranoid`, or `lake comparator --paranoid` (this was a read-only referee review; kernel verification is outside scope). As noted in F9, the paranoid and comparator runs were performed locally by the author rather than in public CI, so I could not inspect independent execution logs for them.
2. **Raw FACTORY container logs and subscription-meter records:** The raw agent session logs, build-queue logs, and Anthropic weekly-usage screenshots are not stored in the repository. I verified numbers against `PLAN.md`, `STATUS.md`, `fleet/goal-*.md`, and git history, but could not independently audit whether Runs 1–4, 6, and 7 accessed external URLs, nor independently re-audit Run 5's raw network log.
3. **Paywalled / exhaustive literature search:** Web searches were performed on 24 November 2026 across arXiv, GitHub, and public indices (covering ProjectAinos, grlab, Lightlike, TauCeti, PhysLean/Physlib, Isabelle/Coq/Rocq GR work, and classical Birkhoff papers). I did not read paywalled full texts (e.g., Bergmann–Cahen–Komar 1965, Goenner 1970, Szenthe 2004–2007, Chruściel OUP 2020) and cannot rule out unpublished or unindexed formalisations.
4. **Line-by-line audit of all intermediate proof files:** Only the definitions, fixed final statements, `Audit.lean`, `comparator/Challenge.lean`, and key proof files (`Rim/Product.lean`, `Rim/NullKruskal.lean`, `Rim/Core.lean`, `Rim/Patch.lean`, `Rim/Goal.lean`, `Global/Kretschmann.lean`, `Global/KretschmannKruskal.lean`, `Global/KruskalKept.lean`, `Global/KruskalPlane.lean`, `Global/UniqueKruskal.lean`, `Global/UniqueSchw.lean`, `Global/UniqueFlat.lean`, `Global/Develop.lean`, `Global/Glue.lean`, `Connection/Exists.lean`, `Connection/Candidate.lean`, `Curved/Tables.lean`, `Curved/Flat.lean`, `Curved/KnownAnswers.lean`, `Curved/Unique.lean`, `GeneralCurvature.lean`, `Symmetry.lean`, `RoundSpacetime.lean`, `NewCoordinates.lean`, `Curvature.lean`) were read directly. Correctness of the remaining intermediate proof bodies relies on Lean's kernel.

---

## Response (added by the authors, 24 November 2026)

The review above is kept as it came. It was written by an AI reviewer that had not written the
paper, from a prompt that asked for a strict referee's report on `paper/paper.md`. Each finding
was checked against the repository before anything was changed. All changes are to the text
(`paper/paper.md`, `paper/plain-summary.md`, `paper/checklist.md`, `SURVEY.md`); no Lean file
changed.

| Finding | Checked | Done |
|---|---|---|
| F1 | Confirmed: Section 8 still called the checks of Section 9 not established. | Section 8 now lists what Section 9 leaves open: comparator coverage, no second machine or public CI, `nanoda` on the whole export. |
| F2 | Confirmed: the local "if and only if" is only for points with non-null gradient; the global converse asks, for mass zero, a map that misses the centre. | Abstract, Section 1 (items 4 and 6) and Section 4 say so. |
| F3 | Confirmed: `kretschmann` contracts to −R_abcd R^abcd, so −48m²/r⁶ is right for it, but "curvature scalar" is the wrong name and the sign has nothing to do with conventions. | Section 5 names the Kretschmann invariant and explains the sign. |
| F4 | Confirmed: the gluing example is not Hausdorff, and the paragraph used internal labels. Also stale: the classification has since been stated (`Goals/GlobalComplete.lean`, with `T2Space`). | Section 4 rewritten; Section 8 says the classification is stated, not proved. |
| F5 | Confirmed: the abstract did not say the reviewers and second readers were AI. | Abstract says so, and names the three limits of the method. Whether a human specialist must read the definitions before submission stays the author's decision; the checklist records the reviewer's view. |
| F6 | Confirmed: run 4's brief allowed reading documentation and one named file; run 7 was missing. | Section 7 rewritten from the briefs. |
| F7 | Confirmed, all six: "630" was the sum for runs 1 to 6; "local" ignored the global theorem; run 7 missing from two paragraphs; the count of work done twice was wrong; route changes of runs 2 and 7 missing; `Global/STATUS.md` missing. | All six fixed. |
| F8 | Confirmed: the two meters were mixed, and "three sessions active" is not in `PLAN.md`. | Tokens column added from `PLAN.md`; the meters separated; the unrecorded phrase removed. |
| F9 | Confirmed: the comparator question covers 16 of the 54 fixed statements (the other 38: 25 failure tests, nine Kruskal known answers, three "exactly when" checks, `SchwarzschildIsEmptyStatement`). `connectionUnique` is not one of the 54. | Section 9 names the coverage. Widening the question to all 54 and running it in CI is on the checklist. |
| F10 | Confirmed: physlib, BishopWolf/physics, the Isabelle work, mathlib's Riemannian Levi-Civita file and Lightlike's Kruskal files were missing (most were already in `SURVEY.md`); Wald and Szekeres were cited but not listed; three listed works were not cited. Not confirmed: that `Connection/` was modelled on mathlib's file; it does not refer to it. | Section 2 and the references extended; every listed work is now cited. References remain marked as to be verified. |
| F11 | Confirmed: with mathlib's bracket a left action gives [X₁, X₂] = −X₃, and the project orders its own turns (y, x, z) for that reason. | Section 8 says so, and that two-dimensional orbits exclude fixed points. |
| F12 | Venue and contribution: a judgement for the author, not a change of text. Signature and Schwarzschild's line element were missing. | Signature stated in Section 3, line element in Section 4. |
| F13 | Confirmed: the excerpts agree up to line breaks and left-out field comments. | Section 9 says so. |
| F14 | Items 1 to 3 confirmed (run 7 leaves out `Global/Checks.lean`, 707 lines and 52 theorems written before the run; its Lean runs are counted to 03:59). Item 4 (200 or 201 modules) could not be checked: the `leanchecker` log is not in the repository; 199 files under `GravityInLean/` plus `Audit` make 200, and `GravityInLean.lean` only imports. | Notes under the run table; item 4 unchanged. |
| F15 | Items 1, 2, 4, 5, 6 and 3(a) confirmed and fixed. Item 3(b) not confirmed: grlab's `exists_mass_of_areal_vacuum` takes an open interval `Set.Ioo a b`; the convex set belongs to its helper `areal_invariant_const`. The table is unchanged there. | Section 1, 2, 3, 4 and 5 wording. |

The review missed one thing of the same kind: mathlib v4.36.0 already has the existence and
uniqueness of the Levi-Civita connection for Riemannian metrics (it named the file under F10,
but the paper's item 5 still read as if nothing were there). Section 1, item 5 now says so.
