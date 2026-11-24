# Publish Birkhoff now, then avoid crowded races

Research of 23 November 2026, asked for by Mario: which results could make a real paper? Five research helpers searched separately and one writer combined their notes, which are kept outside this repository (where the text names a notes file, it means one of those). Facts marked **[Checked]** were read at the source; three of them (TauCeti's connection file, the Lean blog's Riemann post, the CADE-31 deadlines) were checked a second time before this file was added. Related: [SURVEY.md](SURVEY.md) for what exists, [PLAN.md](PLAN.md) for the steps.

The one result gravity-in-lean can publish soon with an honest claim to be first is **Birkhoff's theorem stated without coordinates**. In plain words: an empty spacetime that looks the same in every direction around a centre must be the Schwarzschild black-hole spacetime, and the proof starts from the symmetry alone, with no map grid given in advance. It is a first only in that precise form. **Another AI-built Lean project, ProjectAinos, machine-checked the coordinate version on 19 November 2026**, four days before this project's own. Further up, none of the famous results has been machine-checked anywhere without large assumptions. That covers singularity theorems, the positive mass theorem, the Penrose inequality, black-hole uniqueness and stability. But two of those open lanes already have better-equipped AI teams running in them. **Lightlike is building the "who can influence whom" theory that singularity theorems need, at several theorems a day.** **TauCeti, incubated by the Lean FRO, has a positive-mass roadmap and most of the curved-space geometry that mathlib lacks**, but on a newer Lean. New mathematics in gravity is out of reach for theorem-proving alone. The realistic route to a new result is checking computer-produced "certificates" for special solutions, and nobody has yet checked whether Lean has the tools for that. My recommendation, in order:

1. Finish and publish coordinate-free Birkhoff together with the team measurements. The venues are the Annals of Formalized Mathematics (submissions accepted any time) and CADE-31 (paper deadline 22 February 2027).
2. Take static black-hole uniqueness as the next solo target. Nobody else is working on it, and it builds directly on Birkhoff.
3. Ask Lightlike about a joint singularity theorem instead of racing them.

Before claiming any "first", four things are needed:

- The repository must be public and dated. Today it is private, so no priority is established.
- The statement must be compared line by line with ProjectAinos.
- The community's four standard checks must pass (listed in the last section).
- A human must write the manuscript, because every venue requires one.

**How to read the marks.** **[Checked]** means I read the code, file or paper myself while writing this report, or the coordinator did. **[Notes: code]** means the researchers report reading the code. **[Notes: summary]** means only abstracts, READMEs or news were seen. **[Judgement]** marks my own or the researchers' opinion. Line counts and sizes for future work are always estimates.

## Level 1: coordinate-free Birkhoff is still open, and the team numbers are the story

### What exists elsewhere, and what that leaves for this project

Birkhoff's theorem has now been machine-checked three ways, all in Lean, all in 2026, and all with a shortcut.

**ProjectAinos** proves it inside a fixed "diagonal" template for the metric. The metric is the rule for measuring time and distance. The template is −A(t,r)dt² + B(t,r)dr² + r²dΩ², with A and B positive. **[Checked]** Its `theorem birkhoff` sits in `Birkhoff.lean`, first committed 2026-11-19 01:37 UTC ([ProjectAinos Birkhoff.lean](https://github.com/x-oai/ProjectAinos/blob/main/ProjectAinos/GeneralRelativity/Birkhoff.lean)). Requiring A and B to be positive limits it to the region outside the black hole's horizon, where r > 2M. The project's own ledger says the step from "a metric with rotational symmetry" to that template is **not stated** ([ProjectAinos GR ledger](https://github.com/x-oai/ProjectAinos/blob/main/docs/cinfty-general-relativity.md)) **[Notes: code]**.

**grlab** (August 2026) proves only the last step, a single equation solved under the extra assumption that nothing changes in time ([GRLab/Birkhoff.lean](https://github.com/BrandonMYates/grlab/blob/main/GRLab/Birkhoff.lean)) **[Notes: code]**.

**Lightlike** has no Birkhoff file at all. It does have close tools. Its `KillingOrbitChart.lean` builds charts from symmetry fields, but it uses them to show that spaces looking the same everywhere and in every direction are standard cosmological spaces. That is a different theorem ([Lightlike repository](https://github.com/LightLikeProject/lightlike)) **[Checked]**.

Searches of Isabelle, Coq/Rocq, the HOL family, Mizar and Metamath found no Birkhoff theorem at all **[Notes: summary]**.

So the **coordinate version is not a first**. The project's coordinate Birkhoff merged on 23 November 2026. Its "from symmetry, no starting template" version merged the same day. That second version is probably **more general than ProjectAinos's** **[Checked: file header only]**. It allows a mixed time–distance term and a free sphere size. It holds "wherever the size of the spheres is a usable distance", which takes in the inside of the horizon. Only the horizon itself (the "rim") and the poles are left out. It still assumes that coordinates exist in which rotations move only the two angles. But that version sits in a **private repository**, so it has no public date. A competing claim made tomorrow would be on record first.

The fully coordinate-free goal is `BirkhoffNoCoordinates`, already fixed in `Curved/Goal.lean`. It reads: a four-dimensional spacetime that is empty, with three symmetry fields that combine like rotations and sweep out spheres, has around each point where the sphere size is a usable distance a chart in which the metric is exactly Schwarzschild's. **That statement has not been found machine-checked anywhere.** It would also cover the black-hole interior and charts that are not diagonal, which ProjectAinos's template excludes. One of its two main building blocks is done. That is `turnsCoordinates`: coordinates adapted to three symmetry fields, about 2,070 lines, merged **[Checked]**.

### What is left, and what can be borrowed

The project's plan lists four remaining pieces ([PLAN.md](https://github.com/flujo-app/gravity-in-lean/blob/main/PLAN.md)) **[Checked]**:

1. **Stream 2.** Show that the connection exists for a metric in which time counts with the opposite sign. The connection is the rule for comparing directions at nearby points. mathlib's 414-line version assumes all lengths are positive.
2. **Stream 3.** A "bridge": in any chart, each new coordinate-free object equals the coordinate formula the project already uses.
3. **Stream 4.** Join everything together.
4. **Two small lemmas.** One gives the shape of a round metric on a small patch of angles; the other continues it to all angles.

Streams 3 and 4 do not yet have exact statements.

Stream 2 has a ready-made answer. **TauCeti's `LeviCivita/Nondegenerate/Existence.lean` proves exactly this existence statement for metrics of any sign pattern.** It is 149 lines, contains no `sorry` (Lean's marker for an unfinished step), is under the Apache-2.0 licence, and cites O'Neill as its source ([TauCeti Existence.lean](https://github.com/TauCetiProject/TauCeti/blob/main/TauCeti/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita/Nondegenerate/Existence.lean)) **[Checked]**. The project should port it with credit, not prove it again and not present it as new.

The project's own guess for the rest is one to three weeks **[Judgement, in PLAN.md]**. Every earlier proof estimate in the plan was too high by a factor of ten or more. Writing definitions and statements has not sped up the same way.

### The method numbers are worth a paper of their own, if framed honestly

Two team runs are measured, each with one lead and nine Claude workers sharing one build queue on one PC ([PLAN.md](https://github.com/flujo-app/gravity-in-lean/blob/main/PLAN.md)) **[Checked]**:

| Run | Result | Wall time | Lean runs | Model use |
|---|---|---|---|---|
| Smooth flows (`smoothFlow`) | about 980 lines, 24 theorems | 14 min 11 s; workers busy only 4 min | 20 runs, 1 failed | 9.4 M tokens read (8.9 M from cache), 178 k written |
| Coordinates fitted to the rotations (`turnsCoordinates`) | about 2,070 lines, 62 theorems | 16 min 42 s | 52 runs, 9 failed and repaired | 16.6 M read (15.8 M from cache), 319 k written; at most 4 points of the weekly allowance |

Two findings carry more weight than the speed.

**First, writing the definitions and statements took longer than proving them.** One person needed 80 minutes for the definitions; the team needed 14 minutes for the proof. Proof estimates ran ten times too high.

**Second, the safety pattern works.** Goals are fixed in files the workers may not change, an audit file checks every declaration, and each definition is tested against cases with known answers: flat space, a sphere, de Sitter space and Schwarzschild.

Raw speed will not impress anyone. Anthropic's Fermat's Last Theorem formalization used dozens of Claude agents for 11 days and produced about 13 million lines from about 6 billion output tokens ([Anthropic](https://www.anthropic.com/research/formalizing-fermats-last-theorem)) **[Notes: summary]**. Reviewers now treat "an AI team formalized X" as routine. A careful split between human design time and team proof time, with costs and failure counts, is still uncommon.

The honest limits must be stated too. There are only two runs. Both ended because the job was finished, so any "per hour" figure is an extrapolation. And nobody checked that the in-between lemmas' comments match their Lean statements **[Checked]**.

## Three questions the research notes disagreed on, settled

### The Riemann Hypothesis has a Lean proof, found by a mathematician working with Claude

The notes disagree. `open_problems.md` reports a certified Lean proof. `venues_and_landscape.md` says "no AI proof of RH exists". The second claim is **outdated**. It rests on secondary reports about an August 2026 partial result: 67.2% of zeros on the critical line. Its sources were written before the 20 November release.

The primary material is clear **[Checked]**. In a four-page note, Levent Alpöge writes that he believes he has, "working with Claude", found a proof. He says it covers the Generalized Riemann Hypothesis too, that he and Claude formalized it in Lean without assumptions, and that he chose to release only the Lean code rather than a 250,000-page machine-written text ([Alpöge, remark.pdf](https://alpo.ge/remark.pdf)). His dated timeline runs from 6 October to 16 November 2026.

On 21 November the **Lean FRO and the Mathlib Initiative jointly certified "that both the statement and the proof of the Riemann Hypothesis are correct"** ([Lean community blog](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/)) **[Checked]**. Their checks were:

- The theorem matches mathlib's own `RiemannHypothesis`, confirmed by two independent comparison tools.
- The library compiles, reproduced by dozens of people.
- Lean's own kernel accepted the exported proof, and so did several independent checkers, two of them themselves formally proved sound.

According to the local video notes, the library is 17.4 million lines with no comments. It covers RH and GRH for Dirichlet L-functions, not the wider families. Some of the strictest check runs were still going on 23 November ([Sutherland's log](https://math.mit.edu/~drew/grh/), via the [Numberphile notes](https://www.youtube.com/watch?v=PjGlt3y-Nco)) **[Notes: summary]**.

The careful phrasing is: **a Lean-checked proof of RH, found by a human mathematician working with Claude, certified by the Lean and mathlib leadership; no human-readable proof exists yet, and it has not been peer-reviewed.** "An AI proved RH" is not supported by the sources. Neither is "no AI has proved it".

What this means for the project **[Judgement]**:

- Machine-checked proofs by themselves are no longer news.
- The RH result could be trusted quickly because its *statement* already lived in mathlib and had been vetted. The project's Birkhoff statement rests on brand-new definitions. Its credibility therefore depends on human review of those definitions, not on the size of the proof.

### Raychaudhuri and the causal theory exist; an unconditional singularity theorem does not

The three notes are each partly right. Here is what exists in code.

**Raychaudhuri's equation and focusing are done in Lightlike** **[Checked: API map]**. Raychaudhuri's equation describes how a bundle of free-falling paths spreads or converges; focusing means that ordinary matter forces it to converge. Lightlike has:

- the identity for timelike paths in coordinates, with its split into expansion, shear and rotation;
- the same identity on manifolds;
- the null (light-ray) version, with a screen projection;
- focusing within (n−1)/|θ₀| for timelike paths and (n−2)/|θ₀| for light rays;
- the Riccati lemma behind focusing.

See ([Lightlike Spacetime API map](https://github.com/LightLikeProject/lightlike/blob/main/Lightlike/Spacetime/API-map.md)). ProjectAinos has a version for "synchronous" metrics **[Notes: code]**. So the suggestion in `mathlib_foundations.md` that Raychaudhuri would be a cheap first is wrong.

**Causal theory exists as working code in Lightlike, and only there.** Causal theory is the mathematics of which events can affect which. Lightlike's `Spacetime/Causal` and `Spacetime/CausalLadder` folders hold 86 files **[Checked: file tree]**. Their API map, marked "Alpha", lists the following as proved:

- time orientation, causal and timelike curves, and chronological and causal futures;
- transitivity of the futures, and "causality implies chronology";
- the closed light cone and global hyperbolicity of flat Minkowski space;
- "Cauchy surfaces are closed and achronal";
- the push-up lemmas, derived from openness;
- the limit-curve theorem.

Global hyperbolicity is the property that the future is fully determined by a "now" slice. Proofs of two tasks landed on 18 and 19 November: the limit-curve theorem (task P20) and "causal simplicity implies stable causality" (task P11) ([Lightlike causal API map](https://github.com/LightLikeProject/lightlike/blob/main/Lightlike/Spacetime/Causal/API-map.md); [commit history](https://github.com/LightLikeProject/lightlike/commits/main/Lightlike/Spacetime/CausalLadder)) **[Checked]**.

It is not finished. Lightlike's definition of a timelike curve deliberately differs from the textbooks: it adds a "margin", approved by its maintainers on 17 November. Whether that changes anything is an open task. Its exponential map and local causality work on one chart of ℝⁿ, not yet on a general manifold **[Checked: file headers]**. `mathlib_foundations.md`'s "nobody has the causal theory" is true of mathlib, TauCeti and physlib, and **false for Lightlike**.

**A singularity theorem exists only in conditional form.** ProjectAinos's `SingularityTheorem.lean` proves a Hawking-type bound, length ≤ 3/C, inside one coordinate chart **[Checked]**. It takes as a *premise* that every point is reached by a path that maximizes proper time. The file says the construction of those paths from global hyperbolicity "is not part of this file". It proves the premise only for special cases: synchronous metrics, Kasner and contracting dust ([SingularityTheorem.lean](https://github.com/x-oai/ProjectAinos/blob/main/ProjectAinos/GeneralRelativity/SingularityTheorem.lean)). Lightlike's `BigBangSingularity.lean` is an ODE fact about the Friedmann equations for an expanding universe, not a singularity theorem **[Checked]**. Penrose's theorem (Lightlike milestone GE4, "research-level") and Hawking's (CO3) are open there ([Lightlike task board](https://github.com/LightLikeProject/lightlike/blob/main/docs/tasks/README.md)) **[Checked]**.

**Verdict.** "First machine-checked singularity theorem" is still available only for an **unconditional** version, one that proves the maximizing paths exist rather than assuming them. Lightlike already has most of the groundwork, and it was still pushing new commits on the day this report was written.

### TauCeti: reuse its pieces, don't race it, and plan around three Lean versions

TauCeti is an AI-written library downstream of mathlib, "human-directed and human-reviewed", incubated by the Lean FRO and the Mathlib Initiative. It states it will not push material into mathlib **[Notes: code/README]**. It was created on 2 June 2026, is Apache-2.0, has 320 stars, and was pushed on 24 November **[Checked]**. **Its toolchain is Lean v4.37.0-rc1 on mathlib master** **[Checked]**.

It has much of what mathlib v4.36.0 lacks **[Notes: code]**:

- curvature and the Bianchi identities;
- geodesics, the exponential map and Hopf–Rinow;
- Jacobi fields and Rauch comparison;
- Stokes and divergence theorems;
- Frobenius;
- any-signature metrics with their connection;
- asymptotically flat ends with the ADM mass flux.

It has **no causal or Lorentzian roadmap**, and an early-stage **PositiveMass** roadmap.

Three Lean versions are in play: Lightlike on v4.35.0, this project on v4.36.0 and TauCeti on v4.37.0-rc1. **None of them can import another as-is.** Lean libraries must match versions exactly. Practically this means three things **[Judgement]**:

1. For Birkhoff, port the one TauCeti file needed, with attribution.
2. For any target in ordinary curved-space geometry (positive mass, Penrose inequality, static uniqueness), move to mathlib master and depend on TauCeti. Rebuilding its library would take months and duplicate a team that is ahead.
3. Do not start a solo positive mass theorem. TauCeti's team is aiming at the same theorem with more of the foundations already built.

## Level 2: famous theorems offer one quiet lane and several crowded ones

The table pulls the three notes together. Sizes are the researchers' estimates in "AI-team" terms: **small** means days and **huge** means many months. Most of the cost is in designing new definitions, not in proof lines.

| Target (plain meaning) | Machine-checked elsewhere? | What Lean/mathlib v4.36.0 lacks | Size | Race risk | Verdict |
|---|---|---|---|---|---|
| Raychaudhuri and focusing (matter makes bundles of paths converge) | **Yes**: Lightlike, coordinates and manifolds, timelike and null **[Checked]** | nothing new | small | taken | Not a first. Reuse or cite. |
| Hawking 1967 cosmological singularity theorem (a universe contracting everywhere must have a beginning or end) | Conditional only: ProjectAinos assumes maximizing paths **[Checked]** | causal theory on manifolds; existence of maximizing paths (Avez–Seifert); focal points; manifold exponential map | large (guess 5–20k lines with library) | **high**: Lightlike task CO3 | Best fame per effort, but only together with Lightlike |
| Penrose 1965 (a trapped surface forces a singularity; Nobel 2020) | No; Lightlike GE4 open **[Checked]** | all of the above plus achronal boundaries, trapped surfaces, invariance of domain | large (guess 15–40k lines) | **high** | Join, don't race |
| Hawking–Penrose 1970 | No | plus genericity conditions and chronology-only theory | large+ | medium | Later |
| Hawking area theorem (horizon area never decreases) | No; Lightlike SC5 open **[Checked]** | null infinity, low-regularity horizons | huge | low | No |
| Positive mass theorem, 3-D (total mass of an isolated system is not negative) | No; TauCeti roadmap at layer 0 **[Notes: code]** | weighted elliptic theory, plus minimal surfaces, spinors or harmonic level sets; coarea formula | huge alone, large on TauCeti | **high**: TauCeti | No solo attempt |
| Riemannian Penrose inequality (mass ≥ √(horizon area/16π)) | No | needs positive mass, plus inverse mean curvature flow or Bray's flow | huge | low | No |
| Static black-hole uniqueness, Israel form (a static black hole must be Schwarzschild) | **No, and no roadmap found anywhere** | Hessians, divergence theorem with boundary, Gauss–Bonnet, level-set geometry; the final step "round ⇒ Schwarzschild" reuses Birkhoff | large (with stated assumptions) | **low** | Best uncontested next target |
| Kerr uniqueness, Bunting–Masood-ul-Alam | No | positive mass in low regularity | huge | low | No |
| Stability of Minkowski, Schwarzschild, Kerr | No | quasilinear wave equations on curved spaces: absent everywhere; proofs run 100–1,000+ pages | huge | none | Out of reach |
| Smaller classics: Kerr is a vacuum, Einstein's equations from an action, FLRW, perihelion and light bending, Kruskal | **Yes**, in Lightlike and/or ProjectAinos **[Notes: code]** | — | — | taken | Not firsts |
| Buchdahl bound (a static star cannot be smaller than 9/8 of its Schwarzschild radius) | Not found; physlib proves a related junction bound for constant density **[Notes: code]** | a few thousand lines on the star equations (TOV) | small–medium | low | A good companion section |

Sources for the table: Lightlike ([API map](https://github.com/LightLikeProject/lightlike/blob/main/Lightlike/Spacetime/API-map.md), [tasks](https://github.com/LightLikeProject/lightlike/blob/main/docs/tasks/README.md)); ProjectAinos ([ledger](https://github.com/x-oai/ProjectAinos/blob/main/docs/cinfty-general-relativity.md)); TauCeti roadmaps ([TauCetiRoadmap](https://github.com/TauCetiProject/TauCetiRoadmap/tree/main/TauCetiRoadmap/RiemannianGeometry)); physlib ([IncompressibleSphere.lean](https://github.com/leanprover-community/physlib/blob/master/PhyslibAlpha/Relativity/General/Schwarzschild/IncompressibleSphere.lean)).

**What mathlib v4.36.0 itself lacks** sets the scale of all of this **[Notes: code, against the local copy]**. mathlib stops one layer below curvature. It has manifolds, vector fields, flows and a Levi-Civita connection, but only for positive-definite metrics. There is no curvature tensor, no geodesics, no indefinite metrics, no differential forms or integration on manifolds, no Gauss–Bonnet, no coarea formula, no invariance of domain, and no wave-equation estimates. The project has filled some gaps itself: curvature and Ricci on its own terms, uniqueness of the connection for indefinite metrics, smooth dependence of flows, and rotation-adapted coordinates. Curvature, Christoffel symbols and geodesics exist upstream only in an open placeholder pull request, mathlib #36036 ([PR #36036](https://github.com/leanprover-community/mathlib4/pull/36036)).

**Why the singularity theorems are the obvious prize.** Penrose's original paper is under three pages. It earned half of the 2020 Nobel Prize in Physics. Its proof needs no PDE (equations for how fields change across space and time), only causal theory plus an ODE comparison along one path ([Steinbauer review](https://pmc.ncbi.nlm.nih.gov/articles/PMC10228498/); [Nobel popular information](https://nobelprize.org/prizes/physics/2020/popular-information/)). The smallest honest version is Hawking's smooth theorem: a globally hyperbolic spacetime, ordinary matter, and a "now" slice that is contracting everywhere together imply that no free-fall path from that slice lasts longer than (n−1)/β **[Judgement, from landmark_theorems.md]**.

**Why to step back from that prize anyway.** Lightlike already has the limit-curve theorem, the Raychaudhuri and focusing lemmas, and an exponential map with the Gauss lemma in charts. It lists both theorems as its own milestones. Racing a team that is weeks ahead on the groundwork risks losing the "first" in the middle of the work. The better course is to open an issue with Lightlike and offer to contribute. Both projects are Apache-2.0, and a shared paper is credible **[Judgement]**. If Lightlike declines or stalls, the theorem returns to the list.

**Why static uniqueness fits this project.** Israel's 1967 theorem says a static, isolated, empty black hole with a regular horizon is Schwarzschild. Its proof ends with "the level sets are round spheres, so the spacetime is spherically symmetric, so Birkhoff applies". That last step is exactly what the project will own. No library has it, and no roadmap names it. It needs the Riemannian layer that TauCeti largely has. The honest version states its assumptions (a connected horizon whose gradient does not vanish) in the title **[Judgement, from mathlib_foundations.md]**.

## Level 3: new mathematics means certificates, not famous conjectures

The large open problems are not realistic targets:

- weak and strong cosmic censorship (whether singularities are always hidden behind horizons);
- the final-state conjecture;
- black-hole uniqueness without analyticity;
- the sharp spacetime Penrose inequality;
- the hoop conjecture.

They need new ideas, and the Lean foundations for PDE on curved spaces do not exist ([Van de Moortel review](https://arxiv.org/html/2501.13180)) **[Notes: summary]**.

Kerr stability, the question whether a spinning black hole settles down after being disturbed, has moved fast but is not settled. Full-range linear stability is claimed by Häfner–Hintz–Vasy ([arXiv 2506.21183](https://arxiv.org/pdf/2506.21183)). **Szeftel's preprint claims to complete the nonlinear Kerr stability conjecture in 166 pages**, posted 30 September and revised 5 November 2026. It is not yet refereed ([arXiv 2609.40068](https://arxiv.org/abs/2609.40068)). Machine-checking it is out of reach for years. The search for any AI-produced new theorem in general relativity found none **[Notes: summary]**.

The opening is in **finite, computer-checkable statements**: special solutions that reduce to ordinary differential equations and can be proved with rigorous error bounds (interval arithmetic). Two such proofs already exist on paper with computer help:

- Reiterer and Trubowitz proved that Choptuik's critical-collapse solution exists, using integer-only arithmetic and an 80-digit data file. It was published in Communications in Mathematical Physics in 2020 ([CMP](https://link.springer.com/article/10.1007/s00220-019-03413-8)).
- Goldstein and Jejjala proved that a non-Schwarzschild black hole exists in Einstein–Weyl gravity, an extension of Einstein's theory. They used Taylor models and a fixed-point argument and proved existence only, not uniqueness ([arXiv 2609.21797](https://arxiv.org/abs/2609.21797)).

Researchers' ranking of fit **[Judgement]**:

1. Re-check one of these in Lean. That would be the first formally verified critical-collapse solution, which is new as a verification but not new mathematics.
2. Prove the missing **uniqueness** of the Einstein–Weyl solution, or a continuous family of such solutions. That would be new mathematics.
3. Show that Choptuik's solution has **exactly one unstable mode**. This is open, and it is the source of the 0.37 critical exponent ([review arXiv 2507.07636](https://arxiv.org/pdf/2507.07636)).
4. Prove mode stability for Kerr–de Sitter black holes on explicit parameter ranges. Mode stability means no small vibration grows exponentially. It is the missing hypothesis of a 2025 conditional stability theorem ([arXiv 2508.06620](https://arxiv.org/pdf/2508.06620)).

Two cautions. **Nobody has checked whether Lean has a mature library for interval arithmetic or for enclosing ODE solutions**, and every item above depends on one. Checking that comes before any commitment. And these targets pull the project away from its geometry library towards numerics. They suit the AI-team method well: a fixed statement, a large mechanical proof, Lean as judge. They do not build on Birkhoff.

The second limit is conceptual. Alpöge's note says he guided the work to the right setting and Claude then supplied the technical steps ([remark.pdf](https://alpo.ge/remark.pdf)). Nothing in this project yet shows the workers supplying the *idea* for an open problem; they have proved statements a human set **[Judgement]**.

## Where to publish in 2027, and the human-author rule

| Venue | Kind | 2027 timing | Best for | AI rule |
|---|---|---|---|---|
| Annals of Formalized Mathematics | diamond open-access journal | rolling; post to arXiv/HAL/Zenodo first | Birkhoff mathematics plus formalization lessons | **"Only human-authored manuscripts"**; disclose AI use for text and code; known results need "insight", not just "first" ([AFM instructions](https://afm.episciences.org/page/instructions-for-authors); [scope](https://afm.episciences.org/page/aims-and-scope)) |
| CADE-31, Nijmegen, 22–25 Aug 2027 | conference, Springer LNCS | **abstracts 15 Feb, papers 22 Feb 2027** ([FSCD-CADE 2027](https://fscd-cade.science.ru.nl/)) | the AI-team method and measurements | Springer: AI not an author; document use in methods ([Springer](https://www.springer.com/us/editorial-policies/artificial-intelligence--ai-/25428500)) |
| ITP 2027 | conference, LIPIcs | no call yet; 2026 deadlines were 12/19 Feb, so likely Feb–Mar 2027 **[Judgement]** ([ITP 2026 CFP](https://itp-conference-2026.github.io/cfp)) | library plus method; 16-page limit, double-blind | declare substantial AI use |
| CPP 2028 (CPP 2027's deadline passed in Sept 2026) | ACM conference with POPL | likely Sept 2027 **[Judgement]** | library design | **desk rejection if the work is "primarily the result of the tool's generative capabilities"**; the riskiest venue ([CPP 2027 CFP](https://discourse.rocq-prover.org/t/cfp-cpp-2027-certified-programs-and-proofs/3063)) |
| NeurIPS MATH-AI / AITP 2027 | workshops, mostly non-archival | not announced (2026 deadline 6 Sep; AITP 2027 listed for early Sept, unconfirmed) | quick visibility for the method | NeurIPS is strict on AI-written text ([NeurIPS blog](https://blog.neurips.cc/2026/06/02/ai-generated-papers-in-the-neurips-2026-position-paper-track/)) |
| Computer Physics Communications | Elsevier physics journal | rolling | a library paper for physicists (HepLean precedent) ([arXiv 2405.08863](https://arxiv.org/abs/2405.08863)) | declare AI use in methods ([Elsevier](https://www.elsevier.com/en-gb/about/policies-and-standards/the-use-of-generative-ai-and-ai-assisted-technologies-in-writing-for-elsevier)) |
| arXiv (cs.LO, cross-listed to gr-qc and math-ph) | preprint | any time; **this is what dates a priority claim** | — | authors fully responsible; news reports a one-year ban for unchecked AI content ([TechCrunch](https://techcrunch.com/2026/05/16/research-repository-arxiv-will-ban-authors-for-a-year-if-they-let-ai-do-all-the-work)) |

No CICM 2027 call was found. Every publisher checked agrees that AI cannot be an author, a human takes full responsibility, and AI use must be disclosed. mathlib's contribution page warns that AI-written code falls far short of its standard and prefers that such code first prove itself downstream ([mathlib contributing](https://leanprover-community.github.io/contribute/)) **[Notes: summary]**.

**The practical consequence is a staffing question, not a writing one** **[Judgement]**. The proofs can be AI-written if disclosed. The manuscript, the explanation of how each formal statement matches the textbook statement, and the design rationale must come from a person who can defend them. The project owner is not a relativist. The strongest papers would therefore add a human co-author who is: a relativist for AFM, or a Lean formalizer for ITP or CADE. The owner remains the author of the method and the measurements.

## Ranked recommendation and the checks before saying "first"

| Rank | Target | Why | Venue and timing |
|---|---|---|---|
| 1 | **Finish coordinate-free Birkhoff**: port TauCeti's connection existence, write the statements for streams 3–4 with a second reader, and run the team | Small, nearly done, still a first, and covers the black-hole interior | Make the repository public and post to arXiv/Zenodo as soon as it is green; AFM (rolling); method paper at **CADE-31 by 22 Feb 2027** |
| 2 | **Static black-hole uniqueness (Israel form, assumptions in the title)** | Nobody has it or plans it; its last step is Birkhoff; it is a natural "paper 2" | Requires moving to mathlib master plus TauCeti; ITP 2027 or AFM, late 2027 |
| 3 | **Hawking 1967 singularity theorem, unconditional, smooth**, done *with* Lightlike | Highest fame per effort, but Lightlike owns the groundwork and the milestone | Open an issue with Lightlike now; joint paper if accepted |
| 4 | **A certificate-type new result** (Einstein–Weyl uniqueness, or a Choptuik re-check) | The only realistic route to new mathematics | Only after confirming Lean has interval and ODE-enclosure tools |
| 5 | Quick sections: Buchdahl bound; Birkhoff with a cosmological constant, with charge, or in n dimensions | Cheap, low novelty; strengthens paper 1 or 2 | Inside other papers |
| Not now | Solo Penrose 1965, positive mass, Penrose inequality, area theorem, any stability result, open conjectures | Crowded (Lightlike, TauCeti) or years of missing foundations | — |

The checks before any "first" claim are concrete. All are **[Judgement]**, drawn from the researchers' notes and the RH precedent.

1. **Make it public and dated.** The repository is private today, so no priority exists. ProjectAinos's date is public.
2. **Compare statements word for word** with ProjectAinos's `birkhoff` and grlab's `Birkhoff.lean`. Phrase the claim narrowly, for example: "to our knowledge, the first machine-checked Birkhoff theorem from coordinate-free symmetry hypotheses, in any proof assistant, including the region inside the horizon". Credit ProjectAinos (19 Nov 2026) and grlab (Aug 2026) as earlier coordinate versions.
3. **Re-search on the day of submission.** Cover Lightlike, ProjectAinos, TauCeti, physlib pull requests #968 and #2132, mathlib #36036, a GitHub code search, the Isabelle Archive of Formal Proofs, Rocq, HOL and Mizar, and the Lean "1000+ theorems" list. Ask on the Lean Zulip and on the Lightlike and ProjectAinos issue trackers. All three AI libraries changed within the last week.
4. **Pass Buzzard's four checks.** The Lean statement must match the paper. It must compile. A comparator tool must confirm the proved theorem is the fixed statement. And a "paranoid" multi-kernel check must rule out tricks with Lean itself. Add an axioms printout and a reproducible build ([Xena blog](https://xenaproject.wordpress.com/2026/11/12/and-the-proof-is-checked-in-lean/)).
5. **Get a human expert to read the definitions and the goal statement.** Unlike RH, Birkhoff's statement is not in mathlib, so its trustworthiness rests on new definitions. Also close the plan's own gaps: no test yet across a real change of chart, and no test that "looks the same from every side" can fail.
6. **Disclose the AI system** (models, versions, team set-up) in a methods section, and list only humans as authors.

## Conclusion

In late 2026, "first machine-checked X" has become a race among AI-built libraries that appear and grow within days. Proof size no longer limits anyone, as a 17-million-line RH proof shows. What limits the field is trusted definitions and an open lane. So the project's real asset is not its speed but its discipline: goals fixed in protected files, definitions tested against known answers, and a measured record showing that design, not proving, is the slow part. That discipline makes a narrow, well-defended first credible.

The strategic picture also changed. The project should treat Lightlike and TauCeti as partners and suppliers, not rivals: port what they have proved, offer what they lack, and stay in the quiet lane the project's own work leads into. That lane runs from Birkhoff to static black-hole uniqueness, a theorem whose final step only this project currently owns.
