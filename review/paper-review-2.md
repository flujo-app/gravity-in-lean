# Review 2 of Paper 1: a hostile round

**Reviewed:** `paper/paper.md` and `paper/plain-summary.md` at commit `7ef6544` (main, after
pull request 64), with `paper/checklist.md` and the repository as the record.
**Date:** 25 November 2026 (UTC).
**Who:** Claude Opus 5.5, in one Claude Code session, with two fresh instances of the same model
that were given only the repository and a brief: one read the mathematics against the Lean
files, the other checked every number, date, commit and claim about the record. Neither edited
anything. Each of their findings was checked again against the repository before anything
changed. Because the same model wrote much of the paper, this is not an outside review; the
checklist keeps that item open.

## In short

About forty findings, all on the text and the record. **None is about the theorems or the
definitions**: both readers found that the Lean statements say what the paper says they say,
and that the mathematics of Section 5 is right. No Lean file changed. One finding needed a
change outside the paper: the workflow "Check the proofs" did not build from scratch, as the
paper said it did; it restored a saved build of an earlier commit. It now builds from source.

The most important findings, in plain words:

1. The paper said the CI build was a build from scratch. It was not (finding 1).
2. The paper said a classification of all maximal space-times was stated in Lean. Only a
   narrower one is; the full one is an open problem (finding 2).
3. The abstract said all 25 tests are cases where a definition must fail. Thirteen are
   (finding 3).
4. The review "against the textbooks" covered only the first definitions; the later ones had one
   AI reader each (finding 4).
5. The paper did not say what its own research notes say: the global theorem follows from the
   every-point theorem by a known argument, and experts may call it folklore (finding 5).
6. The team briefs in the repository were edited after the runs; the paper now names the
   versions that were handed out (finding 6).
7. The human author read the paper before both AI reviews of the text; Section 10 now says so
   (finding 10).

## Findings and what was done

Source: **M** = this session's own reading, **A** = the reader for the mathematics, **B** = the
reader for the record. Every finding below was confirmed against the repository.

### Important

| # | Finding | Source | Done |
|---|---|---|---|
| 1 | Section 8, Section 9 and the checklist said the workflow "Check the proofs" builds from scratch on a clean machine. It used `lean-action`'s GitHub cache: at the tag's commit it restored a saved 2 GB build and rebuilt nothing (run 45327015167). Only "Compare statements" built the project from source. | B | `.github/workflows/check.yml` now passes `use-github-cache: false`, so every push builds the project from source (mathlib's prebuilt files only). Sections 8 and 9 and the checklist say what was true when. |
| 2 | Sections 4 and 8 said the classification of all maximal or inextendible space-times is "stated but not proved". `GlobalComplete` assumes a completeness condition (every geodesic that stops has r → 0); the full classification is open (Chruściel: "remains to be seen"; infinitely many maximal ones, his Remark 1.2.9). The error came in with the fix for review 1's F4. | A | Both sections split the two: the full classification is not stated and open; a narrower one is stated, not proved. |
| 3 | Abstract: "25 tests in which a definition must fail". 13 of the 25 are failures; 12 show that the other hypotheses hold in the same examples. | A, B | Abstract, Section 6, plain summary and checklist give 13 of 25. |
| 4 | Abstract, Section 6 and the plain summary presented the textbook review as covering the definitions in general. `REVIEW.md` reviewed commit `600b6a2` (the core definitions and `BirkhoffNoCoordinates`), before every later statement file; only the relativist compared with the textbooks. | A, B | Abstract, Section 6 item 3, Section 9 item 1, plain summary and checklist give the scope. |
| 5 | The abstract said "no complete written proof ... for the global statement" without saying what `Goals/Global.lean` and `review/global-birkhoff.md` say: it follows from the every-point theorem by the argument of the classical extension theorem (Kobayashi–Nomizu VI.6.3; Chruściel Thm 1.4.4), which those sources state for analytic metrics; experts may regard it as folklore. | M, B | Abstract and Section 2 say so; the plain summary has it as a sentence to defend. |
| 6 | Section 9: "the briefs ... are in the repository". All seven `fleet/goal-*.md` were edited after the last run (`8e5858e`), and run 4's after its run (`0c601e4`, Part 3 replaced by "withdrawn"). | B | Section 9 names the commits at which each brief was handed out (`2435611`, `7449b7e`, `8b249e9`, `de245a3`, `cf98a9b`, `79efdde`, `d34c333`) and says what changed later. |
| 7 | The header said every number is recorded in `PLAN.md` or the repository's run logs. Most figures of the local checker runs (Section 9, items 3 and 4) are in no tracked file; their logs were not kept (searched for on this PC; not found). | B | Header says where each kind of number is recorded. Checklist: keep such logs in the repository next time. |
| 8 | "each later set of statements took about 20 minutes to write and 12 to 13 minutes to read": only run 4's set is recorded (20 and 12). | B | Section 7 says run 4's and that the others were not recorded. |
| 9 | Section 10 named the AI systems for the proofs and the first draft, not for the revisions or for outside review 1. | B | Section 10 covers "the first draft and all its revisions", review 1 and review 2. Which system wrote review 1 is not recorded anywhere this session could read; Section 10 says so and the checklist asks the author to add it. |
| 10 | "The human author has read the manuscript in full": that reading (commit `a26e6f7`) came before both AI reviews of the text and before the sandbox and comparator sections. | B | Section 10 says which version was read. Checklist and plain summary: re-read the current one. |
| 11 | Section 9: "It ran twice." The comparator had run at least four times; with the main-branch pushes, seven (one cancelled run aside). | M, B | Section 9 gives the runs. |
| 12 | "What was changed after a run" left out the leads' edits in runs 3, 5 and 6, a worker's extra `omit … in` lines in run 5, and the unused assumption the supervisor removed after run 1. | B | Section 7 lists all of them. |
| 13 | Plain summary: "one map **onto** Kruskal's black hole" (the map is into, and need not be one-to-one); and "exactly when ... for the whole space-time" (the forward direction needs a simply connected region). | M, A, B | Both corrected. |
| 14 | The committed `paper/paper.pdf` was built at `ce48042`, before review 1's fixes, and still showed the errors review 1 found. | M, A | Rebuilt from this branch by the workflow "Build the paper" and committed. |
| 15 | Section 1 and the plain summary said the statements "could not be changed by the teams". Nothing in the set-up prevented it; the briefs forbade it and the supervisor's diff checked it afterwards (Section 7 had this right). | M, A, B | Section 1 and the plain summary say so. Checklist: make the statement files read-only for later runs. |

### Minor

| # | Finding | Source | Done |
|---|---|---|---|
| 16 | Section 8 "Established" said each theorem has "the type that was fixed before its proof, by a check that is part of every build". The build checks the type in the current statement file; that the file is the one fixed beforehand rests on the git history. The comparator cannot show it either: question and answer are built from the same statement files. | M, A | Sections 8 and 9 and the plain summary say which check shows what. |
| 17 | Section 3: "harmless because the connection is unique and exists". Uniqueness is on differentiable fields, and curvature applies the connection to ∇_Y Z; the missing step is proved (`curvatureAt_eq_of_isConnectionOf`, `ricciAt_eq_of_isConnectionOf`, `curvatureAt_carry`) but was not cited. | M, A | Section 3 gives the full reason and the names. |
| 18 | "Three independent reviewers", "an independent second reader": separate instances of one model are not independent in the usual sense. | M, A, B | Section 6 says "separate" and why that is weaker. |
| 19 | Section 8: an SO(3) action gives `IsRoundOn`, "so the theorem here is at least as strong". Only for smooth metrics: the textbook theorem also covers C². | A | Section 8 says so. |
| 20 | Section 4: "four quotients by a reflection" (the involutions are fixed-point free: the antipodal map of the sphere with T ↦ ±T, X ↦ ±X); "complete in a sense defined through geodesics" (the condition allows geodesics that stop with r → 0); the non-Hausdorff example stated as fact although `GlobalCompleteNeedsHausdorff` is unproved; Section 5 "a rotation or a reflection" (O(3)). The first three came in with the fix for review 1's F4. Chamblin and Gibbons, who list the quotients, were not cited. | M, A | All four reworded; Chamblin and Gibbons cited. |
| 21 | Section 4 table: `BirkhoffExactlyWhenInCoordinates` dropped its hypothesis that the gradient of the area radius is nowhere null. | A | Added. |
| 22 | Section 1: adapted coordinates are "usually taken for granted"; Hawking and Ellis cite B. Schmidt (1967) for them. Section 2: H.-J. Schmidt (1997) "avoids introducing coordinates", but starts from the warped-product form, after the step `turnsCoordinates` provides. | A | Both reworded; B. Schmidt (1967) added to the references. |
| 23 | Section 2: "Hawking and Ellis treat it in one sentence" (they join the two forms across the horizons and do not treat the bifurcation sphere separately); Schleich and Witt, who claim charts across both horizons, were not mentioned at that point. | A | Section 2 says both, the second as "in our reading". |
| 24 | Section 2 stated as fact some items that `SURVEY.md` marks "Not verified" (the preprint, physlib's pull requests, the Isabelle work); `SURVEY.md` still marked grlab "Not verified" although the paper reads its source. | A | Section 2 says how each is known; `SURVEY.md`'s grlab row updated. |
| 25 | Plain summary: "for each notion there is a checked example where it does not hold"; no test makes `IsConnectionOf` fail. | A | Reworded. |
| 26 | Section 7: the shared build and the route on paper are written as true of every run; both began with run 2. | B | Section 7 says "from run 2 on". |
| 27 | Section 6: "Section 3 names two" gaps found by the second reader; it named one. The second (nothing ruled out a second connection, `PLAN.md`) was credited nowhere. | B | Section 3 now names it. |
| 28 | Section 1: "They were written by teams", against the abstract's "Most of the proofs". | M, B | "Most of them". |
| 29 | Checklist boxes out of date: the comparator box still described sixteen statements; the excerpt box said "copied". | B | Updated. |
| 30 | "about 27,400 lines": the table adds to 27,450. | B | "about 27,450". |
| 31 | Tokens counted until "a few minutes after its goal": 13 minutes for run 2; for runs 1 and 4 to 7 the record does not say. | B | Section 7 says so. |
| 32 | `ConnectionUniqueStatement` listed with the final statements, but outside the 54 and, at the tag, without an `example` line in `Audit.lean`. | B | Section 4 says who wrote and proved it, and when; Section 9 says the audit line came on 24 November. |
| 33 | The three statements of `Goals/GlobalComplete.lean` proved since the tag were not named. | B | Named in Sections 4 and 9. |
| 34 | "files were only added, and lines added to the audit": `GravityInLean.lean` and `lakefile.toml` changed too (no proof file did). | B | Added. |
| 35 | References: Kruskal 1960 and Szekeres 1960 listed but not cited as works; the Chruściel entry had no year or publisher. | B | Cited in Section 4; Chruściel entry completed. Kobayashi–Nomizu, Chamblin–Gibbons and B. Schmidt added for the new sentences. |
| 36 | The comparator's export of 57 statements counts about 56,000 declarations; `leanexport`'s export of the sixteen headline theorems, a subset, counts 58,081. | B | Section 9 says the tools count differently and that the difference was not traced. |
| 37 | Run 3's Lean runs: 79 in `PLAN.md` (ten of them set-up builds), 70 in the team's record. The test-run sentence put twenty minutes on all three set-up faults; `PLAN.md` puts it on one. | B | A note under the table; the sentence corrected. |
| 38 | Section 8: the intermediate lemmas "were read by nobody but their authors"; review 1 read about twenty-five proof files. | M | Corrected. |
| 39 | Section 5 announced "three layers" and then gave five parts; Section 9 said "every statement file loads its proof" (some do). | M | Corrected. |

## Checked and found sound

So that silence means something:

- **Statements and definitions** (reader A, by the Lean source): the five excerpts match the
  files; `outside`, `inside`, `roundG`, `IsKruskalNear`, `kruskalR` and its two specification
  statements; `IsKruskalMapOn` and `IsSchwarzschildMapOn` are local isometries into the model
  (smooth, image in the model, pullback of the model's metric; differential injective);
  the symmetries of `GlobalBirkhoffUnique` are the full isometry groups (O(1,1) × O(3) for
  Kruskal, time shift or reversal × O(3) for negative mass, the whole Poincaré group for mass
  zero), on a region only required to be in one piece; `GlobalBirkhoffConverse` and
  `GlobalMassUnique` as described; the quantifier order of the one-mass statements; the
  connection statements (any finite dimension, model with corners, open set; uniqueness on
  differentiable fields).
- **Section 5 mathematics**, redone by hand: Kretschmann 48m²/r⁶ and the sign of the project's
  contraction; the Hessian of r (m/r² on the plane, (r − 2m)/r² on the sphere, equal only at
  r = 3m, never for m < 0); no shift because X² − T² is kept; `product_form` for Ω = UV.
- **The record** (reader B): first commit and tag times (27.1 hours); 199 files, 39,406 lines,
  about 1,550 theorems and 2,605 audited declarations at the tag; every row of the run table,
  the sums, the token counts and both usage meters against `PLAN.md` and the team records;
  57 and 80 minutes, about an hour of fleet set-up, one to three weeks, about four hours,
  7 min 35 s; second readings recorded before each of the seven runs; the network rules as
  handed out; all 54 statements and the definitions they use unchanged after their runs began,
  except in comments; `ConnectionUniqueStatement` written 24 minutes before its proof; the
  comparator workflow runs, commits, durations and 58 statements; no Lean proof file changed
  between the tag and the comparator commits.
- **Outside repositories**, read on 25 November through GitHub: ProjectAinos's `birkhoff` and
  `birkhoff_timeChange`, grlab's open interval, Lightlike's `KruskalMaximal.lean` (19 November)
  and still no Birkhoff file, TauCeti's existence file, BishopWolf's folder, physlib's open pull
  requests; mathlib v4.36.0 has no smooth dependence of flows on the starting point, and its
  Levi-Civita file covers Riemannian metrics only.
- **A new search** (GitHub code and repository search, read-only, 25 November): no new
  machine-checked Birkhoff theorem. This is not the search on the day of submission that the
  checklist asks for.

## Not checked

- Anything that needs Lean to run: no build was needed, since no Lean file changed. The
  workflow "Check the proofs" on this branch is the first run without the cache.
- The figures of the local checker runs (logs not kept), the raw records of runs 1 to 4, 6 and
  7 (network use), and which AI system wrote review 1.
- The textbooks themselves (Hawking and Ellis, Wald, O'Neill) and the papers of Schmidt and of
  Schleich and Witt: the descriptions rest on `review/global-birkhoff.md`.
- Whether the unproved statements of `Goals/GlobalComplete.lean` are true.
