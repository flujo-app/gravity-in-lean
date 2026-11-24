# Before submitting

What is still needed before [paper.md](paper.md) goes anywhere. This is the only list: issue 34
points here and keeps no boxes of its own. Tick a box only when the thing is done and written
down where others can see it.

[paper.tex](paper.tex) and [paper.pdf](paper.pdf) are made from paper.md by
[tools/md2tex.py](tools/md2tex.py) and the workflow "Build the paper". Edit only paper.md, run
`python paper/tools/md2tex.py`, and take the new PDF from that workflow's run (artifact
`paper-pdf`).

## The claim

- [ ] **Search again on the day of submission** for machine-checked Birkhoff theorems, in Lean,
      Isabelle, Coq/Rocq, HOL, Mizar, on GitHub and arXiv. Record the date and what was found in
      `SURVEY.md`. If anything turns up, change Sections 1 and 2 before submitting.
- [ ] **Ask in the Lean community chat** whether anyone knows earlier work (issue 2).
- [x] **Compare the statement word for word** with ProjectAinos's `birkhoff` and grlab's
      `Birkhoff.lean`: the table "Side by side" in Section 2, from the source files read on
      24 November 2026. Read them again on the day of submission; both projects change often.
- [ ] **Verify every reference** against the source: authors, title, year, volume, pages. The
      draft marks the list as unverified. Do not describe Schmidt's method beyond "avoids
      introducing coordinates".
- [ ] Keep every priority claim as "to our knowledge" or "not found written down". No "first",
      no "new".
- [ ] In reader-facing text say "horizon" and "inside the horizon", not "rim": an outside reader
      took "including the region inside the rim" to mean the horizon itself.

## The text

- [x] **Outside review 1** (24 November 2026, `review/paper-outside-review-1.md`): fifteen
      findings, all on the text, none on the theorems or definitions. Worked in; what was done
      with each is at the end of that file.
- [ ] **Before each new version, read the whole paper against the repository.** Every paragraph
      that goes run by run covers all seven runs; every number is taken again from `PLAN.md`,
      the `STATUS.md` files or the audit; Section 8 agrees with Section 9; the abstract claims
      nothing the statements do not say. The outside review found that late additions (run 7,
      the sandbox checks) had left older paragraphs behind.
- [ ] **One more outside review** of the whole draft after the next large change, by a model
      that did not write it.

## The four questions for AI-written formal proofs

From the Xena blog, 12 November 2026; the answers are in Section 9.

- [x] **The statement matches the paper.** The Lean excerpts in the draft are copied from the
      files. Re-check the excerpts against the commit named in Section 9 before submitting.
- [x] **It compiles** from scratch, on this PC and on GitHub's clean machine (workflow "Check
      the proofs").
- [x] **It proves the theorem as stated:** `Audit.lean` holds `example : Statement := theorem`
      for every final statement, checked by every build.
- [x] **Lean's own `lake comparator`** on the same question, with the statements (in `Goals/`
      and `Curved/Goal.lean`) as the challenge: `comparator/Challenge.lean` (the sixteen
      headline statements, each with a hole for its proof) and `comparator.json`.
      `lake comparator --paranoid`, inside Lake's sandbox on Linux (the setting below), accepted
      all sixteen against `Audit`: same statements, only the three standard axioms, all six
      checkers. A question changed by hand was rejected. Section 9, item 3.
- [x] **A kernel re-check outside the build:** `leanchecker` over all 200 modules at tag
      `paper-1-numbers`: 199 passed; the checker itself crashed twice on
      `GravityInLean.OneMass`, whose declarations then passed the six checkers below.
- [x] **Independent checkers:** `lake check --from-export --paranoid` (Lean's kernel,
      `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`) on an export of
      the sixteen headline theorems and one of `GravityInLean.OneMass`: all six accept both,
      with only the three standard axioms.
- [x] **The same inside Lake's sandbox, on Linux,** over the whole project: `lake check
      --paranoid` without `--inadvisably-no-sandbox`, in a Linux container on this PC
      (`scripts/sandbox-check/`; Docker ran it with `--security-opt seccomp=unconfined` so that
      the sandbox could start, and nothing else was loosened). On the export of everything in
      scope (464,847 declarations, mathlib and Lean's own library included) five checkers
      accept; `nanoda` crashed with a stack overflow. `nanoda` accepts the project's own 2,605
      declarations with everything they depend on, also inside the sandbox. Section 9, item 4.
- [x] **`lake comparator` for all fixed statements, in public CI** (outside review 1, finding
      F9). The question is written from `Audit.lean` by `scripts/comparator/make_challenge.py`
      (57 statements: the paper's 54 and three proved since); the workflow "Compare statements"
      runs `lake comparator --paranoid` on GitHub's Linux machine and fails when the question is
      out of date. First run accepted, 12.5 minutes. `connectionUnique` cannot be asked: the
      statement files import its proof. Section 9, item 3.
- [ ] **`nanoda` on the whole export.** Tell nanoda's authors about the stack overflow (it
      needs only the public repository and `scripts/sandbox-check/run.sh` to repeat), and run it
      again with a version that gets through.
- [ ] **Axioms printout** for the main theorems in the paper's appendix or repository
      (`#print axioms`). The audit already checks this for every declaration; a printed list for
      the named theorems is still to be added.

## The definitions

- [x] Reviewed against the textbooks by three AI reviewers (`REVIEW.md`). Its to-do list is
      done: the connection exists, one mass per connected region, the 25 tests, the comments.
- [x] 25 failure tests proved.
- [ ] **The textbook's symmetry gives ours.** The textbooks assume an isometric action of SO(3)
      with two-dimensional spacelike orbits; the statements assume three Killing fields
      (`IsRoundOn`). Either prove in Lean that such an action gives `IsRoundOn`, or keep calling
      the result a variant, as Sections 3 and 8 now do. This is the question a referee will ask.
- [ ] **A person who works in gravity reads** `Curved/Basic.lean`, `Curved/Goal.lean`,
      `Goals/ExactlyWhen.lean`, `Goals/EveryPoint.lean` and `Goals/Global.lean`. Welcome, not
      strictly required; say in the paper which it was. The outside review of 24 November
      (`review/paper-outside-review-1.md`, F5 and F9) ranks this first among the gaps in the
      trust story and calls it a blocker for a mathematics venue.

## The method

- [x] **What the workers could see and reach**, and **what was changed after each run and by
      whom**: written in Section 7.
- [ ] **A comparison point** for the method paper: the same job (for example run 2 or run 4)
      run by one agent instead of ten, or without the route in the brief. Without one, Section 7
      reports measurements, not a comparison.
- [ ] For later runs: cut the container off from everything but the model, or check every
      run's record for use of the network, not only run 5's.

## The author

- [x] **The author has read the whole paper** (24 November 2026). Section 10 says plainly that
      the author is not a specialist and has not checked the mathematics, so the sentences in
      [plain-summary.md](plain-summary.md) are not yet defended by a human. A reading by a
      human expert (Sections 6 and 8) is what would close that.
- [x] **Section 10 has the author's part**: what the author chose, decided and read, and that
      the author did not check the mathematics. Taken from the author's own words and put into
      formal wording on 24 November 2026. For a venue that wants human-written text, the author
      rewrites it.
- [x] Author names are on the paper: Mario Andreschak, Claude Fable 5.2 and Claude Opus 5.5
      (24 November 2026). Affiliation and contact are added at submission and are not kept in
      this repository.
- [ ] **AI systems as authors.** arXiv, Springer Nature and the Annals of Formalized Mathematics
      do not accept an AI system as an author (read 24 November 2026); the reason they give is
      that an author must be able to take responsibility for the paper. Before submitting, move
      Claude Fable 5.2 and Claude Opus 5.5 from the author line to Section 10 or the
      acknowledgements, unless the chosen venue's rules, read on the day, say otherwise.
- [ ] **Responsibility for the content.** Venues expect the human author to answer for the whole
      paper, and arXiv was reported in 2026 to ban authors for a year over unverified AI
      content (read its moderation page on the day). Section 10 says honestly that the author
      has not checked the mathematics. Before submitting anywhere, either have a human expert
      read the paper, or confirm that the venue accepts a paper whose human author relies on
      the machine checks.

## The venue

Rules read at the source on 24 November 2026:

- **Annals of Formalized Mathematics**
  ([instructions](https://afm.episciences.org/page/instructions-for-authors),
  [aims and scope](https://afm.episciences.org/page/aims-and-scope)): "Only human-authored
  manuscripts are accepted"; every paper discloses AI use for "the manuscript, the code, or
  both". AI-written proofs are allowed when disclosed, but the text must be written by a person,
  and this draft was written by AI. So for this journal the author writes the paper himself and
  uses the draft as notes. It also wants "mathematical novelty or new insight":
  "formalizations of known results, without this insight, are not in scope".
- **CADE-31** (Springer LNCS; abstracts 15 February 2027, papers 22 February 2027): Springer
  allows AI help when it is documented. The draft can be the base; confirm the wording for the
  year.

- [ ] Choose the venue with those two rules in view.
- [ ] Consider posting to arXiv first (cs.LO, cross-listed to gr-qc).
- [ ] Convert the draft to the venue's format and length. The Lean excerpts and the table of
      runs are the parts to keep if space is short.

## The content

- [x] The global theorem (issue 39, second step) is in the paper: proved and merged (PR #55);
      Sections 1, 4, 5, 7 and 8 describe it.
- [x] Freeze a commit and tag it: tag `paper-1-numbers` on commit `3b816ea` (PR #55). Section 9
      and the numbers in the abstract and Section 7 are taken from it (theorems counted as
      lines that start a theorem or lemma: about 1,550; 2,605 declarations audited; about 39,400
      lines of Lean in `GravityInLean/`).
- [ ] Have someone who did not write the draft read it for sentences that claim more than the
      measurements show.
