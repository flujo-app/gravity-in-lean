# Before submitting

What is still needed before [paper.md](paper.md) goes anywhere. Taken from issue 34. Tick a box
only when the thing is done and written down where others can see it.

## The claim

- [ ] **Search again on the day of submission** for machine-checked Birkhoff theorems, in Lean,
      Isabelle, Coq/Rocq, HOL, Mizar, on GitHub and arXiv. Record the date and what was found in
      `SURVEY.md`. If anything turns up, change Sections 1 and 2 before submitting.
- [ ] **Ask in the Lean community chat** whether anyone knows earlier work (issue 2).
- [ ] **Compare the statement word for word** with ProjectAinos's `birkhoff` and grlab's
      `Birkhoff.lean`, and say in Section 2 exactly how they differ.
- [ ] **Verify every reference** against the source: authors, title, year, volume, pages. The
      draft marks the list as unverified. Do not describe Schmidt's method beyond "avoids
      introducing coordinates".
- [ ] Keep every priority claim as "to our knowledge" or "not found written down". No "first",
      no "new".

## The four checks for AI-written formal proofs

- [x] **The statement matches the paper.** `Audit.lean` holds `example : Statement := theorem`
      for every statement quoted; the Lean excerpts in the draft are copied from the files.
      Re-check the excerpts against the commit named in Section 9 before submitting.
- [x] **It builds** from scratch, on this PC and on GitHub's clean machine (workflow "Check the
      proofs").
- [ ] **An external re-check of the compiled proofs** with a kernel re-checker such as
      `lean4checker`. Not done. Needs a build slot; report the result in Section 9.
- [ ] **An independent checker** (a second implementation of Lean's kernel). Not done.
- [ ] **Axioms printout** for the main theorems in the paper's appendix or repository
      (`#print axioms`). The audit already checks this for every declaration; a printed list for
      the named theorems is still to be added.

## The definitions

- [x] Reviewed against the textbooks by three AI reviewers (`REVIEW.md`).
- [x] 25 failure tests proved.
- [ ] **A person who works in gravity reads** `Curved/Basic.lean`, `Curved/Goal.lean` and
      `Goals/EveryPoint.lean`. Welcome, not strictly required; say in the paper which it was.

## The author

- [ ] **The author reads the whole paper** and can defend each sentence listed in
      [plain-summary.md](plain-summary.md).
- [ ] **The author writes his part of Section 10** in his own words: what he chose, decided,
      read and checked.
- [ ] Author name, affiliation and contact are filled in by the author at submission. They are
      not in this repository.

## The venue

- [ ] **Read the venue's exact rules on AI-written text and proofs** before choosing it.
      CADE-31 (Springer LNCS; abstracts 15 February 2027, papers 22 February 2027): Springer
      allows AI help when it is documented; confirm the wording for the year. The Annals of
      Formalized Mathematics says "only human-authored manuscripts": do not submit there until
      someone has read that rule in full and it fits.
- [ ] Consider posting to arXiv first (cs.LO, cross-listed to gr-qc).
- [ ] Convert the draft to the venue's format and length. The Lean excerpts and the table of
      runs are the parts to keep if space is short.

## The content

- [ ] Decide whether the global theorem (issue 39, second step) is in the paper. If it is
      proved in time, it becomes a section; if not, it stays as future work in Section 8.
- [ ] Freeze a commit and tag it; use that commit in Section 9 and re-take every number from
      it (theorems, declarations, lines).
- [ ] Have someone who did not write the draft read it for sentences that claim more than the
      measurements show.
