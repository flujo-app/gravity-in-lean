# The paper in plain words

One page for the author. What the paper claims, what it does not, and the sentences you must be
ready to defend. The draft itself is [paper.md](paper.md).

## What it is about

**Birkhoff's theorem.** If space around a mass is empty and looks the same from every side,
then space-time there has exactly one possible shape: Schwarzschild's. It does not matter
whether the mass pulsates or collapses, as long as it stays round. This has been known on paper
since 1921.

**What we did.** We had a computer check a proof of it, line by line, in the proof checker
Lean. A proof checker accepts no gaps and no "it is clear that".

## What the paper claims

1. **The theorem is checked without coordinates at the start.** Textbooks begin by choosing
   labels for time, distance and two angles that fit the roundness. That such labels exist is
   itself a piece of mathematics, usually skipped. Here the proof starts from a bare curved
   space and builds the labels.
2. **It holds at every point, also on the rim of a black hole.** The usual labels break down on
   the rim. We use Kruskal's labels, which do not.
3. **One mass.** A space-time in one piece gets one mass, not a different one at each point.
4. **Both directions.** Round and empty means Schwarzschild's, and Schwarzschild's means round
   and empty: as one "exactly when" at points off the rim, and for a region with no holes a
   loop could wind round (for mass zero the map must miss the centre). The every-point theorem
   of item 2 has no such reverse direction of its own.
5. **No hidden assumption in "empty".** The tool that measures curvature (the connection)
   is proved to exist and to be the only one, for space-times; the standard library already
   had this for ordinary (Riemannian) spaces.
6. **The whole space-time.** On a region with no holes a loop could wind round, the pieces fit
   together into one map into Kruskal's black hole (or flat space-time, or negative-mass
   Schwarzschild), unique up to a symmetry. The map keeps all lengths but need not cover the
   model or be one-to-one. A full list of all possible shapes is not claimed. Experts may see this
   step as a known argument applied to the every-point theorem; the paper says so.
7. **The definitions can fail.** For almost every notion there is a checked example where it
   does not hold (13 of the 25 tests); the connection is pinned down instead by the proof that
   there is only one. A definition that can never fail says nothing.
8. **How it was made.** Teams of ten AI workers wrote most of the proofs, in seven runs of 11
   to 46 minutes. The groundwork in coordinates, the definitions and the statements were written
   by single AI chats. The statements were fixed before each run, in files the workers were
   told not to change; afterwards a check of what they had changed showed they had not, and
   everything was rebuilt from nothing and audited.

## What the paper does not claim

- **No new physics.** The theorem is a hundred years old.
- **Not "the first".** It says "to our knowledge", and names what others did first: another
  project checked the theorem four days earlier, starting from fixed labels; another proved
  that the connection exists; a proof on paper without coordinates dates from 1997.
- **Not that the definitions are right beyond doubt.** A proof checker checks the proof, not
  whether the statement says what we mean. AI reviewers compared the first definitions with the
  textbooks and found none wrong; the later ones were read by one AI reader each. No person who
  works in gravity has read them yet.
- **Not a full list of every possible shape.** The whole-space-time theorem maps every space-time
  without loop-holes into a model; which folded or extended versions occur is not claimed. A
  narrower list, under a condition on paths of free fall, is written down in Lean but not
  proved.
- **Not the most general case.** No electric charge, no cosmological constant, and the
  space-time is assumed perfectly smooth.

## Sentences you must be ready to defend

1. "Every final theorem has exactly the statement that was fixed before it was proved." *Why it
   holds:* each build checks that every final theorem has exactly the statement in its
   statement file (`Audit.lean`), and the public build on GitHub shows it. *And:* Lean's own
   comparison tool (`lake comparator`) confirms this from outside the build, for every fixed
   statement that has been proved, on GitHub's machines, where anyone can read the log. That
   the statement files are the ones fixed before the runs is shown by the git history, not by
   either tool. *Weak point:* the workers were told not to change those files; nothing stopped
   them, but the check afterwards found no change.
2. "The proofs rest on nothing but Lean's three standard assumptions." *Why:* the same audit,
   for all 2,605 declarations. *And:* six separate checking programs that ship with Lean
   accept the main theorems, also inside Lake's protective sandbox on Linux (Section 9).
   Over the whole project, five of the six accept everything; the sixth (`nanoda`) crashed
   partway through, on a fixed limit of its own, and accepts everything the project uses
   when given only that. *Weak point:* the Linux machine was a container on the same PC, with one
   of Docker's safety filters switched off so that the sandbox could start.
3. "To our knowledge no earlier machine-checked Birkhoff theorem starts without coordinates or
   covers the rim." *Why:* searches on the dates given in `SURVEY.md`. *Weak point:* this field
   moves by the day. Search again on the day of submission.
4. "For the place where the two rims cross we found no complete written proof." *Why:*
   `review/global-birkhoff.md` lists what was read. *Weak point:* "not found" is not "does not
   exist". Never say "new".
5. "The connection proof was made without looking at the other project's proof." *Why:* the
   run's record shows no access to the network. *The full story:* an earlier attempt did look;
   it was thrown away unmerged.
6. "The cost figures are upper bounds." *Why:* other work used the same allowance at the same
   time.
7. "I did not write the proofs." The paper says so in its section on the use of AI, together
   with what you did do (chose the goal, set the rules, read the paper) and that you did not
   check the mathematics yourself. It also says that you read the version of 24 November,
   before the two AI reviews of the text: read the current one before it goes anywhere.
8. "The global theorem was not found written down." *Why:* the research notes. *Weak point:*
   an expert will say it follows from the every-point theorem by a known argument (the
   extension theorem for maps that keep lengths). The paper says so itself; agree, and point
   out that here nothing had to be assumed analytic.

## Read first

1. Section 8 of the draft, "What is and is not established". It is the honest core.
2. Section 10, "Use of AI". Your part is filled in from your own words; change anything that
   is not how you would put it.
3. The abstract, last. If you can defend every sentence of it after the first two, it is yours.
