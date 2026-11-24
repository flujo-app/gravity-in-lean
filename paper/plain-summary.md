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
   and empty.
5. **No hidden assumption in "empty".** The tool that measures curvature (the connection)
   is proved to exist and to be the only one.
6. **The definitions can fail.** For each notion there is a checked example where it does not
   hold. A definition that can never fail says nothing.
7. **How it was made.** Teams of ten AI workers wrote most of the proofs, in six runs of 11
   to 29 minutes. The groundwork in coordinates, the definitions and the statements were written
   by single AI chats. The statements were fixed before each run in a file the workers could not change.
   Afterwards everything was rebuilt from nothing and audited.

## What the paper does not claim

- **No new physics.** The theorem is a hundred years old.
- **Not "the first".** It says "to our knowledge", and names what others did first: another
  project checked the theorem four days earlier, starting from fixed labels; another proved
  that the connection exists; a proof on paper without coordinates dates from 1997.
- **Not that the definitions are right beyond doubt.** A proof checker checks the proof, not
  whether the statement says what we mean. AI reviewers compared the definitions with the
  textbooks and found none wrong. No person who works in gravity has read them yet.
- **Nothing about the whole space-time at once** (unless the global theorem is finished before
  submission).
- **Not the most general case.** No electric charge, no cosmological constant, and the
  space-time is assumed perfectly smooth.

## Sentences you must be ready to defend

1. "Every final theorem has exactly the statement that was fixed before it was proved." *Why it
   holds:* each build checks this (`Audit.lean`), and the public build on GitHub shows it.
2. "The proofs rest on nothing but Lean's three standard assumptions." *Why:* the same audit,
   for all 2,004 declarations.
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
7. "I did not write the proofs." The paper says so in its section on the use of AI. What you
   did do (chose the goal, set the rules, read and stand behind the claims) is for you to
   write there in your own words.

## Read first

1. Section 8 of the draft, "What is and is not established". It is the honest core.
2. Section 10, "Use of AI". It has a gap that only you can fill.
3. The abstract, last. If you can defend every sentence of it after the first two, it is yours.
