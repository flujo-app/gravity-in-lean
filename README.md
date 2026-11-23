# Gravity in Lean

**Einstein's gravity, checked by machine, one small piece at a time.**

A proof checker called [Lean](https://lean-lang.org) reads every step of every proof in this
folder and refuses anything that does not follow. Mathematicians use the same tool for their
largest proofs. So the results below are not "the numbers agree" or "we think so". They are proved.

[What is proved](#what-is-proved-today) ·
[What is taken on trust](#what-is-still-taken-on-trust) ·
[Check it yourself](#check-it-yourself) ·
[What exists elsewhere](SURVEY.md) ·
[Where this could go](PLAN.md)

## Why this exists

The formulas come from the interactive page
[Slow Clocks, Bent Light](https://claude.ai/artifact/2wKidE7zA8Z1FXimbFPkjL), where you fly around
a heavy mass and watch clocks slow down and light bend. That page was tested with numbers. This
project asks the stricter question: can a machine confirm the formulas exactly? And how far up
could that go, perhaps as far as two masses circling each other?

The short answer: one mass, yes, and that part is now done. Two masses: an exact formula almost
certainly does not exist, so that is not the goal. The honest steps in between are in
[PLAN.md](PLAN.md).

```mermaid
flowchart LR
  T["Three pieces<br/>and a probe<br/>(done)"] --> R1["1 · One mass,<br/>from the definitions<br/>(done)"]
  R1 --> R2["2 · It is the only one<br/>(Birkhoff)"]
  R2 --> R3["3 · Weak gravity<br/>gives Newton"]
  R3 --> R4["4a · Two masses,<br/>approximately"]
  R4 -.-> R5["4b · Derive that from<br/>Einstein's equations"]
  R5 -.-> X["Exact formula for two masses:<br/>does not exist"]
```

Solid arrows are steps worth taking. Dotted arrows are not for now.

## The pages

The interactive pages this project grew out of are kept in [pages/](pages/): eight pages, each of
which opens in a browser by itself, and one picture. Start with *Slow Clocks, Bent Light*.

## What is proved today

| Piece | In plain words | File and main result |
|---|---|---|
| **A** | Two ways of writing how slowly a clock runs near a mass give exactly the same number: the page's `(1 - s)/(1 + s)` and the textbook's `√(1 - 2M/r)`. | [ClockRate.lean](GravityInLean/ClockRate.lean), `clockRateMap_eq_clockRateTextbook` |
| **B** | Schwarzschild's solution of 1916 makes all three curvature formulas for empty space vanish, everywhere outside the rim of the black hole. | [OneMass.lean](GravityInLean/OneMass.lean), `schwarzschild_isEmptySpace` |
| **C** | A clock on a round orbit runs at `√(1 - 3M/r)` of a far clock, and goes round at the rate Kepler found. Such orbits exist at every distance outside `r = 3M`. | [RoundOrbit.lean](GravityInLean/RoundOrbit.lean), `roundOrbit_clockRate`, `roundOrbit_kepler`, `roundOrbit_exists` |
| **The budget** | Speed through time, squared, plus speed through space, squared, always adds up to the same total. Light spends all of it on space. | [RoundOrbit.lean](GravityInLean/RoundOrbit.lean), `budget`, `budget_light` |
| **Step 1, curvature** | Take the general definition of curvature and apply it to a round, unchanging space-time. All sixteen parts come out: three of them are the formulas of Piece B, one is a multiple of the third, twelve are zero. So Schwarzschild's space-time is empty in the full sense of Einstein's equation. | [RoundSpacetime.lean](GravityInLean/RoundSpacetime.lean), `round_ricciFlat_iff`, `schwarzschild_ricciFlat` |
| **Step 1, orbit** | Take the general equation of free fall and apply it to a round orbit. Three of its four equations hold by themselves, the fourth is exactly a starting fact of Piece C. So the orbit's clock rate now follows from free fall itself. | [FreeFall.lean](GravityInLean/FreeFall.lean), `roundOrbit_isFreeFall_iff`, `roundOrbit_clockRate_of_freeFall` |
| **Probe** | The curvature of a sphere, computed from the same general definitions, comes out equal to the sphere's own length measure, as the textbooks say. | [Probe/Sphere.lean](GravityInLean/Probe/Sphere.lean), `ricci_sphere` |

In numbers: 79 theorems in about 1,300 lines.

## What is still taken on trust

Before step 1 this list said: the three curvature formulas of Piece B, and the two starting facts
of Piece C. Both are now proved. What is left:

1. **The definitions themselves.** Curvature and free fall are written down here as the classic
   textbook formulas in coordinates ([Curvature.lean](GravityInLean/Curvature.lean)). They are not
   yet tied to the abstract geometry of Lean's standard library, because that library has no
   curvature yet.
2. **The starting shape.** That a round, unchanging space-time can be described by just a clock
   function and a ruler function. Showing that is part of step 2.
3. **The blind spots of the coordinates.** The two poles, the centre, and everything at or inside
   the rim of the black hole are left out of every statement. Textbooks that use these coordinates
   leave them out too.
4. **Meaning.** Lean checks that a proof proves its statement. It cannot check that the statement
   says what we mean. That is why the statements are short and each has a plain-language comment:
   they are meant to be read.

## Check it yourself

On this PC Lean is already installed. It is not on the search path, so add it first:

```powershell
$env:PATH = "$HOME\.elan\bin;$env:PATH"
```

Then, in this folder:

```powershell
lake build
```

You should see `Build completed successfully` and six lines that end in
`none rests on more than [propext, Classical.choice, Quot.sound]`. A full rebuild takes about a
minute.

On another computer: install Lean from [lean-lang.org/install](https://lean-lang.org/install/),
then run `lake exe cache get` in this folder before `lake build`. That downloads the standard
library ready-built (the folder ends up at about 3.4 GB). Never let it build the standard library
from source; that takes hours.

This PC is shared and often short of memory, so please run one build at a time.

## The judge

Lean accepts a proof with a hole in it and only warns. It also lets anyone add a new assumption
and then "prove" anything from it. So "it builds" is not enough.

[Audit.lean](Audit.lean) closes both doors, and it is part of `lake build`. It asks Lean what each
of the 189 declarations in the project rests on (every definition and theorem, plus the helper
pieces Lean generates for them), and fails the build unless the answer is: nothing but Lean's own
three standard assumptions, the same three that almost all of the standard library uses.

It was tested. A deliberately planted hole made the build fail, and the error named both the
theorem with the hole and a second theorem that merely used it.

So a green build means three things at once: proved, no holes, no extra assumptions.

## Good to know

- **Units.** The speed of light and Newton's constant are both 1. A mass `M` is then a length:
  for the Sun, about 1.5 km.
- **Coordinates.** A point of space-time is four numbers: far time, distance, angle from the pole,
  angle around the axis.
- **Versions are pinned:** Lean 4.36.0 and its standard library mathlib v4.36.0. Updating either
  is a deliberate step, not something that happens by itself.
- **GitHub repeats the check** on a clean machine after every push
  ([check.yml](.github/workflows/check.yml)).
- **Licence:** Apache 2.0, the same as the standard library.

## Where things are

```
GravityInLean/ClockRate.lean        Piece A
GravityInLean/OneMass.lean          Piece B
GravityInLean/RoundOrbit.lean       Piece C and the budget
GravityInLean/Curvature.lean        the general definitions: connection, curvature, free fall
GravityInLean/RoundSpacetime.lean   step 1: the curvature of the round space-time
GravityInLean/FreeFall.lean         step 1: the round orbit as free fall
GravityInLean/Probe/Sphere.lean     the probe
pages/                              the interactive pages

SURVEY.md                           what already exists elsewhere
PLAN.md                             where this could go, and what it would cost
```

## Learn more

- [SURVEY.md](SURVEY.md): what Lean's standard library has and lacks, who else has tried, and
  where physics itself stops. Every statement is marked measured, worked out, open or not verified.
- [PLAN.md](PLAN.md): the steps from here, the effort for each, where a swarm of workers helps, and
  a plain recommendation.
