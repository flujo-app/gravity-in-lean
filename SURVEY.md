# What already exists

Survey of 22 November 2026. The question behind it: if we want Einstein's gravity checked by
machine, what is already there, and where does the unknown begin?

Every statement carries one of four marks.

| Mark | Meaning |
|---|---|
| **Measured** | We ran it or counted it ourselves on this PC today. For physics: it is seen in experiments. |
| **Worked out** | Proved or derived on paper, and accepted in the field. |
| **Open** | Nobody has it. |
| **Not verified** | Its authors say so. We only read a title, summary or abstract, and where noted nobody independent has confirmed it yet. |

## The short version

1. **Measured.** Lean's standard library (called mathlib) has all the calculus we need. Since 2025
   it also knows what a "connection" on a curved space is. It has **no curvature at all**, and
   nothing for space-time.
2. **Measured.** The community physics library (physlib) has Einstein's special relativity, the
   one without gravity. For gravity it has a single experimental file, and that file says itself
   that the field equations are not checked there.
3. **Not verified.** We found no machine-checked proof, in any proof checker, that Schwarzschild's
   solution solves Einstein's equations, and none of Birkhoff's theorem. A search can miss things,
   so this is "we did not find one", not "there is none".
4. **Not verified.** Very large geometry proofs in Lean are now real: 2026 papers report Lean
   versions of Hamilton's and Perelman's work, with a curvature library of their own. That library
   is for ordinary curved spaces, not for space-time, and it is not part of mathlib.
5. **Open.** Two masses orbiting each other: no exact formula is known and none is expected.
   **Measured:** computer simulations have handled it since 2005, and their waves match what the
   detectors record.

## 1. The tool and its standard library

Checked on this PC, in the exact versions this project is pinned to: Lean 4.36.0 and mathlib
v4.36.0 (8,712 files). "Files that mention X" was counted with a plain text search.

| Topic | What is there | Mark |
|---|---|---|
| Calculus: slopes, products, chains, square roots | Complete for our needs. All our proofs use it. | Measured |
| Curved spaces and lengths on them | Present: `Mathlib/Geometry/Manifold/Riemannian/` | Measured |
| The connection that belongs to a length measure (Levi-Civita) | Present since 2025: one 414-line file by Massot, Rothgang and Macbeth. It proves that it exists and is unique. Its own notes say smoothness is left for later. | Measured |
| Curvature | **Missing.** Files that mention "Christoffel": 0. "Ricci": 0. "curvature tensor", "Riemann curvature", "sectional curvature": 0. | Measured |
| Space-time, where time counts with the opposite sign to space | **Missing.** "Lorentz": 0. "pseudo-Riemannian": 0. ("Minkowski" appears in 14 files, but the ones we opened are about his work on convex shapes, not about space-time.) | Measured |
| Paths of free fall (geodesics) as an equation of motion | **Missing.** The word appears in 5 files, in other senses (graphs, groups, a curved plane). | Measured |
| Einstein's equations | **Missing.** "Einstein" appears once, in a reference to the Einstein-Podolsky-Rosen paper. | Measured |
| Tools for wave-like equations (Sobolev spaces) | A beginning: 3 files. | Measured |

What this means: the calculus is ready, the geometry stops one step before curvature, and the
physics is not there. Anything about gravity has to bring its own definitions for now.

## 2. Physics in Lean

| Project | What it has | Mark |
|---|---|---|
| [physlib](https://github.com/leanprover-community/physlib), the community physics library (869 stars, Apache 2.0, last change today) | Its relativity folder holds the Lorentz group, Minkowski's matrix, the Poincaré group, special relativity and tensors. That is the no-gravity side. | Measured (read from GitHub today) |
| physlib, experimental part: `PhyslibAlpha/Relativity/General/Schwarzschild/IncompressibleSphere.lean` | The inside of a star of even density: 42 theorems, no holes. The file says the field equations are not verified there. Same kind of gap as ours. | Measured (file read earlier today) |
| [Logos Library](https://reservoir.lean-lang.org/@adambornemann-glitch/logos_library) | Says it covers Minkowski space-time and spinning black holes. Reports 4,034 checked proofs, but also 114 added assumptions and 7 holes. | Not verified |
| [OmegaTheory V2](https://ramzesx.github.io/Omega-Theory-Discrete-Spacetime/lean/) | One author's own theory, with a list of gravity cases. Status is self-reported. | Not verified |
| [LeviPy](https://pypi.org/project/levipy/) ([code](https://github.com/mirajcs/levipy)) | A Python tool that computes connections and curvature and then writes the matching Lean statements for someone to prove. It calls itself a list of proof duties, not a prover. No stars, last change May 2026. | Not verified |
| ["Formalising Linear Elliptic PDE Theory in Lean 4"](https://arxiv.org/abs/2609.32561) | A 2026 paper on tools for one family of equations. Relevant to the far rungs of the plan. Title only. | Not verified |

## 3. Big geometry proofs in Lean (2026)

| Work | Claim | Mark |
|---|---|---|
| [A Lean Formalization of Hamilton's Three-Manifold Theorem](https://arxiv.org/abs/2608.21502) (Chow, Liao, Qin) | Machine-checked. | Not verified |
| [A Lean Formalization of the Hamilton-Perelman Proof of the Three-Dimensional Poincaré Conjecture](https://arxiv.org/abs/2609.33842) (Qin, Liao, Khaitan, Chow) | Machine-checked, with a geometry library of its own. | Not verified |
| [A Lean Formalization of the Hamilton-Perelman Proof of Thurston's Geometrization Conjecture](https://arxiv.org/abs/2610.13897) | Title only. | Not verified |
| [An AI-Assisted Formalization of the Poincaré Conjecture](https://arxiv.org/abs/2610.08329) | Title only. | Not verified |

Two cautions that came with these. A public
[tracker](https://kingy.ai/mathematics-science-breakthrough-tracker/records/math-poincare-lean-formalization-2026/)
points out that a proof which builds does not show that every definition means what it should, and
that independent review was still pending. And the figure of "4.7 million lines" comes from a news
site we could not confirm against the papers.

Why it matters here: it shows the scale is possible, and that curvature has been built in Lean
outside the standard library. But it is for ordinary curved spaces, where all lengths are
positive. Space-time needs the version where time counts with the opposite sign. We did not
download or build any of it.

## 4. Other proof checkers

| What | Status | Mark |
|---|---|---|
| Special relativity in Isabelle: ["Using Isabelle to verify special relativity"](https://arxiv.org/abs/1211.6468) (Stannett and Németi) | Exists. | Not verified |
| Gravity (general relativity) in Isabelle, Coq or HOL | We found nothing. | Not verified |

## 5. The research frontier

**One mass**

| Statement | Mark |
|---|---|
| Schwarzschild's solution of 1916 describes space and time around one round mass that does not spin. | Worked out |
| Its predictions hold: clocks lower down run slower, light bends, Mercury's orbit turns, black holes cast a shadow. | Measured (by experiments, not by us) |
| Birkhoff's theorem of 1923: for a round, empty surrounding it is the *only* solution. | Worked out |
| Either of the two, checked by machine from the definitions. | Not found (see the short version, point 3). Both are now done in this repository, in coordinates (steps 1 and 2, 23 November 2026). Birkhoff's theorem is proved there from "looks the same from every side", for any coordinates in which turning space moves only the two angles. The coordinate formulas for curvature, free fall and symmetry are also proved there to give the same answer in any coordinates. Whether that had been checked by machine elsewhere before: not verified. |

**Two masses**

| Statement | Mark |
|---|---|
| An exact formula for two masses orbiting each other. None is known. Nobody expects one, because the pair loses energy as waves and spirals together. Strictly, nobody has proved that none can exist. | Open |
| Solving the equations step by step on a computer. Works since 2005 (Pretorius, then two more groups within a year). | Worked out |
| The computed waves match what the detectors have recorded since 2015. | Measured (by experiments, not by us) |
| Approximating in steps from Newton upwards. The first step is the Einstein-Infeld-Hoffmann equations of 1938. | Worked out |
| The fourth step, agreed between several groups working by different methods. | Worked out |
| Pieces of the fifth step, 2026: [black-hole scattering at fifth order](https://arxiv.org/abs/2601.16256) (Driesse, Jakobsen, Mogull, Nega, Plefka, Sauer, Usovitsch), [a second approach](https://arxiv.org/abs/2512.23654), and [a fifth-step result still to be reconciled with them](https://arxiv.org/abs/2604.09545). | Not verified |

**Theorems about what stays stable**

| Statement | Mark |
|---|---|
| Empty flat space is stable: small ripples die away (Christodoulou and Klainerman, 1993). | Worked out |
| Slowly spinning black holes are stable (Klainerman and Szeftel, with Giorgi and Shen; [introduction](https://arxiv.org/abs/2210.14400)). A very long proof, still being absorbed by the field. | Worked out |
| The simplified, "linear" version for any spin below the limit: [paper](https://arxiv.org/abs/2506.21183). Title only. | Not verified |
| The full version for any spin below the limit, claimed in 2026: [Hintz](https://arxiv.org/abs/2606.28253) and [a second paper](https://arxiv.org/abs/2609.40068). We found no independent confirmation. | Not verified |
| A theorem that follows two black holes all the way through their merger. | Open |

## 6. What this means for this project

- The standard library stops just short of curvature, and has nothing for space-time. So the
  very first step, "Schwarzschild's solution solves Einstein's equations, from the definitions",
  seems not to have been done by machine. It is small, and the probe in this repository shows the
  method works. (Update, 23 November 2026: that step is now done in this repository, in
  coordinates. Whether it was done elsewhere before is still not verified.)
- The far end, two masses, is not a gap in machine-checking. It is a gap in mathematics itself.
  No proof checker can check a formula that does not exist.
- Everything marked "Not verified" above should be read before anyone builds on it. In
  particular, before claiming a "first", someone should ask in the Lean community chat whether
  the one-mass proof already exists somewhere we did not look.

## How the counts were made

- mathlib: text search over the 8,712 `.lean` files of the pinned version (`v4.36.0`), counting
  files that contain each word.
- physlib and LeviPy: GitHub's own figures, read on 22 November 2026.
- Papers: web searches on 22 November 2026. Unless a row says otherwise, only the title and a
  search summary were read, not the paper.
