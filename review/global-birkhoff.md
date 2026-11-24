# Global Birkhoff theorem: what is known, what is open

Research notes, 23 November 2026. Written for the Lean 4 project that has machine-checked the
local, coordinate-free Birkhoff theorem at points where the gradient of the area radius r is not null.

Tags used for every fact:

- **[READ]**: I read the passage in the source itself (PDF text).
- **[SUMMARY]**: I saw only an abstract, a database summary or a search-engine summary.
- **[JUDGEMENT]**: my own reasoning. It is not taken from a source.

---

## 0. Short answer in plain words

1. **Horizons included (local).** People have long believed, and Hawking–Ellis state, that every
   spherically symmetric vacuum spacetime looks like a piece of the Kruskal spacetime around
   every point, horizons included. But no source I found writes out a full proof for the
   **bifurcation sphere**, the sphere where the two horizons cross and the gradient of r is zero.
   - Hawking–Ellis only sketch the horizon step ("join them together ... as in §5.5").
   - Chruściel's lecture notes state the theorem only near points where the extra Killing field
     is **not null**, so the horizons are left out.
   - An and Wong (2018) give an explicit Eddington–Finkelstein form at every point where dr ≠ 0,
     which covers the ordinary horizon points. They give no explicit local form at the points
     where dr = 0.
   - Schleich and Witt (2010) claim that their charts cross the horizons, but their proof has a
     gap exactly at the bifurcation sphere [JUDGEMENT].
2. **Global classification.** There is **no complete global classification** in the literature.
   - The positive results known are uniqueness theorems under strong extra conditions. The main
     one: Kruskal is the only simply connected, analytic extension of the Schwarzschild exterior
     in which every incomplete geodesic runs into blowing-up curvature.
   - There is also a list of examples that break naive uniqueness: the RP³ geon, the other Z₂
     quotients, universal covers of Kruskal with a sphere removed, the S¹×S² "Schwarzschild
     cosmologies", and the data of Schleich and Witt.
   - Chruściel writes that classifying all maximal analytic extensions in this way "remains to be
     seen". Szenthe (2004) writes that a general global theory of spherically symmetric
     spacetimes "is lacking".
3. **What can realistically be proved.**
   - A "developing map" version of the global theorem looks true and was not found written down as an explicit
     statement: the universal cover of any connected spherically symmetric vacuum spacetime maps
     into Kruskal (or Minkowski, or negative-mass Schwarzschild) by a map that preserves the metric.
   - Adding one completeness condition gives a finite list: Kruskal and its four Z₂ quotients.
   - Both follow from known tools once the local theorem holds at **every** point, the
     bifurcation sphere included [JUDGEMENT].

---

## 1. Q1: Is "locally isometric to Kruskal at every point" proved, and where?

### 1.1 Hawking & Ellis (1973), Appendix B, pp. 369–372 [READ]

- **Definition.** Spacetime is spherically symmetric if it "admits the group SO(3) as a group of
  isometries, with the group orbits spacelike two-surfaces". This is a global group action, but
  the theorem is applied "in an open set". The orbits are said to be surfaces of constant
  positive curvature, so RP² orbits are not excluded explicitly.
- **Method.**
  - Uses B. Schmidt (1967) to get orthogonal 2-surfaces and the warped form
    `dτ²(t,r) + Y²(t,r) dΩ²`.
  - Then picks orthogonal coordinates, following Bergmann–Cahen–Komar.
  - The case `Y;a Y;a = 0` on an open set is ruled out, because two field equations contradict
    each other there.
  - Spacelike gradient gives the exterior form (A7). Timelike gradient gives the interior form (A8).
- **Horizon step: a sketch only.** If both cases occur, "one can obtain solutions (A8) and (A7)
  in these parts, and then join them together across the surfaces where Y;aY;a = 0 as in §5.5".
  The bifurcation sphere (dY = 0) is not treated separately. Equality of the mass parameter
  across the join is not argued.
- **Statement.** "any C² solution of Einstein's empty space equations which is spherically
  symmetric in an open set V, is locally equivalent to part of the maximally extended
  Schwarzschild solution in V".
  - They add that this still holds for C⁰, piecewise C¹ metrics, citing Bergmann, Cahen and
    Komar (1965).

**Verdict [JUDGEMENT]:** this is the textbook claim that includes horizons. It is a sketch at
r = 2m, and gives no argument at the bifurcation sphere.

### 1.2 Chruściel, *Geometry of Black Holes* (lecture notes, revised July 2018) [READ]

Source: the Vienna PDF. The OUP book (2020) grew out of these notes; I did not see the printed
book, so the numbering there may differ.

- **Theorem 1.2.1 (Jebsen/Birkhoff).** A spherically symmetric vacuum metric has a further
  *local* Killing vector X orthogonal to the orbits. "Near any point at which X is not null"
  the metric takes the Schwarzschild form.
  - **Horizon points are excluded explicitly.** This matches what the project has already proved.
- **Theorem 1.2.3** specialises An–Wong [8, Thm 3.2] to warped products
  `Q × F, g + r² h` with a cosmological constant. The trichotomy:
  1. Eddington–Finkelstein form `−(...)du² ± 2du dr + r²h`,
  2. a Λ = 0 Ricci-flat-fibre case (does not apply for S²),
  3. r constant (Nariai).
- **Remark 1.2.4:** local Killing vectors need not extend to global ones (flat torus example).
- **Theorem 1.2.8:** "The Kruskal-Szekeres spacetime is the unique extension, within the class
  of simply connected analytic extensions of the Schwarzschild region r > 2m, with the property
  that all maximally extended causal geodesics on which R_{αβγδ}R^{αβγδ} is bounded are complete."
- **Remark 1.2.9:** the exterior has many non-isometric vacuum extensions, even among maximal,
  analytic, simply connected ones.
  - Construction: take the universal cover of Kruskal minus any closed 2-surface S in the black
    hole region such that removing S breaks simple connectedness (for example the bifurcation sphere).
  - These extensions contain inextendible geodesics along which the geometry stays bounded.
- **Theorem 1.2.10 (Sbierski):** Kruskal is inextendible even with continuous (C⁰) metrics.
- **§1.4.1:**
  - "One is tempted to believe that such constructions can be used to classify all maximal
    analytic extensions, but this remains to be seen." **This is an explicit open problem.**
  - Globally hyperbolic extensions are not unique either (remove a set from a Cauchy surface,
    take the universal cover, evolve the data).
- **Example 1.4.1:** the four isometries `(T,X,p) ↦ (±T, ±X, −p)`, with −p the antipodal map.
  - `M₋±` are maximal analytic but not time-orientable.
  - `M₊₋` is the RP³ geon, a maximal globally hyperbolic analytic extension different from Kruskal.
- **Theorem 1.4.4** (Kobayashi–Nomizu Vol. I, Thm VI.6.3, with "complete" weakened to
  "timelike s-complete"). Let (M,g) and (M',g') be analytic, M connected and simply connected,
  and M' timelike s-complete. Then every isometric immersion of an open U ⊂ M into M' extends
  uniquely to an isometric immersion M → M'.
  - "s-complete" means: every maximally extended geodesic is either complete, or some
    polynomial curvature invariant is unbounded along it.
- **Corollary 1.4.7:** two connected, simply connected, s-complete analytic extensions of the
  same (U,g) are isometric.

### 1.3 Beig & Chruściel, "Stationary black holes" (gr-qc/0502041, footnote 3) [READ]

Same message as Remark 1.2.9: there are infinitely many non-isometric maximal, analytic, simply
connected vacuum extensions. Kruskal–Szekeres "is singled out by the property that it is vacuum,
analytic, simply connected, with the area of the orbits of the isometry group tending to zero
along incomplete geodesics".

### 1.4 An & Wong, "Warped product space-times", CQG 35 (2018) 025011, arXiv:1707.01483 [READ]

- **Setting.** A **global** warped product `M = Q ×_r F` with Q 2-dimensional and connected.
- **Proposition 2.7 (rigidity).** If the Q-part of the Einstein tensor is pure trace, then the
  Kodama field `K = ⋆_g dr` is a Killing field of M, unless r is constant.
  - It holds on all of Q, horizons included.
  - The zeros of dr are discrete in Q.
- **Theorem 3.2 (classification).** The Hawking energy m is constant, and
  `⟨dr,dr⟩ = S[h]/(n(n−1)) − 2m/r^{n−1} − ...`.
  - In the Lorentzian case, the metric has the explicit local form
    `−⟨dr,dr⟩ du² ± (du⊗dr + dr⊗du)` (Eddington–Finkelstein) **on the set {dr ≠ 0}**.
  - So ordinary horizon points (dr null, nonzero) are covered.
  - Points with dr = 0 get no explicit local form.
- **Caveat [JUDGEMENT]:** the paper assumes a global warped product, not just local so(3)
  Killing fields. Locally the two settings agree (Schmidt 1967; HE App. B). So the theorem gives
  the local result at every point with dr ≠ 0.

### 1.5 H.-J. Schmidt

**"A new proof of Birkhoff's theorem", gr-qc/9709071 (Grav. Cosmol. 1997) [READ]**

- Assumes SO(3) spherical symmetry written as a warped product `dσ² + e^{2U} dΩ²`.
- Shows that `ξ^i = ε^{ij}(e^U)_{;j}`, the "curl" of r, is a Killing field of the 2-metric, and
  that it lifts to 4D.
- Boundaries between the cases are "covered by a continuity argument" (no details).
- Coordinate-free. It gives the extra Killing field, not a local isometry to Kruskal at horizon points.

**"The tetralogy of Birkhoff theorems", GRG 2013, arXiv:1208.5237 [READ]**

- States the mathematical-physics version as holding "up to singular exceptions of measure
  zero" (the horizons).
- Says the coordinate-free approach needs "no special care ... to deal with the horizon" for the
  Killing field. Again, no local-isometry statement at r = 2m.

### 1.6 Schleich & Witt

**"A simple proof of Birkhoff's theorem for cosmological constant", arXiv:0908.4110 (J. Math. Phys. 51 (2010) 112502) [READ]**

- **Definition 2 (local spherical symmetry).** Every point has a neighbourhood U with three
  independent vector fields generating a faithful so(3), whose orbits are spacelike and
  2-dimensional, and which leave the tensor invariant.
  - Global symmetry means these extend to global Killing fields.
  - This is the closest published match to the project's hypothesis.
- **Theorem 1.** Locally spherically symmetric solutions of `R_ab = Λ g_ab` are locally isometric
  to Schwarzschild–(A)dS or Nariai, and are real analytic in each chart.
  - Method: a null-coordinate (Vaidya/EF) gauge `F du² + 2X du dv + Y² dΩ²`.
  - The authors claim the chart "extends ... across black and white hole horizons".
  - The mass is said to be the same in overlapping charts "due to analyticity".
- **Gap [JUDGEMENT].**
  - From `∂_v(∂_v Y / X) = 0` they conclude that either ∂_v Y ≡ 0 or `X = α(u) ∂_v Y` with α
    "nonvanishing".
  - The function `β(u) = ∂_v Y / X` can vanish on a null line u = u₀ where r is constant along
    ∂_v. That is exactly a horizon generator.
  - At ordinary horizon points you can avoid this by choosing ∂_v transverse to the horizon.
  - At the bifurcation sphere, dY = 0 and both null directions give β(u₀) = 0. The proof does
    not handle that point.

### 1.7 Other classical local proofs [SUMMARY only]

- **Bergmann, Cahen & Komar, J. Math. Phys. 6 (1965) 1–5.**
  - Schwarzschild is the only spherically symmetric vacuum solution, even for continuous,
    piecewise C¹ metrics.
  - Petrov's claimed counterexample turns out to be Schwarzschild.
- **Goenner, Commun. Math. Phys. 16 (1970) 34–47.**
  - Studies a 3-parameter isometry group with 2-dimensional non-null orbits.
  - Gives algebraic conditions on the Einstein tensor for an extra normal Killing vector.
  - Includes a historical review.
- **Bona, J. Math. Phys. 29 (1988) 1440–1441.** Generalised Birkhoff via conformal
  reducibility. Maciel–Le Delliou–Mimoso (arXiv:1803.11547, [READ] abstract and intro) note
  that it requires dY ≠ 0.
- **Szenthe, J. Geom. Phys. 57 (2007) 1099–1113** (zbMATH review).
  - SO(3)-actions with principal (S²) and exceptional orbits.
  - The principal part M* is open and dense, and is a warped product `L ×_ρ S²` "under fairly
    general global conditions".
  - Gives a "Birkhoff field" lifted from a Killing field of L.
- **Szenthe, Math. Proc. Camb. Phil. Soc. 137 (2004) 741–754** (zbMATH summary): "it seems that
  a general global theory is lacking even now"; introduces axes and transverse submanifolds for
  a classification.
- **Szenthe, Int. J. Geom. Methods Mod. Phys. 3 (2006) 1263–1271:** isometry horizons in
  spherically symmetric spacetimes are Killing horizons.

### 1.8 Verdict on Q1 [JUDGEMENT]

| Points covered | Status | Best source |
|---|---|---|
| dr not null | proved, textbook, fully written | HE App. B; Chruściel Thm 1.2.1; Schleich–Witt; Schmidt |
| dr null but ≠ 0 (horizon generators away from the bifurcation sphere) | proved; explicit EF form, but under a global warped-product assumption | An–Wong Thm 3.2 (3.4b); Chruściel Thm 1.2.3; HE sketch |
| dr = 0 (bifurcation sphere) | claimed (HE "join ... as in §5.5"); **no complete written proof found** | none |
| local vs global SO(3), S² vs RP² orbits | local so(3) Killing fields: Schleich–Witt Def. 2. RP² orbits happen in quotients (geon); the local theorem does not care | Schleich–Witt; Szenthe (exceptional orbits) |

**Assumptions in the sources.**

- C² metric (HE); C⁰ piecewise C¹ (BCK).
- Global SO(3) action (HE, Szenthe) versus local Killing algebra (Schleich–Witt).
- Global warped product (An–Wong, Schmidt).

**A short route to the bifurcation sphere [JUDGEMENT].** This is my own proof sketch, not found
in the literature. It uses only ODE facts in two dimensions, so it suits a formal proof.

1. Near p, write the 2D metric in double null form `g_Q = −Ω² du dv`, with p = (0,0).
2. Vacuum gives the Raychaudhuri equations `∂_u(Ω⁻²∂_u r) = 0` and `∂_v(Ω⁻²∂_v r) = 0`.
   So `Ω⁻²∂_u r = f(v)` and `Ω⁻²∂_v r = h(u)`.
3. Vacuum also gives the mixed equation `r ∂_u∂_v r + ∂_u r ∂_v r = −Ω²/4`.
4. The Hawking mass `m = (r/2)(1 − g(dr,dr))` has dm = 0 at every point, horizons included.
   This replaces the analyticity argument for "same m on both sides".
5. At p we have dr = 0, so f(0) = h(0) = 0, and `r(p) = 2m > 0`.
6. The mixed equation gives `∂_u∂_v r(p) = −Ω²(p)·m/(2r²) ≠ 0`. Hence f'(0) ≠ 0 and h'(0) ≠ 0.
7. Reparametrise u → U(u) and v → V(v) by solving `(ln V)' = f'(0)/f(v)`, and the same for U.
   The solution is smooth with V'(0) ≠ 0, because `f'(0)/f(v) − 1/v` is smooth.
8. In the new coordinates, `Ω̃⁻²∂_U r = aV` and `Ω̃⁻²∂_V r = aU`, with `a = −1/(8m)`.
   So `U∂_U r = V∂_V r`, which means r = R(UV) in each of the four quadrants.
9. The mass identity gives the ODE `R' = 2m(1 − 2m/R)/s`, with s = UV.
   - It integrates to `(R − 2m)e^{R/2m} = C·s` in each quadrant.
   - Smoothness of r at p (Taylor: `r = 2m − Ω̃²(p) UV/(8m) + O(3)`) forces the four constants
     C to be equal.
10. Then `Ω̃² = R'(UV)/a`. So the metric equals the Kruskal metric in (U,V), after a constant
    rescaling of U and V.

The 2-sphere part comes from the same local warped-product lemma used at the other points.
Ordinary horizon points follow An–Wong: the Kodama field K = ⋆dr is Killing, and the EF chart
uses r and a null coordinate u with K(u) = 1.

---

## 2. Q2: Is there a complete global classification?

### 2.1 Schleich & Witt, "What does Birkhoff's theorem really tell us?" arXiv:0910.5194 (2009, v1 only; no journal reference on arXiv) [READ]

**Their claims:**

- **Theorem 1.** Locally spherically symmetric vacuum data (with Λ ≥ 0) evolves into a spacetime
  that is locally spherically symmetric near Σ. So the local Birkhoff theorem applies to the
  development.
- **Example 1, "RP² Schwarzschild".**
  - Cauchy surface `R × RP²`.
  - The development is Kruskal divided by the antipodal map on the spheres.
  - Not asymptotically flat; non-orientable.
- **Example 2, the RP³ geon.**
  - Cauchy surface `RP³ − {pt}`.
  - The development is Kruskal divided by `X ↦ −X` combined with the antipodal map.
  - It has one asymptotically flat end and any positive ADM mass.
  - Its time-symmetric slice has a one-sided minimal RP² that is marginally trapped but is not
    a trapped surface.
  - It also appears in Friedman–Schleich–Witt, PRL 71 (1993) 1486.
- **Example 3, "Schwarzschild cosmologies".**
  - Data `h = a²dχ² + dΩ²`, `K = b dχ² + c dΩ²`, whose development is the black-hole (or
    white-hole) interior.
  - Quotients by the translation in χ (a boost in Kruskal) give closed Cauchy surfaces
    S¹×S², S¹×̃S², S¹×RP², RP³#RP³.
  - These are "singular both to the future and the past". They have no static region and no
    asymptotically flat end.
  - The authors claim the S¹×S² spacetime "cannot be extended through this surface" (the
    Cauchy horizon), because the boost has a fixed point at the bifurcation point.
- **Examples 4–5:** Schwarzschild–de Sitter versions, with n black holes and n de Sitter regions
  for period 2nπ; Nariai and Kasner–de Sitter cases.
- **Examples 6–8:** only *locally* spherically symmetric data.
  - Flat and hyperbolic quotients.
  - "Designer de Sitter" data: arbitrary connected sums glued by spherically symmetric necks.
    Their universal cover is not de Sitter (Morrow-Jones–Witt 1993).
- **Examples 9–11:** Birkhoff used as a recognition tool.
  - An abstractly constructed RP³ − {p} data set is recognised as the geon.
  - Data on R³ that looks like negative-mass Schwarzschild far out, but has K ~ r^{−3/2}, is
    really flat Minkowski. It is not asymptotically flat in the required sense, so it does not
    contradict the positive mass theorem.
- **Conclusions:** Birkhoff implies neither a static region nor asymptotic flatness. "not every
  maximally extended asymptotically flat, spherically symmetric spacetime is the maximal analytic
  extension of Schwarzschild" (Example 2).

**What it does not do:** it gives **no classification theorem**. It is a collection of examples.

**One correction [JUDGEMENT, high confidence].** The claimed non-extendibility of the S¹×S²
Schwarzschild cosmology holds only within globally hyperbolic extensions, or extensions through
the bifurcation point. It fails in general:

- In Kruskal null coordinates, the boost `B: (U,V) ↦ (e^a U, e^{−a} V)` acts freely and properly
  discontinuously on the open set `W = {U > 0, UV < 1}`.
- W contains the interior region II, one exterior region, and the horizon `{V = 0, U > 0}`.
- The quotient `W/B` is a smooth, analytic, Hausdorff vacuum spacetime that contains `II/B` (the
  S¹×S² cosmology) as an open subset. It extends the cosmology across one half of its Cauchy
  horizon.
- Beyond the horizon there are closed timelike curves: the static exterior with periodic time.
- The choice {V > 0} gives a second, non-isometric extension.
- This is the Misner/Taub-NUT phenomenon (compare Rieger, arXiv:2402.09312, on Misner space).
- So spherically symmetric **vacuum** already gives explicit examples of inequivalent maximal
  extensions of a maximal globally hyperbolic development. I did not find this written down for
  Schwarzschild.

### 2.2 Papers citing 0910.5194 [READ via the INSPIRE API, titles only]

INSPIRE lists 10 citing records:

- Carlip's "midisuperspace foam" papers (2021–2025) and his spacetime-foam review. These use
  locally spherically symmetric de Sitter data.
- Faraoni (2010), "The Jebsen–Birkhoff theorem in alternative gravity"; Faraoni & Capozziello's
  book *Beyond Einstein Gravity*.
- Bhattacharya (2013), on black holes with Λ > 0.
- Two f(R,T) neutron-star papers and one bimetric thesis.

**None of them extends or completes the vacuum classification** [JUDGEMENT, from titles and topics].

### 2.3 Kruskal quotients [READ]

- **Chamblin & Gibbons, PRD 55 (1997) 2177, gr-qc/9607079, Table 1.** The four freely acting
  involutions `P, P R_T, P R_Z, P R_T R_Z`, with P the antipodal map, R_T: T ↦ −T and
  R_Z: Z ↦ −Z.

  | Quotient | Asymptotically flat? | Time-orientable? | Space-orientable? |
  |---|---|---|---|
  | `R_T R_Z P` (elliptic interpretation) | yes | no | yes |
  | `R_T P` | no | no | no |
  | `R_Z P` (RP³ geon) | yes | yes | yes |
  | `P` (RP² Schwarzschild) | no | yes | no |

  They do not claim the list is exhaustive.
- **Louko (arXiv:1001.0124)** points to Chamblin–Gibbons for "a general discussion of quotients
  of Kruskal".

**Completeness of the list [JUDGEMENT].** The list is complete among quotients of the whole
Kruskal manifold:

1. `Isom(Kruskal) = O(3) × O(1,1)`. Isometries preserve r, because the Kretschmann scalar is
   `48m²/r⁶`. They also preserve the so(3) ⊕ ℝ Killing algebra and its orbits. On the (T,X)
   plane, the maps that preserve r are linear Lorentz maps.
2. Every element fixes the origin of the (T,X) plane. So any group Γ that acts properly
   discontinuously leaves the compact bifurcation sphere invariant, and hence Γ is **finite**.
3. A free finite action on S² has order at most 2, since the group order divides χ(S²) = 2. The
   non-trivial element acts by the antipodal map −I.
4. It has the form (−I, b) with b² = 1, and b is one of ±1 or a reflection. Up to conjugation by
   a boost, that gives exactly the four involutions above.
5. Result: **Kruskal plus exactly 4 quotients**. Of these, only the geon is orientable and
   time-orientable.

### 2.4 Cauchy problem view

- **Choquet-Bruhat–Geroch (1969):** the maximal globally hyperbolic development (MGHD) exists and
  is unique. Sbierski (2016) gives a proof without Zorn's lemma (search summary). Standard.
- **Schleich–Witt Theorem 1:** spherically symmetric data gives a spherically symmetric development.
- No paper found states the classification "the MGHD of spherically symmetric vacuum data equals
  a domain of dependence in Kruskal, modulo π₁(Σ)". See candidate (iii-c) in Section 3.
- The **non-analytic** extensions beyond the MGHD:
  - Chruściel–Isenberg (1993, Taub-NUT) is the classic vacuum example of inequivalent extensions.
  - In spherical symmetry with vacuum, Birkhoff makes every extension locally Kruskal. So it is
    automatically analytic once the local theorem holds at every point [JUDGEMENT].
  - Hence "non-analytic extensions" cannot occur in vacuum spherical symmetry, as long as the
    extension is itself spherically symmetric.
  - An extension that is **not** spherically symmetric beyond the Cauchy horizon is a different,
    much harder question (strong cosmic censorship territory). For Kruskal itself, Sbierski
    proved C⁰-inextendibility (JDG 108 (2018) 319–378; read via Chruściel Thm 1.2.10).

### 2.5 Uniqueness theorems that exist [READ / SUMMARY]

- **Chruściel, Theorem 1.2.8 [READ]:** see §1.2.
- **Chruściel & Cortier, "Maximal analytic extensions of the Emparan–Reall black ring", JDG 85
  (2010) 425–459, Thm 4.5** [SUMMARY]: the same Schwarzschild uniqueness, used as the model case.
- **Inextendibility:** C² (Kretschmann blow-up plus geodesic analysis) and C⁰ (Sbierski).

---

## 3. Q3: Graded candidate statements [JUDGEMENT throughout]

Notation:

- X_m = Kruskal(m) for m > 0, Minkowski for m = 0, and negative-mass Schwarzschild
  `ℝ_t × (0,∞)_r × S²` for m < 0.
- "LSS vacuum": a connected smooth Lorentzian 4-manifold that is Ricci-flat and has, around every
  point, three Killing fields with so(3) brackets and 2-dimensional spacelike orbits. This is the
  project's hypothesis, imposed everywhere.

### (i) Known and textbook

- **T1 (local, non-null points).** At every point of an LSS vacuum where dr is not null, there is
  a neighbourhood isometric to an open subset of Schwarzschild with some real m. Sources: HE App.
  B, Chruściel Thm 1.2.1, Schleich–Witt, Schmidt. Already machine-checked by the project.
- **T2 (uniqueness of Kruskal).** Kruskal(m) is the unique connected, simply connected, analytic
  vacuum extension of the Schwarzschild exterior in which every causal geodesic with bounded
  Kretschmann scalar is complete (Chruściel Thm 1.2.8).
- **T3 (inextendibility).** Kruskal is C²- and even C⁰-inextendible (Sbierski).
- **T4 (non-uniqueness).** Maximal analytic, simply connected extensions of the exterior are not
  unique. The RP³ geon is a maximal globally hyperbolic analytic extension different from Kruskal
  (Chruściel Remark 1.2.9, Example 1.4.1; Friedman–Schleich–Witt).

### (ii) Known but scattered or sketched

- **S1 (all points: the project's goal (a)).** Every point of an LSS vacuum has a neighbourhood
  isometric to an open subset of X_m, with **one** m for all of M (M connected).
  - At dr = 0 points, which only occur for m > 0, the model is a neighbourhood of the Kruskal
    bifurcation sphere.
  - Status: HE claim with a sketch; An–Wong prove the case dr ≠ 0; the bifurcation sphere is
    unwritten. Proof route: §1.8.
- **S2 (constancy of mass).** The Hawking mass `m = (r/2)(1 − |dr|²)` satisfies dm = 0
  everywhere for vacuum spherical symmetry (An–Wong Prop. 2.16 and Thm 3.2). This is the clean
  replacement for "analyticity forces the same m".
- **S3 (Z₂ quotients).** The four freely acting involutions and their quotients (Chamblin–Gibbons;
  Chruściel Ex. 1.4.1). Completeness of that list is easy (§2.3) but I did not see it stated.
- **S4 (examples beyond Kruskal).** RP² Schwarzschild, the geon, S¹×S² and other closed
  Kantowski–Sachs-type quotients, and universal covers of Kruskal minus a closed set (Schleich–Witt
  0910.5194; Chruściel §1.4.1).

### (iii) Plausibly open: no published statement found

- **G1 (developing-map global Birkhoff).** Let M be an LSS vacuum with mass m, and M̃ its
  universal cover. Then:
  - there is a local isometry `D: M̃ → X_m` and a homomorphism `ρ: π₁(M) → Isom(X_m)` with
    `D∘γ = ρ(γ)∘D`;
  - the pair (D, ρ) is unique up to `(D,ρ) ↦ (g∘D, g ρ g⁻¹)` for g ∈ Isom(X_m).

  Proof route:
  - Use S1, then the rigidity of X_m: every isometry between connected open subsets of X_m is the
    restriction of a unique global isometry. That follows from Chruściel Thm 1.4.4 applied with
    M = M' = X_m, plus the s-completeness of X_m.
  - Then Thurston's (G,X)-structure argument (analytic continuation along paths, monodromy) gives
    D and ρ.
  - With rigidity proved directly for Kruskal, no analytic manifold theory is needed for M itself.
- **G2 (classification under s-completeness).** Suppose an LSS vacuum M with m > 0 is s-complete:
  every inextendible geodesic is complete, or some polynomial curvature invariant is unbounded
  along it. Then M is isometric to exactly one of:
  - Kruskal(m),
  - Kruskal/P (RP² Schwarzschild),
  - Kruskal/(R_Z P) (RP³ geon),
  - Kruskal/(R_T P),
  - Kruskal/(R_T R_Z P).

  If M is also orientable and time-orientable, M is Kruskal or the RP³ geon.

  Proof: by G1, D is an isometry M̃ ≅ X_m (Cor. 1.4.7 needs s-completeness of both sides), so
  M ≅ X_m/Γ; then apply §2.3.

  Variants:
  - For m < 0 the list is infinite. Quotients may contain time translations, so they have closed
    timelike curves.
  - For m = 0 every flat spacetime qualifies, so the classification of complete flat Lorentzian
    4-manifolds is a separate hard problem. Excluding m = 0, or demanding global Killing fields,
    keeps the statement clean.
- **G3 (maximal globally hyperbolic developments).** Let (Σ,h,K) be complete, spherically
  symmetric vacuum data with m > 0 and simply connected Σ. Then:
  - the MGHD is isometric to the domain of dependence, in Kruskal, of an embedded spacelike
    hypersurface `Σ̂ = γ × S²`, with γ a complete spacelike curve in the Kruskal (T,X) plane;
  - for general Σ, the MGHD is that domain of dependence divided by the holonomy image of π₁(Σ).

  Corollaries:
  - Complete data with two asymptotically flat ends gives exactly Kruskal.
  - Compact Σ forces the image into region II or IV, giving the S¹×S²-type Kantowski–Sachs quotients.

  Key fact: spacelike curves in the 2D Kruskal plane are graphs over X, so D restricted to Σ̃ is
  injective.
- **G4 (all maximal analytic LSS vacua).** Classify every inextendible analytic LSS vacuum.
  - Chruściel says this "remains to be seen".
  - The family includes universal covers of Kruskal minus closed sets, quotients of non-simply
    connected open pieces, and Misner-type quotients W/B of the S¹×S² cosmologies.
  - Some constructions are non-Hausdorff and must be excluded.
  - **Genuinely open and hard.** It is closer to a description ("immersed pieces of Kruskal that
    cannot be enlarged") than to a list. G1 reduces it to: which open Γ-invariant domains
    Ω ⊂ X_m admit no larger Γ'-equivariant extension.
- **G5 (horizon points, global SO(3) action, regularity).** HE claim C², and BCK claim C⁰
  piecewise C¹. A low-regularity version of S1 (for example C^{1,1} metrics at the bifurcation
  sphere) is not written down anywhere I found.

---

## 4. Recommendation for the Lean project [JUDGEMENT]

1. **First, S1 (goal (a)).** It is the one missing local piece. Everything global depends on it.
   Suggested order:
   1. dm = 0 pointwise (S2).
   2. The Kodama field is Killing everywhere.
   3. EF charts at points with dr null but nonzero (An–Wong argument).
   4. The bifurcation sphere by the double-null reparametrisation trick of §1.8: two
      Raychaudhuri first integrals plus one separable ODE. No analyticity and no characteristic
      initial value problem needed.
2. **Then the most promising global theorem: G2**, "an s-complete, non-flat LSS vacuum with
   m > 0 is Kruskal or one of its four Z₂ quotients", and as a corollary, "orientable +
   time-orientable ⇒ Kruskal or the RP³ geon".
   - It is a clean, finite, checkable list. It strengthens textbook T2: from "analytic extension
     of the exterior" to "any spherically symmetric vacuum".
   - Its ingredients are explicit:
     - S1;
     - rigidity of Kruskal (isometries are O(3) × O(1,1), local isometries extend);
     - the developing map;
     - s-completeness of Kruskal (geodesic analysis);
     - the finite group argument of §2.3.
   - The hardest formal ingredient is the geodesic analysis behind s-completeness of Kruskal.
   - A lighter first milestone: **G1 for simply connected M**, "every simply connected LSS
     vacuum with m > 0 maps into Kruskal by a local isometry". It needs only S1, rigidity, and
     path-lifting, and no geodesic completeness.

---

## Sources

- Hawking & Ellis, *The Large Scale Structure of Space-Time* (CUP 1973), Appendix B, pp. 369–372 [READ, Cambridge PDF].
- P.T. Chruściel, *Geometry of Black Holes*, lecture notes revised July 2018,
  https://homepage.univie.ac.at/piotr.chrusciel/teaching/Black%20Holes/BlackHolesVienna.pdf [READ: Thm 1.2.1, 1.2.3, 1.2.8, Rem. 1.2.9, Thm 1.2.10, §1.4.1, Ex. 1.4.1, Thm 1.4.4, Cor. 1.4.7].
- R. Beig & P.T. Chruściel, "Stationary black holes", arXiv:gr-qc/0502041 [READ, footnote 3].
- X. An & W.W.Y. Wong, "Warped product space-times", CQG 35 (2018) 025011, arXiv:1707.01483 [READ: Prop. 2.7, Thm 3.2].
- H.-J. Schmidt, "A new proof of Birkhoff's theorem", arXiv:gr-qc/9709071 [READ].
- H.-J. Schmidt, "The tetralogy of Birkhoff theorems", GRG 45 (2013) 395, arXiv:1208.5237 [READ].
- K. Schleich & D.M. Witt, "A simple proof of Birkhoff's theorem for cosmological constant", J. Math. Phys. 51 (2010) 112502, arXiv:0908.4110 [READ].
- K. Schleich & D.M. Witt, "What does Birkhoff's theorem really tell us?", arXiv:0910.5194 [READ].
- A. Chamblin & G.W. Gibbons, "Nucleating black holes via non-orientable instantons", PRD 55 (1997) 2177, arXiv:gr-qc/9607079 [READ: §I, Table 1].
- J. Louko, "Geon black holes and quantum field theory", arXiv:1001.0124 [READ: intro].
- A. Maciel, M. Le Delliou, J.P. Mimoso, "Revisiting the Birkhoff theorem from a dual null point of view", arXiv:1803.11547 [READ: abstract and intro].
- P.G. Bergmann, M. Cahen, A.B. Komar, J. Math. Phys. 6 (1965) 1 [SUMMARY].
- H. Goenner, Commun. Math. Phys. 16 (1970) 34 [SUMMARY].
- C. Bona, J. Math. Phys. 29 (1988) 1440 [SUMMARY, zbMATH].
- J. Szenthe, Math. Proc. Camb. Phil. Soc. 137 (2004) 741; Int. J. Geom. Meth. Mod. Phys. 3 (2006) 1263; J. Geom. Phys. 57 (2007) 1099 [SUMMARY, zbMATH].
- P.T. Chruściel & J. Cortier, JDG 85 (2010) 425 [SUMMARY].
- J. Sbierski, "The C⁰-inextendibility of the Schwarzschild spacetime...", JDG 108 (2018) 319 [via Chruściel's notes and search listing].
- J.L. Friedman, K. Schleich, D.M. Witt, PRL 71 (1993) 1486 [cited; not read].
- N.E. Rieger, "Coverings and non-Hausdorff extensions of Misner spacetime", arXiv:2402.09312 [SUMMARY].
- INSPIRE citation list of arXiv:0910.5194 (10 records) [READ via API].
