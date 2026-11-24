# Relativist's review: definitions and the final statement of `birkhoffNoCoordinates`

The snapshot I read is the repository at commit 600b6a2. Paths below are relative to its root (`repo:` marks files read in the live repository).
Lean says the proof is correct. This review only asks whether the words mean what a relativist means by them.

## Table of verdicts

| # | Lean notion | Textbook notion | Verdict |
|---|---|---|---|
| 1 | `HasOneTimeDirection` (Basic.lean:81) | Lorentzian signature (-,+,+,+) | **matches** |
| 2 | `Nondegenerate` (Basic.lean:86) | nondegenerate bilinear form | **matches** |
| 3 | `IsSmoothOn` (Basic.lean:201) | C^infinity metric (a smooth section of T*M (x) T*M) | **matches** (assumes more smoothness than Hawking–Ellis's C^2; harmless) |
| 4 | `IsLengthMeasureOn` (Basic.lean:208) | semi-Riemannian metric on an open set | **matches** |
| 5 | `IsSpaceTimeOn` (Basic.lean:218) | Lorentzian metric (space-time) | **matches**. No time orientation and no Hausdorff or paracompact space are assumed; harmless for a local theorem, and only makes the theorem more general |
| 6 | `IsConnectionOf` (Basic.lean:246) | Levi-Civita connection | **matches**. Uniqueness is proved (Unique.lean:76). Existence on a general manifold is not proved; this is harmless, see D6 |
| 7 | `curvatureOfFields` (Basic.lean:265) | R(X,Y)Z = nabla_X nabla_Y Z - nabla_Y nabla_X Z - nabla_[X,Y] Z | **matches** (Wald/Carroll/MTW sign; O'Neill's has the opposite sign) |
| 8 | `curvatureAt` (Basic.lean:275) | Riemann tensor at a point | **differs but harmless**: it extends the vectors as constant fields in the chart at x; any extension gives the same answer because the tensor is tensorial |
| 9 | `ricciAt` (Basic.lean:304) | Ric(v,w) = tr(u -> R(u,v)w) = R^a_{vaw} | **matches**: sign tested (sphere Ric = +g; de Sitter Ric = (3/L^2) g) |
| 10 | `IsEmptyOn` (Basic.lean:310) | vacuum Einstein equations with Lambda = 0, i.e. Ric = 0 (equivalent to G_ab = 0 in 4 dimensions) | **matches** |
| 11 | `LeavesUnchangedAt` (Basic.lean:321) | Killing field: L_xi g = 0 | **matches** |
| 12 | `IsRoundOn` (Basic.lean:338) | spherical symmetry: SO(3) acts by isometries with spacelike 2-sphere orbits | **differs but harmless** (the Lean version is weaker, so the theorem is stronger): it uses the Lie algebra so(3) acting locally, not a group action, and allows no fixed points in s. See D12 |
| 13 | `sizeSq` (Goal.lean:60) | r^2, where r is the area radius (Area = 4 pi r^2) | **matches** (it does not depend on which basis is chosen; see D13) |
| 14 | `UsableDistanceAt` (Goal.lean:68) | grad r is not null (g^{ab} d_a r d_b r != 0), i.e. not on the horizon | **matches** as a definition. Because it is a **hypothesis**, it is the main way the theorem is weaker than Hawking–Ellis |
| 15 | Schwarzschild table `roundG (schwA m) (schwB m)` (repo: RoundSpacetime.lean:146-157, OneMass.lean:72-75) | -(1-2m/r)dt^2 + (1-2m/r)^-1 dr^2 + r^2 dOmega^2 | **matches**: coordinate order (t,r,theta,phi), signature (-+++) |
| 16 | `outside m`, `inside m` (KnownAnswers.lean:388, 391) | exterior r>2m and interior 0<r<2m, with the poles left out | **matches**. When m <= 0, `outside m` is all of r>0, so m=0 (Minkowski) and negative mass are included |
| 17 | `BirkhoffNoCoordinates` (Goal.lean:166) | Birkhoff's theorem, local form | **weaker than Hawking–Ellis App. B in two ways** (horizon points are excluded; m is not shown to be the same over all of s). **Stronger in one way** (only small rotations need to keep lengths unchanged, not a full SO(3) group). It is fair to call it "local Birkhoff away from the horizon" |
| 18 | Doc comments | — | **stale text, fix before submission**: Goal.lean:17-18 and :149 still say "not proved anywhere"; Basic.lean:244-245 says uniqueness "is not shown here" but Unique.lean proves it |

Most serious issue: none of the definitions is wrong. The gap that matters for a paper is in the statement. It says nothing at points where the gradient of r is null (the horizon r = 2m). It also does not say that one mass m serves all of a connected region s. Both are part of the usual statement (Hawking–Ellis: "locally equivalent to part of the maximally extended Schwarzschild solution"). The paper's wording has to state these limits.

---

## Details

Conventions I compare against: Wald (1984) §3.2 and §3.4 (Riemann: (nabla_a nabla_b - nabla_b nabla_a) omega_c = R_abc^d omega_d, Ricci R_ac = R_abc^b); Carroll gr-qc/9712019 ch. 3 ([nabla_mu, nabla_nu] V^rho = R^rho_{sigma mu nu} V^sigma, R_{mu nu} = R^lambda_{mu lambda nu}); O'Neill (1983) ch. 3 (R_XY Z = nabla_[X,Y] Z - [nabla_X, nabla_Y] Z, the opposite sign, but Ricci(sphere) > 0 in all three); Hawking–Ellis (1973) §2.6 and Appendix B; Straumann, *General Relativity* (2nd ed. 2013), the chapter on Schwarzschild and Birkhoff (a warped-product, coordinate-free treatment).

### D1. `HasOneTimeDirection` — Basic.lean:81-82
- Textbook: g_x has signature (1, n-1). This means there is an orthogonal basis with one negative and n-1 positive norms. Equivalently, there is a timelike t with g(t,t) < 0 whose orthogonal complement is positive definite.
- Lean: there is a t with b(t,t) < 0, and every nonzero v with b(t,v) = 0 has b(v,v) > 0.
- Verdict: **matches**. Since g(t,t) != 0, V = span(t) (+) t^perp, and the form is (-) on the first part and (+…+) on the second. So the signature is exactly (1,3). `not_orthogonal` (Basic.lean:110) proves that this means "exactly one" time direction, not "at least one". The sign convention is mostly-plus (Wald, MTW, Carroll). A metric written in the (+,-,-,-) convention fails this test; it has to be replaced by -g first. That is a choice of convention, not a mistake. The paper should say "(-,+,+,+)".

### D2. `Nondegenerate` — Basic.lean:86-87
Standard. On s it follows from D1 together with symmetry (`HasOneTimeDirection.nondegenerate`, Basic.lean:90).

### D3–D5. `IsSmoothOn`, `IsLengthMeasureOn`, `IsSpaceTimeOn` — Basic.lean:201-231
- `IsSmoothOn` says g is a C^infinity section, on s, of the bundle Hom(TM, Hom(TM, R)). That is the textbook "smooth metric". `isSmoothOn_flat_iff` (Flat.lean:200) checks that in a chart this is ordinary smoothness of the components.
- `IsSpaceTimeOn` = symmetric + one time direction at every x in s + smooth on s. This is a Lorentzian metric on the region s.
- What the textbooks add that Lean does not ask for: Hausdorff, paracompact, connected and time-orientable spaces (Hawking–Ellis §3.1; Wald §8.1 adds time orientation for causal structure). None of these matter for a local statement, and leaving them out only widens the theorem. M is in `Type` (universe 0), which is harmless.
- Dimension 4 comes from the model space `Coords 4 = Fin 4 → ℝ` (repo: Curvature.lean:39) with `𝓘(ℝ, Coords 4)`. It is not taken as an extra assumption. The norm on `Fin 4 → ℝ` is the sup norm, which is irrelevant topologically.
- Smoothness: Hawking–Ellis state Birkhoff for C^2 metrics. Lean asks for C^infinity. This makes the Lean statement slightly weaker in regularity, but nobody in GR would object.

### D6. `IsConnectionOf` — Basic.lean:246-257
- Textbook: nabla is the unique torsion-free, metric-compatible connection (Wald Thm 3.1.1; O'Neill Thm 3.11).
- Lean: (i) mathlib's `IsCovariantDerivativeOn`, meaning additive and Leibniz on sections that are differentiable at points of s (repo: .lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/Basic.lean:92-100). Linearity in the direction slot is built into the type `TangentSpace x →L …`. mathlib warns that `cov σ x (X x)` is nabla_X sigma at x, and Basic.lean uses it the right way round. (ii) `noTwist`: nabla_X Y - nabla_Y X = [X,Y]. (iii) `keepsLengths`: v(g(Y,Z)) = g(nabla_v Y, Z) + g(Y, nabla_v Z).
- Bracket convention: mathlib's `mlieBracket I X Y` is the standard [X,Y] = X(Y) - Y(X). Flat.lean:94-98 checks this: it equals DY·X - DX·Y.
- Verdict: **matches**. Uniqueness is proved (`IsConnectionOf.unique`, Unique.lean:76). So `IsEmptyOn` cannot be made true by choosing a convenient connection, and de Sitter is correctly *not* empty (KnownAnswers.lean:363).
- Remaining point: existence of a Levi-Civita connection on a general manifold is not formalised (`ConnectionExistsStatement` is open; README:102). For the theorem this is harmless. `IsEmptyOn` is a *hypothesis*, so to apply the theorem to some textbook vacuum space-time you must supply a `cov`. On any chart domain the Christoffel connection already does this (`IsRegularTableOn.isConnectionOf`, Tables.lean:547). A global one can be built by taking chartAt x's Christoffel symbols at each x, since the axioms are pointwise. Mathematically, "IsEmptyOn ⟺ Ric[g] = 0 on s" is true. The paper should say that uniqueness is formalised and existence is the standard textbook fact (formalised in a chart).

### D7. `curvatureOfFields` — Basic.lean:265-267
- Lean: R(X,Y)Z = nabla_X(nabla_Y Z) - nabla_Y(nabla_X Z) - nabla_[X,Y] Z. Reading `cov Z y (Y y)` as (nabla_Y Z)(y) confirms the order.
- This is the Wald/Carroll/MTW convention: R(X,Y)Z = R^rho_{sigma mu nu} Z^sigma X^mu Y^nu in Carroll's notation. O'Neill's R_XY has the opposite overall sign.
- Verdict: **matches**. For a vacuum theorem the overall sign does not matter anyway.

### D8. `curvatureAt` — Basic.lean:275-277
- Lean extends u, v, w with mathlib's `extend` (constant components in the trivialisation at x, i.e. in chartAt x; Flat.lean:102 checks this in flat space). Then it evaluates R on these fields at x.
- Textbook: R is a tensor, so any extension gives the same value.
- Verdict: **differs but harmless**. On a smooth manifold with the (unique, smooth) Levi-Civita connection, the result is the textbook Riemann tensor. Independence of the extension is proved only in flat coordinate space (`curvatureOfFields_flat_eq_curvatureAt`, Flat.lean:364). In general it is not needed, because the definition picks a specific valid extension.

### D9. `ricciAt` — Basic.lean:304-305 (with `traceIn`, :287; `stepBasis`, :298)
- Lean: Ric(v,w) = tr(u ↦ R(u,v)w). The trace is read off in a fixed basis, and the result does not depend on the basis (`traceIn_eq_trace`, Flat.lean:381).
- Index form: R^mu_{sigma mu nu} w^sigma v^nu. This is Carroll's R_{mu nu} = R^lambda_{mu lambda nu}, or equally Wald's R_ac = R_abc^b. Ricci is symmetric for Levi-Civita, so the order of the slots does not matter.
- Sign tested against known answers: unit 2-sphere Ric = +g (KnownAnswers.lean:205), correct since Ric = (n-1)K g. De Sitter Ric = (3/L^2) g (KnownAnswers.lean:346), correct since Ric = Lambda g with Lambda = 3/L^2.
- Verdict: **matches**.

### D10. `IsEmptyOn` — Basic.lean:310-312
- Lean: there is a connection of g on s, and its Ricci vanishes on s.
- Textbook "vacuum": G_ab + Lambda g_ab = 0. With Lambda = 0 in 4 dimensions this is equivalent to R_ab = 0 (take the trace: R = 0).
- Verdict: **matches vacuum with Lambda = 0**. It does not cover Lambda != 0 (Kottler/Schwarzschild–de Sitter) or Einstein–Maxwell (Reissner–Nordström). Hawking–Ellis App. B also treats those, and the paper must not suggest otherwise. Leaving out Lambda is sensible: with Lambda > 0 the Nariai solution (r = const) breaks the naive statement.

### D11. `LeavesUnchangedAt` — Basic.lean:321-324
- Lean: xi(g(X,Y)) = g([xi,X],Y) + g(X,[xi,Y]) for all X, Y differentiable at x. This is (L_xi g)(X,Y) = 0 at x, because L_xi X = [xi,X].
- Textbook: Killing's equation, L_xi g = 0, equivalently nabla_(a xi_b) = 0 (Wald App. C.3; Carroll §5.? "Killing vectors").
- Check: `leavesUnchangedAt_flat_iff` (Flat.lean:250) and `leavesUnchangedAt_table_iff` (Tables.lean:395) reduce it to xi^k d_k g_ij + g_kj d_i xi^k + g_ik d_j xi^k = 0, the textbook coordinate form.
- Verdict: **matches**. It is only meaningful where g is differentiable. That holds on s, which is the only place it is used.

### D12. `IsRoundOn` — Basic.lean:338-351
- Textbook (Hawking–Ellis App. B; Wald §6.1; Straumann): space-time is spherically symmetric if its isometry group contains a subgroup isomorphic to SO(3) whose orbits are spacelike 2-spheres (Hawking–Ellis also allow fixed points, the centre). Consequence: locally g = h_AB dx^A dx^B + r^2 dOmega^2, a warped product.
- Lean: on the open set s there are three C^infinity Killing fields with [xi0,xi1]=xi2, [xi1,xi2]=xi0, [xi2,xi0]=xi1 (the Lie algebra so(3)). At every x in s they span a 2-plane, and g is positive definite on that plane.
- Points to check:
  1. *Sign of the structure constants.* Vector fields of a left action form an anti-representation. But xi -> -xi maps the relation [xi_i,xi_j] = eps_ijk xi_k to its negative, and both describe so(3). Harmless.
  2. *Lie algebra instead of group.* Lean asks only for the infinitesimal (local) action. Every SO(3) action gives such fields, but not every such set of fields comes from a global action. So the hypothesis is **weaker** and the theorem **stronger** than the textbook one. Locally there is nothing exotic. The kernel of the action is an ideal of the simple algebra so(3), so with 2-dimensional orbits the action is faithful. The isotropy is 1-dimensional, every 1-dimensional subalgebra of so(3) is conjugate to so(2), and so the orbits are locally so(3)/so(2) = S^2 with a round metric (an so(3) Killing algebra forces constant curvature K > 0). README:140-147 says this honestly.
  3. *No fixed points in s.* `surfaces` asks for rank exactly 2 everywhere on s, so the centre (orbits that are points) is left out. For vacuum this only loses the regular centre of Minkowski (m = 0). Harmless.
  4. *Spacelike orbits.* `positive` is exactly "orbits spacelike". Matches.
  5. *Poles.* Nothing about poles is assumed on M. Only the image of the chart in the conclusion avoids sin(theta) = 0, which is why p is placed on the equator in `TurnsCoordinatesStatement` (Turns.lean:155). So unlike the coordinate theorems, **no point of M is left out because of the poles**. README:148 ("the two poles ... left out of every statement") undersells the curved statement, and the paper can say so.
- Verdict: **differs but harmless (more general)**.

### D13. `sizeSq` — Goal.lean:60-61
- Lean: r^2 := (|xi0|^2 + |xi1|^2 + |xi2|^2)/2.
- Textbook: the area radius r, defined by Area(orbit) = 4 pi r^2 (Misner–Sharp/Hawking–Ellis "r").
- Check: on a round sphere of radius r, the standard rotation fields satisfy sum|xi_i|^2 = r^2(3 - 1) = 2r^2. The relations with unit structure constants fix the basis up to Aut(so(3)) = SO(3), and the trace is O(3)-invariant. So sizeSq does not depend on which fields satisfying `likeTurns` are chosen, and it equals r^2 of the orbit through x (the orbit is locally round, by D12.2). Test: `schwarzschild_sizeSq` (Goal.lean:130) gives r^2.
- Verdict: **matches**, and it is a neat coordinate-free definition. It deserves a sentence in the paper.

### D14. `UsableDistanceAt` — Goal.lean:68-70
- Lean: there is an n at p with g(n,·) = d(r^2), so n = grad(r^2), and g(n,n) != 0.
- Because g is nondegenerate, such an n always exists, so the condition reduces to g(grad r^2, grad r^2) = 4r^2 |grad r|^2 != 0. Since r > 0 on s, this says *grad r is not null* (and not zero).
- In vacuum, |grad r|^2 = 1 - 2m/r, where m is the (constant) Misner–Sharp mass. So the condition fails exactly on r = 2m, the horizon, for m > 0. A short argument (textbook, not formalised) shows this set has empty interior in s. If |grad r|^2 = 0 on an open set, then r = 2m is constant there, so grad r = 0. But an r = const vacuum metric M^2 x S^2(r) needs Lambda != 0 or matter (Nariai, Bertotti–Robinson). So with Lambda = 0, `UsableDistanceAt` holds on a dense open subset of s.
- Verdict: **matches** the textbook condition "dr is not null". As a hypothesis of the theorem it marks the main way the theorem is weaker than Hawking–Ellis (see D17).

### D15–D16. The Schwarzschild target: `roundG`, `schwA`, `schwB`, `outside`, `inside`
- repo: RoundSpacetime.lean:146-157: diag(-A(r), B(r), r^2, r^2 sin^2 theta) in coordinates (t, r, theta, phi) = (x0, x1, x2, x3). repo: OneMass.lean:72,75: A = 1 - 2m/r, B = (1 - 2m/r)^-1. That is the textbook Schwarzschild line element in Schwarzschild coordinates, signature (-+++), G = c = 1.
- `outside m` = {r > 0, r > 2m, sin theta != 0}. `inside m` = {0 < r < 2m, sin theta != 0} (KnownAnswers.lean:388-391). Inside, the same formula holds with r timelike (`schwarzschild_isSpaceTimeOn_inside`, KnownAnswers.lean:461). That is the correct Kantowski–Sachs-type interior. For m <= 0, `outside m` is just r > 0, so **m = 0 (Minkowski in spherical coordinates) and m < 0 (negative mass) are both allowed**, as they should be in a local vacuum theorem. `inside m` is empty unless m > 0.
- Verdict: **matches**.

### D17. The final statement — Goal.lean:166-178, proved in Join/Goal.lean:36

**What it says, in textbook words.** Let (M, g) be a smooth 4-manifold and s ⊂ M open. Suppose that on s, g is Lorentzian, Ric[g] = 0, and three Killing fields obey the so(3) relations with 2-dimensional spacelike orbits. Then for every p in s at which grad r is not null, there are a real m and a smooth chart phi around p, mapping into the Schwarzschild exterior (r > 2m) or interior (0 < r < 2m) coordinate region with the poles removed, such that g = phi^* g_Schw(m) on the domain of phi. In other words, p has a neighbourhood isometric to an open piece of Schwarzschild in Schwarzschild coordinates.

Checks on the conclusion:
- `φ ∈ maximalAtlas` (Goal.lean:173): phi is a smooth chart compatible with M, so a diffeomorphism onto an open subset of R^4. With `g q v w = g_S(φ q)(dφ v, dφ w)` this is exactly "phi is an isometry onto its image". Correct direction: `schwarzschild_meets_conclusion` (Goal.lean:197) checks it with the identity chart.
- Not required: φ.source ⊆ s. This makes the conclusion slightly stronger, not weaker.
- Not stated: phi carries the xi_i to the standard rotations. Birkhoff's theorem is about g, so that is fine. A stronger version could add it.
- Satisfiable: `schwarzschild_meets_goal` (Goal.lean:183). So the theorem is not vacuous.

**Comparison with Hawking–Ellis, Appendix B.** From memory (check the page before citing): they show that a C^2 vacuum solution that is spherically symmetric on an open set V is locally equivalent to part of the maximally extended (Kruskal) Schwarzschild solution in V. They go through the cases where grad r is spacelike, timelike or null.

| Aspect | Hawking–Ellis App. B | Lean | Effect |
|---|---|---|---|
| Dimension | 4 | 4 (model `Coords 4`) | same |
| Signature | Lorentzian | Lorentzian, (-+++) | same |
| Field equations | vacuum, Lambda = 0 (they also treat Einstein–Maxwell) | Ric = 0 (Lambda = 0) | same for vacuum; EM and Lambda not covered |
| Regularity | C^2 | C^infinity | Lean slightly weaker (harmless) |
| Symmetry | SO(3) isometry group, spacelike 2-sphere orbits (fixed points allowed) | so(3) Killing algebra, locally, 2-dim spacelike orbits, no fixed points on s | Lean **stronger** in the symmetry part; leaves out the centre (only matters for m = 0) |
| Points covered | all of V, including the horizon r = 2m (via Kruskal) | only p with grad r not null; **horizon points excluded** | Lean **weaker** |
| Target | maximally extended Schwarzschild | Schwarzschild coordinate patches r > 2m or 0 < r < 2m | Lean weaker (no Kruskal or Eddington–Finkelstein patch), which is the same point as the row above |
| Mass | one m for the connected region | an m for each point p (constant only on the chart around p) | Lean **weaker**; one m over connected s is not stated |
| m <= 0 | allowed by the local argument | allowed (m ∈ R; m = 0 is Minkowski, m < 0 is negative mass) | same |
| Interior r < 2m | included | included (`inside m`) | same |
| Local/global | local | local | same |

Second source, Straumann (GR, 2nd ed.), Birkhoff section; also Schmidt, gr-qc/9709071, "A new proof of Birkhoff's theorem", Grav. Cosmol. 3 (1997) 185. Both prove it without coordinates for the symmetry (warped product, or reduction to 2D dilaton gravity) and get local isometry with Schwarzschild where grad r is not null, treating the null case separately. The Lean statement matches these "where grad r is not null" versions closely. Carroll's notes (ch. 7) prove it in coordinates, assuming coordinates adapted to the spheres and r usable as a coordinate. The Lean statement is strictly stronger than Carroll's version, because it builds those coordinates instead of assuming them. Wald §6.1 states the theorem and leaves the proof as an exercise (from memory; check).

Note on novelty: Schmidt (1997) already calls his paper-and-pencil proof coordinate-free. The paper should say that the novelty is the *formalised* coordinate-free statement and proof, not a coordinate-free proof as such. That matches README:87-88 ("not found is not first").

**Is it fair to call it "Birkhoff's theorem, local form, from coordinate-free symmetry assumptions"?** Mostly yes. The symmetry and the field equations are stated without coordinates, and the conclusion is the standard local isometry. The title needs one qualifier: "away from the horizon" (where grad r is null). The paper should also say plainly: Lambda = 0, vacuum only, smooth metric, and the infinitesimal (Lie-algebra) form of spherical symmetry. Without the qualifier, a GR referee will object that Hawking–Ellis's version covers the horizon.

**Suggested one-sentence claim:**
> Let g be a smooth Lorentzian metric on a 4-manifold that is Ricci-flat on an open set carrying three Killing fields with the commutation relations of so(3), whose orbits are 2-dimensional and spacelike; then every point of that set at which the gradient of the area radius is not null has a neighbourhood isometric to an open subset of the Schwarzschild exterior (r > 2m) or interior (0 < r < 2m) region for some real mass m (m <= 0 included).

Short title: "A formal proof of Birkhoff's theorem away from the horizon, from coordinate-free symmetry assumptions."

### Suggested follow-ups (in order of value to a referee)
1. **One mass for the whole region.** State and prove that m is given at p by a formula in g and xi alone, m = (r/2)(1 - g(grad r, grad r)) (the Misner–Sharp mass), and that it is constant on each connected component of s. This holds across the horizon too, because it is a smooth function on s that is locally constant on a dense set. This closes the "m per point" gap cheaply.
2. **The horizon.** Either prove that horizon points have empty interior in s (the argument in D14), so the theorem holds on a dense open set; or add an Eddington–Finkelstein target chart (the repo already has `Eddington.lean`) to cover points with null grad r. Either one turns "weaker than Hawking–Ellis" into "equal on a dense set" or "equal".
3. Prove `ConnectionExistsStatement` (D6), so that "IsEmptyOn ⟺ Ricci-flat" is formal in both directions.
4. Fix the stale doc comments: Goal.lean:17-18 ("It is a statement, not a theorem ... not proved anywhere in this project yet") and Goal.lean:149 ("A statement, not yet a theorem"); Basic.lean:244-245 (uniqueness "not shown here", but Unique.lean:76 proves it). A referee reading the source will trip over these.
