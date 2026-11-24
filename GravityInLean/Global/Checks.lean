/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.Global

import Mathlib.Analysis.Convex.Contractible
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Checks of the statements for a whole space-time

The statements of `Goals/Global.lean` are tested here before anyone tries to prove them.

* **The model tables say what they should.** `kruskalWhole_apply`, `schwSpace_apply`: the two
  whole tables, read as formulas.
* **The pole-free Kruskal's is the shared Kruskal's** (`kruskalWrap_isKruskalMapOn`): wrapping
  Kruskal's table of `Goals/EveryPoint.lean` round the unit sphere,
  `(T, X, θ, φ) ↦ (T, X, sin θ cos φ, sin θ sin φ, cos θ)`, is a length-keeping map into
  Kruskal's whole space-time, on every open region away from the centre.
* **Schwarzschild's in ordinary space labels is Schwarzschild's**
  (`sphericalToSpace_isSchwarzschildMapOn`): `(t, r, θ, φ) ↦ (t, r sin θ cos φ, r sin θ sin φ,
  r cos θ)` is a length-keeping map from Schwarzschild's table into `schwSpaceG`, for every mass,
  off the centre and off the rim. (For a positive mass this is only a check of the formula; the
  model for a positive mass is Kruskal's.)
* **A length-keeping map is a chart of the model** (`IsKruskalMapOn.mfderiv_injective`,
  `IsSchwarzschildMapOn.mfderiv_injective`): it carries no step to zero. In particular a map
  that does not move is never length-keeping (`IsKruskalMapOn.not_const`): Lean gives every map
  a derivative, zero where there is none, and this shows that the definition is not fooled.
* **The assumptions of `GlobalBirkhoff` can be met, and its conclusion then holds:**
  - `schwarzschild_meets_global`, `schwarzschild_global_conclusion`: Schwarzschild's table on a
    region `shellBox a b` (convex, so in one piece and without holes), for every mass;
    for a mass that is zero or negative the conclusion of `GlobalBirkhoff` holds there with
    the map above (`schwarzschild_global`).
  - `kruskal_meets_global`: Kruskal's table on `kruskalBox`, a convex region that contains
    points of the rim and of the sphere where the two rims cross, provided the known answers
    `KruskalIsSpaceTime`, `KruskalIsEmpty`, `KruskalIsRound` of `Goals/EveryPoint.lean` hold;
    `kruskalBox_conclusion`: the conclusion holds there with the wrapping map, unconditionally.
* **The symmetries named in `GlobalBirkhoffUnique` are symmetries** (`IsKruskalMapOn.sym`): a
  length-keeping map into Kruskal's, followed by such a symmetry, is again one. So the freedom
  that `GlobalBirkhoffUnique` leaves is really there.
* **The poles are really included** (`kruskal_map_reaches_pole`): a length-keeping map from
  Kruskal's table into Kruskal's whole space-time can reach a pole of the sphere.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

/-! ## The tables, read as formulas -/

/-- Kruskal's whole table, as a formula: `A · (-dT² + dX²) + r² · (dy₁² + dy₂² + dy₃²)`. -/
theorem kruskalWhole_apply (m : ℝ) (p u w : Coords 5) :
    tableMeasure (kruskalWhole m) p u w
      = kruskalA m (p 0) (p 1) * (-(u 0 * w 0) + u 1 * w 1)
        + kruskalS m (p 0) (p 1) * (u 2 * w 2 + u 3 * w 3 + u 4 * w 4) := by
  rw [show tableMeasure (kruskalWhole m) p u w = ∑ a, kruskalWholeDiag m a p * u a * w a from
    formOf_diag (fun a ↦ kruskalWholeDiag m a p) u w]
  simp only [Fin.sum_univ_five, kruskalWholeDiag, Matrix.cons_val]
  ring

/-- Kruskal's table of `Goals/EveryPoint.lean`, as a formula. -/
theorem kruskalG_apply (m : ℝ) (x v w : Coords 4) :
    tableMeasure (kruskalG m) x v w
      = kruskalA m (x 0) (x 1) * (-(v 0 * w 0) + v 1 * w 1)
        + kruskalS m (x 0) (x 1) * (v 2 * w 2 + sin (x 2) ^ 2 * (v 3 * w 3)) := by
  simp only [tableMeasure, formOf_apply, Fin.sum_univ_four, kruskalG, genG, sep2, gTR, gΘ]
  simp
  simp only [negA, zero2, constOne, sin2]
  ring

/-- Schwarzschild's table of distance and angles, as a formula. -/
theorem schw_apply (m : ℝ) (x v w : Coords 4) :
    tableMeasure (roundG (schwA m) (schwB m)) x v w
      = -schwA m (x 1) * (v 0 * w 0) + schwB m (x 1) * (v 1 * w 1) + x 1 ^ 2 * (v 2 * w 2)
        + x 1 ^ 2 * sin (x 2) ^ 2 * (v 3 * w 3) := by
  rw [round_measure_apply]
  simp [Fin.sum_univ_four, roundDiag, sep, gr, gθ, negF, sqF, sin2, constOne]
  ring

/-- Schwarzschild's table in ordinary space labels, as a formula. -/
theorem schwSpace_apply (m : ℝ) (z u w : Coords 4) :
    tableMeasure (schwSpaceG m) z u w
      = -schwA m (centreDist z) * (u 0 * w 0) + (u 1 * w 1 + u 2 * w 2 + u 3 * w 3)
        + 2 * m / (centreDist z ^ 2 * (centreDist z - 2 * m))
          * (z 1 * u 1 + z 2 * u 2 + z 3 * u 3) * (z 1 * w 1 + z 2 * w 2 + z 3 * w 3) := by
  simp only [tableMeasure, formOf_apply, Fin.sum_univ_four, schwSpaceG]
  simp
  ring

/-- For mass zero, Schwarzschild's table in ordinary space labels is flat space-time,
`-dt² + dx₁² + dx₂² + dx₃²`, at every point, the centre included. -/
theorem schwSpace_zero_apply (z u w : Coords 4) :
    tableMeasure (schwSpaceG 0) z u w = -(u 0 * w 0) + (u 1 * w 1 + u 2 * w 2 + u 3 * w 3) := by
  rw [schwSpace_apply]
  simp [schwA]

/-! ## A derivative read off part by part -/

theorem fderiv_pi_apply {n k : ℕ} {Φ : Coords n → Coords k} {x : Coords n}
    (h : DifferentiableAt ℝ Φ x) (v : Coords n) (i : Fin k) :
    fderiv ℝ Φ x v i = fderiv ℝ (fun y ↦ Φ y i) x v := by
  have h2 := (hasFDerivAt_pi'.mp h.hasFDerivAt) i
  rw [h2.fderiv]
  rfl

/-! ## Kruskal's table, wrapped round the sphere -/

/-- **Wrapping Kruskal's table round the unit sphere:** the two angles go to the point of the
unit sphere they describe. -/
noncomputable def kruskalWrap (x : Coords 4) : Coords 5 :=
  ![x 0, x 1, sin (x 2) * cos (x 3), sin (x 2) * sin (x 3), cos (x 2)]

theorem kruskalWrap_mem {x : Coords 4} (hx : -1 < x 1 ^ 2 - x 0 ^ 2) :
    kruskalWrap x ∈ kruskalSpace := by
  refine ⟨by simpa [kruskalWrap] using hx, ?_⟩
  simp only [kruskalWrap, Matrix.cons_val]
  have h1 := Real.sin_sq_add_cos_sq (x 2)
  have h2 := Real.sin_sq_add_cos_sq (x 3)
  linear_combination (sin (x 2) ^ 2) * h2 + h1

theorem contDiff_kruskalWrap : ContDiff ℝ ∞ kruskalWrap := by
  refine contDiff_pi.mpr fun i ↦ ?_
  have c : ∀ j : Fin 4, ContDiff ℝ ∞ (fun x : Coords 4 ↦ x j) :=
    fun j ↦ contDiff_apply ℝ (fun _ : Fin 4 ↦ ℝ) j
  fin_cases i
  · exact c 0
  · exact c 1
  · exact (Real.contDiff_sin.comp (c 2)).mul (Real.contDiff_cos.comp (c 3))
  · exact (Real.contDiff_sin.comp (c 2)).mul (Real.contDiff_sin.comp (c 3))
  · exact Real.contDiff_cos.comp (c 2)

theorem fderiv_kruskalWrap (x v : Coords 4) :
    fderiv ℝ kruskalWrap x v = ![v 0, v 1,
      cos (x 2) * cos (x 3) * v 2 - sin (x 2) * sin (x 3) * v 3,
      cos (x 2) * sin (x 3) * v 2 + sin (x 2) * cos (x 3) * v 3,
      -sin (x 2) * v 2] := by
  have hd : DifferentiableAt ℝ kruskalWrap x :=
    (contDiff_kruskalWrap.differentiable (by simp)).differentiableAt
  funext i
  rw [fderiv_pi_apply hd]
  have a0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) x
  have a1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 4) x
  have a2 := hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) x
  have a3 := hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) x
  fin_cases i
  · simp [kruskalWrap, a0.fderiv]
  · simp [kruskalWrap, a1.fderiv]
  · have e : HasFDerivAt (fun y : Coords 4 ↦ sin (y 2) * cos (y 3)) _ x := (a2.sin).mul (a3.cos)
    change fderiv ℝ (fun y : Coords 4 ↦ sin (y 2) * cos (y 3)) x v
      = cos (x 2) * cos (x 3) * v 2 - sin (x 2) * sin (x 3) * v 3
    rw [e.fderiv]
    simp
    ring
  · have e : HasFDerivAt (fun y : Coords 4 ↦ sin (y 2) * sin (y 3)) _ x := (a2.sin).mul (a3.sin)
    change fderiv ℝ (fun y : Coords 4 ↦ sin (y 2) * sin (y 3)) x v
      = cos (x 2) * sin (x 3) * v 2 + sin (x 2) * cos (x 3) * v 3
    rw [e.fderiv]
    simp
    ring
  · have e := a2.cos
    simp only [kruskalWrap] at e ⊢
    simp [e.fderiv]

/-- **Wrapping keeps lengths:** Kruskal's table of `Goals/EveryPoint.lean` is what Kruskal's
whole table gives for the wrapped steps, at every point (the poles included, where both sides
lose the step along the angle around the axis). -/
theorem kruskalWrap_pullback (m : ℝ) (x v w : Coords 4) :
    tableMeasure (kruskalG m) x v w
      = tableMeasure (kruskalWhole m) (kruskalWrap x) (fderiv ℝ kruskalWrap x v)
          (fderiv ℝ kruskalWrap x w) := by
  rw [kruskalG_apply, kruskalWhole_apply, fderiv_kruskalWrap, fderiv_kruskalWrap]
  simp only [kruskalWrap, Matrix.cons_val]
  have h1 := Real.sin_sq_add_cos_sq (x 2)
  have h2 := Real.sin_sq_add_cos_sq (x 3)
  linear_combination (-(kruskalS m (x 0) (x 1)) * v 2 * w 2 * cos (x 2) ^ 2
      - kruskalS m (x 0) (x 1) * v 3 * w 3 * sin (x 2) ^ 2) * h2
    - kruskalS m (x 0) (x 1) * v 2 * w 2 * h1

/-- **The pole-free Kruskal's is the shared Kruskal's.** On every open region away from the
centre, wrapping Kruskal's table round the sphere is a length-keeping map into Kruskal's whole
space-time. -/
theorem kruskalWrap_isKruskalMapOn (m : ℝ) {s : Set (Coords 4)} (hs : IsOpen s)
    (hsub : ∀ x ∈ s, -1 < x 1 ^ 2 - x 0 ^ 2) :
    IsKruskalMapOn m (flatMeasure (tableMeasure (kruskalG m))) kruskalWrap s := by
  refine ⟨hs, contDiff_kruskalWrap.contMDiff.contMDiffOn,
    fun q hq ↦ ⟨kruskalWrap_mem (hsub q hq), fun v w ↦ ?_⟩⟩
  rw [mfderiv_eq_fderiv]
  exact kruskalWrap_pullback m q v w

/-! ## Schwarzschild's table, in ordinary space labels -/

/-- **From distance and angles to ordinary space labels:**
`(t, r, θ, φ) ↦ (t, r sin θ cos φ, r sin θ sin φ, r cos θ)`. -/
noncomputable def sphericalToSpace (x : Coords 4) : Coords 4 :=
  ![x 0, x 1 * sin (x 2) * cos (x 3), x 1 * sin (x 2) * sin (x 3), x 1 * cos (x 2)]

theorem sphericalToSpace_sumSq (x : Coords 4) :
    sphericalToSpace x 1 ^ 2 + sphericalToSpace x 2 ^ 2 + sphericalToSpace x 3 ^ 2 = x 1 ^ 2 := by
  simp only [sphericalToSpace, Matrix.cons_val]
  have h1 := Real.sin_sq_add_cos_sq (x 2)
  have h2 := Real.sin_sq_add_cos_sq (x 3)
  linear_combination x 1 ^ 2 * sin (x 2) ^ 2 * h2 + x 1 ^ 2 * h1

theorem contDiff_sphericalToSpace : ContDiff ℝ ∞ sphericalToSpace := by
  refine contDiff_pi.mpr fun i ↦ ?_
  have c : ∀ j : Fin 4, ContDiff ℝ ∞ (fun x : Coords 4 ↦ x j) :=
    fun j ↦ contDiff_apply ℝ (fun _ : Fin 4 ↦ ℝ) j
  fin_cases i
  · exact c 0
  · exact ((c 1).mul (Real.contDiff_sin.comp (c 2))).mul (Real.contDiff_cos.comp (c 3))
  · exact ((c 1).mul (Real.contDiff_sin.comp (c 2))).mul (Real.contDiff_sin.comp (c 3))
  · exact (c 1).mul (Real.contDiff_cos.comp (c 2))

theorem fderiv_sphericalToSpace (x v : Coords 4) :
    fderiv ℝ sphericalToSpace x v = ![v 0,
      sin (x 2) * cos (x 3) * v 1 + x 1 * cos (x 2) * cos (x 3) * v 2
        - x 1 * sin (x 2) * sin (x 3) * v 3,
      sin (x 2) * sin (x 3) * v 1 + x 1 * cos (x 2) * sin (x 3) * v 2
        + x 1 * sin (x 2) * cos (x 3) * v 3,
      cos (x 2) * v 1 - x 1 * sin (x 2) * v 2] := by
  have hd : DifferentiableAt ℝ sphericalToSpace x :=
    (contDiff_sphericalToSpace.differentiable (by simp)).differentiableAt
  funext i
  rw [fderiv_pi_apply hd]
  have a0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) x
  have a1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 4) x
  have a2 := hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) x
  have a3 := hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) x
  fin_cases i
  · simp [sphericalToSpace, a0.fderiv]
  · have e : HasFDerivAt (fun y : Coords 4 ↦ y 1 * sin (y 2) * cos (y 3)) _ x :=
      (a1.mul a2.sin).mul a3.cos
    change fderiv ℝ (fun y : Coords 4 ↦ y 1 * sin (y 2) * cos (y 3)) x v
      = sin (x 2) * cos (x 3) * v 1 + x 1 * cos (x 2) * cos (x 3) * v 2
        - x 1 * sin (x 2) * sin (x 3) * v 3
    rw [e.fderiv]
    simp
    ring
  · have e : HasFDerivAt (fun y : Coords 4 ↦ y 1 * sin (y 2) * sin (y 3)) _ x :=
      (a1.mul a2.sin).mul a3.sin
    change fderiv ℝ (fun y : Coords 4 ↦ y 1 * sin (y 2) * sin (y 3)) x v
      = sin (x 2) * sin (x 3) * v 1 + x 1 * cos (x 2) * sin (x 3) * v 2
        + x 1 * sin (x 2) * cos (x 3) * v 3
    rw [e.fderiv]
    simp
    ring
  · have e : HasFDerivAt (fun y : Coords 4 ↦ y 1 * cos (y 2)) _ x := a1.mul a2.cos
    change fderiv ℝ (fun y : Coords 4 ↦ y 1 * cos (y 2)) x v
      = cos (x 2) * v 1 - x 1 * sin (x 2) * v 2
    rw [e.fderiv]
    simp
    ring

/-- **Schwarzschild's table is `schwSpaceG` in ordinary space labels,** off the centre and off
the rim, for every mass. -/
theorem sphericalToSpace_pullback (m : ℝ) {x : Coords 4} (hr : 0 < x 1) (hrim : x 1 ≠ 2 * m)
    (v w : Coords 4) :
    tableMeasure (roundG (schwA m) (schwB m)) x v w
      = tableMeasure (schwSpaceG m) (sphericalToSpace x) (fderiv ℝ sphericalToSpace x v)
          (fderiv ℝ sphericalToSpace x w) := by
  have hr0 : x 1 ≠ 0 := hr.ne'
  have hd : x 1 - 2 * m ≠ 0 := sub_ne_zero.mpr hrim
  have h1 := Real.sin_sq_add_cos_sq (x 2)
  have h2 := Real.sin_sq_add_cos_sq (x 3)
  have hρ : centreDist (sphericalToSpace x) = x 1 := by
    rw [centreDist, sphericalToSpace_sumSq, Real.sqrt_sq hr.le]
  have hB : schwB m (x 1) = 1 + 2 * m / (x 1 ^ 2 * (x 1 - 2 * m)) * x 1 ^ 2 := by
    rw [schwB, one_sub_div hr0, inv_div]
    field_simp
    ring
  have h0 : ∀ u : Coords 4, fderiv ℝ sphericalToSpace x u 0 = u 0 := fun u ↦ by
    rw [fderiv_sphericalToSpace]
    rfl
  have hdot : ∀ u : Coords 4,
      sphericalToSpace x 1 * fderiv ℝ sphericalToSpace x u 1
        + sphericalToSpace x 2 * fderiv ℝ sphericalToSpace x u 2
        + sphericalToSpace x 3 * fderiv ℝ sphericalToSpace x u 3 = x 1 * u 1 := fun u ↦ by
    rw [fderiv_sphericalToSpace]
    simp only [sphericalToSpace, Matrix.cons_val]
    linear_combination (x 1 * u 1 * sin (x 2) ^ 2 + x 1 ^ 2 * u 2 * sin (x 2) * cos (x 2)) * h2
      + x 1 * u 1 * h1
  have hsq : fderiv ℝ sphericalToSpace x v 1 * fderiv ℝ sphericalToSpace x w 1
      + fderiv ℝ sphericalToSpace x v 2 * fderiv ℝ sphericalToSpace x w 2
      + fderiv ℝ sphericalToSpace x v 3 * fderiv ℝ sphericalToSpace x w 3
      = v 1 * w 1 + x 1 ^ 2 * (v 2 * w 2) + x 1 ^ 2 * sin (x 2) ^ 2 * (v 3 * w 3) := by
    rw [fderiv_sphericalToSpace, fderiv_sphericalToSpace]
    simp only [Matrix.cons_val]
    linear_combination (v 1 * w 1 * sin (x 2) ^ 2 + v 2 * w 2 * x 1 ^ 2 * cos (x 2) ^ 2
        + v 3 * w 3 * x 1 ^ 2 * sin (x 2) ^ 2
        + (v 1 * w 2 + v 2 * w 1) * x 1 * sin (x 2) * cos (x 2)) * h2
      + (v 1 * w 1 + v 2 * w 2 * x 1 ^ 2) * h1
  rw [schw_apply, schwSpace_apply, hρ, h0 v, h0 w, hdot v, hdot w, hsq, hB]
  ring

/-- **Schwarzschild's table maps into `schwSpaceG` by `sphericalToSpace`,** keeping lengths, on
every open region off the centre and off the rim. -/
theorem sphericalToSpace_isSchwarzschildMapOn (m : ℝ) {s : Set (Coords 4)} (hs : IsOpen s)
    (hsub : ∀ x ∈ s, 0 < x 1 ∧ x 1 ≠ 2 * m) :
    IsSchwarzschildMapOn m (flatMeasure (tableMeasure (roundG (schwA m) (schwB m))))
      sphericalToSpace s := by
  refine ⟨hs, contDiff_sphericalToSpace.contMDiff.contMDiffOn,
    fun q hq ↦ ⟨Or.inr ?_, fun v w ↦ ?_⟩⟩
  · rw [sphericalToSpace_sumSq]
    exact pow_pos (hsub q hq).1 2
  · rw [mfderiv_eq_fderiv]
    exact sphericalToSpace_pullback m (hsub q hq).1 (hsub q hq).2 v w

/-! ## A length-keeping map carries no step to zero -/

section Injective

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  [IsManifold 𝓘(ℝ, Coords 4) ∞ M] {m : ℝ} {g : LengthMeasure 𝓘(ℝ, Coords 4) M} {s : Set M}

/-- **A length-keeping map into Kruskal's carries no step to zero,** where `g` is a space-time:
a step it carried to zero would be at right angles to every step. So near each point the map is
a chart of Kruskal's space-time. -/
theorem IsKruskalMapOn.mfderiv_injective {D : M → Coords 5} (hD : IsKruskalMapOn m g D s)
    (hg : IsSpaceTimeOn g s) {q : M} (hq : q ∈ s) :
    Function.Injective (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 5) D q) := by
  refine (injective_iff_map_eq_zero _).mpr fun v hv ↦ ?_
  refine hg.isLengthMeasureOn.nondegenerate q hq v fun w ↦ ?_
  change g q v w = 0
  rw [(hD.2.2 q hq).2 v w, hv]
  simp

/-- The same for a map into Schwarzschild's whole space-time. -/
theorem IsSchwarzschildMapOn.mfderiv_injective {D : M → Coords 4}
    (hD : IsSchwarzschildMapOn m g D s) (hg : IsSpaceTimeOn g s) {q : M} (hq : q ∈ s) :
    Function.Injective (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D q) := by
  refine (injective_iff_map_eq_zero _).mpr fun v hv ↦ ?_
  refine hg.isLengthMeasureOn.nondegenerate q hq v fun w ↦ ?_
  change g q v w = 0
  rw [(hD.2.2 q hq).2 v w, hv]
  simp

/-- **A map that does not move is never length-keeping,** on a region that is not empty where
`g` is a space-time. -/
theorem IsKruskalMapOn.not_const {p : Coords 5} (hD : IsKruskalMapOn m g (fun _ ↦ p) s)
    (hg : IsSpaceTimeOn g s) (hs : s.Nonempty) : False := by
  obtain ⟨q, hq⟩ := hs
  have hinj := hD.mfderiv_injective hg hq
  have h0 : mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 5) (fun _ : M ↦ p) q = 0 := mfderiv_const
  rw [h0] at hinj
  have h1 : (Pi.single 0 1 : Coords 4) = 0 := hinj (by simp)
  simpa using congrFun h1 0

end Injective

/-! ## The assumptions can be met -/

section Smaller

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem isSpaceTimeOn_sub {g : LengthMeasure I M} {s t : Set M} (h : IsSpaceTimeOn g s)
    (hts : t ⊆ s) : IsSpaceTimeOn g t where
  symm := fun x hx ↦ h.symm x (hts hx)
  oneTime := fun x hx ↦ h.oneTime x (hts hx)
  smooth := ContMDiffOn.mono h.smooth hts

theorem isEmptyOn_sub [FiniteDimensional ℝ E] {g : LengthMeasure I M} {s t : Set M}
    (h : IsEmptyOn g s) (ht : IsOpen t) (hts : t ⊆ s) : IsEmptyOn g t := by
  obtain ⟨cov, hc, hr⟩ := h
  exact ⟨cov, ⟨ht, hc.isConnection.mono hts, fun x hx ↦ hc.noTwist x (hts hx),
    fun x hx ↦ hc.keepsLengths x (hts hx)⟩, fun x hx ↦ hr x (hts hx)⟩

theorem isRoundOn_sub {g : LengthMeasure I M} {ξ : Fin 3 → Arrows I M} {s t : Set M}
    (h : IsRoundOn g ξ s) (ht : IsOpen t) (hts : t ⊆ s) : IsRoundOn g ξ t where
  isOpen := ht
  smooth := fun i ↦ (h.smooth i).mono hts
  unchanged := fun i x hx ↦ h.unchanged i x (hts hx)
  likeTurns := fun x hx ↦ h.likeTurns x (hts hx)
  surfaces := fun x hx ↦ h.surfaces x (hts hx)
  positive := fun x hx ↦ h.positive x (hts hx)

end Smaller

section Boxes

variable {n : ℕ}

theorem isOpen_coord_gt (i : Fin n) (r : ℝ) : IsOpen {x : Coords n | r < x i} :=
  isOpen_lt continuous_const (continuous_apply i)

theorem isOpen_coord_lt (i : Fin n) (r : ℝ) : IsOpen {x : Coords n | x i < r} :=
  isOpen_lt (continuous_apply i) continuous_const

theorem convex_coord_gt (i : Fin n) (r : ℝ) : Convex ℝ {x : Coords n | r < x i} :=
  convex_halfSpace_gt (f := fun x : Coords n ↦ x i) ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩ r

theorem convex_coord_lt (i : Fin n) (r : ℝ) : Convex ℝ {x : Coords n | x i < r} :=
  convex_halfSpace_lt (f := fun x : Coords n ↦ x i) ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩ r

/-- A convex region that is not empty is in one piece and has no holes. -/
theorem isSimplyConnected_of_convex {s : Set (Coords n)} (hc : Convex ℝ s) (hne : s.Nonempty) :
    IsSimplyConnected s := by
  have := hc.contractibleSpace hne
  change SimplyConnectedSpace s
  infer_instance

end Boxes

theorem isOpen_shellBox (a b : ℝ) : IsOpen (shellBox a b) :=
  (((isOpen_coord_gt 1 a).inter (isOpen_coord_lt 1 b)).inter (isOpen_coord_gt 2 0)).inter
    (isOpen_coord_lt 2 π)

theorem convex_shellBox (a b : ℝ) : Convex ℝ (shellBox a b) :=
  (((convex_coord_gt 1 a).inter (convex_coord_lt 1 b)).inter (convex_coord_gt 2 0)).inter
    (convex_coord_lt 2 π)

theorem shellBox_nonempty {a b : ℝ} (hab : a < b) : (shellBox a b).Nonempty := by
  refine ⟨![0, (a + b) / 2, π / 2, 0], ?_⟩
  simp only [shellBox, Set.mem_inter_iff, Set.mem_ofPred_eq, Matrix.cons_val]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> linarith [pi_pos]

theorem isSimplyConnected_shellBox {a b : ℝ} (hab : a < b) : IsSimplyConnected (shellBox a b) :=
  isSimplyConnected_of_convex (convex_shellBox a b) (shellBox_nonempty hab)

theorem shellBox_subset_outside {m a b : ℝ} (ha : 0 ≤ a) (hm : 2 * m ≤ a) :
    shellBox a b ⊆ outside m := fun x ⟨⟨⟨h1, _⟩, h3⟩, h4⟩ ↦ by
  have h1 : a < x 1 := h1
  exact ⟨by linarith, by linarith, (Real.sin_pos_of_pos_of_lt_pi h3 h4).ne'⟩

/-- **The assumptions of `GlobalBirkhoff` can be met,** for every mass: Schwarzschild's table on
`shellBox a b`, outside the rim, is a space-time, empty and round, and the region is open, in
one piece and without holes. -/
theorem schwarzschild_meets_global (m : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hm : 2 * m ≤ a) (hab : a < b) :
    IsOpen (shellBox a b) ∧ IsSimplyConnected (shellBox a b)
      ∧ IsSpaceTimeOn (flatMeasure (tableMeasure (roundG (schwA m) (schwB m)))) (shellBox a b)
      ∧ IsEmptyOn (flatMeasure (tableMeasure (roundG (schwA m) (schwB m)))) (shellBox a b)
      ∧ IsRoundOn (flatMeasure (tableMeasure (roundG (schwA m) (schwB m)))) turns
          (shellBox a b) :=
  ⟨isOpen_shellBox a b, isSimplyConnected_shellBox hab,
    isSpaceTimeOn_sub (schwarzschild_isSpaceTimeOn_outside m) (shellBox_subset_outside ha hm),
    isEmptyOn_sub (schwarzschild_isEmptyOn m) (isOpen_shellBox a b)
      (shellBox_subset_outside ha hm),
    isRoundOn_sub (schwarzschild_isRoundOn m) (isOpen_shellBox a b)
      (shellBox_subset_outside ha hm)⟩

/-- On the same region, Schwarzschild's table has a length-keeping map into `schwSpaceG`. -/
theorem schwarzschild_global_conclusion (m : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hm : 2 * m ≤ a) :
    IsSchwarzschildMapOn m (flatMeasure (tableMeasure (roundG (schwA m) (schwB m))))
      sphericalToSpace (shellBox a b) :=
  sphericalToSpace_isSchwarzschildMapOn m (isOpen_shellBox a b) fun _ hx ↦
    ⟨(shellBox_subset_outside ha hm hx).1, (shellBox_subset_outside ha hm hx).2.1.ne'⟩

/-- **For a mass that is zero or negative, `GlobalBirkhoff` holds on Schwarzschild's
`shellBox 0 b`:** all its assumptions, and its conclusion with the map `sphericalToSpace`. -/
theorem schwarzschild_global (m : ℝ) (hm : m ≤ 0) {b : ℝ} (hb : 0 < b) :
    (IsOpen (shellBox 0 b) ∧ IsSimplyConnected (shellBox 0 b)
      ∧ IsSpaceTimeOn (flatMeasure (tableMeasure (roundG (schwA m) (schwB m)))) (shellBox 0 b)
      ∧ IsEmptyOn (flatMeasure (tableMeasure (roundG (schwA m) (schwB m)))) (shellBox 0 b)
      ∧ IsRoundOn (flatMeasure (tableMeasure (roundG (schwA m) (schwB m)))) turns
          (shellBox 0 b))
    ∧ ∃ D : Coords 4 → Coords 4,
        IsSchwarzschildMapOn m (flatMeasure (tableMeasure (roundG (schwA m) (schwB m)))) D
          (shellBox 0 b) :=
  ⟨schwarzschild_meets_global m le_rfl (by linarith) hb,
    sphericalToSpace, schwarzschild_global_conclusion m le_rfl (by linarith)⟩

/-- A region of Kruskal's table that contains points of the rim and of the sphere where the two
rims cross: `-1/2 < T < 1/2`, any `X`, the pole angle strictly between `0` and `π`, any angle
around the axis. -/
def kruskalBox : Set (Coords 4) :=
  {x | -(1 / 2 : ℝ) < x 0} ∩ {x | x 0 < 1 / 2} ∩ {x | 0 < x 2} ∩ {x | x 2 < π}

theorem isOpen_kruskalBox : IsOpen kruskalBox :=
  (((isOpen_coord_gt 0 _).inter (isOpen_coord_lt 0 _)).inter (isOpen_coord_gt 2 0)).inter
    (isOpen_coord_lt 2 π)

theorem isSimplyConnected_kruskalBox : IsSimplyConnected kruskalBox := by
  refine isSimplyConnected_of_convex
    ((((convex_coord_gt 0 _).inter (convex_coord_lt 0 _)).inter (convex_coord_gt 2 0)).inter
      (convex_coord_lt 2 π)) ⟨![0, 0, π / 2, 0], ?_⟩
  simp only [kruskalBox, Set.mem_inter_iff, Set.mem_ofPred_eq, Matrix.cons_val]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> linarith [pi_pos]

/-- The box contains a point of the sphere where the two rims cross (`T = X = 0`), so points
where the size of the spheres is not a usable distance. -/
theorem crossing_mem_kruskalBox : (![0, 0, π / 2, 0] : Coords 4) ∈ kruskalBox := by
  simp only [kruskalBox, Set.mem_inter_iff, Set.mem_ofPred_eq, Matrix.cons_val]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> linarith [pi_pos]

theorem kruskalBox_subset : kruskalBox ⊆ kruskalRegion := fun x ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ ↦ by
  refine ⟨?_, (Real.sin_pos_of_pos_of_lt_pi h3 h4).ne'⟩
  have h1 : -(1 / 2 : ℝ) < x 0 := h1
  have h2 : x 0 < 1 / 2 := h2
  have : x 0 ^ 2 < 1 / 4 := by nlinarith
  nlinarith [sq_nonneg (x 1)]

/-- **The assumptions of `GlobalBirkhoff` can be met across the rim:** if Kruskal's table is a
space-time, empty and round on its region (the known answers of `Goals/EveryPoint.lean`), then
it meets every assumption of `GlobalBirkhoff` on `kruskalBox`, which contains points of the rim
and of the sphere where the two rims cross. -/
theorem kruskal_meets_global (hS : KruskalIsSpaceTime) (hE : KruskalIsEmpty) (hR : KruskalIsRound)
    (m : ℝ) (hm : 0 < m) :
    IsOpen kruskalBox ∧ IsSimplyConnected kruskalBox
      ∧ IsSpaceTimeOn (flatMeasure (tableMeasure (kruskalG m))) kruskalBox
      ∧ IsEmptyOn (flatMeasure (tableMeasure (kruskalG m))) kruskalBox
      ∧ IsRoundOn (flatMeasure (tableMeasure (kruskalG m))) turns kruskalBox :=
  ⟨isOpen_kruskalBox, isSimplyConnected_kruskalBox,
    isSpaceTimeOn_sub (hS m hm) kruskalBox_subset,
    isEmptyOn_sub (hE m hm) isOpen_kruskalBox kruskalBox_subset,
    isRoundOn_sub (hR m hm) isOpen_kruskalBox kruskalBox_subset⟩

/-- **The conclusion of `GlobalBirkhoff` holds on `kruskalBox`,** with the wrapping map, for every
positive mass (in fact for every mass), with no assumption. -/
theorem kruskalBox_conclusion (m : ℝ) :
    IsKruskalMapOn m (flatMeasure (tableMeasure (kruskalG m))) kruskalWrap kruskalBox :=
  kruskalWrap_isKruskalMapOn m isOpen_kruskalBox fun _ hx ↦ (kruskalBox_subset hx).1

/-! ## The symmetries of Kruskal's whole space-time keep lengths -/

theorem lightSign2_entries {L : Matrix (Fin 2) (Fin 2) ℝ}
    (hL : L.transpose * lightSign2 * L = lightSign2) :
    -(L 0 0 * L 0 0) + L 1 0 * L 1 0 = -1 ∧ -(L 0 0 * L 0 1) + L 1 0 * L 1 1 = 0
      ∧ -(L 0 1 * L 0 1) + L 1 1 * L 1 1 = 1 := by
  have e : ∀ i j, (L.transpose * lightSign2 * L) i j = lightSign2 i j := fun i j ↦ by rw [hL]
  have e00 := e 0 0
  have e01 := e 0 1
  have e11 := e 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, lightSign2] at e00 e01 e11
  exact ⟨by linarith, by linarith, by linarith⟩

theorem orthogonal_entries {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R.transpose * R = 1) :
    R 0 0 * R 0 0 + R 1 0 * R 1 0 + R 2 0 * R 2 0 = 1
      ∧ R 0 1 * R 0 1 + R 1 1 * R 1 1 + R 2 1 * R 2 1 = 1
      ∧ R 0 2 * R 0 2 + R 1 2 * R 1 2 + R 2 2 * R 2 2 = 1
      ∧ R 0 0 * R 0 1 + R 1 0 * R 1 1 + R 2 0 * R 2 1 = 0
      ∧ R 0 0 * R 0 2 + R 1 0 * R 1 2 + R 2 0 * R 2 2 = 0
      ∧ R 0 1 * R 0 2 + R 1 1 * R 1 2 + R 2 1 * R 2 2 = 0 := by
  have e : ∀ i j, (R.transpose * R) i j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j :=
    fun i j ↦ by rw [hR]
  have e00 := e 0 0
  have e11 := e 1 1
  have e22 := e 2 2
  have e01 := e 0 1
  have e02 := e 0 2
  have e12 := e 1 2
  simp [Matrix.mul_apply, Fin.sum_univ_three] at e00 e11 e22 e01 e02 e12
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

section Sym

variable {L : Matrix (Fin 2) (Fin 2) ℝ} {R : Matrix (Fin 3) (Fin 3) ℝ}

theorem kruskalSym_light (hL : L.transpose * lightSign2 * L = lightSign2) (p : Coords 5) :
    kruskalSym L R p 1 ^ 2 - kruskalSym L R p 0 ^ 2 = p 1 ^ 2 - p 0 ^ 2 := by
  obtain ⟨l00, l01, l11⟩ := lightSign2_entries hL
  simp only [kruskalSym, Matrix.cons_val]
  linear_combination p 0 ^ 2 * l00 + 2 * p 0 * p 1 * l01 + p 1 ^ 2 * l11

theorem kruskalSym_time (hL : L.transpose * lightSign2 * L = lightSign2) (u w : Coords 5) :
    -(kruskalSym L R u 0 * kruskalSym L R w 0) + kruskalSym L R u 1 * kruskalSym L R w 1
      = -(u 0 * w 0) + u 1 * w 1 := by
  obtain ⟨l00, l01, l11⟩ := lightSign2_entries hL
  simp only [kruskalSym, Matrix.cons_val]
  linear_combination u 0 * w 0 * l00 + (u 0 * w 1 + u 1 * w 0) * l01 + u 1 * w 1 * l11

theorem kruskalSym_sphere (hR : R.transpose * R = 1) (u w : Coords 5) :
    kruskalSym L R u 2 * kruskalSym L R w 2 + kruskalSym L R u 3 * kruskalSym L R w 3
        + kruskalSym L R u 4 * kruskalSym L R w 4
      = u 2 * w 2 + u 3 * w 3 + u 4 * w 4 := by
  obtain ⟨o00, o11, o22, o01, o02, o12⟩ := orthogonal_entries hR
  simp only [kruskalSym, Matrix.cons_val]
  linear_combination u 2 * w 2 * o00 + u 3 * w 3 * o11 + u 4 * w 4 * o22
    + (u 2 * w 3 + u 3 * w 2) * o01 + (u 2 * w 4 + u 4 * w 2) * o02
    + (u 3 * w 4 + u 4 * w 3) * o12

/-- **A symmetry carries Kruskal's whole space-time to itself.** -/
theorem kruskalSym_mem (hL : L.transpose * lightSign2 * L = lightSign2) (hR : R.transpose * R = 1)
    {p : Coords 5} (hp : p ∈ kruskalSpace) : kruskalSym L R p ∈ kruskalSpace := by
  refine ⟨by rw [kruskalSym_light hL]; exact hp.1, ?_⟩
  have h := kruskalSym_sphere (L := L) hR p p
  have hp2 := hp.2
  nlinarith [h, hp2]

/-- **A symmetry keeps Kruskal's lengths.** -/
theorem kruskalSym_measure (m : ℝ) (hL : L.transpose * lightSign2 * L = lightSign2)
    (hR : R.transpose * R = 1) (p u w : Coords 5) :
    tableMeasure (kruskalWhole m) (kruskalSym L R p) (kruskalSym L R u) (kruskalSym L R w)
      = tableMeasure (kruskalWhole m) p u w := by
  have hA : kruskalA m (kruskalSym L R p 0) (kruskalSym L R p 1) = kruskalA m (p 0) (p 1) := by
    unfold kruskalA
    rw [kruskalSym_light hL]
  have hS : kruskalS m (kruskalSym L R p 0) (kruskalSym L R p 1) = kruskalS m (p 0) (p 1) := by
    unfold kruskalS
    rw [kruskalSym_light hL]
  rw [kruskalWhole_apply, kruskalWhole_apply, hA, hS, kruskalSym_time hL, kruskalSym_sphere hR]

theorem contDiff_kruskalSym (L : Matrix (Fin 2) (Fin 2) ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) :
    ContDiff ℝ ∞ (kruskalSym L R) := by
  refine contDiff_pi.mpr fun i ↦ ?_
  have c : ∀ j : Fin 5, ContDiff ℝ ∞ (fun x : Coords 5 ↦ x j) :=
    fun j ↦ contDiff_apply ℝ (fun _ : Fin 5 ↦ ℝ) j
  fin_cases i
  · exact (contDiff_const.mul (c 0)).add (contDiff_const.mul (c 1))
  · exact (contDiff_const.mul (c 0)).add (contDiff_const.mul (c 1))
  · exact ((contDiff_const.mul (c 2)).add (contDiff_const.mul (c 3))).add
      (contDiff_const.mul (c 4))
  · exact ((contDiff_const.mul (c 2)).add (contDiff_const.mul (c 3))).add
      (contDiff_const.mul (c 4))
  · exact ((contDiff_const.mul (c 2)).add (contDiff_const.mul (c 3))).add
      (contDiff_const.mul (c 4))

theorem fderiv_kruskalSym (L : Matrix (Fin 2) (Fin 2) ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (p u : Coords 5) : fderiv ℝ (kruskalSym L R) p u = kruskalSym L R u := by
  have hd : DifferentiableAt ℝ (kruskalSym L R) p :=
    ((contDiff_kruskalSym L R).differentiable (by simp)).differentiableAt
  funext i
  rw [fderiv_pi_apply hd]
  have a : ∀ j : Fin 5, HasFDerivAt (fun q : Coords 5 ↦ q j) (ContinuousLinearMap.proj j) p :=
    fun j ↦ hasFDerivAt_apply (𝕜 := ℝ) j p
  fin_cases i
  · have e : HasFDerivAt (fun q : Coords 5 ↦ L 0 0 * q 0 + L 0 1 * q 1) _ p :=
      ((a 0).const_mul (L 0 0)).add ((a 1).const_mul (L 0 1))
    change fderiv ℝ (fun q : Coords 5 ↦ L 0 0 * q 0 + L 0 1 * q 1) p u = L 0 0 * u 0 + L 0 1 * u 1
    rw [e.fderiv]
    simp
  · have e : HasFDerivAt (fun q : Coords 5 ↦ L 1 0 * q 0 + L 1 1 * q 1) _ p :=
      ((a 0).const_mul (L 1 0)).add ((a 1).const_mul (L 1 1))
    change fderiv ℝ (fun q : Coords 5 ↦ L 1 0 * q 0 + L 1 1 * q 1) p u = L 1 0 * u 0 + L 1 1 * u 1
    rw [e.fderiv]
    simp
  · have e : HasFDerivAt (fun q : Coords 5 ↦ R 0 0 * q 2 + R 0 1 * q 3 + R 0 2 * q 4) _ p :=
      (((a 2).const_mul (R 0 0)).add ((a 3).const_mul (R 0 1))).add ((a 4).const_mul (R 0 2))
    change fderiv ℝ (fun q : Coords 5 ↦ R 0 0 * q 2 + R 0 1 * q 3 + R 0 2 * q 4) p u
      = R 0 0 * u 2 + R 0 1 * u 3 + R 0 2 * u 4
    rw [e.fderiv]
    simp
  · have e : HasFDerivAt (fun q : Coords 5 ↦ R 1 0 * q 2 + R 1 1 * q 3 + R 1 2 * q 4) _ p :=
      (((a 2).const_mul (R 1 0)).add ((a 3).const_mul (R 1 1))).add ((a 4).const_mul (R 1 2))
    change fderiv ℝ (fun q : Coords 5 ↦ R 1 0 * q 2 + R 1 1 * q 3 + R 1 2 * q 4) p u
      = R 1 0 * u 2 + R 1 1 * u 3 + R 1 2 * u 4
    rw [e.fderiv]
    simp
  · have e : HasFDerivAt (fun q : Coords 5 ↦ R 2 0 * q 2 + R 2 1 * q 3 + R 2 2 * q 4) _ p :=
      (((a 2).const_mul (R 2 0)).add ((a 3).const_mul (R 2 1))).add ((a 4).const_mul (R 2 2))
    change fderiv ℝ (fun q : Coords 5 ↦ R 2 0 * q 2 + R 2 1 * q 3 + R 2 2 * q 4) p u
      = R 2 0 * u 2 + R 2 1 * u 3 + R 2 2 * u 4
    rw [e.fderiv]
    simp

/-- **A length-keeping map into Kruskal's, followed by a symmetry of Kruskal's, is again a
length-keeping map into Kruskal's.** So the freedom that `GlobalBirkhoffUnique` leaves is really
there, and that statement cannot ask for more. -/
theorem IsKruskalMapOn.sym {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M] {m : ℝ} {g : LengthMeasure 𝓘(ℝ, Coords 4) M}
    {D : M → Coords 5} {s : Set M} (hD : IsKruskalMapOn m g D s)
    (hL : L.transpose * lightSign2 * L = lightSign2) (hR : R.transpose * R = 1) :
    IsKruskalMapOn m g (fun q ↦ kruskalSym L R (D q)) s := by
  obtain ⟨hs, hsm, hpt⟩ := hD
  refine ⟨hs, (contDiff_kruskalSym L R).contMDiff.comp_contMDiffOn hsm,
    fun q hq ↦ ⟨kruskalSym_mem hL hR (hpt q hq).1, fun v w ↦ ?_⟩⟩
  have hDq : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 5) D q :=
    (hsm.contMDiffAt (hs.mem_nhds hq)).mdifferentiableAt (by simp)
  have hΦ : MDifferentiableAt 𝓘(ℝ, Coords 5) 𝓘(ℝ, Coords 5) (kruskalSym L R) (D q) :=
    ((contDiff_kruskalSym L R).contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  have key : ∀ a b : Coords 5,
      tableMeasure (kruskalWhole m) (kruskalSym L R (D q)) (fderiv ℝ (kruskalSym L R) (D q) a)
        (fderiv ℝ (kruskalSym L R) (D q) b) = tableMeasure (kruskalWhole m) (D q) a b :=
    fun a b ↦ by
      rw [fderiv_kruskalSym, fderiv_kruskalSym]
      exact kruskalSym_measure m hL hR (D q) a b
  change g q v w = flatMeasure (tableMeasure (kruskalWhole m)) (kruskalSym L R (D q))
    (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 5) (kruskalSym L R ∘ D) q v)
    (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 5) (kruskalSym L R ∘ D) q w)
  rw [mfderiv_comp_apply q hΦ hDq v, mfderiv_comp_apply q hΦ hDq w, mfderiv_eq_fderiv,
    (hpt q hq).2 v w]
  exact (key _ _).symm

end Sym

/-- The turn of the sphere that takes the point `(1, 0, 0)` of the equator to the pole
`(0, 0, 1)`. -/
def turnToPole : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, -1; 0, 1, 0; 1, 0, 0]

/-- **The poles are really included.** A length-keeping map from Kruskal's table on
`kruskalBox` into Kruskal's whole space-time reaches the pole `y = (0, 0, 1)` of the sphere, at
the sphere where the two rims cross: wrap round the sphere, then turn the sphere. -/
theorem kruskal_map_reaches_pole (m : ℝ) :
    ∃ D : Coords 4 → Coords 5,
      IsKruskalMapOn m (flatMeasure (tableMeasure (kruskalG m))) D kruskalBox ∧
        ∃ q ∈ kruskalBox, D q = ![0, 0, 0, 0, 1] := by
  refine ⟨fun q ↦ kruskalSym 1 turnToPole (kruskalWrap q), (kruskalBox_conclusion m).sym ?_ ?_,
    ![0, 0, π / 2, 0], crossing_mem_kruskalBox, ?_⟩
  · simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [turnToPole, Matrix.mul_apply, Fin.sum_univ_three]
  · funext i
    fin_cases i <;> simp [kruskalSym, kruskalWrap, turnToPole]

end GravityInLean.Curved
