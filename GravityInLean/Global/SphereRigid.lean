/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.Checks
public import GravityInLean.Global.UniqueFlat
public import GravityInLean.SlopeRules
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.LinearAlgebra.Matrix.ToLin

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# A map of the two angles that keeps the lengths of the sphere is a turn or mirror of the sphere

Board item `task:global-sphere-rigid`. The result `sphere_rigid`: a smooth map of the two angles
that keeps the length `dθ² + sin² θ dφ²` of the unit sphere is, near every point, one fixed turn
or mirror of the sphere.

No new analysis is done here. The statement is reduced to the uniqueness of length-keeping maps
into flat space-time (`unique_flat` of `Global/UniqueFlat.lean`; the steps before the last take
it as the assumption `FlatUnique`, so that they do not depend on how it is proved):

* flat space-time in distance and angles is `-dt² + dr² + r² (dθ² + sin² θ dφ²)`
  (Schwarzschild's table of mass zero), and `sphericalToSpace` maps it to flat space-time in
  ordinary labels, keeping lengths;
* the map `angleMap f : (t, r, θ, φ) ↦ (t, r, θ', φ')`, with the new angles of `f`, keeps that
  table (`angleMap_pullback`), so `sphericalToSpace` after it is a second length-keeping map;
* so the two differ by a Lorentz transformation `Λ` and a shift, on a ball around the point;
* comparing what the two maps do to the step straight away from the centre shows that the point
  of the sphere with the new angles is the space part of `Λ` applied to the point with the old
  angles; comparing the time parts shows that the space part of `Λ` is a turn or mirror.

The distance label must be positive for this, so the map is first shifted along the distance
label (`sphere_rigid_of_flat` from `sphere_rigid_pos`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

/-! ## Plain algebra with lists of three and four numbers -/

/-- A table of four by four numbers applied to a list of four numbers, written out. -/
theorem mulVec_four (Λ : Matrix (Fin 4) (Fin 4) ℝ) (u : Fin 4 → ℝ) (i : Fin 4) :
    Λ.mulVec u i = Λ i 0 * u 0 + Λ i 1 * u 1 + Λ i 2 * u 2 + Λ i 3 * u 3 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- A table of three by three numbers applied to a list of three numbers, written out. -/
theorem mulVec_three (R : Matrix (Fin 3) (Fin 3) ℝ) (u : Fin 3 → ℝ) (i : Fin 3) :
    R.mulVec u i = R i 0 * u 0 + R i 1 * u 1 + R i 2 * u 2 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The signs of `-t² + x₁² + x₂² + x₃²`, entry by entry. -/
theorem lightSign4_apply (j k : Fin 4) :
    lightSign4 j k = if j = k then (if j = 0 then -1 else 1) else 0 := by
  fin_cases j <;> fin_cases k <;> simp [lightSign4]

/-- What it means for a table `Λ` to keep `-t² + x₁² + x₂² + x₃²`, entry by entry. -/
theorem lightSign4_entry {Λ : Matrix (Fin 4) (Fin 4) ℝ}
    (hΛ : Λ.transpose * lightSign4 * Λ = lightSign4) (j k : Fin 4) :
    -(Λ 0 j * Λ 0 k) + Λ 1 j * Λ 1 k + Λ 2 j * Λ 2 k + Λ 3 j * Λ 3 k
      = if j = k then (if j = 0 then -1 else 1) else 0 := by
  have e : (Λ.transpose * lightSign4 * Λ) j k
      = -(Λ 0 j * Λ 0 k) + Λ 1 j * Λ 1 k + Λ 2 j * Λ 2 k + Λ 3 j * Λ 3 k := by
    simp [lightSign4, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_four]
  rw [← e, hΛ, lightSign4_apply]

/-- A table of four by four numbers, as a linear map of lists of four numbers. -/
noncomputable def mulVecCLM (Λ : Matrix (Fin 4) (Fin 4) ℝ) : Coords 4 →L[ℝ] Coords 4 :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin Λ)

theorem mulVecCLM_apply (Λ : Matrix (Fin 4) (Fin 4) ℝ) (u : Coords 4) :
    mulVecCLM Λ u = Λ.mulVec u := rfl

/-! ## The slope of a map, part by part -/

/-- What the slope of a map makes of a step, in one part: the sum over the four parts of the
step of the rate of change along that part. -/
theorem fderiv_apply_four {f : Coords 4 → Coords 4} {x : Coords 4}
    (hf : DifferentiableAt ℝ f x) (v : Coords 4) (α : Fin 4) :
    fderiv ℝ f x v α
      = jac f α 0 x * v 0 + jac f α 1 x * v 1 + jac f α 2 x * v 2 + jac f α 3 x * v 3 := by
  have h := clm_apply_eq_sum
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 ↦ ℝ) α).comp (fderiv ℝ f x)) v
  rw [Fin.sum_univ_four] at h
  have h' : fderiv ℝ f x v α
      = v 0 * fderiv ℝ f x (Pi.single 0 1) α + v 1 * fderiv ℝ f x (Pi.single 1 1) α
        + v 2 * fderiv ℝ f x (Pi.single 2 1) α + v 3 * fderiv ℝ f x (Pi.single 3 1) α := h
  rw [jac_eq_fderiv hf α 0, jac_eq_fderiv hf α 1, jac_eq_fderiv hf α 2, jac_eq_fderiv hf α 3, h']
  ring

/-- The slope of `sphericalToSpace` along the step straight away from the centre: the point of
the unit sphere that the two angles describe. -/
theorem fderiv_sphericalToSpace_radial (y : Coords 4) :
    fderiv ℝ sphericalToSpace y (Pi.single 1 1)
      = ![0, sin (y 2) * cos (y 3), sin (y 2) * sin (y 3), cos (y 2)] := by
  rw [fderiv_sphericalToSpace]
  simp

/-! ## The map of the angles, with time and distance left alone -/

/-- Time and distance stay, the two angles are those of `f`. -/
noncomputable def angleMap (f : Coords 4 → Coords 4) (x : Coords 4) : Coords 4 :=
  ![x 0, x 1, f x 2, f x 3]

/-- The map `angleMap f` is smooth where `f` is. -/
theorem contDiffOn_angleMap {f : Coords 4 → Coords 4} {W : Set (Coords 4)}
    (hf : ContDiffOn ℝ ∞ f W) : ContDiffOn ℝ ∞ (angleMap f) W := by
  refine contDiffOn_pi.mpr fun i ↦ ?_
  have c : ∀ j : Fin 4, ContDiffOn ℝ ∞ (fun x : Coords 4 ↦ x j) W :=
    fun j ↦ (contDiff_apply ℝ (fun _ : Fin 4 ↦ ℝ) j).contDiffOn
  have d : ∀ j : Fin 4, ContDiffOn ℝ ∞ (fun x : Coords 4 ↦ f x j) W :=
    fun j ↦ contDiffOn_pi.mp hf j
  fin_cases i
  · exact c 0
  · exact c 1
  · exact d 2
  · exact d 3

/-- The slope of `angleMap f`: the first two parts of a step stay, the last two are those that
the slope of `f` gives. -/
theorem hasFDerivAt_angleMap {f : Coords 4 → Coords 4} {x : Coords 4}
    (hf : DifferentiableAt ℝ f x) :
    HasFDerivAt (angleMap f) (ContinuousLinearMap.pi ![coordL 0, coordL 1,
      (coordL 2).comp (fderiv ℝ f x), (coordL 3).comp (fderiv ℝ f x)]) x := by
  refine (hasFDerivAt_pi (φ := fun i y ↦ angleMap f y i)
    (φ' := ![coordL 0, coordL 1, (coordL 2).comp (fderiv ℝ f x),
      (coordL 3).comp (fderiv ℝ f x)])).2 fun i ↦ ?_
  fin_cases i
  · exact (coordL (n := 4) 0).hasFDerivAt
  · exact (coordL (n := 4) 1).hasFDerivAt
  · exact (coordL (n := 4) 2).hasFDerivAt.comp x hf.hasFDerivAt
  · exact (coordL (n := 4) 3).hasFDerivAt.comp x hf.hasFDerivAt

/-- The slope of `angleMap f`, applied to a step. -/
theorem fderiv_angleMap {f : Coords 4 → Coords 4} {x : Coords 4} (hf : DifferentiableAt ℝ f x)
    (v : Coords 4) :
    fderiv ℝ (angleMap f) x v = ![v 0, v 1, fderiv ℝ f x v 2, fderiv ℝ f x v 3] := by
  rw [(hasFDerivAt_angleMap hf).fderiv]
  funext i
  fin_cases i <;> rfl

/-- **The map of the angles keeps the flat table in distance and angles.** If the new angles of
`f` do not change with time and distance, and the length `dθ² + sin² θ dφ²` of steps along the
angles is kept, then `angleMap f` keeps `-dt² + dr² + r² (dθ² + sin² θ dφ²)`. -/
theorem angleMap_pullback {f : Coords 4 → Coords 4} {x : Coords 4} (hf : DifferentiableAt ℝ f x)
    (hsplit : jac f 2 0 x = 0 ∧ jac f 2 1 x = 0 ∧ jac f 3 0 x = 0 ∧ jac f 3 1 x = 0)
    (hkeep : ∀ i j : Fin 4, 2 ≤ i.val → 2 ≤ j.val →
      jac f 2 i x * jac f 2 j x + sin (f x 2) ^ 2 * (jac f 3 i x * jac f 3 j x)
        = if i = j then (if i = 2 then 1 else sin (x 2) ^ 2) else 0)
    (v w : Coords 4) :
    tableMeasure (roundG (schwA 0) (schwB 0)) x v w
      = tableMeasure (roundG (schwA 0) (schwB 0)) (angleMap f x) (fderiv ℝ (angleMap f) x v)
          (fderiv ℝ (angleMap f) x w) := by
  obtain ⟨s20, s21, s30, s31⟩ := hsplit
  have k22 : jac f 2 2 x * jac f 2 2 x + sin (f x 2) ^ 2 * (jac f 3 2 x * jac f 3 2 x) = 1 := by
    have h := hkeep 2 2 (by decide) (by decide)
    rwa [ite_eq_left rfl, ite_eq_left rfl] at h
  have k33 : jac f 2 3 x * jac f 2 3 x + sin (f x 2) ^ 2 * (jac f 3 3 x * jac f 3 3 x)
      = sin (x 2) ^ 2 := by
    have h := hkeep 3 3 (by decide) (by decide)
    rwa [ite_eq_left rfl, ite_eq_right (by decide)] at h
  have k23 : jac f 2 2 x * jac f 2 3 x + sin (f x 2) ^ 2 * (jac f 3 2 x * jac f 3 3 x) = 0 := by
    have h := hkeep 2 3 (by decide) (by decide)
    rwa [ite_eq_right (by decide)] at h
  have e2 : ∀ u : Coords 4, fderiv ℝ f x u 2 = jac f 2 2 x * u 2 + jac f 2 3 x * u 3 := fun u ↦ by
    rw [fderiv_apply_four hf, s20, s21]
    ring
  have e3 : ∀ u : Coords 4, fderiv ℝ f x u 3 = jac f 3 2 x * u 2 + jac f 3 3 x * u 3 := fun u ↦ by
    rw [fderiv_apply_four hf, s30, s31]
    ring
  have hA : schwA 0 (x 1) = 1 := by simp [schwA]
  have hB : schwB 0 (x 1) = 1 := by simp [schwB]
  have p1 : angleMap f x 1 = x 1 := rfl
  have p2 : angleMap f x 2 = f x 2 := rfl
  have q0 : ∀ u : Coords 4, fderiv ℝ (angleMap f) x u 0 = u 0 := fun u ↦ by
    rw [fderiv_angleMap hf]
    rfl
  have q1 : ∀ u : Coords 4, fderiv ℝ (angleMap f) x u 1 = u 1 := fun u ↦ by
    rw [fderiv_angleMap hf]
    rfl
  have q2 : ∀ u : Coords 4,
      fderiv ℝ (angleMap f) x u 2 = jac f 2 2 x * u 2 + jac f 2 3 x * u 3 := fun u ↦ by
    rw [fderiv_angleMap hf, ← e2 u]
    rfl
  have q3 : ∀ u : Coords 4,
      fderiv ℝ (angleMap f) x u 3 = jac f 3 2 x * u 2 + jac f 3 3 x * u 3 := fun u ↦ by
    rw [fderiv_angleMap hf, ← e3 u]
    rfl
  rw [schw_apply, schw_apply, p1, p2, hA, hB, q0 v, q0 w, q1 v, q1 w, q2 v, q2 w, q3 v, q3 w]
  linear_combination (-(x 1 ^ 2) * (v 2 * w 2)) * k22 + (-(x 1 ^ 2) * (v 3 * w 3)) * k33
    + (-(x 1 ^ 2) * (v 2 * w 3 + v 3 * w 2)) * k23

/-! ## From flat space-time to the sphere -/

/-- **The assumption this file rests on:** two length-keeping maps from a region in one piece of
coordinate space into flat space-time differ by a Lorentz transformation and a shift. (This is
`unique_flat`, for coordinate space.) -/
def FlatUnique : Prop :=
  ∀ (g : LengthMeasure 𝓘(ℝ, Coords 4) (Coords 4)) (s : Set (Coords 4)),
    IsPreconnected s → IsSpaceTimeOn g s → ∀ D D' : Coords 4 → Coords 4,
    IsSchwarzschildMapOn 0 g D s → IsSchwarzschildMapOn 0 g D' s →
    ∃ (Λ : Matrix (Fin 4) (Fin 4) ℝ) (b : Coords 4),
      Λ.transpose * lightSign4 * Λ = lightSign4 ∧ ∀ q ∈ s, D' q = Λ.mulVec (D q) + b

/-- **The result where the distance label is positive.** As `sphere_rigid`, at a point `x₀` with
`0 < x₀ 1`, given the uniqueness of length-keeping maps into flat space-time. -/
theorem sphere_rigid_pos (hflat : FlatUnique) {f : Coords 4 → Coords 4} {W : Set (Coords 4)}
    {x₀ : Coords 4} (hW : IsOpen W) (hx₀ : x₀ ∈ W) (hpos : 0 < x₀ 1) (hf : ContDiffOn ℝ ∞ f W)
    (hsin : ∀ x ∈ W, sin (x 2) ≠ 0 ∧ sin (f x 2) ≠ 0)
    (hsplit : ∀ x ∈ W, jac f 2 0 x = 0 ∧ jac f 2 1 x = 0 ∧ jac f 3 0 x = 0 ∧ jac f 3 1 x = 0)
    (hkeep : ∀ x ∈ W, ∀ i j : Fin 4, 2 ≤ i.val → 2 ≤ j.val →
      jac f 2 i x * jac f 2 j x + sin (f x 2) ^ 2 * (jac f 3 i x * jac f 3 j x)
        = if i = j then (if i = 2 then 1 else sin (x 2) ^ 2) else 0) :
    ∃ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 ∧ ∀ᶠ x in 𝓝 x₀,
      (![sin (f x 2) * cos (f x 3), sin (f x 2) * sin (f x 3), cos (f x 2)] : Fin 3 → ℝ)
        = R.mulVec ![sin (x 2) * cos (x 3), sin (x 2) * sin (x 3), cos (x 2)] := by
  -- a ball around the point, inside `W`, on which the distance label is positive
  have hW' : W ∩ {x : Coords 4 | 0 < x 1} ∈ 𝓝 x₀ :=
    (hW.inter (isOpen_coord_gt 1 0)).mem_nhds ⟨hx₀, hpos⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hW'
  have hBW : Metric.ball x₀ ε ⊆ W := fun x hx ↦ (hball hx).1
  have hBpos : ∀ x ∈ Metric.ball x₀ ε, 0 < x 1 := fun x hx ↦ (hball hx).2
  have hBo : IsOpen (Metric.ball x₀ ε) := Metric.isOpen_ball
  have hBpre : IsPreconnected (Metric.ball x₀ ε) := (convex_ball x₀ ε).isPreconnected
  have hx₀B : x₀ ∈ Metric.ball x₀ ε := Metric.mem_ball_self hε
  have hfd : ∀ x ∈ Metric.ball x₀ ε, DifferentiableAt ℝ f x := fun x hx ↦
    (hf.contDiffAt (hW.mem_nhds (hBW hx))).differentiableAt (by simp)
  have hhd : ∀ x ∈ Metric.ball x₀ ε, DifferentiableAt ℝ (angleMap f) x := fun x hx ↦
    (hasFDerivAt_angleMap (hfd x hx)).differentiableAt
  have hSd : ∀ y : Coords 4, DifferentiableAt ℝ sphericalToSpace y := fun y ↦
    (contDiff_sphericalToSpace.differentiable (by simp)).differentiableAt
  -- the flat table in distance and angles is a space-time on the ball
  have hg : IsSpaceTimeOn (flatMeasure (tableMeasure (roundG (schwA 0) (schwB 0))))
      (Metric.ball x₀ ε) :=
    isSpaceTimeOn_sub (schwarzschild_isSpaceTimeOn_outside 0) fun x hx ↦
      ⟨hBpos x hx, by rw [mul_zero]; exact hBpos x hx, (hsin x (hBW hx)).1⟩
  -- two length-keeping maps into flat space-time
  have hD : IsSchwarzschildMapOn 0 (flatMeasure (tableMeasure (roundG (schwA 0) (schwB 0))))
      sphericalToSpace (Metric.ball x₀ ε) :=
    sphericalToSpace_isSchwarzschildMapOn 0 hBo fun x hx ↦
      ⟨hBpos x hx, by rw [mul_zero]; exact (hBpos x hx).ne'⟩
  have hD' : IsSchwarzschildMapOn 0 (flatMeasure (tableMeasure (roundG (schwA 0) (schwB 0))))
      (sphericalToSpace ∘ angleMap f) (Metric.ball x₀ ε) := by
    refine ⟨hBo, (contDiff_sphericalToSpace.comp_contDiffOn
      ((contDiffOn_angleMap hf).mono hBW)).contMDiffOn, fun q hq ↦ ⟨Or.inl rfl, fun v w ↦ ?_⟩⟩
    have hq1 : angleMap f q 1 = q 1 := rfl
    rw [mfderiv_eq_fderiv, fderiv_comp q (hSd _) (hhd q hq)]
    change tableMeasure (roundG (schwA 0) (schwB 0)) q v w
      = tableMeasure (schwSpaceG 0) (sphericalToSpace (angleMap f q))
          (fderiv ℝ sphericalToSpace (angleMap f q) (fderiv ℝ (angleMap f) q v))
          (fderiv ℝ sphericalToSpace (angleMap f q) (fderiv ℝ (angleMap f) q w))
    rw [← sphericalToSpace_pullback 0 (x := angleMap f q) (by rw [hq1]; exact hBpos q hq)
      (by rw [hq1, mul_zero]; exact (hBpos q hq).ne')]
    exact angleMap_pullback (hfd q hq) (hsplit q (hBW hq)) (hkeep q (hBW hq)) v w
  -- so they differ by a Lorentz transformation and a shift
  obtain ⟨Λ, b, hΛ, hEq⟩ := hflat _ _ hBpre hg _ _ hD hD'
  -- the same for the steps: the shift drops out
  have hstar : ∀ q ∈ Metric.ball x₀ ε, ∀ v : Coords 4,
      fderiv ℝ sphericalToSpace (angleMap f q) (fderiv ℝ (angleMap f) q v)
        = Λ.mulVec (fderiv ℝ sphericalToSpace q v) := by
    intro q hq v
    have hev : (sphericalToSpace ∘ angleMap f)
        =ᶠ[𝓝 q] fun y ↦ mulVecCLM Λ (sphericalToSpace y) + b :=
      Filter.eventuallyEq_of_mem (hBo.mem_nhds hq) hEq
    have h1 : fderiv ℝ (sphericalToSpace ∘ angleMap f) q
        = (fderiv ℝ sphericalToSpace (angleMap f q)).comp (fderiv ℝ (angleMap f) q) :=
      fderiv_comp q (hSd _) (hhd q hq)
    have h2 : HasFDerivAt (fun y ↦ mulVecCLM Λ (sphericalToSpace y) + b)
        ((mulVecCLM Λ).comp (fderiv ℝ sphericalToSpace q)) q :=
      ((mulVecCLM Λ).hasFDerivAt.comp q (hSd q).hasFDerivAt).add_const b
    have h3 : (fderiv ℝ sphericalToSpace (angleMap f q)).comp (fderiv ℝ (angleMap f) q)
        = (mulVecCLM Λ).comp (fderiv ℝ sphericalToSpace q) := by
      rw [← h1, ← h2.fderiv]
      exact hev.fderiv_eq
    exact congrArg (fun A : Coords 4 →L[ℝ] Coords 4 ↦ A v) h3
  -- the step straight away from the centre stays what it is under `angleMap f`
  have hrad : ∀ q ∈ Metric.ball x₀ ε,
      fderiv ℝ (angleMap f) q (Pi.single 1 1) = Pi.single 1 1 := by
    intro q hq
    obtain ⟨-, s21, -, s31⟩ := hsplit q (hBW hq)
    rw [fderiv_angleMap (hfd q hq), ← jac_eq_fderiv (hfd q hq) 2 1,
      ← jac_eq_fderiv (hfd q hq) 3 1, s21, s31]
    funext i
    fin_cases i <;> simp
  -- so the point of the sphere with the new angles is `Λ` applied to the point with the old
  have hrot : ∀ q ∈ Metric.ball x₀ ε,
      (![0, sin (f q 2) * cos (f q 3), sin (f q 2) * sin (f q 3), cos (f q 2)] : Fin 4 → ℝ)
        = Λ.mulVec ![0, sin (q 2) * cos (q 3), sin (q 2) * sin (q 3), cos (q 2)] := by
    intro q hq
    have h := hstar q hq (Pi.single 1 1)
    rw [hrad q hq, fderiv_sphericalToSpace_radial, fderiv_sphericalToSpace_radial] at h
    exact h
  -- the time part of `Λ` applied to any list is the time part of the list
  have hrow : ∀ u : Coords 4, Λ.mulVec u 0 = u 0 := by
    intro u
    have hinj : Function.Injective (fderiv ℝ sphericalToSpace x₀) := by
      have h := hD.mfderiv_injective hg hx₀B
      rwa [mfderiv_eq_fderiv] at h
    obtain ⟨v, hv⟩ := LinearMap.surjective_of_injective
      (f := (fderiv ℝ sphericalToSpace x₀ : Coords 4 →ₗ[ℝ] Coords 4)) hinj u
    have hv' : fderiv ℝ sphericalToSpace x₀ v = u := hv
    have h := congrFun (hstar x₀ hx₀B v) 0
    have e1 : fderiv ℝ sphericalToSpace (angleMap f x₀) (fderiv ℝ (angleMap f) x₀ v) 0 = v 0 := by
      rw [fderiv_sphericalToSpace, fderiv_angleMap (hfd x₀ hx₀B)]
      rfl
    have e2 : u 0 = v 0 := by
      rw [← hv', fderiv_sphericalToSpace]
      rfl
    rw [e1, hv'] at h
    rw [e2]
    exact h.symm
  have r1 : Λ 0 1 = 0 := by
    have h := hrow (Pi.single 1 1)
    rw [mulVec_four] at h
    simpa [Pi.single_apply] using h
  have r2 : Λ 0 2 = 0 := by
    have h := hrow (Pi.single 2 1)
    rw [mulVec_four] at h
    simpa [Pi.single_apply] using h
  have r3 : Λ 0 3 = 0 := by
    have h := hrow (Pi.single 3 1)
    rw [mulVec_four] at h
    simpa [Pi.single_apply] using h
  -- so the space part of `Λ` is a turn or mirror
  have E11 : Λ 1 1 * Λ 1 1 + Λ 2 1 * Λ 2 1 + Λ 3 1 * Λ 3 1 = 1 := by
    have h := lightSign4_entry hΛ 1 1
    rw [ite_eq_left rfl, ite_eq_right (by decide), r1] at h
    linarith
  have E22 : Λ 1 2 * Λ 1 2 + Λ 2 2 * Λ 2 2 + Λ 3 2 * Λ 3 2 = 1 := by
    have h := lightSign4_entry hΛ 2 2
    rw [ite_eq_left rfl, ite_eq_right (by decide), r2] at h
    linarith
  have E33 : Λ 1 3 * Λ 1 3 + Λ 2 3 * Λ 2 3 + Λ 3 3 * Λ 3 3 = 1 := by
    have h := lightSign4_entry hΛ 3 3
    rw [ite_eq_left rfl, ite_eq_right (by decide), r3] at h
    linarith
  have E12 : Λ 1 1 * Λ 1 2 + Λ 2 1 * Λ 2 2 + Λ 3 1 * Λ 3 2 = 0 := by
    have h := lightSign4_entry hΛ 1 2
    rw [ite_eq_right (by decide), r1] at h
    linarith
  have E13 : Λ 1 1 * Λ 1 3 + Λ 2 1 * Λ 2 3 + Λ 3 1 * Λ 3 3 = 0 := by
    have h := lightSign4_entry hΛ 1 3
    rw [ite_eq_right (by decide), r1] at h
    linarith
  have E23 : Λ 1 2 * Λ 1 3 + Λ 2 2 * Λ 2 3 + Λ 3 2 * Λ 3 3 = 0 := by
    have h := lightSign4_entry hΛ 2 3
    rw [ite_eq_right (by decide), r2] at h
    linarith
  refine ⟨!![Λ 1 1, Λ 1 2, Λ 1 3; Λ 2 1, Λ 2 2, Λ 2 3; Λ 3 1, Λ 3 2, Λ 3 3], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
      linarith [E11, E22, E33, E12, E13, E23]
  · refine Filter.eventually_of_mem (hBo.mem_nhds hx₀B) fun q hq ↦ ?_
    have h := hrot q hq
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    rw [mulVec_four] at h1 h2 h3
    funext i
    rw [mulVec_three]
    fin_cases i
    · simpa using h1
    · simpa using h2
    · simpa using h3

/-- **The result, given the uniqueness of length-keeping maps into flat space-time.** The map is
shifted along the distance label so that the label is positive at the point; the angles do not
notice. -/
theorem sphere_rigid_of_flat (hflat : FlatUnique) {f : Coords 4 → Coords 4}
    {W : Set (Coords 4)} {x₀ : Coords 4}
    (hW : IsOpen W) (hx₀ : x₀ ∈ W) (hf : ContDiffOn ℝ ∞ f W)
    (hsin : ∀ x ∈ W, sin (x 2) ≠ 0 ∧ sin (f x 2) ≠ 0)
    (hsplit : ∀ x ∈ W, jac f 2 0 x = 0 ∧ jac f 2 1 x = 0 ∧ jac f 3 0 x = 0 ∧ jac f 3 1 x = 0)
    (hkeep : ∀ x ∈ W, ∀ i j : Fin 4, 2 ≤ i.val → 2 ≤ j.val →
      jac f 2 i x * jac f 2 j x + sin (f x 2) ^ 2 * (jac f 3 i x * jac f 3 j x)
        = if i = j then (if i = 2 then 1 else sin (x 2) ^ 2) else 0) :
    ∃ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 ∧ ∀ᶠ x in 𝓝 x₀,
      (![sin (f x 2) * cos (f x 3), sin (f x 2) * sin (f x 3), cos (f x 2)] : Fin 3 → ℝ)
        = R.mulVec ![sin (x 2) * cos (x 3), sin (x 2) * sin (x 3), cos (x 2)] := by
  -- the shift: `x₀ 1 - 1` along the distance label
  obtain ⟨a, ha⟩ : ∃ a : Coords 4, a = Pi.single 1 (x₀ 1 - 1) := ⟨_, rfl⟩
  have a1 : a 1 = x₀ 1 - 1 := by rw [ha]; simp
  have a2 : a 2 = 0 := by rw [ha]; simp
  have a3 : a 3 = 0 := by rw [ha]; simp
  have p2 : ∀ x : Coords 4, (x + a) 2 = x 2 := fun x ↦ by rw [Pi.add_apply, a2, add_zero]
  have hW' : IsOpen ((fun x : Coords 4 ↦ x + a) ⁻¹' W) :=
    hW.preimage (continuous_id.add continuous_const)
  have hfd : ∀ x : Coords 4, x + a ∈ W → DifferentiableAt ℝ f (x + a) := fun x hx ↦
    (hf.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)
  -- the rates of change of the shifted map are those of the map at the shifted point
  have hjac : ∀ x : Coords 4, x + a ∈ W → ∀ α μ : Fin 4,
      jac (fun y ↦ f (y + a)) α μ x = jac f α μ (x + a) := by
    intro x hx α μ
    have hd : DifferentiableAt ℝ (fun y ↦ f (y + a)) x :=
      (hfd x hx).comp x (differentiableAt_id.add_const a)
    rw [jac_eq_fderiv hd, jac_eq_fderiv (hfd x hx), fderiv_comp_add_right]
  have hx₀' : x₀ - a ∈ (fun x : Coords 4 ↦ x + a) ⁻¹' W := by
    change x₀ - a + a ∈ W
    rwa [sub_add_cancel]
  have hpos : 0 < (x₀ - a) 1 := by
    rw [Pi.sub_apply, a1]
    linarith
  obtain ⟨R, hR, hev⟩ := sphere_rigid_pos hflat (f := fun y ↦ f (y + a)) hW' hx₀' hpos
    (hf.comp (contDiff_id.add contDiff_const).contDiffOn fun x hx ↦ hx)
    (fun x hx ↦ by
      have h := hsin (x + a) hx
      rw [p2] at h
      exact h)
    (fun x hx ↦ by
      simp only [hjac x hx]
      exact hsplit (x + a) hx)
    (fun x hx i j hi hj ↦ by
      have h := hkeep (x + a) hx i j hi hj
      rw [p2] at h
      simp only [hjac x hx]
      exact h)
  refine ⟨R, hR, ?_⟩
  have ht : Filter.Tendsto (fun y : Coords 4 ↦ y - a) (𝓝 x₀) (𝓝 (x₀ - a)) :=
    (continuous_id.sub continuous_const).continuousAt
  filter_upwards [ht.eventually hev] with y hy
  have hy' : (![sin (f (y - a + a) 2) * cos (f (y - a + a) 3),
      sin (f (y - a + a) 2) * sin (f (y - a + a) 3), cos (f (y - a + a) 2)] : Fin 3 → ℝ)
        = R.mulVec ![sin ((y - a) 2) * cos ((y - a) 3), sin ((y - a) 2) * sin ((y - a) 3),
          cos ((y - a) 2)] := hy
  have e2 : (y - a) 2 = y 2 := by rw [Pi.sub_apply, a2, sub_zero]
  have e3 : (y - a) 3 = y 3 := by rw [Pi.sub_apply, a3, sub_zero]
  rw [sub_add_cancel, e2, e3] at hy'
  exact hy'

/-- **A map of the angles that keeps the lengths of the unit sphere is a turn or mirror.** Let
`f` be smooth on the open set `W` of coordinate space, off the poles before and after, with new
angles `f x 2`, `f x 3` that do not depend on the first two coordinates, and such that the
length `dθ² + sin² θ dφ²` of steps along the angles is kept. Then near every point of `W` the
point of the unit sphere with the new angles is one fixed turn or mirror `R` applied to the
point with the old angles. -/
theorem sphere_rigid {f : Coords 4 → Coords 4} {W : Set (Coords 4)} {x₀ : Coords 4}
    (hW : IsOpen W) (hx₀ : x₀ ∈ W) (hf : ContDiffOn ℝ ∞ f W)
    (hsin : ∀ x ∈ W, sin (x 2) ≠ 0 ∧ sin (f x 2) ≠ 0)
    (hsplit : ∀ x ∈ W, jac f 2 0 x = 0 ∧ jac f 2 1 x = 0 ∧ jac f 3 0 x = 0 ∧ jac f 3 1 x = 0)
    (hkeep : ∀ x ∈ W, ∀ i j : Fin 4, 2 ≤ i.val → 2 ≤ j.val →
      jac f 2 i x * jac f 2 j x + sin (f x 2) ^ 2 * (jac f 3 i x * jac f 3 j x)
        = if i = j then (if i = 2 then 1 else sin (x 2) ^ 2) else 0) :
    ∃ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 ∧ ∀ᶠ x in 𝓝 x₀,
      (![sin (f x 2) * cos (f x 3), sin (f x 2) * sin (f x 3), cos (f x 2)] : Fin 3 → ℝ)
        = R.mulVec ![sin (x 2) * cos (x 3), sin (x 2) * sin (x 3), cos (x 2)] :=
  sphere_rigid_of_flat (fun g s hs hg D D' hD hD' ↦ unique_flat g s hs hg D D' hD hD')
    hW hx₀ hf hsin hsplit hkeep

end GravityInLean.Curved
