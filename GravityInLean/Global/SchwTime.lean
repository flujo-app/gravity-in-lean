/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.Kretschmann
public import GravityInLean.Global.UniqueFlat

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# A map that keeps Schwarzschild's table of negative mass shifts time, possibly turned round

For a map `f` of coordinate space that keeps Schwarzschild's table of a negative mass on an
open set `W`, keeps the distance label and keeps the split into the `(t, r)` plane and the
sphere: near every point of `W` the new time is `ε · t + c` with `ε = 1` or `ε = -1`
(`schw_time_of_kept`).

The steps:

* `schw_time_slope`: at every point of `W` the slope of the new time is `ε · dt` with
  `ε² = 1` (read the table on the steps of the `(t, r)` plane).
* `timeMap f`: the new time together with the old distance and angles. Its slope keeps the flat
  length measure (`timeMap_keeps`), so near every point it is a linear map and a shift
  (`affine_of_keeps_form_self`, `Global/FlatRigid.lean`); the linear map is its slope.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

variable {m : ℝ} {f : Coords 4 → Coords 4} {W : Set (Coords 4)} {x x₀ : Coords 4}

/-- **The slope of the new time is `ε · dt` with `ε = 1` or `ε = -1`,** at every point of `W`,
for a map that keeps Schwarzschild's table outside the rim, the distance label and the
split. -/
theorem schw_time_slope (hW : IsOpen W) (hWsub : W ⊆ outside m)
    (hf : ∀ x ∈ W, CarriesTableAt (roundG (schwA m) (schwB m)) (roundG (schwA m) (schwB m)) f x)
    (hrad : ∀ x ∈ W, f x 1 = x 1)
    (hsplit : ∀ x ∈ W, ∀ a i : Fin 4,
      (a.val < 2 ∧ 2 ≤ i.val) ∨ (2 ≤ a.val ∧ i.val < 2) → jac f a i x = 0)
    (hx : x ∈ W) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ u : Coords 4, fderiv ℝ f x u 0 = ε * u 0 := by
  have hd : DifferentiableAt ℝ f x := (hf x hx).1.differentiableAt (by simp)
  have hG : ∀ u v : Coords 4,
      tableMeasure (roundG (schwA m) (schwB m)) (f x) (fderiv ℝ f x u) (fderiv ℝ f x v)
        = tableMeasure (roundG (schwA m) (schwB m)) x u v := (hf x hx).2.self_of_nhds
  -- the table of slopes, and its entries that the split makes zero
  obtain ⟨J, hJ⟩ : ∃ J : Fin 4 → Fin 4 → ℝ,
      ∀ a i, J a i = fderiv ℝ f x (Pi.single i 1) a := ⟨_, fun _ _ ↦ rfl⟩
  have hJ0 : ∀ a i : Fin 4, (a.val < 2 ∧ 2 ≤ i.val) ∨ (2 ≤ a.val ∧ i.val < 2) → J a i = 0 :=
    fun a i hai ↦ by
      rw [hJ, ← jac_eq_fderiv hd]
      exact hsplit x hx a i hai
  have E : ∀ (u : Coords 4) (a : Fin 4),
      fderiv ℝ f x u a = u 0 * J a 0 + u 1 * J a 1 + u 2 * J a 2 + u 3 * J a 3 := fun u a ↦ by
    have e := clm_apply_eq_sum
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 ↦ ℝ) a).comp (fderiv ℝ f x)) u
    rw [Fin.sum_univ_four] at e
    rw [hJ, hJ, hJ, hJ]
    exact e
  have p0 : ∀ u : Coords 4, fderiv ℝ f x u 0 = J 0 0 * u 0 + J 0 1 * u 1 := fun u ↦ by
    rw [E, hJ0 0 2 (Or.inl ⟨by decide, by decide⟩), hJ0 0 3 (Or.inl ⟨by decide, by decide⟩)]
    ring
  have p2 : ∀ u : Coords 4, fderiv ℝ f x u 2 = J 2 2 * u 2 + J 2 3 * u 3 := fun u ↦ by
    rw [E, hJ0 2 0 (Or.inr ⟨by decide, by decide⟩), hJ0 2 1 (Or.inr ⟨by decide, by decide⟩)]
    ring
  have p3 : ∀ u : Coords 4, fderiv ℝ f x u 3 = J 3 2 * u 2 + J 3 3 * u 3 := fun u ↦ by
    rw [E, hJ0 3 0 (Or.inr ⟨by decide, by decide⟩), hJ0 3 1 (Or.inr ⟨by decide, by decide⟩)]
    ring
  -- the distance label is kept on the open set `W`, so its slope is `dr`
  have p1 : ∀ u : Coords 4, fderiv ℝ f x u 1 = u 1 := fun u ↦ by
    have hev : (fun y : Coords 4 ↦ f y 1) =ᶠ[𝓝 x] fun y : Coords 4 ↦ y 1 :=
      Filter.eventuallyEq_of_mem (hW.mem_nhds hx) fun y hy ↦ hrad y hy
    have a : HasFDerivAt (fun q : Coords 4 ↦ q 1) (ContinuousLinearMap.proj 1) x :=
      hasFDerivAt_apply (𝕜 := ℝ) 1 x
    rw [fderiv_pi_apply hd, hev.fderiv_eq, a.fderiv]
    rfl
  have hA : schwA m (x 1) ≠ 0 := (schwA_pos_outside (hWsub hx).1 (hWsub hx).2.1).ne'
  -- the lengths of two steps in the `(t, r)` plane
  have K : ∀ s t s' t' : ℝ, (J 0 0 * s + J 0 1 * t) * (J 0 0 * s' + J 0 1 * t') = s * s' :=
    fun s t s' t' ↦ by
      have H' : schwA m (x 1) * ((J 0 0 * s + J 0 1 * t) * (J 0 0 * s' + J 0 1 * t'))
          = schwA m (x 1) * (s * s') := by
        have H := hG ![s, t, 0, 0] ![s', t', 0, 0]
        rw [schw_apply, schw_apply, hrad x hx, p0, p1, p2, p3, p0, p1, p2, p3] at H
        simp only [Matrix.cons_val] at H
        linear_combination (-1 : ℝ) * H
      exact mul_left_cancel₀ hA H'
  have e00 : J 0 0 * J 0 0 = 1 := by linear_combination K 1 0 1 0
  have e01 : J 0 1 * J 0 1 = 0 := by linear_combination K 0 1 0 1
  have h01 : J 0 1 = 0 := mul_self_eq_zero.mp e01
  refine ⟨J 0 0, mul_self_eq_one_iff.mp e00, fun u ↦ ?_⟩
  rw [p0, h01]
  ring

/-! ## The new time with the old distance and angles -/

/-- The map `f` with all parts but the time replaced by the old ones: `(t', r, θ, φ)`. -/
noncomputable def timeMap (f : Coords 4 → Coords 4) (x : Coords 4) : Coords 4 :=
  ![f x 0, x 1, x 2, x 3]

/-- The map `timeMap f` is smooth where `f` is. -/
theorem contDiffAt_timeMap (hf : ContDiffAt ℝ ∞ f x) : ContDiffAt ℝ ∞ (timeMap f) x := by
  refine contDiffAt_pi.2 fun i ↦ ?_
  have c : ∀ j : Fin 4, ContDiffAt ℝ ∞ (fun y : Coords 4 ↦ y j) x :=
    fun j ↦ (contDiff_apply ℝ (fun _ : Fin 4 ↦ ℝ) j).contDiffAt
  fin_cases i
  · exact contDiffAt_pi.1 hf 0
  · exact c 1
  · exact c 2
  · exact c 3

/-- The slope of `timeMap f`: the time part of the slope of `f`, and the other parts of the
step itself. -/
theorem fderiv_timeMap (hf : DifferentiableAt ℝ f x) (hp : DifferentiableAt ℝ (timeMap f) x)
    (u : Coords 4) :
    fderiv ℝ (timeMap f) x u 0 = fderiv ℝ f x u 0 ∧ fderiv ℝ (timeMap f) x u 1 = u 1
      ∧ fderiv ℝ (timeMap f) x u 2 = u 2 ∧ fderiv ℝ (timeMap f) x u 3 = u 3 := by
  have a : ∀ j : Fin 4, HasFDerivAt (fun q : Coords 4 ↦ q j) (ContinuousLinearMap.proj j) x :=
    fun j ↦ hasFDerivAt_apply (𝕜 := ℝ) j x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [fderiv_pi_apply hp, fderiv_pi_apply hf]
    rfl
  · rw [fderiv_pi_apply hp]
    change fderiv ℝ (fun q : Coords 4 ↦ q 1) x u = u 1
    rw [(a 1).fderiv]
    rfl
  · rw [fderiv_pi_apply hp]
    change fderiv ℝ (fun q : Coords 4 ↦ q 2) x u = u 2
    rw [(a 2).fderiv]
    rfl
  · rw [fderiv_pi_apply hp]
    change fderiv ℝ (fun q : Coords 4 ↦ q 3) x u = u 3
    rw [(a 3).fderiv]
    rfl

/-- **The new time with the old distance and angles keeps the flat length measure,** at every
point of `W`. -/
theorem timeMap_keeps (hW : IsOpen W) (hWsub : W ⊆ outside m)
    (hf : ∀ x ∈ W, CarriesTableAt (roundG (schwA m) (schwB m)) (roundG (schwA m) (schwB m)) f x)
    (hrad : ∀ x ∈ W, f x 1 = x 1)
    (hsplit : ∀ x ∈ W, ∀ a i : Fin 4,
      (a.val < 2 ∧ 2 ≤ i.val) ∨ (2 ≤ a.val ∧ i.val < 2) → jac f a i x = 0)
    (hx : x ∈ W) (u v : Coords 4) :
    tableMeasure (schwSpaceG 0) 0 (fderiv ℝ (timeMap f) x u) (fderiv ℝ (timeMap f) x v)
      = tableMeasure (schwSpaceG 0) 0 u v := by
  have hc := (hf x hx).1
  have hd : DifferentiableAt ℝ f x := hc.differentiableAt (by simp)
  have hp : DifferentiableAt ℝ (timeMap f) x := (contDiffAt_timeMap hc).differentiableAt (by simp)
  obtain ⟨ε, hε, hslope⟩ := schw_time_slope hW hWsub hf hrad hsplit hx
  have hεε : ε * ε = 1 := mul_self_eq_one_iff.mpr hε
  obtain ⟨u0, u1, u2, u3⟩ := fderiv_timeMap hd hp u
  obtain ⟨v0, v1, v2, v3⟩ := fderiv_timeMap hd hp v
  rw [schwSpace_zero_apply, schwSpace_zero_apply, u0, u1, u2, u3, v0, v1, v2, v3, hslope u,
    hslope v]
  linear_combination (-(u 0 * v 0)) * hεε

/-! ## The statement -/

/-- **The time part of a map that keeps Schwarzschild's table of negative mass:** if the map
also keeps the distance label and the split into the `(t, r)` plane and the sphere, then near
every point of its region the new time is `ε · t + c`, with `ε = 1` or `ε = -1`. (The proof
uses neither the sign of the mass nor where `f` lands: only that `W` lies outside the rim.) -/
theorem schw_time_of_kept {m : ℝ} (_hm : m < 0) {f : Coords 4 → Coords 4} {W : Set (Coords 4)}
    (hW : IsOpen W) (hWsub : W ⊆ outside m) (_hfW : ∀ x ∈ W, f x ∈ outside m)
    (hf : ∀ x ∈ W, CarriesTableAt (roundG (schwA m) (schwB m)) (roundG (schwA m) (schwB m)) f x)
    (hrad : ∀ x ∈ W, f x 1 = x 1)
    (hsplit : ∀ x ∈ W, ∀ a i : Fin 4,
      (a.val < 2 ∧ 2 ≤ i.val) ∨ (2 ≤ a.val ∧ i.val < 2) → jac f a i x = 0)
    {x₀ : Coords 4} (hx₀ : x₀ ∈ W) :
    ∃ ε c : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ᶠ x in 𝓝 x₀, f x 0 = ε * x 0 + c := by
  -- a ball around `x₀` inside `W`: there the new time with the old distance and angles is a
  -- linear map and a shift
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hW x₀ hx₀
  have hx₀b : x₀ ∈ Metric.ball x₀ δ := Metric.mem_ball_self hδ
  have hsm : ContDiffOn ℝ 2 (timeMap f) (Metric.ball x₀ δ) := fun y hy ↦
    ((contDiffAt_timeMap (hf y (hball hy)).1).of_le
      (by norm_num : (2 : WithTop ℕ∞) ≤ ∞)).contDiffWithinAt
  obtain ⟨Λ, b, -, hΛ⟩ := affine_of_keeps_form_self (B := tableMeasure (schwSpaceG 0) 0)
    (fun y z ↦ flat_symm 0 y z) (fun y hy ↦ flat_nondegenerate 0 y hy) Metric.isOpen_ball
    (convex_ball x₀ δ).isPreconnected hsm
    fun y hy u v ↦ timeMap_keeps hW hWsub hf hrad hsplit (hball hy) u v
  -- the linear map is the slope at `x₀`, whose time part is `ε · dt`
  obtain ⟨ε, hε, hslope⟩ := schw_time_slope hW hWsub hf hrad hsplit hx₀
  have hc₀ := (hf x₀ hx₀).1
  have hd₀ : DifferentiableAt ℝ f x₀ := hc₀.differentiableAt (by simp)
  have hp₀ : DifferentiableAt ℝ (timeMap f) x₀ :=
    (contDiffAt_timeMap hc₀).differentiableAt (by simp)
  have hΛ₀ : fderiv ℝ (timeMap f) x₀ = Λ := (hΛ x₀ hx₀b).2
  refine ⟨ε, b 0, hε, Filter.eventually_of_mem (Metric.ball_mem_nhds x₀ hδ) fun y hy ↦ ?_⟩
  have h1 : timeMap f y = Λ y + b := (hΛ y hy).1
  have e0 : f y 0 = Λ y 0 + b 0 := congrFun h1 0
  rw [← hΛ₀, (fderiv_timeMap hd₀ hp₀ y).1, hslope y] at e0
  exact e0

end GravityInLean.Curved
