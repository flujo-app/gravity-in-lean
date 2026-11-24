/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.KruskalKept
public import GravityInLean.Global.UniqueFlat
public import GravityInLean.Rim.Table

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# A map that keeps Kruskal's table changes `(T, X)` by a matrix that keeps `-T² + X²`

The steps, for a map `f` that keeps Kruskal's table on `W`:

* `KeepsKruskalOn.plane_jac`: at every point of `W` the slope of `f` carries the `(T, X)` part
  of a step by four numbers, and these keep `-T² + X²` (the split is kept, and the factor in
  front of `-dT² + dX²` depends on the radius only, which is kept).
* `planeMap f`: the new `(T, X)` together with the old angles. It keeps the flat length measure
  (`KeepsKruskalOn.planeMap_keeps`), so near every point it is a linear map and a shift
  (`affine_of_keeps_form_self`, `Global/FlatRigid.lean`).
* The shift of `(T, X)` is zero, because `X² - T²` is kept on an open set
  (`coeffs_zero_of_eventually`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

variable {m : ℝ} {f : Coords 4 → Coords 4} {W : Set (Coords 4)} {x x₀ : Coords 4}

/-! ## Two small tools -/

/-- **A matrix whose entries keep `-T² + X²` keeps it.** (`lightSign2_entries`, read
backwards.) -/
theorem lightSign2_of_entries {L : Matrix (Fin 2) (Fin 2) ℝ}
    (h00 : -(L 0 0 * L 0 0) + L 1 0 * L 1 0 = -1) (h01 : -(L 0 0 * L 0 1) + L 1 0 * L 1 1 = 0)
    (h11 : -(L 0 1 * L 0 1) + L 1 1 * L 1 1 = 1) :
    L.transpose * lightSign2 * L = lightSign2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, lightSign2] <;>
    linarith

/-- **An expression `α · T + β · X + γ` that is zero near a point has `α = 0` and `β = 0`.** -/
theorem coeffs_zero_of_eventually {α β γ : ℝ}
    (h : ∀ᶠ y in 𝓝 x₀, α * y 0 + β * y 1 + γ = 0) : α = 0 ∧ β = 0 := by
  have h0 : α * x₀ 0 + β * x₀ 1 + γ = 0 := h.self_of_nhds
  -- move one label a little: the expression stays zero
  have key : ∀ i : Fin 4, ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      α * Function.update x₀ i (x₀ i + t) 0 + β * Function.update x₀ i (x₀ i + t) 1 + γ = 0 := by
    intro i
    have hc : Continuous fun t : ℝ ↦ Function.update x₀ i (x₀ i + t) :=
      continuous_const.update i (continuous_const.add continuous_id)
    have ht : Filter.Tendsto (fun t : ℝ ↦ Function.update x₀ i (x₀ i + t)) (𝓝 0)
        (𝓝 (Function.update x₀ i (x₀ i + 0))) := hc.tendsto 0
    rw [add_zero, Function.update_eq_self] at ht
    exact (ht.eventually h).filter_mono nhdsWithin_le_nhds
  constructor
  · obtain ⟨t, ht, ht0⟩ := ((key 0).and eventually_mem_nhdsWithin).exists
    have ht0' : t ≠ 0 := ht0
    rw [Function.update_self, Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0)] at ht
    have e : α * t = 0 := by linear_combination ht - h0
    exact (mul_eq_zero.mp e).resolve_right ht0'
  · obtain ⟨t, ht, ht0⟩ := ((key 1).and eventually_mem_nhdsWithin).exists
    have ht0' : t ≠ 0 := ht0
    rw [Function.update_of_ne (by decide : (0 : Fin 4) ≠ 1), Function.update_self] at ht
    have e : β * t = 0 := by linear_combination ht - h0
    exact (mul_eq_zero.mp e).resolve_right ht0'

/-! ## The slope of a map that keeps Kruskal's table, on the `(T, X)` plane -/

/-- **The slope of a map that keeps Kruskal's table carries the `(T, X)` part of a step by four
numbers that keep `-T² + X²`.** At a point of `W` there are `a`, `b`, `c`, `d` such that the new
`T` and `X` parts of a step `u` are `a · u₀ + b · u₁` and `c · u₀ + d · u₁`, and
`-(a s + b t)(a s' + b t') + (c s + d t)(c s' + d t') = -s s' + t t'` for all numbers. -/
theorem KeepsKruskalOn.plane_jac (hm : 0 < m) (h : KeepsKruskalOn m f W) (hx : x ∈ W) :
    ∃ a b c d : ℝ,
      (∀ u : Coords 4, fderiv ℝ f x u 0 = a * u 0 + b * u 1
        ∧ fderiv ℝ f x u 1 = c * u 0 + d * u 1) ∧
      ∀ s t s' t' : ℝ, -((a * s + b * t) * (a * s' + b * t'))
        + (c * s + d * t) * (c * s' + d * t') = -(s * s') + t * t' := by
  have hd : DifferentiableAt ℝ f x := (h.2.2.2 x hx).1.differentiableAt (by simp)
  have hG : ∀ u v : Coords 4, tableMeasure (kruskalG m) (f x) (fderiv ℝ f x u) (fderiv ℝ f x v)
      = tableMeasure (kruskalG m) x u v := (h.2.2.2 x hx).2.self_of_nhds
  -- the table of slopes, and its entries that the split makes zero
  obtain ⟨J, hJ⟩ : ∃ J : Fin 4 → Fin 4 → ℝ,
      ∀ a i, J a i = fderiv ℝ f x (Pi.single i 1) a := ⟨_, fun _ _ ↦ rfl⟩
  have hJ0 : ∀ a i : Fin 4, (a.val < 2 ∧ 2 ≤ i.val) ∨ (2 ≤ a.val ∧ i.val < 2) → J a i = 0 :=
    fun a i hai ↦ by
      rw [hJ, ← jac_eq_fderiv hd]
      exact h.split hm hx a i hai
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
  have p1 : ∀ u : Coords 4, fderiv ℝ f x u 1 = J 1 0 * u 0 + J 1 1 * u 1 := fun u ↦ by
    rw [E, hJ0 1 2 (Or.inl ⟨by decide, by decide⟩), hJ0 1 3 (Or.inl ⟨by decide, by decide⟩)]
    ring
  have p2 : ∀ u : Coords 4, fderiv ℝ f x u 2 = J 2 2 * u 2 + J 2 3 * u 3 := fun u ↦ by
    rw [E, hJ0 2 0 (Or.inr ⟨by decide, by decide⟩), hJ0 2 1 (Or.inr ⟨by decide, by decide⟩)]
    ring
  have p3 : ∀ u : Coords 4, fderiv ℝ f x u 3 = J 3 2 * u 2 + J 3 3 * u 3 := fun u ↦ by
    rw [E, hJ0 3 0 (Or.inr ⟨by decide, by decide⟩), hJ0 3 1 (Or.inr ⟨by decide, by decide⟩)]
    ring
  -- the factor in front of `-dT² + dX²` is kept, and it is positive
  have hA : kruskalA m (f x 0) (f x 1) = kruskalA m (x 0) (x 1) := by
    simp only [kruskalA, h.radius hm hx]
  have hApos : 0 < kruskalA m (x 0) (x 1) := kruskalA_pos hm (h.2.1 hx).1
  refine ⟨J 0 0, J 0 1, J 1 0, J 1 1, fun u ↦ ⟨p0 u, p1 u⟩, fun s t s' t' ↦ ?_⟩
  -- the lengths of two steps in the `(T, X)` plane
  have H' : kruskalA m (x 0) (x 1) * (-((J 0 0 * s + J 0 1 * t) * (J 0 0 * s' + J 0 1 * t'))
      + (J 1 0 * s + J 1 1 * t) * (J 1 0 * s' + J 1 1 * t'))
      = kruskalA m (x 0) (x 1) * (-(s * s') + t * t') := by
    have H := hG ![s, t, 0, 0] ![s', t', 0, 0]
    rw [kruskalG_apply, kruskalG_apply, p0, p1, p2, p3, p0, p1, p2, p3, hA] at H
    simp only [Matrix.cons_val] at H
    linear_combination H
  exact mul_left_cancel₀ hApos.ne' H'

/-! ## The new `(T, X)` with the old angles -/

/-- The map `f` with its angle parts replaced by the old angles: `(T', X', θ, φ)`. -/
noncomputable def planeMap (f : Coords 4 → Coords 4) (x : Coords 4) : Coords 4 :=
  ![f x 0, f x 1, x 2, x 3]

/-- The map `planeMap f` is smooth where `f` is. -/
theorem contDiffAt_planeMap (hf : ContDiffAt ℝ ∞ f x) : ContDiffAt ℝ ∞ (planeMap f) x := by
  refine contDiffAt_pi.2 fun i ↦ ?_
  have c : ∀ j : Fin 4, ContDiffAt ℝ ∞ (fun y : Coords 4 ↦ y j) x :=
    fun j ↦ (contDiff_apply ℝ (fun _ : Fin 4 ↦ ℝ) j).contDiffAt
  fin_cases i
  · exact contDiffAt_pi.1 hf 0
  · exact contDiffAt_pi.1 hf 1
  · exact c 2
  · exact c 3

/-- The slope of `planeMap f`: the `(T, X)` parts of the slope of `f`, and the angle parts of
the step itself. -/
theorem fderiv_planeMap (hf : DifferentiableAt ℝ f x)
    (hp : DifferentiableAt ℝ (planeMap f) x) (u : Coords 4) :
    fderiv ℝ (planeMap f) x u 0 = fderiv ℝ f x u 0
      ∧ fderiv ℝ (planeMap f) x u 1 = fderiv ℝ f x u 1
      ∧ fderiv ℝ (planeMap f) x u 2 = u 2 ∧ fderiv ℝ (planeMap f) x u 3 = u 3 := by
  have a : ∀ j : Fin 4, HasFDerivAt (fun q : Coords 4 ↦ q j) (ContinuousLinearMap.proj j) x :=
    fun j ↦ hasFDerivAt_apply (𝕜 := ℝ) j x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [fderiv_pi_apply hp, fderiv_pi_apply hf]
    rfl
  · rw [fderiv_pi_apply hp, fderiv_pi_apply hf]
    rfl
  · rw [fderiv_pi_apply hp]
    change fderiv ℝ (fun q : Coords 4 ↦ q 2) x u = u 2
    rw [(a 2).fderiv]
    rfl
  · rw [fderiv_pi_apply hp]
    change fderiv ℝ (fun q : Coords 4 ↦ q 3) x u = u 3
    rw [(a 3).fderiv]
    rfl

/-- **The new `(T, X)` with the old angles keeps the flat length measure,** at every point of
`W`. -/
theorem KeepsKruskalOn.planeMap_keeps (hm : 0 < m) (h : KeepsKruskalOn m f W) (hx : x ∈ W)
    (u v : Coords 4) :
    tableMeasure (schwSpaceG 0) 0 (fderiv ℝ (planeMap f) x u) (fderiv ℝ (planeMap f) x v)
      = tableMeasure (schwSpaceG 0) 0 u v := by
  have hc := (h.2.2.2 x hx).1
  have hd : DifferentiableAt ℝ f x := hc.differentiableAt (by simp)
  have hp : DifferentiableAt ℝ (planeMap f) x :=
    (contDiffAt_planeMap hc).differentiableAt (by simp)
  obtain ⟨a, b, c, d, hab, K⟩ := h.plane_jac hm hx
  obtain ⟨u0, u1, u2, u3⟩ := fderiv_planeMap hd hp u
  obtain ⟨v0, v1, v2, v3⟩ := fderiv_planeMap hd hp v
  rw [schwSpace_zero_apply, schwSpace_zero_apply, u0, u1, u2, u3, v0, v1, v2, v3, (hab u).1,
    (hab u).2, (hab v).1, (hab v).2]
  linear_combination K (u 0) (u 1) (v 0) (v 1)

/-! ## The statement -/

/-- **The `(T, X)` part of a map that keeps Kruskal's table:** near every point of its region
the new `T` and `X` are the old ones changed by one matrix `L` that keeps `-T² + X²`. -/
theorem KeepsKruskalOn.plane (hm : 0 < m) (h : KeepsKruskalOn m f W) (hx₀ : x₀ ∈ W) :
    ∃ L : Matrix (Fin 2) (Fin 2) ℝ, L.transpose * lightSign2 * L = lightSign2 ∧
      ∀ᶠ x in 𝓝 x₀, f x 0 = L 0 0 * x 0 + L 0 1 * x 1 ∧ f x 1 = L 1 0 * x 0 + L 1 1 * x 1 := by
  -- a ball around `x₀` inside `W`: there the new `(T, X)` with the old angles is a linear map
  -- and a shift
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp h.1 x₀ hx₀
  have hx₀b : x₀ ∈ Metric.ball x₀ ε := Metric.mem_ball_self hε
  have hsm : ContDiffOn ℝ 2 (planeMap f) (Metric.ball x₀ ε) := fun y hy ↦
    ((contDiffAt_planeMap (h.2.2.2 y (hball hy)).1).of_le
      (by norm_num : (2 : WithTop ℕ∞) ≤ ∞)).contDiffWithinAt
  obtain ⟨Λ, b, -, hΛ⟩ := affine_of_keeps_form_self (B := tableMeasure (schwSpaceG 0) 0)
    (fun y z ↦ flat_symm 0 y z) (fun y hy ↦ flat_nondegenerate 0 y hy) Metric.isOpen_ball
    (convex_ball x₀ ε).isPreconnected hsm fun y hy u v ↦ h.planeMap_keeps hm (hball hy) u v
  -- the linear map is the slope at `x₀`, which is four numbers that keep `-T² + X²`
  obtain ⟨a, b', c, d, hab, K⟩ := h.plane_jac hm hx₀
  have hc₀ := (h.2.2.2 x₀ hx₀).1
  have hd₀ : DifferentiableAt ℝ f x₀ := hc₀.differentiableAt (by simp)
  have hp₀ : DifferentiableAt ℝ (planeMap f) x₀ :=
    (contDiffAt_planeMap hc₀).differentiableAt (by simp)
  have hΛ₀ : fderiv ℝ (planeMap f) x₀ = Λ := (hΛ x₀ hx₀b).2
  have F : ∀ y ∈ Metric.ball x₀ ε,
      f y 0 = a * y 0 + b' * y 1 + b 0 ∧ f y 1 = c * y 0 + d * y 1 + b 1 := fun y hy ↦ by
    have h1 : planeMap f y = Λ y + b := (hΛ y hy).1
    have e0 : f y 0 = Λ y 0 + b 0 := congrFun h1 0
    have e1 : f y 1 = Λ y 1 + b 1 := congrFun h1 1
    rw [← hΛ₀, (fderiv_planeMap hd₀ hp₀ y).1, (hab y).1] at e0
    rw [← hΛ₀, (fderiv_planeMap hd₀ hp₀ y).2.1, (hab y).2] at e1
    exact ⟨e0, e1⟩
  have r00 : -(a * a) + c * c = -1 := by linear_combination K 1 0 1 0
  have r01 : -(a * b') + c * d = 0 := by linear_combination K 1 0 0 1
  have r11 : -(b' * b') + d * d = 1 := by linear_combination K 0 1 0 1
  have hdet : (a * d - b' * c) ^ 2 = 1 := by
    linear_combination (-(d ^ 2 - b' ^ 2)) * r00 + r11 + (-(a * b') + c * d) * r01
  have hdet0 : a * d - b' * c ≠ 0 := fun h0 ↦ by
    rw [h0] at hdet
    norm_num at hdet
  -- the shift is zero: `X² - T²` is kept on the ball
  have hQ : ∀ᶠ y in 𝓝 x₀, (2 * (c * b 1 - a * b 0)) * y 0 + (2 * (d * b 1 - b' * b 0)) * y 1
      + (b 1 ^ 2 - b 0 ^ 2) = 0 :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds x₀ hε) fun y hy ↦ by
      obtain ⟨F0, F1⟩ := F y hy
      have rad := h.radius hm (hball hy)
      rw [F0, F1] at rad
      linear_combination rad - K (y 0) (y 1) (y 0) (y 1)
  obtain ⟨hα, hβ⟩ := coeffs_zero_of_eventually hQ
  have hb0 : b 0 = 0 := by
    have e : (a * d - b' * c) * b 0 = 0 := by
      linear_combination (-(d / 2)) * hα + (c / 2) * hβ
    exact (mul_eq_zero.mp e).resolve_left hdet0
  have hb1 : b 1 = 0 := by
    have e : (a * d - b' * c) * b 1 = 0 := by
      linear_combination (-(b' / 2)) * hα + (a / 2) * hβ
    exact (mul_eq_zero.mp e).resolve_left hdet0
  refine ⟨!![a, b'; c, d], lightSign2_of_entries r00 r01 r11,
    Filter.eventually_of_mem (Metric.ball_mem_nhds x₀ hε) fun y hy ↦ ?_⟩
  obtain ⟨F0, F1⟩ := F y hy
  rw [hb0, add_zero] at F0
  rw [hb1, add_zero] at F1
  exact ⟨F0, F1⟩

end GravityInLean.Curved
