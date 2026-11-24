/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Flows.SmoothFlow
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

import Mathlib.Tactic

/-!
# A function that is constant along a field of arrows in the plane

Board item `task:rim-first-integral`. Around a point of the plane where a smooth field of
arrows `(a, b)` is not zero there is a smooth function `u` whose slope along the field is zero
everywhere near the point, and whose slope at the point is not zero.

On paper: take a direction `n` across the field at the point `p`. Follow the field for the time
`τ` from the point `p + s • n` (`smoothFlow`). The map `(s, τ) ↦` that point is smooth, and its
slope at `(0, 0)` has the columns `n` and `(a p, b p)`, so it can be undone near `p` (the
inverse function theorem). `u` is the label `s` of the point. It does not change along the
paths of the field, so its slope along the field is zero.
-/

@[expose] public section

namespace GravityInLean

open Set

open scoped ContDiff Topology

namespace Rim

/-- **Inverse function theorem, as a change of labels.** A map `Φ` that is smooth on an open set
`W`, and whose slope at a point `y₀` of `W` can be undone, is near `y₀` one-to-one on an open
set around `y₀` inside `W`, smooth there, with a smooth inverse. (As `Join.exists_localDiffeo`,
for any complete space in place of the four coordinates.) -/
theorem exists_localDiffeo {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {Φ : E → E} {W : Set E} (hW : IsOpen W)
    (hΦ : ContDiffOn ℝ ∞ Φ W) {y₀ : E} (hy₀ : y₀ ∈ W)
    (hunit : IsUnit (fderiv ℝ Φ y₀)) :
    ∃ e : OpenPartialHomeomorph E E, y₀ ∈ e.source ∧ e.source ⊆ W ∧
      (∀ y, e y = Φ y) ∧ ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  -- at every point of `W` with a slope that can be undone, `Φ` has that slope as an equivalence
  have hequiv : ∀ y ∈ W, IsUnit (fderiv ℝ Φ y) →
      ∃ f' : E ≃L[ℝ] E, HasFDerivAt Φ (f' : E →L[ℝ] E) y := by
    rintro y hy ⟨u, hu⟩
    refine ⟨ContinuousLinearEquiv.ofUnit u, ?_⟩
    have e : (ContinuousLinearEquiv.ofUnit u : E →L[ℝ] E) = fderiv ℝ Φ y := by
      rw [← hu]
      rfl
    rw [e]
    exact ((hΦ.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
  have hcd : ContDiffAt ℝ ∞ Φ y₀ := hΦ.contDiffAt (hW.mem_nhds hy₀)
  obtain ⟨f', hf'⟩ := hequiv y₀ hy₀ hunit
  -- the set of points of `W` where the slope can be undone is open
  have hV : IsOpen (W ∩ fderiv ℝ Φ ⁻¹' {A : E →L[ℝ] E | IsUnit A}) :=
    (hΦ.continuousOn_fderiv_of_isOpen hW (by simp)).isOpen_inter_preimage hW Units.isOpen
  refine ⟨(hcd.toOpenPartialHomeomorph Φ hf' (by simp)).restrOpen _ hV,
    ⟨hcd.mem_toOpenPartialHomeomorph_source hf' (by simp), hy₀, hunit⟩,
    fun y hy ↦ hy.2.1, fun y ↦ rfl, hΦ.mono fun y hy ↦ hy.2.1, fun z hz ↦ ?_⟩
  set e := (hcd.toOpenPartialHomeomorph Φ hf' (by simp)).restrOpen _ hV with he
  have hs : e.symm z ∈ e.source := e.map_target hz
  obtain ⟨f'', hf''⟩ := hequiv (e.symm z) hs.2.1 hs.2.2
  exact (e.contDiffAt_symm hz (f₀' := f'') hf''
    (hΦ.contDiffAt (hW.mem_nhds hs.2.1))).contDiffWithinAt

/-- A linear map of the plane to itself that sends `(1, 0)` to `(-b, a)` and `(0, 1)` to
`(a, b)`, with `a` and `b` not both zero, can be undone. -/
theorem isUnit_of_columns {L : ℝ × ℝ →L[ℝ] ℝ × ℝ} {a b : ℝ} (hne : a ≠ 0 ∨ b ≠ 0)
    (h1 : L (1, 0) = (-b, a)) (h2 : L (0, 1) = (a, b)) : IsUnit L := by
  refine ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.2
    ((LinearMap.isUnit_iff_ker_eq_bot _).2 (LinearMap.ker_eq_bot'.2 fun v hv ↦ ?_))
  have hv' : L v = 0 := hv
  have hdecomp : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  have h := congrArg L hdecomp
  rw [hv', map_add, map_smul, map_smul, h1, h2] at h
  have e1 : 0 = v.1 * -b + v.2 * a := by simpa using congrArg Prod.fst h
  have e2 : 0 = v.1 * a + v.2 * b := by simpa using congrArg Prod.snd h
  have hd : 0 < a ^ 2 + b ^ 2 := by
    rcases hne with h | h
    · have := sq_pos_of_ne_zero h
      nlinarith [sq_nonneg b]
    · have := sq_pos_of_ne_zero h
      nlinarith [sq_nonneg a]
  have hv1 : v.1 * (a ^ 2 + b ^ 2) = 0 := by linear_combination (-a) * e2 + b * e1
  have hv2 : v.2 * (a ^ 2 + b ^ 2) = 0 := by linear_combination (-a) * e1 + (-b) * e2
  exact Prod.ext ((mul_eq_zero.1 hv1).resolve_right hd.ne')
    ((mul_eq_zero.1 hv2).resolve_right hd.ne')

/-- **A function constant along a field.** Near a point `p` of the plane where the smooth field
of arrows `(a, b)` is not zero, there is a smooth function `u` with slope zero along the field
at every point near `p`, and with a slope at `p` that is not zero. -/
theorem exists_firstIntegral {a b : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    (ha : ContDiffOn ℝ ∞ a W) (hb : ContDiffOn ℝ ∞ b W) {p : ℝ × ℝ} (hp : p ∈ W)
    (hne : a p ≠ 0 ∨ b p ≠ 0) :
    ∃ (u : ℝ × ℝ → ℝ) (N : Set (ℝ × ℝ)), IsOpen N ∧ p ∈ N ∧ N ⊆ W ∧ ContDiffOn ℝ ∞ u N ∧
      (∀ x ∈ N, fderiv ℝ u x (a x, b x) = 0) ∧ fderiv ℝ u p ≠ 0 := by
  -- follow the field: its flow
  have hX : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ ↦ (a x, b x)) W := ha.prodMk hb
  obtain ⟨ε, flow, hε, hflow, hflow0, hflowd⟩ :=
    smoothFlow (ℝ × ℝ) (fun x ↦ (a x, b x)) W hW hX p hp
  have hp0 : p ∈ Metric.ball p ε := Metric.mem_ball_self hε
  -- a direction across the field at `p`
  obtain ⟨n, hn⟩ : ∃ n : ℝ × ℝ, n = (-(b p), a p) := ⟨_, rfl⟩
  have hline : HasDerivAt (fun s : ℝ ↦ p + s • n) n 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const n).const_add p
  have hlineC : Continuous (fun s : ℝ ↦ p + s • n) := by fun_prop
  have hball : ∀ᶠ s : ℝ in 𝓝 0, p + s • n ∈ Metric.ball p ε := by
    have h : Metric.ball p ε ∈ 𝓝 (p + (0 : ℝ) • n) := by
      rw [zero_smul, add_zero]
      exact Metric.ball_mem_nhds p hε
    exact hlineC.continuousAt.preimage_mem_nhds h
  -- the map `(s, τ) ↦` the point reached after the time `τ` from `p + s • n`
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℝ × ℝ → ℝ × ℝ, ∀ s τ, Ψ (s, τ) = flow τ (p + s • n) :=
    ⟨fun q ↦ flow q.2 (p + q.1 • n), fun _ _ ↦ rfl⟩
  have hGC : ContDiff ℝ ∞ (fun q : ℝ × ℝ ↦ (q.2, p + q.1 • n)) := by fun_prop
  obtain ⟨D, hD⟩ : ∃ D : Set (ℝ × ℝ),
      D = (fun q : ℝ × ℝ ↦ (q.2, p + q.1 • n)) ⁻¹' (Ioo (-ε) ε ×ˢ Metric.ball p ε) := ⟨_, rfl⟩
  have hDmem : ∀ s τ : ℝ, (s, τ) ∈ D ↔ τ ∈ Ioo (-ε) ε ∧ p + s • n ∈ Metric.ball p ε := by
    intro s τ
    rw [hD]
    rfl
  have hDopen : IsOpen D := by
    rw [hD]
    exact (isOpen_Ioo.prod Metric.isOpen_ball).preimage hGC.continuous
  have h0D : ((0 : ℝ), (0 : ℝ)) ∈ D := by
    rw [hDmem, zero_smul, add_zero]
    exact ⟨⟨by linarith, hε⟩, hp0⟩
  have hΨsmooth : ContDiffOn ℝ ∞ Ψ D := by
    have h : ContDiffOn ℝ ∞ ((fun q : ℝ × (ℝ × ℝ) ↦ flow q.1 q.2) ∘
        fun q : ℝ × ℝ ↦ (q.2, p + q.1 • n)) D :=
      hflow.comp hGC.contDiffOn (fun q hq ↦ by rw [hD] at hq; exact hq)
    exact h.congr fun q _ ↦ hΨ q.1 q.2
  -- its slope at `(0, 0)`: the columns are `n` and the arrow of the field at `p`
  have hL : HasFDerivAt Ψ (fderiv ℝ Ψ (0, 0)) (0, 0) :=
    ((hΨsmooth.contDiffAt (hDopen.mem_nhds h0D)).differentiableAt (by simp)).hasFDerivAt
  have hcol1 : fderiv ℝ Ψ (0, 0) (1, 0) = (-(b p), a p) := by
    have h1 : HasDerivAt (Ψ ∘ fun s : ℝ ↦ (s, (0 : ℝ))) (fderiv ℝ Ψ (0, 0) (1, 0)) 0 :=
      HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ ↦ (s, (0 : ℝ))) (0 : ℝ) hL
        ((hasDerivAt_id' (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ)))
    have h3 : (Ψ ∘ fun s : ℝ ↦ (s, (0 : ℝ))) =ᶠ[𝓝 0] fun s ↦ p + s • n := by
      filter_upwards [hball] with s hs
      change Ψ (s, 0) = p + s • n
      rw [hΨ]
      exact hflow0 _ hs
    rw [← hn]
    exact h1.unique (hline.congr_of_eventuallyEq h3)
  have hcol2 : fderiv ℝ Ψ (0, 0) (0, 1) = (a p, b p) := by
    have h1 : HasDerivAt (Ψ ∘ fun τ : ℝ ↦ ((0 : ℝ), τ)) (fderiv ℝ Ψ (0, 0) (0, 1)) 0 :=
      HasFDerivAt.comp_hasDerivAt (f := fun τ : ℝ ↦ ((0 : ℝ), τ)) (0 : ℝ) hL
        ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk (hasDerivAt_id' (0 : ℝ)))
    have h2 : HasDerivAt (fun r ↦ flow r p) (a (flow 0 p), b (flow 0 p)) 0 :=
      (hflowd p hp0 0 ⟨by linarith, hε⟩).2
    rw [hflow0 p hp0] at h2
    have h3 : (Ψ ∘ fun τ : ℝ ↦ ((0 : ℝ), τ)) = fun r ↦ flow r p := by
      funext τ
      change Ψ (0, τ) = flow τ p
      rw [hΨ, zero_smul, add_zero]
    rw [h3] at h1
    exact h1.unique h2
  -- so the map can be undone near `(0, 0)`
  obtain ⟨e, he0, heD, heΨ, -, hesymm⟩ :=
    exists_localDiffeo hDopen hΨsmooth h0D (isUnit_of_columns hne hcol1 hcol2)
  have hΨ0 : e (0, 0) = p := by
    rw [heΨ, hΨ, zero_smul, add_zero]
    exact hflow0 p hp0
  have hpN : p ∈ e.target := hΨ0 ▸ e.map_source he0
  -- `u` is the label `s` of the point
  have hu : ContDiffOn ℝ ∞ (fun x ↦ (e.symm x).1) e.target := contDiff_fst.comp_contDiffOn hesymm
  have hudiff : ∀ x ∈ e.target,
      HasFDerivAt (fun x ↦ (e.symm x).1) (fderiv ℝ (fun x ↦ (e.symm x).1) x) x := fun x hx ↦
    ((hu.contDiffAt (e.open_target.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  refine ⟨fun x ↦ (e.symm x).1, e.target, e.open_target, hpN, ?_, hu, ?_, ?_⟩
  · -- the points near `p` are reached by the flow, which stays where the field lives
    intro x hx
    obtain ⟨⟨s, τ⟩, hsτ⟩ : ∃ q : ℝ × ℝ, q = e.symm x := ⟨_, rfl⟩
    have hq : (s, τ) ∈ e.source := hsτ ▸ e.map_target hx
    have hqD := (hDmem s τ).1 (heD hq)
    have hx' : flow τ (p + s • n) = x := by
      rw [← hΨ, ← heΨ, hsτ]
      exact e.right_inv hx
    exact hx' ▸ (hflowd _ hqD.2 _ hqD.1).1
  · -- along a path of the field the label `s` does not change
    intro x hx
    obtain ⟨⟨s, τ⟩, hsτ⟩ : ∃ q : ℝ × ℝ, q = e.symm x := ⟨_, rfl⟩
    have hq : (s, τ) ∈ e.source := hsτ ▸ e.map_target hx
    have hqD := (hDmem s τ).1 (heD hq)
    have hx' : flow τ (p + s • n) = x := by
      rw [← hΨ, ← heΨ, hsτ]
      exact e.right_inv hx
    have hc : HasDerivAt (fun r ↦ flow r (p + s • n))
        (a (flow τ (p + s • n)), b (flow τ (p + s • n))) τ := (hflowd _ hqD.2 _ hqD.1).2
    have hux : HasFDerivAt (fun x ↦ (e.symm x).1) (fderiv ℝ (fun x ↦ (e.symm x).1) x)
        (flow τ (p + s • n)) := by
      rw [hx']
      exact hudiff x hx
    have h1 : HasDerivAt ((fun x ↦ (e.symm x).1) ∘ fun r ↦ flow r (p + s • n))
        (fderiv ℝ (fun x ↦ (e.symm x).1) x
          (a (flow τ (p + s • n)), b (flow τ (p + s • n)))) τ :=
      hux.comp_hasDerivAt τ hc
    rw [hx'] at h1
    have h2 : ((fun x ↦ (e.symm x).1) ∘ fun r ↦ flow r (p + s • n)) =ᶠ[𝓝 τ] fun _ ↦ s := by
      have hmem : ∀ᶠ r : ℝ in 𝓝 τ, (s, r) ∈ e.source :=
        (Continuous.prodMk_right s).continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hq)
      filter_upwards [hmem] with r hr
      change (e.symm (flow r (p + s • n))).1 = s
      rw [← hΨ, ← heΨ, e.left_inv hr]
    exact h1.unique ((hasDerivAt_const τ s).congr_of_eventuallyEq h2)
  · -- across the field at `p` the label `s` grows at the rate one
    intro h0
    have hup : HasFDerivAt (fun x ↦ (e.symm x).1) (fderiv ℝ (fun x ↦ (e.symm x).1) p)
        (p + (0 : ℝ) • n) := by
      rw [zero_smul, add_zero]
      exact hudiff p hpN
    have h1 : HasDerivAt ((fun x ↦ (e.symm x).1) ∘ fun s : ℝ ↦ p + s • n)
        (fderiv ℝ (fun x ↦ (e.symm x).1) p n) 0 := hup.comp_hasDerivAt (0 : ℝ) hline
    have h2 : ((fun x ↦ (e.symm x).1) ∘ fun s : ℝ ↦ p + s • n) =ᶠ[𝓝 0] fun s ↦ s := by
      have hmem : ∀ᶠ s : ℝ in 𝓝 0, (s, (0 : ℝ)) ∈ e.source :=
        (Continuous.prodMk_left (0 : ℝ)).continuousAt.preimage_mem_nhds
          (e.open_source.mem_nhds he0)
      filter_upwards [hmem, hball] with s hs hsb
      have h : p + s • n = e (s, 0) := by
        rw [heΨ, hΨ]
        exact (hflow0 _ hsb).symm
      change (e.symm (p + s • n)).1 = s
      rw [h, e.left_inv hs]
    have h4 : fderiv ℝ (fun x ↦ (e.symm x).1) p n = 1 :=
      h1.unique ((hasDerivAt_id' (0 : ℝ)).congr_of_eventuallyEq h2)
    rw [h0, zero_apply] at h4
    exact zero_ne_one h4

end Rim

end GravityInLean
