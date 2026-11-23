/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import Mathlib.Analysis.Calculus.ImplicitContDiff

import Mathlib.Tactic

/-!
# Solving a smooth equation: the answer is smooth all around, not only at one point

Board item `task:flows-implicit`.

Lean's standard library has the theorem (`ContDiffAt.implicitFunction` and what follows it in
`Mathlib/Analysis/Calculus/ImplicitContDiff.lean`), but for "infinitely smooth" it gives
smoothness *at* the one point only, which does not say that the answer is smooth on a whole
neighbourhood. This file adds that.
-/

@[expose] public section

namespace GravityInLean.Flows

open Set Metric Topology Filter

open scoped ContDiff

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Let `f (x, y)` be smooth on an open set `s`, let `u` be a point of `s`, and let the slope of
`f` at `u` in the `y` directions alone have an inverse. Then the equation `f (x, y) = f u` can be
solved for `y` near `u`: there is a function `ψ` with

* `ψ u.1 = u.2`;
* `ψ` is smooth at every `x` near `u.1` (so: on a whole neighbourhood);
* `f (x, ψ x) = f u` for `x` near `u.1`;
* near `u`, there is no other solution: `f v = f u` exactly if `ψ v.1 = v.2`. -/
theorem exists_implicit_smooth {f : E₁ × E₂ → F} {s : Set (E₁ × E₂)} (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ f s) {u : E₁ × E₂} (hu : u ∈ s)
    (hinv : (fderiv ℝ f u ∘L ContinuousLinearMap.inr ℝ E₁ E₂).IsInvertible) :
    ∃ ψ : E₁ → E₂, ψ u.1 = u.2 ∧ (∀ᶠ x in 𝓝 u.1, ContDiffAt ℝ ∞ ψ x) ∧
      (∀ᶠ x in 𝓝 u.1, f (x, ψ x) = f u) ∧ ∀ᶠ v in 𝓝 u, f v = f u ↔ ψ v.1 = v.2 := by
  have pn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have cdf : ContDiffAt ℝ ∞ f u := hf.contDiffAt (hs.mem_nhds hu)
  -- The library's answer `ψ` at the point `u`: smooth at `u.1` only, so far.
  obtain ⟨ψ, h0, hsm, heq, huniq⟩ : ∃ ψ : E₁ → E₂, ψ u.1 = u.2 ∧ ContDiffAt ℝ ∞ ψ u.1 ∧
      (∀ᶠ x in 𝓝 u.1, f (x, ψ x) = f u) ∧ ∀ᶠ v in 𝓝 u, f v = f u ↔ ψ v.1 = v.2 :=
    ⟨_, cdf.implicitFunction_apply_self pn hinv, cdf.contDiffAt_implicitFunction pn hinv,
      cdf.eventually_apply_implicitFunction pn hinv,
      cdf.eventually_apply_eq_iff_implicitFunction pn hinv⟩
  refine ⟨ψ, h0, ?_, heq, huniq⟩
  -- The point `(x, ψ x)` on the graph of `ψ` comes near `u` as `x` comes near `u.1`.
  have hg : Tendsto (fun x => (x, ψ x)) (𝓝 u.1) (𝓝 u) := by
    have h : Tendsto (fun x => (x, ψ x)) (𝓝 u.1) (𝓝 (u.1, ψ u.1)) :=
      continuousAt_id.prodMk hsm.continuousAt
    rw [h0] at h
    exact h
  -- Near `u`, the slope of `f` in the `y` directions still has an inverse.
  have hinv' : ∀ᶠ v in 𝓝 u, (fderiv ℝ f v ∘L ContinuousLinearMap.inr ℝ E₁ E₂).IsInvertible := by
    have hc : ContinuousAt (fun v => fderiv ℝ f v ∘L ContinuousLinearMap.inr ℝ E₁ E₂) u :=
      (cdf.continuousAt_fderiv pn).clm_comp continuousAt_const
    exact hc.tendsto.eventually hinv.eventually_nhds
  have hmem : ∀ᶠ v in 𝓝 u, v ∈ s := hs.mem_nhds hu
  have key : ∀ᶠ x in 𝓝 u.1, (x, ψ x) ∈ s ∧
      (fderiv ℝ f (x, ψ x) ∘L ContinuousLinearMap.inr ℝ E₁ E₂).IsInvertible ∧
      (∀ᶠ w in 𝓝 (x, ψ x), f w = f u ↔ ψ w.1 = w.2) ∧ f (x, ψ x) = f u :=
    (hg.eventually hmem).and ((hg.eventually hinv').and
      ((hg.eventually huniq.eventually_nhds).and heq))
  filter_upwards [key] with x₁ ⟨hx₁s, hx₁inv, hx₁uniq, hx₁eq⟩
  -- Solve the equation once more, now around the point `(x₁, ψ x₁)` of the graph.
  have cdf₁ : ContDiffAt ℝ ∞ f (x₁, ψ x₁) := hf.contDiffAt (hs.mem_nhds hx₁s)
  obtain ⟨ψ₁, h1, hsm₁, heq₁⟩ : ∃ ψ₁ : E₁ → E₂, ψ₁ x₁ = ψ x₁ ∧ ContDiffAt ℝ ∞ ψ₁ x₁ ∧
      ∀ᶠ x in 𝓝 x₁, f (x, ψ₁ x) = f (x₁, ψ x₁) :=
    ⟨_, cdf₁.implicitFunction_apply_self pn hx₁inv, cdf₁.contDiffAt_implicitFunction pn hx₁inv,
      cdf₁.eventually_apply_implicitFunction pn hx₁inv⟩
  have hg₁ : Tendsto (fun x => (x, ψ₁ x)) (𝓝 x₁) (𝓝 (x₁, ψ x₁)) := by
    have h : Tendsto (fun x => (x, ψ₁ x)) (𝓝 x₁) (𝓝 (x₁, ψ₁ x₁)) :=
      continuousAt_id.prodMk hsm₁.continuousAt
    rw [h1] at h
    exact h
  -- The new answer `ψ₁` is smooth at `x₁`, and near `x₁` it is the old answer `ψ`, because near
  -- `(x₁, ψ x₁)` the equation has no other solution than `ψ`.
  have hagree : ψ =ᶠ[𝓝 x₁] ψ₁ := by
    filter_upwards [heq₁, hg₁.eventually hx₁uniq] with x hx hiff
    exact hiff.mp (hx.trans hx₁eq)
  exact hsm₁.congr_of_eventuallyEq hagree

end GravityInLean.Flows
