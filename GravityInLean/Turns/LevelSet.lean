/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Turns.Basic
public import GravityInLean.Flows.Implicit
public import Mathlib.Topology.Algebra.Module.FiniteDimension

import Mathlib.Tactic

/-!
# Where two smooth functions of four numbers are both zero: a surface

Board item `task:turns-level-set`. Step 3 of the route, in abstract form.

Take two smooth functions of four numbers (written as one map `F` into pairs) that are both zero
at a point `p`, and two directions `a`, `b` at `p` along which the pair of functions loses no
direction (a determinant of two by two slopes is not zero). Then the points near `p` where both
functions are zero form a surface: there is a smooth `σ` of two numbers that runs through such
points, starts at `p`, and whose two directions at the start are any two given arrows `e₁`, `e₂`,
each corrected by a mix of `a` and `b`.

The proof solves the equation `F (p + u.1 • e₁ + u.2 • e₂ + w.1 • a + w.2 • b) = 0` for `w`, by
`GravityInLean.Flows.exists_implicit_smooth`.
-/

@[expose] public section

namespace GravityInLean.Turns

open Set Metric Topology Filter

open scoped ContDiff

/-- In a space of finitely many dimensions, a straight map of the space to itself that sends no
two points to the same point has an inverse. -/
theorem isInvertible_of_injective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (M : E →L[ℝ] E) (h : Function.Injective M) : M.IsInvertible :=
  ⟨(LinearEquiv.ofInjectiveEndo (M : E →ₗ[ℝ] E) h).toContinuousLinearEquiv,
    ContinuousLinearMap.ext fun _ ↦ rfl⟩

/-- A straight map `M` of pairs to pairs that sends `w` to `w.1 • x + w.2 • y` has an inverse,
when the determinant of the two pairs `x`, `y` is not zero. -/
theorem isInvertible_of_det_ne_zero (M : ℝ × ℝ →L[ℝ] ℝ × ℝ) (x y : ℝ × ℝ)
    (hM : ∀ w, M w = w.1 • x + w.2 • y) (hdet : x.1 * y.2 - x.2 * y.1 ≠ 0) : M.IsInvertible := by
  apply isInvertible_of_injective
  rw [injective_iff_map_eq_zero]
  intro w hw
  rw [hM] at hw
  have h1 : w.1 * x.1 + w.2 * y.1 = 0 := by simpa using congrArg Prod.fst hw
  have h2 : w.1 * x.2 + w.2 * y.2 = 0 := by simpa using congrArg Prod.snd hw
  have e1 : w.1 * (x.1 * y.2 - x.2 * y.1) = 0 := by linear_combination y.2 * h1 - y.1 * h2
  have e2 : w.2 * (x.1 * y.2 - x.2 * y.1) = 0 := by linear_combination x.1 * h2 - x.2 * h1
  exact Prod.ext ((mul_eq_zero.mp e1).resolve_right hdet) ((mul_eq_zero.mp e2).resolve_right hdet)

/-- The zero set of two smooth functions of four numbers is a surface. Let `F` (a pair of
functions) be smooth on the open region `s` and zero at the point `p` of `s`, and let `a`, `b` be
two directions along which `F` loses no direction at `p` (`hdet`). Then for any two arrows `e₁`,
`e₂` there is a smooth `σ` of two numbers, defined within `δ` of the pair `0`, with `σ 0 = p`,
all of whose points lie in `s` and are zeros of `F`, and whose two directions at `0` are `e₁`
and `e₂`, each corrected by a mix of `a` and `b`. -/
theorem exists_levelSurface (F : Coords 4 → ℝ × ℝ) (s : Set (Coords 4)) (hs : IsOpen s)
    (p : Coords 4) (hp : p ∈ s) (hF : ContDiffOn ℝ ∞ F s) (hFp : F p = 0) (a b : Coords 4)
    (hdet : (fderiv ℝ F p a).1 * (fderiv ℝ F p b).2 - (fderiv ℝ F p a).2 * (fderiv ℝ F p b).1 ≠ 0)
    (e₁ e₂ : Coords 4) :
    ∃ (δ : ℝ) (σ : ℝ × ℝ → Coords 4), 0 < δ ∧ ContDiffOn ℝ ∞ σ (Metric.ball 0 δ) ∧ σ 0 = p ∧
      (∀ u ∈ Metric.ball (0 : ℝ × ℝ) δ, σ u ∈ s ∧ F (σ u) = 0) ∧
      ∃ c₁ d₁ c₂ d₂ : ℝ, fderiv ℝ σ 0 (1, 0) = e₁ + c₁ • a + d₁ • b ∧
        fderiv ℝ σ 0 (0, 1) = e₂ + c₂ • a + d₂ • b := by
  -- The straight map `A (u, w) = u.1 • e₁ + u.2 • e₂ + w.1 • a + w.2 • b`.
  obtain ⟨A, hA⟩ : ∃ A : (ℝ × ℝ) × (ℝ × ℝ) →L[ℝ] Coords 4,
      ∀ v, A v = v.1.1 • e₁ + v.1.2 • e₂ + v.2.1 • a + v.2.2 • b :=
    ⟨((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
          (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ))).smulRight e₁
        + ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
          (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ))).smulRight e₂
        + ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
          (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ))).smulRight a
        + ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
          (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ))).smulRight b,
      fun v ↦ by simp⟩
  have hA0 : p + A 0 = p := by simp
  -- The function `f (u, w) = F (p + A (u, w))` is smooth on an open set around `0`.
  have hs' : IsOpen {v : (ℝ × ℝ) × (ℝ × ℝ) | p + A v ∈ s} :=
    hs.preimage (continuous_const.add A.continuous)
  have hf : ContDiffOn ℝ ∞ (fun v ↦ F (p + A v)) {v : (ℝ × ℝ) × (ℝ × ℝ) | p + A v ∈ s} :=
    hF.comp (contDiff_const.add A.contDiff).contDiffOn fun v hv ↦ hv
  have h0 : (0 : (ℝ × ℝ) × (ℝ × ℝ)) ∈ {v : (ℝ × ℝ) × (ℝ × ℝ) | p + A v ∈ s} := by
    change p + A 0 ∈ s
    rw [hA0]
    exact hp
  -- Its slope at `0` is the slope of `F` at `p` after `A`.
  have hFd : HasFDerivAt F (fderiv ℝ F p) (p + A 0) := by
    rw [hA0]
    exact ((hF.contDiffAt (hs.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hfd : HasFDerivAt (fun v ↦ F (p + A v)) ((fderiv ℝ F p).comp A)
      (0 : (ℝ × ℝ) × (ℝ × ℝ)) :=
    HasFDerivAt.comp (g := F) (f := fun v ↦ p + A v) (0 : (ℝ × ℝ) × (ℝ × ℝ)) hFd
      (A.hasFDerivAt.const_add p)
  -- In the directions `w` alone the slope has an inverse, by `hdet`.
  have hinv : (fderiv ℝ (fun v ↦ F (p + A v)) (0 : (ℝ × ℝ) × (ℝ × ℝ)) ∘L
      ContinuousLinearMap.inr ℝ (ℝ × ℝ) (ℝ × ℝ)).IsInvertible := by
    rw [hfd.fderiv]
    refine isInvertible_of_det_ne_zero _ (fderiv ℝ F p a) (fderiv ℝ F p b) (fun w ↦ ?_) hdet
    simp [hA]
  -- Solve `f (u, w) = 0` for `w = ψ u`.
  obtain ⟨ψ, hψ0, hψsm, hψeq⟩ : ∃ ψ : ℝ × ℝ → ℝ × ℝ, ψ 0 = 0 ∧
      (∀ᶠ x in 𝓝 (0 : ℝ × ℝ), ContDiffAt ℝ ∞ ψ x) ∧
      (∀ᶠ x in 𝓝 (0 : ℝ × ℝ), F (p + A (x, ψ x)) = F (p + A 0)) := by
    obtain ⟨ψ, h1, h2, h3, -⟩ :=
      Flows.exists_implicit_smooth (f := fun v ↦ F (p + A v)) hs' hf h0 hinv
    exact ⟨ψ, h1, h2, h3⟩
  have hσ0 : p + A (0, ψ 0) = p := by
    rw [hψ0]
    exact hA0
  -- The surface `σ u = p + A (u, ψ u)` stays in the region near `0`.
  have hσc : ContinuousAt (fun x : ℝ × ℝ ↦ p + A (x, ψ x)) 0 :=
    continuousAt_const.add
      (A.continuous.continuousAt.comp (continuousAt_id.prodMk hψsm.self_of_nhds.continuousAt))
  have hmem : ∀ᶠ x in 𝓝 (0 : ℝ × ℝ), p + A (x, ψ x) ∈ s :=
    hσc.eventually_mem (hs.mem_nhds (by rw [hσ0]; exact hp))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hψsm.and (hψeq.and hmem))
  refine ⟨δ, fun u ↦ p + A (u, ψ u), hδ, ?_, hσ0, ?_, ?_⟩
  · -- smooth
    intro u hu
    exact (contDiffAt_const.add
      (A.contDiff.contDiffAt.comp u (contDiffAt_id.prodMk (hball u hu).1))).contDiffWithinAt
  · -- in the region, and zeros of `F`
    intro u hu
    refine ⟨(hball u hu).2.2, ?_⟩
    have h := (hball u hu).2.1
    rw [hA0, hFp] at h
    exact h
  · -- the two directions at the start
    have hψd : HasFDerivAt ψ (fderiv ℝ ψ 0) 0 :=
      (hψsm.self_of_nhds.differentiableAt (by simp)).hasFDerivAt
    have hσd : HasFDerivAt (fun u : ℝ × ℝ ↦ p + A (u, ψ u))
        (A.comp ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod (fderiv ℝ ψ 0))) 0 :=
      (HasFDerivAt.comp (g := A) (f := fun u : ℝ × ℝ ↦ (u, ψ u)) (0 : ℝ × ℝ) A.hasFDerivAt
        ((hasFDerivAt_id (0 : ℝ × ℝ)).prodMk hψd)).const_add p
    rw [hσd.fderiv]
    refine ⟨(fderiv ℝ ψ 0 (1, 0)).1, (fderiv ℝ ψ 0 (1, 0)).2, (fderiv ℝ ψ 0 (0, 1)).1,
      (fderiv ℝ ψ 0 (0, 1)).2, ?_, ?_⟩ <;> simp [hA]

end GravityInLean.Turns
