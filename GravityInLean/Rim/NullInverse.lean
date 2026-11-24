/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Rim.FirstIntegral
public import GravityInLean.Join.Patch
public import GravityInLean.TwoSlopes

import Mathlib.Tactic

/-!
# Two new labels can be undone

Board item `task:rim-null-inverse`. Two smooth functions `u` and `v` of time and distance, whose
table of slopes at a point has a determinant that is not zero, are new labels near that point:
time and distance can be read back from them.

On paper: the map `(t, ρ) ↦ (u t ρ, v t ρ)` is smooth, and its slope at the point can be undone
because the determinant is not zero. By the inverse function theorem (`exists_localDiffeo`) it
has a smooth inverse near the point. Around the values of `u` and `v` at the point there is a
box, a product of two open stretches, on which that inverse lives; the old time and the old
distance, as functions of the new labels, are its two parts.

* `isUnit_of_det`: a linear map of the plane to itself whose two columns have a determinant that
  is not zero can be undone;
* `exists_inverse_labels`: the statement above.
-/

@[expose] public section

namespace GravityInLean

open Set

open scoped ContDiff Topology

namespace Rim

/-- A linear map of the plane to itself that sends `(1, 0)` to `(a, c)` and `(0, 1)` to
`(b, d)`, with `a d - b c` not zero, can be undone. -/
theorem isUnit_of_det {L : ℝ × ℝ →L[ℝ] ℝ × ℝ} {a b c d : ℝ} (hdet : a * d - b * c ≠ 0)
    (h1 : L (1, 0) = (a, c)) (h2 : L (0, 1) = (b, d)) : IsUnit L := by
  refine ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.2
    ((LinearMap.isUnit_iff_ker_eq_bot _).2 (LinearMap.ker_eq_bot'.2 fun w hw ↦ ?_))
  have hw' : L w = 0 := hw
  have hdecomp : w = w.1 • ((1 : ℝ), (0 : ℝ)) + w.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  have h := congrArg L hdecomp
  rw [hw', map_add, map_smul, map_smul, h1, h2] at h
  have e1 : 0 = w.1 * a + w.2 * b := by simpa using congrArg Prod.fst h
  have e2 : 0 = w.1 * c + w.2 * d := by simpa using congrArg Prod.snd h
  have hw1 : w.1 * (a * d - b * c) = 0 := by linear_combination (-d) * e1 + b * e2
  have hw2 : w.2 * (a * d - b * c) = 0 := by linear_combination c * e1 + (-a) * e2
  exact Prod.ext ((mul_eq_zero.1 hw1).resolve_right hdet)
    ((mul_eq_zero.1 hw2).resolve_right hdet)

/-- **Two new labels can be undone.** Let `u` and `v` be smooth functions of time and distance
on an open set `N`, and let the determinant of their table of slopes be not zero at a point of
`N`. Then there are a smaller open set `N'` around the point, two open stretches `J'` and `I'`,
each in one piece, and smooth functions `τ` and `ϱ` on `J' × I'` that give back time and
distance: `(u, v)` sends `N'` into `J' × I'`, `(τ, ϱ)` sends `J' × I'` into `N'`, and each undoes
the other. -/
theorem exists_inverse_labels {u v : ℝ → ℝ → ℝ} {N : Set (ℝ × ℝ)} (hN : IsOpen N)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) N) (hv : ContDiffOn ℝ ∞ (Function.uncurry v) N)
    {t₀ ρ₀ : ℝ} (h₀ : (t₀, ρ₀) ∈ N)
    (hdet : dt u t₀ ρ₀ * dr v t₀ ρ₀ - dr u t₀ ρ₀ * dt v t₀ ρ₀ ≠ 0) :
    ∃ (τ ϱ : ℝ → ℝ → ℝ) (J' I' : Set ℝ) (N' : Set (ℝ × ℝ)),
      IsOpen J' ∧ IsPreconnected J' ∧ IsOpen I' ∧ IsPreconnected I' ∧ IsOpen N' ∧
      (t₀, ρ₀) ∈ N' ∧ N' ⊆ N ∧
      ContDiffOn ℝ ∞ (Function.uncurry τ) (J' ×ˢ I') ∧
      ContDiffOn ℝ ∞ (Function.uncurry ϱ) (J' ×ˢ I') ∧
      (∀ a ∈ J', ∀ b ∈ I', (τ a b, ϱ a b) ∈ N' ∧ u (τ a b) (ϱ a b) = a ∧
        v (τ a b) (ϱ a b) = b) ∧
      ∀ x ∈ N', u x.1 x.2 ∈ J' ∧ v x.1 x.2 ∈ I' ∧ τ (u x.1 x.2) (v x.1 x.2) = x.1 ∧
        ϱ (u x.1 x.2) (v x.1 x.2) = x.2 := by
  -- the map `(t, ρ) ↦ (u t ρ, v t ρ)`
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ × ℝ → ℝ × ℝ,
      Λ = fun x ↦ (Function.uncurry u x, Function.uncurry v x) := ⟨_, rfl⟩
  have hΛapp : ∀ x : ℝ × ℝ, Λ x = (u x.1 x.2, v x.1 x.2) := fun x ↦ by
    rw [hΛ]
    rfl
  have hΛs : ContDiffOn ℝ ∞ Λ N := by
    rw [hΛ]
    exact hu.prodMk hv
  -- its slope at the point: the columns are the slopes along time and along distance
  have hUd : DifferentiableAt ℝ (Function.uncurry u) (t₀, ρ₀) :=
    (hu.contDiffAt (hN.mem_nhds h₀)).differentiableAt (by simp)
  have hVd : DifferentiableAt ℝ (Function.uncurry v) (t₀, ρ₀) :=
    (hv.contDiffAt (hN.mem_nhds h₀)).differentiableAt (by simp)
  have hfd : fderiv ℝ Λ (t₀, ρ₀)
      = (fderiv ℝ (Function.uncurry u) (t₀, ρ₀)).prod
        (fderiv ℝ (Function.uncurry v) (t₀, ρ₀)) := by
    rw [hΛ]
    exact (hUd.hasFDerivAt.prodMk hVd.hasFDerivAt).fderiv
  have hcol1 : fderiv ℝ Λ (t₀, ρ₀) (1, 0) = (dt u t₀ ρ₀, dt v t₀ ρ₀) := by
    rw [hfd, dt_eq_fderiv hUd, dt_eq_fderiv hVd]
    rfl
  have hcol2 : fderiv ℝ Λ (t₀, ρ₀) (0, 1) = (dr u t₀ ρ₀, dr v t₀ ρ₀) := by
    rw [hfd, dr_eq_fderiv hUd, dr_eq_fderiv hVd]
    rfl
  -- so the map can be undone near the point
  obtain ⟨e, he0, heN, heΛ, -, hesymm⟩ :=
    exists_localDiffeo hN hΛs h₀ (isUnit_of_det hdet hcol1 hcol2)
  -- a box around the values of `u` and `v` at the point, on which the inverse lives
  have htgt : (u t₀ ρ₀, v t₀ ρ₀) ∈ e.target := by
    have h := e.map_source he0
    rw [heΛ, hΛapp] at h
    exact h
  obtain ⟨J', I', hJ, hJc, hI, hIc, hu0, hv0, hbox⟩ :=
    Join.exists_intervals_of_eventually (P := fun q ↦ q ∈ e.target)
      (e.open_target.mem_nhds htgt)
  have hsub : J' ×ˢ I' ⊆ e.target := fun q hq ↦ hbox q.1 hq.1 q.2 hq.2
  -- the old time and the old distance are the two parts of the inverse
  have hτ : ContDiffOn ℝ ∞ (fun q ↦ (e.symm q).1) (J' ×ˢ I') :=
    contDiff_fst.comp_contDiffOn (hesymm.mono hsub)
  have hϱ : ContDiffOn ℝ ∞ (fun q ↦ (e.symm q).2) (J' ×ˢ I') :=
    contDiff_snd.comp_contDiffOn (hesymm.mono hsub)
  refine ⟨fun a b ↦ (e.symm (a, b)).1, fun a b ↦ (e.symm (a, b)).2, J', I',
    e.source ∩ e ⁻¹' (J' ×ˢ I'), hJ, hJc, hI, hIc, e.isOpen_inter_preimage (hJ.prod hI), ?_,
    fun x hx ↦ heN hx.1, hτ.congr fun q _ ↦ rfl, hϱ.congr fun q _ ↦ rfl, fun a ha b hb ↦ ?_,
    fun x hx ↦ ?_⟩
  · -- the point is in the smaller set
    refine ⟨he0, ?_⟩
    rw [mem_preimage, heΛ, hΛapp]
    exact ⟨hu0, hv0⟩
  · -- from the box back into the smaller set, and `u`, `v` there are the labels of the box
    have hq : (a, b) ∈ e.target := hbox a ha b hb
    have hmem : e.symm (a, b) ∈ e.source ∩ e ⁻¹' (J' ×ˢ I') := by
      refine ⟨e.map_target hq, ?_⟩
      rw [mem_preimage, e.right_inv hq]
      exact ⟨ha, hb⟩
    have h : (u (e.symm (a, b)).1 (e.symm (a, b)).2, v (e.symm (a, b)).1 (e.symm (a, b)).2)
        = (a, b) := by
      rw [← hΛapp (e.symm (a, b)), ← heΛ (e.symm (a, b))]
      exact e.right_inv hq
    exact ⟨hmem, congrArg Prod.fst h, congrArg Prod.snd h⟩
  · -- from the smaller set into the box, and the inverse gives back time and distance
    have hx2 : (u x.1 x.2, v x.1 x.2) ∈ J' ×ˢ I' := by
      rw [← hΛapp x, ← heΛ x]
      exact hx.2
    have h : e.symm (u x.1 x.2, v x.1 x.2) = x := by
      rw [← hΛapp x, ← heΛ x]
      exact e.left_inv hx.1
    exact ⟨hx2.1, hx2.2, congrArg Prod.fst h, congrArg Prod.snd h⟩

end Rim

end GravityInLean
