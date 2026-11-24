/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Rim.FirstIntegral
public import GravityInLean.GeneralShape
public import Mathlib.Analysis.SpecialFunctions.Sqrt

import Mathlib.Tactic

/-!
# Two labels along the paths of light

Board item `task:rim-null-labels`. The time-distance part `-A dt² + 2 C dt dρ + B dρ²` of a
round table, with `D = A B + C² > 0`, has two directions of zero length at every point. Around
any point there are two smooth functions `u` and `v`, each constant along one of the two
directions, whose slopes at every point near it are independent. Said with the slopes of `u`:
`-B u_t² + 2 C u_t u_ρ + A u_ρ² = 0`, and the same for `v`.

On paper: one direction of zero length is given by the arrows `(B, -C + √D)` or
`(C + √D, A)` (they are parallel, and not both zero), the other by `(B, -C - √D)` or
`(C - √D, A)`. At the given point choose for each direction a form that is not zero there, and
take `exists_firstIntegral` (`FirstIntegral.lean`) for it. A function with slope `(a, b)` that
is constant along a direction of zero length `(n₁, n₂)` has `(a, b)` proportional to
`(n₂, -n₁)`, which gives the equation. The two slopes are independent at the point because the
two directions are different (`D > 0`), and so near the point.

In this file the two forms of a direction are handled together: with `σ` one of the two square
roots of `D`, a slope `(P, Q)` that is at right angles to one form that is not zero is at right
angles to both, `B P + (σ - C) Q = 0` and `(C + σ) P + A Q = 0` (`exists_label`). The equation
for the slopes and the independence then come from these two lines by algebra alone.

* `clm_apply_pair`, `clm_ne_zero`: a slope in the plane is given by its two entries.
* `dt_curry`, `dr_curry`: the two slopes of a function of the plane, written with two numbers.
* `exists_label`: one label, for one of the two square roots.
* `exists_nullLabels`: the two labels.
-/

@[expose] public section

namespace GravityInLean

open Set

open scoped ContDiff

namespace Rim

/-- A slope in the plane is given by its two entries: its value on the arrow `(x, y)` is `x`
times its value on `(1, 0)` plus `y` times its value on `(0, 1)`. -/
theorem clm_apply_pair (f : ℝ × ℝ →L[ℝ] ℝ) (x y : ℝ) :
    f (x, y) = x * f (1, 0) + y * f (0, 1) := by
  have h : ((x, y) : ℝ × ℝ) = x • ((1 : ℝ), (0 : ℝ)) + y • ((0 : ℝ), (1 : ℝ)) := by simp
  calc f (x, y) = f (x • ((1 : ℝ), (0 : ℝ)) + y • ((0 : ℝ), (1 : ℝ))) := by rw [← h]
    _ = x * f (1, 0) + y * f (0, 1) := by
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- A slope in the plane that is not zero has an entry that is not zero. -/
theorem clm_ne_zero {f : ℝ × ℝ →L[ℝ] ℝ} (h : f ≠ 0) : f (1, 0) ≠ 0 ∨ f (0, 1) ≠ 0 := by
  by_contra hcon
  have h1 : f (1, 0) = 0 := by
    by_contra h'
    exact hcon (Or.inl h')
  have h2 : f (0, 1) = 0 := by
    by_contra h'
    exact hcon (Or.inr h')
  refine h (ContinuousLinearMap.ext fun z ↦ ?_)
  rcases z with ⟨x, y⟩
  rw [clm_apply_pair f x y, h1, h2, mul_zero, mul_zero, add_zero]
  rfl

/-- The time slope of a function of the plane, written as a function of two numbers, is its
slope applied to the time direction. -/
theorem dt_curry {w : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (h : DifferentiableAt ℝ w x) :
    dt (Function.curry w) x.1 x.2 = fderiv ℝ w x (1, 0) :=
  (hasDerivAt_along_t (G := w) (t := x.1) (r := x.2) h).deriv

/-- The distance slope of a function of the plane, written as a function of two numbers, is its
slope applied to the distance direction. -/
theorem dr_curry {w : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (h : DifferentiableAt ℝ w x) :
    dr (Function.curry w) x.1 x.2 = fderiv ℝ w x (0, 1) :=
  (hasDerivAt_along_r (G := w) (t := x.1) (r := x.2) h).deriv

/-- Two numbers that are not both zero have squares whose sum is not zero. -/
theorem sq_add_sq_ne_zero_of {x y : ℝ} (h : x ≠ 0 ∨ y ≠ 0) : x ^ 2 + y ^ 2 ≠ 0 := by
  intro h0
  have hx : x ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  have hy : y ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  rcases h with h | h
  · exact h ((pow_eq_zero_iff two_ne_zero).mp hx)
  · exact h ((pow_eq_zero_iff two_ne_zero).mp hy)

/-- **One label along the paths of light.** Let `a`, `b`, `c` be smooth on an open set of the
plane, and `σ` a smooth square root of `a b + c²` that is nowhere zero there. Around any point
of the set there is a smooth function `u` whose slope `(P, Q)` is at right angles to both forms
of the direction of zero length that belongs to `σ`: `b P + (σ - c) Q = 0` and
`(c + σ) P + a Q = 0`. Its slope at the point is not zero. -/
theorem exists_label {a b c σ : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    (ha : ContDiffOn ℝ ∞ a W) (hb : ContDiffOn ℝ ∞ b W) (hc : ContDiffOn ℝ ∞ c W)
    (hσ : ContDiffOn ℝ ∞ σ W) (hsq : ∀ x ∈ W, σ x ^ 2 = a x * b x + c x * c x)
    (hσ0 : ∀ x ∈ W, σ x ≠ 0) {p : ℝ × ℝ} (hp : p ∈ W) :
    ∃ (u : ℝ × ℝ → ℝ) (N : Set (ℝ × ℝ)), IsOpen N ∧ p ∈ N ∧ N ⊆ W ∧ ContDiffOn ℝ ∞ u N ∧
      (∀ x ∈ N, b x * fderiv ℝ u x (1, 0) + (σ x - c x) * fderiv ℝ u x (0, 1) = 0) ∧
      (∀ x ∈ N, (c x + σ x) * fderiv ℝ u x (1, 0) + a x * fderiv ℝ u x (0, 1) = 0) ∧
      fderiv ℝ u p ≠ 0 := by
  by_cases h : b p ≠ 0 ∨ σ p - c p ≠ 0
  · -- The form `(b, σ - c)` is not zero at the point: follow it.
    obtain ⟨u, N₁, hN₁, hpN₁, hN₁W, hu, hflow, hne⟩ :=
      exists_firstIntegral hW hb (hσ.sub hc) hp h
    have hcont : ContinuousOn (fun x ↦ b x ^ 2 + (σ x - c x) ^ 2) N₁ :=
      ((hb.continuousOn.pow 2).add ((hσ.sub hc).continuousOn.pow 2)).mono hN₁W
    have hopen : IsOpen (N₁ ∩ {x | b x ^ 2 + (σ x - c x) ^ 2 ≠ 0}) :=
      hcont.isOpen_inter_preimage hN₁ isOpen_compl_singleton
    have hE1 : ∀ x ∈ N₁,
        b x * fderiv ℝ u x (1, 0) + (σ x - c x) * fderiv ℝ u x (0, 1) = 0 := fun x hx ↦ by
      have h1 : fderiv ℝ u x (b x, σ x - c x) = 0 := hflow x hx
      exact (clm_apply_pair _ _ _).symm.trans h1
    refine ⟨u, N₁ ∩ {x | b x ^ 2 + (σ x - c x) ^ 2 ≠ 0}, hopen,
      ⟨hpN₁, sq_add_sq_ne_zero_of h⟩, fun x hx ↦ hN₁W hx.1, hu.mono inter_subset_left,
      fun x hx ↦ hE1 x hx.1, fun x hx ↦ ?_, hne⟩
    have h1 := hE1 x hx.1
    have h2 : σ x ^ 2 = a x * b x + c x * c x := hsq x (hN₁W hx.1)
    have h3 : b x ^ 2 + (σ x - c x) ^ 2 ≠ 0 := hx.2
    have h4 : (b x ^ 2 + (σ x - c x) ^ 2)
        * ((c x + σ x) * fderiv ℝ u x (1, 0) + a x * fderiv ℝ u x (0, 1)) = 0 := by
      linear_combination (b x * (c x + σ x) + (σ x - c x) * a x) * h1
        + (-(b x * fderiv ℝ u x (0, 1)) + (σ x - c x) * fderiv ℝ u x (1, 0)) * h2
    exact (mul_eq_zero.mp h4).resolve_left h3
  · -- The form `(b, σ - c)` is zero at the point, so `(c + σ, a)` is not: follow that one.
    have hb0 : b p = 0 := by
      by_contra h'
      exact h (Or.inl h')
    have hσc : σ p - c p = 0 := by
      by_contra h'
      exact h (Or.inr h')
    have h' : c p + σ p ≠ 0 := by
      intro h0
      exact hσ0 p hp (by linarith)
    obtain ⟨u, N₁, hN₁, hpN₁, hN₁W, hu, hflow, hne⟩ :=
      exists_firstIntegral hW (hc.add hσ) ha hp (Or.inl h')
    have hcont : ContinuousOn (fun x ↦ (c x + σ x) ^ 2 + a x ^ 2) N₁ :=
      (((hc.add hσ).continuousOn.pow 2).add (ha.continuousOn.pow 2)).mono hN₁W
    have hopen : IsOpen (N₁ ∩ {x | (c x + σ x) ^ 2 + a x ^ 2 ≠ 0}) :=
      hcont.isOpen_inter_preimage hN₁ isOpen_compl_singleton
    have hE2 : ∀ x ∈ N₁,
        (c x + σ x) * fderiv ℝ u x (1, 0) + a x * fderiv ℝ u x (0, 1) = 0 := fun x hx ↦ by
      have h1 : fderiv ℝ u x (c x + σ x, a x) = 0 := hflow x hx
      exact (clm_apply_pair _ _ _).symm.trans h1
    refine ⟨u, N₁ ∩ {x | (c x + σ x) ^ 2 + a x ^ 2 ≠ 0}, hopen,
      ⟨hpN₁, sq_add_sq_ne_zero_of (Or.inl h')⟩, fun x hx ↦ hN₁W hx.1,
      hu.mono inter_subset_left, fun x hx ↦ ?_, fun x hx ↦ hE2 x hx.1, hne⟩
    have h1 := hE2 x hx.1
    have h2 : σ x ^ 2 = a x * b x + c x * c x := hsq x (hN₁W hx.1)
    have h3 : (c x + σ x) ^ 2 + a x ^ 2 ≠ 0 := hx.2
    have h4 : ((c x + σ x) ^ 2 + a x ^ 2)
        * (b x * fderiv ℝ u x (1, 0) + (σ x - c x) * fderiv ℝ u x (0, 1)) = 0 := by
      linear_combination ((c x + σ x) * b x + a x * (σ x - c x)) * h1
        + ((c x + σ x) * fderiv ℝ u x (0, 1) - a x * fderiv ℝ u x (1, 0)) * h2
    exact (mul_eq_zero.mp h4).resolve_left h3

/-- **Two labels along the paths of light.** Around any point of a box on which `A`, `B`, `C`
are smooth with `A B + C² > 0` there are two smooth functions `u`, `v` of time and distance
with `-B u_t² + 2 C u_t u_ρ + A u_ρ² = 0`, the same for `v`, and `u_t v_ρ - u_ρ v_t ≠ 0`. -/
theorem exists_nullLabels {A B C : ℝ → ℝ → ℝ} {J I : Set ℝ} (hJ : IsOpen J) (hI : IsOpen I)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (J ×ˢ I))
    (hB : ContDiffOn ℝ ∞ (Function.uncurry B) (J ×ˢ I))
    (hC : ContDiffOn ℝ ∞ (Function.uncurry C) (J ×ˢ I))
    (hdet : ∀ t ∈ J, ∀ ρ ∈ I, 0 < det2 A B C t ρ) {t₀ ρ₀ : ℝ} (ht₀ : t₀ ∈ J) (hρ₀ : ρ₀ ∈ I) :
    ∃ (u v : ℝ → ℝ → ℝ) (N : Set (ℝ × ℝ)), IsOpen N ∧ (t₀, ρ₀) ∈ N ∧ N ⊆ J ×ˢ I ∧
      ContDiffOn ℝ ∞ (Function.uncurry u) N ∧ ContDiffOn ℝ ∞ (Function.uncurry v) N ∧
      (∀ x ∈ N, -B x.1 x.2 * dt u x.1 x.2 ^ 2 + 2 * C x.1 x.2 * dt u x.1 x.2 * dr u x.1 x.2
        + A x.1 x.2 * dr u x.1 x.2 ^ 2 = 0) ∧
      (∀ x ∈ N, -B x.1 x.2 * dt v x.1 x.2 ^ 2 + 2 * C x.1 x.2 * dt v x.1 x.2 * dr v x.1 x.2
        + A x.1 x.2 * dr v x.1 x.2 ^ 2 = 0) ∧
      ∀ x ∈ N, dt u x.1 x.2 * dr v x.1 x.2 - dr u x.1 x.2 * dt v x.1 x.2 ≠ 0 := by
  have hW : IsOpen (J ×ˢ I) := hJ.prod hI
  have hp : (t₀, ρ₀) ∈ J ×ˢ I := ⟨ht₀, hρ₀⟩
  -- `D = A B + C²` is smooth and positive on the box, so its square root is smooth there.
  have hD : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ ↦ Function.uncurry A x * Function.uncurry B x
      + Function.uncurry C x * Function.uncurry C x) (J ×ˢ I) := (hA.mul hB).add (hC.mul hC)
  have hDpos : ∀ x ∈ J ×ˢ I, 0 < Function.uncurry A x * Function.uncurry B x
      + Function.uncurry C x * Function.uncurry C x := fun x hx ↦ hdet x.1 hx.1 x.2 hx.2
  obtain ⟨s, hs, hs0, hsq⟩ : ∃ s : ℝ × ℝ → ℝ, ContDiffOn ℝ ∞ s (J ×ˢ I) ∧
      (∀ x ∈ J ×ˢ I, s x ≠ 0) ∧ ∀ x ∈ J ×ˢ I, s x ^ 2 = Function.uncurry A x
        * Function.uncurry B x + Function.uncurry C x * Function.uncurry C x :=
    ⟨fun x ↦ √(Function.uncurry A x * Function.uncurry B x
        + Function.uncurry C x * Function.uncurry C x),
      hD.sqrt fun x hx ↦ (hDpos x hx).ne', fun x hx ↦ (Real.sqrt_pos.mpr (hDpos x hx)).ne',
      fun x hx ↦ Real.sq_sqrt (hDpos x hx).le⟩
  have hsq' : ∀ x ∈ J ×ˢ I, (-s x) ^ 2 = Function.uncurry A x * Function.uncurry B x
      + Function.uncurry C x * Function.uncurry C x := fun x hx ↦ by
    rw [neg_sq]
    exact hsq x hx
  -- One label for each of the two square roots.
  obtain ⟨u, N₁, hN₁, hpN₁, hN₁W, hu, hu1, hu2, hune⟩ :=
    exists_label hW hA hB hC hs hsq hs0 hp
  obtain ⟨v, N₂, hN₂, hpN₂, -, hv, hv1, hv2, hvne⟩ :=
    exists_label hW hA hB hC hs.neg hsq' (fun x hx ↦ neg_ne_zero.mpr (hs0 x hx)) hp
  have hud : ∀ x ∈ N₁, DifferentiableAt ℝ u x := fun x hx ↦
    (hu.contDiffAt (hN₁.mem_nhds hx)).differentiableAt (by simp)
  have hvd : ∀ x ∈ N₂, DifferentiableAt ℝ v x := fun x hx ↦
    (hv.contDiffAt (hN₂.mem_nhds hx)).differentiableAt (by simp)
  -- The four entries of the two slopes, written out with `A`, `B`, `C`.
  have hu1' : ∀ x ∈ N₁, B x.1 x.2 * fderiv ℝ u x (1, 0)
      + (s x - C x.1 x.2) * fderiv ℝ u x (0, 1) = 0 := hu1
  have hu2' : ∀ x ∈ N₁, (C x.1 x.2 + s x) * fderiv ℝ u x (1, 0)
      + A x.1 x.2 * fderiv ℝ u x (0, 1) = 0 := hu2
  have hv1' : ∀ x ∈ N₂, B x.1 x.2 * fderiv ℝ v x (1, 0)
      + (-s x - C x.1 x.2) * fderiv ℝ v x (0, 1) = 0 := hv1
  have hv2' : ∀ x ∈ N₂, (C x.1 x.2 + -s x) * fderiv ℝ v x (1, 0)
      + A x.1 x.2 * fderiv ℝ v x (0, 1) = 0 := hv2
  -- The two slopes are independent at the point.
  have hδp : fderiv ℝ u (t₀, ρ₀) (1, 0) * fderiv ℝ v (t₀, ρ₀) (0, 1)
      - fderiv ℝ u (t₀, ρ₀) (0, 1) * fderiv ℝ v (t₀, ρ₀) (1, 0) ≠ 0 := by
    intro hdep
    have h1 := hu1' _ hpN₁
    have h2 := hu2' _ hpN₁
    have h1' := hv1' _ hpN₂
    have h2' := hv2' _ hpN₂
    have h2s : 2 * s (t₀, ρ₀) ≠ 0 := mul_ne_zero two_ne_zero (hs0 _ hp)
    have e1 : 2 * s (t₀, ρ₀)
        * (fderiv ℝ u (t₀, ρ₀) (0, 1) * fderiv ℝ v (t₀, ρ₀) (1, 0)) = 0 := by
      linear_combination fderiv ℝ v (t₀, ρ₀) (1, 0) * h1 - fderiv ℝ u (t₀, ρ₀) (1, 0) * h1'
        - (s (t₀, ρ₀) + C t₀ ρ₀) * hdep
    have e2 : 2 * s (t₀, ρ₀)
        * (fderiv ℝ u (t₀, ρ₀) (0, 1) * fderiv ℝ v (t₀, ρ₀) (0, 1)) = 0 := by
      linear_combination fderiv ℝ v (t₀, ρ₀) (0, 1) * h1 - fderiv ℝ u (t₀, ρ₀) (0, 1) * h1'
        - B t₀ ρ₀ * hdep
    have e3 : 2 * s (t₀, ρ₀)
        * (fderiv ℝ u (t₀, ρ₀) (1, 0) * fderiv ℝ v (t₀, ρ₀) (1, 0)) = 0 := by
      linear_combination fderiv ℝ v (t₀, ρ₀) (1, 0) * h2 - fderiv ℝ u (t₀, ρ₀) (1, 0) * h2'
        + A t₀ ρ₀ * hdep
    have e4 : 2 * s (t₀, ρ₀)
        * (fderiv ℝ u (t₀, ρ₀) (1, 0) * fderiv ℝ v (t₀, ρ₀) (0, 1)) = 0 := by
      linear_combination fderiv ℝ v (t₀, ρ₀) (0, 1) * h2 - fderiv ℝ u (t₀, ρ₀) (0, 1) * h2'
        - (C t₀ ρ₀ - s (t₀, ρ₀)) * hdep
    rcases clm_ne_zero hune with hP | hQ <;> rcases clm_ne_zero hvne with hP' | hQ'
    · exact mul_ne_zero h2s (mul_ne_zero hP hP') e3
    · exact mul_ne_zero h2s (mul_ne_zero hP hQ') e4
    · exact mul_ne_zero h2s (mul_ne_zero hQ hP') e1
    · exact mul_ne_zero h2s (mul_ne_zero hQ hQ') e2
  -- So they are independent near the point: the slopes are continuous.
  have hcont : ContinuousOn (fun x ↦ fderiv ℝ u x (1, 0) * fderiv ℝ v x (0, 1)
      - fderiv ℝ u x (0, 1) * fderiv ℝ v x (1, 0)) (N₁ ∩ N₂) := by
    have hfu : ContinuousOn (fderiv ℝ u) (N₁ ∩ N₂) :=
      (hu.continuousOn_fderiv_of_isOpen hN₁ (by simp)).mono inter_subset_left
    have hfv : ContinuousOn (fderiv ℝ v) (N₁ ∩ N₂) :=
      (hv.continuousOn_fderiv_of_isOpen hN₂ (by simp)).mono inter_subset_right
    exact ((hfu.clm_apply continuousOn_const).mul (hfv.clm_apply continuousOn_const)).sub
      ((hfu.clm_apply continuousOn_const).mul (hfv.clm_apply continuousOn_const))
  have hopen : IsOpen ((N₁ ∩ N₂) ∩ {x | fderiv ℝ u x (1, 0) * fderiv ℝ v x (0, 1)
      - fderiv ℝ u x (0, 1) * fderiv ℝ v x (1, 0) ≠ 0}) :=
    hcont.isOpen_inter_preimage (hN₁.inter hN₂) isOpen_compl_singleton
  refine ⟨Function.curry u, Function.curry v, _, hopen, ⟨⟨hpN₁, hpN₂⟩, hδp⟩,
    fun x hx ↦ hN₁W hx.1.1, ?_, ?_, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · rw [Function.uncurry_curry]
    exact hu.mono fun x hx ↦ hx.1.1
  · rw [Function.uncurry_curry]
    exact hv.mono fun x hx ↦ hx.1.2
  · -- The equation for `u`, from the two lines its slope lies on.
    rw [dt_curry (hud x hx.1.1), dr_curry (hud x hx.1.1)]
    linear_combination fderiv ℝ u x (0, 1) * hu2' x hx.1.1
      - fderiv ℝ u x (1, 0) * hu1' x hx.1.1
  · -- The equation for `v`, the same way.
    rw [dt_curry (hvd x hx.1.2), dr_curry (hvd x hx.1.2)]
    linear_combination fderiv ℝ v x (0, 1) * hv2' x hx.1.2
      - fderiv ℝ v x (1, 0) * hv1' x hx.1.2
  · rw [dt_curry (hud x hx.1.1), dr_curry (hud x hx.1.1), dt_curry (hvd x hx.1.2),
      dr_curry (hvd x hx.1.2)]
    exact hx.2

end Rim

end GravityInLean
