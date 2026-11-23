/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.TwoSlopes
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.Analysis.SpecialFunctions.Sqrt

import Mathlib.Tactic

/-!
# A function with two given slopes

To change coordinates one needs new labels, for example a new time `T(t, ρ)`. Often only its two
slopes are known: `P` along time and `Q` along distance. Such a `T` exists exactly when the slopes
fit together: the slope of `P` along distance has to equal the slope of `Q` along time.

* `exists_potential`: on a rectangle of times and distances, two differentiable functions `P` and
  `Q` with `∂P/∂ρ = ∂Q/∂t` are the two slopes of one differentiable function `T`.

This is Poincaré's lemma. The standard library proves it for open convex sets
(`Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric`); this file only translates it into the
two slopes used here.

Also here: the slope of a square root, in the form that is convenient later
(`hasDerivAt_sqrt_of_pos`), and the chain rule for a path through new labels
(`hasDerivAt_comp_path`).
-/

@[expose] public section

namespace GravityInLean

open Filter Topology Set

/-- Every linear function of two numbers is fixed by its values on the two basic steps. -/
theorem clm_apply_pair (L : ℝ × ℝ →L[ℝ] ℝ) (v : ℝ × ℝ) :
    L v = v.1 * L (1, 0) + v.2 * L (0, 1) := by
  have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  conv_lhs => rw [hv]
  simp only [map_add, map_smul, smul_eq_mul]

/-- **A function with two given slopes** (Poincaré's lemma on a rectangle). If `P` and `Q` are
differentiable on a rectangle of times and distances and the slope of `P` along distance equals
the slope of `Q` along time, there is a differentiable function `T` with slope `P` along time and
slope `Q` along distance. -/
theorem exists_potential {P Q : ℝ → ℝ → ℝ} {J I : Set ℝ} (hJ : IsOpen J)
    (hJc : IsPreconnected J) (hI : IsOpen I) (hIc : IsPreconnected I)
    (hP : ∀ t ∈ J, ∀ ρ ∈ I, DifferentiableAt ℝ (Function.uncurry P) (t, ρ))
    (hQ : ∀ t ∈ J, ∀ ρ ∈ I, DifferentiableAt ℝ (Function.uncurry Q) (t, ρ))
    (hclosed : ∀ t ∈ J, ∀ ρ ∈ I, dr P t ρ = dt Q t ρ) :
    ∃ T : ℝ → ℝ → ℝ, ∀ t ∈ J, ∀ ρ ∈ I,
      DifferentiableAt ℝ (Function.uncurry T) (t, ρ) ∧ dt T t ρ = P t ρ ∧ dr T t ρ = Q t ρ := by
  -- The two slopes, bundled as the library wants them.
  let ω : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) := fun q =>
    Function.uncurry P q • ContinuousLinearMap.fst ℝ ℝ ℝ
      + Function.uncurry Q q • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hconv : Convex ℝ (J ×ˢ I) := hJc.convex.prod hIc.convex
  have hopen : IsOpen (J ×ˢ I) := hJ.prod hI
  have hωd : ∀ q ∈ J ×ˢ I, HasFDerivAt ω
      ((fderiv ℝ (Function.uncurry P) q).smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ)
        + (fderiv ℝ (Function.uncurry Q) q).smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ)) q := by
    rintro ⟨t, ρ⟩ ⟨ht, hρ⟩
    exact ((hP t ht ρ hρ).hasFDerivAt.smul_const _).add ((hQ t ht ρ hρ).hasFDerivAt.smul_const _)
  have hsymm : ∀ q ∈ J ×ˢ I, ∀ v w, fderiv ℝ ω q v w = fderiv ℝ ω q w v := by
    rintro ⟨t, ρ⟩ ⟨ht, hρ⟩ v w
    have hc := hclosed t ht ρ hρ
    rw [dr_eq_fderiv (hP t ht ρ hρ), dt_eq_fderiv (hQ t ht ρ hρ)] at hc
    have e : ∀ a b : ℝ × ℝ, fderiv ℝ ω (t, ρ) a b
        = fderiv ℝ (Function.uncurry P) (t, ρ) a * b.1
          + fderiv ℝ (Function.uncurry Q) (t, ρ) a * b.2 := by
      intro a b
      rw [(hωd (t, ρ) ⟨ht, hρ⟩).fderiv]
      simp
    rw [e v w, e w v, clm_apply_pair (fderiv ℝ (Function.uncurry P) (t, ρ)) v,
      clm_apply_pair (fderiv ℝ (Function.uncurry P) (t, ρ)) w,
      clm_apply_pair (fderiv ℝ (Function.uncurry Q) (t, ρ)) v,
      clm_apply_pair (fderiv ℝ (Function.uncurry Q) (t, ρ)) w]
    linear_combination (v.2 * w.1 - v.1 * w.2) * hc
  obtain ⟨f, hf⟩ := hconv.exists_forall_hasFDerivAt_of_fderiv_symmetric hopen
    (fun q hq => (hωd q hq).differentiableAt.differentiableWithinAt) hsymm
  refine ⟨fun t ρ => f (t, ρ), fun t ht ρ hρ => ?_⟩
  have hfd : HasFDerivAt f (ω (t, ρ)) (t, ρ) := hf (t, ρ) ⟨ht, hρ⟩
  have hdiff : DifferentiableAt ℝ f (t, ρ) := hfd.differentiableAt
  refine ⟨hdiff, ?_, ?_⟩
  · have h1 : dt (fun t ρ => f (t, ρ)) t ρ = fderiv ℝ f (t, ρ) (1, 0) :=
      (hasDerivAt_along_t hdiff).deriv
    rw [h1, hfd.fderiv]
    simp [ω]
  · have h1 : dr (fun t ρ => f (t, ρ)) t ρ = fderiv ℝ f (t, ρ) (0, 1) :=
      (hasDerivAt_along_r hdiff).deriv
    rw [h1, hfd.fderiv]
    simp [ω]

/-- The slope of a square root, written with the square root itself as a factor. -/
theorem hasDerivAt_sqrt_of_pos {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) (hx : 0 < f x) :
    HasDerivAt (fun y => √(f y)) (√(f x) * (f' / (2 * f x))) x := by
  refine (hf.sqrt hx.ne').congr_deriv ?_
  have h2 : √(f x) ^ 2 = f x := Real.sq_sqrt hx.le
  have h0 : √(f x) ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hx0 : f x ≠ 0 := hx.ne'
  field_simp
  linear_combination -f' * h2

/-- **The chain rule for new labels.** If a path moves through times `a(τ)` and distances `b(τ)`,
a differentiable label `T` changes along it by its time slope times the path's speed in time,
plus its distance slope times the path's speed in distance. -/
theorem hasDerivAt_comp_path {T : ℝ → ℝ → ℝ} {a b : ℝ → ℝ} {a' b' τ : ℝ}
    (hT : DifferentiableAt ℝ (Function.uncurry T) (a τ, b τ)) (ha : HasDerivAt a a' τ)
    (hb : HasDerivAt b b' τ) :
    HasDerivAt (fun s => T (a s) (b s)) (dt T (a τ) (b τ) * a' + dr T (a τ) (b τ) * b') τ := by
  have hpath : HasDerivAt (fun s => (a s, b s)) (a', b') τ := ha.prodMk hb
  have h := HasFDerivAt.comp_hasDerivAt (l := Function.uncurry T) (f := fun s => (a s, b s))
    (x := τ) hT.hasFDerivAt hpath
  refine h.congr_deriv ?_
  rw [clm_apply_pair, ← dt_eq_fderiv hT, ← dr_eq_fderiv hT]
  ring

end GravityInLean
