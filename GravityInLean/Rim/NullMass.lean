/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.BirkhoffGeneral

import Mathlib.Tactic

/-!
# The mass function is the same in the labels along the paths of light

Board item `task:rim-null-mass`. A helper for `Rim/NullForm.lean`. Let `u` and `v` be new labels
for time and distance, in which the time-distance part `-A dt² + 2 C dt dρ + B dρ²` reads
`2 F du dv`, and let the size of the spheres be `S = S' ∘ (u, v)`. Then the mass function of the
round shape `genG zero2 zero2 F S'`, taken at `(u, v)`, is the mass function of `genG A B C S`.

On paper: `massFn = √S / 2 · (1 - radiusSlopeSq)` and
`radiusSlopeSq = sizeSlopeSq / (4 · S · det2)`. With `Δ = u_t v_ρ - u_ρ v_t` the chain rule gives
`sizeSlopeSq A B C S = 2 F S'_u S'_v Δ²` and `det2 A B C = F² Δ²`, while in the new labels
`sizeSlopeSq = 2 F S'_u S'_v` and `det2 = F²`. The factor `Δ²` cancels.
-/

@[expose] public section

namespace GravityInLean

open Filter Topology

namespace Rim

/-- A slope read on the arrow `(x, y)` is `x` times the slope along the first label plus `y`
times the slope along the second. -/
theorem clm_apply_two (L : ℝ × ℝ →L[ℝ] ℝ) (x y : ℝ) :
    L (x, y) = L (1, 0) * x + L (0, 1) * y := by
  have h : (x, y) = x • ((1 : ℝ), (0 : ℝ)) + y • ((0 : ℝ), (1 : ℝ)) := by simp
  conv_lhs => rw [h]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- **The chain rule along a path.** If the two labels `a`, `b` move with the slopes `a'`, `b'`,
then `S' (a, b)` moves with the slope `S'_u · a' + S'_v · b'`. -/
theorem hasDerivAt_comp_two {S' : ℝ → ℝ → ℝ} {a b : ℝ → ℝ} {a' b' x : ℝ}
    (ha : HasDerivAt a a' x) (hb : HasDerivAt b b' x)
    (hS' : DifferentiableAt ℝ (Function.uncurry S') (a x, b x)) :
    HasDerivAt (fun s => S' (a s) (b s)) (dt S' (a x) (b x) * a' + dr S' (a x) (b x) * b') x := by
  have h1 : HasDerivAt (fun s => (a s, b s)) (a', b') x := ha.prodMk hb
  have h2 : HasDerivAt (fun s => S' (a s) (b s))
      (fderiv ℝ (Function.uncurry S') (a x, b x) (a', b')) x :=
    HasFDerivAt.comp_hasDerivAt (l := Function.uncurry S') (f := fun s => (a s, b s)) (x := x)
      hS'.hasFDerivAt h1
  refine h2.congr_deriv ?_
  rw [clm_apply_two, dt_eq_fderiv hS', dr_eq_fderiv hS']

/-- The slope along time of one of the labels, as the library's slope of a function of time. -/
theorem hasDerivAt_dt_of_slope {u : ℝ → ℝ → ℝ} {t ρ : ℝ}
    (hu : DifferentiableAt ℝ (Function.uncurry u) (t, ρ)) :
    HasDerivAt (fun s => u s ρ) (dt u t ρ) t := by
  rw [dt_eq_fderiv hu]
  exact hasDerivAt_along_t hu

/-- The slope along distance of one of the labels, as the library's slope of a function of
distance. -/
theorem hasDerivAt_dr_of_slope {u : ℝ → ℝ → ℝ} {t ρ : ℝ}
    (hu : DifferentiableAt ℝ (Function.uncurry u) (t, ρ)) :
    HasDerivAt (fun s => u t s) (dr u t ρ) ρ := by
  rw [dr_eq_fderiv hu]
  exact hasDerivAt_along_r hu

/-- **The chain rule for the size of the spheres, along time.** Where `S = S' ∘ (u, v)` near
`(t, ρ)`, the slope of `S` along time is `S'_u · u_t + S'_v · v_t`. -/
theorem dt_eq_of_comp {S S' u v : ℝ → ℝ → ℝ} {t ρ : ℝ}
    (hu : DifferentiableAt ℝ (Function.uncurry u) (t, ρ))
    (hv : DifferentiableAt ℝ (Function.uncurry v) (t, ρ))
    (hS' : DifferentiableAt ℝ (Function.uncurry S') (u t ρ, v t ρ))
    (hSeq : ∀ᶠ x in 𝓝 (t, ρ), S x.1 x.2 = S' (u x.1 x.2) (v x.1 x.2)) :
    dt S t ρ = dt S' (u t ρ) (v t ρ) * dt u t ρ + dr S' (u t ρ) (v t ρ) * dt v t ρ := by
  have ht : Tendsto (fun s : ℝ => (s, ρ)) (𝓝 t) (𝓝 (t, ρ)) :=
    tendsto_id.prodMk_nhds tendsto_const_nhds
  have h1 : (fun s => S s ρ) =ᶠ[𝓝 t] fun s => S' (u s ρ) (v s ρ) := ht.eventually hSeq
  have h2 : HasDerivAt (fun s => S' (u s ρ) (v s ρ))
      (dt S' (u t ρ) (v t ρ) * dt u t ρ + dr S' (u t ρ) (v t ρ) * dt v t ρ) t :=
    hasDerivAt_comp_two (a := fun s => u s ρ) (b := fun s => v s ρ)
      (hasDerivAt_dt_of_slope hu) (hasDerivAt_dt_of_slope hv) hS'
  exact (h2.congr_of_eventuallyEq h1).deriv

/-- **The chain rule for the size of the spheres, along distance.** Where `S = S' ∘ (u, v)` near
`(t, ρ)`, the slope of `S` along distance is `S'_u · u_ρ + S'_v · v_ρ`. -/
theorem dr_eq_of_comp {S S' u v : ℝ → ℝ → ℝ} {t ρ : ℝ}
    (hu : DifferentiableAt ℝ (Function.uncurry u) (t, ρ))
    (hv : DifferentiableAt ℝ (Function.uncurry v) (t, ρ))
    (hS' : DifferentiableAt ℝ (Function.uncurry S') (u t ρ, v t ρ))
    (hSeq : ∀ᶠ x in 𝓝 (t, ρ), S x.1 x.2 = S' (u x.1 x.2) (v x.1 x.2)) :
    dr S t ρ = dt S' (u t ρ) (v t ρ) * dr u t ρ + dr S' (u t ρ) (v t ρ) * dr v t ρ := by
  have ht : Tendsto (fun s : ℝ => (t, s)) (𝓝 ρ) (𝓝 (t, ρ)) :=
    tendsto_const_nhds.prodMk_nhds tendsto_id
  have h1 : (fun s => S t s) =ᶠ[𝓝 ρ] fun s => S' (u t s) (v t s) := ht.eventually hSeq
  have h2 : HasDerivAt (fun s => S' (u t s) (v t s))
      (dt S' (u t ρ) (v t ρ) * dr u t ρ + dr S' (u t ρ) (v t ρ) * dr v t ρ) ρ :=
    hasDerivAt_comp_two (a := fun s => u t s) (b := fun s => v t s)
      (hasDerivAt_dr_of_slope hu) (hasDerivAt_dr_of_slope hv) hS'
  exact (h2.congr_of_eventuallyEq h1).deriv

/-- **The mass function is the same in the labels along the paths of light.** If the
time-distance part `-A dt² + 2 C dt dρ + B dρ²` is `2 F du dv` at the point, the size of the
spheres is `S = S' ∘ (u, v)` near the point, and `(u, v)` are honest labels there
(`u_t v_ρ - u_ρ v_t ≠ 0`), then the mass function of the shape `2 F du dv` with size `S'`, at
`(u, v)`, is the mass function of the shape `A`, `B`, `C` with size `S`. -/
theorem massFn_null_eq {A B C S F S' u v : ℝ → ℝ → ℝ} {t ρ : ℝ}
    (hu : DifferentiableAt ℝ (Function.uncurry u) (t, ρ))
    (hv : DifferentiableAt ℝ (Function.uncurry v) (t, ρ))
    (hS' : DifferentiableAt ℝ (Function.uncurry S') (u t ρ, v t ρ))
    (hSeq : ∀ᶠ x in 𝓝 (t, ρ), S x.1 x.2 = S' (u x.1 x.2) (v x.1 x.2))
    (hA : A t ρ = -2 * F (u t ρ) (v t ρ) * (dt u t ρ * dt v t ρ))
    (hC : C t ρ = F (u t ρ) (v t ρ) * (dt u t ρ * dr v t ρ + dr u t ρ * dt v t ρ))
    (hB : B t ρ = 2 * F (u t ρ) (v t ρ) * (dr u t ρ * dr v t ρ))
    (hdet : dt u t ρ * dr v t ρ - dr u t ρ * dt v t ρ ≠ 0) :
    massFn zero2 zero2 F S' (u t ρ) (v t ρ) = massFn A B C S t ρ := by
  have hS0 : S t ρ = S' (u t ρ) (v t ρ) := hSeq.self_of_nhds
  have hSt := dt_eq_of_comp hu hv hS' hSeq
  have hSρ := dr_eq_of_comp hu hv hS' hSeq
  have hnum : sizeSlopeSq A B C S t ρ =
      2 * F (u t ρ) (v t ρ) * (dt S' (u t ρ) (v t ρ) * dr S' (u t ρ) (v t ρ)) *
        (dt u t ρ * dr v t ρ - dr u t ρ * dt v t ρ) ^ 2 := by
    unfold sizeSlopeSq
    rw [hSt, hSρ, hA, hB, hC]
    ring
  have hden : det2 A B C t ρ =
      F (u t ρ) (v t ρ) ^ 2 * (dt u t ρ * dr v t ρ - dr u t ρ * dt v t ρ) ^ 2 := by
    unfold det2
    rw [hA, hB, hC]
    ring
  have hnum' : sizeSlopeSq zero2 zero2 F S' (u t ρ) (v t ρ) =
      2 * F (u t ρ) (v t ρ) * (dt S' (u t ρ) (v t ρ) * dr S' (u t ρ) (v t ρ)) := by
    unfold sizeSlopeSq zero2
    ring
  have hden' : det2 zero2 zero2 F (u t ρ) (v t ρ) = F (u t ρ) (v t ρ) ^ 2 := by
    unfold det2 zero2
    ring
  have hrs : radiusSlopeSq A B C S t ρ = radiusSlopeSq zero2 zero2 F S' (u t ρ) (v t ρ) := by
    unfold radiusSlopeSq
    rw [hnum, hden, hnum', hden', ← hS0,
      show 4 * (S t ρ * (F (u t ρ) (v t ρ) ^ 2 *
          (dt u t ρ * dr v t ρ - dr u t ρ * dt v t ρ) ^ 2)) =
        4 * (S t ρ * F (u t ρ) (v t ρ) ^ 2) *
          (dt u t ρ * dr v t ρ - dr u t ρ * dt v t ρ) ^ 2 by ring,
      mul_div_mul_right _ _ (pow_ne_zero 2 hdet)]
  unfold massFn
  rw [hrs, hS0]

end Rim

end GravityInLean
