/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.GeneralShape

import Mathlib.Tactic

/-!
# The curvature of the general round shape

For the length measure `-A dt² + 2C dt dρ + B dρ² + S (dθ² + sin²θ dφ²)` of `GeneralShape.lean`,
this file computes all sixteen parts of the curvature from the general definitions.

**The formulas.** Two ingredients appear:

* `curv2`: the curvature of the time-distance part by itself, a surface with one time and one
  space direction (Gauss's formula for the curvature of a surface);
* `hessTT`, `hessTR`, `hessRR`: how the sphere size `S` bends, that is its second slopes,
  corrected by the connection.

With them the four parts that are not zero by themselves read

* time-time: `-K·A - hessTT / S + S_t² / (2S²)`
* time-distance: `K·C - hessTR / S + S_t S_ρ / (2S²)`
* distance-distance: `K·B - hessRR / S + S_ρ² / (2S²)`
* around the mass: `1 - (A·hessRR + 2C·hessTR - B·hessTT) / (2 (AB + C²))`

**What is proved here.**

* `ricci_gen_tt`, `_tr`, `_rt`, `_rr`, `_θθ`, `_φφ`, `_offdiag`: the general formula for the
  curvature gives exactly these four formulas; every other part is zero or a multiple of them.
* `gen_ricciFlat_iff`: so Einstein's equation for empty space, all sixteen parts of it, holds at
  a point exactly when the four formulas vanish there.
* `sizeEquations`: in empty space the size of the spheres obeys three equations that fix its
  second slopes in terms of its first ones. In the textbooks' notation, with `S = R²`, they read
  `∇∇R = (m / R²) · h`. Everything in `BirkhoffGeneral.lean` follows from these three.

**What is still assumed.** As before: curvature is defined by the classic coordinate formulas,
the poles are left out, and the four functions have to be twice smoothly differentiable.
-/

@[expose] public section

namespace GravityInLean

open Real Filter Topology

variable {A B C S : ℝ → ℝ → ℝ}

/-! ## Slopes of the pieces -/

section Slopes

variable {t ρ : ℝ}

theorem hasDerivAt_det2_t (hA : TwiceSmooth A t ρ) (hB : TwiceSmooth B t ρ)
    (hC : TwiceSmooth C t ρ) :
    HasDerivAt (fun s => det2 A B C s ρ)
      (dt A t ρ * B t ρ + A t ρ * dt B t ρ + (dt C t ρ * C t ρ + C t ρ * dt C t ρ)) t :=
  (hA.slopeT.mul hB.slopeT).add (hC.slopeT.mul hC.slopeT)

theorem hasDerivAt_det2_r (hA : TwiceSmooth A t ρ) (hB : TwiceSmooth B t ρ)
    (hC : TwiceSmooth C t ρ) :
    HasDerivAt (fun s => det2 A B C t s)
      (dr A t ρ * B t ρ + A t ρ * dr B t ρ + (dr C t ρ * C t ρ + C t ρ * dr C t ρ)) ρ :=
  (hA.slopeR.mul hB.slopeR).add (hC.slopeR.mul hC.slopeR)

theorem hasDerivAt_n000_r (hA : TwiceSmooth A t ρ) (hB : TwiceSmooth B t ρ)
    (hC : TwiceSmooth C t ρ) :
    HasDerivAt (fun s => n000 A B C t s)
      (dr B t ρ * dt A t ρ + B t ρ * dr (dt A) t ρ
        + (dr C t ρ * (2 * dt C t ρ + dr A t ρ)
          + C t ρ * (2 * dr (dt C) t ρ + dr (dr A) t ρ))) ρ :=
  (hB.slopeR.mul hA.slopeTR).add (hC.slopeR.mul ((hC.slopeTR.const_mul 2).add hA.slopeRR))

theorem hasDerivAt_n001_t (hA : TwiceSmooth A t ρ) (hB : TwiceSmooth B t ρ)
    (hC : TwiceSmooth C t ρ) :
    HasDerivAt (fun s => n001 A B C s ρ)
      (dt B t ρ * dr A t ρ + B t ρ * dt (dr A) t ρ
        + (dt C t ρ * dt B t ρ + C t ρ * dt (dt B) t ρ)) t :=
  (hB.slopeT.mul hA.slopeRT).add (hC.slopeT.mul hB.slopeTT)

theorem hasDerivAt_n001_r (hA : TwiceSmooth A t ρ) (hB : TwiceSmooth B t ρ)
    (hC : TwiceSmooth C t ρ) :
    HasDerivAt (fun s => n001 A B C t s)
      (dr B t ρ * dr A t ρ + B t ρ * dr (dr A) t ρ
        + (dr C t ρ * dt B t ρ + C t ρ * dr (dt B) t ρ)) ρ :=
  (hB.slopeR.mul hA.slopeRR).add (hC.slopeR.mul hB.slopeTR)

theorem hasDerivAt_n011_t (hB : TwiceSmooth B t ρ) (hC : TwiceSmooth C t ρ) :
    HasDerivAt (fun s => n011 B C s ρ)
      (dt C t ρ * dr B t ρ + C t ρ * dt (dr B) t ρ
        - (dt B t ρ * (2 * dr C t ρ - dt B t ρ)
          + B t ρ * (2 * dt (dr C) t ρ - dt (dt B) t ρ))) t :=
  (hC.slopeT.mul hB.slopeRT).sub (hB.slopeT.mul ((hC.slopeRT.const_mul 2).sub hB.slopeTT))

theorem hasDerivAt_n100_r (hA : TwiceSmooth A t ρ) (hC : TwiceSmooth C t ρ) :
    HasDerivAt (fun s => n100 A C t s)
      (dr A t ρ * (2 * dt C t ρ + dr A t ρ) + A t ρ * (2 * dr (dt C) t ρ + dr (dr A) t ρ)
        - (dr C t ρ * dt A t ρ + C t ρ * dr (dt A) t ρ)) ρ :=
  (hA.slopeR.mul ((hC.slopeTR.const_mul 2).add hA.slopeRR)).sub (hC.slopeR.mul hA.slopeTR)

theorem hasDerivAt_n101_t (hA : TwiceSmooth A t ρ) (hB : TwiceSmooth B t ρ)
    (hC : TwiceSmooth C t ρ) :
    HasDerivAt (fun s => n101 A B C s ρ)
      (dt A t ρ * dt B t ρ + A t ρ * dt (dt B) t ρ
        - (dt C t ρ * dr A t ρ + C t ρ * dt (dr A) t ρ)) t :=
  (hA.slopeT.mul hB.slopeTT).sub (hC.slopeT.mul hA.slopeRT)

theorem hasDerivAt_n101_r (hA : TwiceSmooth A t ρ) (hB : TwiceSmooth B t ρ)
    (hC : TwiceSmooth C t ρ) :
    HasDerivAt (fun s => n101 A B C t s)
      (dr A t ρ * dt B t ρ + A t ρ * dr (dt B) t ρ
        - (dr C t ρ * dr A t ρ + C t ρ * dr (dr A) t ρ)) ρ :=
  (hA.slopeR.mul hB.slopeTR).sub (hC.slopeR.mul hA.slopeRR)

theorem hasDerivAt_n111_t (hA : TwiceSmooth A t ρ) (hB : TwiceSmooth B t ρ)
    (hC : TwiceSmooth C t ρ) :
    HasDerivAt (fun s => n111 A B C s ρ)
      (dt A t ρ * dr B t ρ + A t ρ * dt (dr B) t ρ
        + (dt C t ρ * (2 * dr C t ρ - dt B t ρ)
          + C t ρ * (2 * dt (dr C) t ρ - dt (dt B) t ρ))) t :=
  (hA.slopeT.mul hB.slopeRT).add (hC.slopeT.mul ((hC.slopeRT.const_mul 2).sub hB.slopeTT))

theorem hasDerivAt_m0_t (hB : TwiceSmooth B t ρ) (hC : TwiceSmooth C t ρ)
    (hS : TwiceSmooth S t ρ) :
    HasDerivAt (fun s => m0 B C S s ρ)
      (dt B t ρ * dt S t ρ + B t ρ * dt (dt S) t ρ
        - (dt C t ρ * dr S t ρ + C t ρ * dt (dr S) t ρ)) t :=
  (hB.slopeT.mul hS.slopeTT).sub (hC.slopeT.mul hS.slopeRT)

theorem hasDerivAt_m1_r (hA : TwiceSmooth A t ρ) (hC : TwiceSmooth C t ρ)
    (hS : TwiceSmooth S t ρ) :
    HasDerivAt (fun s => m1 A C S t s)
      (-(dr C t ρ * dt S t ρ + C t ρ * dr (dt S) t ρ
        + (dr A t ρ * dr S t ρ + A t ρ * dr (dr S) t ρ))) ρ :=
  ((hC.slopeR.mul hS.slopeTR).add (hA.slopeR.mul hS.slopeRR)).neg

/-- `S / S` does not change in time, wherever `S` is not zero. -/
theorem dt_oneS (hS : TwiceSmooth S t ρ) (h0 : S t ρ ≠ 0) : dt (oneS S) t ρ = 0 := by
  refine deriv_eq_zero_of_eventually_const (c := 1) ?_
  filter_upwards [hS.slopeT.continuousAt.eventually_ne h0] with s hs
  exact inv_mul_cancel₀ hs

/-- `S / S` does not change with distance, wherever `S` is not zero. -/
theorem dr_oneS (hS : TwiceSmooth S t ρ) (h0 : S t ρ ≠ 0) : dr (oneS S) t ρ = 0 := by
  refine deriv_eq_zero_of_eventually_const (c := 1) ?_
  filter_upwards [hS.slopeR.continuousAt.eventually_ne h0] with s hs
  exact inv_mul_cancel₀ hs

end Slopes

/-! ## The formulas -/

/-- How the sphere size bends along time: its second slope, corrected by the connection. -/
noncomputable def hessTT (A B C S : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ :=
  dt (dt S) t ρ - half (n000 A B C) (det2 A B C) t ρ * dt S t ρ
    - half (n100 A C) (det2 A B C) t ρ * dr S t ρ

/-- How the sphere size bends along time and distance together. -/
noncomputable def hessTR (A B C S : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ :=
  dr (dt S) t ρ - half (n001 A B C) (det2 A B C) t ρ * dt S t ρ
    - half (n101 A B C) (det2 A B C) t ρ * dr S t ρ

/-- How the sphere size bends along distance. -/
noncomputable def hessRR (A B C S : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ :=
  dr (dr S) t ρ - half (n011 B C) (det2 A B C) t ρ * dt S t ρ
    - half (n111 A B C) (det2 A B C) t ρ * dr S t ρ

/-- The curvature of the time-distance part by itself: Gauss's curvature of the surface with
length measure `-A dt² + 2C dt dρ + B dρ²`. -/
noncomputable def curv2 (A B C : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ :=
  (dt (dt B) t ρ - dr (dr A) t ρ - 2 * dr (dt C) t ρ) / (2 * det2 A B C t ρ)
    + (A t ρ * (dr A t ρ * dr B t ρ + 2 * dr B t ρ * dt C t ρ - dt B t ρ ^ 2)
        + B t ρ * (dr A t ρ ^ 2 - dt A t ρ * dt B t ρ + 2 * dt A t ρ * dr C t ρ)
        + C t ρ * (dr A t ρ * dt B t ρ + 2 * dr A t ρ * dr C t ρ - dt A t ρ * dr B t ρ
            - 2 * dt B t ρ * dt C t ρ + 4 * dr C t ρ * dt C t ρ))
      / (4 * det2 A B C t ρ ^ 2)

/-- The time-time part of the curvature of the general round shape. -/
noncomputable def ricciTTg (A B C S : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ :=
  -(curv2 A B C t ρ * A t ρ) - hessTT A B C S t ρ / S t ρ + dt S t ρ ^ 2 / (2 * S t ρ ^ 2)

/-- The mixed time-distance part. -/
noncomputable def ricciTRg (A B C S : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ :=
  curv2 A B C t ρ * C t ρ - hessTR A B C S t ρ / S t ρ
    + dt S t ρ * dr S t ρ / (2 * S t ρ ^ 2)

/-- The distance-distance part. -/
noncomputable def ricciRRg (A B C S : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ :=
  curv2 A B C t ρ * B t ρ - hessRR A B C S t ρ / S t ρ + dr S t ρ ^ 2 / (2 * S t ρ ^ 2)

/-- The part along the directions around the mass. -/
noncomputable def ricciAngG (A B C S : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ :=
  1 - (A t ρ * hessRR A B C S t ρ + 2 * C t ρ * hessTR A B C S t ρ
        - B t ρ * hessTT A B C S t ρ) / (2 * det2 A B C t ρ)

/-- "Space is empty at time `t` and distance label `ρ`": all four formulas vanish there. -/
def IsEmptyG (A B C S : ℝ → ℝ → ℝ) (t ρ : ℝ) : Prop :=
  ricciTTg A B C S t ρ = 0 ∧ ricciRRg A B C S t ρ = 0 ∧ ricciTRg A B C S t ρ = 0 ∧
    ricciAngG A B C S t ρ = 0

/-! ## The curvature, part by part -/

/-- The conditions under which the computation makes sense at the point `x`: away from the poles,
the time-distance part not degenerate, the sphere size not zero, and all four functions twice
smoothly differentiable around the point. -/
structure RegularG (A B C S : ℝ → ℝ → ℝ) (x : Coords 4) : Prop where
  sin_ne : sin (x 2) ≠ 0
  det_ne : det2 A B C (x 0) (x 1) ≠ 0
  S_ne : S (x 0) (x 1) ≠ 0
  smoothA : TwiceSmooth A (x 0) (x 1)
  smoothB : TwiceSmooth B (x 0) (x 1)
  smoothC : TwiceSmooth C (x 0) (x 1)
  smoothS : TwiceSmooth S (x 0) (x 1)

variable {x : Coords 4}

theorem ricci_gen_tt (h : RegularG A B C S x) :
    ricci (genΓ A B C S) 0 0 x = ricciTTg A B C S (x 0) (x 1) := by
  have hs := h.sin_ne
  have hD := h.det_ne
  have hS0 := h.S_ne
  have d1 := dr_half (P := n100 A C) (Q := det2 A B C) (hasDerivAt_n100_r h.smoothA h.smoothC)
    (hasDerivAt_det2_r h.smoothA h.smoothB h.smoothC) hD
  have d2 := dt_half (P := n101 A B C) (Q := det2 A B C)
    (hasDerivAt_n101_t h.smoothA h.smoothB h.smoothC)
    (hasDerivAt_det2_t h.smoothA h.smoothB h.smoothC) hD
  have d3 := dt_half h.smoothS.slopeTT h.smoothS.slopeT hS0
  simp only [ricci, Fin.sum_univ_four, slope_genΓ_t, slope_genΓ_r, slope_genΓ_θ, slope_genΓ_φ,
    genΓ_apply]
  conv_lhs => simp [trPartG, θPartG, dt_zero2, dr_zero2, deriv_constOne, constOne, zero2, d1, d2,
    d3]
  simp only [h.smoothA.swap, half, n000, n001, n100, n101, n111, oneθ, ricciTTg, hessTT, curv2]
  field_simp
  simp only [det2]
  ring

theorem ricci_gen_tr (h : RegularG A B C S x) :
    ricci (genΓ A B C S) 0 1 x = ricciTRg A B C S (x 0) (x 1) := by
  have hs := h.sin_ne
  have hD := h.det_ne
  have hS0 := h.S_ne
  have d1 := dt_half (P := n001 A B C) (Q := det2 A B C)
    (hasDerivAt_n001_t h.smoothA h.smoothB h.smoothC)
    (hasDerivAt_det2_t h.smoothA h.smoothB h.smoothC) hD
  have d2 := dr_half (P := n000 A B C) (Q := det2 A B C)
    (hasDerivAt_n000_r h.smoothA h.smoothB h.smoothC)
    (hasDerivAt_det2_r h.smoothA h.smoothB h.smoothC) hD
  have d3 := dr_half h.smoothS.slopeTR h.smoothS.slopeR hS0
  simp only [ricci, Fin.sum_univ_four, slope_genΓ_t, slope_genΓ_r, slope_genΓ_θ, slope_genΓ_φ,
    genΓ_apply]
  conv_lhs => simp [trPartG, θPartG, dt_zero2, dr_zero2, deriv_constOne, constOne, zero2, d1, d2,
    d3]
  simp only [h.smoothA.swap, half, n000, n001, n011, n100, n101, n111, oneθ, ricciTRg, hessTR,
    curv2]
  field_simp
  simp only [det2]
  ring

theorem ricci_gen_rt (h : RegularG A B C S x) :
    ricci (genΓ A B C S) 1 0 x = ricciTRg A B C S (x 0) (x 1) := by
  have hs := h.sin_ne
  have hD := h.det_ne
  have hS0 := h.S_ne
  have d1 := dr_half (P := n101 A B C) (Q := det2 A B C)
    (hasDerivAt_n101_r h.smoothA h.smoothB h.smoothC)
    (hasDerivAt_det2_r h.smoothA h.smoothB h.smoothC) hD
  have d2 := dt_half (P := n111 A B C) (Q := det2 A B C)
    (hasDerivAt_n111_t h.smoothA h.smoothB h.smoothC)
    (hasDerivAt_det2_t h.smoothA h.smoothB h.smoothC) hD
  have d3 := dt_half h.smoothS.slopeRT h.smoothS.slopeT hS0
  simp only [ricci, Fin.sum_univ_four, slope_genΓ_t, slope_genΓ_r, slope_genΓ_θ, slope_genΓ_φ,
    genΓ_apply]
  conv_lhs => simp [trPartG, θPartG, dt_zero2, dr_zero2, deriv_constOne, constOne, zero2, d1, d2,
    d3]
  simp only [h.smoothB.swap, h.smoothC.swap, h.smoothS.swap, half, n000, n001, n011, n100, n101,
    n111, oneθ, ricciTRg, hessTR, curv2]
  field_simp
  simp only [det2]
  ring

theorem ricci_gen_rr (h : RegularG A B C S x) :
    ricci (genΓ A B C S) 1 1 x = ricciRRg A B C S (x 0) (x 1) := by
  have hs := h.sin_ne
  have hD := h.det_ne
  have hS0 := h.S_ne
  have d1 := dt_half (P := n011 B C) (Q := det2 A B C) (hasDerivAt_n011_t h.smoothB h.smoothC)
    (hasDerivAt_det2_t h.smoothA h.smoothB h.smoothC) hD
  have d2 := dr_half (P := n001 A B C) (Q := det2 A B C)
    (hasDerivAt_n001_r h.smoothA h.smoothB h.smoothC)
    (hasDerivAt_det2_r h.smoothA h.smoothB h.smoothC) hD
  have d3 := dr_half h.smoothS.slopeRR h.smoothS.slopeR hS0
  simp only [ricci, Fin.sum_univ_four, slope_genΓ_t, slope_genΓ_r, slope_genΓ_θ, slope_genΓ_φ,
    genΓ_apply]
  conv_lhs => simp [trPartG, θPartG, dt_zero2, dr_zero2, deriv_constOne, constOne, zero2, d1, d2,
    d3]
  simp only [h.smoothB.swap, h.smoothC.swap, half, n000, n001, n011, n101, n111, oneθ, ricciRRg,
    hessRR, curv2]
  field_simp
  simp only [det2]
  ring

theorem ricci_gen_θθ (h : RegularG A B C S x) :
    ricci (genΓ A B C S) 2 2 x = ricciAngG A B C S (x 0) (x 1) := by
  have hs := h.sin_ne
  have hD := h.det_ne
  have hS0 := h.S_ne
  have d1 := dt_half (P := m0 B C S) (Q := det2 A B C)
    (hasDerivAt_m0_t h.smoothB h.smoothC h.smoothS)
    (hasDerivAt_det2_t h.smoothA h.smoothB h.smoothC) hD
  have d2 := dr_half (P := m1 A C S) (Q := det2 A B C)
    (hasDerivAt_m1_r h.smoothA h.smoothC h.smoothS)
    (hasDerivAt_det2_r h.smoothA h.smoothB h.smoothC) hD
  have dcot := (hasDerivAt_cotF hs).deriv
  simp only [ricci, Fin.sum_univ_four, slope_genΓ_t, slope_genΓ_r, slope_genΓ_θ, slope_genΓ_φ,
    genΓ_apply]
  conv_lhs => simp [trPartG, θPartG, dt_zero2, dr_zero2, deriv_constOne, constOne, zero2, d1, d2,
    dcot]
  simp only [h.smoothS.swap, half, n000, n001, n011, n100, n101, n111, m0, m1, oneS, oneθ, cotF,
    ricciAngG, hessTT, hessTR, hessRR]
  field_simp
  simp only [det2]
  ring

theorem ricci_gen_φφ (h : RegularG A B C S x) :
    ricci (genΓ A B C S) 3 3 x = sin (x 2) ^ 2 * ricciAngG A B C S (x 0) (x 1) := by
  have hs := h.sin_ne
  have hD := h.det_ne
  have hS0 := h.S_ne
  have d1 := dt_half (P := m0 B C S) (Q := det2 A B C)
    (hasDerivAt_m0_t h.smoothB h.smoothC h.smoothS)
    (hasDerivAt_det2_t h.smoothA h.smoothB h.smoothC) hD
  have d2 := dr_half (P := m1 A C S) (Q := det2 A B C)
    (hasDerivAt_m1_r h.smoothA h.smoothC h.smoothS)
    (hasDerivAt_det2_r h.smoothA h.smoothB h.smoothC) hD
  have dsc := (hasDerivAt_scF (x 2)).deriv
  simp only [ricci, Fin.sum_univ_four, slope_genΓ_t, slope_genΓ_r, slope_genΓ_θ, slope_genΓ_φ,
    genΓ_apply]
  conv_lhs => simp [trPartG, θPartG, dt_zero2, dr_zero2, deriv_constOne, constOne, zero2, d1, d2,
    dsc]
  simp only [h.smoothS.swap, half, n000, n001, n011, n100, n101, n111, m0, m1, oneS, oneθ, sin2,
    scF, cotF, ricciAngG, hessTT, hessTR, hessRR]
  field_simp
  simp only [det2]
  ring

/-- The mixed part "time, pole angle" of the curvature vanishes. -/
theorem ricci_gen_tθ (h : RegularG A B C S x) : ricci (genΓ A B C S) 0 2 x = 0 := by
  have hs := h.sin_ne
  have hS0 := h.S_ne
  have d1 := (hasDerivAt_oneθ hs).deriv
  simp only [ricci, Fin.sum_univ_four, slope_genΓ_t, slope_genΓ_r, slope_genΓ_θ, slope_genΓ_φ,
    genΓ_apply]
  conv_lhs => simp [trPartG, θPartG, dt_zero2, dr_zero2, deriv_constOne, constOne, zero2, d1]
  simp only [oneS, oneθ, cotF]
  field_simp
  ring

/-- The mixed part "pole angle, time" of the curvature vanishes. -/
theorem ricci_gen_θt (h : RegularG A B C S x) : ricci (genΓ A B C S) 2 0 x = 0 := by
  have hs := h.sin_ne
  have hS0 := h.S_ne
  have d1 := dt_oneS h.smoothS hS0
  simp only [ricci, Fin.sum_univ_four, slope_genΓ_t, slope_genΓ_r, slope_genΓ_θ, slope_genΓ_φ,
    genΓ_apply]
  conv_lhs => simp [trPartG, θPartG, dt_zero2, dr_zero2, deriv_constOne, constOne, zero2, d1]
  simp only [oneS, oneθ, cotF]
  field_simp
  ring

/-- The mixed part "distance, pole angle" of the curvature vanishes. -/
theorem ricci_gen_rθ (h : RegularG A B C S x) : ricci (genΓ A B C S) 1 2 x = 0 := by
  have hs := h.sin_ne
  have hS0 := h.S_ne
  have d1 := (hasDerivAt_oneθ hs).deriv
  simp only [ricci, Fin.sum_univ_four, slope_genΓ_t, slope_genΓ_r, slope_genΓ_θ, slope_genΓ_φ,
    genΓ_apply]
  conv_lhs => simp [trPartG, θPartG, dt_zero2, dr_zero2, deriv_constOne, constOne, zero2, d1]
  simp only [oneS, oneθ, cotF]
  field_simp
  ring

/-- The mixed part "pole angle, distance" of the curvature vanishes. -/
theorem ricci_gen_θr (h : RegularG A B C S x) : ricci (genΓ A B C S) 2 1 x = 0 := by
  have hs := h.sin_ne
  have hS0 := h.S_ne
  have d1 := dr_oneS h.smoothS hS0
  simp only [ricci, Fin.sum_univ_four, slope_genΓ_t, slope_genΓ_r, slope_genΓ_θ, slope_genΓ_φ,
    genΓ_apply]
  conv_lhs => simp [trPartG, θPartG, dt_zero2, dr_zero2, deriv_constOne, constOne, zero2, d1]
  simp only [oneS, oneθ, cotF]
  field_simp
  ring

/-- Every mixed part of the curvature other than time-distance vanishes. -/
theorem ricci_gen_offdiag (h : RegularG A B C S x) {i j : Fin 4} (hij : i ≠ j)
    (h01 : ¬(i = 0 ∧ j = 1)) (h10 : ¬(i = 1 ∧ j = 0)) : ricci (genΓ A B C S) i j x = 0 := by
  by_cases h02 : i = 0 ∧ j = 2
  · obtain ⟨rfl, rfl⟩ := h02
    exact ricci_gen_tθ h
  by_cases h20 : i = 2 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := h20
    exact ricci_gen_θt h
  by_cases h12 : i = 1 ∧ j = 2
  · obtain ⟨rfl, rfl⟩ := h12
    exact ricci_gen_rθ h
  by_cases h21 : i = 2 ∧ j = 1
  · obtain ⟨rfl, rfl⟩ := h21
    exact ricci_gen_θr h
  fin_cases i <;> fin_cases j <;>
    simp [ricci, Fin.sum_univ_four, slope_genΓ_t, slope_genΓ_r, slope_genΓ_θ, slope_genΓ_φ,
      genΓ_apply, trPartG, θPartG, dt_zero2, dr_zero2, deriv_constOne, constOne, zero2]
      at hij h01 h10 h02 h20 h12 h21 ⊢

/-! ## The result -/

/-- **The curvature of the general round shape.** Einstein's equation for empty space, all
sixteen parts of it, holds at a point exactly when the four formulas `ricciTTg`, `ricciRRg`,
`ricciTRg` and `ricciAngG` vanish there. -/
theorem gen_ricciFlat_iff (h : RegularG A B C S x) :
    IsRicciFlatAt (genG A B C S) (genGinv A B C S) x ↔ IsEmptyG A B C S (x 0) (x 1) := by
  unfold IsRicciFlatAt IsEmptyG
  rw [christoffel_gen_eq]
  constructor
  · intro hf
    exact ⟨(ricci_gen_tt h).symm.trans (hf 0 0), (ricci_gen_rr h).symm.trans (hf 1 1),
      (ricci_gen_tr h).symm.trans (hf 0 1), (ricci_gen_θθ h).symm.trans (hf 2 2)⟩
  · rintro ⟨h0, h1, h01, h2⟩ i j
    by_cases hij : i = j
    · subst hij
      fin_cases i
      · exact (ricci_gen_tt h).trans h0
      · exact (ricci_gen_rr h).trans h1
      · exact (ricci_gen_θθ h).trans h2
      · exact (ricci_gen_φφ h).trans (by rw [h2, mul_zero])
    · by_cases ha : i = 0 ∧ j = 1
      · obtain ⟨rfl, rfl⟩ := ha
        exact (ricci_gen_tr h).trans h01
      by_cases hb : i = 1 ∧ j = 0
      · obtain ⟨rfl, rfl⟩ := hb
        exact (ricci_gen_rt h).trans h01
      exact ricci_gen_offdiag h hij ha hb

/-! ## The size of the spheres in empty space -/

/-- The slope of the sphere size `S`, squared and measured by the time-distance part, times
`AB + C²`. It is zero exactly where the size of the spheres changes in no direction, or only along
the path of a light ray. The rim of a black hole is such a place. -/
noncomputable def sizeSlopeSq (A B C S : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ :=
  A t ρ * (dr S t ρ * dr S t ρ) + 2 * C t ρ * (dt S t ρ * dr S t ρ)
    - B t ρ * (dt S t ρ * dt S t ρ)

/-- How fast the radius `√S` of the spheres grows, squared: `|∇R|²` in the textbooks. For
Schwarzschild's space-time this is `1 - 2M/r`. -/
noncomputable def radiusSlopeSq (A B C S : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ :=
  sizeSlopeSq A B C S t ρ / (4 * (S t ρ * det2 A B C t ρ))

/-- The three equations the size of the spheres obeys in empty space. They fix its second slopes
in terms of its first ones. With `S = R²` they are `∇∇R = (m / R²) · h` in the textbooks'
notation. -/
def SizeEquations (A B C S : ℝ → ℝ → ℝ) (t ρ : ℝ) : Prop :=
  hessTT A B C S t ρ
      = -(A t ρ) * (1 - radiusSlopeSq A B C S t ρ) + dt S t ρ ^ 2 / (2 * S t ρ) ∧
    hessTR A B C S t ρ
      = C t ρ * (1 - radiusSlopeSq A B C S t ρ) + dt S t ρ * dr S t ρ / (2 * S t ρ) ∧
    hessRR A B C S t ρ
      = B t ρ * (1 - radiusSlopeSq A B C S t ρ) + dr S t ρ ^ 2 / (2 * S t ρ)

/-- **In empty space the size of the spheres obeys the three size equations.** -/
theorem sizeEquations {t ρ : ℝ} (hD : det2 A B C t ρ ≠ 0) (hS : S t ρ ≠ 0)
    (h : IsEmptyG A B C S t ρ) : SizeEquations A B C S t ρ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have k1 : hessTT A B C S t ρ
      - (-(A t ρ) * (1 - radiusSlopeSq A B C S t ρ) + dt S t ρ ^ 2 / (2 * S t ρ))
      = -(S t ρ) * ricciTTg A B C S t ρ
        + -(A t ρ) * (S t ρ / (2 * det2 A B C t ρ)
            * (-(B t ρ) * ricciTTg A B C S t ρ + 2 * C t ρ * ricciTRg A B C S t ρ
              + A t ρ * ricciRRg A B C S t ρ) - ricciAngG A B C S t ρ) := by
    simp only [ricciTTg, ricciTRg, ricciRRg, ricciAngG, radiusSlopeSq, sizeSlopeSq]
    field_simp
    simp only [det2]
    ring
  have k2 : hessTR A B C S t ρ
      - (C t ρ * (1 - radiusSlopeSq A B C S t ρ) + dt S t ρ * dr S t ρ / (2 * S t ρ))
      = -(S t ρ) * ricciTRg A B C S t ρ
        + C t ρ * (S t ρ / (2 * det2 A B C t ρ)
            * (-(B t ρ) * ricciTTg A B C S t ρ + 2 * C t ρ * ricciTRg A B C S t ρ
              + A t ρ * ricciRRg A B C S t ρ) - ricciAngG A B C S t ρ) := by
    simp only [ricciTTg, ricciTRg, ricciRRg, ricciAngG, radiusSlopeSq, sizeSlopeSq]
    field_simp
    simp only [det2]
    ring
  have k3 : hessRR A B C S t ρ
      - (B t ρ * (1 - radiusSlopeSq A B C S t ρ) + dr S t ρ ^ 2 / (2 * S t ρ))
      = -(S t ρ) * ricciRRg A B C S t ρ
        + B t ρ * (S t ρ / (2 * det2 A B C t ρ)
            * (-(B t ρ) * ricciTTg A B C S t ρ + 2 * C t ρ * ricciTRg A B C S t ρ
              + A t ρ * ricciRRg A B C S t ρ) - ricciAngG A B C S t ρ) := by
    simp only [ricciTTg, ricciTRg, ricciRRg, ricciAngG, radiusSlopeSq, sizeSlopeSq]
    field_simp
    simp only [det2]
    ring
  rw [h1, h2, h3, h4] at k1 k2 k3
  exact ⟨by linear_combination k1, by linear_combination k2, by linear_combination k3⟩

end GravityInLean
