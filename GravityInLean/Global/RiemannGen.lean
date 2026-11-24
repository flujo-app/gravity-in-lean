/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.GeneralCurvature
public import GravityInLean.NewCoordinates

import Mathlib.Tactic

/-!
# The full curvature of the general round shape

For the length measure `-A dt² + 2C dt dρ + B dρ² + S (dθ² + sin²θ dφ²)` of `GeneralShape.lean`
this file computes the full curvature `riemM`, one table of numbers for each of the six pairs of
directions, from the connection `genΓ`. (`GeneralCurvature.lean` computed only the sums of these
tables that Einstein's equation uses.)

Three ingredients appear:

* `curv2`: the curvature of the time-distance part by itself;
* `bendTT`, `bendTR`, `bendRR`: how the radius `R = √S` of the spheres bends, divided by the
  radius (in the textbooks `∇∇R / R`);
* `radiusSlopeSq`: how fast the radius grows, squared (in the textbooks `|∇R|²`).

**What is proved here.** `riemM_gen_tr`, `riemM_gen_tθ`, `riemM_gen_rθ`, `riemM_gen_tφ`,
`riemM_gen_rφ`, `riemM_gen_θφ`: the six tables, at every point where the computation makes sense
(`RegularG`), for all four functions `A`, `B`, `C`, `S`.
-/

@[expose] public section

namespace GravityInLean

open Real Filter Topology

variable {A B C S : ℝ → ℝ → ℝ}

/-! ## Two more slopes of the pieces of the connection -/

section Slopes

variable {t ρ : ℝ}

/-- The slope along distance of the numerator of the connection entry "time; angle, angle". -/
theorem hasDerivAt_m0_r (hB : TwiceSmooth B t ρ) (hC : TwiceSmooth C t ρ)
    (hS : TwiceSmooth S t ρ) :
    HasDerivAt (fun s => m0 B C S t s)
      (dr B t ρ * dt S t ρ + B t ρ * dr (dt S) t ρ
        - (dr C t ρ * dr S t ρ + C t ρ * dr (dr S) t ρ)) ρ :=
  (hB.slopeR.mul hS.slopeTR).sub (hC.slopeR.mul hS.slopeRR)

/-- The slope along time of the numerator of the connection entry "distance; angle, angle". -/
theorem hasDerivAt_m1_t (hA : TwiceSmooth A t ρ) (hC : TwiceSmooth C t ρ)
    (hS : TwiceSmooth S t ρ) :
    HasDerivAt (fun s => m1 A C S s ρ)
      (-(dt C t ρ * dt S t ρ + C t ρ * dt (dt S) t ρ
        + (dt A t ρ * dr S t ρ + A t ρ * dt (dr S) t ρ))) t :=
  ((hC.slopeT.mul hS.slopeTT).add (hA.slopeT.mul hS.slopeRT)).neg

end Slopes

/-! ## How the radius of the spheres bends -/

/-- How the radius `√S` of the spheres bends along time, divided by the radius. -/
noncomputable def bendTT (A B C S : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ :=
  hessTT A B C S t ρ / (2 * S t ρ) - dt S t ρ ^ 2 / (4 * S t ρ ^ 2)

/-- How the radius of the spheres bends along time and distance together, divided by the
radius. -/
noncomputable def bendTR (A B C S : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ :=
  hessTR A B C S t ρ / (2 * S t ρ) - dt S t ρ * dr S t ρ / (4 * S t ρ ^ 2)

/-- How the radius of the spheres bends along distance, divided by the radius. -/
noncomputable def bendRR (A B C S : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ :=
  hessRR A B C S t ρ / (2 * S t ρ) - dr S t ρ ^ 2 / (4 * S t ρ ^ 2)

/-! ## Tables of four rows and four columns -/

/-- Two tables of four rows and four columns are the same when their sixteen entries are. -/
theorem matrix_ext_fin4 {M N : Matrix (Fin 4) (Fin 4) ℝ}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1) (h02 : M 0 2 = N 0 2) (h03 : M 0 3 = N 0 3)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) (h12 : M 1 2 = N 1 2) (h13 : M 1 3 = N 1 3)
    (h20 : M 2 0 = N 2 0) (h21 : M 2 1 = N 2 1) (h22 : M 2 2 = N 2 2) (h23 : M 2 3 = N 2 3)
    (h30 : M 3 0 = N 3 0) (h31 : M 3 1 = N 3 1) (h32 : M 3 2 = N 3 2) (h33 : M 3 3 = N 3 3) :
    M = N := by
  ext a b
  fin_cases a <;> fin_cases b <;> assumption

/-! ## The six tables of the full curvature -/

variable {x : Coords 4}

/-- **The full curvature in the directions time and distance** is the curvature of the
time-distance part by itself. -/
theorem riemM_gen_tr (h : RegularG A B C S x) :
    riemM (genΓ A B C S) 0 1 x
      = !![curv2 A B C (x 0) (x 1) * C (x 0) (x 1), curv2 A B C (x 0) (x 1) * B (x 0) (x 1), 0, 0;
          curv2 A B C (x 0) (x 1) * A (x 0) (x 1), -(curv2 A B C (x 0) (x 1) * C (x 0) (x 1)), 0, 0;
          0, 0, 0, 0;
          0, 0, 0, 0] := by
  have hs := h.sin_ne
  have hD := h.det_ne
  have hS0 := h.S_ne
  have hdt := hasDerivAt_det2_t h.smoothA h.smoothB h.smoothC
  have hdr := hasDerivAt_det2_r h.smoothA h.smoothB h.smoothC
  have d1 := dt_half (hasDerivAt_n001_t h.smoothA h.smoothB h.smoothC) hdt hD
  have d2 := dr_half (hasDerivAt_n000_r h.smoothA h.smoothB h.smoothC) hdr hD
  have d3 := dt_half (hasDerivAt_n011_t h.smoothB h.smoothC) hdt hD
  have d4 := dr_half (hasDerivAt_n001_r h.smoothA h.smoothB h.smoothC) hdr hD
  have d5 := dt_half (hasDerivAt_n101_t h.smoothA h.smoothB h.smoothC) hdt hD
  have d6 := dr_half (hasDerivAt_n100_r h.smoothA h.smoothC) hdr hD
  have d7 := dt_half (hasDerivAt_n111_t h.smoothA h.smoothB h.smoothC) hdt hD
  have d8 := dr_half (hasDerivAt_n101_r h.smoothA h.smoothB h.smoothC) hdr hD
  have d9 := dt_half h.smoothS.slopeRT h.smoothS.slopeT hS0
  have d10 := dr_half h.smoothS.slopeTR h.smoothS.slopeR hS0
  refine matrix_ext_fin4 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [riemM, dtab, tab, dirT, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.of_apply, Fin.sum_univ_four, slope_genΓ_t, slope_genΓ_r, slope_genΓ_θ, slope_genΓ_φ,
      genΓ_apply] <;>
    (conv_lhs => simp [trPartG, θPartG, dt_zero2, dr_zero2, deriv_constOne, constOne, zero2,
      d1, d2, d3, d4, d5, d6, d7, d8, d9, d10]) <;>
    (conv_rhs => simp) <;>
    (try simp only [h.smoothA.swap, h.smoothB.swap, h.smoothC.swap, h.smoothS.swap, half, n000,
      n001, n011, n100, n101, n111, oneθ, curv2]) <;>
    (try field_simp) <;>
    (try simp only [det2]) <;>
    ring

/-- **The full curvature in the directions time and pole angle** is how the radius of the
spheres bends along time. -/
theorem riemM_gen_tθ (h : RegularG A B C S x) :
    riemM (genΓ A B C S) 0 2 x
      = !![0, 0, -(S (x 0) (x 1) * (-(B (x 0) (x 1) * bendTT A B C S (x 0) (x 1))
              + C (x 0) (x 1) * bendTR A B C S (x 0) (x 1)) / det2 A B C (x 0) (x 1)), 0;
          0, 0, -(S (x 0) (x 1) * (C (x 0) (x 1) * bendTT A B C S (x 0) (x 1)
              + A (x 0) (x 1) * bendTR A B C S (x 0) (x 1)) / det2 A B C (x 0) (x 1)), 0;
          bendTT A B C S (x 0) (x 1), bendTR A B C S (x 0) (x 1), 0, 0;
          0, 0, 0, 0] := by
  have hs := h.sin_ne
  have hD := h.det_ne
  have hS0 := h.S_ne
  have hdt := hasDerivAt_det2_t h.smoothA h.smoothB h.smoothC
  have d1 := dt_half (hasDerivAt_m0_t h.smoothB h.smoothC h.smoothS) hdt hD
  have d2 := dt_half (hasDerivAt_m1_t h.smoothA h.smoothC h.smoothS) hdt hD
  have d3 := dt_half h.smoothS.slopeTT h.smoothS.slopeT hS0
  have d4 := dt_half h.smoothS.slopeRT h.smoothS.slopeT hS0
  have d5 := (hasDerivAt_oneθ hs).deriv
  have d6 := dt_oneS h.smoothS hS0
  refine matrix_ext_fin4 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [riemM, dtab, tab, dirT, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.of_apply, Fin.sum_univ_four, slope_genΓ_t, slope_genΓ_r, slope_genΓ_θ, slope_genΓ_φ,
      genΓ_apply] <;>
    (conv_lhs => simp [trPartG, θPartG, dt_zero2, dr_zero2, deriv_constOne, constOne, zero2,
      d1, d2, d3, d4, d5, d6]) <;>
    (conv_rhs => simp) <;>
    (try simp only [h.smoothA.swap, h.smoothB.swap, h.smoothC.swap, h.smoothS.swap, half, n000,
      n001, n011, n100, n101, n111, m0, m1, oneS, oneθ, cotF, scF, sin2, bendTT, bendTR,
      hessTT, hessTR]) <;>
    (try field_simp) <;>
    (try simp only [det2]) <;>
    ring

/-- **The full curvature in the directions distance and pole angle** is how the radius of the
spheres bends along distance. -/
theorem riemM_gen_rθ (h : RegularG A B C S x) :
    riemM (genΓ A B C S) 1 2 x
      = !![0, 0, -(S (x 0) (x 1) * (-(B (x 0) (x 1) * bendTR A B C S (x 0) (x 1))
              + C (x 0) (x 1) * bendRR A B C S (x 0) (x 1)) / det2 A B C (x 0) (x 1)), 0;
          0, 0, -(S (x 0) (x 1) * (C (x 0) (x 1) * bendTR A B C S (x 0) (x 1)
              + A (x 0) (x 1) * bendRR A B C S (x 0) (x 1)) / det2 A B C (x 0) (x 1)), 0;
          bendTR A B C S (x 0) (x 1), bendRR A B C S (x 0) (x 1), 0, 0;
          0, 0, 0, 0] := by
  have hs := h.sin_ne
  have hD := h.det_ne
  have hS0 := h.S_ne
  have hdr := hasDerivAt_det2_r h.smoothA h.smoothB h.smoothC
  have d1 := dr_half (hasDerivAt_m0_r h.smoothB h.smoothC h.smoothS) hdr hD
  have d2 := dr_half (hasDerivAt_m1_r h.smoothA h.smoothC h.smoothS) hdr hD
  have d3 := dr_half h.smoothS.slopeTR h.smoothS.slopeR hS0
  have d4 := dr_half h.smoothS.slopeRR h.smoothS.slopeR hS0
  have d5 := (hasDerivAt_oneθ hs).deriv
  have d6 := dr_oneS h.smoothS hS0
  refine matrix_ext_fin4 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [riemM, dtab, tab, dirT, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.of_apply, Fin.sum_univ_four, slope_genΓ_t, slope_genΓ_r, slope_genΓ_θ, slope_genΓ_φ,
      genΓ_apply] <;>
    (conv_lhs => simp [trPartG, θPartG, dt_zero2, dr_zero2, deriv_constOne, constOne, zero2,
      d1, d2, d3, d4, d5, d6]) <;>
    (conv_rhs => simp) <;>
    (try simp only [h.smoothA.swap, h.smoothB.swap, h.smoothC.swap, h.smoothS.swap, half, n000,
      n001, n011, n100, n101, n111, m0, m1, oneS, oneθ, cotF, scF, sin2, bendTR, bendRR,
      hessTR, hessRR]) <;>
    (try field_simp) <;>
    (try simp only [det2]) <;>
    ring

/-- **The full curvature in the directions time and angle around the axis:** the same as for
time and pole angle, with the size of the circle around the axis. -/
theorem riemM_gen_tφ (h : RegularG A B C S x) :
    riemM (genΓ A B C S) 0 3 x
      = !![0, 0, 0, -(S (x 0) (x 1) * sin (x 2) ^ 2 * (-(B (x 0) (x 1) * bendTT A B C S (x 0) (x 1))
              + C (x 0) (x 1) * bendTR A B C S (x 0) (x 1)) / det2 A B C (x 0) (x 1));
          0, 0, 0, -(S (x 0) (x 1) * sin (x 2) ^ 2 * (C (x 0) (x 1) * bendTT A B C S (x 0) (x 1)
              + A (x 0) (x 1) * bendTR A B C S (x 0) (x 1)) / det2 A B C (x 0) (x 1));
          0, 0, 0, 0;
          bendTT A B C S (x 0) (x 1), bendTR A B C S (x 0) (x 1), 0, 0] := by
  have hs := h.sin_ne
  have hD := h.det_ne
  have hS0 := h.S_ne
  have hdt := hasDerivAt_det2_t h.smoothA h.smoothB h.smoothC
  have d1 := dt_half (hasDerivAt_m0_t h.smoothB h.smoothC h.smoothS) hdt hD
  have d2 := dt_half (hasDerivAt_m1_t h.smoothA h.smoothC h.smoothS) hdt hD
  have d3 := dt_half h.smoothS.slopeTT h.smoothS.slopeT hS0
  have d4 := dt_half h.smoothS.slopeRT h.smoothS.slopeT hS0
  have d5 := (hasDerivAt_oneθ hs).deriv
  have d6 := dt_oneS h.smoothS hS0
  refine matrix_ext_fin4 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [riemM, dtab, tab, dirT, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.of_apply, Fin.sum_univ_four, slope_genΓ_t, slope_genΓ_r, slope_genΓ_θ, slope_genΓ_φ,
      genΓ_apply] <;>
    (conv_lhs => simp [trPartG, θPartG, dt_zero2, dr_zero2, deriv_constOne, constOne, zero2,
      d1, d2, d3, d4, d5, d6]) <;>
    (conv_rhs => simp) <;>
    (try simp only [h.smoothA.swap, h.smoothB.swap, h.smoothC.swap, h.smoothS.swap, half, n000,
      n001, n011, n100, n101, n111, m0, m1, oneS, oneθ, cotF, scF, sin2, bendTT, bendTR,
      hessTT, hessTR]) <;>
    (try field_simp) <;>
    (try simp only [det2]) <;>
    ring

/-- **The full curvature in the directions distance and angle around the axis:** the same as
for distance and pole angle, with the size of the circle around the axis. -/
theorem riemM_gen_rφ (h : RegularG A B C S x) :
    riemM (genΓ A B C S) 1 3 x
      = !![0, 0, 0, -(S (x 0) (x 1) * sin (x 2) ^ 2 * (-(B (x 0) (x 1) * bendTR A B C S (x 0) (x 1))
              + C (x 0) (x 1) * bendRR A B C S (x 0) (x 1)) / det2 A B C (x 0) (x 1));
          0, 0, 0, -(S (x 0) (x 1) * sin (x 2) ^ 2 * (C (x 0) (x 1) * bendTR A B C S (x 0) (x 1)
              + A (x 0) (x 1) * bendRR A B C S (x 0) (x 1)) / det2 A B C (x 0) (x 1));
          0, 0, 0, 0;
          bendTR A B C S (x 0) (x 1), bendRR A B C S (x 0) (x 1), 0, 0] := by
  have hs := h.sin_ne
  have hD := h.det_ne
  have hS0 := h.S_ne
  have hdr := hasDerivAt_det2_r h.smoothA h.smoothB h.smoothC
  have d1 := dr_half (hasDerivAt_m0_r h.smoothB h.smoothC h.smoothS) hdr hD
  have d2 := dr_half (hasDerivAt_m1_r h.smoothA h.smoothC h.smoothS) hdr hD
  have d3 := dr_half h.smoothS.slopeTR h.smoothS.slopeR hS0
  have d4 := dr_half h.smoothS.slopeRR h.smoothS.slopeR hS0
  have d5 := (hasDerivAt_oneθ hs).deriv
  have d6 := dr_oneS h.smoothS hS0
  refine matrix_ext_fin4 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [riemM, dtab, tab, dirT, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.of_apply, Fin.sum_univ_four, slope_genΓ_t, slope_genΓ_r, slope_genΓ_θ, slope_genΓ_φ,
      genΓ_apply] <;>
    (conv_lhs => simp [trPartG, θPartG, dt_zero2, dr_zero2, deriv_constOne, constOne, zero2,
      d1, d2, d3, d4, d5, d6]) <;>
    (conv_rhs => simp) <;>
    (try simp only [h.smoothA.swap, h.smoothB.swap, h.smoothC.swap, h.smoothS.swap, half, n000,
      n001, n011, n100, n101, n111, m0, m1, oneS, oneθ, cotF, scF, sin2, bendTR, bendRR,
      hessTR, hessRR]) <;>
    (try field_simp) <;>
    (try simp only [det2]) <;>
    ring

/-- **The full curvature in the two directions along the spheres** is the curvature of the
spheres: one minus how fast the radius grows, squared. -/
theorem riemM_gen_θφ (h : RegularG A B C S x) :
    riemM (genΓ A B C S) 2 3 x
      = !![0, 0, 0, 0;
          0, 0, 0, 0;
          0, 0, 0, (1 - radiusSlopeSq A B C S (x 0) (x 1)) * sin (x 2) ^ 2;
          0, 0, -(1 - radiusSlopeSq A B C S (x 0) (x 1)), 0] := by
  have hs := h.sin_ne
  have hD := h.det_ne
  have hS0 := h.S_ne
  have d1 := (hasDerivAt_oneθ hs).deriv
  have d2 := (hasDerivAt_cotF hs).deriv
  have d3 := (hasDerivAt_scF (x 2)).deriv
  refine matrix_ext_fin4 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [riemM, dtab, tab, dirT, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.of_apply, Fin.sum_univ_four, slope_genΓ_t, slope_genΓ_r, slope_genΓ_θ, slope_genΓ_φ,
      genΓ_apply] <;>
    (conv_lhs => simp [trPartG, θPartG, dt_zero2, dr_zero2, deriv_constOne, deriv_sin2, constOne,
      zero2, d1, d2, d3]) <;>
    (conv_rhs => simp) <;>
    (try simp only [half, n000, n001, n011, n100, n101, n111, m0, m1, oneS, oneθ, cotF, scF,
      sin2, radiusSlopeSq, sizeSlopeSq]) <;>
    (try field_simp) <;>
    (try simp only [det2]) <;>
    ring

end GravityInLean
