/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Rim.RadiusSmooth
public import GravityInLean.Checks.EfEmpty

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Kruskal's table is a good table and a space-time, rim included

Board item `task:rim-table`. Kruskal's table for a positive mass is
`-A dT² + A dX² + r² (dθ² + sin²θ dφ²)` with `A = (32 m³ / r) · exp (-r / 2m)` and
`r = kruskalR m (X² - T²)`. On its whole region (`X² - T² > -1`, off the poles), the rim
`X² = T²` included:

* `isOpen_kruskalRegion`: the region is open;
* `kruskalA_pos`, `kruskalS_pos`: the factor `A` and the size of the spheres `r²` are positive;
* `contDiffAt_kruskalA`, `contDiffAt_kruskalS`, `smooth_kruskalG`: they, and so every entry of
  the table, are smooth;
* `kruskal_regular`: so the table is good on the region, with the inverse `genGinv` of the
  general round shape;
* `kruskal_measure_apply`: the length measure written out;
* `kruskal_oneTime`: the step `(1, 0, 0, 0)` has squared length `-A`, and every other step at
  right angles to it has a positive squared length;
* `kruskalIsSpaceTime`: so Kruskal's table is a space-time on all of its region.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean

open Real Set

open scoped Manifold ContDiff

namespace Curved

/-- Kruskal's region is open. -/
theorem isOpen_kruskalRegion : IsOpen kruskalRegion :=
  (isOpen_lt continuous_const
    (((continuous_apply 1).pow 2).sub ((continuous_apply 0).pow 2))).inter
    (isOpen_ne_fun (Real.continuous_sin.comp (continuous_apply 2)) continuous_const)

/-- The factor in front of `-dT² + dX²` in Kruskal's table is positive, the rim included. -/
theorem kruskalA_pos {m T X : ℝ} (hm : 0 < m) (h : -1 < X ^ 2 - T ^ 2) :
    0 < kruskalA m T X :=
  mul_pos (div_pos (mul_pos (by norm_num) (pow_pos hm 3)) (kruskalR_pos hm h)) (Real.exp_pos _)

/-- The size of the spheres in Kruskal's table is positive, the rim included. -/
theorem kruskalS_pos {m T X : ℝ} (hm : 0 < m) (h : -1 < X ^ 2 - T ^ 2) :
    0 < kruskalS m T X :=
  pow_pos (kruskalR_pos hm h) 2

/-- The radius of Kruskal's table is a smooth function of the two labels `T` and `X`, the rim
included. -/
theorem contDiffAt_kruskalR_labels {m T X : ℝ} (hm : 0 < m) (h : -1 < X ^ 2 - T ^ 2) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ ↦ kruskalR m (p.2 ^ 2 - p.1 ^ 2)) (T, X) := by
  have hu : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ ↦ p.2 ^ 2 - p.1 ^ 2) (T, X) :=
    (contDiffAt_snd.pow 2).sub (contDiffAt_fst.pow 2)
  have hR : ContDiffAt ℝ ∞ (kruskalR m) ((fun p : ℝ × ℝ ↦ p.2 ^ 2 - p.1 ^ 2) (T, X)) :=
    contDiffAt_kruskalR hm h
  exact ContDiffAt.comp (g := kruskalR m) (T, X) hR hu

/-- The factor in front of `-dT² + dX²` in Kruskal's table is a smooth function of the two
labels `T` and `X`, the rim included. -/
theorem contDiffAt_kruskalA {m T X : ℝ} (hm : 0 < m) (h : -1 < X ^ 2 - T ^ 2) :
    ContDiffAt ℝ ∞ (Function.uncurry (kruskalA m)) (T, X) := by
  have hR := contDiffAt_kruskalR_labels hm h
  have hne : kruskalR m ((T, X).2 ^ 2 - (T, X).1 ^ 2) ≠ 0 := (kruskalR_pos hm h).ne'
  have h1 : ContDiffAt ℝ ∞
      (fun p : ℝ × ℝ ↦ 32 * m ^ 3 / kruskalR m (p.2 ^ 2 - p.1 ^ 2)) (T, X) :=
    contDiffAt_const.div hR hne
  have h2 : ContDiffAt ℝ ∞
      (fun p : ℝ × ℝ ↦ Real.exp (-(kruskalR m (p.2 ^ 2 - p.1 ^ 2)) / (2 * m))) (T, X) :=
    (hR.neg.div_const (2 * m)).exp
  exact h1.mul h2

/-- The size of the spheres in Kruskal's table is a smooth function of the two labels `T` and
`X`, the rim included. -/
theorem contDiffAt_kruskalS {m T X : ℝ} (hm : 0 < m) (h : -1 < X ^ 2 - T ^ 2) :
    ContDiffAt ℝ ∞ (Function.uncurry (kruskalS m)) (T, X) :=
  (contDiffAt_kruskalR_labels hm h).pow 2

/-- Every entry of Kruskal's table is smooth on its region, the rim included. -/
theorem smooth_kruskalG {m : ℝ} (hm : 0 < m) {x : Coords 4} (h : -1 < x 1 ^ 2 - x 0 ^ 2)
    (i j : Fin 4) : ContDiffAt ℝ ∞ (kruskalG m i j) x := by
  have hF : ContDiffAt ℝ ∞
      (Function.uncurry (gTR (kruskalA m) (kruskalA m) zero2 (kruskalS m) i j)) (x 0, x 1) := by
    unfold gTR
    split_ifs
    · exact (contDiffAt_kruskalA hm h).neg
    · exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ × ℝ => (0 : ℝ)) (x 0, x 1))
    · exact contDiffAt_kruskalA hm h
    · exact contDiffAt_kruskalS hm h
    · exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ × ℝ => (0 : ℝ)) (x 0, x 1))
  have hh : ContDiffAt ℝ ∞ (gΘ i j) (x 2) := by
    unfold gΘ
    split_ifs
    · exact (Real.contDiff_sin.contDiffAt).pow 2
    · exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (1 : ℝ)) (x 2))
  exact Tests.smooth_sep2 hF hh

/-- Kruskal's table is good on all of its region, the rim included: its entries are smooth, it
is symmetric, and the inverse of the general round shape is its inverse. -/
theorem kruskal_regular {m : ℝ} (hm : 0 < m) :
    IsRegularTableOn (kruskalG m) (genGinv (kruskalA m) (kruskalA m) zero2 (kruskalS m))
      kruskalRegion where
  isOpen := isOpen_kruskalRegion
  smooth := fun a b _ hx ↦ (smooth_kruskalG hm hx.1 a b).contDiffWithinAt
  symm := fun x _ a b ↦ genG_symm (kruskalA m) (kruskalA m) zero2 (kruskalS m) a b x
  inverse := fun x hx a c ↦ by
    have hA : 0 < kruskalA m (x 0) (x 1) := kruskalA_pos hm hx.1
    have hD : det2 (kruskalA m) (kruskalA m) zero2 (x 0) (x 1) ≠ 0 := by
      have hdet : det2 (kruskalA m) (kruskalA m) zero2 (x 0) (x 1)
          = kruskalA m (x 0) (x 1) * kruskalA m (x 0) (x 1) := by
        simp only [det2, zero2, mul_zero, add_zero]
      rw [hdet]
      exact (mul_pos hA hA).ne'
    exact genG_mul_genGinv hD (kruskalS_pos hm hx.1).ne' hx.2 a c

/-- The length measure of Kruskal's table, written out: `-A dT² + A dX² + r² dθ² +
r² sin²θ dφ²`. -/
theorem kruskal_measure_apply (m : ℝ) (x v w : Coords 4) :
    tableMeasure (kruskalG m) x v w
      = -kruskalA m (x 0) (x 1) * v 0 * w 0 + kruskalA m (x 0) (x 1) * v 1 * w 1
        + kruskalS m (x 0) (x 1) * v 2 * w 2
        + kruskalS m (x 0) (x 1) * sin (x 2) ^ 2 * v 3 * w 3 := by
  simp only [tableMeasure, formOf_apply, Fin.sum_univ_four]
  simp [kruskalG, genG, sep2, gTR, gΘ, negA, zero2, sin2, constOne]

/-- **Kruskal's table has one time direction, on the rim as well.** The step `(1, 0, 0, 0)` has
squared length `-A`. A step at right angles to it has `v 0 = 0`, and so the squared length
`A (v 1)² + r² (v 2)² + r² sin²θ (v 3)²`. -/
theorem kruskal_oneTime {m : ℝ} (hm : 0 < m) {x : Coords 4} (h : -1 < x 1 ^ 2 - x 0 ^ 2)
    (hs : sin (x 2) ≠ 0) :
    HasOneTimeDirection fun v w : Coords 4 ↦ tableMeasure (kruskalG m) x v w := by
  have hA : 0 < kruskalA m (x 0) (x 1) := kruskalA_pos hm h
  have hS : 0 < kruskalS m (x 0) (x 1) := kruskalS_pos hm h
  have h0 : (![1, 0, 0, 0] : Coords 4) 0 = 1 := rfl
  have h1 : (![1, 0, 0, 0] : Coords 4) 1 = 0 := rfl
  have h2 : (![1, 0, 0, 0] : Coords 4) 2 = 0 := rfl
  have h3 : (![1, 0, 0, 0] : Coords 4) 3 = 0 := rfl
  refine ⟨![1, 0, 0, 0], ?_, ?_⟩
  · change tableMeasure (kruskalG m) x ![1, 0, 0, 0] ![1, 0, 0, 0] < 0
    rw [kruskal_measure_apply, h0, h1, h2, h3]
    linarith
  · intro v hv hne
    have hv' : tableMeasure (kruskalG m) x ![1, 0, 0, 0] v = 0 := hv
    rw [kruskal_measure_apply, h0, h1, h2, h3] at hv'
    have hAv : kruskalA m (x 0) (x 1) * v 0 = 0 := by linear_combination -hv'
    have z0 : v 0 = 0 := (mul_eq_zero.mp hAv).resolve_left hA.ne'
    have key : tableMeasure (kruskalG m) x v v
        = kruskalA m (x 0) (x 1) * v 1 ^ 2 + kruskalS m (x 0) (x 1) * v 2 ^ 2
          + kruskalS m (x 0) (x 1) * sin (x 2) ^ 2 * v 3 ^ 2 := by
      rw [kruskal_measure_apply, z0]
      ring
    have hs2 : 0 < sin (x 2) ^ 2 := sq_pos_iff.mpr hs
    have hex : v 1 ≠ 0 ∨ v 2 ≠ 0 ∨ v 3 ≠ 0 := by
      by_contra hcon
      have hcon' : v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0 := by tauto
      obtain ⟨z1, z2, z3⟩ := hcon'
      refine hne (funext fun i ↦ ?_)
      fin_cases i
      · exact z0
      · exact z1
      · exact z2
      · exact z3
    have p1 : 0 ≤ kruskalA m (x 0) (x 1) * v 1 ^ 2 := mul_nonneg hA.le (sq_nonneg _)
    have p2 : 0 ≤ kruskalS m (x 0) (x 1) * v 2 ^ 2 := mul_nonneg hS.le (sq_nonneg _)
    have p3 : 0 ≤ kruskalS m (x 0) (x 1) * sin (x 2) ^ 2 * v 3 ^ 2 :=
      mul_nonneg (mul_pos hS hs2).le (sq_nonneg _)
    change 0 < tableMeasure (kruskalG m) x v v
    rw [key]
    rcases hex with h | h | h
    · have q : 0 < kruskalA m (x 0) (x 1) * v 1 ^ 2 := mul_pos hA (sq_pos_iff.mpr h)
      linarith
    · have q : 0 < kruskalS m (x 0) (x 1) * v 2 ^ 2 := mul_pos hS (sq_pos_iff.mpr h)
      linarith
    · have q : 0 < kruskalS m (x 0) (x 1) * sin (x 2) ^ 2 * v 3 ^ 2 :=
        mul_pos (mul_pos hS hs2) (sq_pos_iff.mpr h)
      linarith

/-- **Kruskal's is a space-time,** rim included: for a positive mass, Kruskal's table is
symmetric, smooth, and has one time direction on all of its region. -/
theorem kruskalIsSpaceTime : KruskalIsSpaceTime := fun _ hm ↦
  { symm := fun _ hx v w ↦ (kruskal_regular hm).measure_symm hx v w
    oneTime := fun _ hx ↦ kruskal_oneTime hm hx.1 hx.2
    smooth := (kruskal_regular hm).isSmoothOn }

end Curved

end GravityInLean
