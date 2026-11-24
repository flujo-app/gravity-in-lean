/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Rim.Table
public import GravityInLean.Eddington
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

import Mathlib.Tactic

/-!
# Kruskal's space-time is empty, the rim included

Board item `task:rim-empty`. Kruskal's table is the general round shape `genG A A zero2 S` with
`A = kruskalA m` and `S = kruskalS m`, and both are functions of the one number `u = X² - T²`.
So all their slopes in `T` and `X` come from slopes in `u` by the chain rule, and the four
formulas for the curvature of the general round shape (`GeneralCurvature.lean`) turn into three
ordinary equations in `u`. They hold for Kruskal's functions.

The steps:

* `sqDiff f`: the function `f (X² - T²)` of the two labels, and its first and second slopes
  (`dt_sqDiff`, `dr_sqDiff`, `dt_dt_sqDiff`, `dr_dt_sqDiff`, `dr_dr_sqDiff`);
* `isEmptyG_of_sqDiff`: for a table `genG A A zero2 S` whose slopes have that form, the four
  formulas vanish as soon as three ordinary equations hold;
* `kruskalW`, `kruskalAu`, `kruskalSu` and their slopes in `u`: Kruskal's functions, written in
  the radius `r` and in `w = exp (-r / 2m)`;
* `kruskal_isEmptyG`: the four formulas vanish for Kruskal's table, wherever `X² - T² > -1`;
* `kruskal_regularG`: the conditions under which the formulas are the curvature hold there;
* `kruskalIsEmpty_of_regular`: so Kruskal's space-time is empty, given that its table is good;
* `kruskalIsEmpty`: the statement `KruskalIsEmpty`, with the good table of `Rim/Table.lean`.
-/

@[expose] public section

namespace GravityInLean

open Real Set Filter Topology

open scoped ContDiff

namespace Curved

/-! ## Functions of `X² - T²` -/

/-- The function `f (X² - T²)` of the two labels `T` and `X`. -/
noncomputable def sqDiff (f : ℝ → ℝ) (T X : ℝ) : ℝ := f (X ^ 2 - T ^ 2)

section Chain

variable {f f1 f2 : ℝ → ℝ} {f' T X : ℝ}

/-- The chain rule along `T`: the slope of `f (X² - T²)` in `T` is `-2T` times the slope of
`f`. -/
theorem hasDerivAt_sqDiff_T (hf : HasDerivAt f f' (X ^ 2 - T ^ 2)) :
    HasDerivAt (fun s : ℝ => f (X ^ 2 - s ^ 2)) (-2 * T * f') T := by
  have hin : HasDerivAt (fun s : ℝ => X ^ 2 - s ^ 2) (-(2 * T)) T :=
    ((hasDerivAt_pow 2 T).const_sub (X ^ 2)).congr_deriv (by norm_num)
  exact (HasDerivAt.comp T hf hin).congr_deriv (by ring)

/-- The chain rule along `X`: the slope of `f (X² - T²)` in `X` is `2X` times the slope of
`f`. -/
theorem hasDerivAt_sqDiff_X (hf : HasDerivAt f f' (X ^ 2 - T ^ 2)) :
    HasDerivAt (fun s : ℝ => f (s ^ 2 - T ^ 2)) (2 * X * f') X := by
  have hin : HasDerivAt (fun s : ℝ => s ^ 2 - T ^ 2) (2 * X) X :=
    ((hasDerivAt_pow 2 X).fun_sub (hasDerivAt_const X (T ^ 2))).congr_deriv (by norm_num)
  exact (HasDerivAt.comp X hf hin).congr_deriv (by ring)

/-- Moving `T` a little keeps `X² - T²` above `-1`. -/
theorem eventually_sqDiff_T (h : -1 < X ^ 2 - T ^ 2) : ∀ᶠ s in 𝓝 T, -1 < X ^ 2 - s ^ 2 := by
  have hc : ContinuousAt (fun s : ℝ => X ^ 2 - s ^ 2) T := by fun_prop
  exact Filter.Tendsto.eventually hc (lt_mem_nhds h)

/-- Moving `X` a little keeps `X² - T²` above `-1`. -/
theorem eventually_sqDiff_X (h : -1 < X ^ 2 - T ^ 2) : ∀ᶠ s in 𝓝 X, -1 < s ^ 2 - T ^ 2 := by
  have hc : ContinuousAt (fun s : ℝ => s ^ 2 - T ^ 2) X := by fun_prop
  exact Filter.Tendsto.eventually hc (lt_mem_nhds h)

/-- The slope of `f (X² - T²)` in `T`. -/
theorem dt_sqDiff (h1 : ∀ u, -1 < u → HasDerivAt f (f1 u) u) (h : -1 < X ^ 2 - T ^ 2) :
    dt (sqDiff f) T X = -2 * T * f1 (X ^ 2 - T ^ 2) :=
  (hasDerivAt_sqDiff_T (h1 _ h)).deriv

/-- The slope of `f (X² - T²)` in `X`. -/
theorem dr_sqDiff (h1 : ∀ u, -1 < u → HasDerivAt f (f1 u) u) (h : -1 < X ^ 2 - T ^ 2) :
    dr (sqDiff f) T X = 2 * X * f1 (X ^ 2 - T ^ 2) :=
  (hasDerivAt_sqDiff_X (h1 _ h)).deriv

/-- The second slope of `f (X² - T²)` in `T`. -/
theorem dt_dt_sqDiff (h1 : ∀ u, -1 < u → HasDerivAt f (f1 u) u)
    (h2 : ∀ u, -1 < u → HasDerivAt f1 (f2 u) u) (h : -1 < X ^ 2 - T ^ 2) :
    dt (dt (sqDiff f)) T X = -2 * f1 (X ^ 2 - T ^ 2) + 4 * T ^ 2 * f2 (X ^ 2 - T ^ 2) := by
  have hev : (fun s => dt (sqDiff f) s X) =ᶠ[𝓝 T] fun s => -2 * s * f1 (X ^ 2 - s ^ 2) := by
    filter_upwards [eventually_sqDiff_T h] with s hs
    exact dt_sqDiff h1 hs
  have hd : HasDerivAt (fun s : ℝ => -2 * s * f1 (X ^ 2 - s ^ 2))
      (-2 * f1 (X ^ 2 - T ^ 2) + 4 * T ^ 2 * f2 (X ^ 2 - T ^ 2)) T :=
    (((hasDerivAt_id' T).const_mul (-2)).fun_mul (hasDerivAt_sqDiff_T (h2 _ h))).congr_deriv
      (by ring)
  exact hev.deriv_eq.trans hd.deriv

/-- The mixed second slope of `f (X² - T²)`: first in `T`, then in `X`. -/
theorem dr_dt_sqDiff (h1 : ∀ u, -1 < u → HasDerivAt f (f1 u) u)
    (h2 : ∀ u, -1 < u → HasDerivAt f1 (f2 u) u) (h : -1 < X ^ 2 - T ^ 2) :
    dr (dt (sqDiff f)) T X = -4 * T * X * f2 (X ^ 2 - T ^ 2) := by
  have hev : (fun s => dt (sqDiff f) T s) =ᶠ[𝓝 X] fun s => -2 * T * f1 (s ^ 2 - T ^ 2) := by
    filter_upwards [eventually_sqDiff_X h] with s hs
    exact dt_sqDiff h1 hs
  have hd : HasDerivAt (fun s : ℝ => -2 * T * f1 (s ^ 2 - T ^ 2))
      (-4 * T * X * f2 (X ^ 2 - T ^ 2)) X :=
    ((hasDerivAt_sqDiff_X (h2 _ h)).const_mul (-2 * T)).congr_deriv (by ring)
  exact hev.deriv_eq.trans hd.deriv

/-- The second slope of `f (X² - T²)` in `X`. -/
theorem dr_dr_sqDiff (h1 : ∀ u, -1 < u → HasDerivAt f (f1 u) u)
    (h2 : ∀ u, -1 < u → HasDerivAt f1 (f2 u) u) (h : -1 < X ^ 2 - T ^ 2) :
    dr (dr (sqDiff f)) T X = 2 * f1 (X ^ 2 - T ^ 2) + 4 * X ^ 2 * f2 (X ^ 2 - T ^ 2) := by
  have hev : (fun s => dr (sqDiff f) T s) =ᶠ[𝓝 X] fun s => 2 * s * f1 (s ^ 2 - T ^ 2) := by
    filter_upwards [eventually_sqDiff_X h] with s hs
    exact dr_sqDiff h1 hs
  have hd : HasDerivAt (fun s : ℝ => 2 * s * f1 (s ^ 2 - T ^ 2))
      (2 * f1 (X ^ 2 - T ^ 2) + 4 * X ^ 2 * f2 (X ^ 2 - T ^ 2)) X :=
    (((hasDerivAt_id' X).const_mul 2).fun_mul (hasDerivAt_sqDiff_X (h2 _ h))).congr_deriv
      (by ring)
  exact hev.deriv_eq.trans hd.deriv

end Chain

/-! ## The four formulas, for a table made of functions of `X² - T²` -/

/-- **Three ordinary equations are enough.** Take the general round shape with the same function
`A` in front of `-dT²` and of `dX²` and no cross term, and let `A` and the sphere size `S` have,
at the point `(T, X)`, the values `a`, `s` and the slopes of functions of `X² - T²` with first
slopes `a1`, `s1` and second slopes `a2`, `s2`. Then the four formulas for the curvature vanish
there as soon as three equations between these six numbers and `X² - T²` hold. -/
theorem isEmptyG_of_sqDiff {A S : ℝ → ℝ → ℝ} {T X a a1 a2 s s1 s2 : ℝ}
    (hA : A T X = a) (hAt : dt A T X = -2 * T * a1) (hAr : dr A T X = 2 * X * a1)
    (hAtt : dt (dt A) T X = -2 * a1 + 4 * T ^ 2 * a2)
    (hArr : dr (dr A) T X = 2 * a1 + 4 * X ^ 2 * a2)
    (hS : S T X = s) (hSt : dt S T X = -2 * T * s1) (hSr : dr S T X = 2 * X * s1)
    (hStt : dt (dt S) T X = -2 * s1 + 4 * T ^ 2 * s2)
    (hSrt : dr (dt S) T X = -4 * T * X * s2)
    (hSrr : dr (dr S) T X = 2 * s1 + 4 * X ^ 2 * s2)
    (ha : a ≠ 0) (hs : s ≠ 0)
    (e1 : s2 - a1 * s1 / a - s1 ^ 2 / (2 * s) = 0)
    (e2 : (-2 * a1 - 2 * (X ^ 2 - T ^ 2) * a2) / a + 2 * (X ^ 2 - T ^ 2) * a1 ^ 2 / a ^ 2
        - (2 * s1 + 2 * (X ^ 2 - T ^ 2) * s2) / s + (X ^ 2 - T ^ 2) * s1 ^ 2 / s ^ 2 = 0)
    (e3 : a - 2 * (s1 + (X ^ 2 - T ^ 2) * s2) = 0) :
    IsEmptyG A A zero2 S T X := by
  have hdet : det2 A A zero2 T X = a ^ 2 := by
    simp only [det2, zero2, hA]
    ring
  simp only [IsEmptyG, ricciTTg, ricciTRg, ricciRRg, ricciAngG, hessTT, hessTR, hessRR, curv2,
    half, n000, n001, n011, n100, n101, n111, hdet, dt_zero2_fun, dr_zero2_fun, zero2,
    hA, hAt, hAr, hAtt, hArr, hS, hSt, hSr, hStt, hSrt, hSrr]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (norm := skip) (-1) * e2 - 2 * (T ^ 2 + X ^ 2) / s * e1
    field_simp
    ring
  · linear_combination (norm := skip) e2 - 2 * (T ^ 2 + X ^ 2) / s * e1
    field_simp
    ring
  · linear_combination (norm := skip) 4 * T * X / s * e1
    field_simp
    ring
  · linear_combination (norm := skip) 1 / a * e3
    field_simp
    ring

/-! ## Kruskal's functions of `u = X² - T²` and their slopes -/

/-- The factor `exp (-r / 2m)`, as a function of `u = X² - T²`. -/
noncomputable def kruskalW (m u : ℝ) : ℝ := Real.exp (-(kruskalR m u) / (2 * m))

/-- Kruskal's factor in front of `-dT² + dX²`, as a function of `u = X² - T²`. -/
noncomputable def kruskalAu (m u : ℝ) : ℝ := 32 * m ^ 3 / kruskalR m u * kruskalW m u

/-- The slope of `kruskalAu m` in `u`. -/
noncomputable def kruskalAu1 (m u : ℝ) : ℝ :=
  -64 * m ^ 4 * kruskalW m u ^ 2 * (kruskalR m u + 2 * m) / kruskalR m u ^ 3

/-- The second slope of `kruskalAu m` in `u`. -/
noncomputable def kruskalAu2 (m u : ℝ) : ℝ :=
  256 * m ^ 5 * kruskalW m u ^ 3 * (kruskalR m u ^ 2 + 4 * m * kruskalR m u + 6 * m ^ 2)
    / kruskalR m u ^ 5

/-- The size of the spheres in Kruskal's form, as a function of `u = X² - T²`. -/
noncomputable def kruskalSu (m u : ℝ) : ℝ := kruskalR m u ^ 2

/-- The slope of `kruskalSu m` in `u`. -/
noncomputable def kruskalSu1 (m u : ℝ) : ℝ := 8 * m ^ 2 * kruskalW m u

/-- The second slope of `kruskalSu m` in `u`. -/
noncomputable def kruskalSu2 (m u : ℝ) : ℝ := -16 * m ^ 3 * kruskalW m u ^ 2 / kruskalR m u

section KruskalSlopes

variable {m u : ℝ}

/-- The factor `exp (-r / 2m)` is positive. -/
theorem kruskalW_pos (m u : ℝ) : 0 < kruskalW m u := Real.exp_pos _

/-- `exp (r / 2m)` is one over `exp (-r / 2m)`. -/
theorem exp_eq_inv_kruskalW (m u : ℝ) :
    Real.exp (kruskalR m u / (2 * m)) = (kruskalW m u)⁻¹ := by
  rw [kruskalW, ← Real.exp_neg]
  congr 1
  ring

/-- The slope of the radius, written with `w = exp (-r / 2m)`: `4m² w / r`. -/
theorem hasDerivAt_kruskalR_w (hm : 0 < m) (hu : -1 < u) :
    HasDerivAt (kruskalR m) (4 * m ^ 2 * kruskalW m u / kruskalR m u) u := by
  have hr : kruskalR m u ≠ 0 := (kruskalR_pos hm hu).ne'
  have hw : kruskalW m u ≠ 0 := (kruskalW_pos m u).ne'
  refine (hasDerivAt_kruskalR hm hu).congr_deriv ?_
  rw [exp_eq_inv_kruskalW]
  field_simp

/-- The slope of `w = exp (-r / 2m)` in `u`: `-2m w² / r`. -/
theorem hasDerivAt_kruskalW (hm : 0 < m) (hu : -1 < u) :
    HasDerivAt (kruskalW m) (-2 * m * kruskalW m u ^ 2 / kruskalR m u) u := by
  have hr : kruskalR m u ≠ 0 := (kruskalR_pos hm hu).ne'
  have hm' : m ≠ 0 := hm.ne'
  have h := (((hasDerivAt_kruskalR_w hm hu).fun_neg).div_const (2 * m)).exp
  refine h.congr_deriv ?_
  change kruskalW m u * (-(4 * m ^ 2 * kruskalW m u / kruskalR m u) / (2 * m)) = _
  field_simp
  ring

/-- The slope of Kruskal's factor in `u`. -/
theorem hasDerivAt_kruskalAu (hm : 0 < m) (hu : -1 < u) :
    HasDerivAt (kruskalAu m) (kruskalAu1 m u) u := by
  have hr : kruskalR m u ≠ 0 := (kruskalR_pos hm hu).ne'
  have h := ((hasDerivAt_const u (32 * m ^ 3)).fun_div (hasDerivAt_kruskalR_w hm hu) hr).fun_mul
    (hasDerivAt_kruskalW hm hu)
  refine h.congr_deriv ?_
  rw [kruskalAu1]
  field_simp
  ring

/-- The second slope of Kruskal's factor in `u`. -/
theorem hasDerivAt_kruskalAu1 (hm : 0 < m) (hu : -1 < u) :
    HasDerivAt (kruskalAu1 m) (kruskalAu2 m u) u := by
  have hr : kruskalR m u ≠ 0 := (kruskalR_pos hm hu).ne'
  have hR := hasDerivAt_kruskalR_w hm hu
  have h := ((((hasDerivAt_kruskalW hm hu).fun_pow 2).const_mul (-64 * m ^ 4)).fun_mul
    (hR.fun_add (hasDerivAt_const u (2 * m)))).fun_div (hR.fun_pow 3) (pow_ne_zero 3 hr)
  refine h.congr_deriv ?_
  rw [kruskalAu2]
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp
  ring

/-- The slope of the size of the spheres in `u`. -/
theorem hasDerivAt_kruskalSu (hm : 0 < m) (hu : -1 < u) :
    HasDerivAt (kruskalSu m) (kruskalSu1 m u) u := by
  have hr : kruskalR m u ≠ 0 := (kruskalR_pos hm hu).ne'
  refine ((hasDerivAt_kruskalR_w hm hu).fun_pow 2).congr_deriv ?_
  rw [kruskalSu1]
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp
  ring

/-- The second slope of the size of the spheres in `u`. -/
theorem hasDerivAt_kruskalSu1 (hm : 0 < m) (hu : -1 < u) :
    HasDerivAt (kruskalSu1 m) (kruskalSu2 m u) u := by
  refine ((hasDerivAt_kruskalW hm hu).const_mul (8 * m ^ 2)).congr_deriv ?_
  rw [kruskalSu2]
  ring

end KruskalSlopes

/-! ## Kruskal's table is empty -/

section Empty

variable {m T X : ℝ}

/-- **The four formulas for the curvature vanish for Kruskal's table,** at every `T`, `X` with
`X² - T² > -1`, the rim `X² = T²` included. -/
theorem kruskal_isEmptyG (hm : 0 < m) (h : -1 < X ^ 2 - T ^ 2) :
    IsEmptyG (kruskalA m) (kruskalA m) zero2 (kruskalS m) T X := by
  have hA : kruskalA m = sqDiff (kruskalAu m) := rfl
  have hS : kruskalS m = sqDiff (kruskalSu m) := rfl
  have a1 : ∀ u, -1 < u → HasDerivAt (kruskalAu m) (kruskalAu1 m u) u :=
    fun _ hu => hasDerivAt_kruskalAu hm hu
  have a2 : ∀ u, -1 < u → HasDerivAt (kruskalAu1 m) (kruskalAu2 m u) u :=
    fun _ hu => hasDerivAt_kruskalAu1 hm hu
  have s1 : ∀ u, -1 < u → HasDerivAt (kruskalSu m) (kruskalSu1 m u) u :=
    fun _ hu => hasDerivAt_kruskalSu hm hu
  have s2 : ∀ u, -1 < u → HasDerivAt (kruskalSu1 m) (kruskalSu2 m u) u :=
    fun _ hu => hasDerivAt_kruskalSu1 hm hu
  have hm' : m ≠ 0 := hm.ne'
  have hr : kruskalR m (X ^ 2 - T ^ 2) ≠ 0 := (kruskalR_pos hm h).ne'
  have hw : kruskalW m (X ^ 2 - T ^ 2) ≠ 0 := (kruskalW_pos m _).ne'
  -- the equation that ties the radius to `X² - T²`
  have hrel : X ^ 2 - T ^ 2
      = (kruskalR m (X ^ 2 - T ^ 2) / (2 * m) - 1) * (kruskalW m (X ^ 2 - T ^ 2))⁻¹ := by
    have hF : kruskalF m (kruskalR m (X ^ 2 - T ^ 2)) = X ^ 2 - T ^ 2 := kruskalF_kruskalR hm h
    rw [kruskalF, exp_eq_inv_kruskalW] at hF
    exact hF.symm
  refine isEmptyG_of_sqDiff (a := kruskalAu m (X ^ 2 - T ^ 2)) (a1 := kruskalAu1 m (X ^ 2 - T ^ 2))
    (a2 := kruskalAu2 m (X ^ 2 - T ^ 2)) (s := kruskalSu m (X ^ 2 - T ^ 2))
    (s1 := kruskalSu1 m (X ^ 2 - T ^ 2)) (s2 := kruskalSu2 m (X ^ 2 - T ^ 2))
    rfl (hA ▸ dt_sqDiff a1 h) (hA ▸ dr_sqDiff a1 h) (hA ▸ dt_dt_sqDiff a1 a2 h)
    (hA ▸ dr_dr_sqDiff a1 a2 h) rfl (hS ▸ dt_sqDiff s1 h) (hS ▸ dr_sqDiff s1 h)
    (hS ▸ dt_dt_sqDiff s1 s2 h) (hS ▸ dr_dt_sqDiff s1 s2 h) (hS ▸ dr_dr_sqDiff s1 s2 h)
    ?_ ?_ ?_ ?_ ?_
  · exact (kruskalA_pos hm h).ne'
  · exact (kruskalS_pos hm h).ne'
  · simp only [kruskalAu, kruskalAu1, kruskalSu, kruskalSu1, kruskalSu2]
    generalize kruskalW m (X ^ 2 - T ^ 2) = w at hw
    generalize kruskalR m (X ^ 2 - T ^ 2) = r at hr
    field_simp
    ring
  · simp only [kruskalAu, kruskalAu1, kruskalAu2, kruskalSu, kruskalSu1, kruskalSu2]
    generalize kruskalW m (X ^ 2 - T ^ 2) = w at hw hrel ⊢
    generalize kruskalR m (X ^ 2 - T ^ 2) = r at hr hrel ⊢
    rw [hrel]
    field_simp
    ring
  · simp only [kruskalAu, kruskalSu1, kruskalSu2]
    generalize kruskalW m (X ^ 2 - T ^ 2) = w at hw hrel ⊢
    generalize kruskalR m (X ^ 2 - T ^ 2) = r at hr hrel ⊢
    rw [hrel]
    field_simp
    ring

/-- Kruskal's factor is twice smoothly differentiable in `T` and `X`, and so is the size of the
spheres, wherever `X² - T² > -1`. -/
theorem twiceSmooth_kruskal (hm : 0 < m) (h : -1 < X ^ 2 - T ^ 2) :
    TwiceSmooth (kruskalA m) T X ∧ TwiceSmooth (kruskalS m) T X := by
  have hin : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => p.2 ^ 2 - p.1 ^ 2) (T, X) :=
    (contDiffAt_snd.pow 2).sub (contDiffAt_fst.pow 2)
  have hR : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => kruskalR m (p.2 ^ 2 - p.1 ^ 2)) (T, X) :=
    ContDiffAt.comp (g := kruskalR m) (T, X)
      ((contDiffAt_kruskalR hm h).of_le (by norm_num)) hin
  have hr : kruskalR m (X ^ 2 - T ^ 2) ≠ 0 := (kruskalR_pos hm h).ne'
  constructor
  · exact (contDiffAt_const.div hR hr).mul ((hR.neg.div_const (2 * m)).exp)
  · exact hR.pow 2

/-- The conditions under which the four formulas are the curvature hold for Kruskal's table at
every point of its region. -/
theorem kruskal_regularG (hm : 0 < m) {x : Coords 4} (hx : x ∈ kruskalRegion) :
    RegularG (kruskalA m) (kruskalA m) zero2 (kruskalS m) x where
  sin_ne := hx.2
  det_ne := by
    have ha := kruskalA_pos hm hx.1
    simp only [det2, zero2]
    positivity
  S_ne := (kruskalS_pos hm hx.1).ne'
  smoothA := (twiceSmooth_kruskal hm hx.1).1
  smoothB := (twiceSmooth_kruskal hm hx.1).1
  smoothC := twiceSmooth_zero2 _ _
  smoothS := (twiceSmooth_kruskal hm hx.1).2

/-- **Kruskal's space-time is empty, the rim included,** given that Kruskal's table is good on
its region (with the inverse table of the general round shape). -/
theorem kruskalIsEmpty_of_regular (hm : 0 < m)
    (hreg : IsRegularTableOn (kruskalG m)
      (genGinv (kruskalA m) (kruskalA m) zero2 (kruskalS m)) kruskalRegion) :
    IsEmptyOn (flatMeasure (tableMeasure (kruskalG m))) kruskalRegion :=
  hreg.isEmptyOn fun _ hx ↦ (gen_ricciFlat_iff (kruskal_regularG hm hx)).mpr
    (kruskal_isEmptyG hm hx.1)

/-- **Kruskal's is empty,** rim included: for a positive mass, space is empty on all of the
region of Kruskal's table. -/
theorem kruskalIsEmpty : KruskalIsEmpty := fun _ hm ↦
  kruskalIsEmpty_of_regular hm (kruskal_regular hm)

end Empty

end Curved

end GravityInLean
