/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.Checks

import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Angles for the directions near a given direction

Near every direction of ordinary space, after a turn or mirror that takes the direction
`(1, 0, 0)` to it, the two angles of a direction are smooth functions of the direction.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

/-- **Angles after a given turn.** If the turn or mirror `R` takes the direction `(1, 0, 0)` to
a direction on the same side as `y₀`, then near `y₀` the two angles of `Rᵀ y / |y|` are smooth:
the pole angle is `arccos` of the third number, the angle around the axis is `arctan` of the
second number over the first. -/
theorem sphere_section_of_turn {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R.transpose * R = 1)
    {y₀ : Fin 3 → ℝ} (h0 : 0 < R 0 0 * y₀ 0 + R 1 0 * y₀ 1 + R 2 0 * y₀ 2) :
    ∃ (U : Set (Fin 3 → ℝ)) (θ φ : (Fin 3 → ℝ) → ℝ),
      IsOpen U ∧ y₀ ∈ U ∧ ContDiffOn ℝ ∞ θ U ∧ ContDiffOn ℝ ∞ φ U ∧
      ∀ y ∈ U, 0 < y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 ∧ sin (θ y) ≠ 0 ∧
        R.mulVec ![sin (θ y) * cos (φ y), sin (θ y) * sin (φ y), cos (θ y)]
          = (√(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2))⁻¹ • y := by
  -- the rows of `R` are of length one and at right angles to each other
  have hR' : R * R.transpose = 1 := mul_eq_one_comm.mp hR
  have e : ∀ i j, R i 0 * R j 0 + R i 1 * R j 1 + R i 2 * R j 2
      = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by
    intro i j
    rw [← hR', Matrix.mul_apply, Fin.sum_univ_three]
    simp only [Matrix.transpose_apply]
  have e00 : R 0 0 * R 0 0 + R 0 1 * R 0 1 + R 0 2 * R 0 2 = 1 := (e 0 0).trans (by simp)
  have e11 : R 1 0 * R 1 0 + R 1 1 * R 1 1 + R 1 2 * R 1 2 = 1 := (e 1 1).trans (by simp)
  have e22 : R 2 0 * R 2 0 + R 2 1 * R 2 1 + R 2 2 * R 2 2 = 1 := (e 2 2).trans (by simp)
  have e01 : R 0 0 * R 1 0 + R 0 1 * R 1 1 + R 0 2 * R 1 2 = 0 := (e 0 1).trans (by simp)
  have e02 : R 0 0 * R 2 0 + R 0 1 * R 2 1 + R 0 2 * R 2 2 = 0 := (e 0 2).trans (by simp)
  have e12 : R 1 0 * R 2 0 + R 1 1 * R 2 1 + R 1 2 * R 2 2 = 0 := (e 1 2).trans (by simp)
  -- the three numbers of `Rᵀ y`
  obtain ⟨a, ha⟩ : ∃ a : (Fin 3 → ℝ) → ℝ, ∀ y, a y = R 0 0 * y 0 + R 1 0 * y 1 + R 2 0 * y 2 :=
    ⟨_, fun _ ↦ rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : (Fin 3 → ℝ) → ℝ, ∀ y, b y = R 0 1 * y 0 + R 1 1 * y 1 + R 2 1 * y 2 :=
    ⟨_, fun _ ↦ rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : (Fin 3 → ℝ) → ℝ, ∀ y, c y = R 0 2 * y 0 + R 1 2 * y 1 + R 2 2 * y 2 :=
    ⟨_, fun _ ↦ rfl⟩
  -- they are smooth, and so is the square of the length
  have cj : ∀ j : Fin 3, ContDiff ℝ ∞ (fun y : Fin 3 → ℝ ↦ y j) :=
    fun j ↦ contDiff_apply ℝ (fun _ : Fin 3 ↦ ℝ) j
  have lin : ∀ p q r : ℝ, ContDiff ℝ ∞ (fun y : Fin 3 → ℝ ↦ p * y 0 + q * y 1 + r * y 2) :=
    fun p q r ↦ ((contDiff_const.mul (cj 0)).add (contDiff_const.mul (cj 1))).add
      (contDiff_const.mul (cj 2))
  have hca : ContDiff ℝ ∞ a := by
    rw [show a = _ from funext ha]
    exact lin _ _ _
  have hcb : ContDiff ℝ ∞ b := by
    rw [show b = _ from funext hb]
    exact lin _ _ _
  have hcc : ContDiff ℝ ∞ c := by
    rw [show c = _ from funext hc]
    exact lin _ _ _
  have hcN : ContDiff ℝ ∞ (fun y : Fin 3 → ℝ ↦ y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) :=
    (((cj 0).pow 2).add ((cj 1).pow 2)).add ((cj 2).pow 2)
  -- `Rᵀ` keeps the length, and `R` undoes `Rᵀ`
  have hN : ∀ y, a y ^ 2 + b y ^ 2 + c y ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
    intro y
    rw [ha, hb, hc]
    linear_combination y 0 ^ 2 * e00 + y 1 ^ 2 * e11 + y 2 ^ 2 * e22 + 2 * y 0 * y 1 * e01
      + 2 * y 0 * y 2 * e02 + 2 * y 1 * y 2 * e12
  have back : ∀ y i, R i 0 * a y + R i 1 * b y + R i 2 * c y = y i := by
    intro y i
    have h : R i 0 * a y + R i 1 * b y + R i 2 * c y
        = (1 : Matrix (Fin 3) (Fin 3) ℝ) i 0 * y 0 + (1 : Matrix (Fin 3) (Fin 3) ℝ) i 1 * y 1
          + (1 : Matrix (Fin 3) (Fin 3) ℝ) i 2 * y 2 := by
      rw [ha, hb, hc]
      linear_combination y 0 * e i 0 + y 1 * e i 1 + y 2 * e i 2
    rw [h]
    simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using
      congrFun (Matrix.one_mulVec y) i
  -- where the first number is positive: the length is positive and the third number is small
  have bounds : ∀ y, 0 < a y → 0 < y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2
      ∧ 0 < √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2)
      ∧ √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) ^ 2 = a y ^ 2 + b y ^ 2 + c y ^ 2
      ∧ -1 < c y / √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2)
      ∧ c y / √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) < 1 := by
    intro y hay
    have ha2 : 0 < a y ^ 2 := pow_pos hay 2
    have hNpos : 0 < y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
      rw [← hN y]
      linarith [sq_nonneg (b y), sq_nonneg (c y)]
    have hn : 0 < √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) := Real.sqrt_pos.mpr hNpos
    have hn2 : √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) ^ 2 = a y ^ 2 + b y ^ 2 + c y ^ 2 := by
      rw [Real.sq_sqrt hNpos.le, hN]
    have hc2 : c y ^ 2 < √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) ^ 2 := by
      rw [hn2]
      linarith [sq_nonneg (b y)]
    obtain ⟨hl, hu⟩ := abs_lt_of_sq_lt_sq' hc2 hn.le
    refine ⟨hNpos, hn, hn2, ?_, ?_⟩
    · rw [lt_div_iff₀ hn]
      linarith
    · rw [div_lt_one hn]
      exact hu
  -- the statement at one point
  have main : ∀ y, 0 < a y → 0 < y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2
      ∧ sin (arccos (c y / √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2))) ≠ 0
      ∧ R.mulVec ![sin (arccos (c y / √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2))) * cos (arctan (b y / a y)),
          sin (arccos (c y / √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2))) * sin (arctan (b y / a y)),
          cos (arccos (c y / √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2)))]
        = (√(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2))⁻¹ • y := by
    intro y hay
    obtain ⟨hNpos, hn, hn2, hx1, hx2⟩ := bounds y hay
    have hn' : √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) ≠ 0 := hn.ne'
    have hay' : a y ≠ 0 := hay.ne'
    have hρ : 0 < √(a y ^ 2 + b y ^ 2) :=
      Real.sqrt_pos.mpr (by linarith [pow_pos hay 2, sq_nonneg (b y)])
    have hρ' : √(a y ^ 2 + b y ^ 2) ≠ 0 := hρ.ne'
    -- the pole angle
    have h3 : cos (arccos (c y / √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2)))
        = c y / √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) := Real.cos_arccos hx1.le hx2.le
    have hsin : sin (arccos (c y / √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2)))
        = √(a y ^ 2 + b y ^ 2) / √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) := by
      have h : 1 - (c y / √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2)) ^ 2
          = (a y ^ 2 + b y ^ 2) / √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) ^ 2 := by
        rw [div_pow, eq_div_iff (pow_ne_zero 2 hn'), sub_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hn')]
        linear_combination hn2
      rw [Real.sin_arccos, h, Real.sqrt_div (by positivity), Real.sqrt_sq hn.le]
    -- the angle around the axis
    have hsq : √(1 + (b y / a y) ^ 2) = √(a y ^ 2 + b y ^ 2) / a y := by
      have h : 1 + (b y / a y) ^ 2 = (a y ^ 2 + b y ^ 2) / a y ^ 2 := by
        rw [div_pow, eq_div_iff (pow_ne_zero 2 hay'), add_mul,
          div_mul_cancel₀ _ (pow_ne_zero 2 hay'), one_mul]
      rw [h, Real.sqrt_div (by positivity), Real.sqrt_sq hay.le]
    have hcosφ : cos (arctan (b y / a y)) = a y / √(a y ^ 2 + b y ^ 2) := by
      rw [Real.cos_arctan, hsq, one_div, inv_div]
    have hsinφ : sin (arctan (b y / a y)) = b y / √(a y ^ 2 + b y ^ 2) := by
      rw [Real.sin_arctan, hsq]
      field_simp
    have h1 : sin (arccos (c y / √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2))) * cos (arctan (b y / a y))
        = a y / √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) := by
      rw [hsin, hcosφ]
      field_simp
    have h2 : sin (arccos (c y / √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2))) * sin (arctan (b y / a y))
        = b y / √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) := by
      rw [hsin, hsinφ]
      field_simp
    refine ⟨hNpos, ?_, ?_⟩
    · rw [hsin]
      exact div_ne_zero hρ' hn'
    · rw [h1, h2, h3]
      ext i
      have h : (R.mulVec ![a y / √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2),
          b y / √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2), c y / √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2)]) i
          = (R i 0 * a y + R i 1 * b y + R i 2 * c y) / √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) := by
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val]
        ring
      rw [h, back y i, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
  refine ⟨{y | 0 < a y}, fun y ↦ arccos (c y / √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2)),
    fun y ↦ arctan (b y / a y), isOpen_lt continuous_const hca.continuous, ?_, ?_, ?_,
    fun y hy ↦ main y hy⟩
  · rw [Set.mem_ofPred_eq, ha]
    exact h0
  · intro y hy
    obtain ⟨hNpos, hn, -, hx1, hx2⟩ := bounds y hy
    have hq : ContDiffAt ℝ ∞ (fun y ↦ c y / √(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2)) y :=
      hcc.contDiffAt.div (hcN.contDiffAt.sqrt hNpos.ne') hn.ne'
    exact ((Real.contDiffAt_arccos hx1.ne' hx2.ne).comp y hq).contDiffWithinAt
  · intro y hy
    have hay : a y ≠ 0 := (show 0 < a y from hy).ne'
    exact (hcb.contDiffAt.div hca.contDiffAt hay).arctan.contDiffWithinAt

/-- **Angles near a direction.** For a vector `y₀` of ordinary space that is not zero there are
a turn or mirror `R`, an open set `U` around `y₀`, and two smooth functions `θ`, `φ` on `U`
such that every `y` in `U` is not zero and has, after `R`, the direction with the pole angle
`θ y` (off the poles) and the angle `φ y` around the axis. -/
theorem exists_sphere_section {y₀ : Fin 3 → ℝ} (hy : 0 < y₀ 0 ^ 2 + y₀ 1 ^ 2 + y₀ 2 ^ 2) :
    ∃ (R : Matrix (Fin 3) (Fin 3) ℝ) (U : Set (Fin 3 → ℝ)) (θ φ : (Fin 3 → ℝ) → ℝ),
      R.transpose * R = 1 ∧ IsOpen U ∧ y₀ ∈ U ∧ ContDiffOn ℝ ∞ θ U ∧ ContDiffOn ℝ ∞ φ U ∧
      ∀ y ∈ U, 0 < y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 ∧ sin (θ y) ≠ 0 ∧
        R.mulVec ![sin (θ y) * cos (φ y), sin (θ y) * sin (φ y), cos (θ y)]
          = (√(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2))⁻¹ • y := by
  -- a turn or mirror that takes `(1, 0, 0)` to the axis, with sign, along which `y₀` is not zero
  obtain ⟨R, hR, h0⟩ : ∃ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1
      ∧ 0 < R 0 0 * y₀ 0 + R 1 0 * y₀ 1 + R 2 0 * y₀ 2 := by
    rcases lt_trichotomy (y₀ 0) 0 with h | h | h
    · refine ⟨!![-1, 0, 0; 0, 1, 0; 0, 0, 1], ?_, ?_⟩
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
      · change 0 < (-1 : ℝ) * y₀ 0 + 0 * y₀ 1 + 0 * y₀ 2
        linarith
    · rcases lt_trichotomy (y₀ 1) 0 with h' | h' | h'
      · refine ⟨!![0, 1, 0; -1, 0, 0; 0, 0, 1], ?_, ?_⟩
        · ext i j
          fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
        · change 0 < (0 : ℝ) * y₀ 0 + (-1) * y₀ 1 + 0 * y₀ 2
          linarith
      · rcases lt_trichotomy (y₀ 2) 0 with h'' | h'' | h''
        · refine ⟨!![0, 0, 1; 0, 1, 0; -1, 0, 0], ?_, ?_⟩
          · ext i j
            fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
          · change 0 < (0 : ℝ) * y₀ 0 + 0 * y₀ 1 + (-1) * y₀ 2
            linarith
        · rw [h, h', h''] at hy
          norm_num at hy
        · refine ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], ?_, ?_⟩
          · ext i j
            fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
          · change 0 < (0 : ℝ) * y₀ 0 + 0 * y₀ 1 + 1 * y₀ 2
            linarith
      · refine ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], ?_, ?_⟩
        · ext i j
          fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
        · change 0 < (0 : ℝ) * y₀ 0 + 1 * y₀ 1 + 0 * y₀ 2
          linarith
    · refine ⟨!![1, 0, 0; 0, 1, 0; 0, 0, 1], ?_, ?_⟩
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
      · change 0 < (1 : ℝ) * y₀ 0 + 0 * y₀ 1 + 0 * y₀ 2
        linarith
  obtain ⟨U, θ, φ, hU, hmem, hθ, hφ, hall⟩ := sphere_section_of_turn hR h0
  exact ⟨R, U, θ, φ, hR, hU, hmem, hθ, hφ, hall⟩

end GravityInLean.Curved
