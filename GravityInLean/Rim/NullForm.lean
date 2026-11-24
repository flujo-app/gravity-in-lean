/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Rim.NullLabels
public import GravityInLean.Rim.NullInverse
public import GravityInLean.Rim.NullTable
public import GravityInLean.Rim.NullMass
public import GravityInLean.BirkhoffGeneral
public import GravityInLean.BirkhoffFromSymmetry

import Mathlib.Tactic

/-!
# The round shape in labels along the paths of light

Board item `task:rim-null-form`. Step 8 of the route, second half. Around a point of a box on
which the round shape `genG A B C S` is in the setting of the general theorem and empty, the
two labels `u`, `v` along the paths of light (`exists_nullLabels`) are new coordinates for time
and distance. In them the table is the round shape `genG zero2 zero2 F S'` (time-distance part
`2 F du dv`) on a box `J' × I'`, again in the setting of the general theorem and empty, and its
mass function is the old one.

Said without the change of coordinates in four dimensions, on a neighbourhood `N` of the point:
`S = S' ∘ (u, v)`, and `-A dt² + 2 C dt dρ + B dρ² = 2 F du dv`, that is
`A = -2 F u_t v_t`, `C = F (u_t v_ρ + u_ρ v_t)`, `B = 2 F u_ρ v_ρ`.

On paper, and in this file:

* `(t, ρ) ↦ (u, v)` can be undone near the point (`exists_inverse_labels`); call the inverse
  `(τ, ϱ)`, on a box `J' × I'`.
* The slopes of the inverse undo the slopes of `u`, `v` (`inverse_labels_slopes`, the chain
  rule): `u_t τ_a + u_ρ ϱ_a = 1`, `u_t τ_b + u_ρ ϱ_b = 0`, `v_t τ_a + v_ρ ϱ_a = 0`,
  `v_t τ_b + v_ρ ϱ_b = 1`.
* Plain algebra (`null_alg`): with `Δ = u_t v_ρ - u_ρ v_t` and
  `P = -B u_t v_t + C (u_t v_ρ + u_ρ v_t) + A u_ρ v_ρ`, the two equations "the slope of `u` has
  length zero", "the slope of `v` has length zero" give `P² = (A B + C²) Δ²`,
  `A Δ² = -2 P u_t v_t`, `C Δ² = P (u_t v_ρ + u_ρ v_t)`, `B Δ² = 2 P u_ρ v_ρ`. So the three
  relations hold with the factor `P / Δ²`, which is not zero.
* With the chain rule (`null_pull_alg`): in the labels `(a, b)` the entries for `da²` and `db²`
  are zero, the mixed entry is that factor, and the slopes of `(τ, ϱ)` have a determinant that
  is not zero.
* `nullTable` (`NullTable.lean`): the table in the labels `(a, b)` is again in the setting of
  the general theorem and empty. Its entries for `da²` and `db²` are zero on the box, so it is
  `genG zero2 zero2 F S'` there with `F` the mixed entry and `S' = S ∘ (τ, ϱ)`; "empty" only
  looks at the table near a point (`isRicciFlatAt_congr`).
* The mass function is the old one: `massFn_null_eq` (`NullMass.lean`).
-/

@[expose] public section

namespace GravityInLean

open Set Filter Topology

open scoped ContDiff

namespace Rim

/-! ## Plain algebra -/

/-- If two independent slopes `(ut, ur)`, `(vt, vr)` both have length zero for the
time-distance part with the entries `A`, `B`, `C`, then that part is `2 f du dv` for a factor
`f` that is not zero. -/
theorem null_alg {A B C ut ur vt vr : ℝ}
    (hu : -B * ut ^ 2 + 2 * C * ut * ur + A * ur ^ 2 = 0)
    (hv : -B * vt ^ 2 + 2 * C * vt * vr + A * vr ^ 2 = 0)
    (hΔ : ut * vr - ur * vt ≠ 0) (hD : 0 < A * B + C * C) :
    ∃ f : ℝ, f ≠ 0 ∧ A = -2 * f * (ut * vt) ∧ C = f * (ut * vr + ur * vt)
      ∧ B = 2 * f * (ur * vr) := by
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = -B * (ut * vt) + C * (ut * vr + ur * vt) + A * (ur * vr) :=
    ⟨_, rfl⟩
  obtain ⟨Δ, hΔe⟩ : ∃ Δ : ℝ, Δ = ut * vr - ur * vt := ⟨_, rfl⟩
  have hΔ0 : Δ ≠ 0 := by
    rw [hΔe]
    exact hΔ
  have hP2 : P ^ 2 = (A * B + C * C) * Δ ^ 2 := by
    rw [hP, hΔe]
    linear_combination (-B * vt ^ 2 + 2 * C * vt * vr + A * vr ^ 2) * hu
  have hPpos : 0 < P ^ 2 := by
    rw [hP2]
    exact mul_pos hD (by positivity)
  have hP0 : P ≠ 0 := (pow_ne_zero_iff two_ne_zero).1 hPpos.ne'
  have hAΔ : A * Δ ^ 2 = -2 * P * (ut * vt) := by
    rw [hP, hΔe]
    linear_combination ut ^ 2 * hv + vt ^ 2 * hu
  have hCΔ : C * Δ ^ 2 = P * (ut * vr + ur * vt) := by
    rw [hP, hΔe]
    linear_combination -(ut * ur) * hv - (vt * vr) * hu
  have hBΔ : B * Δ ^ 2 = 2 * P * (ur * vr) := by
    rw [hP, hΔe]
    linear_combination -ur ^ 2 * hv - vr ^ 2 * hu
  refine ⟨P / Δ ^ 2, div_ne_zero hP0 (pow_ne_zero 2 hΔ0), ?_, ?_, ?_⟩
  · field_simp
    linear_combination hAΔ
  · field_simp
    linear_combination hCΔ
  · field_simp
    linear_combination hBΔ

/-- The same, read in the labels `(a, b)` in which `u = a` and `v = b`: with the slopes
`τa`, `τb`, `ϱa`, `ϱb` of the old labels along the new ones, the entries for `da²` and `db²`
are zero, the mixed entry is not zero and is the factor of `null_alg`, and the slopes of the
change of labels have a determinant that is not zero. -/
theorem null_pull_alg {A B C ut ur vt vr τa τb ϱa ϱb : ℝ}
    (hu : -B * ut ^ 2 + 2 * C * ut * ur + A * ur ^ 2 = 0)
    (hv : -B * vt ^ 2 + 2 * C * vt * vr + A * vr ^ 2 = 0)
    (hΔ : ut * vr - ur * vt ≠ 0) (hD : 0 < A * B + C * C)
    (c1 : ut * τa + ur * ϱa = 1) (c2 : ut * τb + ur * ϱb = 0)
    (c3 : vt * τa + vr * ϱa = 0) (c4 : vt * τb + vr * ϱb = 1) :
    A * τa ^ 2 - 2 * C * (τa * ϱa) - B * ϱa ^ 2 = 0 ∧
    -A * τb ^ 2 + 2 * C * (τb * ϱb) + B * ϱb ^ 2 = 0 ∧
    -A * (τa * τb) + C * (τa * ϱb + τb * ϱa) + B * (ϱa * ϱb) ≠ 0 ∧
    τa * ϱb - τb * ϱa ≠ 0 ∧
    A = -2 * (-A * (τa * τb) + C * (τa * ϱb + τb * ϱa) + B * (ϱa * ϱb)) * (ut * vt) ∧
    C = (-A * (τa * τb) + C * (τa * ϱb + τb * ϱa) + B * (ϱa * ϱb)) * (ut * vr + ur * vt) ∧
    B = 2 * (-A * (τa * τb) + C * (τa * ϱb + τb * ϱa) + B * (ϱa * ϱb)) * (ur * vr) := by
  obtain ⟨f, hf, hA, hC, hB⟩ := null_alg hu hv hΔ hD
  -- the mixed entry in the new labels is the factor
  have hpC : -A * (τa * τb) + C * (τa * ϱb + τb * ϱa) + B * (ϱa * ϱb) = f := by
    linear_combination -(τa * τb) * hA + (τa * ϱb + τb * ϱa) * hC + (ϱa * ϱb) * hB
      + f * (vt * τb + vr * ϱb) * c1 + f * c4 + f * (vt * τa + vr * ϱa) * c2
  -- the two tables of slopes undo each other, so their determinants multiply to one
  have hJ : (ut * vr - ur * vt) * (τa * ϱb - τb * ϱa) = 1 := by
    linear_combination (vt * τb + vr * ϱb) * c1 + c4 - (vt * τa + vr * ϱa) * c2
  refine ⟨?_, ?_, ?_, right_ne_zero_of_mul_eq_one hJ, ?_, ?_, ?_⟩
  · linear_combination τa ^ 2 * hA - 2 * (τa * ϱa) * hC - ϱa ^ 2 * hB
      - 2 * f * (vt * τa + vr * ϱa) * c1 - 2 * f * c3
  · linear_combination -τb ^ 2 * hA + 2 * (τb * ϱb) * hC + ϱb ^ 2 * hB
      + 2 * f * (vt * τb + vr * ϱb) * c2
  · rw [hpC]
    exact hf
  · rw [hpC]
    exact hA
  · rw [hpC]
    exact hC
  · rw [hpC]
    exact hB

/-! ## The slopes of the inverse labels -/

/-- **The slopes of the inverse labels undo the slopes of the labels** (the chain rule). If
`(τ, ϱ)` on the box `J' × I'` undoes `(u, v)`, that is `u (τ, ϱ) = a` and `v (τ, ϱ) = b`, then
at every point of the box the table of slopes of `(u, v)` times the table of slopes of
`(τ, ϱ)` is the unit table. -/
theorem inverse_labels_slopes {u v τ ϱ : ℝ → ℝ → ℝ} {N : Set (ℝ × ℝ)} {J' I' : Set ℝ}
    (hN : IsOpen N) (hJ' : IsOpen J') (hI' : IsOpen I')
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) N) (hv : ContDiffOn ℝ ∞ (Function.uncurry v) N)
    (hτ : ContDiffOn ℝ ∞ (Function.uncurry τ) (J' ×ˢ I'))
    (hϱ : ContDiffOn ℝ ∞ (Function.uncurry ϱ) (J' ×ˢ I'))
    (hinv : ∀ a ∈ J', ∀ b ∈ I',
      (τ a b, ϱ a b) ∈ N ∧ u (τ a b) (ϱ a b) = a ∧ v (τ a b) (ϱ a b) = b)
    {a b : ℝ} (ha : a ∈ J') (hb : b ∈ I') :
    dt u (τ a b) (ϱ a b) * dt τ a b + dr u (τ a b) (ϱ a b) * dt ϱ a b = 1 ∧
    dt u (τ a b) (ϱ a b) * dr τ a b + dr u (τ a b) (ϱ a b) * dr ϱ a b = 0 ∧
    dt v (τ a b) (ϱ a b) * dt τ a b + dr v (τ a b) (ϱ a b) * dt ϱ a b = 0 ∧
    dt v (τ a b) (ϱ a b) * dr τ a b + dr v (τ a b) (ϱ a b) * dr ϱ a b = 1 := by
  have hmem : J' ×ˢ I' ∈ 𝓝 (a, b) := (hJ'.prod hI').mem_nhds ⟨ha, hb⟩
  have hτd : DifferentiableAt ℝ (Function.uncurry τ) (a, b) :=
    (hτ.contDiffAt hmem).differentiableAt (by simp)
  have hϱd : DifferentiableAt ℝ (Function.uncurry ϱ) (a, b) :=
    (hϱ.contDiffAt hmem).differentiableAt (by simp)
  have hxN : (τ a b, ϱ a b) ∈ N := (hinv a ha b hb).1
  have hud : DifferentiableAt ℝ (Function.uncurry u) (τ a b, ϱ a b) :=
    (hu.contDiffAt (hN.mem_nhds hxN)).differentiableAt (by simp)
  have hvd : DifferentiableAt ℝ (Function.uncurry v) (τ a b, ϱ a b) :=
    (hv.contDiffAt (hN.mem_nhds hxN)).differentiableAt (by simp)
  -- near `(a, b)` the first label is `u (τ, ϱ)` and the second is `v (τ, ϱ)`
  have eu : ∀ᶠ x in 𝓝 (a, b), (fun p _ : ℝ ↦ p) x.1 x.2 = u (τ x.1 x.2) (ϱ x.1 x.2) := by
    filter_upwards [hmem] with x hx
    exact (hinv x.1 hx.1 x.2 hx.2).2.1.symm
  have ev : ∀ᶠ x in 𝓝 (a, b), (fun _ q : ℝ ↦ q) x.1 x.2 = v (τ x.1 x.2) (ϱ x.1 x.2) := by
    filter_upwards [hmem] with x hx
    exact (hinv x.1 hx.1 x.2 hx.2).2.2.symm
  -- the slopes of the two labels themselves
  have d1 : dt (fun p _ : ℝ ↦ p) a b = 1 := by simp [dt]
  have d2 : dr (fun p _ : ℝ ↦ p) a b = 0 := by simp [dr]
  have d3 : dt (fun _ q : ℝ ↦ q) a b = 0 := by simp [dt]
  have d4 : dr (fun _ q : ℝ ↦ q) a b = 1 := by simp [dr]
  exact ⟨(dt_eq_of_comp (S := fun p _ ↦ p) hτd hϱd hud eu).symm.trans d1,
    (dr_eq_of_comp (S := fun p _ ↦ p) hτd hϱd hud eu).symm.trans d2,
    (dt_eq_of_comp (S := fun _ q ↦ q) hτd hϱd hvd ev).symm.trans d3,
    (dr_eq_of_comp (S := fun _ q ↦ q) hτd hϱd hvd ev).symm.trans d4⟩

/-! ## A table whose entries for `dt²` and `dρ²` are zero at a point -/

/-- At a point where the clock and ruler functions are zero, the general round shape has the
entries of the shape with the clock and ruler functions put to zero. -/
theorem genG_zero_congr {A B C S : ℝ → ℝ → ℝ} {y : Coords 4} (hA : A (y 0) (y 1) = 0)
    (hB : B (y 0) (y 1) = 0) (i j : Fin 4) :
    genG A B C S i j y = genG zero2 zero2 C S i j y := by
  fin_cases i <;> fin_cases j <;> simp [genG, sep2, gTR, gΘ, negA, zero2, hA, hB]

/-- The same for the inverse table. -/
theorem genGinv_zero_congr {A B C S : ℝ → ℝ → ℝ} {y : Coords 4} (hA : A (y 0) (y 1) = 0)
    (hB : B (y 0) (y 1) = 0) (i j : Fin 4) :
    genGinv A B C S i j y = genGinv zero2 zero2 C S i j y := by
  fin_cases i <;> fin_cases j <;> simp [genGinv, ginvTR, ginvΘ, det2, zero2, hA, hB]

/-! ## The result -/

/-- **The round shape in labels along the paths of light.** -/
theorem exists_nullForm {A B C S : ℝ → ℝ → ℝ} {J I : Set ℝ} (hset : SettingG A B C S J I)
    (hE : IsEmptyOnG A B C S J I)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (J ×ˢ I))
    (hB : ContDiffOn ℝ ∞ (Function.uncurry B) (J ×ˢ I))
    (hC : ContDiffOn ℝ ∞ (Function.uncurry C) (J ×ˢ I))
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (J ×ˢ I))
    {t₀ ρ₀ : ℝ} (ht₀ : t₀ ∈ J) (hρ₀ : ρ₀ ∈ I) :
    ∃ (u v : ℝ → ℝ → ℝ) (N : Set (ℝ × ℝ)) (F S' : ℝ → ℝ → ℝ) (J' I' : Set ℝ),
      IsOpen N ∧ (t₀, ρ₀) ∈ N ∧ N ⊆ J ×ˢ I ∧
      ContDiffOn ℝ ∞ (Function.uncurry u) N ∧ ContDiffOn ℝ ∞ (Function.uncurry v) N ∧
      SettingG zero2 zero2 F S' J' I' ∧ IsEmptyOnG zero2 zero2 F S' J' I' ∧
      ContDiffOn ℝ ∞ (Function.uncurry F) (J' ×ˢ I') ∧
      ContDiffOn ℝ ∞ (Function.uncurry S') (J' ×ˢ I') ∧
      ∀ x ∈ N, u x.1 x.2 ∈ J' ∧ v x.1 x.2 ∈ I' ∧
        S x.1 x.2 = S' (u x.1 x.2) (v x.1 x.2) ∧
        A x.1 x.2 = -2 * F (u x.1 x.2) (v x.1 x.2) * (dt u x.1 x.2 * dt v x.1 x.2) ∧
        C x.1 x.2 = F (u x.1 x.2) (v x.1 x.2)
          * (dt u x.1 x.2 * dr v x.1 x.2 + dr u x.1 x.2 * dt v x.1 x.2) ∧
        B x.1 x.2 = 2 * F (u x.1 x.2) (v x.1 x.2) * (dr u x.1 x.2 * dr v x.1 x.2) ∧
        massFn zero2 zero2 F S' (u x.1 x.2) (v x.1 x.2) = massFn A B C S x.1 x.2 := by
  -- the two labels along the paths of light, and their inverse on a box
  obtain ⟨u, v, N₀, hN₀, h₀, hN₀sub, hu₀, hv₀, hnu, hnv, hΔ⟩ :=
    exists_nullLabels hset.openJ hset.openI hA hB hC hset.spaceTime ht₀ hρ₀
  obtain ⟨τ, ϱ, J', I', N, hJ', hJ'c, hI', hI'c, hN, h₀', hNsub, hτ, hϱ, hinv, hfwd⟩ :=
    exists_inverse_labels hN₀ hu₀ hv₀ h₀ (hΔ _ h₀)
  have hu : ContDiffOn ℝ ∞ (Function.uncurry u) N := hu₀.mono hNsub
  have hv : ContDiffOn ℝ ∞ (Function.uncurry v) N := hv₀.mono hNsub
  have hNJI : N ⊆ J ×ˢ I := hNsub.trans hN₀sub
  -- on the box: no `da²`, no `db²`, a mixed entry that is not zero, a genuine change of labels,
  -- and the three relations at the point `(τ, ϱ)`
  have hbox : ∀ a ∈ J', ∀ b ∈ I',
      pullA A B C τ ϱ a b = 0 ∧ pullB A B C τ ϱ a b = 0 ∧ pullC A B C τ ϱ a b ≠ 0 ∧
      dt τ a b * dr ϱ a b - dr τ a b * dt ϱ a b ≠ 0 ∧
      A (τ a b) (ϱ a b) = -2 * pullC A B C τ ϱ a b
        * (dt u (τ a b) (ϱ a b) * dt v (τ a b) (ϱ a b)) ∧
      C (τ a b) (ϱ a b) = pullC A B C τ ϱ a b
        * (dt u (τ a b) (ϱ a b) * dr v (τ a b) (ϱ a b)
          + dr u (τ a b) (ϱ a b) * dt v (τ a b) (ϱ a b)) ∧
      B (τ a b) (ϱ a b) = 2 * pullC A B C τ ϱ a b
        * (dr u (τ a b) (ϱ a b) * dr v (τ a b) (ϱ a b)) := by
    intro a ha b hb
    have hxN : (τ a b, ϱ a b) ∈ N := (hinv a ha b hb).1
    have hxJI : (τ a b, ϱ a b) ∈ J ×ˢ I := hNJI hxN
    obtain ⟨c1, c2, c3, c4⟩ := inverse_labels_slopes hN hJ' hI' hu hv hτ hϱ hinv ha hb
    exact null_pull_alg (hnu _ (hNsub hxN)) (hnv _ (hNsub hxN)) (hΔ _ (hNsub hxN))
      (hset.spaceTime _ hxJI.1 _ hxJI.2) c1 c2 c3 c4
  -- the table in the new labels is in the setting and empty
  obtain ⟨hset', hE', -, -, hC', hS'⟩ :=
    nullTable hset hE hA hB hC hS hJ' hJ'c hI' hI'c hτ hϱ
      (fun a ha b hb ↦ hNJI (hinv a ha b hb).1) (fun a ha b hb ↦ (hbox a ha b hb).2.2.2.1)
  refine ⟨u, v, N, pullC A B C τ ϱ, pullS S τ ϱ, J', I', hN, h₀', hNJI, hu, hv, ?_, ?_, hC',
    hS', fun x hx ↦ ?_⟩
  · -- the setting, with the clock and ruler functions put to zero
    exact
      { openJ := hJ'
        onePieceJ := hJ'c
        openI := hI'
        onePieceI := hI'c
        smoothA := fun a _ b _ ↦
          (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : ℝ × ℝ ↦ (0 : ℝ)) (a, b))
        smoothB := fun a _ b _ ↦
          (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : ℝ × ℝ ↦ (0 : ℝ)) (a, b))
        smoothC := hset'.smoothC
        smoothS := hset'.smoothS
        spaceTime := fun a ha b hb ↦ by
          have h : det2 zero2 zero2 (pullC A B C τ ϱ) a b
              = pullC A B C τ ϱ a b * pullC A B C τ ϱ a b := by
            simp [det2, zero2]
          rw [h]
          exact mul_self_pos.2 (hbox a ha b hb).2.2.1
        S_pos := hset'.S_pos }
  · -- empty: near every point of the box the two tables have the same entries
    intro x hx0 hx1 hxs
    have hnear : ∀ᶠ y in 𝓝 x, y 0 ∈ J' ∧ y 1 ∈ I' :=
      ((hJ'.preimage (continuous_apply 0)).inter (hI'.preimage (continuous_apply 1))).mem_nhds
        ⟨hx0, hx1⟩
    refine (isRicciFlatAt_congr (fun i j ↦ ?_) (fun i j ↦ ?_)).1 (hE' x hx0 hx1 hxs)
    · filter_upwards [hnear] with y hy
      exact genG_zero_congr (hbox _ hy.1 _ hy.2).1 (hbox _ hy.1 _ hy.2).2.1 i j
    · filter_upwards [hnear] with y hy
      exact genGinv_zero_congr (hbox _ hy.1 _ hy.2).1 (hbox _ hy.1 _ hy.2).2.1 i j
  · -- at a point of the neighbourhood
    obtain ⟨hua, hvb, hτx, hϱx⟩ := hfwd x hx
    obtain ⟨-, -, -, -, rA, rC, rB⟩ := hbox _ hua _ hvb
    rw [hτx, hϱx] at rA rC rB
    have hmem : N ∈ 𝓝 (x.1, x.2) := hN.mem_nhds hx
    have hud : DifferentiableAt ℝ (Function.uncurry u) (x.1, x.2) :=
      (hu.contDiffAt hmem).differentiableAt (by simp)
    have hvd : DifferentiableAt ℝ (Function.uncurry v) (x.1, x.2) :=
      (hv.contDiffAt hmem).differentiableAt (by simp)
    have hS'd : DifferentiableAt ℝ (Function.uncurry (pullS S τ ϱ))
        (u x.1 x.2, v x.1 x.2) :=
      (hS'.contDiffAt ((hJ'.prod hI').mem_nhds ⟨hua, hvb⟩)).differentiableAt (by simp)
    -- the size of the spheres is the new one after the labels, on the neighbourhood
    have hSS' : ∀ y ∈ N, S y.1 y.2 = pullS S τ ϱ (u y.1 y.2) (v y.1 y.2) := by
      intro y hy
      obtain ⟨-, -, e1, e2⟩ := hfwd y hy
      change S y.1 y.2 = S (τ (u y.1 y.2) (v y.1 y.2)) (ϱ (u y.1 y.2) (v y.1 y.2))
      rw [e1, e2]
    have hSeq : ∀ᶠ y in 𝓝 (x.1, x.2), S y.1 y.2 = pullS S τ ϱ (u y.1 y.2) (v y.1 y.2) :=
      Filter.eventually_of_mem hmem hSS'
    exact ⟨hua, hvb, hSS' x hx, rA, rC, rB,
      massFn_null_eq hud hvd hS'd hSeq rA rC rB (hΔ x (hNsub hx))⟩

end Rim

end GravityInLean
