/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Rim.RadiusSmooth
public import GravityInLean.BirkhoffGeneral
public import Mathlib.Analysis.SpecialFunctions.Sqrt

import Mathlib.Tactic

/-!
# The equations in two labels along the paths of light

Board item `task:rim-null-equations`. Step 9 of the route. In labels `a`, `b` along the paths of
light the time-distance part of the table is `2 F da db`: the round shape `genG zero2 zero2 F S`.
Let it be empty, with the mass function equal to `m > 0` everywhere on a box. Write `r = √S` and
`Ω = kruskalF m r` (`kruskalΩ`). Then, with `dt` the slope in `a` and `dr` the slope in `b`:

* `kruskalΩ_mixed`: `(32 m³ / r) · exp (-r / 2m) · Ω_ab = 2 F`;
* `kruskalΩ_product`: `Ω · Ω_ab = Ω_a · Ω_b`.

In this project's conventions (checked here, `null_point`): the size equations and the mass
give `S_ab = F` and `S_a S_b = 2 r (r - 2m) F` for the size `S = r²` of the spheres; and
`Ω_a = exp (r / 2m) / (8 m²) · S_a` (`dt_kruskalΩ`), likewise in `b`, so that
`Ω_ab = F · r · exp (r / 2m) / (16 m³)` (`dt_dr_kruskalΩ_eq`).

On paper, in the textbooks' notation: the size equations for this shape give
`r_ab = (m / r²) · F`, and the mass function gives `1 - 2m / r = 2 r_a r_b / F`. Then
`Ω_ab = G'' r_a r_b + G' r_ab` with `G = kruskalF m`, `G' = (r / 4m²) · exp (r / 2m)`,
`G'' = (1 / 4m²) · (1 + r / 2m) · exp (r / 2m)`, which is `F · r · exp (r / 2m) / (16 m³)`; and
`Ω_a Ω_b = G'² r_a r_b` is `Ω` times the same. The constants are to be checked against this
project's `SizeEquations` and `massFn`; on Kruskal's own table (`a = U`, `b = V`,
`F = -kruskalA / 2`, `Ω = -U V`) both statements hold.
-/

@[expose] public section

namespace GravityInLean

open Set

open scoped ContDiff

namespace Rim

open Curved

/-- Kruskal's function of the radius, read off the size of the spheres:
`kruskalF m r` with `r = √S`. -/
noncomputable def kruskalΩ (m : ℝ) (S : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ := kruskalF m (√(S a b))

/-- `kruskalΩ m S` is smooth where `S` is smooth and positive. -/
theorem contDiffOn_kruskalΩ {S : ℝ → ℝ → ℝ} {J I : Set ℝ} (m : ℝ)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (J ×ˢ I))
    (hpos : ∀ a ∈ J, ∀ b ∈ I, 0 < S a b) :
    ContDiffOn ℝ ∞ (Function.uncurry (kruskalΩ m S)) (J ×ˢ I) := by
  have hG : ContDiff ℝ ∞ (kruskalF m) := by
    have h : ContDiff ℝ ∞ fun r : ℝ ↦ (r / (2 * m) - 1) * Real.exp (r / (2 * m)) := by
      fun_prop
    exact h
  have hsq : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ √(Function.uncurry S p)) (J ×ˢ I) :=
    hS.sqrt fun p hp ↦ (hpos p.1 hp.1 p.2 hp.2).ne'
  exact hG.comp_contDiffOn hsq

/-! ## Slopes in one variable -/

/-- The slope of `s ↦ kruskalF m (√s)` at a positive `s` is `exp (√s / 2m) / (8 m²)`. -/
theorem hasDerivAt_kruskalF_sqrt {m s : ℝ} (hm : m ≠ 0) (hs : 0 < s) :
    HasDerivAt (fun s ↦ kruskalF m (√s)) (Real.exp (√s / (2 * m)) / (8 * m ^ 2)) s := by
  have h := (hasDerivAt_kruskalF hm (√s)).comp s (Real.hasDerivAt_sqrt hs.ne')
  have hr : √s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  refine h.congr_deriv ?_
  field_simp
  ring

/-- The slope of `s ↦ exp (√s / 2m) / (8 m²)` at a positive `s` is
`exp (√s / 2m) / (32 m³ √s)`. -/
theorem hasDerivAt_exp_sqrt {m s : ℝ} (hm : m ≠ 0) (hs : 0 < s) :
    HasDerivAt (fun s ↦ Real.exp (√s / (2 * m)) / (8 * m ^ 2))
      (Real.exp (√s / (2 * m)) / (32 * m ^ 3 * √s)) s := by
  have h := (((Real.hasDerivAt_sqrt hs.ne').div_const (2 * m)).exp).div_const (8 * m ^ 2)
  have hr : √s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  refine h.congr_deriv ?_
  field_simp
  ring

/-! ## The slopes of `Ω` -/

/-- The slope of `Ω` in the first label: `Ω_a = exp (r / 2m) / (8 m²) · S_a`. -/
theorem dt_kruskalΩ {S : ℝ → ℝ → ℝ} {m a b : ℝ} (hm : m ≠ 0) (hS : TwiceSmooth S a b)
    (hpos : 0 < S a b) :
    dt (kruskalΩ m S) a b = Real.exp (√(S a b) / (2 * m)) / (8 * m ^ 2) * dt S a b := by
  have h := (hasDerivAt_kruskalF_sqrt hm hpos).comp a hS.slopeT
  exact h.deriv

/-- The slope of `Ω` in the second label: `Ω_b = exp (r / 2m) / (8 m²) · S_b`. -/
theorem dr_kruskalΩ {S : ℝ → ℝ → ℝ} {m a b : ℝ} (hm : m ≠ 0) (hS : TwiceSmooth S a b)
    (hpos : 0 < S a b) :
    dr (kruskalΩ m S) a b = Real.exp (√(S a b) / (2 * m)) / (8 * m ^ 2) * dr S a b := by
  have h := (hasDerivAt_kruskalF_sqrt hm hpos).comp b hS.slopeR
  exact h.deriv

/-- The mixed slope of `Ω`, by the chain rule alone:
`Ω_ab = exp (r / 2m) / (8 m²) · S_ab + exp (r / 2m) / (32 m³ r) · S_a S_b`. -/
theorem dt_dr_kruskalΩ {S : ℝ → ℝ → ℝ} {J : Set ℝ} {m a b : ℝ} (hm : m ≠ 0) (hJ : IsOpen J)
    (hS : ∀ s ∈ J, TwiceSmooth S s b) (hpos : ∀ s ∈ J, 0 < S s b) (ha : a ∈ J) :
    dt (dr (kruskalΩ m S)) a b
      = Real.exp (√(S a b) / (2 * m)) / (8 * m ^ 2) * dt (dr S) a b
        + Real.exp (√(S a b) / (2 * m)) / (32 * m ^ 3 * √(S a b))
          * (dt S a b * dr S a b) := by
  -- near `a` the slope in the second label is known
  have hev : (fun s ↦ dr (kruskalΩ m S) s b)
      =ᶠ[nhds a] fun s ↦ Real.exp (√(S s b) / (2 * m)) / (8 * m ^ 2) * dr S s b := by
    filter_upwards [hJ.mem_nhds ha] with s hs
    exact dr_kruskalΩ hm (hS s hs) (hpos s hs)
  -- and that is a product, whose slope the product rule gives
  have hK := (hasDerivAt_exp_sqrt hm (hpos a ha)).comp a (hS a ha).slopeT
  have hd : HasDerivAt (fun s ↦ Real.exp (√(S s b) / (2 * m)) / (8 * m ^ 2) * dr S s b)
      (Real.exp (√(S a b) / (2 * m)) / (32 * m ^ 3 * √(S a b)) * dt S a b * dr S a b
        + Real.exp (√(S a b) / (2 * m)) / (8 * m ^ 2) * dt (dr S) a b) a :=
    hK.mul (hS a ha).slopeRT
  have e : dt (dr (kruskalΩ m S)) a b = deriv (fun s ↦ dr (kruskalΩ m S) s b) a := rfl
  rw [e, hev.deriv_eq, hd.deriv]
  ring

/-! ## What the equations say at a point -/

/-- The sum behind `null_point`: from the mixed size equation `w = F (1 - ρ) + p q / (2 S)`, the
squared slope of the radius `ρ = p q / (2 S F)` and the mass `(r / 2) (1 - ρ) = m`, with
`S = r²`: the mixed slope `w` of the size is `F`, and the product `p q` of its two slopes is
`2 r F (r - 2m)`. -/
theorem null_point_algebra {m r Fv S0 p q w ρ : ℝ} (hr : 0 < r) (hF : Fv ≠ 0)
    (hS : S0 = r ^ 2) (hρ : ρ = p * q / (2 * S0 * Fv)) (hmass : r / 2 * (1 - ρ) = m)
    (hw : w = Fv * (1 - ρ) + p * q / (2 * S0)) :
    w = Fv ∧ p * q = 2 * r * Fv * (r - 2 * m) := by
  subst hS
  have hr0 : r ≠ 0 := hr.ne'
  have h1 : 1 - ρ = 2 * m / r := by
    rw [eq_div_iff hr0]
    linear_combination 2 * hmass
  have hpq : p * q = 2 * r * Fv * (r - 2 * m) := by
    have h2 : p * q / (2 * r ^ 2 * Fv) = 1 - 2 * m / r := by
      rw [← hρ]
      linear_combination -h1
    rw [div_eq_iff (mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 2 hr0)) hF)] at h2
    rw [h2]
    field_simp
  refine ⟨?_, hpq⟩
  rw [hw, h1, hpq]
  field_simp
  ring

/-- **The equations in two labels along the paths of light, for the size of the spheres.** In
an empty table `2 F da db + S (sphere)` with the mass `m` everywhere: the mixed slope of the
size is `S_ab = F`, and the product of its two slopes is `S_a S_b = 2 r (r - 2m) F`, with
`r = √S`. -/
theorem null_point {F S : ℝ → ℝ → ℝ} {J I : Set ℝ} (hset : SettingG zero2 zero2 F S J I)
    (hE : IsEmptyOnG zero2 zero2 F S J I) {m : ℝ}
    (hmass : ∀ a ∈ J, ∀ b ∈ I, massFn zero2 zero2 F S a b = m) {a b : ℝ} (ha : a ∈ J)
    (hb : b ∈ I) :
    dt (dr S) a b = F a b
      ∧ dt S a b * dr S a b = 2 * √(S a b) * F a b * (√(S a b) - 2 * m) := by
  have hS0 : 0 < S a b := hset.S_pos a ha b hb
  have hF0 : F a b ≠ 0 := by
    have h : 0 < zero2 a b * zero2 a b + F a b * F a b := hset.spaceTime a ha b hb
    have h' : 0 < F a b * F a b := by
      rw [show zero2 a b = 0 from rfl] at h
      linarith
    exact mul_self_pos.1 h'
  obtain ⟨-, e2, -⟩ := hset.sizeEquations hE ha hb
  have hρ : radiusSlopeSq zero2 zero2 F S a b
      = dt S a b * dr S a b / (2 * S a b * F a b) := by
    have h0 : zero2 a b = 0 := rfl
    simp only [radiusSlopeSq, sizeSlopeSq, det2, h0]
    field_simp
    ring
  have hTR : hessTR zero2 zero2 F S a b = dr (dt S) a b := by
    have h0 : zero2 a b = 0 := rfl
    simp only [hessTR, half, n001, n101, dt_zero2, dr_zero2, h0]
    ring
  rw [hTR, ← (hset.smoothS a ha b hb).swap] at e2
  exact null_point_algebra (Real.sqrt_pos.2 hS0) hF0 (Real.sq_sqrt hS0.le).symm hρ
    (hmass a ha b hb) e2

/-- **The mixed slope of `Ω`, written out:** `Ω_ab = F · r · exp (r / 2m) / (16 m³)`. -/
theorem dt_dr_kruskalΩ_eq {F S : ℝ → ℝ → ℝ} {J I : Set ℝ}
    (hset : SettingG zero2 zero2 F S J I) (hE : IsEmptyOnG zero2 zero2 F S J I) {m : ℝ}
    (hm : 0 < m) (hmass : ∀ a ∈ J, ∀ b ∈ I, massFn zero2 zero2 F S a b = m) {a b : ℝ}
    (ha : a ∈ J) (hb : b ∈ I) :
    dt (dr (kruskalΩ m S)) a b
      = F a b * √(S a b) * Real.exp (√(S a b) / (2 * m)) / (16 * m ^ 3) := by
  obtain ⟨hw, hpq⟩ := null_point hset hE hmass ha hb
  have hr : √(S a b) ≠ 0 := (Real.sqrt_pos.2 (hset.S_pos a ha b hb)).ne'
  have hm0 : m ≠ 0 := hm.ne'
  rw [dt_dr_kruskalΩ hm0 hset.openJ (fun s hs ↦ hset.smoothS s hs b hb)
    (fun s hs ↦ hset.S_pos s hs b hb) ha, hw, hpq]
  field_simp
  ring

/-! ## The two equations for `Ω` -/

/-- **The mixed slope of `Ω` is the factor of the table, up to Kruskal's factor:**
`(32 m³ / r) · exp (-r / 2m) · Ω_ab = 2 F`. -/
theorem kruskalΩ_mixed {F S : ℝ → ℝ → ℝ} {J I : Set ℝ} (hset : SettingG zero2 zero2 F S J I)
    (hE : IsEmptyOnG zero2 zero2 F S J I)
    (_hF : ContDiffOn ℝ ∞ (Function.uncurry F) (J ×ˢ I))
    (_hS : ContDiffOn ℝ ∞ (Function.uncurry S) (J ×ˢ I)) {m : ℝ} (hm : 0 < m)
    (hmass : ∀ a ∈ J, ∀ b ∈ I, massFn zero2 zero2 F S a b = m) :
    ∀ a ∈ J, ∀ b ∈ I,
      32 * m ^ 3 / √(S a b) * Real.exp (-√(S a b) / (2 * m)) * dt (dr (kruskalΩ m S)) a b
        = 2 * F a b := by
  intro a ha b hb
  have hr : √(S a b) ≠ 0 := (Real.sqrt_pos.2 (hset.S_pos a ha b hb)).ne'
  have hm0 : m ≠ 0 := hm.ne'
  have hE0 : Real.exp (√(S a b) / (2 * m)) ≠ 0 := (Real.exp_pos _).ne'
  have e1 : -√(S a b) / (2 * m) = -(√(S a b) / (2 * m)) := by ring
  rw [dt_dr_kruskalΩ_eq hset hE hm hmass ha hb, e1, Real.exp_neg]
  field_simp
  ring

/-- **`Ω` times its mixed slope is the product of its two slopes:** `Ω · Ω_ab = Ω_a · Ω_b`. -/
theorem kruskalΩ_product {F S : ℝ → ℝ → ℝ} {J I : Set ℝ} (hset : SettingG zero2 zero2 F S J I)
    (hE : IsEmptyOnG zero2 zero2 F S J I)
    (_hF : ContDiffOn ℝ ∞ (Function.uncurry F) (J ×ˢ I))
    (_hS : ContDiffOn ℝ ∞ (Function.uncurry S) (J ×ˢ I)) {m : ℝ} (hm : 0 < m)
    (hmass : ∀ a ∈ J, ∀ b ∈ I, massFn zero2 zero2 F S a b = m) :
    ∀ a ∈ J, ∀ b ∈ I,
      kruskalΩ m S a b * dt (dr (kruskalΩ m S)) a b
        = dt (kruskalΩ m S) a b * dr (kruskalΩ m S) a b := by
  intro a ha b hb
  obtain ⟨-, hpq⟩ := null_point hset hE hmass ha hb
  have hS0 : 0 < S a b := hset.S_pos a ha b hb
  have hr : √(S a b) ≠ 0 := (Real.sqrt_pos.2 hS0).ne'
  have hm0 : m ≠ 0 := hm.ne'
  have hsm : TwiceSmooth S a b := hset.smoothS a ha b hb
  have e : Real.exp (√(S a b) / (2 * m)) / (8 * m ^ 2) * dt S a b
        * (Real.exp (√(S a b) / (2 * m)) / (8 * m ^ 2) * dr S a b)
      = (Real.exp (√(S a b) / (2 * m)) / (8 * m ^ 2)) ^ 2 * (dt S a b * dr S a b) := by
    ring
  rw [dt_dr_kruskalΩ_eq hset hE hm hmass ha hb, dt_kruskalΩ hm0 hsm hS0,
    dr_kruskalΩ hm0 hsm hS0, e, hpq]
  unfold kruskalΩ kruskalF
  field_simp
  ring

end Rim

end GravityInLean
