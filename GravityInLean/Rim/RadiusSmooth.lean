/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Rim.Radius
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

import Mathlib.Tactic

/-!
# Kruskal's radius is smooth

Board item `task:rim-radius-smooth`. `kruskalR m` is the inverse of `kruskalF m` on the positive
numbers, and the slope of `kruskalF m` is never zero there. So, by the inverse function theorem
in one variable, `kruskalR m` is smooth on all numbers `u > -1`, with the slope
`4m² / (r · exp (r / 2m))` at `u`, where `r = kruskalR m u`.
-/

@[expose] public section

namespace GravityInLean

open Real Set Filter Topology

open scoped ContDiff

namespace Curved

/-- For a positive mass and `u > -1` the radius is positive. -/
theorem kruskalR_pos {m u : ℝ} (hm : 0 < m) (hu : -1 < u) : 0 < kruskalR m u :=
  (kruskalRadiusSpec m hm u hu).1

/-- For a positive mass and `u > -1` the radius solves its equation. -/
theorem kruskalF_kruskalR {m u : ℝ} (hm : 0 < m) (hu : -1 < u) :
    kruskalF m (kruskalR m u) = u :=
  (kruskalRadiusSpec m hm u hu).2.1

/-- For a positive mass and `r > 0`, `kruskalF m r > -1`. -/
theorem neg_one_lt_kruskalF {m r : ℝ} (hm : 0 < m) (hr : 0 < r) : -1 < kruskalF m r := by
  have hx : 0 < r / (2 * m) := by positivity
  have h1 : -(r / (2 * m)) + 1 < Real.exp (-(r / (2 * m))) :=
    Real.add_one_lt_exp (neg_ne_zero.mpr hx.ne')
  have h2 : Real.exp (-(r / (2 * m))) * Real.exp (r / (2 * m)) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h3 : 0 < Real.exp (r / (2 * m)) := Real.exp_pos _
  have h4 : (-(r / (2 * m)) + 1) * Real.exp (r / (2 * m))
      < Real.exp (-(r / (2 * m))) * Real.exp (r / (2 * m)) :=
    mul_lt_mul_of_pos_right h1 h3
  unfold kruskalF
  linarith

/-- For a positive mass, the radius that belongs to `kruskalF m r` is `r`, for `r > 0`. -/
theorem kruskalR_kruskalF {m r : ℝ} (hm : 0 < m) (hr : 0 < r) :
    kruskalR m (kruskalF m r) = r :=
  ((kruskalRadiusSpec m hm (kruskalF m r) (neg_one_lt_kruskalF hm hr)).2.2 r hr rfl).symm

/-- On the rim: the radius that belongs to `u = 0` is `2m`. -/
theorem kruskalR_zero {m : ℝ} (hm : 0 < m) : kruskalR m 0 = 2 * m := by
  have h0 : kruskalF m (2 * m) = 0 := by
    unfold kruskalF
    rw [div_self (by positivity), sub_self, zero_mul]
  exact ((kruskalRadiusSpec m hm 0 (by norm_num)).2.2 (2 * m) (by positivity) h0).symm

/-- `kruskalF m` is smooth, for every `m`. -/
theorem contDiff_kruskalF (m : ℝ) : ContDiff ℝ ∞ (kruskalF m) := by
  change ContDiff ℝ ∞ (fun r : ℝ => (r / (2 * m) - 1) * Real.exp (r / (2 * m)))
  fun_prop

/-- **The radius is smooth** at every number `u > -1`, for a positive mass. -/
theorem contDiffAt_kruskalR {m u : ℝ} (hm : 0 < m) (hu : -1 < u) :
    ContDiffAt ℝ ∞ (kruskalR m) u := by
  have ha0 : 0 < kruskalR m u := kruskalR_pos hm hu
  have hfa : kruskalF m (kruskalR m u) = u := kruskalF_kruskalR hm hu
  have hf' : kruskalR m u / (4 * m ^ 2) * Real.exp (kruskalR m u / (2 * m)) ≠ 0 := by positivity
  -- the local inverse of `kruskalF m` at the root, from the inverse function theorem
  have hd := (hasDerivAt_kruskalF hm.ne' (kruskalR m u)).hasFDerivAt_equiv hf'
  have hc : ContDiffAt ℝ ∞ (kruskalF m) (kruskalR m u) := (contDiff_kruskalF m).contDiffAt
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hg : ContDiffAt ℝ ∞ (hc.localInverse hd hn) (kruskalF m (kruskalR m u)) :=
    hc.to_localInverse hd hn
  have hga : hc.localInverse hd hn (kruskalF m (kruskalR m u)) = kruskalR m u :=
    hc.localInverse_apply_image hd hn
  have hright : ∀ᶠ y in 𝓝 (kruskalF m (kruskalR m u)),
      kruskalF m (hc.localInverse hd hn y) = y :=
    (hc.hasStrictFDerivAt hd hn).eventually_right_inverse
  have hpos : ∀ᶠ y in 𝓝 (kruskalF m (kruskalR m u)), 0 < hc.localInverse hd hn y :=
    hg.continuousAt.tendsto.eventually (lt_mem_nhds (hga.symm ▸ ha0))
  rw [hfa] at hg hright hpos
  -- it is positive and solves the equation, so it is the radius near `u`
  have hEq : kruskalR m =ᶠ[𝓝 u] hc.localInverse hd hn := by
    filter_upwards [hright, hpos, lt_mem_nhds hu] with y hy1 hy2 hy3
    exact ((kruskalRadiusSpec m hm y hy3).2.2 _ hy2 hy1).symm
  exact hg.congr_of_eventuallyEq hEq

/-- **The radius is smooth** on all numbers `u > -1`, for a positive mass. -/
theorem kruskalRadiusSmooth : KruskalRadiusSmooth :=
  fun _ hm _ hu => (contDiffAt_kruskalR hm hu).contDiffWithinAt

/-- The slope of the radius at `u > -1` is `4m² / (r · exp (r / 2m))` with `r = kruskalR m u`. -/
theorem hasDerivAt_kruskalR {m u : ℝ} (hm : 0 < m) (hu : -1 < u) :
    HasDerivAt (kruskalR m)
      (4 * m ^ 2 / (kruskalR m u * Real.exp (kruskalR m u / (2 * m)))) u := by
  have ha0 : 0 < kruskalR m u := kruskalR_pos hm hu
  have hf' : kruskalR m u / (4 * m ^ 2) * Real.exp (kruskalR m u / (2 * m)) ≠ 0 := by positivity
  have hfg : ∀ᶠ y in 𝓝 u, kruskalF m (kruskalR m y) = y := by
    filter_upwards [lt_mem_nhds hu] with y hy
    exact kruskalF_kruskalR hm hy
  have h := HasDerivAt.of_local_left_inverse (contDiffAt_kruskalR hm hu).continuousAt
    (hasDerivAt_kruskalF hm.ne' (kruskalR m u)) hf' hfg
  have he : (kruskalR m u / (4 * m ^ 2) * Real.exp (kruskalR m u / (2 * m)))⁻¹
      = 4 * m ^ 2 / (kruskalR m u * Real.exp (kruskalR m u / (2 * m))) := by
    have h1 : kruskalR m u ≠ 0 := ha0.ne'
    have h2 : Real.exp (kruskalR m u / (2 * m)) ≠ 0 := (Real.exp_pos _).ne'
    have h3 : m ≠ 0 := hm.ne'
    rw [inv_eq_iff_eq_inv, inv_div]
    field_simp
  rw [← he]
  exact h

end Curved

end GravityInLean
