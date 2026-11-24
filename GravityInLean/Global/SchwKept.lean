/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.Checks
public import GravityInLean.Global.TableHess
public import GravityInLean.Global.HessKept
public import GravityInLean.Global.KretschmannKept
public import GravityInLean.Global.KruskalKept
public import GravityInLean.Global.SchwScalars
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Normed.Module.Convex

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# A map of coordinate space that keeps Schwarzschild's table of negative mass

`KeepsSchwOn m f W`: on the open set `W` of the region of Schwarzschild's table (distance
positive, off the poles), the map `f` of coordinate space lands in the region and keeps
Schwarzschild's table of mass `m`. For a negative mass such a map keeps the distance label, keeps
the split of the steps into the `(t, r)` plane and the sphere, and changes time by a shift,
possibly turned round.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

/-- **The map `f` keeps Schwarzschild's table of mass `m` on the open set `W`:** `W` lies in
the region `outside m`, `f` sends `W` into that region, and near every point of `W` the map `f`
is smooth and keeps the lengths of Schwarzschild's table. -/
def KeepsSchwOn (m : ℝ) (f : Coords 4 → Coords 4) (W : Set (Coords 4)) : Prop :=
  IsOpen W ∧ W ⊆ outside m ∧ (∀ x ∈ W, f x ∈ outside m) ∧
    ∀ x ∈ W, CarriesTableAt (roundG (schwA m) (schwB m)) (roundG (schwA m) (schwB m)) f x

variable {m : ℝ} {f : Coords 4 → Coords 4} {W : Set (Coords 4)} {x x₀ : Coords 4}

/-! ## The algebra of the split -/

/-- The algebra behind the split, for a step along the sphere: if the table and the second slope
of the distance label are both kept, the step has no part along time. -/
theorem schw_plane_part_zero {m r A B s S J0 J1 J2 J3 : ℝ} (hm : m < 0) (hr : 0 < r)
    (hA : A ≠ 0) (hJ1 : J1 = 0)
    (E2 : -A * (J0 * J0) + B * (J1 * J1) + r ^ 2 * (J2 * J2) + r ^ 2 * s ^ 2 * (J3 * J3) = S)
    (E1 : (r - 2 * m) / r ^ 2 * S = m / r ^ 2 * (-A * (J0 * J0) + B * (J1 * J1))
      + (r - 2 * m) / r ^ 2 * (r ^ 2 * (J2 * J2) + r ^ 2 * s ^ 2 * (J3 * J3))) : J0 = 0 := by
  subst hJ1
  have hr0 : r ≠ 0 := hr.ne'
  have key : (r - 3 * m) * (A * (J0 * J0)) = 0 := by
    rw [← E2] at E1
    linear_combination (norm := skip) (-r ^ 2) * E1
    field_simp
    ring
  have h3 : r - 3 * m ≠ 0 := ne_of_gt (by linarith)
  exact mul_self_eq_zero.mp
    ((mul_eq_zero.mp ((mul_eq_zero.mp key).resolve_left h3)).resolve_left hA)

/-- The algebra behind the split, for a step in the `(t, r)` plane: if the table and the second
slope of the distance label are both kept, the step has no part along the sphere. -/
theorem schw_sphere_part_zero {m r A B s S J0 J1 J2 J3 : ℝ} (hm : m < 0) (hr : 0 < r)
    (hs : s ≠ 0)
    (E2 : -A * (J0 * J0) + B * (J1 * J1) + r ^ 2 * (J2 * J2) + r ^ 2 * s ^ 2 * (J3 * J3) = S)
    (E1 : m / r ^ 2 * S = m / r ^ 2 * (-A * (J0 * J0) + B * (J1 * J1))
      + (r - 2 * m) / r ^ 2 * (r ^ 2 * (J2 * J2) + r ^ 2 * s ^ 2 * (J3 * J3))) :
    J2 = 0 ∧ J3 = 0 := by
  have hr0 : r ≠ 0 := hr.ne'
  have key : (r - 3 * m) * (r ^ 2 * (J2 * J2) + r ^ 2 * s ^ 2 * (J3 * J3)) = 0 := by
    rw [← E2] at E1
    linear_combination (norm := skip) (-r ^ 2) * E1
    field_simp
    ring
  have h3 : r - 3 * m ≠ 0 := ne_of_gt (by linarith)
  have hQ : r ^ 2 * (J2 * J2) + r ^ 2 * s ^ 2 * (J3 * J3) = 0 :=
    (mul_eq_zero.mp key).resolve_left h3
  have a1 : 0 ≤ r ^ 2 * (J2 * J2) := mul_nonneg (sq_nonneg r) (mul_self_nonneg J2)
  have a2 : 0 ≤ r ^ 2 * s ^ 2 * (J3 * J3) :=
    mul_nonneg (mul_nonneg (sq_nonneg r) (sq_nonneg s)) (mul_self_nonneg J3)
  have b1 : r ^ 2 * (J2 * J2) = 0 := by linarith
  have b2 : r ^ 2 * s ^ 2 * (J3 * J3) = 0 := by linarith
  exact ⟨mul_self_eq_zero.mp ((mul_eq_zero.mp b1).resolve_left (pow_ne_zero 2 hr0)),
    mul_self_eq_zero.mp ((mul_eq_zero.mp b2).resolve_left
      (mul_ne_zero (pow_ne_zero 2 hr0) (pow_ne_zero 2 hs)))⟩

/-! ## Schwarzschild's table, entry by entry -/

/-- The time-time entry of Schwarzschild's table. -/
theorem schwG_time_time (m : ℝ) (y : Coords 4) :
    roundG (schwA m) (schwB m) 0 0 y = -schwA m (y 1) := by
  simp [roundG, diag, roundDiag, sep, gr, gθ, negF, constOne]

/-- The distance-distance entry of Schwarzschild's table. -/
theorem schwG_dist_dist (m : ℝ) (y : Coords 4) :
    roundG (schwA m) (schwB m) 1 1 y = schwB m (y 1) := by
  simp [roundG, diag, roundDiag, sep, gr, gθ, constOne]

/-- The second slope of the distance label for two equal directions along the sphere. -/
theorem hessT_schwRad_sphere (hx : x ∈ BothWays.offRim m) {i : Fin 4} (hi : 2 ≤ i.val) :
    hessT (roundG (schwA m) (schwB m)) (roundGinv (schwA m) (schwB m)) (fun y ↦ y 1) i i x
      = (x 1 - 2 * m) / x 1 ^ 2 * roundG (schwA m) (schwB m) i i x := by
  have h' : ¬ i.val < 2 := not_lt.mpr hi
  simp [hessT_schwRad hx, h', hi]

/-- The second slope of the distance label for two equal directions in the `(t, r)` plane. -/
theorem hessT_schwRad_plane (hx : x ∈ BothWays.offRim m) {i : Fin 4} (hi : i.val < 2) :
    hessT (roundG (schwA m) (schwB m)) (roundGinv (schwA m) (schwB m)) (fun y ↦ y 1) i i x
      = m / x 1 ^ 2 * roundG (schwA m) (schwB m) i i x := by
  simp [hessT_schwRad hx, hi]

/-- **The map keeps the table, entry by entry:** Schwarzschild's table at `f x`, both slots
multiplied by the slopes of `f`, is Schwarzschild's table at `x`. -/
theorem carries_schw_entry
    (hf : CarriesTableAt (roundG (schwA m) (schwB m)) (roundG (schwA m) (schwB m)) f x)
    (i j : Fin 4) :
    -schwA m (f x 1) * (jac f 0 i x * jac f 0 j x) + schwB m (f x 1) * (jac f 1 i x * jac f 1 j x)
        + f x 1 ^ 2 * (jac f 2 i x * jac f 2 j x)
        + f x 1 ^ 2 * sin (f x 2) ^ 2 * (jac f 3 i x * jac f 3 j x)
      = roundG (schwA m) (schwB m) i j x := by
  have hd : DifferentiableAt ℝ f x := hf.1.differentiableAt (by simp)
  have h1 := hf.2.self_of_nhds (Pi.single i 1) (Pi.single j 1)
  have h2 : tableMeasure (roundG (schwA m) (schwB m)) x (Pi.single i 1) (Pi.single j 1)
      = roundG (schwA m) (schwB m) i j x := formOf_single_single _ i j
  rw [← h2, ← h1, schw_apply]
  simp only [jac_eq_fderiv hd]

/-- **The map keeps the second slope of the distance label, entry by entry,** if it keeps the
distance label near `x`. -/
theorem carries_schw_hess (hx : x ∈ outside m) (hfx : f x ∈ outside m)
    (hf : CarriesTableAt (roundG (schwA m) (schwB m)) (roundG (schwA m) (schwB m)) f x)
    (hρ : (fun y ↦ f y 1) =ᶠ[𝓝 x] fun y ↦ y 1) (i j : Fin 4) :
    hessT (roundG (schwA m) (schwB m)) (roundGinv (schwA m) (schwB m)) (fun y ↦ y 1) i j x
      = m / f x 1 ^ 2 * (-schwA m (f x 1) * (jac f 0 i x * jac f 0 j x)
          + schwB m (f x 1) * (jac f 1 i x * jac f 1 j x))
        + (f x 1 - 2 * m) / f x 1 ^ 2 * (f x 1 ^ 2 * (jac f 2 i x * jac f 2 j x)
          + f x 1 ^ 2 * sin (f x 2) ^ 2 * (jac f 3 i x * jac f 3 j x)) := by
  have hF : ContDiffAt ℝ ∞ (fun y : Coords 4 ↦ y 1) (f x) :=
    (contDiff_apply ℝ (fun _ : Fin 4 ↦ ℝ) 1).contDiffAt
  refine ((hessT_congr hρ.symm i j).trans
    (hessT_of_carries (schwarzschild_regularTable_outside m)
      (schwarzschild_regularTable_outside m) hx hfx hf hF i j)).trans ?_
  simp only [hessT_schwRad (BothWays.mem_offRim (Or.inl hfx))]
  conv_lhs => simp [Fin.sum_univ_four, roundG, diag, roundDiag, sep, gr, gθ, negF, sqF, sin2,
    constOne]
  ring

/-! ## What a map that keeps the table does -/

/-- **The distance label is kept** by a map that keeps Schwarzschild's table of negative mass. -/
theorem KeepsSchwOn.radius (hm : m < 0) (h : KeepsSchwOn m f W) (hx : x ∈ W) : f x 1 = x 1 := by
  obtain ⟨-, hsub, hfW, hc⟩ := h
  have hxo := hsub hx
  have hfo := hfW x hx
  have hk := kretschmann_eq_of_carries (schwarzschild_regularTable_outside m)
    (schwarzschild_regularTable_outside m) hxo hfo (hc x hx)
  rw [kretschmann_schw (BothWays.mem_offRim (Or.inl hfo)),
    kretschmann_schw (BothWays.mem_offRim (Or.inl hxo))] at hk
  have h1 : 0 < f x 1 := hfo.1
  have h2 : 0 < x 1 := hxo.1
  have hc0 : -48 * m ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hm.ne)
  have e := (div_eq_div_iff (pow_ne_zero 6 h1.ne') (pow_ne_zero 6 h2.ne')).mp hk
  have h6 : x 1 ^ 6 = f x 1 ^ 6 := mul_left_cancel₀ hc0 e
  exact (pow_left_inj₀ h1.le h2.le (by norm_num)).mp h6.symm

/-- The slopes of the new distance label: one along the distance, zero along the other
labels. -/
theorem KeepsSchwOn.jac_radius (hm : m < 0) (h : KeepsSchwOn m f W) (hx : x ∈ W) (i : Fin 4) :
    jac f 1 i x = if i = 1 then 1 else 0 := by
  have hρ : (fun y ↦ f y 1) =ᶠ[𝓝 x] fun y ↦ y 1 :=
    Filter.eventually_of_mem (h.1.mem_nhds hx) fun y hy ↦ h.radius hm hy
  exact (slope_congr hρ i).trans (slope_radius i x)

/-- **The split is kept:** such a map carries steps in the `(t, r)` plane to steps in the
`(t, r)` plane, and steps along the sphere to steps along the sphere. -/
theorem KeepsSchwOn.split (hm : m < 0) (h : KeepsSchwOn m f W) (hx : x ∈ W)
    (a i : Fin 4) (hai : (a.val < 2 ∧ 2 ≤ i.val) ∨ (2 ≤ a.val ∧ i.val < 2)) :
    jac f a i x = 0 := by
  have hxo := h.2.1 hx
  have hfo := h.2.2.1 x hx
  have hr := h.radius hm hx
  have hρ : (fun y ↦ f y 1) =ᶠ[𝓝 x] fun y ↦ y 1 :=
    Filter.eventually_of_mem (h.1.mem_nhds hx) fun y hy ↦ h.radius hm hy
  have hA : schwA m (x 1) ≠ 0 := (schwA_pos_outside hxo.1 hxo.2.1).ne'
  have E2 := carries_schw_entry (h.2.2.2 x hx) i i
  have E1 := carries_schw_hess hxo hfo (h.2.2.2 x hx) hρ i i
  rw [hr] at E1 E2
  rcases hai with ⟨ha, hi⟩ | ⟨ha, hi⟩
  · -- a step along the sphere has no part in the `(t, r)` plane
    have hi1 : i ≠ 1 := by
      rintro rfl
      exact absurd hi (by decide)
    have hJ1 : jac f 1 i x = 0 := by
      rw [h.jac_radius hm hx i]
      simp [hi1]
    rw [hessT_schwRad_sphere (BothWays.mem_offRim (Or.inl hxo)) hi] at E1
    have hJ0 : jac f 0 i x = 0 := schw_plane_part_zero hm hxo.1 hA hJ1 E2 E1
    fin_cases a
    · exact hJ0
    · exact hJ1
    · exact absurd ha (by decide)
    · exact absurd ha (by decide)
  · -- a step in the `(t, r)` plane has no part along the sphere
    rw [hessT_schwRad_plane (BothWays.mem_offRim (Or.inl hxo)) hi] at E1
    obtain ⟨hJ2, hJ3⟩ := schw_sphere_part_zero hm hxo.1 hfo.2.2 E2 E1
    fin_cases a
    · exact absurd ha (by decide)
    · exact absurd ha (by decide)
    · exact hJ2
    · exact hJ3

/-- The slopes of the new time: one or minus one along time, zero along the other labels. -/
theorem KeepsSchwOn.jac_time (hm : m < 0) (h : KeepsSchwOn m f W) (hx : x ∈ W) :
    jac f 0 0 x ^ 2 = 1 ∧ jac f 0 1 x = 0 ∧ jac f 0 2 x = 0 ∧ jac f 0 3 x = 0 := by
  have hxo := h.2.1 hx
  have hr := h.radius hm hx
  have hA : schwA m (x 1) ≠ 0 := (schwA_pos_outside hxo.1 hxo.2.1).ne'
  have j10 : jac f 1 0 x = 0 := by
    rw [h.jac_radius hm hx 0]
    simp
  have j11 : jac f 1 1 x = 1 := by
    rw [h.jac_radius hm hx 1]
    simp
  have j20 := h.split hm hx 2 0 (Or.inr ⟨by decide, by decide⟩)
  have j30 := h.split hm hx 3 0 (Or.inr ⟨by decide, by decide⟩)
  have j21 := h.split hm hx 2 1 (Or.inr ⟨by decide, by decide⟩)
  have j31 := h.split hm hx 3 1 (Or.inr ⟨by decide, by decide⟩)
  have j02 := h.split hm hx 0 2 (Or.inl ⟨by decide, by decide⟩)
  have j03 := h.split hm hx 0 3 (Or.inl ⟨by decide, by decide⟩)
  have E00 := carries_schw_entry (h.2.2.2 x hx) 0 0
  have E11 := carries_schw_entry (h.2.2.2 x hx) 1 1
  rw [hr, j10, j20, j30, schwG_time_time] at E00
  rw [hr, j11, j21, j31, schwG_dist_dist] at E11
  refine ⟨?_, ?_, j02, j03⟩
  · have e : schwA m (x 1) * (jac f 0 0 x ^ 2 - 1) = 0 := by
      linear_combination (-1 : ℝ) * E00
    have e' : jac f 0 0 x ^ 2 - 1 = 0 := (mul_eq_zero.mp e).resolve_left hA
    linarith
  · have e : schwA m (x 1) * (jac f 0 1 x * jac f 0 1 x) = 0 := by
      linear_combination (-1 : ℝ) * E11
    exact mul_self_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hA)

/-- On a ball where the new time has slope `ε` along time and slope zero along the other
labels, the new time is `ε t + c`. -/
theorem time_of_slopes {τ : Coords 4 → ℝ} {x₀ : Coords 4} {δ ε : ℝ}
    (hd : ∀ y ∈ Metric.ball x₀ δ, DifferentiableAt ℝ τ y)
    (h0 : ∀ y ∈ Metric.ball x₀ δ, slope 0 τ y = ε)
    (h1 : ∀ y ∈ Metric.ball x₀ δ, slope 1 τ y = 0)
    (h2 : ∀ y ∈ Metric.ball x₀ δ, slope 2 τ y = 0)
    (h3 : ∀ y ∈ Metric.ball x₀ δ, slope 3 τ y = 0)
    {y : Coords 4} (hy : y ∈ Metric.ball x₀ δ) (hx₀ : x₀ ∈ Metric.ball x₀ δ) :
    τ y = ε * y 0 + (τ x₀ - ε * x₀ 0) := by
  have hlind : ∀ z : Coords 4, DifferentiableAt ℝ (fun w : Coords 4 ↦ ε * w 0) z := fun z ↦
    (differentiableAt_apply (𝕜 := ℝ) (0 : Fin 4) z).const_mul ε
  have hlin : ∀ (z : Coords 4) (k : Fin 4),
      slope k (fun w : Coords 4 ↦ ε * w 0) z = if k = 0 then ε else 0 := by
    intro z k
    by_cases hk : k = 0
    · subst hk
      have e : slope 0 (fun w : Coords 4 ↦ ε * w 0) z = ε :=
        (slope_along 0 (fun s ↦ ε * s) z).trans (by simp)
      simpa using e
    · simpa [hk] using slope_across (Ne.symm hk) (fun s ↦ ε * s) z
  have hgd : DifferentiableOn ℝ (fun z ↦ τ z - ε * z 0) (Metric.ball x₀ δ) := fun z hz ↦
    ((hd z hz).sub (hlind z)).differentiableWithinAt
  have hg0 : (Metric.ball x₀ δ).EqOn (fderiv ℝ (fun z ↦ τ z - ε * z 0)) 0 := fun z hz ↦ by
    have hτs : ∀ k : Fin 4, slope k τ z = if k = 0 then ε else 0 := by
      have t0 := h0 z hz
      have t1 := h1 z hz
      have t2 := h2 z hz
      have t3 := h3 z hz
      intro k
      fin_cases k <;> simp [t0, t1, t2, t3]
    have hsl : ∀ k : Fin 4, slope k (fun w ↦ τ w - ε * w 0) z = 0 := fun k ↦
      (slope_sub (hd z hz) (hlind z) k).trans (by rw [hτs, hlin, sub_self])
    have hdz : DifferentiableAt ℝ (fun w ↦ τ w - ε * w 0) z := (hd z hz).sub (hlind z)
    refine ContinuousLinearMap.ext fun v ↦ ?_
    rw [clm_apply_eq_sum]
    simp only [← slope_eq_fderiv hdz, hsl, mul_zero, Finset.sum_const_zero]
    rfl
  have hc : τ y - ε * y 0 = τ x₀ - ε * x₀ 0 :=
    Metric.isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball x₀ δ).isPreconnected hgd hg0 hy hx₀
  linarith

/-- **Time is shifted, possibly turned round:** near every point of the region the new time is
`ε t + c` with `ε = 1` or `ε = -1`. -/
theorem KeepsSchwOn.time (hm : m < 0) (h : KeepsSchwOn m f W) (hx₀ : x₀ ∈ W) :
    ∃ ε c : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ᶠ x in 𝓝 x₀, f x 0 = ε * x 0 + c := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp h.1 x₀ hx₀
  have hx₀b : x₀ ∈ Metric.ball x₀ δ := Metric.mem_ball_self hδ
  -- the new time can be differentiated, and its slope along time is continuous
  have hd : ∀ y ∈ Metric.ball x₀ δ, DifferentiableAt ℝ (fun z ↦ f z 0) y := fun y hy ↦
    ((h.2.2.2 y (hball hy)).contDiffAt_part (k := 1) (by simp) 0).differentiableAt (by simp)
  have hJc : ContinuousOn (jac f 0 0) (Metric.ball x₀ δ) := fun y hy ↦
    ((contDiffAt_slope (m := 1) ((h.2.2.2 y (hball hy)).contDiffAt_part (k := 2) (by simp) 0)
      (by simp) (by simp) (by norm_num) 0).differentiableAt
        (by simp)).continuousAt.continuousWithinAt
  have hsq : (Metric.ball x₀ δ).EqOn (jac f 0 0 ^ 2) 1 := fun y hy ↦
    (h.jac_time hm (hball hy)).1
  have key : ∀ ε : ℝ, (Metric.ball x₀ δ).EqOn (jac f 0 0) (fun _ ↦ ε) →
      ∀ᶠ x in 𝓝 x₀, f x 0 = ε * x 0 + (f x₀ 0 - ε * x₀ 0) := fun ε hε ↦
    Filter.eventually_of_mem (Metric.ball_mem_nhds x₀ hδ) fun y hy ↦
      time_of_slopes (τ := fun z ↦ f z 0) hd (fun z hz ↦ hε hz)
        (fun z hz ↦ (h.jac_time hm (hball hz)).2.1)
        (fun z hz ↦ (h.jac_time hm (hball hz)).2.2.1)
        (fun z hz ↦ (h.jac_time hm (hball hz)).2.2.2) hy hx₀b
  rcases (convex_ball x₀ δ).isPreconnected.eq_one_or_eq_neg_one_of_sq_eq hJc hsq with h1 | h1
  · exact ⟨1, f x₀ 0 - 1 * x₀ 0, Or.inl rfl, key 1 h1⟩
  · exact ⟨-1, f x₀ 0 - -1 * x₀ 0, Or.inr rfl, key (-1) h1⟩

end GravityInLean.Curved
