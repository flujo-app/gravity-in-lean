/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.KruskalChart
public import GravityInLean.Global.SchwChart
public import GravityInLean.Global.TableHess
public import GravityInLean.Global.KretschmannKept
public import GravityInLean.Global.KretschmannKruskal
public import GravityInLean.Global.HessKept
public import GravityInLean.Global.HessKruskal
public import GravityInLean.Global.SchwScalars
public import GravityInLean.Join.CarryPointwise

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# The mass is fixed by the space-time

A map of coordinate space that carries Kruskal's or Schwarzschild's table of one mass to the
table of another mass does not exist unless the masses agree (the curvature scalar and the
squared length of the slope of the radius are kept). So length-keeping maps into models of two
different masses never both exist: `globalMassUnique`.

How it is done. A table "has the radius `ρ` and the mass `m`" (`HasRadius`) when its curvature
scalar is `-48 m² / ρ⁶` and the squared length of the slope of `ρ` is `1 - 2m / ρ`. Kruskal's
table has the radius `kruskalRad m`, Schwarzschild's the label `r`. For a map that carries one
such table to another:

* the curvature scalar is kept, so `(m ρ'³)² = (m' ρ³)²` (`HasRadius.scalar_kept`);
* so `m ρ'³ = ± m' ρ³` on the open set, and the squared slope length of both sides is kept
  (`HasRadius.slope_kept`);
* with the sign `+` the two relations at one point give `m = m'` (`mass_alg_same`);
* with the sign `-` (a positive against a negative mass) they fix the radius `ρ` at every point
  of the open set (`mass_alg_opp`), but Kruskal's radius is not constant on an open set
  (`exists_kruskalRad_ne`).

Two charts of the curved space in which the length measure reads as two tables give such a map:
the change of charts (`carriesTableAt_changeOfCharts`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set Filter

open scoped Manifold ContDiff Topology

/-! ## Slopes of a function of a function -/

/-- The slope of an outer function of one number after a function of the labels: the outer slope
times the slope. -/
theorem slope_outer {n : ℕ} {φ : ℝ → ℝ} {φ' : ℝ} {F : Coords n → ℝ} {x : Coords n}
    (hφ : HasDerivAt φ φ' (F x)) (hF : DifferentiableAt ℝ F x) (a : Fin n) :
    slope a (fun y ↦ φ (F y)) x = φ' * slope a F x := by
  have h1 := hasDerivAt_slope hF a
  have h2 : HasDerivAt φ φ' (F (Function.update x a (x a))) := by
    rw [Function.update_eq_self]
    exact hφ
  exact (HasDerivAt.comp (h := fun s ↦ F (Function.update x a s)) (x := x a) h2 h1).deriv

/-- The squared slope length of an outer function after `F`: the square of the outer slope
times the squared slope length of `F`. -/
theorem gradSq_outer {n : ℕ} {ginv : Fin n → Fin n → Coords n → ℝ} {φ : ℝ → ℝ} {φ' : ℝ}
    {F : Coords n → ℝ} {x : Coords n} (hφ : HasDerivAt φ φ' (F x))
    (hF : DifferentiableAt ℝ F x) :
    gradSq ginv (fun y ↦ φ (F y)) x = φ' ^ 2 * gradSq ginv F x := by
  simp only [gradSq, slope_outer hφ hF, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring

/-- Two functions that agree near `x` have the same squared slope length at `x`. -/
theorem gradSq_congr {n : ℕ} {ginv : Fin n → Fin n → Coords n → ℝ} {F F' : Coords n → ℝ}
    {x : Coords n} (h : F =ᶠ[𝓝 x] F') : gradSq ginv F x = gradSq ginv F' x := by
  simp only [gradSq, slope_congr h]

/-- The slope of `a s³` is `3 a s²`. -/
theorem hasDerivAt_const_mul_cube (a t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ a * s ^ 3) (3 * a * t ^ 2) t :=
  ((hasDerivAt_pow 3 t).const_mul a).congr_deriv (by push_cast; ring)

/-! ## A table with a radius and a mass -/

/-- **The table `g` has the radius `ρ` and the mass `m` on the region `s`:** the table is
regular there, `ρ` is smooth and positive, the curvature scalar is `-48 m² / ρ⁶`, and the
squared length of the slope of `ρ` is `1 - 2m / ρ`. -/
structure HasRadius (g ginv : Fin 4 → Fin 4 → Coords 4 → ℝ) (s : Set (Coords 4))
    (ρ : Coords 4 → ℝ) (m : ℝ) : Prop where
  /-- The table is regular on the region, with the inverse table `ginv`. -/
  regular : IsRegularTableOn g ginv s
  /-- The radius is smooth. -/
  smooth : ∀ x ∈ s, ContDiffAt ℝ ∞ ρ x
  /-- The radius is positive. -/
  pos : ∀ x ∈ s, 0 < ρ x
  /-- The curvature scalar is `-48 m² / ρ⁶`. -/
  scalar : ∀ x ∈ s, kretschmann g ginv x = -48 * m ^ 2 / ρ x ^ 6
  /-- The squared length of the slope of the radius is `1 - 2m / ρ`. -/
  slopeSq : ∀ x ∈ s, gradSq ginv ρ x = 1 - 2 * m / ρ x

section Generic

variable {g ginv h hinv : Fin 4 → Fin 4 → Coords 4 → ℝ} {s t : Set (Coords 4)}
  {ρ ρ' : Coords 4 → ℝ} {m m' : ℝ} {f : Coords 4 → Coords 4} {W : Set (Coords 4)}

/-- **The curvature scalar is kept:** where `f` carries a table with radius `ρ` and mass `m` to
one with radius `ρ'` and mass `m'`, `(m ρ'³)² = (m' ρ³)²`. -/
theorem HasRadius.scalar_kept (hρ : HasRadius g ginv s ρ m) (hρ' : HasRadius h hinv t ρ' m')
    {x : Coords 4} (hx : x ∈ s) (hfx : f x ∈ t) (hf : CarriesTableAt g h f x) :
    (m * ρ' (f x) ^ 3) ^ 2 = (m' * ρ x ^ 3) ^ 2 := by
  have h1 := kretschmann_eq_of_carries hρ.regular hρ'.regular hx hfx hf
  rw [hρ'.scalar _ hfx, hρ.scalar _ hx] at h1
  have h2 := (div_eq_div_iff (pow_ne_zero 6 (hρ'.pos _ hfx).ne')
    (pow_ne_zero 6 (hρ.pos x hx).ne')).mp h1
  linear_combination (1 / 48 : ℝ) * h2

/-- **The squared slope length is kept:** if `a ρ'³ = b ρ³` along `f` on the open set `W`, then
the squared slope lengths of the two sides agree at every point of `W`. -/
theorem HasRadius.slope_kept (hρ : HasRadius g ginv s ρ m) (hρ' : HasRadius h hinv t ρ' m')
    (hW : IsOpen W) (hWs : W ⊆ s) (hfW : ∀ x ∈ W, f x ∈ t)
    (hf : ∀ x ∈ W, CarriesTableAt g h f x) {a b : ℝ}
    (hab : ∀ y ∈ W, a * ρ' (f y) ^ 3 = b * ρ y ^ 3) {x : Coords 4} (hx : x ∈ W) :
    (3 * a * ρ' (f x) ^ 2) ^ 2 * gradSq hinv ρ' (f x)
      = (3 * b * ρ x ^ 2) ^ 2 * gradSq ginv ρ x := by
  have hxs := hWs hx
  have hfx := hfW x hx
  have hρd : DifferentiableAt ℝ ρ x := (hρ.smooth x hxs).differentiableAt (by simp)
  have hρ'c := hρ'.smooth _ hfx
  have hρ'd : DifferentiableAt ℝ ρ' (f x) := hρ'c.differentiableAt (by simp)
  have hF : ContDiffAt ℝ ∞ (fun z ↦ a * ρ' z ^ 3) (f x) := by fun_prop
  have e1 : gradSq ginv (fun y ↦ a * ρ' (f y) ^ 3) x
      = gradSq hinv (fun z ↦ a * ρ' z ^ 3) (f x) :=
    gradSq_of_carries (F := fun z ↦ a * ρ' z ^ 3) hρ.regular hρ'.regular hxs hfx (hf x hx) hF
  have e2 : gradSq hinv (fun z ↦ a * ρ' z ^ 3) (f x)
      = (3 * a * ρ' (f x) ^ 2) ^ 2 * gradSq hinv ρ' (f x) :=
    gradSq_outer (φ := fun s ↦ a * s ^ 3) (F := ρ') (hasDerivAt_const_mul_cube a (ρ' (f x)))
      hρ'd
  have e3 : gradSq ginv (fun y ↦ a * ρ' (f y) ^ 3) x = gradSq ginv (fun y ↦ b * ρ y ^ 3) x :=
    gradSq_congr (Filter.eventuallyEq_of_mem (hW.mem_nhds hx) hab)
  have e4 : gradSq ginv (fun y ↦ b * ρ y ^ 3) x = (3 * b * ρ x ^ 2) ^ 2 * gradSq ginv ρ x :=
    gradSq_outer (φ := fun s ↦ b * s ^ 3) (F := ρ) (hasDerivAt_const_mul_cube b (ρ x)) hρd
  exact e2.symm.trans (e1.symm.trans (e3.trans e4))

/-- The algebra for two masses of the same sign: the kept scalar (`E1`) and the kept squared
slope length (`E2`, with `Q`, `Q'` the squared slope lengths of the two radii) give equal
masses. -/
theorem mass_alg_same {m m' r G Q Q' : ℝ} (hm' : m' ≠ 0) (hr : 0 < r) (hG : 0 < G)
    (E1 : m * G ^ 3 = m' * r ^ 3) (EQ' : G * Q' = G - 2 * m') (EQ : r * Q = r - 2 * m)
    (E2 : (3 * m * G ^ 2) ^ 2 * Q' = (3 * m' * r ^ 2) ^ 2 * Q) : m = m' := by
  have A : m ^ 2 * G ^ 3 * (G - 2 * m') = m' ^ 2 * r ^ 3 * (r - 2 * m) := by
    refine mul_left_cancel₀ (mul_ne_zero hG.ne' hr.ne') ?_
    linear_combination (G * r / 9) * E2 - r * m ^ 2 * G ^ 4 * EQ' + G * m' ^ 2 * r ^ 4 * EQ
  have B : m * G = m' * r := by
    refine mul_left_cancel₀ (mul_ne_zero hm' (pow_ne_zero 3 hr.ne')) ?_
    linear_combination A - m * (G - 2 * m') * E1
  have C : G ^ 2 = r ^ 2 := by
    refine mul_left_cancel₀ (mul_ne_zero hm' hr.ne') ?_
    linear_combination E1 - G ^ 2 * B
  have hGr : G = r := by
    have h0 : (G - r) * (G + r) = 0 := by linear_combination C
    rcases mul_eq_zero.mp h0 with h1 | h1
    · linarith
    · linarith
  rw [hGr] at B
  exact mul_right_cancel₀ hr.ne' B

/-- The algebra for a mass `m` against a mass `-n` of the other sign: the kept scalar and the
kept squared slope length tie the radius `r` to the two masses. -/
theorem mass_alg_opp {m n r G Q Q' : ℝ} (hn : n ≠ 0) (hr : 0 < r) (hG : 0 < G)
    (E1 : m * G ^ 3 = n * r ^ 3) (EQ' : G * Q' = G + 2 * n) (EQ : r * Q = r - 2 * m)
    (E2 : (3 * m * G ^ 2) ^ 2 * Q' = (3 * n * r ^ 2) ^ 2 * Q) :
    n ^ 2 * (r - 4 * m) ^ 3 = m ^ 2 * r ^ 3 := by
  have A : m ^ 2 * G ^ 3 * (G + 2 * n) = n ^ 2 * r ^ 3 * (r - 2 * m) := by
    refine mul_left_cancel₀ (mul_ne_zero hG.ne' hr.ne') ?_
    linear_combination (G * r / 9) * E2 - r * m ^ 2 * G ^ 4 * EQ' + G * n ^ 2 * r ^ 4 * EQ
  have B : m * G = n * (r - 4 * m) := by
    refine mul_left_cancel₀ (mul_ne_zero hn (pow_ne_zero 3 hr.ne')) ?_
    linear_combination A - m * (G + 2 * n) * E1
  refine mul_left_cancel₀ hn ?_
  linear_combination m ^ 2 * E1
    - ((n * (r - 4 * m)) ^ 2 + n * (r - 4 * m) * (m * G) + (m * G) ^ 2) * B

/-- **Same sign: the masses agree.** If `f` carries a table with radius `ρ` and mass `m` to one
with radius `ρ'` and mass `m'` on an open set that is not empty, neither mass is zero, and
`m ρ'³ = m' ρ³` there, then `m = m'`. -/
theorem HasRadius.mass_eq_same (hρ : HasRadius g ginv s ρ m) (hρ' : HasRadius h hinv t ρ' m')
    (hm' : m' ≠ 0) (hW : IsOpen W) (hne : W.Nonempty) (hWs : W ⊆ s) (hfW : ∀ x ∈ W, f x ∈ t)
    (hf : ∀ x ∈ W, CarriesTableAt g h f x)
    (hsame : ∀ y ∈ W, m * ρ' (f y) ^ 3 = m' * ρ y ^ 3) : m = m' := by
  obtain ⟨x, hx⟩ := hne
  have hr := hρ.pos x (hWs hx)
  have hG := hρ'.pos _ (hfW x hx)
  have EQ' : ρ' (f x) * gradSq hinv ρ' (f x) = ρ' (f x) - 2 * m' := by
    rw [hρ'.slopeSq _ (hfW x hx)]
    field_simp
  have EQ : ρ x * gradSq ginv ρ x = ρ x - 2 * m := by
    rw [hρ.slopeSq _ (hWs hx)]
    field_simp
  exact mass_alg_same hm' hr hG (hsame x hx) EQ' EQ
    (hρ.slope_kept hρ' hW hWs hfW hf hsame hx)

/-- **Opposite signs: the radius is tied to the masses.** If `f` carries a table with radius
`ρ` and mass `m` to one with radius `ρ'` and mass `m'` on an open set, `m'` is not zero, and
`m ρ'³ = -m' ρ³` there, then `m'² (ρ - 4m)³ = m² ρ³` at every point of the set. -/
theorem HasRadius.radius_of_opp (hρ : HasRadius g ginv s ρ m) (hρ' : HasRadius h hinv t ρ' m')
    (hm' : m' ≠ 0) (hW : IsOpen W) (hWs : W ⊆ s) (hfW : ∀ x ∈ W, f x ∈ t)
    (hf : ∀ x ∈ W, CarriesTableAt g h f x)
    (hopp : ∀ y ∈ W, m * ρ' (f y) ^ 3 = -m' * ρ y ^ 3) {x : Coords 4} (hx : x ∈ W) :
    m' ^ 2 * (ρ x - 4 * m) ^ 3 = m ^ 2 * ρ x ^ 3 := by
  have hr := hρ.pos x (hWs hx)
  have hG := hρ'.pos _ (hfW x hx)
  have EQ' : ρ' (f x) * gradSq hinv ρ' (f x) = ρ' (f x) + 2 * -m' := by
    rw [hρ'.slopeSq _ (hfW x hx)]
    field_simp
    ring
  have EQ : ρ x * gradSq ginv ρ x = ρ x - 2 * m := by
    rw [hρ.slopeSq _ (hWs hx)]
    field_simp
  have key := mass_alg_opp (neg_ne_zero.mpr hm') hr hG (hopp x hx) EQ' EQ
    (hρ.slope_kept hρ' hW hWs hfW hf hopp hx)
  linear_combination key

end Generic

/-! ## Kruskal's table and Schwarzschild's table have a radius and a mass -/

/-- Kruskal's table of a positive mass has the radius `kruskalRad m` and the mass `m`. -/
theorem kruskal_hasRadius {m : ℝ} (hm : 0 < m) :
    HasRadius (kruskalG m) (genGinv (kruskalA m) (kruskalA m) zero2 (kruskalS m)) kruskalRegion
      (kruskalRad m) m where
  regular := kruskal_regular hm
  smooth := fun x hx ↦ by
    have h1 : ContDiffAt ℝ ∞ (fun y : Coords 4 ↦ y 1 ^ 2 - y 0 ^ 2) x := by fun_prop
    exact (contDiffAt_kruskalR hm hx.1).comp x h1
  pos := fun _ hx ↦ kruskalR_pos hm hx.1
  scalar := fun _ hx ↦ kretschmann_kruskal hm hx
  slopeSq := fun _ hx ↦ gradSq_kruskalRad hm hx

/-- **Kruskal's radius is not constant on an open set.** -/
theorem exists_kruskalRad_ne {m : ℝ} (hm : 0 < m) {W : Set (Coords 4)} (hW : IsOpen W)
    (hWsub : W ⊆ kruskalRegion) {x : Coords 4} (hx : x ∈ W) :
    ∃ y ∈ W, kruskalRad m y ≠ kruskalRad m x := by
  -- move the label `X` a little, away from zero
  have hγ : Continuous fun s : ℝ ↦ Function.update x 1 s :=
    continuous_const.update 1 continuous_id
  have hx1 : x 1 ∈ (fun s : ℝ ↦ Function.update x 1 s) ⁻¹' W := by
    change Function.update x 1 (x 1) ∈ W
    rw [Function.update_eq_self]
    exact hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hW.preimage hγ) (x 1) hx1
  obtain ⟨s, hs1, hs2⟩ : ∃ s : ℝ, |s - x 1| < ε ∧ x 1 ^ 2 < s ^ 2 := by
    rcases le_or_gt 0 (x 1) with h0 | h0
    · refine ⟨x 1 + ε / 2, ?_, by nlinarith⟩
      rw [add_sub_cancel_left, abs_of_pos (half_pos hε)]
      linarith
    · refine ⟨x 1 - ε / 2, ?_, by nlinarith⟩
      rw [show x 1 - ε / 2 - x 1 = -(ε / 2) by ring, abs_neg, abs_of_pos (half_pos hε)]
      linarith
  have hy : Function.update x 1 s ∈ W :=
    hball (Metric.mem_ball.mpr (by rw [Real.dist_eq]; exact hs1))
  refine ⟨Function.update x 1 s, hy, fun heq ↦ ?_⟩
  have hy1 : (Function.update x 1 s) 1 = s := Function.update_self 1 s x
  have hy0 : (Function.update x 1 s) 0 = x 0 := Function.update_of_ne (by decide) s x
  have hu : -1 < s ^ 2 - x 0 ^ 2 := by
    have := (hWsub hy).1
    rwa [hy1, hy0] at this
  have heq' : kruskalR m (s ^ 2 - x 0 ^ 2) = kruskalR m (x 1 ^ 2 - x 0 ^ 2) := by
    have : kruskalRad m (Function.update x 1 s) = kruskalR m (s ^ 2 - x 0 ^ 2) := by
      rw [kruskalRad, hy1, hy0]
    rw [← this]
    exact heq
  have h1 := kruskalF_kruskalR hm hu
  rw [heq', kruskalF_kruskalR hm (hWsub hx).1] at h1
  linarith

/-- Schwarzschild's table has the radius `r` (the second label) and the mass `m`, outside. -/
theorem schw_hasRadius (m : ℝ) :
    HasRadius (roundG (schwA m) (schwB m)) (roundGinv (schwA m) (schwB m)) (outside m)
      (fun y ↦ y 1) m where
  regular := schwarzschild_regularTable_outside m
  smooth := fun _ _ ↦ (contDiff_apply ℝ (fun _ : Fin 4 ↦ ℝ) 1).contDiffAt
  pos := fun _ hx ↦ hx.1
  scalar := fun _ hx ↦ kretschmann_schw (BothWays.mem_offRim (Or.inl hx))
  slopeSq := fun x _ ↦ gradSq_schwRad m x

/-! ## The three cases, for maps of coordinate space -/

/-- **Kruskal's tables of two positive masses:** a map that carries one to the other on an open
set that is not empty has equal masses. -/
theorem mass_eq_of_carries_kruskal {m m' : ℝ} (hm : 0 < m) (hm' : 0 < m')
    {f : Coords 4 → Coords 4} {W : Set (Coords 4)} (hW : IsOpen W) (hne : W.Nonempty)
    (hWsub : W ⊆ kruskalRegion) (hfW : ∀ x ∈ W, f x ∈ kruskalRegion)
    (hf : ∀ x ∈ W, CarriesTableAt (kruskalG m) (kruskalG m') f x) : m = m' := by
  have hρ := kruskal_hasRadius hm
  have hρ' := kruskal_hasRadius hm'
  refine hρ.mass_eq_same hρ' hm'.ne' hW hne hWsub hfW hf fun y hy ↦ ?_
  have hr := hρ.pos y (hWsub hy)
  have hG := hρ'.pos _ (hfW y hy)
  have h1 : 0 < m * kruskalRad m' (f y) ^ 3 := by positivity
  have h2 : 0 < m' * kruskalRad m y ^ 3 := by positivity
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ (hρ.scalar_kept hρ' (hWsub hy) (hfW y hy) (hf y hy))
    with h3 | h3
  · exact h3
  · linarith

/-- **Schwarzschild's tables of two masses that are zero or negative:** a map that carries one
to the other on an open set that is not empty has equal masses. -/
theorem mass_eq_of_carries_schw {m m' : ℝ} (hm : m ≤ 0) (hm' : m' ≤ 0)
    {f : Coords 4 → Coords 4} {W : Set (Coords 4)} (hW : IsOpen W) (hne : W.Nonempty)
    (hWsub : W ⊆ outside m) (hfW : ∀ x ∈ W, f x ∈ outside m')
    (hf : ∀ x ∈ W,
      CarriesTableAt (roundG (schwA m) (schwB m)) (roundG (schwA m') (schwB m')) f x) :
    m = m' := by
  have hρ := schw_hasRadius m
  have hρ' := schw_hasRadius m'
  have hsq : ∀ y ∈ W, (m * f y 1 ^ 3) ^ 2 = (m' * y 1 ^ 3) ^ 2 := fun y hy ↦
    hρ.scalar_kept hρ' (hWsub hy) (hfW y hy) (hf y hy)
  have hr : ∀ y ∈ W, 0 < y 1 := fun y hy ↦ (hWsub hy).1
  have hG : ∀ y ∈ W, 0 < f y 1 := fun y hy ↦ (hfW y hy).1
  obtain ⟨x, hx⟩ := id hne
  -- a mass zero on one side forces mass zero on the other
  rcases eq_or_lt_of_le hm with h0 | hneg
  · have h1 : (m' * x 1 ^ 3) ^ 2 = 0 := by rw [← hsq x hx, h0]; ring
    have h2 : m' * x 1 ^ 3 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · rw [h0, h3]
    · exact absurd h3 (pow_ne_zero 3 (hr x hx).ne')
  rcases eq_or_lt_of_le hm' with h0' | hneg'
  · have h1 : (m * f x 1 ^ 3) ^ 2 = 0 := by rw [hsq x hx, h0']; ring
    have h2 : m * f x 1 ^ 3 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hneg.ne
    · exact absurd h3 (pow_ne_zero 3 (hG x hx).ne')
  -- both negative
  refine hρ.mass_eq_same hρ' hneg'.ne hW hne hWsub hfW hf fun y hy ↦ ?_
  have h1 : m * f y 1 ^ 3 < 0 := mul_neg_of_neg_of_pos hneg (pow_pos (hG y hy) 3)
  have h2 : m' * y 1 ^ 3 < 0 := mul_neg_of_neg_of_pos hneg' (pow_pos (hr y hy) 3)
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ (hsq y hy) with h3 | h3
  · exact h3
  · linarith

/-- **Kruskal's table of a positive mass against Schwarzschild's of a mass that is zero or
negative:** no map carries the first to the second on an open set. -/
theorem not_carries_kruskal_schw {m m' : ℝ} (hm : 0 < m) (hm' : m' ≤ 0)
    {f : Coords 4 → Coords 4} {W : Set (Coords 4)} (hW : IsOpen W) (hne : W.Nonempty)
    (hWsub : W ⊆ kruskalRegion) (hfW : ∀ x ∈ W, f x ∈ outside m')
    (hf : ∀ x ∈ W, CarriesTableAt (kruskalG m) (roundG (schwA m') (schwB m')) f x) : False := by
  have hρ := kruskal_hasRadius hm
  have hρ' := schw_hasRadius m'
  have hsq : ∀ y ∈ W, (m * f y 1 ^ 3) ^ 2 = (m' * kruskalRad m y ^ 3) ^ 2 := fun y hy ↦
    hρ.scalar_kept hρ' (hWsub hy) (hfW y hy) (hf y hy)
  have hr : ∀ y ∈ W, 0 < kruskalRad m y := fun y hy ↦ hρ.pos y (hWsub hy)
  have hG : ∀ y ∈ W, 0 < f y 1 := fun y hy ↦ (hfW y hy).1
  have hpos : ∀ y ∈ W, 0 < m * f y 1 ^ 3 := fun y hy ↦ mul_pos hm (pow_pos (hG y hy) 3)
  obtain ⟨x, hx⟩ := hne
  -- mass zero on the other side: the curvature scalar would vanish
  rcases eq_or_lt_of_le hm' with h0 | hneg
  · have h1 : (m * f x 1 ^ 3) ^ 2 = 0 := by rw [hsq x hx, h0]; ring
    exact (hpos x hx).ne' (pow_eq_zero_iff (two_ne_zero) |>.mp h1)
  -- negative mass: the radius would be constant on `W`
  have hopp : ∀ y ∈ W, m * f y 1 ^ 3 = -m' * kruskalRad m y ^ 3 := fun y hy ↦ by
    have h2 : m' * kruskalRad m y ^ 3 < 0 := mul_neg_of_neg_of_pos hneg (pow_pos (hr y hy) 3)
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ (hsq y hy) with h3 | h3
    · linarith [hpos y hy]
    · linarith
  have hP : ∀ y ∈ W, m' ^ 2 * (kruskalRad m y - 4 * m) ^ 3 = m ^ 2 * kruskalRad m y ^ 3 :=
    fun y hy ↦ hρ.radius_of_opp hρ' hneg.ne hW hWsub hfW hf hopp hy
  obtain ⟨y, hy, hyx⟩ := exists_kruskalRad_ne hm hW hWsub hx
  have hcube : ((kruskalRad m y - 4 * m) * kruskalRad m x) ^ 3
      = ((kruskalRad m x - 4 * m) * kruskalRad m y) ^ 3 := by
    refine mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 hneg.ne) (pow_ne_zero 2 hm.ne')) ?_
    linear_combination m ^ 2 * kruskalRad m x ^ 3 * hP y hy
      - m ^ 2 * kruskalRad m y ^ 3 * hP x hx
  have hlin := (Odd.pow_inj (⟨1, rfl⟩ : Odd 3)).mp hcube
  have hzero : m * (kruskalRad m y - kruskalRad m x) = 0 := by
    linear_combination (1 / 4 : ℝ) * hlin
  rcases mul_eq_zero.mp hzero with h1 | h1
  · exact hm.ne' h1
  · exact hyx (sub_eq_zero.mp h1)

/-! ## The change of charts carries the table -/

section Charts

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  [IsManifold 𝓘(ℝ, Coords 4) ∞ M] {g : LengthMeasure 𝓘(ℝ, Coords 4) M}

/-- **Around `q` the length measure reads as the table `G`, in a chart that lands in `t`.** -/
def ReadsNear (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (G : Fin 4 → Fin 4 → Coords 4 → ℝ)
    (t : Set (Coords 4)) (q : M) : Prop :=
  ∃ φ : OpenPartialHomeomorph M (Coords 4),
    φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M ∧ q ∈ φ.source ∧
    ∀ q' ∈ φ.source, φ q' ∈ t ∧
      ∀ v w : TangentSpace 𝓘(ℝ, Coords 4) q',
        g q' v w = flatMeasure (tableMeasure G) (φ q')
          (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q' v)
          (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q' w)

omit [IsManifold 𝓘(ℝ, Coords 4) ∞ M] in
/-- **The change of charts carries the table.** If the length measure reads as the table `G` in
the chart `c` and as the table `G'` in the chart `c'`, then the change of charts, `c'` after the
inverse of `c`, carries `G` to `G'` at every point of the range of `c` that comes from the
domain of `c'`. -/
theorem carriesTableAt_changeOfCharts {c c' : OpenPartialHomeomorph M (Coords 4)}
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M)
    (hc' : c' ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M)
    {G G' : Fin 4 → Fin 4 → Coords 4 → ℝ}
    (hread : ∀ q ∈ c.source, ∀ v w : TangentSpace 𝓘(ℝ, Coords 4) q,
      g q v w = flatMeasure (tableMeasure G) (c q)
        (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) c q v)
        (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) c q w))
    (hread' : ∀ q ∈ c'.source, ∀ v w : TangentSpace 𝓘(ℝ, Coords 4) q,
      g q v w = flatMeasure (tableMeasure G') (c' q)
        (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) c' q v)
        (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) c' q w))
    {x : Coords 4} (hx : x ∈ c.target) (hx' : c.symm x ∈ c'.source) :
    CarriesTableAt G G' (c' ∘ c.symm) x := by
  refine ⟨contMDiffAt_iff_contDiffAt.1
    ((contMDiffAt_of_mem_maximalAtlas hc' hx').comp x
      (contMDiffAt_symm_of_mem_maximalAtlas hc hx)), ?_⟩
  have hopen : IsOpen (c.target ∩ c.symm ⁻¹' c'.source) :=
    c.isOpen_inter_preimage_symm c'.open_source
  filter_upwards [hopen.mem_nhds ⟨hx, hx'⟩] with y hy u v
  have hyt : y ∈ c.target := hy.1
  have hp : c.symm y ∈ c.source := c.map_target hyt
  have hp' : c.symm y ∈ c'.source := hy.2
  have hc'd : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) c' (c.symm y) :=
    (contMDiffAt_of_mem_maximalAtlas hc' hp').mdifferentiableAt (by simp)
  have hcsd : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) c.symm y :=
    (contMDiffAt_symm_of_mem_maximalAtlas hc hyt).mdifferentiableAt (by simp)
  -- the slope of the change of charts: back by `c`, then forth by `c'`
  have e1 : ∀ w : Coords 4, fderiv ℝ (c' ∘ c.symm) y w
      = mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) c' (c.symm y)
        (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) c.symm y w) := fun w ↦ by
    rw [← mfderiv_comp_apply y hc'd hcsd w, mfderiv_eq_fderiv]
    rfl
  have key : ∀ z : Coords 4, z = y →
      flatMeasure (tableMeasure G) z u v = tableMeasure G y u v := by
    rintro z rfl
    rfl
  have e2 : tableMeasure G' ((c' ∘ c.symm) y) (fderiv ℝ (c' ∘ c.symm) y u)
      (fderiv ℝ (c' ∘ c.symm) y v)
      = g (c.symm y) (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) c.symm y u)
        (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) c.symm y v) := by
    rw [e1 u, e1 v]
    exact (hread' (c.symm y) hp' _ _).symm
  have e3 : g (c.symm y) (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) c.symm y u)
      (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) c.symm y v)
      = flatMeasure (tableMeasure G) (c (c.symm y)) u v := by
    rw [hread (c.symm y) hp, Join.mfderiv_symm_comp hc hyt u, Join.mfderiv_symm_comp hc hyt v]
  exact e2.trans (e3.trans (key _ (c.right_inv hyt)))

omit [IsManifold 𝓘(ℝ, Coords 4) ∞ M] in
/-- **Two readings of the length measure around one point give a map that carries one table to
the other** on an open set that is not empty. -/
theorem exists_carries_of_readsNear {G G' : Fin 4 → Fin 4 → Coords 4 → ℝ}
    {t t' : Set (Coords 4)} {q : M} (h : ReadsNear g G t q) (h' : ReadsNear g G' t' q) :
    ∃ (f : Coords 4 → Coords 4) (W : Set (Coords 4)), IsOpen W ∧ W.Nonempty ∧ W ⊆ t ∧
      (∀ x ∈ W, f x ∈ t') ∧ ∀ x ∈ W, CarriesTableAt G G' f x := by
  obtain ⟨φ, hφ, hqφ, hφr⟩ := h
  obtain ⟨φ', hφ', hqφ', hφr'⟩ := h'
  refine ⟨φ' ∘ φ.symm, φ.target ∩ φ.symm ⁻¹' φ'.source,
    φ.isOpen_inter_preimage_symm φ'.open_source, ⟨φ q, φ.map_source hqφ, ?_⟩,
    fun x hx ↦ ?_, fun x hx ↦ (hφr' (φ.symm x) hx.2).1, fun x hx ↦
      carriesTableAt_changeOfCharts hφ hφ' (fun q' hq' ↦ (hφr q' hq').2)
        (fun q' hq' ↦ (hφr' q' hq').2) hx.1 hx.2⟩
  · change φ.symm (φ q) ∈ φ'.source
    rw [φ.left_inv hqφ]
    exact hqφ'
  · have h1 := (hφr _ (φ.map_target hx.1)).1
    rwa [φ.right_inv hx.1] at h1

/-- A length-keeping map into Schwarzschild's whole space-time of a mass that is zero or
negative gives, around every point, a chart landing outside in which the length measure is
Schwarzschild's table. -/
theorem IsSchwarzschildMapOn.readsNear {m : ℝ} {s : Set M} {D : M → Coords 4} (hm : m ≤ 0)
    (hD : IsSchwarzschildMapOn m g D s) (hg : IsSpaceTimeOn g s) {q : M} (hq : q ∈ s) :
    ReadsNear g (roundG (schwA m) (schwB m)) (outside m) q := by
  obtain ⟨φ, hφ, hqφ, hφr⟩ := hD.isSchwarzschildWith hm hg hq
  refine ⟨φ, hφ, hqφ, fun q' hq' ↦ ⟨?_, (hφr q' hq').2⟩⟩
  rcases (hφr q' hq').1 with h1 | h1
  · exact h1
  · have h2 : 0 < φ q' 1 := h1.1
    have h3 : φ q' 1 < 2 * m := h1.2.1
    linarith

/-- **The mass is fixed by the space-time:** length-keeping maps into models of two different
masses never both exist on a region that is not empty. -/
theorem globalMassUnique : GlobalMassUnique := by
  intro M _ _ _ g s hne hg
  obtain ⟨q, hq⟩ := hne
  refine ⟨fun m m' hm hm' D D' hD hD' ↦ ?_, fun m m' hm hm' D D' hD hD' ↦ ?_,
    fun m m' hm hm' D D' hD hD' ↦ ?_⟩
  · obtain ⟨f, W, hW, hWne, hWt, hfW, hf⟩ :=
      exists_carries_of_readsNear (hD.isKruskalNear hg hq) (hD'.isKruskalNear hg hq)
    exact mass_eq_of_carries_kruskal hm hm' hW hWne hWt hfW hf
  · obtain ⟨f, W, hW, hWne, hWt, hfW, hf⟩ :=
      exists_carries_of_readsNear (hD.readsNear hm hg hq) (hD'.readsNear hm' hg hq)
    exact mass_eq_of_carries_schw hm hm' hW hWne hWt hfW hf
  · obtain ⟨f, W, hW, hWne, hWt, hfW, hf⟩ :=
      exists_carries_of_readsNear (hD.isKruskalNear hg hq) (hD'.readsNear hm' hg hq)
    exact not_carries_kruskal_schw hm hm' hW hWne hWt hfW hf

end Charts

end GravityInLean.Curved
