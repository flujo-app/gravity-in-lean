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
public import GravityInLean.Rim.Table

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# A map of coordinate space that keeps Kruskal's table keeps the radius and the split

`KeepsKruskalOn m f W`: on the open set `W` of the region of Kruskal's table, the map `f` of
coordinate space lands in the region and keeps Kruskal's table of mass `m`.

Such a map keeps the radius (so it keeps `X² - T²`), and it keeps the split of the steps into
the `(T, X)` plane and the sphere.

How it is shown:

* the radius: the map keeps the curvature scalar (`kretschmann_eq_of_carries`), and for
  Kruskal's table the curvature scalar is a fixed multiple of `1 / r⁶`
  (`KeepsKruskalOn.radius_of_value`);
* the split: the map keeps the radius, so it keeps the second slope of the radius
  (`hessT_of_carries`). For Kruskal's table the second slope of the radius is `(m / r²)` times
  the table on the `(T, X)` plane and `((r - 2m) / r²)` times the table on the sphere: two
  different numbers where `r ≠ 3m`. There the steps along the sphere go to steps along the
  sphere (`KeepsKruskalOn.tx_zero_off`); the points with `r ≠ 3m` come near every point
  (`not_eventually_light_eq`) and the slopes of the map are continuous, so the same holds
  everywhere (`KeepsKruskalOn.tx_zero`). Then, because the map keeps the table, the steps in
  the `(T, X)` plane go to steps in the `(T, X)` plane (`KeepsKruskalOn.sphere_zero`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

/-- **The map `f` keeps Kruskal's table of mass `m` on the open set `W`:** `W` lies in the
region of Kruskal's table, `f` sends `W` into that region, and near every point of `W` the map
`f` is smooth and keeps the lengths of Kruskal's table. -/
def KeepsKruskalOn (m : ℝ) (f : Coords 4 → Coords 4) (W : Set (Coords 4)) : Prop :=
  IsOpen W ∧ W ⊆ kruskalRegion ∧ (∀ x ∈ W, f x ∈ kruskalRegion) ∧
    ∀ x ∈ W, CarriesTableAt (kruskalG m) (kruskalG m) f x

variable {m : ℝ} {f : Coords 4 → Coords 4} {W : Set (Coords 4)} {x : Coords 4}

/-! ## Algebra of the two blocks -/

/-- If a two-by-two table keeps `-T² + X²`, a step that is at right angles (in that sense) to
both of its columns is zero. -/
theorem tx_part_zero {a b c d p q : ℝ} (h00 : -(a * a) + c * c = -1)
    (h01 : -(a * b) + c * d = 0) (h11 : -(b * b) + d * d = 1) (e0 : -(p * a) + q * c = 0)
    (e1 : -(p * b) + q * d = 0) : p = 0 ∧ q = 0 := by
  have hdet : (a * d - b * c) ^ 2 = 1 := by
    linear_combination (c * d - a * b) * h01 - (d * d - b * b) * h00 + h11
  have hdet0 : a * d - b * c ≠ 0 := fun h0 ↦ by
    rw [h0] at hdet
    norm_num at hdet
  have hp : p * (a * d - b * c) = 0 := by linear_combination (-d) * e0 + c * e1
  have hq : q * (a * d - b * c) = 0 := by linear_combination (-b) * e0 + a * e1
  exact ⟨(mul_eq_zero.mp hp).resolve_right hdet0, (mul_eq_zero.mp hq).resolve_right hdet0⟩

/-- The same for the sphere: if a two-by-two table carries one positive length measure of the
sphere to another, a step that is at right angles to both of its columns is zero. -/
theorem sphere_part_zero {S s' Sx s a b c d p q : ℝ} (hS : 0 < S) (hs' : 0 < s')
    (hSx : 0 < Sx) (hs : 0 < s) (e22 : S * a * a + S * s' * c * c = Sx)
    (e23 : S * a * b + S * s' * c * d = 0) (e33 : S * b * b + S * s' * d * d = Sx * s)
    (e0 : S * p * a + S * s' * q * c = 0) (e1 : S * p * b + S * s' * q * d = 0) :
    p = 0 ∧ q = 0 := by
  have hdet : S ^ 2 * s' * (a * d - b * c) ^ 2 = Sx ^ 2 * s := by
    linear_combination (S * b * b + S * s' * d * d) * e22 + Sx * e33
      - (S * a * b + S * s' * c * d) * e23
  have hdet0 : a * d - b * c ≠ 0 := fun h0 ↦ by
    have h1 : Sx ^ 2 * s = 0 := by
      rw [← hdet, h0]
      ring
    exact (mul_pos (pow_pos hSx 2) hs).ne' h1
  have hp : S * p * (a * d - b * c) = 0 := by linear_combination d * e0 - c * e1
  have hq : S * s' * q * (a * d - b * c) = 0 := by linear_combination a * e1 - b * e0
  have hp' : S * p = 0 := (mul_eq_zero.mp hp).resolve_right hdet0
  have hq' : S * s' * q = 0 := (mul_eq_zero.mp hq).resolve_right hdet0
  exact ⟨(mul_eq_zero.mp hp').resolve_left hS.ne',
    (mul_eq_zero.mp hq').resolve_left (mul_pos hS hs').ne'⟩

/-- **Steps along the sphere have no `(T, X)` part,** as algebra. `J` are the slopes of the map,
`G` the table at the point; `hM` says the map keeps the table, `hH` that it keeps a second
table that is `c1` times the first on the `(T, X)` plane and `c2` times it on the sphere, with
`c1 ≠ c2`. -/
theorem tx_rows_zero {A S s' c1 c2 : ℝ} {J G : Fin 4 → Fin 4 → ℝ} {c : Fin 4 → ℝ}
    (hA : A ≠ 0) (hc : c1 ≠ c2)
    (hM : ∀ i j, -A * J 0 i * J 0 j + A * J 1 i * J 1 j + S * J 2 i * J 2 j
      + S * s' * J 3 i * J 3 j = G i j)
    (hH : ∀ i j, c i * G i j = c1 * (-A * J 0 i * J 0 j + A * J 1 i * J 1 j)
      + c2 * (S * J 2 i * J 2 j + S * s' * J 3 i * J 3 j))
    (hG00 : G 0 0 = -A) (hG01 : G 0 1 = 0) (hG11 : G 1 1 = A) (hc0 : c 0 = c1)
    (hc1 : c 1 = c1) (i : Fin 4) (hci : c i = c2) : J 0 i = 0 ∧ J 1 i = 0 := by
  have hP : ∀ i j, (c1 - c2) * A * (-(J 0 i * J 0 j) + J 1 i * J 1 j) = (c i - c2) * G i j :=
    fun i j ↦ by linear_combination (-c2) * hM i j - hH i j
  have hk : (c1 - c2) * A ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hc) hA
  have h00 : -(J 0 0 * J 0 0) + J 1 0 * J 1 0 = -1 := by
    have e := hP 0 0
    rw [hc0, hG00] at e
    refine mul_left_cancel₀ hk ?_
    linear_combination e
  have h01 : -(J 0 0 * J 0 1) + J 1 0 * J 1 1 = 0 := by
    have e := hP 0 1
    rw [hc0, hG01] at e
    refine mul_left_cancel₀ hk ?_
    linear_combination e
  have h11 : -(J 0 1 * J 0 1) + J 1 1 * J 1 1 = 1 := by
    have e := hP 1 1
    rw [hc1, hG11] at e
    refine mul_left_cancel₀ hk ?_
    linear_combination e
  have e0 : -(J 0 i * J 0 0) + J 1 i * J 1 0 = 0 := by
    have e := hP i 0
    rw [hci] at e
    refine mul_left_cancel₀ hk ?_
    linear_combination e
  have e1 : -(J 0 i * J 0 1) + J 1 i * J 1 1 = 0 := by
    have e := hP i 1
    rw [hci] at e
    refine mul_left_cancel₀ hk ?_
    linear_combination e
  exact tx_part_zero h00 h01 h11 e0 e1

/-- **Steps in the `(T, X)` plane have no part along the sphere,** as algebra: `hM` says the
map keeps the table, and steps along the sphere are known to have no `(T, X)` part. -/
theorem sphere_rows_zero {A S s' Sx s : ℝ} {J G : Fin 4 → Fin 4 → ℝ} (hS : 0 < S)
    (hs' : 0 < s') (hSx : 0 < Sx) (hs : 0 < s)
    (hM : ∀ i j, -A * J 0 i * J 0 j + A * J 1 i * J 1 j + S * J 2 i * J 2 j
      + S * s' * J 3 i * J 3 j = G i j)
    (h02 : J 0 2 = 0) (h12 : J 1 2 = 0) (h03 : J 0 3 = 0) (h13 : J 1 3 = 0)
    (hG22 : G 2 2 = Sx) (hG23 : G 2 3 = 0) (hG33 : G 3 3 = Sx * s) (i : Fin 4)
    (hGi2 : G i 2 = 0) (hGi3 : G i 3 = 0) : J 2 i = 0 ∧ J 3 i = 0 := by
  have e22 : S * J 2 2 * J 2 2 + S * s' * J 3 2 * J 3 2 = Sx := by
    have e := hM 2 2
    rw [h02, h12, hG22] at e
    linear_combination e
  have e23 : S * J 2 2 * J 2 3 + S * s' * J 3 2 * J 3 3 = 0 := by
    have e := hM 2 3
    rw [h02, h12, hG23] at e
    linear_combination e
  have e33 : S * J 2 3 * J 2 3 + S * s' * J 3 3 * J 3 3 = Sx * s := by
    have e := hM 3 3
    rw [h03, h13, hG33] at e
    linear_combination e
  have e0 : S * J 2 i * J 2 2 + S * s' * J 3 i * J 3 2 = 0 := by
    have e := hM i 2
    rw [h02, h12, hGi2] at e
    linear_combination e
  have e1 : S * J 2 i * J 2 3 + S * s' * J 3 i * J 3 3 = 0 := by
    have e := hM i 3
    rw [h03, h13, hGi3] at e
    linear_combination e
  exact sphere_part_zero hS hs' hSx hs e22 e23 e33 e0 e1

/-! ## Kruskal's table, entry by entry -/

/-- The entry of Kruskal's table for `T`. -/
theorem kruskalG_zero_zero (m : ℝ) (y : Coords 4) :
    kruskalG m 0 0 y = -kruskalA m (y 0) (y 1) := by
  simp [kruskalG, genG, sep2, gTR, gΘ, negA, constOne]

/-- The entry of Kruskal's table for `X`. -/
theorem kruskalG_one_one (m : ℝ) (y : Coords 4) :
    kruskalG m 1 1 y = kruskalA m (y 0) (y 1) := by
  simp [kruskalG, genG, sep2, gTR, gΘ, constOne]

/-- The entry of Kruskal's table for the pole angle. -/
theorem kruskalG_two_two (m : ℝ) (y : Coords 4) :
    kruskalG m 2 2 y = kruskalS m (y 0) (y 1) := by
  simp [kruskalG, genG, sep2, gTR, gΘ, constOne]

/-- The entry of Kruskal's table for the angle around the axis. -/
theorem kruskalG_three_three (m : ℝ) (y : Coords 4) :
    kruskalG m 3 3 y = kruskalS m (y 0) (y 1) * sin (y 2) ^ 2 := by
  simp [kruskalG, genG, sep2, gTR, gΘ, sin2]

/-- Kruskal's table has no entries off the diagonal. -/
theorem kruskalG_of_ne (m : ℝ) (y : Coords 4) {a b : Fin 4} (hab : a ≠ b) :
    kruskalG m a b y = 0 := by
  fin_cases a <;> fin_cases b <;> simp [kruskalG, genG, sep2, gTR, gΘ, zero2] at hab ⊢

/-- The radius of Kruskal's table is a smooth function of the point. -/
theorem contDiffAt_kruskalR_point (hm : 0 < m) {y : Coords 4} (hy : -1 < y 1 ^ 2 - y 0 ^ 2) :
    ContDiffAt ℝ ∞ (fun z : Coords 4 ↦ kruskalR m (z 1 ^ 2 - z 0 ^ 2)) y := by
  have hpoly : ContDiff ℝ ∞ (fun z : Coords 4 ↦ z 1 ^ 2 - z 0 ^ 2) :=
    ((contDiff_apply ℝ (fun _ : Fin 4 ↦ ℝ) 1).pow 2).sub
      ((contDiff_apply ℝ (fun _ : Fin 4 ↦ ℝ) 0).pow 2)
  exact ContDiffAt.comp (g := kruskalR m) y (contDiffAt_kruskalR hm hy) hpoly.contDiffAt

/-! ## What the proofs take from the known values of Kruskal's table -/

/-- **The value of the curvature scalar of Kruskal's table:** `c / r⁶`. -/
def KruskalCurvatureValue (m c : ℝ) : Prop :=
  ∀ y ∈ kruskalRegion,
    kretschmann (kruskalG m) (genGinv (kruskalA m) (kruskalA m) zero2 (kruskalS m)) y
      = c / kruskalR m (y 1 ^ 2 - y 0 ^ 2) ^ 6

/-- **The value of the second slope of the radius of Kruskal's table:** `m / r²` times the
table on the `(T, X)` plane, `(r - 2m) / r²` times the table on the sphere. -/
def KruskalHessValue (m : ℝ) : Prop :=
  ∀ y ∈ kruskalRegion, ∀ a b : Fin 4,
    hessT (kruskalG m) (genGinv (kruskalA m) (kruskalA m) zero2 (kruskalS m))
        (fun z ↦ kruskalR m (z 1 ^ 2 - z 0 ^ 2)) a b y
      = (if a.val < 2 then m / kruskalR m (y 1 ^ 2 - y 0 ^ 2) ^ 2
          else (kruskalR m (y 1 ^ 2 - y 0 ^ 2) - 2 * m) / kruskalR m (y 1 ^ 2 - y 0 ^ 2) ^ 2)
        * kruskalG m a b y

/-! ## What a map that keeps the table does to the entries -/

/-- Two functions that agree near `x` have the same second slope at `x`. -/
theorem hessT_congr {n : ℕ} {g ginv : Fin n → Fin n → Coords n → ℝ} {F F' : Coords n → ℝ}
    {x : Coords n} (hFF : F' =ᶠ[𝓝 x] F) (a b : Fin n) :
    hessT g ginv F' a b x = hessT g ginv F a b x := by
  have hs : slope b F' =ᶠ[𝓝 x] slope b F :=
    hFF.eventually_nhds.mono fun y hy ↦ slope_congr hy b
  unfold hessT
  rw [slope_congr hs a]
  congr 1
  exact Finset.sum_congr rfl fun c _ ↦ by rw [slope_congr hFF c]

/-- **The map keeps the table, entry by entry:** Kruskal's table at `f x`, both slots multiplied
by the slopes of `f`, is Kruskal's table at `x`. -/
theorem carries_kruskal_entry (hf : CarriesTableAt (kruskalG m) (kruskalG m) f x)
    (i j : Fin 4) :
    -kruskalA m (f x 0) (f x 1) * jac f 0 i x * jac f 0 j x
        + kruskalA m (f x 0) (f x 1) * jac f 1 i x * jac f 1 j x
        + kruskalS m (f x 0) (f x 1) * jac f 2 i x * jac f 2 j x
        + kruskalS m (f x 0) (f x 1) * sin (f x 2) ^ 2 * jac f 3 i x * jac f 3 j x
      = kruskalG m i j x := by
  have hd : DifferentiableAt ℝ f x := hf.1.differentiableAt (by simp)
  have h1 := hf.2.self_of_nhds (Pi.single i 1) (Pi.single j 1)
  have h2 : tableMeasure (kruskalG m) x (Pi.single i 1) (Pi.single j 1) = kruskalG m i j x :=
    formOf_single_single _ i j
  rw [← h2, ← h1, kruskal_measure_apply]
  simp only [jac_eq_fderiv hd]

/-- **The map keeps the second slope of the radius, entry by entry,** if it keeps the radius
near `x`. -/
theorem carries_kruskal_hess (hm : 0 < m) (hH : KruskalHessValue m) (hx : x ∈ kruskalRegion)
    (hfx : f x ∈ kruskalRegion) (hf : CarriesTableAt (kruskalG m) (kruskalG m) f x)
    (hρ : (fun y ↦ kruskalR m (f y 1 ^ 2 - f y 0 ^ 2))
      =ᶠ[𝓝 x] fun y ↦ kruskalR m (y 1 ^ 2 - y 0 ^ 2)) (i j : Fin 4) :
    (if i.val < 2 then m / kruskalR m (x 1 ^ 2 - x 0 ^ 2) ^ 2
        else (kruskalR m (x 1 ^ 2 - x 0 ^ 2) - 2 * m) / kruskalR m (x 1 ^ 2 - x 0 ^ 2) ^ 2)
        * kruskalG m i j x
      = m / kruskalR m (f x 1 ^ 2 - f x 0 ^ 2) ^ 2
          * (-kruskalA m (f x 0) (f x 1) * jac f 0 i x * jac f 0 j x
            + kruskalA m (f x 0) (f x 1) * jac f 1 i x * jac f 1 j x)
        + (kruskalR m (f x 1 ^ 2 - f x 0 ^ 2) - 2 * m) / kruskalR m (f x 1 ^ 2 - f x 0 ^ 2) ^ 2
          * (kruskalS m (f x 0) (f x 1) * jac f 2 i x * jac f 2 j x
            + kruskalS m (f x 0) (f x 1) * sin (f x 2) ^ 2 * jac f 3 i x * jac f 3 j x) := by
  have h1 : hessT (kruskalG m) (genGinv (kruskalA m) (kruskalA m) zero2 (kruskalS m))
      (fun y ↦ kruskalR m (f y 1 ^ 2 - f y 0 ^ 2)) i j x
      = ∑ a, ∑ b, jac f a i x * jac f b j x
        * hessT (kruskalG m) (genGinv (kruskalA m) (kruskalA m) zero2 (kruskalS m))
          (fun z ↦ kruskalR m (z 1 ^ 2 - z 0 ^ 2)) a b (f x) :=
    hessT_of_carries (kruskal_regular hm) (kruskal_regular hm) hx hfx hf
      (contDiffAt_kruskalR_point hm hfx.1) i j
  rw [hessT_congr hρ i j, hH x hx i j] at h1
  have e : ∀ a, ∑ b, jac f a i x * jac f b j x
      * hessT (kruskalG m) (genGinv (kruskalA m) (kruskalA m) zero2 (kruskalS m))
        (fun z ↦ kruskalR m (z 1 ^ 2 - z 0 ^ 2)) a b (f x)
      = jac f a i x * jac f a j x
        * ((if a.val < 2 then m / kruskalR m (f x 1 ^ 2 - f x 0 ^ 2) ^ 2
            else (kruskalR m (f x 1 ^ 2 - f x 0 ^ 2) - 2 * m)
              / kruskalR m (f x 1 ^ 2 - f x 0 ^ 2) ^ 2) * kruskalG m a a (f x)) := fun a ↦ by
    rw [Finset.sum_eq_single a]
    · rw [hH (f x) hfx a a]
    · intro b _ hb
      rw [hH (f x) hfx a b, kruskalG_of_ne m (f x) (Ne.symm hb)]
      ring
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  rw [h1, Finset.sum_congr rfl fun a _ ↦ e a, Fin.sum_univ_four, kruskalG_zero_zero,
    kruskalG_one_one, kruskalG_two_two, kruskalG_three_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.ofNat_pos, Nat.one_lt_ofNat,
    lt_self_iff_false, ite_true, ite_false]
  have h3 : ¬ ((3 : Fin 4).val < 2) := by decide
  rw [ite_eq_right h3]
  ring

/-! ## The radius -/

/-- **The radius is kept,** given the value of the curvature scalar of Kruskal's table. -/
theorem KeepsKruskalOn.radius_of_value (hm : 0 < m) {c : ℝ} (hc : c ≠ 0)
    (hK : KruskalCurvatureValue m c) (h : KeepsKruskalOn m f W) (hx : x ∈ W) :
    f x 1 ^ 2 - f x 0 ^ 2 = x 1 ^ 2 - x 0 ^ 2 := by
  have hxr : x ∈ kruskalRegion := h.2.1 hx
  have hfr : f x ∈ kruskalRegion := h.2.2.1 x hx
  have hr : 0 < kruskalR m (x 1 ^ 2 - x 0 ^ 2) := kruskalR_pos hm hxr.1
  have hr' : 0 < kruskalR m (f x 1 ^ 2 - f x 0 ^ 2) := kruskalR_pos hm hfr.1
  have heq := kretschmann_eq_of_carries (kruskal_regular hm) (kruskal_regular hm) hxr hfr
    (h.2.2.2 x hx)
  rw [hK x hxr, hK (f x) hfr] at heq
  have h6 : kruskalR m (x 1 ^ 2 - x 0 ^ 2) ^ 6 = kruskalR m (f x 1 ^ 2 - f x 0 ^ 2) ^ 6 :=
    mul_left_cancel₀ hc ((div_eq_div_iff (pow_pos hr' 6).ne' (pow_pos hr 6).ne').mp heq)
  have hrr : kruskalR m (x 1 ^ 2 - x 0 ^ 2) = kruskalR m (f x 1 ^ 2 - f x 0 ^ 2) :=
    (pow_left_inj₀ hr.le hr'.le (by norm_num)).mp h6
  calc f x 1 ^ 2 - f x 0 ^ 2 = kruskalF m (kruskalR m (f x 1 ^ 2 - f x 0 ^ 2)) :=
        (kruskalF_kruskalR hm hfr.1).symm
    _ = kruskalF m (kruskalR m (x 1 ^ 2 - x 0 ^ 2)) := by rw [hrr]
    _ = x 1 ^ 2 - x 0 ^ 2 := kruskalF_kruskalR hm hxr.1

/-! ## The split -/

/-- Near no point is `X² - T²` constant: every neighbourhood of every point has points with
another value. -/
theorem not_eventually_light_eq (x : Coords 4) (c : ℝ) :
    ¬ ∀ᶠ y in 𝓝 x, y 1 ^ 2 - y 0 ^ 2 = c := by
  intro hev
  have hγ : Continuous fun t : ℝ ↦ Function.update x 1 (x 1 + t) :=
    continuous_const.update 1 (continuous_const.add continuous_id)
  have h0 : Function.update x 1 (x 1 + 0) = x := by rw [add_zero, Function.update_eq_self]
  have h1 : Filter.Tendsto (fun t : ℝ ↦ Function.update x 1 (x 1 + t)) (𝓝 0) (𝓝 x) := by
    have h2 := hγ.tendsto 0
    rwa [h0] at h2
  have hev' : ∀ᶠ t in 𝓝 (0 : ℝ), (x 1 + t) ^ 2 - x 0 ^ 2 = c := by
    filter_upwards [h1.eventually hev] with t ht
    have ht' : Function.update x 1 (x 1 + t) 1 ^ 2 - Function.update x 1 (x 1 + t) 0 ^ 2 = c :=
      ht
    rw [Function.update_self, Function.update_of_ne (by decide : (0 : Fin 4) ≠ 1)] at ht'
    exact ht'
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev'
  have e0 : (x 1 + 0) ^ 2 - x 0 ^ 2 = c := hball (by rw [dist_self]; exact hε)
  have e1 : (x 1 + ε / 2) ^ 2 - x 0 ^ 2 = c :=
    hball (by rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]; exact half_lt_self hε)
  have e2 : (x 1 + -(ε / 2)) ^ 2 - x 0 ^ 2 = c :=
    hball (by rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (half_pos hε)]
              exact half_lt_self hε)
  have h3 : ε ^ 2 = 0 := by linear_combination 2 * e1 + 2 * e2 - 4 * e0
  exact (pow_pos hε 2).ne' h3

/-- **Where `r ≠ 3m`, steps along the sphere go to steps along the sphere,** if the map keeps
the radius on `W`. -/
theorem KeepsKruskalOn.tx_zero_off (hm : 0 < m) (hH : KruskalHessValue m)
    (h : KeepsKruskalOn m f W)
    (hRad : ∀ y ∈ W, f y 1 ^ 2 - f y 0 ^ 2 = y 1 ^ 2 - y 0 ^ 2) (hx : x ∈ W)
    (h3 : kruskalR m (x 1 ^ 2 - x 0 ^ 2) ≠ 3 * m) (i : Fin 4) (hi : 2 ≤ i.val) :
    jac f 0 i x = 0 ∧ jac f 1 i x = 0 := by
  have hxr : x ∈ kruskalRegion := h.2.1 hx
  have hfr : f x ∈ kruskalRegion := h.2.2.1 x hx
  have hf := h.2.2.2 x hx
  have hu := hRad x hx
  have hρ : (fun y ↦ kruskalR m (f y 1 ^ 2 - f y 0 ^ 2))
      =ᶠ[𝓝 x] fun y ↦ kruskalR m (y 1 ^ 2 - y 0 ^ 2) := by
    filter_upwards [h.1.mem_nhds hx] with y hy
    rw [hRad y hy]
  have hr : 0 < kruskalR m (x 1 ^ 2 - x 0 ^ 2) := kruskalR_pos hm hxr.1
  have hA : 0 < kruskalA m (x 0) (x 1) := kruskalA_pos hm hxr.1
  have hA' : kruskalA m (f x 0) (f x 1) = kruskalA m (x 0) (x 1) := by
    unfold kruskalA
    rw [hu]
  have hS' : kruskalS m (f x 0) (f x 1) = kruskalS m (x 0) (x 1) := by
    unfold kruskalS
    rw [hu]
  have hM : ∀ i j : Fin 4, -kruskalA m (x 0) (x 1) * jac f 0 i x * jac f 0 j x
      + kruskalA m (x 0) (x 1) * jac f 1 i x * jac f 1 j x
      + kruskalS m (x 0) (x 1) * jac f 2 i x * jac f 2 j x
      + kruskalS m (x 0) (x 1) * sin (f x 2) ^ 2 * jac f 3 i x * jac f 3 j x
      = kruskalG m i j x := fun i j ↦ by
    have e := carries_kruskal_entry hf i j
    rw [hA', hS'] at e
    exact e
  have hHe : ∀ i j : Fin 4,
      (if i.val < 2 then m / kruskalR m (x 1 ^ 2 - x 0 ^ 2) ^ 2
        else (kruskalR m (x 1 ^ 2 - x 0 ^ 2) - 2 * m) / kruskalR m (x 1 ^ 2 - x 0 ^ 2) ^ 2)
        * kruskalG m i j x
      = m / kruskalR m (x 1 ^ 2 - x 0 ^ 2) ^ 2
          * (-kruskalA m (x 0) (x 1) * jac f 0 i x * jac f 0 j x
            + kruskalA m (x 0) (x 1) * jac f 1 i x * jac f 1 j x)
        + (kruskalR m (x 1 ^ 2 - x 0 ^ 2) - 2 * m) / kruskalR m (x 1 ^ 2 - x 0 ^ 2) ^ 2
          * (kruskalS m (x 0) (x 1) * jac f 2 i x * jac f 2 j x
            + kruskalS m (x 0) (x 1) * sin (f x 2) ^ 2 * jac f 3 i x * jac f 3 j x) :=
    fun i j ↦ by
      have e := carries_kruskal_hess hm hH hxr hfr hf hρ i j
      rw [hu, hA', hS'] at e
      exact e
  have hcc : m / kruskalR m (x 1 ^ 2 - x 0 ^ 2) ^ 2
      ≠ (kruskalR m (x 1 ^ 2 - x 0 ^ 2) - 2 * m) / kruskalR m (x 1 ^ 2 - x 0 ^ 2) ^ 2 :=
    fun hcc ↦ h3 (by
      have e := (div_left_inj₀ (pow_pos hr 2).ne').mp hcc
      linarith)
  exact tx_rows_zero (J := fun a i ↦ jac f a i x) (G := fun i j ↦ kruskalG m i j x)
    (c := fun i ↦ if i.val < 2 then m / kruskalR m (x 1 ^ 2 - x 0 ^ 2) ^ 2
      else (kruskalR m (x 1 ^ 2 - x 0 ^ 2) - 2 * m) / kruskalR m (x 1 ^ 2 - x 0 ^ 2) ^ 2)
    hA.ne' hcc hM hHe (kruskalG_zero_zero m x) (kruskalG_of_ne m x (by decide))
    (kruskalG_one_one m x) (ite_eq_left (by decide)) (ite_eq_left (by decide)) i
    (ite_eq_right (not_lt.mpr hi))

/-- **Steps along the sphere go to steps along the sphere,** at every point, if the map keeps
the radius on `W`: the points with `r ≠ 3m` come near every point, and the slopes of the map
are continuous. -/
theorem KeepsKruskalOn.tx_zero (hm : 0 < m) (hH : KruskalHessValue m)
    (h : KeepsKruskalOn m f W)
    (hRad : ∀ y ∈ W, f y 1 ^ 2 - f y 0 ^ 2 = y 1 ^ 2 - y 0 ^ 2) (hx : x ∈ W)
    (a i : Fin 4) (ha : a.val < 2) (hi : 2 ≤ i.val) : jac f a i x = 0 := by
  by_contra hne
  have hcont : ContinuousAt (jac f a i) x :=
    (Join.contDiffAt_jac_top (h.2.2.2 x hx).1 a i).continuousAt
  have hev : ∀ᶠ y in 𝓝 x, jac f a i y ≠ 0 ∧ y ∈ W :=
    (hcont.eventually_ne hne).and (h.1.mem_nhds hx)
  refine not_eventually_light_eq x (kruskalF m (3 * m)) ?_
  filter_upwards [hev] with y hy
  by_contra hu
  have h3 : kruskalR m (y 1 ^ 2 - y 0 ^ 2) ≠ 3 * m := fun h3 ↦ hu (by
    rw [← h3]
    exact (kruskalF_kruskalR hm (h.2.1 hy.2).1).symm)
  have hz := h.tx_zero_off hm hH hRad hy.2 h3 i hi
  obtain rfl | rfl := (by decide : ∀ a : Fin 4, a.val < 2 → a = 0 ∨ a = 1) a ha
  · exact hy.1 hz.1
  · exact hy.1 hz.2

/-- **Steps in the `(T, X)` plane go to steps in the `(T, X)` plane,** if the map keeps the
radius on `W`. -/
theorem KeepsKruskalOn.sphere_zero (hm : 0 < m) (hH : KruskalHessValue m)
    (h : KeepsKruskalOn m f W)
    (hRad : ∀ y ∈ W, f y 1 ^ 2 - f y 0 ^ 2 = y 1 ^ 2 - y 0 ^ 2) (hx : x ∈ W)
    (a i : Fin 4) (ha : 2 ≤ a.val) (hi : i.val < 2) : jac f a i x = 0 := by
  have hxr : x ∈ kruskalRegion := h.2.1 hx
  have hfr : f x ∈ kruskalRegion := h.2.2.1 x hx
  have hf := h.2.2.2 x hx
  have hu := hRad x hx
  have hS : 0 < kruskalS m (x 0) (x 1) := kruskalS_pos hm hxr.1
  have hs : 0 < sin (x 2) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hxr.2).symm
  have hs' : 0 < sin (f x 2) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hfr.2).symm
  have hA' : kruskalA m (f x 0) (f x 1) = kruskalA m (x 0) (x 1) := by
    unfold kruskalA
    rw [hu]
  have hS' : kruskalS m (f x 0) (f x 1) = kruskalS m (x 0) (x 1) := by
    unfold kruskalS
    rw [hu]
  have hM : ∀ i j : Fin 4, -kruskalA m (x 0) (x 1) * jac f 0 i x * jac f 0 j x
      + kruskalA m (x 0) (x 1) * jac f 1 i x * jac f 1 j x
      + kruskalS m (x 0) (x 1) * jac f 2 i x * jac f 2 j x
      + kruskalS m (x 0) (x 1) * sin (f x 2) ^ 2 * jac f 3 i x * jac f 3 j x
      = kruskalG m i j x := fun i j ↦ by
    have e := carries_kruskal_entry hf i j
    rw [hA', hS'] at e
    exact e
  have hz : ∀ b j : Fin 4, b.val < 2 → 2 ≤ j.val → jac f b j x = 0 := fun b j hb hj ↦
    h.tx_zero hm hH hRad hx b j hb hj
  have hGi : ∀ j : Fin 4, 2 ≤ j.val → kruskalG m i j x = 0 := fun j hj ↦
    kruskalG_of_ne m x fun hij ↦ by
      rw [hij] at hi
      omega
  have key := sphere_rows_zero (A := kruskalA m (x 0) (x 1)) (J := fun a i ↦ jac f a i x)
    (G := fun i j ↦ kruskalG m i j x) hS hs' hS hs hM (hz 0 2 (by decide) (by decide))
    (hz 1 2 (by decide) (by decide)) (hz 0 3 (by decide) (by decide))
    (hz 1 3 (by decide) (by decide)) (kruskalG_two_two m x) (kruskalG_of_ne m x (by decide))
    (kruskalG_three_three m x) i (hGi 2 (by decide)) (hGi 3 (by decide))
  obtain rfl | rfl := (by decide : ∀ a : Fin 4, 2 ≤ a.val → a = 2 ∨ a = 3) a ha
  · exact key.1
  · exact key.2

/-- **The split is kept,** given the two known values of Kruskal's table. -/
theorem KeepsKruskalOn.split_of_value (hm : 0 < m) {c : ℝ} (hc : c ≠ 0)
    (hK : KruskalCurvatureValue m c) (hH : KruskalHessValue m) (h : KeepsKruskalOn m f W)
    (hx : x ∈ W) (a i : Fin 4)
    (hai : (a.val < 2 ∧ 2 ≤ i.val) ∨ (2 ≤ a.val ∧ i.val < 2)) : jac f a i x = 0 := by
  have hRad : ∀ y ∈ W, f y 1 ^ 2 - f y 0 ^ 2 = y 1 ^ 2 - y 0 ^ 2 := fun y hy ↦
    h.radius_of_value hm hc hK hy
  rcases hai with ⟨ha, hi⟩ | ⟨ha, hi⟩
  · exact h.tx_zero hm hH hRad hx a i ha hi
  · exact h.sphere_zero hm hH hRad hx a i ha hi

/-- **The radius is kept:** a map that keeps Kruskal's table keeps `X² - T²`. -/
theorem KeepsKruskalOn.radius (hm : 0 < m) (h : KeepsKruskalOn m f W) (hx : x ∈ W) :
    f x 1 ^ 2 - f x 0 ^ 2 = x 1 ^ 2 - x 0 ^ 2 := by
  sorry

/-- **The split is kept:** a map that keeps Kruskal's table carries steps in the `(T, X)` plane
to steps in the `(T, X)` plane, and steps along the sphere to steps along the sphere. -/
theorem KeepsKruskalOn.split (hm : 0 < m) (h : KeepsKruskalOn m f W) (hx : x ∈ W)
    (a i : Fin 4) (hai : (a.val < 2 ∧ 2 ≤ i.val) ∨ (2 ≤ a.val ∧ i.val < 2)) :
    jac f a i x = 0 := by
  sorry

end GravityInLean.Curved
