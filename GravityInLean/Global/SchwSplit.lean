/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.KruskalKept
public import GravityInLean.Global.SchwScalars

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# A map that keeps Schwarzschild's table of negative mass keeps the split

The twin of `KeepsKruskalOn.split` for Schwarzschild's table of distance and angles with a
negative mass. Take a map `f` of coordinate space that keeps Schwarzschild's table on an open
set outside the rim, and that keeps the distance label there. Then `f` carries steps in the
`(t, r)` plane to steps in the `(t, r)` plane, and steps along the sphere to steps along the
sphere (`schw_split_of_kept`).

How it is shown: `f` keeps the distance label, so it keeps its second slope
(`hessT_of_carries`). For Schwarzschild's table that second slope is `m / r²` times the table on
the `(t, r)` plane and `(r - 2m) / r²` times the table on the sphere (`hessT_schwRad`). For a
negative mass these two numbers differ at every point (`3m - r` is never zero), so no limit is
needed. The algebra is that of `KruskalKept.lean`, with two different entries on the `(t, r)`
plane.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

/-! ## Algebra of the two blocks, with two different entries on the plane -/

/-- If a two-by-two table keeps `-A t² + B r²`, a step that is at right angles (in that sense)
to both of its columns is zero. -/
theorem tx_part_zero_w {A B a b c d p q : ℝ} (hA : A ≠ 0) (hB : B ≠ 0)
    (h00 : -A * (a * a) + B * (c * c) = -A) (h01 : -A * (a * b) + B * (c * d) = 0)
    (h11 : -A * (b * b) + B * (d * d) = B) (e0 : -A * (p * a) + B * (q * c) = 0)
    (e1 : -A * (p * b) + B * (q * d) = 0) : p = 0 ∧ q = 0 := by
  have hdet : A * B * (a * d - b * c) ^ 2 = A * B := by
    linear_combination (-A * (a * b) + B * (c * d)) * h01
      - (-A * (b * b) + B * (d * d)) * h00 + A * h11
  have hdet0 : a * d - b * c ≠ 0 := fun h0 ↦ by
    have h1 : A * B = 0 := by
      rw [← hdet, h0]
      ring
    exact mul_ne_zero hA hB h1
  have hp : A * p * (a * d - b * c) = 0 := by linear_combination (-d) * e0 + c * e1
  have hq : B * q * (a * d - b * c) = 0 := by linear_combination (-b) * e0 + a * e1
  have hp' : A * p = 0 := (mul_eq_zero.mp hp).resolve_right hdet0
  have hq' : B * q = 0 := (mul_eq_zero.mp hq).resolve_right hdet0
  exact ⟨(mul_eq_zero.mp hp').resolve_left hA, (mul_eq_zero.mp hq').resolve_left hB⟩

/-- **Steps along the sphere have no `(t, r)` part,** as algebra. `J` are the slopes of the map,
`G` the table at the point; `hM` says the map keeps the table, `hH` that it keeps a second
table that is `c1` times the first on the `(t, r)` plane and `c2` times it on the sphere, with
`c1 ≠ c2`. -/
theorem tx_rows_zero_w {A B S s' c1 c2 : ℝ} {J G : Fin 4 → Fin 4 → ℝ} {c : Fin 4 → ℝ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hc : c1 ≠ c2)
    (hM : ∀ i j, -A * (J 0 i * J 0 j) + B * (J 1 i * J 1 j) + S * (J 2 i * J 2 j)
      + S * s' * (J 3 i * J 3 j) = G i j)
    (hH : ∀ i j, c i * G i j = c1 * (-A * (J 0 i * J 0 j) + B * (J 1 i * J 1 j))
      + c2 * (S * (J 2 i * J 2 j) + S * s' * (J 3 i * J 3 j)))
    (hG00 : G 0 0 = -A) (hG01 : G 0 1 = 0) (hG11 : G 1 1 = B) (hc0 : c 0 = c1)
    (hc1 : c 1 = c1) (i : Fin 4) (hci : c i = c2) : J 0 i = 0 ∧ J 1 i = 0 := by
  have hP : ∀ i j, (c1 - c2) * (-A * (J 0 i * J 0 j) + B * (J 1 i * J 1 j))
      = (c i - c2) * G i j :=
    fun i j ↦ by linear_combination (-c2) * hM i j - hH i j
  have hk : c1 - c2 ≠ 0 := sub_ne_zero.mpr hc
  have h00 : -A * (J 0 0 * J 0 0) + B * (J 1 0 * J 1 0) = -A := by
    have e := hP 0 0
    rw [hc0, hG00] at e
    exact mul_left_cancel₀ hk e
  have h01 : -A * (J 0 0 * J 0 1) + B * (J 1 0 * J 1 1) = 0 := by
    have e := hP 0 1
    rw [hc0, hG01] at e
    exact mul_left_cancel₀ hk e
  have h11 : -A * (J 0 1 * J 0 1) + B * (J 1 1 * J 1 1) = B := by
    have e := hP 1 1
    rw [hc1, hG11] at e
    exact mul_left_cancel₀ hk e
  have e0 : -A * (J 0 i * J 0 0) + B * (J 1 i * J 1 0) = 0 := by
    have e := hP i 0
    rw [hci, sub_self, zero_mul] at e
    exact (mul_eq_zero.mp e).resolve_left hk
  have e1 : -A * (J 0 i * J 0 1) + B * (J 1 i * J 1 1) = 0 := by
    have e := hP i 1
    rw [hci, sub_self, zero_mul] at e
    exact (mul_eq_zero.mp e).resolve_left hk
  exact tx_part_zero_w hA hB h00 h01 h11 e0 e1

/-- **Steps in the `(t, r)` plane have no part along the sphere,** as algebra: `hM` says the
map keeps the table, and steps along the sphere are known to have no `(t, r)` part. -/
theorem sphere_rows_zero_w {A B S s' Sx s : ℝ} {J G : Fin 4 → Fin 4 → ℝ} (hS : 0 < S)
    (hs' : 0 < s') (hSx : 0 < Sx) (hs : 0 < s)
    (hM : ∀ i j, -A * (J 0 i * J 0 j) + B * (J 1 i * J 1 j) + S * (J 2 i * J 2 j)
      + S * s' * (J 3 i * J 3 j) = G i j)
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

/-! ## A round table, entry by entry -/

section Entries

variable (A B : ℝ → ℝ) (y : Coords 4)

/-- The entry of a round table for the time label. -/
theorem roundG_zero_zero : roundG A B 0 0 y = -A (y 1) := by
  simp [roundG, diag, roundDiag, sep, gr, gθ, negF, constOne]

/-- The entry of a round table for the distance label. -/
theorem roundG_one_one : roundG A B 1 1 y = B (y 1) := by
  simp [roundG, diag, roundDiag, sep, gr, gθ, constOne]

/-- The entry of a round table for the pole angle. -/
theorem roundG_two_two : roundG A B 2 2 y = y 1 ^ 2 := by
  simp [roundG, diag, roundDiag, sep, gr, gθ, sqF, constOne]

/-- The entry of a round table for the angle around the axis. -/
theorem roundG_three_three : roundG A B 3 3 y = y 1 ^ 2 * sin (y 2) ^ 2 := by
  simp [roundG, diag, roundDiag, sep, gr, gθ, sqF, sin2]

/-- A round table has no entries off the diagonal. -/
theorem roundG_of_ne {a b : Fin 4} (hab : a ≠ b) : roundG A B a b y = 0 := by
  simp [roundG, diag, hab]

end Entries

/-! ## What a map that keeps Schwarzschild's table does to the entries -/

variable {m : ℝ} {f : Coords 4 → Coords 4} {x : Coords 4}

/-- The second slope of the distance label on Schwarzschild's table, in the form used here:
`m / r²` times the table for the `(t, r)` plane, `(r - 2m) / r²` times the table for the
sphere. -/
theorem hessT_schwRad_diag {y : Coords 4} (hy : y ∈ outside m) (a b : Fin 4) :
    hessT (roundG (schwA m) (schwB m)) (roundGinv (schwA m) (schwB m)) (fun z ↦ z 1) a b y
      = (if a.val < 2 then m / y 1 ^ 2 else (y 1 - 2 * m) / y 1 ^ 2)
        * roundG (schwA m) (schwB m) a b y := by
  have e := hessT_schwRad (BothWays.mem_offRim (Or.inl hy)) a b
  by_cases hab : a = b
  · subst hab
    by_cases ha : a.val < 2
    · rw [ite_eq_left (And.intro ha ha)] at e
      rw [ite_eq_left ha]
      exact e
    · rw [ite_eq_right (fun h : a.val < 2 ∧ a.val < 2 ↦ ha h.1),
        ite_eq_left (And.intro (not_lt.mp ha) (not_lt.mp ha))] at e
      rw [ite_eq_right ha]
      exact e
  · rw [roundG_of_ne _ _ y hab, mul_zero] at e ⊢
    exact e

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
    (if i.val < 2 then m / x 1 ^ 2 else (x 1 - 2 * m) / x 1 ^ 2)
        * roundG (schwA m) (schwB m) i j x
      = m / f x 1 ^ 2
          * (-schwA m (f x 1) * (jac f 0 i x * jac f 0 j x)
            + schwB m (f x 1) * (jac f 1 i x * jac f 1 j x))
        + (f x 1 - 2 * m) / f x 1 ^ 2
          * (f x 1 ^ 2 * (jac f 2 i x * jac f 2 j x)
            + f x 1 ^ 2 * sin (f x 2) ^ 2 * (jac f 3 i x * jac f 3 j x)) := by
  have hF : ContDiffAt ℝ ∞ (fun z : Coords 4 ↦ z 1) (f x) :=
    (contDiff_apply ℝ (fun _ : Fin 4 ↦ ℝ) 1).contDiffAt
  have h1 : hessT (roundG (schwA m) (schwB m)) (roundGinv (schwA m) (schwB m))
      (fun y ↦ f y 1) i j x
      = ∑ a, ∑ b, jac f a i x * jac f b j x
        * hessT (roundG (schwA m) (schwB m)) (roundGinv (schwA m) (schwB m))
          (fun z ↦ z 1) a b (f x) :=
    hessT_of_carries (schwarzschild_regularTable_outside m)
      (schwarzschild_regularTable_outside m) hx hfx hf hF i j
  rw [hessT_congr hρ i j, hessT_schwRad_diag hx i j] at h1
  have e : ∀ a, ∑ b, jac f a i x * jac f b j x
      * hessT (roundG (schwA m) (schwB m)) (roundGinv (schwA m) (schwB m))
        (fun z ↦ z 1) a b (f x)
      = jac f a i x * jac f a j x
        * ((if a.val < 2 then m / f x 1 ^ 2 else (f x 1 - 2 * m) / f x 1 ^ 2)
          * roundG (schwA m) (schwB m) a a (f x)) := fun a ↦ by
    rw [Finset.sum_eq_single a]
    · rw [hessT_schwRad_diag hfx a a]
    · intro b _ hb
      rw [hessT_schwRad_diag hfx a b, roundG_of_ne _ _ (f x) (Ne.symm hb)]
      ring
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  rw [h1, Finset.sum_congr rfl fun a _ ↦ e a, Fin.sum_univ_four, roundG_zero_zero,
    roundG_one_one, roundG_two_two, roundG_three_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.ofNat_pos, Nat.one_lt_ofNat,
    lt_self_iff_false, ite_true, ite_false]
  have h3 : ¬ ((3 : Fin 4).val < 2) := by decide
  rw [ite_eq_right h3]
  ring

/-! ## The split -/

/-- **The split is kept for a negative mass.** A map of coordinate space that keeps
Schwarzschild's table of negative mass on an open set, and keeps the distance label there,
carries steps in the `(t, r)` plane to steps in the `(t, r)` plane, and steps along the sphere
to steps along the sphere. -/
theorem schw_split_of_kept {m : ℝ} (hm : m < 0) {f : Coords 4 → Coords 4}
    {W : Set (Coords 4)} (hW : IsOpen W) (hWsub : W ⊆ outside m)
    (hfW : ∀ x ∈ W, f x ∈ outside m)
    (hf : ∀ x ∈ W, CarriesTableAt (roundG (schwA m) (schwB m)) (roundG (schwA m) (schwB m)) f x)
    (hrad : ∀ x ∈ W, f x 1 = x 1) {x : Coords 4} (hx : x ∈ W) (a i : Fin 4)
    (hai : (a.val < 2 ∧ 2 ≤ i.val) ∨ (2 ≤ a.val ∧ i.val < 2)) : jac f a i x = 0 := by
  have hxo : x ∈ outside m := hWsub hx
  have hfo : f x ∈ outside m := hfW x hx
  have hu : f x 1 = x 1 := hrad x hx
  have hρ : (fun y ↦ f y 1) =ᶠ[𝓝 x] fun y ↦ y 1 := by
    filter_upwards [hW.mem_nhds hx] with y hy
    exact hrad y hy
  have hr : 0 < x 1 := hxo.1
  have hA : schwA m (x 1) ≠ 0 := (schwA_pos_outside hxo.1 hxo.2.1).ne'
  have hB : schwB m (x 1) ≠ 0 := inv_ne_zero hA
  have hS : 0 < x 1 ^ 2 := pow_pos hr 2
  have hs : 0 < sin (x 2) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hxo.2.2).symm
  have hs' : 0 < sin (f x 2) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hfo.2.2).symm
  -- the map keeps the table, and the second slope of the distance label
  have hM : ∀ i j : Fin 4, -schwA m (x 1) * (jac f 0 i x * jac f 0 j x)
      + schwB m (x 1) * (jac f 1 i x * jac f 1 j x) + x 1 ^ 2 * (jac f 2 i x * jac f 2 j x)
      + x 1 ^ 2 * sin (f x 2) ^ 2 * (jac f 3 i x * jac f 3 j x)
      = roundG (schwA m) (schwB m) i j x := fun i j ↦ by
    have e := carries_schw_entry (hf x hx) i j
    rw [hu] at e
    exact e
  have hHe : ∀ i j : Fin 4,
      (if i.val < 2 then m / x 1 ^ 2 else (x 1 - 2 * m) / x 1 ^ 2)
        * roundG (schwA m) (schwB m) i j x
      = m / x 1 ^ 2
          * (-schwA m (x 1) * (jac f 0 i x * jac f 0 j x)
            + schwB m (x 1) * (jac f 1 i x * jac f 1 j x))
        + (x 1 - 2 * m) / x 1 ^ 2
          * (x 1 ^ 2 * (jac f 2 i x * jac f 2 j x)
            + x 1 ^ 2 * sin (f x 2) ^ 2 * (jac f 3 i x * jac f 3 j x)) := fun i j ↦ by
    have e := carries_schw_hess hxo hfo (hf x hx) hρ i j
    rw [hu] at e
    exact e
  -- for a negative mass the two factors differ
  have hcc : m / x 1 ^ 2 ≠ (x 1 - 2 * m) / x 1 ^ 2 := fun hcc ↦ by
    have e := (div_left_inj₀ hS.ne').mp hcc
    linarith
  -- steps along the sphere have no `(t, r)` part
  have htx : ∀ j : Fin 4, 2 ≤ j.val → jac f 0 j x = 0 ∧ jac f 1 j x = 0 := fun j hj ↦
    tx_rows_zero_w (J := fun a i ↦ jac f a i x)
      (G := fun i j ↦ roundG (schwA m) (schwB m) i j x)
      (c := fun i ↦ if i.val < 2 then m / x 1 ^ 2 else (x 1 - 2 * m) / x 1 ^ 2)
      hA hB hcc hM hHe (roundG_zero_zero _ _ x) (roundG_of_ne _ _ x (by decide))
      (roundG_one_one _ _ x) (ite_eq_left (by decide)) (ite_eq_left (by decide)) j
      (ite_eq_right (not_lt.mpr hj))
  rcases hai with ⟨ha, hi⟩ | ⟨ha, hi⟩
  · obtain rfl | rfl := (by decide : ∀ a : Fin 4, a.val < 2 → a = 0 ∨ a = 1) a ha
    · exact (htx i hi).1
    · exact (htx i hi).2
  · have hGi : ∀ j : Fin 4, 2 ≤ j.val → roundG (schwA m) (schwB m) i j x = 0 := fun j hj ↦
      roundG_of_ne _ _ x fun hij ↦ by
        rw [hij] at hi
        omega
    have key := sphere_rows_zero_w (J := fun a i ↦ jac f a i x)
      (G := fun i j ↦ roundG (schwA m) (schwB m) i j x) hS hs' hS hs hM
      (htx 2 (by decide)).1 (htx 2 (by decide)).2 (htx 3 (by decide)).1 (htx 3 (by decide)).2
      (roundG_two_two _ _ x) (roundG_of_ne _ _ x (by decide)) (roundG_three_three _ _ x) i
      (hGi 2 (by decide)) (hGi 3 (by decide))
    obtain rfl | rfl := (by decide : ∀ a : Fin 4, 2 ≤ a.val → a = 2 ∨ a = 3) a ha
    · exact key.1
    · exact key.2

end GravityInLean.Curved
