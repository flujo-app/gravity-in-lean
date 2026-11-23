/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.NewCoordinates
public import GravityInLean.Symmetry

import Mathlib.Tactic

/-!
# "Unchanged by a move" does not depend on the coordinates

`Symmetry.lean` says what it means that moving along a field of arrows leaves a length measure
unchanged (Killing's equation), by a formula in coordinates: `lieD`. This file shows that the
formula does not depend on the coordinates.

A field of arrows `ξ'` in the new coordinates and a field `ξ` in the old ones are the same field
when the table of slopes of the change of coordinates turns one into the other:
`∑ μ, jac Φ α μ y * ξ' μ y = ξ α (Φ y)`.

**What is proved here.**

* `lieD_inNewCoords`: the change of the length measure along the field, computed in the new
  coordinates, is the one computed in the old coordinates, re-written the way a length measure is
  re-written.
* `leavesUnchangedAt_inNewCoords`: so a move leaves the length measure unchanged in the new
  coordinates exactly when it does in the old ones.

**What is assumed.** The change of coordinates is twice smoothly differentiable and loses no
direction; the length measure and the two fields can be differentiated. A worked case is in
`SameSpacetime.lean`.
-/

@[expose] public section

namespace GravityInLean

open Filter Topology Matrix

variable {n : ℕ}

/-! ## The algebra -/

/-- An entry of `Aᵀ · G · B`, written out. -/
theorem sandwich_apply (A G B : Matrix (Fin n) (Fin n) ℝ) (μ ν : Fin n) :
    (Aᵀ * G * B) μ ν = ∑ α, ∑ β, A α μ * B β ν * G α β := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring

/-- `Jᵀ · W · J` vanishes exactly when `W` does, if `J` can be inverted. -/
theorem sandwich_eq_zero_iff {J W : Matrix (Fin n) (Fin n) ℝ} (hJ : J.det ≠ 0) :
    Jᵀ * W * J = 0 ↔ W = 0 := by
  have h1 : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hJ)
  have h2 : (J⁻¹)ᵀ * Jᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  constructor
  · intro h
    have e : W = (J⁻¹)ᵀ * (Jᵀ * W * J) * J⁻¹ := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one, ← Matrix.mul_assoc, h2,
        Matrix.one_mul]
    rw [e, h, Matrix.mul_zero, Matrix.zero_mul]
  · intro h
    rw [h, Matrix.mul_zero, Matrix.zero_mul]

/-- The heart of the matter, for square tables of numbers. `J` is the table of slopes of the
change of coordinates, `G` the length measure, `D` and `E` the slopes of the field in the new and
in the old coordinates, `L` the change of the length measure along the field, and `P` the second
slopes of the change of coordinates along the field. The assumption says that the two fields are
the same field. -/
theorem lie_core {J G D E P L : Matrix (Fin n) (Fin n) ℝ} (hR : P + J * D = E * J) :
    Pᵀ * G * J + Jᵀ * G * P + Jᵀ * L * J + Dᵀ * (Jᵀ * G * J) + Jᵀ * G * J * D
      = Jᵀ * (L + Eᵀ * G + G * E) * J := by
  have hJD : J * D = E * J - P := by
    rw [← hR]
    abel
  have e1 : Dᵀ * (Jᵀ * G * J) = (J * D)ᵀ * G * J := by
    rw [Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  have e2 : Jᵀ * G * J * D = Jᵀ * G * (J * D) := by
    simp only [Matrix.mul_assoc]
  rw [e1, e2, hJD, Matrix.transpose_sub, Matrix.transpose_mul]
  noncomm_ring

/-- The same, entry by entry, in the form in which the slopes arrive: `h` are the second slopes of
the change of coordinates, `dg` the slopes of the length measure, `X'`, `dX'` the field and its
slopes in the new coordinates, `X`, `dX` in the old ones. -/
theorem lie_algebra {J G dX dX' : Fin n → Fin n → ℝ} {h dg : Fin n → Fin n → Fin n → ℝ}
    {X X' : Fin n → ℝ} (hsymh : ∀ α a b, h α a b = h α b a)
    (hX : ∀ α, ∑ κ, J α κ * X' κ = X α)
    (hR : ∀ α μ, ∑ κ, (h α μ κ * X' κ + J α κ * dX' κ μ) = ∑ γ, J γ μ * dX α γ)
    (μ ν : Fin n) :
    ∑ κ, (X' κ * (∑ α, ∑ β, (h α κ μ * J β ν * G α β + J α μ * h β κ ν * G α β
              + J α μ * J β ν * ∑ γ, J γ κ * dg γ α β))
            + (∑ α, ∑ β, J α κ * J β ν * G α β) * dX' κ μ
            + (∑ α, ∑ β, J α μ * J β κ * G α β) * dX' κ ν)
      = ∑ α, ∑ β, J α μ * J β ν
          * ∑ k, (X k * dg k α β + G k β * dX k α + G α k * dX k β) := by
  -- The tables, as matrices.
  obtain ⟨Jm, hJm⟩ : ∃ M : Matrix (Fin n) (Fin n) ℝ, ∀ a b, M a b = J a b :=
    ⟨Matrix.of J, fun _ _ => rfl⟩
  obtain ⟨Gm, hGm⟩ : ∃ M : Matrix (Fin n) (Fin n) ℝ, ∀ a b, M a b = G a b :=
    ⟨Matrix.of G, fun _ _ => rfl⟩
  obtain ⟨Dm, hDm⟩ : ∃ M : Matrix (Fin n) (Fin n) ℝ, ∀ a b, M a b = dX' a b :=
    ⟨Matrix.of dX', fun _ _ => rfl⟩
  obtain ⟨Em, hEm⟩ : ∃ M : Matrix (Fin n) (Fin n) ℝ, ∀ a b, M a b = dX a b :=
    ⟨Matrix.of dX, fun _ _ => rfl⟩
  obtain ⟨Pm, hPm⟩ : ∃ M : Matrix (Fin n) (Fin n) ℝ, ∀ a b, M a b = ∑ κ, h a b κ * X' κ :=
    ⟨Matrix.of fun a b => ∑ κ, h a b κ * X' κ, fun _ _ => rfl⟩
  obtain ⟨Lm, hLm⟩ : ∃ M : Matrix (Fin n) (Fin n) ℝ, ∀ a b, M a b = ∑ γ, X γ * dg γ a b :=
    ⟨Matrix.of fun a b => ∑ γ, X γ * dg γ a b, fun _ _ => rfl⟩
  have hRm : Pm + Jm * Dm = Em * Jm := by
    ext α κ
    simp only [Matrix.add_apply, Matrix.mul_apply, hPm, hJm, hDm, hEm]
    rw [← Finset.sum_add_distrib, hR α κ]
    exact Finset.sum_congr rfl fun γ _ => mul_comm _ _
  have core := congrFun (congrFun (lie_core (G := Gm) (L := Lm) hRm) μ) ν
  simp only [Matrix.add_apply] at core
  rw [sandwich_apply Pm Gm Jm, sandwich_apply Jm Gm Pm, sandwich_apply Jm Lm Jm] at core
  -- The first part: the slopes of the new length measure along the new field.
  have s1 : ∑ κ, X' κ * (∑ α, ∑ β, (h α κ μ * J β ν * G α β + J α μ * h β κ ν * G α β
        + J α μ * J β ν * ∑ γ, J γ κ * dg γ α β))
      = (∑ α, ∑ β, Pm α μ * Jm β ν * Gm α β) + (∑ α, ∑ β, Jm α μ * Pm β ν * Gm α β)
        + ∑ α, ∑ β, Jm α μ * Jm β ν * Lm α β := by
    have p : ∀ α β, ∑ κ, X' κ * (h α κ μ * J β ν * G α β + J α μ * h β κ ν * G α β
          + J α μ * J β ν * ∑ γ, J γ κ * dg γ α β)
        = Pm α μ * Jm β ν * Gm α β + Jm α μ * Pm β ν * Gm α β + Jm α μ * Jm β ν * Lm α β := by
      intro α β
      have p1 : ∑ κ, X' κ * (h α κ μ * J β ν * G α β)
          = (∑ κ, h α μ κ * X' κ) * J β ν * G α β := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun κ _ => by rw [hsymh α κ μ]; ring
      have p2 : ∑ κ, X' κ * (J α μ * h β κ ν * G α β)
          = J α μ * (∑ κ, h β ν κ * X' κ) * G α β := by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun κ _ => by rw [hsymh β κ ν]; ring
      have p3 : ∑ κ, X' κ * (J α μ * J β ν * ∑ γ, J γ κ * dg γ α β)
          = J α μ * J β ν * ∑ γ, X γ * dg γ α β := by
        calc ∑ κ, X' κ * (J α μ * J β ν * ∑ γ, J γ κ * dg γ α β)
            = ∑ κ, ∑ γ, J α μ * J β ν * (J γ κ * X' κ * dg γ α β) :=
              Finset.sum_congr rfl fun κ _ => by
                rw [Finset.mul_sum, Finset.mul_sum]
                exact Finset.sum_congr rfl fun γ _ => by ring
          _ = ∑ γ, ∑ κ, J α μ * J β ν * (J γ κ * X' κ * dg γ α β) := Finset.sum_comm
          _ = J α μ * J β ν * ∑ γ, X γ * dg γ α β := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun γ _ => by
                rw [← Finset.mul_sum, ← Finset.sum_mul, hX γ]
      simp only [mul_add, Finset.sum_add_distrib, p1, p2, p3, hPm, hJm, hGm, hLm]
    calc ∑ κ, X' κ * (∑ α, ∑ β, (h α κ μ * J β ν * G α β + J α μ * h β κ ν * G α β
          + J α μ * J β ν * ∑ γ, J γ κ * dg γ α β))
        = ∑ κ, ∑ α, ∑ β, X' κ * (h α κ μ * J β ν * G α β + J α μ * h β κ ν * G α β
            + J α μ * J β ν * ∑ γ, J γ κ * dg γ α β) :=
          Finset.sum_congr rfl fun κ _ => by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun α _ => Finset.mul_sum _ _ _
      _ = ∑ α, ∑ β, ∑ κ, X' κ * (h α κ μ * J β ν * G α β + J α μ * h β κ ν * G α β
            + J α μ * J β ν * ∑ γ, J γ κ * dg γ α β) :=
          (sum3_rotate (fun α β κ => X' κ * (h α κ μ * J β ν * G α β
            + J α μ * h β κ ν * G α β + J α μ * J β ν * ∑ γ, J γ κ * dg γ α β))).symm
      _ = ∑ α, ∑ β, (Pm α μ * Jm β ν * Gm α β + Jm α μ * Pm β ν * Gm α β
            + Jm α μ * Jm β ν * Lm α β) :=
          Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => p α β
      _ = _ := by simp only [Finset.sum_add_distrib]
  -- The other two parts: the new length measure times the slopes of the new field.
  have s2 : ∑ κ, (∑ α, ∑ β, J α κ * J β ν * G α β) * dX' κ μ
      = (Dmᵀ * (Jmᵀ * Gm * Jm)) μ ν := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [sandwich_apply, Matrix.transpose_apply, hDm, mul_comm]
    simp only [hJm, hGm]
  have s3 : ∑ κ, (∑ α, ∑ β, J α μ * J β κ * G α β) * dX' κ ν
      = (Jmᵀ * Gm * Jm * Dm) μ ν := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [sandwich_apply, hDm]
    simp only [hJm, hGm]
  -- The right-hand side.
  have s4 : ∑ α, ∑ β, J α μ * J β ν
        * ∑ k, (X k * dg k α β + G k β * dX k α + G α k * dX k β)
      = (Jmᵀ * (Lm + Emᵀ * Gm + Gm * Em) * Jm) μ ν := by
    rw [sandwich_apply]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    rw [hJm, hJm]
    congr 1
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, hLm, hEm, hGm,
      Finset.sum_add_distrib]
    congr 1
    congr 1
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, s1, s2, s3, s4]
  exact core

/-! ## The theorem -/

/-- The change of a length measure along a field only looks at the length measure near the
point. -/
theorem lieD_congr {g g' : Fin n → Fin n → Coords n → ℝ} {x : Coords n}
    (h : ∀ i j, g i j =ᶠ[𝓝 x] g' i j) (ξ : Fin n → Coords n → ℝ) (i j : Fin n) :
    lieD g ξ i j x = lieD g' ξ i j x := by
  have hv : ∀ a b, g a b x = g' a b x := fun a b => (h a b).eq_of_nhds
  have hs : ∀ a b k, slope k (g a b) x = slope k (g' a b) x :=
    fun a b k => slope_congr (h a b) k
  simp only [lieD, hv, hs]

section Main

variable {Φ : Coords n → Coords n} {g : Fin n → Fin n → Coords n → ℝ}
  {ξ ξ' : Fin n → Coords n → ℝ} {x : Coords n}

/-- **The change of a length measure along a field, in two sets of coordinates.** Computed in the
new coordinates, it is the one computed in the old coordinates, re-written the way a length
measure is re-written. -/
theorem lieD_inNewCoords (hΦ : ∀ α, ContDiffAt ℝ 2 (fun z => Φ z α) x)
    (hg : ∀ α β, DifferentiableAt ℝ (g α β) (Φ x))
    (hξ : ∀ α, DifferentiableAt ℝ (ξ α) (Φ x)) (hξ' : ∀ μ, DifferentiableAt ℝ (ξ' μ) x)
    (hrel : ∀ᶠ y in 𝓝 x, ∀ α, ∑ μ, jac Φ α μ y * ξ' μ y = ξ α (Φ y)) (μ ν : Fin n) :
    lieD (inNewCoords Φ g) ξ' μ ν x
      = ∑ α, ∑ β, jac Φ α μ x * jac Φ β ν x * lieD g ξ α β (Φ x) := by
  have hJ : ∀ α κ, DifferentiableAt ℝ (jac Φ α κ) x := fun α κ =>
    (contDiffAt_slope (m := 1) (hΦ α) (by simp) (by simp) (by norm_num) κ).differentiableAt
      (by simp)
  have hΦd : DifferentiableAt ℝ Φ x :=
    differentiableAt_pi.2 fun α => (hΦ α).differentiableAt (by simp)
  -- The order of two slopes of the change of coordinates does not matter.
  have hsymh : ∀ α a b, slope a (jac Φ α b) x = slope b (jac Φ α a) x :=
    fun α a b => slope_slope_comm (hΦ α) a b
  have hX : ∀ α, ∑ κ, jac Φ α κ x * ξ' κ x = ξ α (Φ x) := fun α => hrel.self_of_nhds α
  -- "The same field", differentiated.
  have hR : ∀ α μ, ∑ κ, (slope μ (jac Φ α κ) x * ξ' κ x + jac Φ α κ x * slope μ (ξ' κ) x)
      = ∑ γ, jac Φ γ μ x * slope γ (ξ α) (Φ x) := by
    intro α μ
    have e1 : slope μ (fun y => ∑ κ, jac Φ α κ y * ξ' κ y) x
        = slope μ (fun y => ξ α (Φ y)) x :=
      slope_congr (hrel.mono fun y hy => hy α) μ
    have hprod : ∀ κ, DifferentiableAt ℝ (fun y => jac Φ α κ y * ξ' κ y) x :=
      fun κ => (hJ α κ).mul (hξ' κ)
    rw [slope_sum hprod, slope_comp (hξ α) hΦd] at e1
    rw [← e1]
    exact Finset.sum_congr rfl fun κ _ => (slope_mul (hJ α κ) (hξ' κ) μ).symm
  have key := lie_algebra (J := fun α μ => jac Φ α μ x) (G := fun α β => g α β (Φ x))
    (dX := fun α γ => slope γ (ξ α) (Φ x)) (dX' := fun κ μ => slope μ (ξ' κ) x)
    (h := fun α a b => slope a (jac Φ α b) x) (dg := fun γ α β => slope γ (g α β) (Φ x))
    (X := fun α => ξ α (Φ x)) (X' := fun κ => ξ' κ x) hsymh hX hR μ ν
  simp only [lieD, slope_inNewCoords hJ hΦd hg]
  simp only [inNewCoords]
  exact key

/-- **"Unchanged by a move" does not depend on the coordinates.** A move along a field of arrows
leaves the length measure unchanged in the new coordinates exactly when it does in the old ones.
`hJ` says that the change of coordinates loses no direction. -/
theorem leavesUnchangedAt_inNewCoords (hΦ : ∀ α, ContDiffAt ℝ 2 (fun z => Φ z α) x)
    (hg : ∀ α β, DifferentiableAt ℝ (g α β) (Φ x))
    (hξ : ∀ α, DifferentiableAt ℝ (ξ α) (Φ x)) (hξ' : ∀ μ, DifferentiableAt ℝ (ξ' μ) x)
    (hrel : ∀ᶠ y in 𝓝 x, ∀ α, ∑ μ, jac Φ α μ y * ξ' μ y = ξ α (Φ y))
    (hJ : (tab (jac Φ) x).det ≠ 0) :
    LeavesUnchangedAt (inNewCoords Φ g) ξ' x ↔ LeavesUnchangedAt g ξ (Φ x) := by
  have key := lieD_inNewCoords hΦ hg hξ hξ' hrel
  have htab : Matrix.of (fun μ ν => lieD (inNewCoords Φ g) ξ' μ ν x)
      = (tab (jac Φ) x)ᵀ * Matrix.of (fun α β => lieD g ξ α β (Φ x)) * tab (jac Φ) x := by
    ext μ ν
    rw [Matrix.of_apply, key μ ν, sandwich_apply]
    rfl
  constructor
  · intro h α β
    have h0 : Matrix.of (fun μ ν => lieD (inNewCoords Φ g) ξ' μ ν x) = 0 := by
      ext μ ν
      exact h μ ν
    rw [htab] at h0
    exact congrFun (congrFun ((sandwich_eq_zero_iff hJ).mp h0) α) β
  · intro h μ ν
    rw [key μ ν]
    exact Finset.sum_eq_zero fun α _ => Finset.sum_eq_zero fun β _ => by rw [h α β, mul_zero]

end Main

end GravityInLean
