/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.SlopeRules
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

import Mathlib.Tactic

/-!
# The curvature does not depend on the coordinates

Curvature is defined in this project by the classic formula in coordinates (`Curvature.lean`).
This file shows that the formula gives the same answer in any coordinates.

A change of coordinates is a function `Φ` that turns the new coordinates of a point into its old
ones. The same length measure, written in the new coordinates, is `inNewCoords Φ g`: the length of
a step is unchanged, only the way the step is written changes.

**What is proved here.**

* `christoffel_inNewCoords`: how the connection changes. It is not simply re-written like the
  length measure: an extra term appears, made of the second slopes of `Φ`.
* `riemann_inNewCoords`: the full curvature (the Riemann tensor of the textbooks), built from the
  connection, *is* simply re-written. The extra terms cancel.
* `ricci_inNewCoords`: so the curvature used in this project (the Ricci tensor) is simply
  re-written as well: in new coordinates it is the old curvature, with each of its two slots
  multiplied by the table of slopes of `Φ`.
* `isRicciFlatAt_inNewCoords`: in particular "space is empty at this point" does not depend on
  the coordinates.

**What is assumed.** The change of coordinates is three times smoothly differentiable and the
length measure twice; the length measure is symmetric and has an inverse. These are the
textbooks' conditions.
-/

@[expose] public section

namespace GravityInLean

open Filter Topology Matrix

variable {n : ℕ}

/-! ## Sums over three indices -/

theorem sum3_rotate (F : Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, F a b c = ∑ c, ∑ a, ∑ b, F a b c := by
  calc ∑ a, ∑ b, ∑ c, F a b c = ∑ a, ∑ c, ∑ b, F a b c :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, F a b c := Finset.sum_comm

/-! ## The algebra behind the change of the connection

In this section everything is a table of plain numbers: the values, at one point, of the slopes
that appear. `J` is the table of slopes of the change of coordinates, `h` the table of its second
slopes, `gΦ` the old length measure, `dg` the table of its slopes, and `dg'` the table of slopes
of the new length measure. -/

section Algebra

variable {J gΦ ginvΦ ginv' : Matrix (Fin n) (Fin n) ℝ} {h dg dg' : Fin n → Fin n → Fin n → ℝ}

/-- The slopes of the new length measure, sorted into three pieces. -/
theorem dgNew_split (hsymg : ∀ α β, gΦ α β = gΦ β α)
    (hdg' : ∀ a b c, dg' a b c = ∑ α, ∑ β,
      (h α a b * J β c * gΦ α β + J α b * h β a c * gΦ α β
        + J α b * J β c * ∑ γ, J γ a * dg γ α β)) (a b c : Fin n) :
    dg' a b c = (∑ α, h α a b * (gΦ * J) α c) + (∑ α, h α a c * (gΦ * J) α b)
      + ∑ γ, J γ a * ∑ α, ∑ β, J α b * J β c * dg γ α β := by
  rw [hdg']
  simp only [Finset.sum_add_distrib]
  have e1 : ∑ α, ∑ β, h α a b * J β c * gΦ α β = ∑ α, h α a b * (gΦ * J) α c := by
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun β _ => by ring
  have e2 : ∑ α, ∑ β, J α b * h β a c * gΦ α β = ∑ α, h α a c * (gΦ * J) α b := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun α _ => by rw [hsymg β α]; ring
  have e3 : ∑ α, ∑ β, J α b * J β c * ∑ γ, J γ a * dg γ α β
      = ∑ γ, J γ a * ∑ α, ∑ β, J α b * J β c * dg γ α β := by
    simp only [Finset.mul_sum]
    rw [sum3_rotate]
    exact Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun α _ =>
      Finset.sum_congr rfl fun β _ => by ring
  rw [e1, e2, e3]

/-- The combination of slopes that enters the new connection is the old combination, re-written,
plus a term with the second slopes of the change of coordinates. -/
theorem bracket_new (hsymg : ∀ α β, gΦ α β = gΦ β α) (hsymh : ∀ α b c, h α b c = h α c b)
    (hdg' : ∀ a b c, dg' a b c = ∑ α, ∑ β,
      (h α a b * J β c * gΦ α β + J α b * h β a c * gΦ α β
        + J α b * J β c * ∑ γ, J γ a * dg γ α β)) (a b c : Fin n) :
    dg' b a c + dg' c a b - dg' a b c
      = ∑ α, J α a * (2 * (gΦ *ᵥ fun β => h β b c) α
          + ∑ β, ∑ γ, J β b * J γ c * (dg β α γ + dg γ α β - dg α β γ)) := by
  have hP : ∀ p q r : Fin n, ∑ α, h α p q * (gΦ * J) α r = ∑ α, h α q p * (gΦ * J) α r :=
    fun p q r => Finset.sum_congr rfl fun α _ => by rw [hsymh α p q]
  -- The term with the second slopes.
  have eP : ∑ α, h α b c * (gΦ * J) α a = ∑ α, J α a * (gΦ *ᵥ fun β => h β b c) α := by
    have e : ∑ α, h α b c * (gΦ * J) α a = ∑ α, ∑ β, h α b c * (gΦ α β * J β a) :=
      Finset.sum_congr rfl fun α _ => by rw [Matrix.mul_apply, Finset.mul_sum]
    rw [e, Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun α _ => by rw [hsymg β α]; ring
  -- The three terms with the slopes of the old length measure.
  have eQ1 : ∑ γ, J γ b * ∑ α, ∑ β, J α a * J β c * dg γ α β
      = ∑ α, J α a * ∑ β, ∑ γ, J β b * J γ c * dg β α γ := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun γ _ =>
      Finset.sum_congr rfl fun β _ => by ring
  have eQ2 : ∑ γ, J γ c * ∑ α, ∑ β, J α a * J β b * dg γ α β
      = ∑ α, J α a * ∑ β, ∑ γ, J β b * J γ c * dg γ α β := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun γ _ => by ring
  rw [dgNew_split hsymg hdg' b a c, dgNew_split hsymg hdg' c a b, dgNew_split hsymg hdg' a b c,
    hP b a c, hP c a b, hP c b a, eQ1, eQ2]
  have e2 : ∑ α, J α a * (2 * (gΦ *ᵥ fun β => h β b c) α)
      = 2 * ∑ α, J α a * (gΦ *ᵥ fun β => h β b c) α := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun α _ => by ring
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [eP, e2]
  ring

/-- **How the connection changes, as algebra.** With the slopes of the new length measure as in
`hdg'`, the new connection, multiplied by the table of slopes `J`, is the second slopes of the
change of coordinates plus the old connection, re-written. -/
theorem christoffel_law_algebra (hsymg : ∀ α β, gΦ α β = gΦ β α)
    (hsymh : ∀ α b c, h α b c = h α c b)
    (hdg' : ∀ a b c, dg' a b c = ∑ α, ∑ β,
      (h α a b * J β c * gΦ α β + J α b * h β a c * gΦ α β
        + J α b * J β c * ∑ γ, J γ a * dg γ α β))
    (hinv : gΦ * ginvΦ = 1) (hinv' : Jᵀ * gΦ * J * ginv' = 1) (ε μ ν : Fin n) :
    ∑ κ, J ε κ * (1 / 2 * ∑ lam, ginv' κ lam * (dg' μ lam ν + dg' ν lam μ - dg' lam μ ν))
      = h ε μ ν + ∑ β, ∑ γ, J β μ
          * (1 / 2 * ∑ σ, ginvΦ ε σ * (dg β σ γ + dg γ σ β - dg σ β γ)) * J γ ν := by
  -- The combination of slopes, as `Jᵀ` applied to a vector.
  have hX : (fun lam => dg' μ lam ν + dg' ν lam μ - dg' lam μ ν)
      = Jᵀ *ᵥ fun α => 2 * (gΦ *ᵥ fun β => h β μ ν) α
          + ∑ β, ∑ γ, J β μ * J γ ν * (dg β α γ + dg γ α β - dg α β γ) := by
    funext lam
    rw [bracket_new hsymg hsymh hdg' lam μ ν]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  -- `J · ginv' · Jᵀ` is the old inverse.
  have key : J * ginv' * Jᵀ = ginvΦ := by
    have h1 : Jᵀ * (gΦ * J * ginv') = 1 := by
      rw [← hinv']
      simp only [Matrix.mul_assoc]
    have h2 : gΦ * J * ginv' * Jᵀ = 1 := mul_eq_one_comm.mp h1
    have h3 : gΦ * (J * ginv' * Jᵀ) = 1 := by
      rw [← h2]
      simp only [Matrix.mul_assoc]
    exact (Matrix.inv_eq_right_inv h3).symm.trans (Matrix.inv_eq_right_inv hinv)
  have hinvL : ginvΦ * gΦ = 1 := mul_eq_one_comm.mp hinv
  -- The left-hand side, as matrices applied to that vector.
  have e1 : ∑ κ, J ε κ
        * (1 / 2 * ∑ lam, ginv' κ lam * (dg' μ lam ν + dg' ν lam μ - dg' lam μ ν))
      = 1 / 2 * (J *ᵥ (ginv' *ᵥ fun lam => dg' μ lam ν + dg' ν lam μ - dg' lam μ ν)) ε := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun lam _ => by ring
  -- The old connection, re-written, with the sum over `σ` outside.
  have e3 : ∑ β, ∑ γ, J β μ
        * (1 / 2 * ∑ σ, ginvΦ ε σ * (dg β σ γ + dg γ σ β - dg σ β γ)) * J γ ν
      = 1 / 2 * (ginvΦ *ᵥ fun α =>
          ∑ β, ∑ γ, J β μ * J γ ν * (dg β α γ + dg γ α β - dg α β γ)) ε := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [sum3_rotate]
    exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun β _ =>
      Finset.sum_congr rfl fun γ _ => by ring
  have e4 : (fun α => 2 * (gΦ *ᵥ fun β => h β μ ν) α
        + ∑ β, ∑ γ, J β μ * J γ ν * (dg β α γ + dg γ α β - dg α β γ))
      = (2 : ℝ) • (gΦ *ᵥ fun β => h β μ ν)
        + fun α => ∑ β, ∑ γ, J β μ * J γ ν * (dg β α γ + dg γ α β - dg α β γ) := by
    funext α
    simp
  rw [e1, e3, hX, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, key, e4, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_mulVec, hinvL, Matrix.one_mulVec]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Algebra

/-! ## The same length measure in new coordinates -/

/-- The same length measure, written in new coordinates. `Φ` turns the new coordinates of a point
into its old ones; the length of a step stays what it was. -/
noncomputable def inNewCoords (Φ : Coords n → Coords n) (g : Fin n → Fin n → Coords n → ℝ)
    (μ ν : Fin n) : Coords n → ℝ := fun x =>
  ∑ α, ∑ β, jac Φ α μ x * jac Φ β ν x * g α β (Φ x)

/-- The values of a table of functions at a point, as a table of numbers. -/
noncomputable def tab (T : Fin n → Fin n → Coords n → ℝ) (x : Coords n) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => T a b x

/-- In the language of tables: new length measure = `Jᵀ · g · J`. -/
theorem tab_inNewCoords (Φ : Coords n → Coords n) (g : Fin n → Fin n → Coords n → ℝ)
    (y : Coords n) :
    tab (inNewCoords Φ g) y = (tab (jac Φ) y)ᵀ * tab g (Φ y) * tab (jac Φ) y := by
  ext μ ν
  simp only [tab, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, inNewCoords,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => by ring

/-- The new length measure is symmetric where the old one is. -/
theorem inNewCoords_symm {Φ : Coords n → Coords n} {g : Fin n → Fin n → Coords n → ℝ}
    {y : Coords n} (hsymm : ∀ α β, g α β (Φ y) = g β α (Φ y)) (μ ν : Fin n) :
    inNewCoords Φ g μ ν y = inNewCoords Φ g ν μ y := by
  simp only [inNewCoords]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => by
    rw [hsymm α β]
    ring

/-- The slopes of the new length measure. -/
theorem slope_inNewCoords {Φ : Coords n → Coords n} {g : Fin n → Fin n → Coords n → ℝ}
    {y : Coords n} (hJ : ∀ α μ, DifferentiableAt ℝ (jac Φ α μ) y) (hΦ : DifferentiableAt ℝ Φ y)
    (hg : ∀ α β, DifferentiableAt ℝ (g α β) (Φ y)) (a b c : Fin n) :
    slope a (inNewCoords Φ g b c) y = ∑ α, ∑ β,
      (slope a (jac Φ α b) y * jac Φ β c y * g α β (Φ y)
        + jac Φ α b y * slope a (jac Φ β c) y * g α β (Φ y)
        + jac Φ α b y * jac Φ β c y * ∑ γ, jac Φ γ a y * slope γ (g α β) (Φ y)) := by
  have hgc : ∀ α β, DifferentiableAt ℝ (fun z => g α β (Φ z)) y := fun α β => (hg α β).comp y hΦ
  have h1 : ∀ α β, DifferentiableAt ℝ (fun z => jac Φ α b z * jac Φ β c z) y :=
    fun α β => (hJ α b).mul (hJ β c)
  have h2 : ∀ α β, DifferentiableAt ℝ (fun z => jac Φ α b z * jac Φ β c z * g α β (Φ z)) y :=
    fun α β => (h1 α β).mul (hgc α β)
  have h3 : ∀ α, DifferentiableAt ℝ
      (fun z => ∑ β, jac Φ α b z * jac Φ β c z * g α β (Φ z)) y :=
    fun α => DifferentiableAt.fun_sum fun β _ => h2 α β
  change slope a (fun z => ∑ α, ∑ β, jac Φ α b z * jac Φ β c z * g α β (Φ z)) y = _
  rw [slope_sum h3]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [slope_sum (h2 α)]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [slope_mul (h1 α β) (hgc α β), slope_mul (hJ α b) (hJ β c), slope_comp (hg α β) hΦ]
  ring

/-- **How the connection changes, at one point.** The new connection, multiplied by the table of
slopes of the change of coordinates, is the second slopes of the change of coordinates plus the
old connection, re-written. The extra term is why a connection is not "just re-written". -/
theorem christoffel_inNewCoords_at {Φ : Coords n → Coords n}
    {g ginv ginv' : Fin n → Fin n → Coords n → ℝ} {y : Coords n}
    (hΦ : ∀ α, ContDiffAt ℝ 2 (fun z => Φ z α) y)
    (hg : ∀ α β, DifferentiableAt ℝ (g α β) (Φ y))
    (hsymm : ∀ α β, g α β (Φ y) = g β α (Φ y))
    (hinv : ∀ α γ, ∑ β, g α β (Φ y) * ginv β γ (Φ y) = if α = γ then 1 else 0)
    (hinv' : ∀ μ κ, ∑ ν, inNewCoords Φ g μ ν y * ginv' ν κ y = if μ = κ then 1 else 0)
    (ε μ ν : Fin n) :
    ∑ κ, jac Φ ε κ y * christoffel (inNewCoords Φ g) ginv' κ μ ν y
      = slope μ (jac Φ ε ν) y
        + ∑ β, ∑ γ, jac Φ β μ y * christoffel g ginv ε β γ (Φ y) * jac Φ γ ν y := by
  have hJ : ∀ α κ, DifferentiableAt ℝ (jac Φ α κ) y := fun α κ =>
    (contDiffAt_slope (m := 1) (hΦ α) (by simp) (by simp) (by norm_num) κ).differentiableAt
      (by simp)
  have hΦd : DifferentiableAt ℝ Φ y :=
    differentiableAt_pi.2 fun α => (hΦ α).differentiableAt (by simp)
  have m1 : tab g (Φ y) * tab ginv (Φ y) = 1 := by
    ext α γ
    simp only [tab, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    exact hinv α γ
  have m2 : (tab (jac Φ) y)ᵀ * tab g (Φ y) * tab (jac Φ) y * tab ginv' y = 1 := by
    rw [← tab_inNewCoords]
    ext α γ
    simp only [tab, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    exact hinv' α γ
  exact christoffel_law_algebra (J := tab (jac Φ) y) (gΦ := tab g (Φ y))
    (ginvΦ := tab ginv (Φ y)) (ginv' := tab ginv' y)
    (h := fun α b c => slope b (jac Φ α c) y) (dg := fun γ α β => slope γ (g α β) (Φ y))
    (dg' := fun a b c => slope a (inNewCoords Φ g b c) y) hsymm
    (fun α b c => slope_slope_comm (hΦ α) b c) (fun a b c => slope_inNewCoords hJ hΦd hg a b c)
    m1 m2 ε μ ν

/-! ## Tables of functions and their slopes -/

/-- The slopes of a table of functions along the coordinate `ρ` at a point, as a table of
numbers. -/
noncomputable def dtab (ρ : Fin n) (T : Fin n → Fin n → Coords n → ℝ) (x : Coords n) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => slope ρ (T a b) x

/-- The product of two tables of functions, as a table of functions. -/
noncomputable def mulT (P Q : Fin n → Fin n → Coords n → ℝ) (a c : Fin n) : Coords n → ℝ :=
  fun y => ∑ b, P a b y * Q b c y

theorem tab_mulT (P Q : Fin n → Fin n → Coords n → ℝ) (x : Coords n) :
    tab (mulT P Q) x = tab P x * tab Q x := by
  ext a c
  simp only [tab, mulT, Matrix.of_apply, Matrix.mul_apply]

/-- The product rule for tables. -/
theorem dtab_mulT {P Q : Fin n → Fin n → Coords n → ℝ} {x : Coords n}
    (hP : ∀ a b, DifferentiableAt ℝ (P a b) x) (hQ : ∀ a b, DifferentiableAt ℝ (Q a b) x)
    (ρ : Fin n) : dtab ρ (mulT P Q) x = dtab ρ P x * tab Q x + tab P x * dtab ρ Q x := by
  ext a c
  have hPQ : ∀ b, DifferentiableAt ℝ (fun y => P a b y * Q b c y) x :=
    fun b => (hP a b).mul (hQ b c)
  have e : dtab ρ (mulT P Q) x a c = ∑ b, slope ρ (fun y => P a b y * Q b c y) x :=
    slope_sum hPQ ρ
  rw [e]
  simp only [dtab, tab, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => slope_mul (hP a b) (hQ b c) ρ

theorem differentiableAt_mulT {P Q : Fin n → Fin n → Coords n → ℝ} {x : Coords n}
    (hP : ∀ a b, DifferentiableAt ℝ (P a b) x) (hQ : ∀ a b, DifferentiableAt ℝ (Q a b) x)
    (a c : Fin n) : DifferentiableAt ℝ (mulT P Q a c) x :=
  DifferentiableAt.fun_sum fun b _ => (hP a b).mul (hQ b c)

/-! ## The full curvature -/

/-- A connection, read as one table for each direction `μ`. -/
noncomputable def dirT (Γ : Fin n → Fin n → Fin n → Coords n → ℝ) (μ : Fin n) :
    Fin n → Fin n → Coords n → ℝ :=
  fun a c => Γ a μ c

/-- The old connection with only its direction re-written for the new coordinates. -/
noncomputable def pullDir (Φ : Coords n → Coords n) (Γ : Fin n → Fin n → Fin n → Coords n → ℝ)
    (μ : Fin n) : Fin n → Fin n → Coords n → ℝ :=
  fun α γ y => ∑ β, jac Φ β μ y * Γ α β γ (Φ y)

/-- **The full curvature** built from a connection (the Riemann tensor of the textbooks): for each
pair of directions `ρ`, `μ` a table of numbers. It measures how much a step changes when it is
carried around a small loop spanned by the two directions. -/
noncomputable def riemM (Γ : Fin n → Fin n → Fin n → Coords n → ℝ) (ρ μ : Fin n) (x : Coords n) :
    Matrix (Fin n) (Fin n) ℝ :=
  dtab ρ (dirT Γ μ) x - dtab μ (dirT Γ ρ) x + tab (dirT Γ ρ) x * tab (dirT Γ μ) x
    - tab (dirT Γ μ) x * tab (dirT Γ ρ) x

/-- The curvature used in this project (the Ricci tensor) is a sum over the full curvature, for a
connection that is symmetric in its two lower indices. -/
theorem ricci_eq_sum_riemM {Γ : Fin n → Fin n → Fin n → Coords n → ℝ} {x : Coords n}
    (hsymm : ∀ᶠ y in 𝓝 x, ∀ a b c, Γ a b c y = Γ a c b y) (ν μ : Fin n) :
    ricci Γ ν μ x = ∑ ρ, riemM Γ ρ μ x ρ ν := by
  have hev : ∀ a b c, Γ a b c =ᶠ[𝓝 x] Γ a c b := fun a b c => hsymm.mono fun y hy => hy a b c
  have hval : ∀ a b c, Γ a b c x = Γ a c b x := fun a b c => (hev a b c).eq_of_nhds
  have t1 : ∑ a, slope a (Γ a ν μ) x = ∑ ρ, slope ρ (Γ ρ μ ν) x :=
    Finset.sum_congr rfl fun a _ => slope_congr (hev a ν μ) a
  have t2 : ∑ a, slope μ (Γ a ν a) x = ∑ ρ, slope μ (Γ ρ ρ ν) x :=
    Finset.sum_congr rfl fun a _ => slope_congr (hev a ν a) μ
  have t3 : ∑ a, ∑ d, Γ a a d x * Γ d ν μ x = ∑ ρ, ∑ κ, Γ ρ ρ κ x * Γ κ μ ν x :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => by rw [hval d ν μ]
  have t4 : ∑ a, ∑ d, Γ a μ d x * Γ d ν a x = ∑ ρ, ∑ κ, Γ ρ μ κ x * Γ κ ρ ν x :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => by rw [hval d ν a]
  simp only [riemM, dtab, tab, dirT, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.of_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [ricci, t1, t2, t3, t4]

/-- The algebra at the heart of the matter. `J` is the table of slopes of the change of
coordinates, `G` the new connection in two directions, `A` the old one re-written in its
direction. The first two assumptions are the law for the connection in the two directions, the
other two are its slopes, taken in the two possible orders. -/
theorem riemann_core {J dJρ dJμ ddJ Gρ Gμ dGρμ dGμρ Aρ Aμ dAρμ dAμρ : Matrix (Fin n) (Fin n) ℝ}
    (h1 : dJρ = J * Gρ - Aρ * J) (h2 : dJμ = J * Gμ - Aμ * J)
    (h3 : ddJ = dJρ * Gμ + J * dGρμ - (dAρμ * J + Aμ * dJρ))
    (h4 : ddJ = dJμ * Gρ + J * dGμρ - (dAμρ * J + Aρ * dJμ)) :
    J * (dGρμ - dGμρ + Gρ * Gμ - Gμ * Gρ) = (dAρμ - dAμρ + Aρ * Aμ - Aμ * Aρ) * J := by
  have h := h3.symm.trans h4
  rw [h1, h2] at h
  have e : J * (dGρμ - dGμρ + Gρ * Gμ - Gμ * Gρ) - (dAρμ - dAμρ + Aρ * Aμ - Aμ * Aρ) * J
      = ((J * Gρ - Aρ * J) * Gμ + J * dGρμ - (dAρμ * J + Aμ * (J * Gρ - Aρ * J)))
        - ((J * Gμ - Aμ * J) * Gρ + J * dGμρ - (dAμρ * J + Aρ * (J * Gμ - Aμ * J))) := by
    noncomm_ring
  rw [h, sub_self] at e
  exact sub_eq_zero.mp e

/-- The old connection, re-written in its direction, gives the old full curvature, re-written in
both directions. Here `s` are the second slopes of the change of coordinates, which do not depend
on the order of the two slopes. -/
theorem bracket_pullDir {J : Fin n → Fin n → ℝ} {s : Fin n → Fin n → Fin n → ℝ}
    {G : Fin n → Matrix (Fin n) (Fin n) ℝ} {dG : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ}
    (hs : ∀ ρ β μ, s ρ β μ = s μ β ρ) (ρ μ : Fin n) :
    (∑ β, s ρ β μ • G β + ∑ β, ∑ δ, (J β μ * J δ ρ) • dG δ β)
        - (∑ β, s μ β ρ • G β + ∑ β, ∑ δ, (J β ρ * J δ μ) • dG δ β)
        + (∑ δ, J δ ρ • G δ) * (∑ β, J β μ • G β) - (∑ β, J β μ • G β) * (∑ δ, J δ ρ • G δ)
      = ∑ δ, ∑ β, (J δ ρ * J β μ) • (dG δ β - dG β δ + G δ * G β - G β * G δ) := by
  have e1 : ∑ β, s ρ β μ • G β = ∑ β, s μ β ρ • G β :=
    Finset.sum_congr rfl fun β _ => by rw [hs ρ β μ]
  have e2 : ∑ β, ∑ δ, (J β μ * J δ ρ) • dG δ β = ∑ δ, ∑ β, (J δ ρ * J β μ) • dG δ β := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun δ _ => Finset.sum_congr rfl fun β _ => by rw [mul_comm]
  have e3 : (∑ δ, J δ ρ • G δ) * (∑ β, J β μ • G β)
      = ∑ δ, ∑ β, (J δ ρ * J β μ) • (G δ * G β) := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun δ _ => Finset.sum_congr rfl fun β _ =>
      smul_mul_smul_comm _ _ _ _
  have e4 : (∑ β, J β μ • G β) * (∑ δ, J δ ρ • G δ)
      = ∑ δ, ∑ β, (J δ ρ * J β μ) • (G β * G δ) := by
    rw [Finset.sum_mul_sum, Finset.sum_comm]
    exact Finset.sum_congr rfl fun δ _ => Finset.sum_congr rfl fun β _ => by
      rw [smul_mul_smul_comm, mul_comm]
  rw [e1, e2, e3, e4]
  simp only [smul_sub, smul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel

/-! ## The full curvature in new coordinates -/

section Curvature

variable {Φ : Coords n → Coords n} {Γ' Γ : Fin n → Fin n → Fin n → Coords n → ℝ} {x : Coords n}

theorem differentiableAt_pullDir (hJ : ∀ α κ, DifferentiableAt ℝ (jac Φ α κ) x)
    (hΦ : DifferentiableAt ℝ Φ x) (hΓ : ∀ a b c, DifferentiableAt ℝ (Γ a b c) (Φ x))
    (μ α γ : Fin n) : DifferentiableAt ℝ (pullDir Φ Γ μ α γ) x :=
  DifferentiableAt.fun_sum fun β _ => (hJ β μ).mul ((hΓ α β γ).comp x hΦ)

theorem tab_pullDir (Φ : Coords n → Coords n) (Γ : Fin n → Fin n → Fin n → Coords n → ℝ)
    (μ : Fin n) (x : Coords n) :
    tab (pullDir Φ Γ μ) x = ∑ β, jac Φ β μ x • tab (dirT Γ β) (Φ x) := by
  ext α γ
  simp only [tab, pullDir, dirT, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]

theorem dtab_pullDir (hJ : ∀ α κ, DifferentiableAt ℝ (jac Φ α κ) x)
    (hΦ : DifferentiableAt ℝ Φ x) (hΓ : ∀ a b c, DifferentiableAt ℝ (Γ a b c) (Φ x))
    (ρ μ : Fin n) :
    dtab ρ (pullDir Φ Γ μ) x = ∑ β, slope ρ (jac Φ β μ) x • tab (dirT Γ β) (Φ x)
      + ∑ β, ∑ δ, (jac Φ β μ x * jac Φ δ ρ x) • dtab δ (dirT Γ β) (Φ x) := by
  ext α γ
  have hc : ∀ β, DifferentiableAt ℝ (fun y => Γ α β γ (Φ y)) x := fun β => (hΓ α β γ).comp x hΦ
  have hprod : ∀ β, DifferentiableAt ℝ (fun y => jac Φ β μ y * Γ α β γ (Φ y)) x :=
    fun β => (hJ β μ).mul (hc β)
  have e : dtab ρ (pullDir Φ Γ μ) x α γ
      = ∑ β, slope ρ (fun y => jac Φ β μ y * Γ α β γ (Φ y)) x := slope_sum hprod ρ
  rw [e]
  simp only [dtab, tab, dirT, Matrix.of_apply, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [slope_mul (hJ β μ) (hc β), slope_comp (hΓ α β γ) hΦ, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun δ _ => by ring

/-- **The full curvature in new coordinates.** If the new connection `Γ'` and the old connection
`Γ` are related by the law for connections near `x`, then the full curvature is simply re-written:
the extra terms of the law cancel. Stated with the table of slopes on the upper index, so that no
inverse is needed. -/
theorem riemann_inNewCoords (hΦ : ∀ α, ContDiffAt ℝ 3 (fun z => Φ z α) x)
    (hΓ' : ∀ a b c, DifferentiableAt ℝ (Γ' a b c) x)
    (hΓ : ∀ a b c, DifferentiableAt ℝ (Γ a b c) (Φ x))
    (hlaw : ∀ᶠ y in 𝓝 x, ∀ ε μ ν, ∑ κ, jac Φ ε κ y * Γ' κ μ ν y
        = slope μ (jac Φ ε ν) y + ∑ β, ∑ γ, jac Φ β μ y * Γ ε β γ (Φ y) * jac Φ γ ν y)
    (ρ μ : Fin n) :
    tab (jac Φ) x * riemM Γ' ρ μ x
      = (∑ δ, ∑ β, (jac Φ δ ρ x * jac Φ β μ x) • riemM Γ δ β (Φ x)) * tab (jac Φ) x := by
  -- Smoothness of the pieces.
  have hΦ2 : ∀ α, ContDiffAt ℝ 2 (fun z => Φ z α) x := fun α => (hΦ α).of_le (by norm_num)
  have hJ2 : ∀ α κ, ContDiffAt ℝ 2 (jac Φ α κ) x := fun α κ =>
    contDiffAt_slope (hΦ α) (by simp) (by simp) (by norm_num) κ
  have hJ : ∀ α κ, DifferentiableAt ℝ (jac Φ α κ) x := fun α κ =>
    (hJ2 α κ).differentiableAt (by simp)
  have hΦd : DifferentiableAt ℝ Φ x :=
    differentiableAt_pi.2 fun α => (hΦ α).differentiableAt (by simp)
  have hA : ∀ κ α γ, DifferentiableAt ℝ (pullDir Φ Γ κ α γ) x :=
    fun κ α γ => differentiableAt_pullDir hJ hΦd hΓ κ α γ
  have hG' : ∀ κ a c, DifferentiableAt ℝ (dirT Γ' κ a c) x := fun κ a c => hΓ' a κ c
  -- The law for connections, as an equality of tables of functions near `x`.
  have hlawT : ∀ κ ε ν, (fun y => slope κ (jac Φ ε ν) y) =ᶠ[𝓝 x] fun y =>
      mulT (jac Φ) (dirT Γ' κ) ε ν y - mulT (pullDir Φ Γ κ) (jac Φ) ε ν y := by
    intro κ ε ν
    filter_upwards [hlaw] with y hy
    have h := hy ε κ ν
    have e : mulT (pullDir Φ Γ κ) (jac Φ) ε ν y
        = ∑ β, ∑ γ, jac Φ β κ y * Γ ε β γ (Φ y) * jac Φ γ ν y := by
      simp only [mulT, pullDir, Finset.sum_mul]
      exact Finset.sum_comm
    have e' : mulT (jac Φ) (dirT Γ' κ) ε ν y = ∑ lam, jac Φ ε lam y * Γ' lam κ ν y := rfl
    rw [e, e']
    linear_combination (-1 : ℝ) * h
  -- At the point itself.
  have F1 : ∀ κ, dtab κ (jac Φ) x
      = tab (jac Φ) x * tab (dirT Γ' κ) x - tab (pullDir Φ Γ κ) x * tab (jac Φ) x := by
    intro κ
    rw [← tab_mulT, ← tab_mulT]
    ext ε ν
    exact (hlawT κ ε ν).eq_of_nhds
  -- Its slopes.
  have F2 : ∀ κ τ, Matrix.of (fun ε ν => slope τ (fun y => slope κ (jac Φ ε ν) y) x)
      = dtab τ (jac Φ) x * tab (dirT Γ' κ) x + tab (jac Φ) x * dtab τ (dirT Γ' κ) x
        - (dtab τ (pullDir Φ Γ κ) x * tab (jac Φ) x
          + tab (pullDir Φ Γ κ) x * dtab τ (jac Φ) x) := by
    intro κ τ
    rw [← dtab_mulT hJ (hG' κ) τ, ← dtab_mulT (hA κ) hJ τ]
    ext ε ν
    simp only [dtab, Matrix.of_apply, Matrix.sub_apply]
    rw [slope_congr (hlawT κ ε ν) τ]
    exact slope_sub (differentiableAt_mulT hJ (hG' κ) ε ν) (differentiableAt_mulT (hA κ) hJ ε ν) τ
  -- The order of the two slopes does not matter.
  have F3 : Matrix.of (fun ε ν => slope ρ (fun y => slope μ (jac Φ ε ν) y) x)
      = Matrix.of (fun ε ν => slope μ (fun y => slope ρ (jac Φ ε ν) y) x) := by
    ext ε ν
    exact slope_slope_comm (hJ2 ε ν) ρ μ
  have core := riemann_core (F1 ρ) (F1 μ) (F2 μ ρ) (F3.trans (F2 ρ μ))
  have hb := bracket_pullDir (J := fun a b => jac Φ a b x)
    (s := fun τ β κ => slope τ (jac Φ β κ) x) (G := fun β => tab (dirT Γ β) (Φ x))
    (dG := fun δ β => dtab δ (dirT Γ β) (Φ x))
    (fun τ β κ => slope_slope_comm (hΦ2 β) τ κ) ρ μ
  rw [dtab_pullDir hJ hΦd hΓ ρ μ, dtab_pullDir hJ hΦd hΓ μ ρ, tab_pullDir, tab_pullDir, hb]
    at core
  exact core

/-- **The curvature of this project in new coordinates**, for any two connections related by the
law for connections. `K` is the inverse of the table of slopes of the change of coordinates. -/
theorem ricci_of_law (hΦ : ∀ α, ContDiffAt ℝ 3 (fun z => Φ z α) x)
    (hΓ' : ∀ a b c, DifferentiableAt ℝ (Γ' a b c) x)
    (hΓ : ∀ a b c, DifferentiableAt ℝ (Γ a b c) (Φ x))
    (hlaw : ∀ᶠ y in 𝓝 x, ∀ ε μ ν, ∑ κ, jac Φ ε κ y * Γ' κ μ ν y
        = slope μ (jac Φ ε ν) y + ∑ β, ∑ γ, jac Φ β μ y * Γ ε β γ (Φ y) * jac Φ γ ν y)
    (hsymm' : ∀ᶠ y in 𝓝 x, ∀ a b c, Γ' a b c y = Γ' a c b y)
    (hsymm : ∀ᶠ z in 𝓝 (Φ x), ∀ a b c, Γ a b c z = Γ a c b z)
    {K : Matrix (Fin n) (Fin n) ℝ} (hK : tab (jac Φ) x * K = 1) (ν μ : Fin n) :
    ricci Γ' ν μ x = ∑ γ, ∑ β, jac Φ γ ν x * jac Φ β μ x * ricci Γ γ β (Φ x) := by
  have hKJ : K * tab (jac Φ) x = 1 := mul_eq_one_comm.mp hK
  -- Each table of the new full curvature, with the inverse applied.
  have hR : ∀ ρ, riemM Γ' ρ μ x = K * ∑ δ, jac Φ δ ρ x
      • ((∑ β, jac Φ β μ x • riemM Γ δ β (Φ x)) * tab (jac Φ) x) := by
    intro ρ
    have h1 := riemann_inNewCoords hΦ hΓ' hΓ hlaw ρ μ
    have h2 : (∑ δ, ∑ β, (jac Φ δ ρ x * jac Φ β μ x) • riemM Γ δ β (Φ x)) * tab (jac Φ) x
        = ∑ δ, jac Φ δ ρ x • ((∑ β, jac Φ β μ x • riemM Γ δ β (Φ x)) * tab (jac Φ) x) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun δ _ => ?_
      rw [← smul_mul_assoc, Finset.smul_sum]
      congr 1
      exact Finset.sum_congr rfl fun β _ => by rw [mul_smul]
    rw [← h2, ← h1, ← Matrix.mul_assoc, hKJ, Matrix.one_mul]
  -- The sum over the direction that is also the upper index.
  have hsum : ∑ ρ, riemM Γ' ρ μ x ρ ν
      = ∑ δ, ((∑ β, jac Φ β μ x • riemM Γ δ β (Φ x)) * tab (jac Φ) x) δ ν := by
    have e1 : ∀ ρ, riemM Γ' ρ μ x ρ ν = ∑ δ, jac Φ δ ρ x
        * (K * ((∑ β, jac Φ β μ x • riemM Γ δ β (Φ x)) * tab (jac Φ) x)) ρ ν := by
      intro ρ
      rw [hR ρ, Matrix.mul_sum, Matrix.sum_apply]
      exact Finset.sum_congr rfl fun δ _ => by
        rw [Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl fun ρ _ => e1 ρ, Finset.sum_comm]
    refine Finset.sum_congr rfl fun δ _ => ?_
    have e2 : ∑ ρ, jac Φ δ ρ x
          * (K * ((∑ β, jac Φ β μ x • riemM Γ δ β (Φ x)) * tab (jac Φ) x)) ρ ν
        = (tab (jac Φ) x
          * (K * ((∑ β, jac Φ β μ x • riemM Γ δ β (Φ x)) * tab (jac Φ) x))) δ ν := by
      rw [Matrix.mul_apply]
      rfl
    rw [e2, ← Matrix.mul_assoc, hK, Matrix.one_mul]
  rw [ricci_eq_sum_riemM hsymm' ν μ, hsum]
  -- Write the entries out and collect the old curvature.
  have e3 : ∀ δ, ((∑ β, jac Φ β μ x • riemM Γ δ β (Φ x)) * tab (jac Φ) x) δ ν
      = ∑ γ, ∑ β, jac Φ β μ x * riemM Γ δ β (Φ x) δ γ * jac Φ γ ν x := by
    intro δ
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Matrix.sum_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun β _ => by
      rw [Matrix.smul_apply, smul_eq_mul]
      rfl
  rw [Finset.sum_congr rfl fun δ _ => e3 δ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [ricci_eq_sum_riemM hsymm γ β, Finset.mul_sum]
  exact Finset.sum_congr rfl fun δ _ => by ring

end Curvature

/-! ## The theorem -/

/-- The connection belonging to a symmetric length measure is symmetric in its two lower
indices. -/
theorem christoffel_symm {g ginv : Fin n → Fin n → Coords n → ℝ} {y : Coords n}
    (hsymm : ∀ᶠ w in 𝓝 y, ∀ α β, g α β w = g β α w) (a b c : Fin n) :
    christoffel g ginv a b c y = christoffel g ginv a c b y := by
  have hev : ∀ α β, g α β =ᶠ[𝓝 y] g β α := fun α β => hsymm.mono fun w hw => hw α β
  simp only [christoffel]
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [slope_congr (hev b c) d]
  ring

/-- The connection of a twice smoothly differentiable length measure can be differentiated. -/
theorem differentiableAt_christoffel {g ginv : Fin n → Fin n → Coords n → ℝ} {y : Coords n}
    (hg : ∀ α β, ContDiffAt ℝ 2 (g α β) y) (hgi : ∀ α β, DifferentiableAt ℝ (ginv α β) y)
    (a b c : Fin n) : DifferentiableAt ℝ (christoffel g ginv a b c) y := by
  have hs : ∀ i α β, DifferentiableAt ℝ (slope i (g α β)) y := fun i α β =>
    (contDiffAt_slope (m := 1) (hg α β) (by simp) (by simp) (by norm_num) i).differentiableAt
      (by simp)
  change DifferentiableAt ℝ (fun w => 1 / 2 * ∑ d, ginv a d w
    * (slope b (g d c) w + slope c (g d b) w - slope d (g b c) w)) y
  exact (DifferentiableAt.fun_sum fun d _ =>
    (hgi a d).mul (((hs b d c).add (hs c d b)).sub (hs d b c))).const_mul _

section Main

variable {Φ : Coords n → Coords n} {g ginv ginv' : Fin n → Fin n → Coords n → ℝ} {x : Coords n}

/-- The new length measure is as smooth as the old one. -/
theorem contDiffAt_inNewCoords (hΦ : ∀ α, ContDiffAt ℝ 3 (fun z => Φ z α) x)
    (hg : ∀ α β, ContDiffAt ℝ 2 (g α β) (Φ x)) (μ ν : Fin n) :
    ContDiffAt ℝ 2 (inNewCoords Φ g μ ν) x := by
  have hJ2 : ∀ α κ, ContDiffAt ℝ 2 (jac Φ α κ) x := fun α κ =>
    contDiffAt_slope (hΦ α) (by simp) (by simp) (by norm_num) κ
  have hΦ2 : ContDiffAt ℝ 2 Φ x := contDiffAt_pi.2 fun α => (hΦ α).of_le (by norm_num)
  have hgc : ∀ α β, ContDiffAt ℝ 2 (fun z => g α β (Φ z)) x := fun α β =>
    ContDiffAt.comp (g := g α β) x (hg α β) hΦ2
  change ContDiffAt ℝ 2 (fun z => ∑ α, ∑ β, jac Φ α μ z * jac Φ β ν z * g α β (Φ z)) x
  exact ContDiffAt.sum fun α _ => ContDiffAt.sum fun β _ =>
    ((hJ2 α μ).mul (hJ2 β ν)).mul (hgc α β)

/-- The table of slopes of the change of coordinates has an inverse wherever the new length
measure has one. -/
theorem exists_inverse_jac
    (hinv' : ∀ μ κ, ∑ ν, inNewCoords Φ g μ ν x * ginv' ν κ x = if μ = κ then 1 else 0) :
    ∃ K : Matrix (Fin n) (Fin n) ℝ, tab (jac Φ) x * K = 1 := by
  have m2 : (tab (jac Φ) x)ᵀ * (tab g (Φ x) * tab (jac Φ) x * tab ginv' x) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← tab_inNewCoords]
    ext α γ
    simp only [tab, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    exact hinv' α γ
  have m3 : tab g (Φ x) * tab (jac Φ) x * tab ginv' x * (tab (jac Φ) x)ᵀ = 1 :=
    mul_eq_one_comm.mp m2
  refine ⟨(tab g (Φ x) * tab (jac Φ) x * tab ginv' x)ᵀ, ?_⟩
  have m4 := congrArg Matrix.transpose m3
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at m4
  exact m4

/-- **The curvature does not depend on the coordinates.** Write a length measure in new
coordinates. Then its curvature, computed in the new coordinates from the general definitions, is
the old curvature re-written: each of its two slots is multiplied by the table of slopes of the
change of coordinates. -/
theorem ricci_inNewCoords (hΦ : ∀ α, ContDiffAt ℝ 3 (fun z => Φ z α) x)
    (hg : ∀ α β, ContDiffAt ℝ 2 (g α β) (Φ x)) (hgi : ∀ α β, ContDiffAt ℝ 1 (ginv α β) (Φ x))
    (hsymm : ∀ᶠ z in 𝓝 (Φ x), ∀ α β, g α β z = g β α z)
    (hinv : ∀ᶠ z in 𝓝 (Φ x), ∀ α γ, ∑ β, g α β z * ginv β γ z = if α = γ then 1 else 0)
    (hgi' : ∀ μ ν, ContDiffAt ℝ 1 (ginv' μ ν) x)
    (hinv' : ∀ᶠ y in 𝓝 x, ∀ μ κ,
      ∑ ν, inNewCoords Φ g μ ν y * ginv' ν κ y = if μ = κ then 1 else 0)
    (μ ν : Fin n) :
    ricci (christoffel (inNewCoords Φ g) ginv') μ ν x
      = ∑ α, ∑ β, jac Φ α μ x * jac Φ β ν x * ricci (christoffel g ginv) α β (Φ x) := by
  -- What holds near `Φ x` holds at `Φ y` for `y` near `x`.
  have hΦc : ContinuousAt Φ x := continuousAt_pi.2 fun α => (hΦ α).continuousAt
  have hΦ2ev : ∀ᶠ y in 𝓝 x, ∀ α, ContDiffAt ℝ 2 (fun z => Φ z α) y :=
    eventually_all.2 fun α =>
      (((hΦ α).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).eventually (by simp))
  have hgev : ∀ᶠ y in 𝓝 x, ∀ α β, DifferentiableAt ℝ (g α β) (Φ y) :=
    hΦc.eventually (eventually_all.2 fun α => eventually_all.2 fun β =>
      ((hg α β).eventually (by simp)).mono fun z hz => hz.differentiableAt (by simp))
  have hsymmev : ∀ᶠ y in 𝓝 x, ∀ α β, g α β (Φ y) = g β α (Φ y) := hΦc.eventually hsymm
  have hinvev : ∀ᶠ y in 𝓝 x, ∀ α γ,
      ∑ β, g α β (Φ y) * ginv β γ (Φ y) = if α = γ then 1 else 0 := hΦc.eventually hinv
  -- The law for connections holds near `x`.
  have hlaw : ∀ᶠ y in 𝓝 x, ∀ ε μ ν,
      ∑ κ, jac Φ ε κ y * christoffel (inNewCoords Φ g) ginv' κ μ ν y
        = slope μ (jac Φ ε ν) y
          + ∑ β, ∑ γ, jac Φ β μ y * christoffel g ginv ε β γ (Φ y) * jac Φ γ ν y := by
    filter_upwards [hΦ2ev, hgev, hsymmev, hinvev, hinv'] with y h1 h2 h3 h4 h5 ε μ ν
    exact christoffel_inNewCoords_at h1 h2 h3 h4 h5 ε μ ν
  -- Both connections can be differentiated, and both are symmetric.
  have hΓ' : ∀ a b c, DifferentiableAt ℝ (christoffel (inNewCoords Φ g) ginv' a b c) x :=
    fun a b c => differentiableAt_christoffel (contDiffAt_inNewCoords hΦ hg)
      (fun α β => (hgi' α β).differentiableAt (by simp)) a b c
  have hΓ : ∀ a b c, DifferentiableAt ℝ (christoffel g ginv a b c) (Φ x) :=
    fun a b c => differentiableAt_christoffel hg
      (fun α β => (hgi α β).differentiableAt (by simp)) a b c
  have hsymΓ : ∀ᶠ z in 𝓝 (Φ x), ∀ a b c,
      christoffel g ginv a b c z = christoffel g ginv a c b z :=
    hsymm.eventually_nhds.mono fun z hz a b c => christoffel_symm hz a b c
  have hsym' : ∀ᶠ y in 𝓝 x, ∀ α β, inNewCoords Φ g α β y = inNewCoords Φ g β α y :=
    hsymmev.mono fun y hy α β => inNewCoords_symm hy α β
  have hsymΓ' : ∀ᶠ y in 𝓝 x, ∀ a b c, christoffel (inNewCoords Φ g) ginv' a b c y
      = christoffel (inNewCoords Φ g) ginv' a c b y :=
    hsym'.eventually_nhds.mono fun y hy a b c => christoffel_symm hy a b c
  obtain ⟨K, hK⟩ := exists_inverse_jac (Φ := Φ) (g := g) (ginv' := ginv') hinv'.self_of_nhds
  exact ricci_of_law hΦ hΓ' hΓ hlaw hsymΓ' hsymΓ hK μ ν

/-- The same statement for whole tables: new curvature = `Jᵀ · old curvature · J`. -/
theorem ricciTab_inNewCoords (hΦ : ∀ α, ContDiffAt ℝ 3 (fun z => Φ z α) x)
    (hg : ∀ α β, ContDiffAt ℝ 2 (g α β) (Φ x)) (hgi : ∀ α β, ContDiffAt ℝ 1 (ginv α β) (Φ x))
    (hsymm : ∀ᶠ z in 𝓝 (Φ x), ∀ α β, g α β z = g β α z)
    (hinv : ∀ᶠ z in 𝓝 (Φ x), ∀ α γ, ∑ β, g α β z * ginv β γ z = if α = γ then 1 else 0)
    (hgi' : ∀ μ ν, ContDiffAt ℝ 1 (ginv' μ ν) x)
    (hinv' : ∀ᶠ y in 𝓝 x, ∀ μ κ,
      ∑ ν, inNewCoords Φ g μ ν y * ginv' ν κ y = if μ = κ then 1 else 0) :
    Matrix.of (fun μ ν => ricci (christoffel (inNewCoords Φ g) ginv') μ ν x)
      = (tab (jac Φ) x)ᵀ * Matrix.of (fun α β => ricci (christoffel g ginv) α β (Φ x))
        * tab (jac Φ) x := by
  ext μ ν
  rw [Matrix.of_apply, ricci_inNewCoords hΦ hg hgi hsymm hinv hgi' hinv' μ ν]
  simp only [tab, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => by ring

/-- **"Empty" does not depend on the coordinates.** A length measure written in new coordinates
makes space empty at a point exactly when it does so in the old coordinates. -/
theorem isRicciFlatAt_inNewCoords (hΦ : ∀ α, ContDiffAt ℝ 3 (fun z => Φ z α) x)
    (hg : ∀ α β, ContDiffAt ℝ 2 (g α β) (Φ x)) (hgi : ∀ α β, ContDiffAt ℝ 1 (ginv α β) (Φ x))
    (hsymm : ∀ᶠ z in 𝓝 (Φ x), ∀ α β, g α β z = g β α z)
    (hinv : ∀ᶠ z in 𝓝 (Φ x), ∀ α γ, ∑ β, g α β z * ginv β γ z = if α = γ then 1 else 0)
    (hgi' : ∀ μ ν, ContDiffAt ℝ 1 (ginv' μ ν) x)
    (hinv' : ∀ᶠ y in 𝓝 x, ∀ μ κ,
      ∑ ν, inNewCoords Φ g μ ν y * ginv' ν κ y = if μ = κ then 1 else 0) :
    IsRicciFlatAt (inNewCoords Φ g) ginv' x ↔ IsRicciFlatAt g ginv (Φ x) := by
  have htab := ricciTab_inNewCoords hΦ hg hgi hsymm hinv hgi' hinv'
  obtain ⟨K, hK⟩ := exists_inverse_jac (Φ := Φ) (g := g) (ginv' := ginv') hinv'.self_of_nhds
  have hKt : Kᵀ * (tab (jac Φ) x)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hK, Matrix.transpose_one]
  constructor
  · intro h α β
    have h0 : Matrix.of (fun μ ν => ricci (christoffel (inNewCoords Φ g) ginv') μ ν x) = 0 := by
      ext μ ν
      exact h μ ν
    have hR : Matrix.of (fun α β => ricci (christoffel g ginv) α β (Φ x)) = 0 := by
      have e : Matrix.of (fun α β => ricci (christoffel g ginv) α β (Φ x))
          = Kᵀ * ((tab (jac Φ) x)ᵀ * Matrix.of (fun α β => ricci (christoffel g ginv) α β (Φ x))
            * tab (jac Φ) x) * K := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, hK, Matrix.mul_one, ← Matrix.mul_assoc, hKt,
          Matrix.one_mul]
      rw [e, ← htab, h0, Matrix.mul_zero, Matrix.zero_mul]
    exact congrFun (congrFun hR α) β
  · intro h μ ν
    rw [ricci_inNewCoords hΦ hg hgi hsymm hinv hgi' hinv' μ ν]
    exact Finset.sum_eq_zero fun α _ => Finset.sum_eq_zero fun β _ => by rw [h α β, mul_zero]

end Main

end GravityInLean
