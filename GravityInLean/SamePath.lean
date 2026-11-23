/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.NewCoordinates
public import Mathlib.Analysis.Calculus.Deriv.Prod

import Mathlib.Tactic

/-!
# Free fall does not depend on the coordinates

`Curvature.lean` defines free fall by the classic equation in coordinates, and "the path is timed
by its own clock" by a formula in coordinates. This file shows that neither depends on the
coordinates.

A path `γ` is given in the new coordinates. The same path in the old coordinates is
`fun s => Φ (γ s)`.

**What is proved here.**

* `freeFallExpr_inNewCoords`: the left-hand side of the free-fall equation, computed for the path
  in the old coordinates, is the one computed in the new coordinates, multiplied by the table of
  slopes of the change of coordinates. The extra term in the law for the connection
  (`christoffel_inNewCoords_at`) is exactly what cancels the extra term that the bending of the
  path picks up.
* `isFreeFallAt_inNewCoords`: so a path falls freely in the new coordinates exactly when it does
  in the old ones.
* `keepsOwnTimeAt_inNewCoords`: and it is timed by its own clock in the new coordinates exactly
  when it is in the old ones.

**What is assumed.** The change of coordinates and the path are twice smoothly differentiable; the
length measure can be differentiated, is symmetric and has an inverse at the point, before and
after the change. A worked case is in `SameSpacetime.lean`.
-/

@[expose] public section

namespace GravityInLean

open Filter Topology Matrix

variable {n : ℕ}

/-! ## The chain rule along a path -/

/-- **The chain rule along a path.** How fast `F` changes along the path `γ`: for each coordinate,
the slope of `F` along it times how fast the path moves along it. -/
theorem hasDerivAt_along_path {F : Coords n → ℝ} {γ : ℝ → Coords n} {τ : ℝ}
    (hF : DifferentiableAt ℝ F (γ τ)) (hγ : ∀ μ, DifferentiableAt ℝ (fun s => γ s μ) τ) :
    HasDerivAt (fun s => F (γ s)) (∑ μ, slope μ F (γ τ) * deriv (fun s => γ s μ) τ) τ := by
  have hγ' : HasDerivAt γ (fun μ => deriv (fun s => γ s μ) τ) τ :=
    hasDerivAt_pi.2 fun μ => (hγ μ).hasDerivAt
  have h : HasDerivAt (fun s => F (γ s))
      (fderiv ℝ F (γ τ) (fun μ => deriv (fun s => γ s μ) τ)) τ :=
    HasFDerivAt.comp_hasDerivAt (l := F) (f := γ) (x := τ) hF.hasFDerivAt hγ'
  have e : fderiv ℝ F (γ τ) (fun μ => deriv (fun s => γ s μ) τ)
      = ∑ μ, slope μ F (γ τ) * deriv (fun s => γ s μ) τ := by
    rw [clm_apply_eq_sum]
    exact Finset.sum_congr rfl fun μ _ => by rw [slope_eq_fderiv hF, mul_comm]
  rw [← e]
  exact h

/-- The slope of a twice smoothly differentiable function of one number can itself be
differentiated. -/
theorem differentiableAt_deriv_of_contDiffAt {f : ℝ → ℝ} {τ : ℝ} (hf : ContDiffAt ℝ 2 f τ) :
    DifferentiableAt ℝ (deriv f) τ := by
  have h1 : DifferentiableAt ℝ (fun s => fderiv ℝ f s 1) τ :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)).clm_apply
      (differentiableAt_const _)
  exact h1

section Path

variable {Φ : Coords n → Coords n} {g ginv ginv' : Fin n → Fin n → Coords n → ℝ}
  {γ : ℝ → Coords n} {τ : ℝ}

/-- How fast the path moves in the old coordinates: the table of slopes of the change of
coordinates, applied to how fast it moves in the new ones. -/
theorem deriv_comp_path (hΦ : ∀ α, DifferentiableAt ℝ (fun z => Φ z α) (γ τ))
    (hγ : ∀ μ, DifferentiableAt ℝ (fun s => γ s μ) τ) (α : Fin n) :
    deriv (fun s => Φ (γ s) α) τ = ∑ μ, jac Φ α μ (γ τ) * deriv (fun s => γ s μ) τ :=
  (hasDerivAt_along_path (F := fun z => Φ z α) (hΦ α) hγ).deriv

/-- How the path bends in the old coordinates. Two parts: the change of coordinates is itself
bent (its second slopes), and the path bends in the new coordinates. -/
theorem deriv_deriv_comp_path (hΦ : ∀ α, ContDiffAt ℝ 2 (fun z => Φ z α) (γ τ))
    (hγ : ∀ μ, ContDiffAt ℝ 2 (fun s => γ s μ) τ) (α : Fin n) :
    deriv (deriv fun s => Φ (γ s) α) τ
      = ∑ μ, ((∑ ν, slope ν (jac Φ α μ) (γ τ) * deriv (fun s => γ s ν) τ)
            * deriv (fun s => γ s μ) τ
          + jac Φ α μ (γ τ) * deriv (deriv fun s => γ s μ) τ) := by
  have hγc : ContinuousAt γ τ := continuousAt_pi.2 fun μ => (hγ μ).continuousAt
  have hγd : ∀ μ, DifferentiableAt ℝ (fun s => γ s μ) τ := fun μ =>
    (hγ μ).differentiableAt (by simp)
  -- Near `τ`, the speed in the old coordinates is given by the chain rule.
  have hev : (deriv fun s => Φ (γ s) α)
      =ᶠ[𝓝 τ] fun s => ∑ μ, jac Φ α μ (γ s) * deriv (fun u => γ u μ) s := by
    have h1 : ∀ᶠ s in 𝓝 τ, ∀ β, DifferentiableAt ℝ (fun z => Φ z β) (γ s) :=
      hγc.eventually (eventually_all.2 fun β =>
        ((hΦ β).eventually (by simp)).mono fun z hz => hz.differentiableAt (by simp))
    have h2 : ∀ᶠ s in 𝓝 τ, ∀ μ, DifferentiableAt ℝ (fun u => γ u μ) s :=
      eventually_all.2 fun μ =>
        ((hγ μ).eventually (by simp)).mono fun s hs => hs.differentiableAt (by simp)
    filter_upwards [h1, h2] with s hs1 hs2
    exact deriv_comp_path hs1 hs2 α
  rw [hev.deriv_eq]
  have hJ : ∀ μ, DifferentiableAt ℝ (jac Φ α μ) (γ τ) := fun μ =>
    (contDiffAt_slope (m := 1) (hΦ α) (by simp) (by simp) (by norm_num) μ).differentiableAt
      (by simp)
  have hterm : ∀ μ, HasDerivAt (fun s => jac Φ α μ (γ s) * deriv (fun u => γ u μ) s)
      ((∑ ν, slope ν (jac Φ α μ) (γ τ) * deriv (fun s => γ s ν) τ) * deriv (fun s => γ s μ) τ
        + jac Φ α μ (γ τ) * deriv (deriv fun s => γ s μ) τ) τ := fun μ =>
    (hasDerivAt_along_path (hJ μ) hγd).mul
      (differentiableAt_deriv_of_contDiffAt (hγ μ)).hasDerivAt
  exact (HasDerivAt.fun_sum fun μ _ => hterm μ).deriv

end Path

/-! ## The algebra -/

/-- The algebra behind the theorem, for tables of plain numbers: `J` the slopes of the change of
coordinates, `h` its second slopes, `Γ` and `Γ'` the old and the new connection, `v` how fast the
path moves in the new coordinates and `a` how it bends there. `law` is the law for the
connection. -/
theorem freeFall_algebra {J : Fin n → Fin n → ℝ} {h Γ Γ' : Fin n → Fin n → Fin n → ℝ}
    {v a : Fin n → ℝ}
    (law : ∀ ε μ ν, ∑ κ, J ε κ * Γ' κ μ ν = h ε μ ν + ∑ β, ∑ γ, J β μ * Γ ε β γ * J γ ν)
    (ε : Fin n) :
    (∑ μ, ((∑ ν, h ε ν μ * v ν) * v μ + J ε μ * a μ))
        + ∑ β, ∑ γ, Γ ε β γ * (∑ μ, J β μ * v μ) * (∑ ν, J γ ν * v ν)
      = ∑ κ, J ε κ * (a κ + ∑ μ, ∑ ν, Γ' κ μ ν * v μ * v ν) := by
  have l1 : ∑ μ, ((∑ ν, h ε ν μ * v ν) * v μ + J ε μ * a μ)
      = (∑ μ, ∑ ν, h ε μ ν * v μ * v ν) + ∑ κ, J ε κ * a κ := by
    rw [Finset.sum_add_distrib]
    congr 1
    calc ∑ μ, (∑ ν, h ε ν μ * v ν) * v μ = ∑ μ, ∑ ν, h ε ν μ * v ν * v μ :=
          Finset.sum_congr rfl fun μ _ => Finset.sum_mul _ _ _
      _ = ∑ ν, ∑ μ, h ε ν μ * v ν * v μ := Finset.sum_comm
  have l2 : ∑ β, ∑ γ, Γ ε β γ * (∑ μ, J β μ * v μ) * (∑ ν, J γ ν * v ν)
      = ∑ μ, ∑ ν, (∑ β, ∑ γ, J β μ * Γ ε β γ * J γ ν) * v μ * v ν := by
    have e1 : ∑ β, ∑ γ, Γ ε β γ * (∑ μ, J β μ * v μ) * (∑ ν, J γ ν * v ν)
        = ∑ β, ∑ γ, ∑ μ, ∑ ν, Γ ε β γ * (J β μ * v μ) * (J γ ν * v ν) := by
      refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun γ _ => ?_
      rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun ν _ => by ring
    have e2 : ∑ μ, ∑ ν, (∑ β, ∑ γ, J β μ * Γ ε β γ * J γ ν) * v μ * v ν
        = ∑ μ, ∑ ν, ∑ β, ∑ γ, J β μ * Γ ε β γ * J γ ν * v μ * v ν := by
      simp only [Finset.sum_mul]
    rw [e1, e2, sum4_swap]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
      Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun γ _ => by ring
  have r1 : ∑ κ, J ε κ * (a κ + ∑ μ, ∑ ν, Γ' κ μ ν * v μ * v ν)
      = (∑ κ, J ε κ * a κ) + ∑ μ, ∑ ν, (∑ κ, J ε κ * Γ' κ μ ν) * v μ * v ν := by
    have e1 : ∑ κ, J ε κ * (a κ + ∑ μ, ∑ ν, Γ' κ μ ν * v μ * v ν)
        = (∑ κ, J ε κ * a κ) + ∑ κ, ∑ μ, ∑ ν, J ε κ * (Γ' κ μ ν * v μ * v ν) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    have e2 : ∑ μ, ∑ ν, (∑ κ, J ε κ * Γ' κ μ ν) * v μ * v ν
        = ∑ μ, ∑ ν, ∑ κ, J ε κ * (Γ' κ μ ν * v μ * v ν) := by
      refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun κ _ => by ring
    rw [e1, e2]
    congr 1
    exact (sum3_rotate (fun μ ν κ => J ε κ * (Γ' κ μ ν * v μ * v ν))).symm
  rw [l1, l2, r1]
  simp only [law, add_mul, Finset.sum_add_distrib]
  ring

/-! ## Free fall, and a path's own time -/

section Main

variable {Φ : Coords n → Coords n} {g ginv ginv' : Fin n → Fin n → Coords n → ℝ}
  {γ : ℝ → Coords n} {τ : ℝ}

/-- **The free-fall equation in two sets of coordinates.** The left-hand side of the free-fall
equation for the path in the old coordinates is the one for the path in the new coordinates,
multiplied by the table of slopes of the change of coordinates. -/
theorem freeFallExpr_inNewCoords (hΦ : ∀ α, ContDiffAt ℝ 2 (fun z => Φ z α) (γ τ))
    (hγ : ∀ μ, ContDiffAt ℝ 2 (fun s => γ s μ) τ)
    (hg : ∀ α β, DifferentiableAt ℝ (g α β) (Φ (γ τ)))
    (hsymm : ∀ α β, g α β (Φ (γ τ)) = g β α (Φ (γ τ)))
    (hinv : ∀ α δ, ∑ β, g α β (Φ (γ τ)) * ginv β δ (Φ (γ τ)) = if α = δ then 1 else 0)
    (hinv' : ∀ μ κ,
      ∑ ν, inNewCoords Φ g μ ν (γ τ) * ginv' ν κ (γ τ) = if μ = κ then 1 else 0)
    (ε : Fin n) :
    freeFallExpr (christoffel g ginv) (fun s => Φ (γ s)) τ ε
      = ∑ κ, jac Φ ε κ (γ τ) * freeFallExpr (christoffel (inNewCoords Φ g) ginv') γ τ κ := by
  have law := christoffel_inNewCoords_at hΦ hg hsymm hinv hinv'
  have hΦd : ∀ α, DifferentiableAt ℝ (fun z => Φ z α) (γ τ) := fun α =>
    (hΦ α).differentiableAt (by simp)
  have hγd : ∀ μ, DifferentiableAt ℝ (fun s => γ s μ) τ := fun μ =>
    (hγ μ).differentiableAt (by simp)
  simp only [freeFallExpr]
  rw [deriv_deriv_comp_path hΦ hγ ε]
  simp only [deriv_comp_path hΦd hγd]
  exact freeFall_algebra (J := fun α μ => jac Φ α μ (γ τ))
    (h := fun α μ ν => slope μ (jac Φ α ν) (γ τ))
    (Γ := fun α β δ => christoffel g ginv α β δ (Φ (γ τ)))
    (Γ' := fun κ μ ν => christoffel (inNewCoords Φ g) ginv' κ μ ν (γ τ))
    (v := fun μ => deriv (fun s => γ s μ) τ) (a := fun μ => deriv (deriv fun s => γ s μ) τ)
    law ε

/-- **Free fall does not depend on the coordinates.** A path falls freely in the new coordinates
exactly when the same path falls freely in the old ones. -/
theorem isFreeFallAt_inNewCoords (hΦ : ∀ α, ContDiffAt ℝ 2 (fun z => Φ z α) (γ τ))
    (hγ : ∀ μ, ContDiffAt ℝ 2 (fun s => γ s μ) τ)
    (hg : ∀ α β, DifferentiableAt ℝ (g α β) (Φ (γ τ)))
    (hsymm : ∀ α β, g α β (Φ (γ τ)) = g β α (Φ (γ τ)))
    (hinv : ∀ α δ, ∑ β, g α β (Φ (γ τ)) * ginv β δ (Φ (γ τ)) = if α = δ then 1 else 0)
    (hinv' : ∀ μ κ,
      ∑ ν, inNewCoords Φ g μ ν (γ τ) * ginv' ν κ (γ τ) = if μ = κ then 1 else 0) :
    IsFreeFallAt (christoffel (inNewCoords Φ g) ginv') γ τ
      ↔ IsFreeFallAt (christoffel g ginv) (fun s => Φ (γ s)) τ := by
  obtain ⟨K, hK⟩ := exists_inverse_jac (Φ := Φ) (g := g) (ginv' := ginv') hinv'
  have hK' : K * tab (jac Φ) (γ τ) = 1 := mul_eq_one_comm.mp hK
  have key := freeFallExpr_inNewCoords hΦ hγ hg hsymm hinv hinv'
  constructor
  · intro h ε
    rw [key ε]
    exact Finset.sum_eq_zero fun κ _ => by rw [h κ, mul_zero]
  · intro h
    have hJe : tab (jac Φ) (γ τ)
        *ᵥ (fun κ => freeFallExpr (christoffel (inNewCoords Φ g) ginv') γ τ κ) = 0 := by
      funext ε
      have h1 := key ε
      rw [h ε] at h1
      exact h1.symm
    have h2 := congrArg (fun w => K *ᵥ w) hJe
    simp only [Matrix.mulVec_mulVec, hK', Matrix.one_mulVec, Matrix.mulVec_zero] at h2
    exact fun κ => congrFun h2 κ

/-- **A path's own time does not depend on the coordinates.** A path is timed by its own clock in
the new coordinates exactly when it is in the old ones. -/
theorem keepsOwnTimeAt_inNewCoords (hΦ : ∀ α, DifferentiableAt ℝ (fun z => Φ z α) (γ τ))
    (hγ : ∀ μ, DifferentiableAt ℝ (fun s => γ s μ) τ) :
    KeepsOwnTimeAt (inNewCoords Φ g) γ τ ↔ KeepsOwnTimeAt g (fun s => Φ (γ s)) τ := by
  have e := length_inNewCoords Φ g (γ τ) (fun μ => deriv (fun s => γ s μ) τ)
  simp only [← deriv_comp_path hΦ hγ] at e
  simp only [KeepsOwnTimeAt]
  rw [e]

end Main

end GravityInLean
