/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.TableHess

import Mathlib.Tactic

/-!
# A map that carries one table to another carries slopes and second slopes of functions

Take a map `f` of coordinate space that, near a point `x`, carries the table `g` to the table
`h`: lengths measured with `g` are the lengths measured with `h` of the steps as `f` carries
them (`CarriesTableAt`). Then:

* near `x`, the table `h` written in new coordinates through `f` is the table `g`
  (`CarriesTableAt.inNewCoords_eq`), so `f` loses no direction (`jac_isUnit_of_carries`) and the
  connections of `g` and `h` are tied by the law for a change of coordinates
  (`christoffel_law_of_carries`);
* the squared length of the slope of a function `F` at `f x`, measured with `h`, is that of
  `F` after `f` at `x`, measured with `g` (`gradSq_of_carries`);
* the second slope (Hessian) of `F` after `f` that belongs to `g` is the second slope of `F`
  that belongs to `h`, both slots multiplied by the slopes of `f` (`hessT_of_carries`).
-/

@[expose] public section

namespace GravityInLean.Curved

open Filter Topology Matrix

open scoped ContDiff

variable {n : ℕ} {g ginv h hinv : Fin n → Fin n → Coords n → ℝ} {s t : Set (Coords n)}
  {f : Coords n → Coords n} {x : Coords n} {F : Coords n → ℝ}

/-! ## The shared first step: `h` in new coordinates is `g` -/

/-- A map that carries a table near `x` can be differentiated at every point near `x`. -/
theorem CarriesTableAt.eventually_differentiableAt (hf : CarriesTableAt g h f x) :
    ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
  ((hf.1.of_le (by simp) : ContDiffAt ℝ 1 f x).eventually (by simp)).mono fun _ hy ↦
    hy.differentiableAt (by simp)

/-- Each part of a map that carries a table is as smooth as one likes at `x`. -/
theorem CarriesTableAt.contDiffAt_part (hf : CarriesTableAt g h f x) {k : WithTop ℕ∞}
    (hk : k ≤ ∞) (α : Fin n) : ContDiffAt ℝ k (fun z ↦ f z α) x :=
  (contDiffAt_pi.1 hf.1 α).of_le hk

/-- **Near `x`, the table `h` written in new coordinates through `f` is the table `g`.** -/
theorem CarriesTableAt.inNewCoords_eq (hf : CarriesTableAt g h f x) :
    ∀ᶠ y in 𝓝 x, ∀ a b, inNewCoords f h a b y = g a b y := by
  filter_upwards [hf.2, hf.eventually_differentiableAt] with y hy hdy a b
  have key : formOf (fun α β ↦ h α β (f y)) (fderiv ℝ f y (Pi.single a 1))
      (fderiv ℝ f y (Pi.single b 1)) = formOf (fun α β ↦ g α β y) (Pi.single a 1)
        (Pi.single b 1) := hy _ _
  rw [formOf_single_single, formOf_apply] at key
  rw [← key]
  change ∑ α, ∑ β, jac f α a y * jac f β b y * h α β (f y) = _
  refine Finset.sum_congr rfl fun α _ ↦ Finset.sum_congr rfl fun β _ ↦ ?_
  rw [jac_eq_fderiv hdy, jac_eq_fderiv hdy]
  ring

/-- At `x`, the inverse table of `g` is an inverse of `h` written in new coordinates. -/
theorem CarriesTableAt.inNewCoords_inverse (hg : IsRegularTableOn g ginv s) (hx : x ∈ s)
    (hf : CarriesTableAt g h f x) (μ κ : Fin n) :
    ∑ ν, inNewCoords f h μ ν x * ginv ν κ x = if μ = κ then 1 else 0 := by
  rw [← hg.inverse x hx μ κ]
  exact Finset.sum_congr rfl fun ν _ ↦ by rw [hf.inNewCoords_eq.self_of_nhds μ ν]

/-- **The slopes of a map that carries a table lose no direction.** -/
theorem jac_isUnit_of_carries (hg : IsRegularTableOn g ginv s) (hx : x ∈ s)
    (hf : CarriesTableAt g h f x) : IsUnit (tab (jac f) x) := by
  obtain ⟨K, hK⟩ := exists_inverse_jac (Φ := f) (g := h) (ginv' := ginv) (x := x)
    (hf.inNewCoords_inverse hg hx)
  exact (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_ne_zero.2 (Matrix.det_ne_zero_of_right_inverse hK))

/-- At `x`, the connection of `h` written in new coordinates is the connection of `g`. -/
theorem christoffel_inNewCoords_of_carries (hf : CarriesTableAt g h f x) (a b c : Fin n) :
    christoffel (inNewCoords f h) ginv a b c x = christoffel g ginv a b c x := by
  have hev : ∀ α β, inNewCoords f h α β =ᶠ[𝓝 x] g α β := fun α β ↦
    hf.inNewCoords_eq.mono fun y hy ↦ hy α β
  simp only [christoffel]
  congr 1
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [slope_congr (hev d c) b, slope_congr (hev d b) c, slope_congr (hev b c) d]

/-- **The law that ties the two connections.** The connection of `g`, multiplied by the slopes
of `f`, is the second slopes of `f` plus the connection of `h` at `f x`, its two lower slots
multiplied by the slopes of `f`. -/
theorem christoffel_law_of_carries (hg : IsRegularTableOn g ginv s)
    (hh : IsRegularTableOn h hinv t) (hx : x ∈ s) (hfx : f x ∈ t)
    (hf : CarriesTableAt g h f x) (ε μ ν : Fin n) :
    ∑ κ, jac f ε κ x * christoffel g ginv κ μ ν x
      = slope μ (jac f ε ν) x
        + ∑ β, ∑ γ, jac f β μ x * christoffel h hinv ε β γ (f x) * jac f γ ν x := by
  rw [← christoffel_inNewCoords_at (ginv' := ginv) (hf.contDiffAt_part (by simp))
    (fun α β ↦ hh.differentiableAt hfx α β) (hh.symm (f x) hfx) (hh.inverse (f x) hfx)
    (hf.inNewCoords_inverse hg hx) ε μ ν]
  exact Finset.sum_congr rfl fun κ _ ↦ by rw [christoffel_inNewCoords_of_carries hf]

/-! ## The squared length of a slope -/

/-- A sum over two indices of a table against one list of numbers twice, in the language of
tables. -/
theorem sum_table_eq_dotProduct (T : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) :
    ∑ a, ∑ b, T a b * w a * w b = w ⬝ᵥ (T *ᵥ w) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring

/-- The inverse table of `h` at `f x` is the inverse table of `g` at `x`, both slots multiplied
by the slopes of `f`. -/
theorem tab_inverse_of_carries (hg : IsRegularTableOn g ginv s)
    (hh : IsRegularTableOn h hinv t) (hx : x ∈ s) (hfx : f x ∈ t)
    (hf : CarriesTableAt g h f x) :
    tab (jac f) x * tab ginv x * (tab (jac f) x)ᵀ = tab hinv (f x) := by
  have m1 : tab h (f x) * tab hinv (f x) = 1 := by
    ext α γ
    simp only [tab, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    exact hh.inverse (f x) hfx α γ
  have m2 : (tab (jac f) x)ᵀ * tab h (f x) * (tab (jac f) x * tab ginv x) = 1 := by
    rw [← Matrix.mul_assoc, ← tab_inNewCoords]
    ext α γ
    simp only [tab, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    exact hf.inNewCoords_inverse hg hx α γ
  have m3 : tab (jac f) x * tab ginv x * ((tab (jac f) x)ᵀ * tab h (f x)) = 1 :=
    mul_eq_one_comm.mp m2
  calc tab (jac f) x * tab ginv x * (tab (jac f) x)ᵀ
      = tab (jac f) x * tab ginv x * (tab (jac f) x)ᵀ * (tab h (f x) * tab hinv (f x)) := by
        rw [m1, Matrix.mul_one]
    _ = tab (jac f) x * tab ginv x * ((tab (jac f) x)ᵀ * tab h (f x)) * tab hinv (f x) := by
        simp only [Matrix.mul_assoc]
    _ = tab hinv (f x) := by rw [m3, Matrix.one_mul]

/-- **The squared length of the slope is carried.** The slope of `F` after `f` at `x`, measured
with `g`, is as long as the slope of `F` at `f x`, measured with `h`. -/
theorem gradSq_of_carries (hg : IsRegularTableOn g ginv s) (hh : IsRegularTableOn h hinv t)
    (hx : x ∈ s) (hfx : f x ∈ t) (hf : CarriesTableAt g h f x) (hF : ContDiffAt ℝ ∞ F (f x)) :
    gradSq ginv (fun y ↦ F (f y)) x = gradSq hinv F (f x) := by
  have hFd : DifferentiableAt ℝ F (f x) := hF.differentiableAt (by simp)
  have hfd : DifferentiableAt ℝ f x := hf.1.differentiableAt (by simp)
  have hsl : ∀ a, slope a (fun y ↦ F (f y)) x
      = ((tab (jac f) x)ᵀ *ᵥ fun δ ↦ slope δ F (f x)) a := fun a ↦ by
    rw [slope_comp hFd hfd]
    rfl
  have e1 : gradSq ginv (fun y ↦ F (f y)) x
      = ∑ a, ∑ b, tab ginv x a b * ((tab (jac f) x)ᵀ *ᵥ fun δ ↦ slope δ F (f x)) a
          * ((tab (jac f) x)ᵀ *ᵥ fun δ ↦ slope δ F (f x)) b :=
    Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by
      rw [hsl a, hsl b]
      rfl
  have e2 : gradSq hinv F (f x)
      = ∑ a, ∑ b, tab hinv (f x) a b * slope a F (f x) * slope b F (f x) := rfl
  rw [e1, e2, sum_table_eq_dotProduct, sum_table_eq_dotProduct,
    ← tab_inverse_of_carries hg hh hx hfx hf, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec]

/-! ## The second slope -/

/-- The algebra behind `hessT_of_carries`, for tables of plain numbers: the second slopes of
`f` (`dJ`) cancel. -/
theorem hess_algebra (Ji Jj dJ dF : Fin n → ℝ) (ddF : Fin n → Fin n → ℝ)
    (Γ : Fin n → Fin n → Fin n → ℝ) :
    ∑ δ, (dJ δ * dF δ + Jj δ * ∑ ε, Ji ε * ddF ε δ)
        - ∑ ε, (dJ ε + ∑ β, ∑ γ, Ji β * Γ ε β γ * Jj γ) * dF ε
      = ∑ a, ∑ b, Ji a * Jj b * (ddF a b - ∑ c, Γ c a b * dF c) := by
  have e1 : ∑ δ, (dJ δ * dF δ + Jj δ * ∑ ε, Ji ε * ddF ε δ)
      = ∑ δ, dJ δ * dF δ + ∑ a, ∑ b, Ji a * Jj b * ddF a b := by
    rw [Finset.sum_add_distrib, Finset.sum_comm (f := fun a b ↦ Ji a * Jj b * ddF a b)]
    congr 1
    refine Finset.sum_congr rfl fun δ _ ↦ ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ε _ ↦ by ring
  have e2 : ∑ ε, (dJ ε + ∑ β, ∑ γ, Ji β * Γ ε β γ * Jj γ) * dF ε
      = ∑ δ, dJ δ * dF δ + ∑ a, ∑ b, ∑ c, Ji a * Jj b * (Γ c a b * dF c) := by
    rw [sum3_rotate (fun a b c ↦ Ji a * Jj b * (Γ c a b * dF c)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ε _ ↦ ?_
    rw [add_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun β _ ↦ ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun γ _ ↦ by ring
  have e3 : ∑ a, ∑ b, Ji a * Jj b * (ddF a b - ∑ c, Γ c a b * dF c)
      = ∑ a, ∑ b, Ji a * Jj b * ddF a b
        - ∑ a, ∑ b, ∑ c, Ji a * Jj b * (Γ c a b * dF c) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [mul_sub, Finset.mul_sum]
  rw [e1, e2, e3]
  ring

/-- **The second slope is carried.** The second slope (Hessian) of `F` after `f` at `x` that
belongs to `g` is the second slope of `F` at `f x` that belongs to `h`, both slots multiplied
by the slopes of `f`. -/
theorem hessT_of_carries (hg : IsRegularTableOn g ginv s) (hh : IsRegularTableOn h hinv t)
    (hx : x ∈ s) (hfx : f x ∈ t) (hf : CarriesTableAt g h f x) (hF : ContDiffAt ℝ ∞ F (f x))
    (i j : Fin n) :
    hessT g ginv (fun y ↦ F (f y)) i j x
      = ∑ a, ∑ b, jac f a i x * jac f b j x * hessT h hinv F a b (f x) := by
  have hFd : DifferentiableAt ℝ F (f x) := hF.differentiableAt (by simp)
  have hfd : DifferentiableAt ℝ f x := hf.1.differentiableAt (by simp)
  -- near `x`, the slope of `F` after `f` is given by the chain rule
  have hFev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ F (f y) :=
    hf.1.continuousAt.eventually
      (((hF.of_le (by simp) : ContDiffAt ℝ 1 F (f x)).eventually (by simp)).mono fun _ hz ↦
        hz.differentiableAt (by simp))
  have hev : slope j (fun y ↦ F (f y))
      =ᶠ[𝓝 x] fun y ↦ ∑ δ, jac f δ j y * slope δ F (f y) := by
    filter_upwards [hFev, hf.eventually_differentiableAt] with y hFy hfy
    exact slope_comp hFy hfy j
  -- the pieces can be differentiated at `x`
  have hJ : ∀ δ, DifferentiableAt ℝ (jac f δ j) x := fun δ ↦
    (contDiffAt_slope (m := 1) (hf.contDiffAt_part (k := 2) (by simp) δ) (by simp) (by simp)
      (by norm_num) j).differentiableAt (by simp)
  have hdF : ∀ δ, DifferentiableAt ℝ (slope δ F) (f x) := fun δ ↦
    (contDiffAt_slope (m := 1) (hF.of_le (by simp) : ContDiffAt ℝ 2 F (f x)) (by simp) (by simp)
      (by norm_num) δ).differentiableAt (by simp)
  have hdFf : ∀ δ, DifferentiableAt ℝ (fun y ↦ slope δ F (f y)) x := fun δ ↦
    (hdF δ).comp x hfd
  -- the plain second slope of `F` after `f`
  have hA : slope i (slope j (fun y ↦ F (f y))) x
      = ∑ δ, (slope i (jac f δ j) x * slope δ F (f x)
          + jac f δ j x * ∑ ε, jac f ε i x * slope ε (slope δ F) (f x)) := by
    have hprod : ∀ δ, DifferentiableAt ℝ (fun y ↦ jac f δ j y * slope δ F (f y)) x :=
      fun δ ↦ (hJ δ).mul (hdFf δ)
    have hm : ∀ δ, slope i (fun y ↦ jac f δ j y * slope δ F (f y)) x
        = slope i (jac f δ j) x * slope δ F (f x)
          + jac f δ j x * slope i (fun y ↦ slope δ F (f y)) x :=
      fun δ ↦ slope_mul (hJ δ) (hdFf δ) i
    rw [slope_congr hev i, slope_sum hprod]
    refine Finset.sum_congr rfl fun δ _ ↦ ?_
    rw [hm δ, slope_comp (hdF δ) hfd]
  -- the correction by the connection of `g`, through the law for the two connections
  have hB : ∑ c, christoffel g ginv c i j x * slope c (fun y ↦ F (f y)) x
      = ∑ ε, (slope i (jac f ε j) x
          + ∑ β, ∑ γ, jac f β i x * christoffel h hinv ε β γ (f x) * jac f γ j x)
          * slope ε F (f x) := by
    have e : ∑ c, christoffel g ginv c i j x * slope c (fun y ↦ F (f y)) x
        = ∑ ε, (∑ κ, jac f ε κ x * christoffel g ginv κ i j x) * slope ε F (f x) := by
      have e' : ∀ c, christoffel g ginv c i j x * slope c (fun y ↦ F (f y)) x
          = ∑ ε, jac f ε c x * christoffel g ginv c i j x * slope ε F (f x) := fun c ↦ by
        rw [slope_comp hFd hfd, Finset.mul_sum]
        exact Finset.sum_congr rfl fun ε _ ↦ by ring
      rw [Finset.sum_congr rfl fun c _ ↦ e' c, Finset.sum_comm]
      exact Finset.sum_congr rfl fun ε _ ↦ by rw [Finset.sum_mul]
    rw [e]
    exact Finset.sum_congr rfl fun ε _ ↦ by
      rw [christoffel_law_of_carries hg hh hx hfx hf]
  change slope i (slope j (fun y ↦ F (f y))) x
      - ∑ c, christoffel g ginv c i j x * slope c (fun y ↦ F (f y)) x
    = ∑ a, ∑ b, jac f a i x * jac f b j x
        * (slope a (slope b F) (f x) - ∑ c, christoffel h hinv c a b (f x) * slope c F (f x))
  rw [hA, hB]
  exact hess_algebra (fun a ↦ jac f a i x) (fun b ↦ jac f b j x)
    (fun δ ↦ slope i (jac f δ j) x) (fun c ↦ slope c F (f x))
    (fun a b ↦ slope a (slope b F) (f x)) (fun c a b ↦ christoffel h hinv c a b (f x))

end GravityInLean.Curved
