/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Curvature
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Operations

import Mathlib.Tactic

/-!
# Rules for slopes

`Curvature.lean` defines `slope i f x`: how fast `f` changes at `x` when only coordinate `i`
moves. This file collects the rules for computing with slopes, for functions of any number of
coordinates.

* `slope_add`, `slope_sub`, `slope_mul`, `slope_sum`: slopes of sums and products.
* `jac Φ α μ`: for a change of coordinates `Φ`, how fast the old coordinate `α` changes when the
  new coordinate `μ` moves (the Jacobian table of the textbooks).
* `slope_comp`: the chain rule. The slope of `F(Φ(x))` along a new coordinate is the sum, over
  the old coordinates, of "how fast that old coordinate moves" times "the slope of `F` along it".
* `slope_slope_comm`: for a twice smoothly differentiable function the order of two slopes does
  not matter.
* `contDiffAt_slope`: a slope of a smooth function is smooth, one level less.
* `slope_congr`: a slope only looks at the function near the point.

All of them translate facts of the standard library (the derivative of a function of several
variables) into the language of slopes used in this project.
-/

@[expose] public section

namespace GravityInLean

open Filter Topology

open scoped ContDiff

variable {n : ℕ}

/-! ## A slope is the full derivative, applied to a basic step -/

/-- Along the coordinate line `i` through `x`, a differentiable function changes at the rate its
full derivative gives for the basic step along `i`. -/
theorem hasDerivAt_line {f : Coords n → ℝ} {x : Coords n} (hf : DifferentiableAt ℝ f x)
    (i : Fin n) :
    HasDerivAt (fun s => f (Function.update x i s)) (fderiv ℝ f x (Pi.single i 1)) (x i) := by
  have h1 : HasDerivAt (Function.update x i) (Pi.single i (1 : ℝ)) (x i) :=
    hasDerivAt_update x i (x i)
  have h2 : HasFDerivAt f (fderiv ℝ f x) (Function.update x i (x i)) := by
    rw [Function.update_eq_self]
    exact hf.hasFDerivAt
  exact HasFDerivAt.comp_hasDerivAt (l := f) (f := Function.update x i) (x := x i) h2 h1

/-- A function that can be differentiated at a point can be differentiated along each coordinate
line through it. -/
theorem differentiableAt_line {f : Coords n → ℝ} {x : Coords n} (hf : DifferentiableAt ℝ f x)
    (k : Fin n) : DifferentiableAt ℝ (fun s => f (Function.update x k s)) (x k) :=
  (hasDerivAt_line hf k).differentiableAt

theorem slope_eq_fderiv {f : Coords n → ℝ} {x : Coords n} (hf : DifferentiableAt ℝ f x)
    (i : Fin n) : slope i f x = fderiv ℝ f x (Pi.single i 1) :=
  (hasDerivAt_line hf i).deriv

/-- Along the coordinate line `i` through `x`, a differentiable function has the slope
`slope i f x`. -/
theorem hasDerivAt_slope {f : Coords n → ℝ} {x : Coords n} (hf : DifferentiableAt ℝ f x)
    (i : Fin n) : HasDerivAt (fun s => f (Function.update x i s)) (slope i f x) (x i) :=
  (differentiableAt_line hf i).hasDerivAt

/-- Two functions that agree near `x` have the same slopes at `x`. -/
theorem slope_congr {f f' : Coords n → ℝ} {x : Coords n} (h : f =ᶠ[𝓝 x] f') (i : Fin n) :
    slope i f x = slope i f' x := by
  have hc : Tendsto (Function.update x i) (𝓝 (x i)) (𝓝 x) := by
    have h1 := (hasDerivAt_update x i (x i)).continuousAt.tendsto
    rwa [Function.update_eq_self] at h1
  exact Filter.EventuallyEq.deriv_eq (hc.eventually h)

/-! ## Sums and products -/

section Rules

variable {f g : Coords n → ℝ} {x : Coords n}

theorem slope_add (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    slope i (fun y => f y + g y) x = slope i f x + slope i g x :=
  ((hasDerivAt_slope hf i).add (hasDerivAt_slope hg i)).deriv

theorem slope_sub (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    slope i (fun y => f y - g y) x = slope i f x - slope i g x :=
  ((hasDerivAt_slope hf i).sub (hasDerivAt_slope hg i)).deriv

theorem slope_mul (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    slope i (fun y => f y * g y) x = slope i f x * g x + f x * slope i g x := by
  have h := ((hasDerivAt_slope hf i).mul (hasDerivAt_slope hg i)).deriv
  simp only [Function.update_eq_self] at h
  exact h

theorem slope_sum {ι : Type*} [Fintype ι] {F : ι → Coords n → ℝ}
    (hF : ∀ k, DifferentiableAt ℝ (F k) x) (i : Fin n) :
    slope i (fun y => ∑ k, F k y) x = ∑ k, slope i (F k) x :=
  (HasDerivAt.fun_sum fun k _ => hasDerivAt_slope (hF k) i).deriv

end Rules

/-! ## The chain rule -/

/-- A linear function of `n` numbers is fixed by its values on the `n` basic steps. -/
theorem clm_apply_eq_sum (L : (Fin n → ℝ) →L[ℝ] ℝ) (w : Fin n → ℝ) :
    L w = ∑ δ, w δ * L (Pi.single δ 1) := by
  have h := (L : (Fin n → ℝ) →ₗ[ℝ] ℝ).pi_apply_eq_sum_univ w
  have e : ∀ δ : Fin n, (fun j => if δ = j then (1 : ℝ) else 0) = Pi.single δ 1 := by
    intro δ
    funext j
    simp [Pi.single_apply, eq_comm]
  simpa [e] using h

/-- For a change of coordinates `Φ` (new coordinates in, old coordinates out): how fast the old
coordinate `α` changes when only the new coordinate `μ` moves. -/
noncomputable def jac (Φ : Coords n → Coords n) (α μ : Fin n) : Coords n → ℝ := fun x =>
  slope μ (fun y => Φ y α) x

theorem jac_eq_fderiv {Φ : Coords n → Coords n} {x : Coords n} (hΦ : DifferentiableAt ℝ Φ x)
    (α μ : Fin n) : jac Φ α μ x = fderiv ℝ Φ x (Pi.single μ 1) α := by
  have hα : HasFDerivAt (fun y => Φ y α) ((ContinuousLinearMap.proj α).comp (fderiv ℝ Φ x)) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) α).hasFDerivAt.comp x
      hΦ.hasFDerivAt
  change slope μ (fun y => Φ y α) x = _
  rw [slope_eq_fderiv hα.differentiableAt, hα.fderiv]
  rfl

/-- **The chain rule.** -/
theorem slope_comp {F : Coords n → ℝ} {Φ : Coords n → Coords n} {x : Coords n}
    (hF : DifferentiableAt ℝ F (Φ x)) (hΦ : DifferentiableAt ℝ Φ x) (i : Fin n) :
    slope i (fun y => F (Φ y)) x = ∑ δ, jac Φ δ i x * slope δ F (Φ x) := by
  have hc : DifferentiableAt ℝ (fun y => F (Φ y)) x := hF.comp x hΦ
  have e : fderiv ℝ (fun y => F (Φ y)) x = (fderiv ℝ F (Φ x)).comp (fderiv ℝ Φ x) :=
    fderiv_comp x hF hΦ
  rw [slope_eq_fderiv hc, e, ContinuousLinearMap.comp_apply, clm_apply_eq_sum]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [slope_eq_fderiv hF, jac_eq_fderiv hΦ]

/-! ## Two slopes, and smoothness -/

/-- **The order of two slopes does not matter**, for a twice smoothly differentiable function. -/
theorem slope_slope_comm {f : Coords n → ℝ} {x : Coords n} (hf : ContDiffAt ℝ 2 f x)
    (i j : Fin n) : slope i (slope j f) x = slope j (slope i f) x := by
  have hev : ∀ k, slope k f =ᶠ[𝓝 x] fun y => fderiv ℝ f y (Pi.single k 1) := fun k =>
    (hf.eventually (by simp)).mono fun y hy => slope_eq_fderiv (hy.differentiableAt (by simp)) k
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have key : ∀ a b : Fin n,
      slope a (slope b f) x = fderiv ℝ (fderiv ℝ f) x (Pi.single a 1) (Pi.single b 1) := by
    intro a b
    have h1 : HasFDerivAt (fun y => fderiv ℝ f y (Pi.single b 1))
        ((fderiv ℝ (fderiv ℝ f) x).flip (Pi.single b 1)) x := by
      simpa using hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single b (1 : ℝ)) x)
    rw [slope_congr (hev b) a, slope_eq_fderiv h1.differentiableAt, h1.fderiv]
    rfl
  rw [key, key]
  exact hf.isSymmSndFDerivAt (by simp) _ _

/-- A slope of a smooth function is smooth, one level less. -/
theorem contDiffAt_slope {f : Coords n → ℝ} {x : Coords n} {m k : WithTop ℕ∞}
    (hf : ContDiffAt ℝ k f x) (hk : k ≠ ∞) (h0 : k ≠ 0) (hmk : m + 1 ≤ k) (j : Fin n) :
    ContDiffAt ℝ m (slope j f) x := by
  have hev : slope j f =ᶠ[𝓝 x] fun y => fderiv ℝ f y (Pi.single j 1) :=
    (hf.eventually hk).mono fun y hy => slope_eq_fderiv (hy.differentiableAt h0) j
  exact ((hf.fderiv_right hmk).clm_apply contDiffAt_const).congr_of_eventuallyEq hev

end GravityInLean
