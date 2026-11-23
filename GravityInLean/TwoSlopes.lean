/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.MeanValue

import Mathlib.Tactic

/-!
# Functions of time and distance: their two slopes

In step 2 the clock and ruler functions may change in time, so each one is a function of two
numbers, the time `t` and the distance `r`.

* `dt F t r`: how fast `F` changes with time, the distance held fixed.
* `dr F t r`: how fast `F` changes with distance, the time held fixed.
* `TwiceSmooth F t r`: `F` is twice smoothly differentiable around `(t, r)`, in the standard
  library's sense (`ContDiffAt ℝ 2`).

**What is proved here.** For such a function both slopes exist, so do the slopes of the slopes,
and the order in which two slopes are taken does not matter (`TwiceSmooth.swap`). That last fact
is a theorem of the standard library (symmetry of second derivatives); this file only translates
it into the two slopes used here. The file ends with the fact step 2 leans on most: a slope that
is zero everywhere on an open stretch in one piece means the function is constant there
(`const_of_hasDerivAt_zero`), again straight from the standard library.
-/

@[expose] public section

namespace GravityInLean

open Filter Topology

/-- How fast `F` changes with time `t`, the distance `r` held fixed. -/
noncomputable def dt (F : ℝ → ℝ → ℝ) (t r : ℝ) : ℝ := deriv (fun s => F s r) t

/-- How fast `F` changes with distance `r`, the time `t` held fixed. -/
noncomputable def dr (F : ℝ → ℝ → ℝ) (t r : ℝ) : ℝ := deriv (fun s => F t s) r

/-- The constant function 0 of time and distance. -/
noncomputable def zero2 (_t _r : ℝ) : ℝ := 0

theorem dt_zero2 (t r : ℝ) : dt zero2 t r = 0 := by simp [dt, zero2]

theorem dr_zero2 (t r : ℝ) : dr zero2 t r = 0 := by simp [dr, zero2]

theorem dt_zero2_fun : dt zero2 = zero2 := by
  funext t r
  simp [dt, zero2]

theorem dr_zero2_fun : dr zero2 = zero2 := by
  funext t r
  simp [dr, zero2]

/-- `F` is twice smoothly differentiable around the point `(t, r)`. -/
def TwiceSmooth (F : ℝ → ℝ → ℝ) (t r : ℝ) : Prop :=
  ContDiffAt ℝ 2 (Function.uncurry F) (t, r)

section Lines

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Moving along time only. -/
theorem hasDerivAt_along_t {G : ℝ × ℝ → E} {t r : ℝ} (h : DifferentiableAt ℝ G (t, r)) :
    HasDerivAt (fun s => G (s, r)) (fderiv ℝ G (t, r) (1, 0)) t := by
  have hl : HasDerivAt (fun s : ℝ => (s, r)) ((1 : ℝ), (0 : ℝ)) t :=
    (hasDerivAt_id' t).prodMk (hasDerivAt_const t r)
  exact HasFDerivAt.comp_hasDerivAt (l := G) (f := fun s : ℝ => (s, r)) (x := t)
    h.hasFDerivAt hl

/-- Moving along distance only. -/
theorem hasDerivAt_along_r {G : ℝ × ℝ → E} {t r : ℝ} (h : DifferentiableAt ℝ G (t, r)) :
    HasDerivAt (fun s => G (t, s)) (fderiv ℝ G (t, r) (0, 1)) r := by
  have hl : HasDerivAt (fun s : ℝ => (t, s)) ((0 : ℝ), (1 : ℝ)) r :=
    (hasDerivAt_const r t).prodMk (hasDerivAt_id' r)
  exact HasFDerivAt.comp_hasDerivAt (l := G) (f := fun s : ℝ => (t, s)) (x := r)
    h.hasFDerivAt hl

end Lines

/-- The time slope, as the library's derivative applied to the time direction. -/
theorem dt_eq_fderiv {F : ℝ → ℝ → ℝ} {t r : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry F) (t, r)) :
    dt F t r = fderiv ℝ (Function.uncurry F) (t, r) (1, 0) :=
  (hasDerivAt_along_t h).deriv

/-- The distance slope, as the library's derivative applied to the distance direction. -/
theorem dr_eq_fderiv {F : ℝ → ℝ → ℝ} {t r : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry F) (t, r)) :
    dr F t r = fderiv ℝ (Function.uncurry F) (t, r) (0, 1) :=
  (hasDerivAt_along_r h).deriv

namespace TwiceSmooth

variable {F : ℝ → ℝ → ℝ} {t r : ℝ}

theorem differentiableAt (h : TwiceSmooth F t r) :
    DifferentiableAt ℝ (Function.uncurry F) (t, r) :=
  ContDiffAt.differentiableAt h (by simp)

/-- Near `(t, r)` the function is still differentiable. -/
theorem eventually_differentiableAt (h : TwiceSmooth F t r) :
    ∀ᶠ q in 𝓝 (t, r), DifferentiableAt ℝ (Function.uncurry F) q :=
  (ContDiffAt.eventually h (by simp)).mono fun _ hq => hq.differentiableAt (by simp)

/-- The library's derivative can itself be differentiated at `(t, r)`. -/
theorem differentiableAt_fderiv (h : TwiceSmooth F t r) :
    DifferentiableAt ℝ (fderiv ℝ (Function.uncurry F)) (t, r) :=
  (ContDiffAt.fderiv_right (m := 1) h (by norm_num)).differentiableAt (by simp)

/-- Near `t`, with the distance held at `r`, the time slope is the library's derivative applied to
the time direction. -/
theorem dt_eventually_t (h : TwiceSmooth F t r) :
    (fun s => dt F s r) =ᶠ[𝓝 t] fun s => fderiv ℝ (Function.uncurry F) (s, r) (1, 0) := by
  have ht : Tendsto (fun s : ℝ => (s, r)) (𝓝 t) (𝓝 (t, r)) :=
    tendsto_id.prodMk_nhds tendsto_const_nhds
  filter_upwards [ht.eventually h.eventually_differentiableAt] with s hs
  exact dt_eq_fderiv hs

theorem dt_eventually_r (h : TwiceSmooth F t r) :
    (fun s => dt F t s) =ᶠ[𝓝 r] fun s => fderiv ℝ (Function.uncurry F) (t, s) (1, 0) := by
  have ht : Tendsto (fun s : ℝ => (t, s)) (𝓝 r) (𝓝 (t, r)) :=
    tendsto_const_nhds.prodMk_nhds tendsto_id
  filter_upwards [ht.eventually h.eventually_differentiableAt] with s hs
  exact dt_eq_fderiv hs

theorem dr_eventually_t (h : TwiceSmooth F t r) :
    (fun s => dr F s r) =ᶠ[𝓝 t] fun s => fderiv ℝ (Function.uncurry F) (s, r) (0, 1) := by
  have ht : Tendsto (fun s : ℝ => (s, r)) (𝓝 t) (𝓝 (t, r)) :=
    tendsto_id.prodMk_nhds tendsto_const_nhds
  filter_upwards [ht.eventually h.eventually_differentiableAt] with s hs
  exact dr_eq_fderiv hs

theorem dr_eventually_r (h : TwiceSmooth F t r) :
    (fun s => dr F t s) =ᶠ[𝓝 r] fun s => fderiv ℝ (Function.uncurry F) (t, s) (0, 1) := by
  have ht : Tendsto (fun s : ℝ => (t, s)) (𝓝 r) (𝓝 (t, r)) :=
    tendsto_const_nhds.prodMk_nhds tendsto_id
  filter_upwards [ht.eventually h.eventually_differentiableAt] with s hs
  exact dr_eq_fderiv hs

theorem hasDerivAt_fderiv_t (h : TwiceSmooth F t r) (v : ℝ × ℝ) :
    HasDerivAt (fun s => fderiv ℝ (Function.uncurry F) (s, r) v)
      (fderiv ℝ (fderiv ℝ (Function.uncurry F)) (t, r) (1, 0) v) t := by
  have := (hasDerivAt_along_t h.differentiableAt_fderiv).clm_apply (hasDerivAt_const t v)
  simpa using this

theorem hasDerivAt_fderiv_r (h : TwiceSmooth F t r) (v : ℝ × ℝ) :
    HasDerivAt (fun s => fderiv ℝ (Function.uncurry F) (t, s) v)
      (fderiv ℝ (fderiv ℝ (Function.uncurry F)) (t, r) (0, 1) v) r := by
  have := (hasDerivAt_along_r h.differentiableAt_fderiv).clm_apply (hasDerivAt_const r v)
  simpa using this

/-- Near `(t, r)` the function is still twice smoothly differentiable. -/
theorem eventually (h : TwiceSmooth F t r) : ∀ᶠ q in 𝓝 (t, r), TwiceSmooth F q.1 q.2 :=
  ContDiffAt.eventually h (by simp)

/-- The time slope, seen as a function of time and distance together, can itself be
differentiated at `(t, r)`. -/
theorem differentiableAt_dt (h : TwiceSmooth F t r) :
    DifferentiableAt ℝ (Function.uncurry (dt F)) (t, r) := by
  have h1 : DifferentiableAt ℝ (fun q : ℝ × ℝ => fderiv ℝ (Function.uncurry F) q (1, 0)) (t, r) :=
    h.differentiableAt_fderiv.clm_apply (differentiableAt_const _)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [h.eventually_differentiableAt] with q hq
  exact dt_eq_fderiv (t := q.1) (r := q.2) hq

/-- The distance slope, seen as a function of time and distance together, can itself be
differentiated at `(t, r)`. -/
theorem differentiableAt_dr (h : TwiceSmooth F t r) :
    DifferentiableAt ℝ (Function.uncurry (dr F)) (t, r) := by
  have h1 : DifferentiableAt ℝ (fun q : ℝ × ℝ => fderiv ℝ (Function.uncurry F) q (0, 1)) (t, r) :=
    h.differentiableAt_fderiv.clm_apply (differentiableAt_const _)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [h.eventually_differentiableAt] with q hq
  exact dr_eq_fderiv (t := q.1) (r := q.2) hq

/-! ### The slopes and the slopes of the slopes -/

theorem slopeT (h : TwiceSmooth F t r) : HasDerivAt (fun s => F s r) (dt F t r) t :=
  (hasDerivAt_along_t h.differentiableAt).differentiableAt.hasDerivAt

theorem slopeR (h : TwiceSmooth F t r) : HasDerivAt (fun s => F t s) (dr F t r) r :=
  (hasDerivAt_along_r h.differentiableAt).differentiableAt.hasDerivAt

theorem slopeTT (h : TwiceSmooth F t r) : HasDerivAt (fun s => dt F s r) (dt (dt F) t r) t :=
  ((h.hasDerivAt_fderiv_t (1, 0)).congr_of_eventuallyEq
    h.dt_eventually_t).differentiableAt.hasDerivAt

theorem slopeTR (h : TwiceSmooth F t r) : HasDerivAt (fun s => dt F t s) (dr (dt F) t r) r :=
  ((h.hasDerivAt_fderiv_r (1, 0)).congr_of_eventuallyEq
    h.dt_eventually_r).differentiableAt.hasDerivAt

theorem slopeRT (h : TwiceSmooth F t r) : HasDerivAt (fun s => dr F s r) (dt (dr F) t r) t :=
  ((h.hasDerivAt_fderiv_t (0, 1)).congr_of_eventuallyEq
    h.dr_eventually_t).differentiableAt.hasDerivAt

theorem slopeRR (h : TwiceSmooth F t r) : HasDerivAt (fun s => dr F t s) (dr (dr F) t r) r :=
  ((h.hasDerivAt_fderiv_r (0, 1)).congr_of_eventuallyEq
    h.dr_eventually_r).differentiableAt.hasDerivAt

/-- **The order of two slopes does not matter.** First along distance then along time gives the
same as first along time then along distance. -/
theorem swap (h : TwiceSmooth F t r) : dt (dr F) t r = dr (dt F) t r := by
  have e1 : dt (dr F) t r = fderiv ℝ (fderiv ℝ (Function.uncurry F)) (t, r) (1, 0) (0, 1) :=
    h.slopeRT.unique ((h.hasDerivAt_fderiv_t (0, 1)).congr_of_eventuallyEq h.dr_eventually_t)
  have e2 : dr (dt F) t r = fderiv ℝ (fderiv ℝ (Function.uncurry F)) (t, r) (0, 1) (1, 0) :=
    h.slopeTR.unique ((h.hasDerivAt_fderiv_r (1, 0)).congr_of_eventuallyEq h.dt_eventually_r)
  rw [e1, e2]
  exact ContDiffAt.isSymmSndFDerivAt (𝕜 := ℝ) h (by simp) (1, 0) (0, 1)

end TwiceSmooth

/-! ## Slope zero means constant -/

/-- A function whose slope is zero everywhere on an open stretch in one piece is constant there.
This is the standard library's `IsOpen.is_const_of_deriv_eq_zero`. -/
theorem const_of_hasDerivAt_zero {f : ℝ → ℝ} {S : Set ℝ} (hS : IsOpen S) (hSc : IsPreconnected S)
    (hf : ∀ s ∈ S, HasDerivAt f 0 s) {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) : f a = f b :=
  hS.is_const_of_deriv_eq_zero hSc (fun s hs => (hf s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hf s hs).deriv) ha hb

/-- A function that is constant near `t` has slope zero at `t`. -/
theorem deriv_eq_zero_of_eventually_const {f : ℝ → ℝ} {t c : ℝ} (h : ∀ᶠ s in 𝓝 t, f s = c) :
    deriv f t = 0 := by
  rw [Filter.EventuallyEq.deriv_eq (f := fun _ => c) h]
  simp

end GravityInLean
