/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.TwoSlopes
public import GravityInLean.Join.NewTime
public import Mathlib.Analysis.Calculus.ContDiff.Basic

import Mathlib.Tactic

/-!
# A function of two labels whose mixed slope ties it to its two slopes is a product

Board item `task:rim-product`. Let `Ω` be a smooth function of two labels `u` and `v` on a box,
with `Ω · Ω_uv = Ω_u · Ω_v` and `Ω_uv ≠ 0` at every point of the box. Then `Ω` is a product of
a function of `u` and a function of `v` on the whole box, across the places where `Ω` is zero:
`Ω(u, v) · Ω_uv(u₀, v₀) = Ω_v(u, v₀) · Ω_u(u₀, v)`.

(`dt` is the slope in the first label, `dr` the slope in the second.)

The steps on paper, with `E = Ω_uv`:

1. `Ω` is zero on no open piece of the box (else `E` would be zero there). So a continuous
   function `G` with `Ω · G = 0`, or `Ω² · G = 0`, on the box is zero on the box.
2. The slope in `u` of `Ω · E = Ω_u · Ω_v` gives `Ω · E_u = Ω_uu · Ω_v`. So
   `Ω · (Ω_uu · E - Ω_u · E_u) = 0`, and by step 1 `Ω_u / E` does not depend on `u`:
   `Ω_u(u, v) · E(u₀, v) = Ω_u(u₀, v) · E(u, v)`. Likewise `Ω_v / E` does not depend on `v`.
3. Likewise `Ω · E_v = Ω_u · Ω_vv` and `Ω · E_uv = Ω_uu · Ω_vv`, so
   `Ω² · (E · E_uv - E_u · E_v) = 0`, and by step 1 `E · E_uv = E_u · E_v`. As `E` is never
   zero, `E_u / E` does not depend on `v`, so `E(u, v) · E(u₀, v₀) = E(u, v₀) · E(u₀, v)`.
4. `Ω · E = Ω_u · Ω_v` with steps 2 and 3 gives the result.
-/

@[expose] public section

namespace GravityInLean

open Set Filter Topology

open scoped ContDiff

namespace Rim

variable {Ω : ℝ → ℝ → ℝ} {J I : Set ℝ}

/-- A function that is smooth on an open box is twice smoothly differentiable around each point
of the box. -/
theorem twiceSmooth_of_box {G : ℝ → ℝ → ℝ} (hJ : IsOpen J) (hI : IsOpen I)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (J ×ˢ I)) {u v : ℝ} (hu : u ∈ J) (hv : v ∈ I) :
    TwiceSmooth G u v :=
  (hG.contDiffAt ((hJ.prod hI).mem_nhds (mk_mem_prod hu hv))).of_le (by norm_num)

/-- Two functions that agree along a line of the first label, on an open stretch, have the same
slope in the first label there. -/
theorem dt_congr_of_box {F G : ℝ → ℝ → ℝ} (hJ : IsOpen J) {v : ℝ}
    (h : ∀ u ∈ J, F u v = G u v) {u : ℝ} (hu : u ∈ J) : dt F u v = dt G u v := by
  change deriv (fun s => F s v) u = deriv (fun s => G s v) u
  exact Filter.EventuallyEq.deriv_eq
    (Filter.eventuallyEq_of_mem (hJ.mem_nhds hu) fun s hs => h s hs)

/-- **Step 1: `Ω` is zero on no open piece of the box.** If the mixed slope of `Ω` is nowhere
zero on the box, then a continuous function `G` with `Ω · G = 0` on the box is zero on the
box. -/
theorem eq_zero_of_mul_eq_zero_on_box (hJ : IsOpen J) (hI : IsOpen I)
    (hne : ∀ u ∈ J, ∀ v ∈ I, dt (dr Ω) u v ≠ 0) {G : ℝ × ℝ → ℝ}
    (hG : ContinuousOn G (J ×ˢ I)) (h : ∀ u ∈ J, ∀ v ∈ I, Ω u v * G (u, v) = 0) :
    ∀ u ∈ J, ∀ v ∈ I, G (u, v) = 0 := by
  intro u hu v hv
  by_contra hG0
  have hU : J ×ˢ I ∈ 𝓝 (u, v) := (hJ.prod hI).mem_nhds (mk_mem_prod hu hv)
  have h1 : ∀ᶠ q in 𝓝 (u, v), G q ≠ 0 := (hG.continuousAt hU).eventually_ne hG0
  have h2 : ∀ᶠ q in 𝓝 (u, v), q ∈ J ×ˢ I ∧ G q ≠ 0 :=
    (Filter.eventually_of_mem hU fun q hq => hq).and h1
  obtain ⟨Ju, Iv, hJu, huJu, hIv, hvIv, hsub⟩ := mem_nhds_prod_iff'.1 h2
  have hΩ0 : ∀ s ∈ Ju, ∀ w ∈ Iv, Ω s w = 0 := by
    intro s hs w hw
    have hq : (s, w) ∈ J ×ˢ I ∧ G (s, w) ≠ 0 := hsub (mk_mem_prod hs hw)
    have hsw := mem_prod.1 hq.1
    exact (mul_eq_zero.1 (h s hsw.1 w hsw.2)).resolve_right hq.2
  have hdr : ∀ s ∈ Ju, dr Ω s v = 0 := fun s hs =>
    deriv_eq_zero_of_eventually_const (c := 0)
      (Filter.eventually_of_mem (hIv.mem_nhds hvIv) fun w hw => hΩ0 s hs w hw)
  have hE : dt (dr Ω) u v = 0 :=
    deriv_eq_zero_of_eventually_const (c := 0)
      (Filter.eventually_of_mem (hJu.mem_nhds huJu) fun s hs => hdr s hs)
  exact hne u hu v hv hE

/-- **A product, across its zeros.** A smooth function `Ω` on a box with
`Ω · Ω_uv = Ω_u · Ω_v` and `Ω_uv ≠ 0` everywhere on the box is the product of its slope in `v`
along one line and its slope in `u` along another, up to the constant `Ω_uv(u₀, v₀)`. -/
theorem product_form {Ω : ℝ → ℝ → ℝ} {J I : Set ℝ} (hJ : IsOpen J) (hJc : IsPreconnected J)
    (hI : IsOpen I) (hIc : IsPreconnected I)
    (hΩ : ContDiffOn ℝ ∞ (Function.uncurry Ω) (J ×ˢ I))
    (heq : ∀ u ∈ J, ∀ v ∈ I, Ω u v * dt (dr Ω) u v = dt Ω u v * dr Ω u v)
    (hne : ∀ u ∈ J, ∀ v ∈ I, dt (dr Ω) u v ≠ 0) :
    ∀ u ∈ J, ∀ v ∈ I, ∀ u₀ ∈ J, ∀ v₀ ∈ I,
      Ω u v * dt (dr Ω) u₀ v₀ = dr Ω u v₀ * dt Ω u₀ v := by
  have hU : IsOpen (J ×ˢ I) := hJ.prod hI
  -- All the slopes that come up are smooth on the box.
  have hP : ContDiffOn ℝ ∞ (Function.uncurry (dt Ω)) (J ×ˢ I) := Join.contDiffOn_dt hU hΩ
  have hQ : ContDiffOn ℝ ∞ (Function.uncurry (dr Ω)) (J ×ˢ I) := Join.contDiffOn_dr hU hΩ
  have hE : ContDiffOn ℝ ∞ (Function.uncurry (dt (dr Ω))) (J ×ˢ I) := Join.contDiffOn_dt hU hQ
  have hPu : ContDiffOn ℝ ∞ (Function.uncurry (dt (dt Ω))) (J ×ˢ I) := Join.contDiffOn_dt hU hP
  have hQv : ContDiffOn ℝ ∞ (Function.uncurry (dr (dr Ω))) (J ×ˢ I) := Join.contDiffOn_dr hU hQ
  have hEu : ContDiffOn ℝ ∞ (Function.uncurry (dt (dt (dr Ω)))) (J ×ˢ I) :=
    Join.contDiffOn_dt hU hE
  have hEv : ContDiffOn ℝ ∞ (Function.uncurry (dr (dt (dr Ω)))) (J ×ˢ I) :=
    Join.contDiffOn_dr hU hE
  have hEuv : ContDiffOn ℝ ∞ (Function.uncurry (dr (dt (dt (dr Ω))))) (J ×ˢ I) :=
    Join.contDiffOn_dr hU hEu
  have ts : ∀ {G : ℝ → ℝ → ℝ}, ContDiffOn ℝ ∞ (Function.uncurry G) (J ×ˢ I) →
      ∀ u ∈ J, ∀ v ∈ I, TwiceSmooth G u v :=
    fun hG u hu v hv => twiceSmooth_of_box hJ hI hG hu hv
  -- The slope in `u` of the equation: `Ω · E_u = Ω_uu · Ω_v`.
  have I1 : ∀ u ∈ J, ∀ v ∈ I, Ω u v * dt (dt (dr Ω)) u v = dt (dt Ω) u v * dr Ω u v := by
    intro u hu v hv
    have a1 : HasDerivAt (fun s => Ω s v * dt (dr Ω) s v)
        (dt Ω u v * dt (dr Ω) u v + Ω u v * dt (dt (dr Ω)) u v) u :=
      (ts hΩ u hu v hv).slopeT.mul (ts hE u hu v hv).slopeT
    have a2 : HasDerivAt (fun s => dt Ω s v * dr Ω s v)
        (dt (dt Ω) u v * dr Ω u v + dt Ω u v * dt (dr Ω) u v) u :=
      (ts hP u hu v hv).slopeT.mul (ts hQ u hu v hv).slopeT
    have a3 : (fun s => Ω s v * dt (dr Ω) s v) =ᶠ[𝓝 u] fun s => dt Ω s v * dr Ω s v :=
      Filter.eventuallyEq_of_mem (hJ.mem_nhds hu) fun s hs => heq s hs v hv
    have a4 : dt Ω u v * dt (dr Ω) u v + Ω u v * dt (dt (dr Ω)) u v =
        dt (dt Ω) u v * dr Ω u v + dt Ω u v * dt (dr Ω) u v :=
      a1.unique (a2.congr_of_eventuallyEq a3)
    linarith
  -- The slope in `v` of the equation: `Ω · E_v = Ω_u · Ω_vv`.
  have I2 : ∀ u ∈ J, ∀ v ∈ I, Ω u v * dr (dt (dr Ω)) u v = dt Ω u v * dr (dr Ω) u v := by
    intro u hu v hv
    have a1 : HasDerivAt (fun s => Ω u s * dt (dr Ω) u s)
        (dr Ω u v * dt (dr Ω) u v + Ω u v * dr (dt (dr Ω)) u v) v :=
      (ts hΩ u hu v hv).slopeR.mul (ts hE u hu v hv).slopeR
    have a2 : HasDerivAt (fun s => dt Ω u s * dr Ω u s)
        (dr (dt Ω) u v * dr Ω u v + dt Ω u v * dr (dr Ω) u v) v :=
      (ts hP u hu v hv).slopeR.mul (ts hQ u hu v hv).slopeR
    have a3 : (fun s => Ω u s * dt (dr Ω) u s) =ᶠ[𝓝 v] fun s => dt Ω u s * dr Ω u s :=
      Filter.eventuallyEq_of_mem (hI.mem_nhds hv) fun s hs => heq u hu s hs
    have a4 : dr Ω u v * dt (dr Ω) u v + Ω u v * dr (dt (dr Ω)) u v =
        dr (dt Ω) u v * dr Ω u v + dt Ω u v * dr (dr Ω) u v :=
      a1.unique (a2.congr_of_eventuallyEq a3)
    have a5 : dt (dr Ω) u v = dr (dt Ω) u v := (ts hΩ u hu v hv).swap
    rw [← a5] at a4
    linarith
  -- The slope in `v` of `I1`: `Ω · E_uv = Ω_uu · Ω_vv`.
  have I3 : ∀ u ∈ J, ∀ v ∈ I,
      Ω u v * dr (dt (dt (dr Ω))) u v = dt (dt Ω) u v * dr (dr Ω) u v := by
    intro u hu v hv
    have a1 : HasDerivAt (fun s => Ω u s * dt (dt (dr Ω)) u s)
        (dr Ω u v * dt (dt (dr Ω)) u v + Ω u v * dr (dt (dt (dr Ω))) u v) v :=
      (ts hΩ u hu v hv).slopeR.mul (ts hEu u hu v hv).slopeR
    have a2 : HasDerivAt (fun s => dt (dt Ω) u s * dr Ω u s)
        (dr (dt (dt Ω)) u v * dr Ω u v + dt (dt Ω) u v * dr (dr Ω) u v) v :=
      (ts hPu u hu v hv).slopeR.mul (ts hQ u hu v hv).slopeR
    have a3 : (fun s => Ω u s * dt (dt (dr Ω)) u s) =ᶠ[𝓝 v]
        fun s => dt (dt Ω) u s * dr Ω u s :=
      Filter.eventuallyEq_of_mem (hI.mem_nhds hv) fun s hs => I1 u hu s hs
    have a4 : dr Ω u v * dt (dt (dr Ω)) u v + Ω u v * dr (dt (dt (dr Ω))) u v =
        dr (dt (dt Ω)) u v * dr Ω u v + dt (dt Ω) u v * dr (dr Ω) u v :=
      a1.unique (a2.congr_of_eventuallyEq a3)
    have a5 : dr (dt (dt Ω)) u v = dt (dt (dr Ω)) u v := by
      rw [← (ts hP u hu v hv).swap]
      exact dt_congr_of_box hJ (fun s hs => ((ts hΩ s hs v hv).swap).symm) hu
    rw [a5] at a4
    linarith
  -- Step 2, first half: `Ω_uu · E - Ω_u · E_u = 0`.
  have Z1 : ∀ u ∈ J, ∀ v ∈ I,
      dt (dt Ω) u v * dt (dr Ω) u v - dt Ω u v * dt (dt (dr Ω)) u v = 0 :=
    eq_zero_of_mul_eq_zero_on_box hJ hI hne
      (G := fun q => Function.uncurry (dt (dt Ω)) q * Function.uncurry (dt (dr Ω)) q -
        Function.uncurry (dt Ω) q * Function.uncurry (dt (dt (dr Ω))) q)
      ((hPu.continuousOn.mul hE.continuousOn).sub (hP.continuousOn.mul hEu.continuousOn))
      (fun u hu v hv => by
        change Ω u v * (dt (dt Ω) u v * dt (dr Ω) u v - dt Ω u v * dt (dt (dr Ω)) u v) = 0
        linear_combination (dt (dt Ω) u v) * heq u hu v hv - (dt Ω u v) * I1 u hu v hv)
  -- Step 2, second half: `Ω_vv · E - Ω_v · E_v = 0`.
  have Z2 : ∀ u ∈ J, ∀ v ∈ I,
      dr (dr Ω) u v * dt (dr Ω) u v - dr Ω u v * dr (dt (dr Ω)) u v = 0 :=
    eq_zero_of_mul_eq_zero_on_box hJ hI hne
      (G := fun q => Function.uncurry (dr (dr Ω)) q * Function.uncurry (dt (dr Ω)) q -
        Function.uncurry (dr Ω) q * Function.uncurry (dr (dt (dr Ω))) q)
      ((hQv.continuousOn.mul hE.continuousOn).sub (hQ.continuousOn.mul hEv.continuousOn))
      (fun u hu v hv => by
        change Ω u v * (dr (dr Ω) u v * dt (dr Ω) u v - dr Ω u v * dr (dt (dr Ω)) u v) = 0
        linear_combination (dr (dr Ω) u v) * heq u hu v hv - (dr Ω u v) * I2 u hu v hv)
  -- Step 3: `Ω · (E_uv · E - E_u · E_v) = 0`, and then `E_uv · E - E_u · E_v = 0`.
  have Z3' : ∀ u ∈ J, ∀ v ∈ I, Ω u v * (dr (dt (dt (dr Ω))) u v * dt (dr Ω) u v -
      dt (dt (dr Ω)) u v * dr (dt (dr Ω)) u v) = 0 :=
    eq_zero_of_mul_eq_zero_on_box hJ hI hne
      (G := fun q => Function.uncurry Ω q *
        (Function.uncurry (dr (dt (dt (dr Ω)))) q * Function.uncurry (dt (dr Ω)) q -
          Function.uncurry (dt (dt (dr Ω))) q * Function.uncurry (dr (dt (dr Ω))) q))
      (hΩ.continuousOn.mul
        ((hEuv.continuousOn.mul hE.continuousOn).sub (hEu.continuousOn.mul hEv.continuousOn)))
      (fun u hu v hv => by
        change Ω u v * (Ω u v * (dr (dt (dt (dr Ω))) u v * dt (dr Ω) u v -
          dt (dt (dr Ω)) u v * dr (dt (dr Ω)) u v)) = 0
        linear_combination (Ω u v * dr (dt (dt (dr Ω))) u v) * heq u hu v hv +
          (dt Ω u v * dr Ω u v) * I3 u hu v hv -
          (Ω u v * dr (dt (dr Ω)) u v) * I1 u hu v hv -
          (dt (dt Ω) u v * dr Ω u v) * I2 u hu v hv)
  have Z3 : ∀ u ∈ J, ∀ v ∈ I, dr (dt (dt (dr Ω))) u v * dt (dr Ω) u v -
      dt (dt (dr Ω)) u v * dr (dt (dr Ω)) u v = 0 :=
    eq_zero_of_mul_eq_zero_on_box hJ hI hne
      (G := fun q => Function.uncurry (dr (dt (dt (dr Ω)))) q * Function.uncurry (dt (dr Ω)) q -
          Function.uncurry (dt (dt (dr Ω))) q * Function.uncurry (dr (dt (dr Ω))) q)
      ((hEuv.continuousOn.mul hE.continuousOn).sub (hEu.continuousOn.mul hEv.continuousOn))
      (fun u hu v hv => Z3' u hu v hv)
  -- Step 2, conclusion: `Ω_u / E` does not depend on `u`.
  have S2a : ∀ v ∈ I, ∀ u ∈ J, ∀ u₀ ∈ J,
      dt Ω u v * dt (dr Ω) u₀ v = dt Ω u₀ v * dt (dr Ω) u v := by
    intro v hv u hu u₀ hu₀
    have d : ∀ s ∈ J, HasDerivAt (fun s => dt Ω s v / dt (dr Ω) s v) 0 s := by
      intro s hs
      have d1 : HasDerivAt (fun s => dt Ω s v / dt (dr Ω) s v)
          ((dt (dt Ω) s v * dt (dr Ω) s v - dt Ω s v * dt (dt (dr Ω)) s v) /
            dt (dr Ω) s v ^ 2) s :=
        (ts hP s hs v hv).slopeT.fun_div (ts hE s hs v hv).slopeT (hne s hs v hv)
      rw [Z1 s hs v hv, zero_div] at d1
      exact d1
    have c : dt Ω u v / dt (dr Ω) u v = dt Ω u₀ v / dt (dr Ω) u₀ v :=
      const_of_hasDerivAt_zero hJ hJc d hu hu₀
    rw [div_eq_div_iff (hne u hu v hv) (hne u₀ hu₀ v hv)] at c
    exact c
  -- Step 2, conclusion: `Ω_v / E` does not depend on `v`.
  have S2b : ∀ u ∈ J, ∀ v ∈ I, ∀ v₀ ∈ I,
      dr Ω u v * dt (dr Ω) u v₀ = dr Ω u v₀ * dt (dr Ω) u v := by
    intro u hu v hv v₀ hv₀
    have d : ∀ s ∈ I, HasDerivAt (fun s => dr Ω u s / dt (dr Ω) u s) 0 s := by
      intro s hs
      have d1 : HasDerivAt (fun s => dr Ω u s / dt (dr Ω) u s)
          ((dr (dr Ω) u s * dt (dr Ω) u s - dr Ω u s * dr (dt (dr Ω)) u s) /
            dt (dr Ω) u s ^ 2) s :=
        (ts hQ u hu s hs).slopeR.fun_div (ts hE u hu s hs).slopeR (hne u hu s hs)
      rw [Z2 u hu s hs, zero_div] at d1
      exact d1
    have c : dr Ω u v / dt (dr Ω) u v = dr Ω u v₀ / dt (dr Ω) u v₀ :=
      const_of_hasDerivAt_zero hI hIc d hv hv₀
    rw [div_eq_div_iff (hne u hu v hv) (hne u hu v₀ hv₀)] at c
    exact c
  -- Step 3: `E_u / E` does not depend on `v`.
  have S3a : ∀ u ∈ J, ∀ v ∈ I, ∀ v₀ ∈ I,
      dt (dt (dr Ω)) u v * dt (dr Ω) u v₀ = dt (dt (dr Ω)) u v₀ * dt (dr Ω) u v := by
    intro u hu v hv v₀ hv₀
    have d : ∀ s ∈ I, HasDerivAt (fun s => dt (dt (dr Ω)) u s / dt (dr Ω) u s) 0 s := by
      intro s hs
      have d1 : HasDerivAt (fun s => dt (dt (dr Ω)) u s / dt (dr Ω) u s)
          ((dr (dt (dt (dr Ω))) u s * dt (dr Ω) u s -
            dt (dt (dr Ω)) u s * dr (dt (dr Ω)) u s) / dt (dr Ω) u s ^ 2) s :=
        (ts hEu u hu s hs).slopeR.fun_div (ts hE u hu s hs).slopeR (hne u hu s hs)
      rw [Z3 u hu s hs, zero_div] at d1
      exact d1
    have c : dt (dt (dr Ω)) u v / dt (dr Ω) u v = dt (dt (dr Ω)) u v₀ / dt (dr Ω) u v₀ :=
      const_of_hasDerivAt_zero hI hIc d hv hv₀
    rw [div_eq_div_iff (hne u hu v hv) (hne u hu v₀ hv₀)] at c
    exact c
  -- Step 3, conclusion: `E` is a product.
  have S3b : ∀ u ∈ J, ∀ u₀ ∈ J, ∀ v ∈ I, ∀ v₀ ∈ I,
      dt (dr Ω) u v * dt (dr Ω) u₀ v₀ = dt (dr Ω) u₀ v * dt (dr Ω) u v₀ := by
    intro u hu u₀ hu₀ v hv v₀ hv₀
    have d : ∀ s ∈ J, HasDerivAt (fun s => dt (dr Ω) s v / dt (dr Ω) s v₀) 0 s := by
      intro s hs
      have d1 : HasDerivAt (fun s => dt (dr Ω) s v / dt (dr Ω) s v₀)
          ((dt (dt (dr Ω)) s v * dt (dr Ω) s v₀ - dt (dr Ω) s v * dt (dt (dr Ω)) s v₀) /
            dt (dr Ω) s v₀ ^ 2) s :=
        (ts hE s hs v hv).slopeT.fun_div (ts hE s hs v₀ hv₀).slopeT (hne s hs v₀ hv₀)
      have d2 : dt (dt (dr Ω)) s v * dt (dr Ω) s v₀ - dt (dr Ω) s v * dt (dt (dr Ω)) s v₀ = 0 := by
        linear_combination S3a s hs v hv v₀ hv₀
      rw [d2, zero_div] at d1
      exact d1
    have c : dt (dr Ω) u v / dt (dr Ω) u v₀ = dt (dr Ω) u₀ v / dt (dr Ω) u₀ v₀ :=
      const_of_hasDerivAt_zero hJ hJc d hu hu₀
    rw [div_eq_div_iff (hne u hu v₀ hv₀) (hne u₀ hu₀ v₀ hv₀)] at c
    exact c
  -- Step 4: put the pieces together.
  intro u hu v hv u₀ hu₀ v₀ hv₀
  have h1 := heq u hu v hv
  have h2 := S2a v hv u hu u₀ hu₀
  have h3 := S2b u hu v hv v₀ hv₀
  have h4 := S3b u hu u₀ hu₀ v hv v₀ hv₀
  apply mul_right_cancel₀ (pow_ne_zero 2 (hne u hu v hv))
  linear_combination (Ω u v * dt (dr Ω) u v) * h4 + (dt (dr Ω) u₀ v * dt (dr Ω) u v₀) * h1 +
    (dr Ω u v * dt (dr Ω) u v₀) * h2 + (dt Ω u₀ v * dt (dr Ω) u v) * h3

end Rim

end GravityInLean
