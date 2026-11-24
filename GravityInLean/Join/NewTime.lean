/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.BirkhoffGeneral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.Sqrt

import Mathlib.Tactic

/-!
# The new time is smooth

Board item `task:join-newtime`. `birkhoff_general_of_sizeEquations` gives a mass `M` and a new
time `T(t, ρ)` for an empty space-time of the general round shape, but it only says that `T` and
the radius `√S` can be differentiated once. A chart of a curved space has to be smooth of every
order. This file proves the same theorem with that added:

* `contDiffOn_dt`, `contDiffOn_dr`: the two slopes of a smooth function of time and distance are
  smooth;
* `contDiffOn_newTimeT`, `contDiffOn_newTimeR`: the two slopes the new time has to have are
  smooth, where the four functions of the shape are;
* `contDiffOn_of_slopes`: a function whose two slopes are smooth is smooth;
* `two_mul_massFn_ne_radius`: where the size of the spheres is a usable distance, the radius is
  off the rim `r = 2M`;
* `birkhoff_general_smooth`: the theorem, with `T` and the radius smooth of every order, and with
  the radius off `2M`.
-/

@[expose] public section

namespace GravityInLean.Join

open Real Filter Topology Set

open scoped ContDiff

variable {A B C S : ℝ → ℝ → ℝ} {J I : Set ℝ} {U : Set (ℝ × ℝ)}

/-! ## Slopes of smooth functions are smooth -/

/-- The slope along time of a smooth function of time and distance is smooth. -/
theorem contDiffOn_dt {F : ℝ → ℝ → ℝ} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ (Function.uncurry F) U) :
    ContDiffOn ℝ ∞ (Function.uncurry (dt F)) U := by
  have h1 : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => fderiv ℝ (Function.uncurry F) q (1, 0)) U :=
    (hF.fderiv_of_isOpen hU ENat.coe_top_add_one.le).clm_apply contDiffOn_const
  refine h1.congr ?_
  rintro ⟨t, ρ⟩ hq
  exact dt_eq_fderiv ((hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hq))

/-- The slope along distance of a smooth function of time and distance is smooth. -/
theorem contDiffOn_dr {F : ℝ → ℝ → ℝ} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ (Function.uncurry F) U) :
    ContDiffOn ℝ ∞ (Function.uncurry (dr F)) U := by
  have h1 : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => fderiv ℝ (Function.uncurry F) q (0, 1)) U :=
    (hF.fderiv_of_isOpen hU ENat.coe_top_add_one.le).clm_apply contDiffOn_const
  refine h1.congr ?_
  rintro ⟨t, ρ⟩ hq
  exact dr_eq_fderiv ((hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hq))

/-- The slope the new time has to have along the old time is smooth, where the four functions of
the shape are smooth and the size of the spheres is a usable distance. -/
theorem contDiffOn_newTimeT (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ (Function.uncurry A) U)
    (hB : ContDiffOn ℝ ∞ (Function.uncurry B) U) (hC : ContDiffOn ℝ ∞ (Function.uncurry C) U)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) U) (hD : ∀ q ∈ U, 0 < det2 A B C q.1 q.2)
    (hS0 : ∀ q ∈ U, 0 < S q.1 q.2) (hn : ∀ q ∈ U, sizeSlopeSq A B C S q.1 q.2 ≠ 0) :
    ContDiffOn ℝ ∞ (Function.uncurry (newTimeT A B C S)) U := by
  have dA : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => A q.1 q.2) U := hA
  have dB : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => B q.1 q.2) U := hB
  have dC : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => C q.1 q.2) U := hC
  have dS : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => S q.1 q.2) U := hS
  have dSt : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => dt S q.1 q.2) U := contDiffOn_dt hU hS
  have dSr : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => dr S q.1 q.2) U := contDiffOn_dr hU hS
  have d2 : ContDiffOn ℝ ∞ (fun _ : ℝ × ℝ => (2 : ℝ)) U := contDiffOn_const
  have ddet : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => det2 A B C q.1 q.2) U :=
    (dA.mul dB).add (dC.mul dC)
  have dn : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => sizeSlopeSq A B C S q.1 q.2) U :=
    ((dA.mul (dSr.mul dSr)).add ((d2.mul dC).mul (dSt.mul dSr))).sub (dB.mul (dSt.mul dSt))
  have dp : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => pT A C S q.1 q.2) U :=
    (dC.mul dSt).add (dA.mul dSr)
  have dσ : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => √(S q.1 q.2 * det2 A B C q.1 q.2)) U :=
    (dS.mul ddet).sqrt fun q hq => (mul_pos (hS0 q hq) (hD q hq)).ne'
  have dquot : ContDiffOn ℝ ∞
      (fun q : ℝ × ℝ => 2 * pT A C S q.1 q.2 / sizeSlopeSq A B C S q.1 q.2) U :=
    (d2.mul dp).div dn hn
  exact dσ.mul dquot

/-- The slope the new time has to have along the old distance label is smooth as well. -/
theorem contDiffOn_newTimeR (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ (Function.uncurry A) U)
    (hB : ContDiffOn ℝ ∞ (Function.uncurry B) U) (hC : ContDiffOn ℝ ∞ (Function.uncurry C) U)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) U) (hD : ∀ q ∈ U, 0 < det2 A B C q.1 q.2)
    (hS0 : ∀ q ∈ U, 0 < S q.1 q.2) (hn : ∀ q ∈ U, sizeSlopeSq A B C S q.1 q.2 ≠ 0) :
    ContDiffOn ℝ ∞ (Function.uncurry (newTimeR A B C S)) U := by
  have dA : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => A q.1 q.2) U := hA
  have dB : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => B q.1 q.2) U := hB
  have dC : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => C q.1 q.2) U := hC
  have dS : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => S q.1 q.2) U := hS
  have dSt : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => dt S q.1 q.2) U := contDiffOn_dt hU hS
  have dSr : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => dr S q.1 q.2) U := contDiffOn_dr hU hS
  have d2 : ContDiffOn ℝ ∞ (fun _ : ℝ × ℝ => (2 : ℝ)) U := contDiffOn_const
  have ddet : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => det2 A B C q.1 q.2) U :=
    (dA.mul dB).add (dC.mul dC)
  have dn : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => sizeSlopeSq A B C S q.1 q.2) U :=
    ((dA.mul (dSr.mul dSr)).add ((d2.mul dC).mul (dSt.mul dSr))).sub (dB.mul (dSt.mul dSt))
  have dq : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => m0 B C S q.1 q.2) U :=
    (dB.mul dSt).sub (dC.mul dSr)
  have dσ : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => √(S q.1 q.2 * det2 A B C q.1 q.2)) U :=
    (dS.mul ddet).sqrt fun q hq => (mul_pos (hS0 q hq) (hD q hq)).ne'
  have dquot : ContDiffOn ℝ ∞
      (fun q : ℝ × ℝ => 2 * m0 B C S q.1 q.2 / sizeSlopeSq A B C S q.1 q.2) U :=
    (d2.mul dq).div dn hn
  exact dσ.mul dquot

/-- The radius `√S` of the spheres is smooth where their size `S` is smooth and positive. -/
theorem contDiffOn_radius (hS : ContDiffOn ℝ ∞ (Function.uncurry S) U)
    (hS0 : ∀ q ∈ U, 0 < S q.1 q.2) : ContDiffOn ℝ ∞ (Function.uncurry (radius S)) U := by
  have dS : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => S q.1 q.2) U := hS
  have h1 : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => √(S q.1 q.2)) U :=
    dS.sqrt fun q hq => (hS0 q hq).ne'
  exact h1

/-! ## A function with two smooth slopes is smooth -/

/-- A function of time and distance that can be differentiated on an open set, and whose two
slopes there are two smooth functions `P` and `Q`, is itself smooth of every order. -/
theorem contDiffOn_of_slopes {T P Q : ℝ → ℝ → ℝ} (hU : IsOpen U)
    (hT : ∀ q ∈ U, DifferentiableAt ℝ (Function.uncurry T) q ∧ dt T q.1 q.2 = P q.1 q.2
      ∧ dr T q.1 q.2 = Q q.1 q.2)
    (hP : ContDiffOn ℝ ∞ (Function.uncurry P) U) (hQ : ContDiffOn ℝ ∞ (Function.uncurry Q) U) :
    ContDiffOn ℝ ∞ (Function.uncurry T) U := by
  rw [contDiffOn_infty_iff_fderiv_of_isOpen hU]
  refine ⟨fun q hq => (hT q hq).1.differentiableWithinAt, ?_⟩
  have h1 : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ =>
      Function.uncurry P q • ContinuousLinearMap.fst ℝ ℝ ℝ
        + Function.uncurry Q q • ContinuousLinearMap.snd ℝ ℝ ℝ) U :=
    (hP.smul_const _).add (hQ.smul_const _)
  refine h1.congr ?_
  rintro ⟨t, ρ⟩ hq
  have hd : DifferentiableAt ℝ (Function.uncurry T) (t, ρ) := (hT (t, ρ) hq).1
  have ht : dt T t ρ = P t ρ := (hT (t, ρ) hq).2.1
  have hr : dr T t ρ = Q t ρ := (hT (t, ρ) hq).2.2
  refine ContinuousLinearMap.ext fun v => ?_
  have e : (Function.uncurry P (t, ρ) • ContinuousLinearMap.fst ℝ ℝ ℝ
      + Function.uncurry Q (t, ρ) • ContinuousLinearMap.snd ℝ ℝ ℝ) v
      = P t ρ * v.1 + Q t ρ * v.2 := by
    simp [Function.uncurry]
  rw [e, clm_apply_pair (fderiv ℝ (Function.uncurry T) (t, ρ)) v, ← dt_eq_fderiv hd,
    ← dr_eq_fderiv hd, ht, hr]
  ring

/-! ## Off the rim -/

/-- Where the size of the spheres is a usable distance, the radius is not twice the mass: the
place is off the rim `r = 2M`. -/
theorem two_mul_massFn_ne_radius {t ρ : ℝ} (hD : 0 < det2 A B C t ρ) (hS0 : 0 < S t ρ)
    (hn : sizeSlopeSq A B C S t ρ ≠ 0) : 2 * massFn A B C S t ρ ≠ radius S t ρ := by
  intro h
  have hw0 : √(S t ρ) ≠ 0 := (Real.sqrt_pos.mpr hS0).ne'
  have hrs : radiusSlopeSq A B C S t ρ ≠ 0 :=
    div_ne_zero hn (mul_ne_zero four_ne_zero (mul_pos hS0 hD).ne')
  have h0 : √(S t ρ) * radiusSlopeSq A B C S t ρ = 0 := by
    unfold massFn radius at h
    linear_combination -h
  exact hrs ((mul_eq_zero.mp h0).resolve_left hw0)

/-! ## The change of labels at one point -/

/-- At one point: a new time with the two right slopes, together with the radius, gives labels
that really are coordinates there (their Jacobian is not zero), and in them the length of every
step is Schwarzschild's, with the mass read off at that point. -/
theorem relabelled_at (h : SettingG A B C S J I) {T : ℝ → ℝ → ℝ} {M : ℝ} {x : Coords 4}
    (ht : x 0 ∈ J) (hρ : x 1 ∈ I) (hn0 : sizeSlopeSq A B C S (x 0) (x 1) ≠ 0)
    (hM : massFn A B C S (x 0) (x 1) = M)
    (hTt : dt T (x 0) (x 1) = newTimeT A B C S (x 0) (x 1))
    (hTr : dr T (x 0) (x 1) = newTimeR A B C S (x 0) (x 1)) :
    dt T (x 0) (x 1) * dr (radius S) (x 0) (x 1)
        - dr T (x 0) (x 1) * dt (radius S) (x 0) (x 1) ≠ 0 ∧
      ∀ v : Coords 4, stepLength (genG A B C S) x v
        = stepLength (roundG (schwA M) (schwB M)) (relabel T (radius S) x)
            (relabelStep T (radius S) x v) := by
  subst hM
  have hS0 := h.S_pos _ ht _ hρ
  have hD := h.spaceTime _ ht _ hρ
  have hSne := hS0.ne'
  have hDne := hD.ne'
  have hw0 : √(S (x 0) (x 1)) ≠ 0 := (Real.sqrt_pos.mpr hS0).ne'
  have hw2 : √(S (x 0) (x 1)) ^ 2 = S (x 0) (x 1) := Real.sq_sqrt hS0.le
  have hσ0 : √(S (x 0) (x 1) * det2 A B C (x 0) (x 1)) ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos hS0 hD)).ne'
  have hRt : dt (radius S) (x 0) (x 1) = dt S (x 0) (x 1) / (2 * √(S (x 0) (x 1))) :=
    ((h.smoothS _ ht _ hρ).slopeT.sqrt hSne).deriv
  have hRr : dr (radius S) (x 0) (x 1) = dr S (x 0) (x 1) / (2 * √(S (x 0) (x 1))) :=
    ((h.smoothS _ ht _ hρ).slopeR.sqrt hSne).deriv
  refine ⟨?_, fun v => ?_⟩
  · -- The Jacobian is `√(S · det) / √S`.
    have hj : newTimeT A B C S (x 0) (x 1) * (dr S (x 0) (x 1) / (2 * √(S (x 0) (x 1))))
        - newTimeR A B C S (x 0) (x 1) * (dt S (x 0) (x 1) / (2 * √(S (x 0) (x 1))))
        = √(S (x 0) (x 1) * det2 A B C (x 0) (x 1)) / √(S (x 0) (x 1)) := by
      simp only [newTimeT, newTimeR]
      field_simp
      simp only [sizeSlopeSq, pT, m0]
      ring
    rw [hTt, hTr, hRt, hRr, hj]
    exact div_ne_zero hσ0 hw0
  · -- The length of a step.
    have hAs : schwA (massFn A B C S (x 0) (x 1)) (√(S (x 0) (x 1)))
        = radiusSlopeSq A B C S (x 0) (x 1) := by
      unfold schwA massFn
      field_simp
      ring
    have hBs : schwB (massFn A B C S (x 0) (x 1)) (√(S (x 0) (x 1)))
        = (radiusSlopeSq A B C S (x 0) (x 1))⁻¹ := by
      rw [← hAs]
      rfl
    have key := timeDistance_relabelled hD hS0 hn0 (v 0) (v 1)
    have e : stepLength (roundG (schwA (massFn A B C S (x 0) (x 1)))
          (schwB (massFn A B C S (x 0) (x 1))))
          (relabel T (radius S) x) (relabelStep T (radius S) x v)
        = -radiusSlopeSq A B C S (x 0) (x 1)
            * (newTimeT A B C S (x 0) (x 1) * v 0 + newTimeR A B C S (x 0) (x 1) * v 1) ^ 2
          + (radiusSlopeSq A B C S (x 0) (x 1))⁻¹
            * (dt S (x 0) (x 1) / (2 * √(S (x 0) (x 1))) * v 0
              + dr S (x 0) (x 1) / (2 * √(S (x 0) (x 1))) * v 1) ^ 2
          + S (x 0) (x 1) * v 2 ^ 2 + S (x 0) (x 1) * sin (x 2) ^ 2 * v 3 ^ 2 := by
      rw [stepLength_round]
      have r1 : relabel T (radius S) x 1 = √(S (x 0) (x 1)) := rfl
      have r2 : relabel T (radius S) x 2 = x 2 := rfl
      have s0 : relabelStep T (radius S) x v 0
          = dt T (x 0) (x 1) * v 0 + dr T (x 0) (x 1) * v 1 := rfl
      have s1 : relabelStep T (radius S) x v 1
          = dt (radius S) (x 0) (x 1) * v 0 + dr (radius S) (x 0) (x 1) * v 1 := rfl
      have s2 : relabelStep T (radius S) x v 2 = v 2 := rfl
      have s3 : relabelStep T (radius S) x v 3 = v 3 := rfl
      rw [r1, r2, s0, s1, s2, s3, hTt, hTr, hRt, hRr, hAs, hBs, hw2]
    rw [stepLength_gen, e]
    linear_combination key

/-! ## Birkhoff's theorem from the general round shape, with smooth new labels -/

/-- **Birkhoff's theorem from the general round shape, with smooth new labels.** Take a
space-time of the general round shape whose four functions are smooth of every order, which obeys
the size equations (as an empty one does), on a region where the size of the spheres is a usable
distance. Then there are a mass `M` and a new time `T(t, ρ)` such that:

* `T` and the radius `r = √S` are smooth of every order;
* the mass function equals `M` everywhere, and the radius is nowhere `2M`;
* the new labels really are coordinates near every point (their Jacobian is not zero);
* the length of every step equals Schwarzschild's length of the same step. -/
theorem birkhoff_general_smooth (h : SettingG A B C S J I)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (J ×ˢ I))
    (hB : ContDiffOn ℝ ∞ (Function.uncurry B) (J ×ˢ I))
    (hC : ContDiffOn ℝ ∞ (Function.uncurry C) (J ×ˢ I))
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (J ×ˢ I))
    (hsize : ∀ t ∈ J, ∀ ρ ∈ I, SizeEquations A B C S t ρ)
    (hn : ∀ t ∈ J, ∀ ρ ∈ I, sizeSlopeSq A B C S t ρ ≠ 0) :
    ∃ M : ℝ, ∃ T : ℝ → ℝ → ℝ,
      ContDiffOn ℝ ∞ (Function.uncurry T) (J ×ˢ I) ∧
      ContDiffOn ℝ ∞ (Function.uncurry (radius S)) (J ×ˢ I) ∧
      ∀ x : Coords 4, x 0 ∈ J → x 1 ∈ I →
        massFn A B C S (x 0) (x 1) = M ∧
        2 * M ≠ radius S (x 0) (x 1) ∧
        dt T (x 0) (x 1) * dr (radius S) (x 0) (x 1)
          - dr T (x 0) (x 1) * dt (radius S) (x 0) (x 1) ≠ 0 ∧
        ∀ v : Coords 4, stepLength (genG A B C S) x v
          = stepLength (roundG (schwA M) (schwB M)) (relabel T (radius S) x)
              (relabelStep T (radius S) x v) := by
  have hU : IsOpen (J ×ˢ I) := h.openJ.prod h.openI
  have hD : ∀ q ∈ J ×ˢ I, 0 < det2 A B C q.1 q.2 := fun q hq => h.spaceTime _ hq.1 _ hq.2
  have hS0 : ∀ q ∈ J ×ˢ I, 0 < S q.1 q.2 := fun q hq => h.S_pos _ hq.1 _ hq.2
  have hn' : ∀ q ∈ J ×ˢ I, sizeSlopeSq A B C S q.1 q.2 ≠ 0 := fun q hq => hn _ hq.1 _ hq.2
  have hR : ContDiffOn ℝ ∞ (Function.uncurry (radius S)) (J ×ˢ I) := contDiffOn_radius hS hS0
  have hz : ContDiffOn ℝ ∞ (Function.uncurry fun _ _ : ℝ => (0 : ℝ)) (J ×ˢ I) :=
    (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ × ℝ => (0 : ℝ)) (J ×ˢ I))
  rcases J.eq_empty_or_nonempty with hJ | ⟨t₀, ht₀⟩
  · exact ⟨0, fun _ _ => 0, hz, hR, fun x hx => by simp [hJ] at hx⟩
  rcases I.eq_empty_or_nonempty with hI | ⟨ρ₀, hρ₀⟩
  · exact ⟨0, fun _ _ => 0, hz, hR, fun x _ hx => by simp [hI] at hx⟩
  have hP : ContDiffOn ℝ ∞ (Function.uncurry (newTimeT A B C S)) (J ×ˢ I) :=
    contDiffOn_newTimeT hU hA hB hC hS hD hS0 hn'
  have hQ : ContDiffOn ℝ ∞ (Function.uncurry (newTimeR A B C S)) (J ×ˢ I) :=
    contDiffOn_newTimeR hU hA hB hC hS hD hS0 hn'
  obtain ⟨T, hT⟩ := exists_potential (P := newTimeT A B C S) (Q := newTimeR A B C S) h.openJ
    h.onePieceJ h.openI h.onePieceI
    (fun t ht ρ hρ => differentiableAt_newTimeT (h.smoothA t ht ρ hρ) (h.smoothB t ht ρ hρ)
      (h.smoothC t ht ρ hρ) (h.smoothS t ht ρ hρ) (h.spaceTime t ht ρ hρ) (h.S_pos t ht ρ hρ)
      (hn t ht ρ hρ))
    (fun t ht ρ hρ => differentiableAt_newTimeR (h.smoothA t ht ρ hρ) (h.smoothB t ht ρ hρ)
      (h.smoothC t ht ρ hρ) (h.smoothS t ht ρ hρ) (h.spaceTime t ht ρ hρ) (h.S_pos t ht ρ hρ)
      (hn t ht ρ hρ))
    (fun t ht ρ hρ => newTime_closed (h.smoothA t ht ρ hρ) (h.smoothB t ht ρ hρ)
      (h.smoothC t ht ρ hρ) (h.smoothS t ht ρ hρ) (h.spaceTime t ht ρ hρ) (h.S_pos t ht ρ hρ)
      (hn t ht ρ hρ) (hsize t ht ρ hρ))
  have hTs : ContDiffOn ℝ ∞ (Function.uncurry T) (J ×ˢ I) :=
    contDiffOn_of_slopes hU (fun q hq => hT q.1 hq.1 q.2 hq.2) hP hQ
  refine ⟨massFn A B C S t₀ ρ₀, T, hTs, hR, fun x ht hρ => ?_⟩
  obtain ⟨-, hTt, hTr⟩ := hT (x 0) ht (x 1) hρ
  have hM : massFn A B C S (x 0) (x 1) = massFn A B C S t₀ ρ₀ :=
    massFn_const_of_sizeEquations h hsize _ ht _ ht₀ _ hρ _ hρ₀
  obtain ⟨hj, hlen⟩ := relabelled_at h ht hρ (hn _ ht _ hρ) hM hTt hTr
  refine ⟨hM, ?_, hj, hlen⟩
  rw [← hM]
  exact two_mul_massFn_ne_radius (h.spaceTime _ ht _ hρ) (h.S_pos _ ht _ hρ) (hn _ ht _ hρ)

end GravityInLean.Join
