/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.TwoSlopes
public import GravityInLean.RoundSpacetime

import Mathlib.Tactic

/-!
# Step 2, part one: a round space-time that may change in time

Step 1 computed the curvature of a round space-time that does not change. Here the clock function
`A` and the ruler function `B` may also depend on the time `t`:

`-A(t, r) dt² + B(t, r) dr² + r² dθ² + r² sin²θ dφ²`

This is the usual starting shape for Birkhoff's theorem in the textbooks.

**What is proved here.**

* `christoffel_changing`: the general formula for the connection, applied to this length measure,
  gives the table `changingΓ` written out below. No conditions.
* `ricci_changing_tt`, `_rr`, `_tr`, `_rt`, `_θθ`, `_φφ`, `_offdiag`: the general formula for the
  curvature, applied to that connection, gives four formulas. Three are the formulas of Piece B
  with new terms for the change in time (`ricciTTc`, `ricciRRc`, `ricciAngc`); the fourth is new,
  the mixed time-distance part `ricciTRc`. Every other part is zero or a multiple of these.
* `changing_ricciFlat_iff`: so Einstein's equation for empty space, all sixteen parts of it, holds
  at a point exactly when these four formulas vanish there.

**What is still assumed.** As in step 1: curvature is defined by the classic coordinate formulas
(`Curvature.lean`), the poles and the centre are left out, and the starting shape is taken as
given. New here: the clock and ruler functions have to be twice smoothly differentiable, because
the mixed time-distance part is only free of second slopes when the order of two slopes does not
matter.
-/

@[expose] public section

namespace GravityInLean

open Real Filter Topology

/-! ## Functions of time, distance and the pole angle -/

/-- A function of the form `F(t, r) · h(θ)`, seen as a function of all four coordinates. -/
noncomputable def sep2 (F : ℝ → ℝ → ℝ) (h : ℝ → ℝ) (x : Coords 4) : ℝ := F (x 0) (x 1) * h (x 2)

/-- Along time, only the first factor changes. -/
theorem slope_sep2_t (F : ℝ → ℝ → ℝ) (h : ℝ → ℝ) (x : Coords 4) :
    slope 0 (sep2 F h) x = dt F (x 0) (x 1) * h (x 2) := by
  simp [slope, sep2, dt, deriv_mul_const_field]

/-- Along the distance, only the first factor changes. -/
theorem slope_sep2_r (F : ℝ → ℝ → ℝ) (h : ℝ → ℝ) (x : Coords 4) :
    slope 1 (sep2 F h) x = dr F (x 0) (x 1) * h (x 2) := by
  simp [slope, sep2, dr, deriv_mul_const_field]

/-- Along the pole angle, only the second factor changes. -/
theorem slope_sep2_θ (F : ℝ → ℝ → ℝ) (h : ℝ → ℝ) (x : Coords 4) :
    slope 2 (sep2 F h) x = F (x 0) (x 1) * deriv h (x 2) := by
  simp [slope, sep2, deriv_const_mul_field]

/-- Such a function does not change around the axis. -/
theorem slope_sep2_φ (F : ℝ → ℝ → ℝ) (h : ℝ → ℝ) (x : Coords 4) : slope 3 (sep2 F h) x = 0 := by
  simp [slope, sep2]

/-! ## The named pieces -/

/-- `-A(t, r)`. -/
noncomputable def negA (A : ℝ → ℝ → ℝ) (t r : ℝ) : ℝ := -A t r

/-- A function of the distance alone, seen as a function of time and distance. -/
noncomputable def onlyR (f : ℝ → ℝ) (_t r : ℝ) : ℝ := f r

/-- `P / (2Q)`: six entries of the connection have this form. -/
noncomputable def half (P Q : ℝ → ℝ → ℝ) (t r : ℝ) : ℝ := P t r / (2 * Q t r)

/-- `-r / B(t, r)`. -/
noncomputable def sF2 (B : ℝ → ℝ → ℝ) (t r : ℝ) : ℝ := -r / B t r

theorem dt_negA (A : ℝ → ℝ → ℝ) (t r : ℝ) : dt (negA A) t r = -dt A t r := by
  simp [dt, negA]

theorem dr_negA (A : ℝ → ℝ → ℝ) (t r : ℝ) : dr (negA A) t r = -dr A t r := by
  simp [dr, negA]

theorem dt_onlyR (f : ℝ → ℝ) (t r : ℝ) : dt (onlyR f) t r = 0 := by
  simp [dt, onlyR]

theorem dr_onlyR (f : ℝ → ℝ) (t r : ℝ) : dr (onlyR f) t r = deriv f r := by
  simp [dr, onlyR]

theorem dt_half {P Q : ℝ → ℝ → ℝ} {t r P' Q' : ℝ} (hP : HasDerivAt (fun s => P s r) P' t)
    (hQ : HasDerivAt (fun s => Q s r) Q' t) (h0 : Q t r ≠ 0) :
    dt (half P Q) t r = (P' * (2 * Q t r) - P t r * (2 * Q')) / (2 * Q t r) ^ 2 :=
  (hP.div (hQ.const_mul 2) (mul_ne_zero two_ne_zero h0)).deriv

theorem dr_half {P Q : ℝ → ℝ → ℝ} {t r P' Q' : ℝ} (hP : HasDerivAt (fun s => P t s) P' r)
    (hQ : HasDerivAt (fun s => Q t s) Q' r) (h0 : Q t r ≠ 0) :
    dr (half P Q) t r = (P' * (2 * Q t r) - P t r * (2 * Q')) / (2 * Q t r) ^ 2 :=
  (hP.div (hQ.const_mul 2) (mul_ne_zero two_ne_zero h0)).deriv

theorem dr_sF2 {B : ℝ → ℝ → ℝ} {t r B' : ℝ} (hB : HasDerivAt (fun s => B t s) B' r)
    (h0 : B t r ≠ 0) : dr (sF2 B) t r = (-1 * B t r - -r * B') / B t r ^ 2 :=
  ((hasDerivAt_id' r).neg.div hB h0).deriv

/-! ## The length measure -/

/-- The time-and-distance part of the four diagonal entries `-A`, `B`, `r²`, `r² sin²θ`. -/
noncomputable def gtr (A B : ℝ → ℝ → ℝ) (i : Fin 4) : ℝ → ℝ → ℝ :=
  if i = 0 then negA A else if i = 1 then B else onlyR sqF

/-- The four diagonal entries of the length measure. -/
noncomputable def changingDiag (A B : ℝ → ℝ → ℝ) (i : Fin 4) : Coords 4 → ℝ :=
  sep2 (gtr A B i) (gθ i)

/-- The length measure `-A(t,r) dt² + B(t,r) dr² + r² dθ² + r² sin²θ dφ²` of a round space-time
that may change in time. -/
noncomputable def changingG (A B : ℝ → ℝ → ℝ) : Fin 4 → Fin 4 → Coords 4 → ℝ :=
  diag (changingDiag A B)

/-- Its inverse: one over each diagonal entry. -/
noncomputable def changingGinv (A B : ℝ → ℝ → ℝ) : Fin 4 → Fin 4 → Coords 4 → ℝ :=
  diag fun i x => (changingDiag A B i x)⁻¹

/-! ## Its connection, written out -/

/-- The time-and-distance part of each entry of the connection. -/
noncomputable def trPart (A B : ℝ → ℝ → ℝ) (a b c : Fin 4) : ℝ → ℝ → ℝ :=
  if a = 0 ∧ b = 0 ∧ c = 0 then half (dt A) A
  else if a = 0 ∧ ((b = 0 ∧ c = 1) ∨ (b = 1 ∧ c = 0)) then half (dr A) A
  else if a = 0 ∧ b = 1 ∧ c = 1 then half (dt B) A
  else if a = 1 ∧ b = 0 ∧ c = 0 then half (dr A) B
  else if a = 1 ∧ ((b = 0 ∧ c = 1) ∨ (b = 1 ∧ c = 0)) then half (dt B) B
  else if a = 1 ∧ b = 1 ∧ c = 1 then half (dr B) B
  else if a = 1 ∧ ((b = 2 ∧ c = 2) ∨ (b = 3 ∧ c = 3)) then sF2 B
  else if (a = 2 ∧ ((b = 1 ∧ c = 2) ∨ (b = 2 ∧ c = 1)))
      ∨ (a = 3 ∧ ((b = 1 ∧ c = 3) ∨ (b = 3 ∧ c = 1))) then onlyR uF
  else if (a = 2 ∧ b = 3 ∧ c = 3) ∨ (a = 3 ∧ ((b = 2 ∧ c = 3) ∨ (b = 3 ∧ c = 2))) then onlyR oneR
  else onlyR constZero

/-- The connection of the round space-time that may change in time, written out. Seventeen of
its 64 entries are not zero; four of them are new compared with step 1. -/
noncomputable def changingΓ (A B : ℝ → ℝ → ℝ) (a b c : Fin 4) : Coords 4 → ℝ :=
  sep2 (trPart A B a b c) (θPart a b c)

theorem changingΓ_apply (A B : ℝ → ℝ → ℝ) (a b c : Fin 4) (x : Coords 4) :
    changingΓ A B a b c x = trPart A B a b c (x 0) (x 1) * θPart a b c (x 2) := rfl

theorem slope_changingΓ_t (A B : ℝ → ℝ → ℝ) (a b c : Fin 4) (x : Coords 4) :
    slope 0 (changingΓ A B a b c) x = dt (trPart A B a b c) (x 0) (x 1) * θPart a b c (x 2) :=
  slope_sep2_t _ _ x

theorem slope_changingΓ_r (A B : ℝ → ℝ → ℝ) (a b c : Fin 4) (x : Coords 4) :
    slope 1 (changingΓ A B a b c) x = dr (trPart A B a b c) (x 0) (x 1) * θPart a b c (x 2) :=
  slope_sep2_r _ _ x

theorem slope_changingΓ_θ (A B : ℝ → ℝ → ℝ) (a b c : Fin 4) (x : Coords 4) :
    slope 2 (changingΓ A B a b c) x
      = trPart A B a b c (x 0) (x 1) * deriv (θPart a b c) (x 2) :=
  slope_sep2_θ _ _ x

theorem slope_changingΓ_φ (A B : ℝ → ℝ → ℝ) (a b c : Fin 4) (x : Coords 4) :
    slope 3 (changingΓ A B a b c) x = 0 := slope_sep2_φ _ _ x

/-- **The connection.** The general formula, applied to the length measure of a round space-time
that may change in time, gives exactly the table `changingΓ`, at every point and for every clock
and ruler function. -/
theorem christoffel_changing (A B : ℝ → ℝ → ℝ) (a b c : Fin 4) (x : Coords 4) :
    christoffel (changingG A B) (changingGinv A B) a b c x = changingΓ A B a b c x := by
  simp only [changingGinv, christoffel_diag, changingG, slope_diag]
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    (conv_lhs =>
      simp [changingDiag, sep2, slope_sep2_t, slope_sep2_r, slope_sep2_θ, slope_sep2_φ, gtr, gθ,
        dt_negA, dr_negA, dt_onlyR, dr_onlyR, deriv_sqF, deriv_sin2, deriv_constOne, negA,
        onlyR, sqF, sin2, constOne]) <;>
    (conv_rhs =>
      simp [changingΓ_apply, trPart, θPart, half, sF2, onlyR, uF, oneR, scF, cotF, oneθ, sin2,
        constOne, constZero]) <;>
    ring

/-- The same as an equality of whole tables. -/
theorem christoffel_changing_eq (A B : ℝ → ℝ → ℝ) :
    christoffel (changingG A B) (changingGinv A B) = changingΓ A B := by
  funext a b c x
  exact christoffel_changing A B a b c x

/-! ## The four formulas -/

/-- The time-time part of the curvature. The first line is the formula of Piece B at the time
`t`; the rest are the new terms that come from change in time. -/
noncomputable def ricciTTc (A B : ℝ → ℝ → ℝ) (t r : ℝ) : ℝ :=
  ricciTT (A t r) (dr A t r) (dr (dr A) t r) (B t r) (dr B t r) r
    - dt (dt B) t r / (2 * B t r) + dt B t r ^ 2 / (4 * B t r ^ 2)
    + dt A t r * dt B t r / (4 * A t r * B t r)

/-- The distance-distance part of the curvature, again Piece B's formula plus new terms. -/
noncomputable def ricciRRc (A B : ℝ → ℝ → ℝ) (t r : ℝ) : ℝ :=
  ricciRR (A t r) (dr A t r) (dr (dr A) t r) (B t r) (dr B t r) r
    + dt (dt B) t r / (2 * A t r) - dt A t r * dt B t r / (4 * A t r ^ 2)
    - dt B t r ^ 2 / (4 * A t r * B t r)

/-- The mixed time-distance part of the curvature: it measures how fast the ruler function
changes in time. Step 1 had no such part. -/
noncomputable def ricciTRc (B : ℝ → ℝ → ℝ) (t r : ℝ) : ℝ := dt B t r / (r * B t r)

/-- The part along the directions around the mass: exactly Piece B's formula at the time `t`. -/
noncomputable def ricciAngc (A B : ℝ → ℝ → ℝ) (t r : ℝ) : ℝ :=
  ricciAng (A t r) (dr A t r) (B t r) (dr B t r) r

/-- "Space is empty at time `t` and distance `r`": all four formulas vanish there. -/
def IsEmptyAt (A B : ℝ → ℝ → ℝ) (t r : ℝ) : Prop :=
  ricciTTc A B t r = 0 ∧ ricciRRc A B t r = 0 ∧ ricciTRc B t r = 0 ∧ ricciAngc A B t r = 0

/-! ## The curvature, part by part -/

/-- The conditions under which the computation makes sense at the point `x`: away from the centre
and the poles, clock and ruler function not zero there, and both twice smoothly differentiable
around it. -/
structure Regular2 (A B : ℝ → ℝ → ℝ) (x : Coords 4) : Prop where
  r_ne : x 1 ≠ 0
  sin_ne : sin (x 2) ≠ 0
  A_ne : A (x 0) (x 1) ≠ 0
  B_ne : B (x 0) (x 1) ≠ 0
  smoothA : TwiceSmooth A (x 0) (x 1)
  smoothB : TwiceSmooth B (x 0) (x 1)

theorem ricci_changing_tt {A B : ℝ → ℝ → ℝ} {x : Coords 4} (h : Regular2 A B x) :
    ricci (changingΓ A B) 0 0 x = ricciTTc A B (x 0) (x 1) := by
  have hr := h.r_ne
  have hs := h.sin_ne
  have hA0 := h.A_ne
  have hB0 := h.B_ne
  have d1 := dr_half h.smoothA.slopeRR h.smoothB.slopeR hB0
  have d2 := dt_half h.smoothB.slopeTT h.smoothB.slopeT hB0
  simp only [ricci, Fin.sum_univ_four, slope_changingΓ_t, slope_changingΓ_r, slope_changingΓ_θ,
    slope_changingΓ_φ, changingΓ_apply]
  conv_lhs => simp [trPart, θPart, dt_onlyR, dr_onlyR, deriv_constOne, deriv_constZero, constOne,
    constZero, onlyR, d1, d2]
  simp only [half, uF, oneθ, ricciTTc, ricciTT]
  field_simp
  ring

theorem ricci_changing_rr {A B : ℝ → ℝ → ℝ} {x : Coords 4} (h : Regular2 A B x) :
    ricci (changingΓ A B) 1 1 x = ricciRRc A B (x 0) (x 1) := by
  have hr := h.r_ne
  have hs := h.sin_ne
  have hA0 := h.A_ne
  have hB0 := h.B_ne
  have d1 := dt_half h.smoothB.slopeTT h.smoothA.slopeT hA0
  have d2 := dr_half h.smoothA.slopeRR h.smoothA.slopeR hA0
  have dU := (hasDerivAt_uF hr).deriv
  simp only [ricci, Fin.sum_univ_four, slope_changingΓ_t, slope_changingΓ_r, slope_changingΓ_θ,
    slope_changingΓ_φ, changingΓ_apply]
  conv_lhs => simp [trPart, θPart, dt_onlyR, dr_onlyR, deriv_constOne, deriv_constZero, constOne,
    constZero, onlyR, d1, d2, dU]
  simp only [half, uF, oneθ, ricciRRc, ricciRR]
  field_simp
  ring

theorem ricci_changing_tr {A B : ℝ → ℝ → ℝ} {x : Coords 4} (h : Regular2 A B x) :
    ricci (changingΓ A B) 0 1 x = ricciTRc B (x 0) (x 1) := by
  have hr := h.r_ne
  have hs := h.sin_ne
  have hA0 := h.A_ne
  have hB0 := h.B_ne
  have d1 := dt_half h.smoothA.slopeRT h.smoothA.slopeT hA0
  have d2 := dr_half h.smoothA.slopeTR h.smoothA.slopeR hA0
  have hsw := h.smoothA.swap
  simp only [ricci, Fin.sum_univ_four, slope_changingΓ_t, slope_changingΓ_r, slope_changingΓ_θ,
    slope_changingΓ_φ, changingΓ_apply]
  conv_lhs => simp [trPart, θPart, dt_onlyR, dr_onlyR, deriv_constOne, deriv_constZero, constOne,
    constZero, onlyR, d1, d2]
  rw [hsw]
  simp only [half, uF, oneθ, ricciTRc]
  field_simp
  ring

theorem ricci_changing_rt {A B : ℝ → ℝ → ℝ} {x : Coords 4} (h : Regular2 A B x) :
    ricci (changingΓ A B) 1 0 x = ricciTRc B (x 0) (x 1) := by
  have hr := h.r_ne
  have hs := h.sin_ne
  have hA0 := h.A_ne
  have hB0 := h.B_ne
  have d1 := dr_half h.smoothB.slopeTR h.smoothB.slopeR hB0
  have d2 := dt_half h.smoothB.slopeRT h.smoothB.slopeT hB0
  have hsw := h.smoothB.swap
  simp only [ricci, Fin.sum_univ_four, slope_changingΓ_t, slope_changingΓ_r, slope_changingΓ_θ,
    slope_changingΓ_φ, changingΓ_apply]
  conv_lhs => simp [trPart, θPart, dt_onlyR, dr_onlyR, deriv_constOne, deriv_constZero, constOne,
    constZero, onlyR, d1, d2]
  rw [hsw]
  simp only [half, uF, oneθ, ricciTRc]
  field_simp
  ring

theorem ricci_changing_θθ {A B : ℝ → ℝ → ℝ} {x : Coords 4} (h : Regular2 A B x) :
    ricci (changingΓ A B) 2 2 x = ricciAngc A B (x 0) (x 1) := by
  have hr := h.r_ne
  have hs := h.sin_ne
  have hA0 := h.A_ne
  have hB0 := h.B_ne
  have dS := dr_sF2 h.smoothB.slopeR hB0
  have dcot := (hasDerivAt_cotF hs).deriv
  simp only [ricci, Fin.sum_univ_four, slope_changingΓ_t, slope_changingΓ_r, slope_changingΓ_θ,
    slope_changingΓ_φ, changingΓ_apply]
  conv_lhs => simp [trPart, θPart, dt_onlyR, dr_onlyR, deriv_constOne, deriv_constZero, constOne,
    constZero, onlyR, dS, dcot]
  simp only [half, sF2, uF, oneR, oneθ, cotF, ricciAngc, ricciAng]
  field_simp
  ring

theorem ricci_changing_φφ {A B : ℝ → ℝ → ℝ} {x : Coords 4} (h : Regular2 A B x) :
    ricci (changingΓ A B) 3 3 x = sin (x 2) ^ 2 * ricciAngc A B (x 0) (x 1) := by
  have hr := h.r_ne
  have hs := h.sin_ne
  have hA0 := h.A_ne
  have hB0 := h.B_ne
  have dS := dr_sF2 h.smoothB.slopeR hB0
  have dsc := (hasDerivAt_scF (x 2)).deriv
  simp only [ricci, Fin.sum_univ_four, slope_changingΓ_t, slope_changingΓ_r, slope_changingΓ_θ,
    slope_changingΓ_φ, changingΓ_apply]
  conv_lhs => simp [trPart, θPart, dt_onlyR, dr_onlyR, deriv_constOne, deriv_constZero, constOne,
    constZero, onlyR, dS, dsc]
  simp only [half, sF2, uF, oneR, oneθ, sin2, scF, cotF, ricciAngc, ricciAng]
  field_simp
  ring

/-- The mixed part "distance, pole angle" of the curvature vanishes. -/
theorem ricci_changing_rθ (A B : ℝ → ℝ → ℝ) {x : Coords 4} (hr : x 1 ≠ 0) (hs : sin (x 2) ≠ 0) :
    ricci (changingΓ A B) 1 2 x = 0 := by
  have d1 := (hasDerivAt_oneθ hs).deriv
  simp only [ricci, Fin.sum_univ_four, slope_changingΓ_t, slope_changingΓ_r, slope_changingΓ_θ,
    slope_changingΓ_φ, changingΓ_apply]
  conv_lhs => simp [trPart, θPart, dt_onlyR, dr_onlyR, deriv_constOne, deriv_constZero, constOne,
    constZero, onlyR, d1]
  simp only [uF, oneR, oneθ, cotF]
  field_simp
  ring

/-- The mixed part "pole angle, distance" of the curvature vanishes. -/
theorem ricci_changing_θr (A B : ℝ → ℝ → ℝ) {x : Coords 4} (hr : x 1 ≠ 0) (hs : sin (x 2) ≠ 0) :
    ricci (changingΓ A B) 2 1 x = 0 := by
  have d1 := (hasDerivAt_oneR hr).deriv
  simp only [ricci, Fin.sum_univ_four, slope_changingΓ_t, slope_changingΓ_r, slope_changingΓ_θ,
    slope_changingΓ_φ, changingΓ_apply]
  conv_lhs => simp [trPart, θPart, dt_onlyR, dr_onlyR, deriv_constOne, deriv_constZero, constOne,
    constZero, onlyR, d1]
  simp only [uF, oneR, oneθ, cotF]
  field_simp
  ring

/-- Every mixed part of the curvature other than time-distance vanishes. -/
theorem ricci_changing_offdiag (A B : ℝ → ℝ → ℝ) {x : Coords 4} (hr : x 1 ≠ 0)
    (hs : sin (x 2) ≠ 0) {i j : Fin 4} (hij : i ≠ j) (h01 : ¬(i = 0 ∧ j = 1))
    (h10 : ¬(i = 1 ∧ j = 0)) : ricci (changingΓ A B) i j x = 0 := by
  by_cases h12 : i = 1 ∧ j = 2
  · obtain ⟨rfl, rfl⟩ := h12
    exact ricci_changing_rθ A B hr hs
  by_cases h21 : i = 2 ∧ j = 1
  · obtain ⟨rfl, rfl⟩ := h21
    exact ricci_changing_θr A B hr hs
  fin_cases i <;> fin_cases j <;>
    simp [ricci, Fin.sum_univ_four, slope_changingΓ_t, slope_changingΓ_r, slope_changingΓ_θ,
      slope_changingΓ_φ, changingΓ_apply, trPart, θPart, dt_onlyR, dr_onlyR, deriv_constOne,
      deriv_constZero, constOne, constZero, onlyR] at hij h01 h10 h12 h21 ⊢

/-! ## The result -/

/-- **Step 2, the curvature.** For a round space-time that may change in time, Einstein's
equation for empty space (all sixteen parts of the curvature vanish) holds at a point exactly when
the four formulas `ricciTTc`, `ricciRRc`, `ricciTRc` and `ricciAngc` vanish there. -/
theorem changing_ricciFlat_iff {A B : ℝ → ℝ → ℝ} {x : Coords 4} (h : Regular2 A B x) :
    IsRicciFlatAt (changingG A B) (changingGinv A B) x ↔ IsEmptyAt A B (x 0) (x 1) := by
  unfold IsRicciFlatAt IsEmptyAt
  rw [christoffel_changing_eq]
  constructor
  · intro hf
    exact ⟨(ricci_changing_tt h).symm.trans (hf 0 0), (ricci_changing_rr h).symm.trans (hf 1 1),
      (ricci_changing_tr h).symm.trans (hf 0 1), (ricci_changing_θθ h).symm.trans (hf 2 2)⟩
  · rintro ⟨h0, h1, h01, h2⟩ i j
    by_cases hij : i = j
    · subst hij
      fin_cases i
      · exact (ricci_changing_tt h).trans h0
      · exact (ricci_changing_rr h).trans h1
      · exact (ricci_changing_θθ h).trans h2
      · exact (ricci_changing_φφ h).trans (by rw [h2, mul_zero])
    · by_cases ha : i = 0 ∧ j = 1
      · obtain ⟨rfl, rfl⟩ := ha
        exact (ricci_changing_tr h).trans h01
      by_cases hb : i = 1 ∧ j = 0
      · obtain ⟨rfl, rfl⟩ := hb
        exact (ricci_changing_rt h).trans h01
      exact ricci_changing_offdiag A B h.r_ne h.sin_ne hij ha hb

/-- `changingGinv` really is the inverse of `changingG` wherever the conditions hold. -/
theorem changingG_mul_changingGinv {A B : ℝ → ℝ → ℝ} {x : Coords 4} (h : Regular2 A B x)
    (i k : Fin 4) :
    ∑ j, changingG A B i j x * changingGinv A B j k x = if i = k then 1 else 0 := by
  have hr := h.r_ne
  have hs := h.sin_ne
  have hA0 := h.A_ne
  have hB0 := h.B_ne
  fin_cases i <;> fin_cases k <;>
    simp [changingG, changingGinv, diag, changingDiag, sep2, gtr, gθ, negA, onlyR, sqF, sin2,
      constOne, hr, hA0, hB0]
  field_simp

/-- Step 1 is the special case: when the clock and ruler functions do not depend on time, the
length measure here is the one of step 1. -/
theorem changingG_static (a b : ℝ → ℝ) :
    changingG (fun _ r => a r) (fun _ r => b r) = roundG a b := by
  funext i j x
  fin_cases i <;> fin_cases j <;>
    simp [changingG, roundG, diag, changingDiag, roundDiag, sep2, sep, gtr, gr, gθ, negA, negF,
      onlyR]

end GravityInLean
