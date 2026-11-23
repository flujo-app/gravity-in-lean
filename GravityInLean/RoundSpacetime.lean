/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import GravityInLean.Curvature
public import GravityInLean.OneMass

import Mathlib.Tactic

/-!
# Step 1: the round space-time, from the definitions

Piece B took three curvature formulas out of textbooks. This file derives them.

The space-time is the round, unchanging one around a single mass. Its four coordinates are
`x 0 = t` (far time), `x 1 = r` (distance), `x 2 = θ` (angle from the pole) and `x 3 = φ` (angle
around the axis). Lengths in it are measured by

`-A(r) dt² + B(r) dr² + r² dθ² + r² sin²θ dφ²`

with a clock function `A` and a ruler function `B`, both still free.

**What is proved here.**

* `christoffel_round`: the general formula for the connection, applied to this length measure,
  gives the table `roundΓ` written out below. No conditions.
* `ricci_roundΓ_tt`, `_rr`, `_θθ`, `_φφ`, `_offdiag`: the general formula for the curvature,
  applied to that connection, gives exactly the three formulas of Piece B (the fourth diagonal
  part is the third one times `sin²θ`), and every mixed part is zero.
* `round_ricciFlat_iff`: so Einstein's equation for empty space, all sixteen parts of it, holds
  at a point exactly when the three formulas of Piece B vanish there.
* `schwarzschild_ricciFlat`: Schwarzschild's space-time is empty in this full sense, everywhere
  outside the rim.

**What is still assumed.** Curvature is *defined* here by the classic coordinate formulas (see
`Curvature.lean`). The poles (`sin θ = 0`) and the centre are left out, as in every textbook that
uses these coordinates.
-/

@[expose] public section

namespace GravityInLean

open Real Filter Topology

/-! ## Functions of the distance and the pole angle -/

/-- A function of the form `f(r) · h(θ)`, seen as a function of all four coordinates. -/
noncomputable def sep (f h : ℝ → ℝ) (x : Coords 4) : ℝ := f (x 1) * h (x 2)

/-- Such a function does not change with time. -/
theorem slope_sep_t (f h : ℝ → ℝ) (x : Coords 4) : slope 0 (sep f h) x = 0 := by
  simp [slope, sep]

/-- Along the distance, only the first factor changes. -/
theorem slope_sep_r (f h : ℝ → ℝ) (x : Coords 4) :
    slope 1 (sep f h) x = deriv f (x 1) * h (x 2) := by
  simp [slope, sep, deriv_mul_const_field]

/-- Along the pole angle, only the second factor changes. -/
theorem slope_sep_θ (f h : ℝ → ℝ) (x : Coords 4) :
    slope 2 (sep f h) x = f (x 1) * deriv h (x 2) := by
  simp [slope, sep, deriv_const_mul_field]

/-- Such a function does not change around the axis. -/
theorem slope_sep_φ (f h : ℝ → ℝ) (x : Coords 4) : slope 3 (sep f h) x = 0 := by
  simp [slope, sep]

/-! ## The named pieces

Every entry of the length measure and of its connection is one of these few functions of `r`,
times one of these few functions of `θ`. -/

/-- The constant function 1. -/
noncomputable def constOne (_ : ℝ) : ℝ := 1

/-- The constant function 0. -/
noncomputable def constZero (_ : ℝ) : ℝ := 0

/-- `-A(r)`. -/
noncomputable def negF (A : ℝ → ℝ) (r : ℝ) : ℝ := -A r

/-- `r²`. -/
noncomputable def sqF (r : ℝ) : ℝ := r ^ 2

/-- `sin²θ`. -/
noncomputable def sin2 (θ : ℝ) : ℝ := sin θ ^ 2

/-- `A' / (2A)`. -/
noncomputable def pF (A : ℝ → ℝ) (r : ℝ) : ℝ := deriv A r / (2 * A r)

/-- `A' / (2B)`. -/
noncomputable def qF (A B : ℝ → ℝ) (r : ℝ) : ℝ := deriv A r / (2 * B r)

/-- `B' / (2B)`. -/
noncomputable def rF (B : ℝ → ℝ) (r : ℝ) : ℝ := deriv B r / (2 * B r)

/-- `-r / B`. -/
noncomputable def sF (B : ℝ → ℝ) (r : ℝ) : ℝ := -r / B r

/-- `1 / r`, in the form the general formula hands it over. -/
noncomputable def uF (r : ℝ) : ℝ := (r ^ 2)⁻¹ * r

/-- The number 1, in the form the general formula hands it over: `r² / r²`. -/
noncomputable def oneR (r : ℝ) : ℝ := (r ^ 2)⁻¹ * r ^ 2

/-- `-sin θ cos θ`. -/
noncomputable def scF (θ : ℝ) : ℝ := -(sin θ * cos θ)

/-- `cos θ / sin θ`, in the form the general formula hands it over. -/
noncomputable def cotF (θ : ℝ) : ℝ := (sin θ ^ 2)⁻¹ * (sin θ * cos θ)

/-- The number 1 again, as `sin²θ / sin²θ`. -/
noncomputable def oneθ (θ : ℝ) : ℝ := (sin θ ^ 2)⁻¹ * sin θ ^ 2

theorem deriv_constOne (s : ℝ) : deriv constOne s = 0 := by
  change deriv (fun _ : ℝ => (1 : ℝ)) s = 0
  simp

theorem deriv_constZero (s : ℝ) : deriv constZero s = 0 := by
  change deriv (fun _ : ℝ => (0 : ℝ)) s = 0
  simp

theorem deriv_negF (A : ℝ → ℝ) (r : ℝ) : deriv (negF A) r = -deriv A r := by
  change deriv (fun y => -A y) r = -deriv A r
  simp

theorem deriv_sqF (r : ℝ) : deriv sqF r = 2 * r := by
  have h : HasDerivAt (fun y : ℝ => y ^ 2) (2 * r) r := by simpa using hasDerivAt_pow 2 r
  exact h.deriv

theorem deriv_sin2 (θ : ℝ) : deriv sin2 θ = 2 * sin θ * cos θ := by
  have hs : HasDerivAt sin (cos θ) θ := Real.hasDerivAt_sin θ
  have h : HasDerivAt (fun t => sin t ^ 2) (2 * sin θ * cos θ) θ := by
    convert HasDerivAt.pow hs 2 using 1
    simp
  exact h.deriv

/-! ## The length measure -/

/-- The `r` part of the four diagonal entries `-A`, `B`, `r²`, `r² sin²θ`. -/
noncomputable def gr (A B : ℝ → ℝ) (i : Fin 4) : ℝ → ℝ :=
  if i = 0 then negF A else if i = 1 then B else sqF

/-- The `θ` part of the four diagonal entries. -/
noncomputable def gθ (i : Fin 4) : ℝ → ℝ := if i = 3 then sin2 else constOne

/-- The four diagonal entries of the length measure. -/
noncomputable def roundDiag (A B : ℝ → ℝ) (i : Fin 4) : Coords 4 → ℝ := sep (gr A B i) (gθ i)

/-- The length measure `-A dt² + B dr² + r² dθ² + r² sin²θ dφ²` of a round, unchanging
space-time. -/
noncomputable def roundG (A B : ℝ → ℝ) : Fin 4 → Fin 4 → Coords 4 → ℝ := diag (roundDiag A B)

/-- Its inverse: one over each diagonal entry. -/
noncomputable def roundGinv (A B : ℝ → ℝ) : Fin 4 → Fin 4 → Coords 4 → ℝ :=
  diag fun i x => (roundDiag A B i x)⁻¹

/-! ## Its connection, written out -/

/-- The `r` part of each entry of the connection. -/
noncomputable def rPart (A B : ℝ → ℝ) (a b c : Fin 4) : ℝ → ℝ :=
  if a = 0 ∧ ((b = 0 ∧ c = 1) ∨ (b = 1 ∧ c = 0)) then pF A
  else if a = 1 ∧ b = 0 ∧ c = 0 then qF A B
  else if a = 1 ∧ b = 1 ∧ c = 1 then rF B
  else if a = 1 ∧ ((b = 2 ∧ c = 2) ∨ (b = 3 ∧ c = 3)) then sF B
  else if (a = 2 ∧ ((b = 1 ∧ c = 2) ∨ (b = 2 ∧ c = 1)))
      ∨ (a = 3 ∧ ((b = 1 ∧ c = 3) ∨ (b = 3 ∧ c = 1))) then uF
  else if (a = 2 ∧ b = 3 ∧ c = 3) ∨ (a = 3 ∧ ((b = 2 ∧ c = 3) ∨ (b = 3 ∧ c = 2))) then oneR
  else constZero

/-- The `θ` part of each entry of the connection. -/
noncomputable def θPart (a b c : Fin 4) : ℝ → ℝ :=
  if a = 1 ∧ b = 3 ∧ c = 3 then sin2
  else if a = 2 ∧ b = 3 ∧ c = 3 then scF
  else if a = 3 ∧ ((b = 1 ∧ c = 3) ∨ (b = 3 ∧ c = 1)) then oneθ
  else if a = 3 ∧ ((b = 2 ∧ c = 3) ∨ (b = 3 ∧ c = 2)) then cotF
  else constOne

/-- The connection of the round space-time, written out. Thirteen of its 64 entries are not
zero. -/
noncomputable def roundΓ (A B : ℝ → ℝ) (a b c : Fin 4) : Coords 4 → ℝ :=
  sep (rPart A B a b c) (θPart a b c)

theorem roundΓ_apply (A B : ℝ → ℝ) (a b c : Fin 4) (x : Coords 4) :
    roundΓ A B a b c x = rPart A B a b c (x 1) * θPart a b c (x 2) := rfl

theorem slope_roundΓ_t (A B : ℝ → ℝ) (a b c : Fin 4) (x : Coords 4) :
    slope 0 (roundΓ A B a b c) x = 0 := slope_sep_t _ _ x

theorem slope_roundΓ_r (A B : ℝ → ℝ) (a b c : Fin 4) (x : Coords 4) :
    slope 1 (roundΓ A B a b c) x = deriv (rPart A B a b c) (x 1) * θPart a b c (x 2) :=
  slope_sep_r _ _ x

theorem slope_roundΓ_θ (A B : ℝ → ℝ) (a b c : Fin 4) (x : Coords 4) :
    slope 2 (roundΓ A B a b c) x = rPart A B a b c (x 1) * deriv (θPart a b c) (x 2) :=
  slope_sep_θ _ _ x

theorem slope_roundΓ_φ (A B : ℝ → ℝ) (a b c : Fin 4) (x : Coords 4) :
    slope 3 (roundΓ A B a b c) x = 0 := slope_sep_φ _ _ x

/-- **The connection.** The general formula, applied to the round length measure, gives exactly
the table `roundΓ`, at every point and for every clock and ruler function. -/
theorem christoffel_round (A B : ℝ → ℝ) (a b c : Fin 4) (x : Coords 4) :
    christoffel (roundG A B) (roundGinv A B) a b c x = roundΓ A B a b c x := by
  simp only [roundGinv, christoffel_diag, roundG, slope_diag]
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    (conv_lhs =>
      simp [roundDiag, sep, slope_sep_t, slope_sep_r, slope_sep_θ, slope_sep_φ, gr, gθ,
        deriv_negF, deriv_sqF, deriv_sin2, deriv_constOne, negF, sqF, sin2, constOne]) <;>
    (conv_rhs =>
      simp [roundΓ_apply, rPart, θPart, pF, qF, rF, sF, uF, oneR, scF, cotF, oneθ, sin2,
        constOne, constZero]) <;>
    ring

/-- The same as an equality of whole tables. -/
theorem christoffel_round_eq (A B : ℝ → ℝ) :
    christoffel (roundG A B) (roundGinv A B) = roundΓ A B := by
  funext a b c x
  exact christoffel_round A B a b c x

/-! ## Slopes of the pieces -/

theorem hasDerivAt_pF {A : ℝ → ℝ} {r : ℝ} (hA : DifferentiableAt ℝ A r)
    (hA' : DifferentiableAt ℝ (deriv A) r) (h0 : A r ≠ 0) :
    HasDerivAt (pF A)
      ((deriv (deriv A) r * (2 * A r) - deriv A r * (2 * deriv A r)) / (2 * A r) ^ 2) r :=
  hA'.hasDerivAt.div (hA.hasDerivAt.const_mul 2) (mul_ne_zero two_ne_zero h0)

theorem hasDerivAt_qF {A B : ℝ → ℝ} {r : ℝ} (hA' : DifferentiableAt ℝ (deriv A) r)
    (hB : DifferentiableAt ℝ B r) (h0 : B r ≠ 0) :
    HasDerivAt (qF A B)
      ((deriv (deriv A) r * (2 * B r) - deriv A r * (2 * deriv B r)) / (2 * B r) ^ 2) r :=
  hA'.hasDerivAt.div (hB.hasDerivAt.const_mul 2) (mul_ne_zero two_ne_zero h0)

theorem hasDerivAt_sF {B : ℝ → ℝ} {r : ℝ} (hB : DifferentiableAt ℝ B r) (h0 : B r ≠ 0) :
    HasDerivAt (sF B) ((-1 * B r - -r * deriv B r) / B r ^ 2) r :=
  (hasDerivAt_id' r).neg.div hB.hasDerivAt h0

theorem hasDerivAt_uF {r : ℝ} (hr : r ≠ 0) : HasDerivAt uF (-(r ^ 2)⁻¹) r := by
  have hev : uF =ᶠ[𝓝 r] fun y => y⁻¹ := by
    filter_upwards [isOpen_ne.mem_nhds hr] with y hy
    change (y ^ 2)⁻¹ * y = y⁻¹
    rw [pow_two, mul_inv, mul_assoc, inv_mul_cancel₀ hy, mul_one]
  exact (hasDerivAt_inv hr).congr_of_eventuallyEq hev

theorem hasDerivAt_oneR {r : ℝ} (hr : r ≠ 0) : HasDerivAt oneR 0 r := by
  have hev : oneR =ᶠ[𝓝 r] fun _ => (1 : ℝ) := by
    filter_upwards [isOpen_ne.mem_nhds hr] with y hy
    change (y ^ 2)⁻¹ * y ^ 2 = 1
    exact inv_mul_cancel₀ (pow_ne_zero 2 hy)
  exact (hasDerivAt_const r (1 : ℝ)).congr_of_eventuallyEq hev

theorem hasDerivAt_oneθ {θ : ℝ} (hs : sin θ ≠ 0) : HasDerivAt oneθ 0 θ := by
  have hev : oneθ =ᶠ[𝓝 θ] fun _ => (1 : ℝ) := by
    filter_upwards [Real.continuous_sin.continuousAt.eventually_ne hs] with y hy
    change (sin y ^ 2)⁻¹ * sin y ^ 2 = 1
    exact inv_mul_cancel₀ (pow_ne_zero 2 hy)
  exact (hasDerivAt_const θ (1 : ℝ)).congr_of_eventuallyEq hev

theorem hasDerivAt_scF (θ : ℝ) :
    HasDerivAt scF (-(cos θ * cos θ + sin θ * -sin θ)) θ :=
  ((Real.hasDerivAt_sin θ).mul (Real.hasDerivAt_cos θ)).neg

theorem hasDerivAt_cotF {θ : ℝ} (hs : sin θ ≠ 0) :
    HasDerivAt cotF ((-sin θ * sin θ - cos θ * cos θ) / sin θ ^ 2) θ := by
  have hev : cotF =ᶠ[𝓝 θ] fun y => cos y / sin y := by
    filter_upwards [Real.continuous_sin.continuousAt.eventually_ne hs] with y hy
    change (sin y ^ 2)⁻¹ * (sin y * cos y) = cos y / sin y
    field_simp
  exact ((Real.hasDerivAt_cos θ).div (Real.hasDerivAt_sin θ) hs).congr_of_eventuallyEq hev

/-! ## The curvature, part by part -/

/-- The conditions under which the computation makes sense at the point `x`: away from the centre
and the poles, clock and ruler function not zero there, and smooth enough to take the slopes the
curvature needs. The ruler function needs only one slope: its second slope enters the curvature
twice, with opposite signs, and drops out. -/
structure Regular (A B : ℝ → ℝ) (x : Coords 4) : Prop where
  r_ne : x 1 ≠ 0
  sin_ne : sin (x 2) ≠ 0
  A_ne : A (x 1) ≠ 0
  B_ne : B (x 1) ≠ 0
  diffA : DifferentiableAt ℝ A (x 1)
  diffA' : DifferentiableAt ℝ (deriv A) (x 1)
  diffB : DifferentiableAt ℝ B (x 1)

/-- The time-time part of the curvature is the first formula of Piece B. -/
theorem ricci_roundΓ_tt {A B : ℝ → ℝ} {x : Coords 4} (h : Regular A B x) :
    ricci (roundΓ A B) 0 0 x
      = ricciTT (A (x 1)) (deriv A (x 1)) (deriv (deriv A) (x 1)) (B (x 1)) (deriv B (x 1))
          (x 1) := by
  have hr := h.r_ne
  have hs := h.sin_ne
  have hA0 := h.A_ne
  have hB0 := h.B_ne
  have dQ := (hasDerivAt_qF h.diffA' h.diffB hB0).deriv
  simp only [ricci, Fin.sum_univ_four, slope_roundΓ_t, slope_roundΓ_r, slope_roundΓ_θ,
    slope_roundΓ_φ, roundΓ_apply]
  conv_lhs => simp [rPart, θPart, deriv_constOne, deriv_constZero, constOne, constZero, dQ]
  simp only [pF, qF, rF, uF, oneθ, ricciTT]
  field_simp
  ring

/-- The distance-distance part of the curvature is the second formula of Piece B. -/
theorem ricci_roundΓ_rr {A B : ℝ → ℝ} {x : Coords 4} (h : Regular A B x) :
    ricci (roundΓ A B) 1 1 x
      = ricciRR (A (x 1)) (deriv A (x 1)) (deriv (deriv A) (x 1)) (B (x 1)) (deriv B (x 1))
          (x 1) := by
  have hr := h.r_ne
  have hs := h.sin_ne
  have hA0 := h.A_ne
  have hB0 := h.B_ne
  have dP := (hasDerivAt_pF h.diffA h.diffA' hA0).deriv
  have dU := (hasDerivAt_uF hr).deriv
  simp only [ricci, Fin.sum_univ_four, slope_roundΓ_t, slope_roundΓ_r, slope_roundΓ_θ,
    slope_roundΓ_φ, roundΓ_apply]
  conv_lhs => simp [rPart, θPart, deriv_constOne, deriv_constZero, constOne, constZero, dP, dU]
  simp only [pF, rF, uF, oneθ, ricciRR]
  field_simp
  ring

/-- The part of the curvature along the pole angle is the third formula of Piece B. -/
theorem ricci_roundΓ_θθ {A B : ℝ → ℝ} {x : Coords 4} (h : Regular A B x) :
    ricci (roundΓ A B) 2 2 x
      = ricciAng (A (x 1)) (deriv A (x 1)) (B (x 1)) (deriv B (x 1)) (x 1) := by
  have hr := h.r_ne
  have hs := h.sin_ne
  have hA0 := h.A_ne
  have hB0 := h.B_ne
  have dS := (hasDerivAt_sF h.diffB hB0).deriv
  have dcot := (hasDerivAt_cotF hs).deriv
  simp only [ricci, Fin.sum_univ_four, slope_roundΓ_t, slope_roundΓ_r, slope_roundΓ_θ,
    slope_roundΓ_φ, roundΓ_apply]
  conv_lhs => simp [rPart, θPart, deriv_constOne, deriv_constZero, constOne, constZero, dS, dcot]
  simp only [pF, rF, sF, uF, oneR, oneθ, cotF, ricciAng]
  field_simp
  ring

/-- The part of the curvature around the axis is the third formula again, times `sin²θ`. -/
theorem ricci_roundΓ_φφ {A B : ℝ → ℝ} {x : Coords 4} (h : Regular A B x) :
    ricci (roundΓ A B) 3 3 x
      = sin (x 2) ^ 2 * ricciAng (A (x 1)) (deriv A (x 1)) (B (x 1)) (deriv B (x 1)) (x 1) := by
  have hr := h.r_ne
  have hs := h.sin_ne
  have hA0 := h.A_ne
  have hB0 := h.B_ne
  have dS := (hasDerivAt_sF h.diffB hB0).deriv
  have dsc := (hasDerivAt_scF (x 2)).deriv
  simp only [ricci, Fin.sum_univ_four, slope_roundΓ_t, slope_roundΓ_r, slope_roundΓ_θ,
    slope_roundΓ_φ, roundΓ_apply]
  conv_lhs => simp [rPart, θPart, deriv_constOne, deriv_constZero, constOne, constZero, dS, dsc]
  simp only [pF, rF, sF, uF, oneR, oneθ, sin2, scF, cotF, ricciAng]
  field_simp
  ring

/-- The mixed part "distance, pole angle" of the curvature vanishes. -/
theorem ricci_roundΓ_rθ (A B : ℝ → ℝ) {x : Coords 4} (hr : x 1 ≠ 0) (hs : sin (x 2) ≠ 0) :
    ricci (roundΓ A B) 1 2 x = 0 := by
  have d1 := (hasDerivAt_oneθ hs).deriv
  simp only [ricci, Fin.sum_univ_four, slope_roundΓ_t, slope_roundΓ_r, slope_roundΓ_θ,
    slope_roundΓ_φ, roundΓ_apply]
  conv_lhs => simp [rPart, θPart, deriv_constOne, deriv_constZero, constOne, constZero, d1]
  simp only [uF, oneR, oneθ, cotF]
  field_simp
  ring

/-- The mixed part "pole angle, distance" of the curvature vanishes. -/
theorem ricci_roundΓ_θr (A B : ℝ → ℝ) {x : Coords 4} (hr : x 1 ≠ 0) (hs : sin (x 2) ≠ 0) :
    ricci (roundΓ A B) 2 1 x = 0 := by
  have d1 := (hasDerivAt_oneR hr).deriv
  simp only [ricci, Fin.sum_univ_four, slope_roundΓ_t, slope_roundΓ_r, slope_roundΓ_θ,
    slope_roundΓ_φ, roundΓ_apply]
  conv_lhs => simp [rPart, θPart, deriv_constOne, deriv_constZero, constOne, constZero, d1]
  simp only [uF, oneR, oneθ, cotF]
  field_simp
  ring

/-- Every mixed part of the curvature vanishes. -/
theorem ricci_roundΓ_offdiag (A B : ℝ → ℝ) {x : Coords 4} (hr : x 1 ≠ 0) (hs : sin (x 2) ≠ 0)
    {i j : Fin 4} (hij : i ≠ j) : ricci (roundΓ A B) i j x = 0 := by
  by_cases h12 : i = 1 ∧ j = 2
  · obtain ⟨rfl, rfl⟩ := h12
    exact ricci_roundΓ_rθ A B hr hs
  by_cases h21 : i = 2 ∧ j = 1
  · obtain ⟨rfl, rfl⟩ := h21
    exact ricci_roundΓ_θr A B hr hs
  fin_cases i <;> fin_cases j <;>
    simp [ricci, Fin.sum_univ_four, slope_roundΓ_t, slope_roundΓ_r, slope_roundΓ_θ,
      slope_roundΓ_φ, roundΓ_apply, rPart, θPart, deriv_constOne, deriv_constZero, constOne,
      constZero] at hij h12 h21 ⊢

/-! ## The result -/

/-- **Step 1, in general.** For a round, unchanging space-time, Einstein's equation for empty
space (all sixteen parts of the curvature vanish) says exactly that the three formulas of Piece B
vanish. This is the step Piece B had to take on trust. -/
theorem round_ricciFlat_iff {A B : ℝ → ℝ} {x : Coords 4} (h : Regular A B x) :
    IsRicciFlatAt (roundG A B) (roundGinv A B) x ↔ IsEmptySpaceAt A B (x 1) := by
  unfold IsRicciFlatAt IsEmptySpaceAt
  rw [christoffel_round_eq]
  constructor
  · intro hf
    exact ⟨(ricci_roundΓ_tt h).symm.trans (hf 0 0), (ricci_roundΓ_rr h).symm.trans (hf 1 1),
      (ricci_roundΓ_θθ h).symm.trans (hf 2 2)⟩
  · rintro ⟨h0, h1, h2⟩ i j
    by_cases hij : i = j
    · subst hij
      fin_cases i
      · exact (ricci_roundΓ_tt h).trans h0
      · exact (ricci_roundΓ_rr h).trans h1
      · exact (ricci_roundΓ_θθ h).trans h2
      · exact (ricci_roundΓ_φφ h).trans (by rw [h2, mul_zero])
    · exact ricci_roundΓ_offdiag A B h.r_ne h.sin_ne hij

/-- Outside the rim and away from the poles, Schwarzschild's functions meet all the conditions. -/
theorem schwarzschild_regular (M : ℝ) {x : Coords 4} (hr : 0 < x 1) (hrim : 2 * M < x 1)
    (hs : sin (x 2) ≠ 0) : Regular (schwA M) (schwB M) x := by
  have hr0 : x 1 ≠ 0 := hr.ne'
  have hpos : 0 < 1 - 2 * M / x 1 := by rw [sub_pos, div_lt_one hr]; exact hrim
  exact
    { r_ne := hr0
      sin_ne := hs
      A_ne := hpos.ne'
      B_ne := inv_ne_zero hpos.ne'
      diffA := (hasDerivAt_schwA M hr0).differentiableAt
      diffA' := (hasDerivAt_deriv_schwA M hr0).differentiableAt
      diffB := (hasDerivAt_schwB M hr0 hpos.ne').differentiableAt }

/-- **Step 1, the result.** Outside the rim, Schwarzschild's space-time is empty in the full
sense: all sixteen parts of its curvature, computed from the general definitions, vanish. -/
theorem schwarzschild_ricciFlat (M : ℝ) {x : Coords 4} (hr : 0 < x 1) (hrim : 2 * M < x 1)
    (hs : sin (x 2) ≠ 0) :
    IsRicciFlatAt (roundG (schwA M) (schwB M)) (roundGinv (schwA M) (schwB M)) x :=
  (round_ricciFlat_iff (schwarzschild_regular M hr hrim hs)).mpr
    (schwarzschild_isEmptySpace M hr hrim)

/-- `roundGinv` really is the inverse of `roundG` wherever the conditions hold. -/
theorem roundG_mul_roundGinv {A B : ℝ → ℝ} {x : Coords 4} (h : Regular A B x) (i k : Fin 4) :
    ∑ j, roundG A B i j x * roundGinv A B j k x = if i = k then 1 else 0 := by
  have hr := h.r_ne
  have hs := h.sin_ne
  have hA0 := h.A_ne
  have hB0 := h.B_ne
  fin_cases i <;> fin_cases k <;>
    simp [roundG, roundGinv, diag, roundDiag, sep, gr, gθ, negF, sqF, sin2, constOne,
      hr, hA0, hB0]
  field_simp

end GravityInLean
