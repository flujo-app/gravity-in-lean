/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.RoundChanging

import Mathlib.Tactic

/-!
# The general round shape

Steps 1 and 2 started from a length measure with only a clock function and a ruler function. That
shape is a choice of coordinates. This file starts one step earlier, from the most general length
measure that looks the same from every side:

`-A dt² + 2C dt dρ + B dρ² + S (dθ² + sin²θ dφ²)`

with four free functions of the time `t` and the distance label `ρ`:

* `A`, `B`, `C`: how time and distance are measured, including a cross term `C` between them;
* `S`: the size of the sphere at `(t, ρ)`. Its surface is `4π S`, so `√S` is its radius.

Steps 1 and 2 are the special case `C = 0`, `S = ρ²`. That this shape is all that symmetry allows
is proved in `Symmetry.lean`.

**What is proved here.**

* `christoffel_gen`: the general formula for the connection, applied to this length measure, gives
  the table `genΓ` written out below (23 of its 64 entries are not zero). No conditions.
* `genG_mul_genGinv`: `genGinv` really is the inverse of `genG`.
* `genG_diagonal`: with `C = 0` and `S = ρ²` this is the length measure of step 2.
-/

@[expose] public section

namespace GravityInLean

open Real Filter Topology

/-! ## The length measure -/

/-- `A B + C²`: minus the determinant of the time-distance part. It is positive exactly when that
part has one time direction and one space direction. -/
noncomputable def det2 (A B C : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ := A t ρ * B t ρ + C t ρ * C t ρ

/-- The time-and-distance part of each entry of the length measure. -/
noncomputable def gTR (A B C S : ℝ → ℝ → ℝ) (i j : Fin 4) : ℝ → ℝ → ℝ :=
  if i = 0 ∧ j = 0 then negA A
  else if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then C
  else if i = 1 ∧ j = 1 then B
  else if (i = 2 ∧ j = 2) ∨ (i = 3 ∧ j = 3) then S
  else zero2

/-- The pole-angle part of each entry of the length measure. -/
noncomputable def gΘ (i j : Fin 4) : ℝ → ℝ := if i = 3 ∧ j = 3 then sin2 else constOne

/-- The general round length measure `-A dt² + 2C dt dρ + B dρ² + S (dθ² + sin²θ dφ²)`. -/
noncomputable def genG (A B C S : ℝ → ℝ → ℝ) (i j : Fin 4) : Coords 4 → ℝ :=
  sep2 (gTR A B C S i j) (gΘ i j)

/-- The time-and-distance part of each entry of the inverse. -/
noncomputable def ginvTR (A B C S : ℝ → ℝ → ℝ) (i j : Fin 4) : ℝ → ℝ → ℝ :=
  if i = 0 ∧ j = 0 then fun t ρ => -B t ρ / det2 A B C t ρ
  else if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then fun t ρ => C t ρ / det2 A B C t ρ
  else if i = 1 ∧ j = 1 then fun t ρ => A t ρ / det2 A B C t ρ
  else if (i = 2 ∧ j = 2) ∨ (i = 3 ∧ j = 3) then fun t ρ => (S t ρ)⁻¹
  else zero2

/-- The pole-angle part of each entry of the inverse. -/
noncomputable def ginvΘ (i j : Fin 4) : ℝ → ℝ :=
  if i = 3 ∧ j = 3 then fun θ => (sin θ ^ 2)⁻¹ else constOne

/-- The inverse of the general round length measure. -/
noncomputable def genGinv (A B C S : ℝ → ℝ → ℝ) (i j : Fin 4) : Coords 4 → ℝ := fun x =>
  ginvTR A B C S i j (x 0) (x 1) * ginvΘ i j (x 2)

/-- `genGinv` really is the inverse of `genG`, wherever the time-distance part is not degenerate
and away from the centre and the poles. -/
theorem genG_mul_genGinv {A B C S : ℝ → ℝ → ℝ} {x : Coords 4}
    (hD : det2 A B C (x 0) (x 1) ≠ 0) (hS : S (x 0) (x 1) ≠ 0) (hs : sin (x 2) ≠ 0)
    (i k : Fin 4) :
    ∑ j, genG A B C S i j x * genGinv A B C S j k x = if i = k then 1 else 0 := by
  have hdet : det2 A B C (x 0) (x 1)
      = A (x 0) (x 1) * B (x 0) (x 1) + C (x 0) (x 1) * C (x 0) (x 1) := rfl
  fin_cases i <;> fin_cases k <;>
    simp +decide only [genG, genGinv, sep2, gTR, gΘ, ginvTR, ginvΘ, negA, zero2, sin2, constOne,
      Fin.sum_univ_four, ite_true, ite_false] <;>
    field_simp <;>
    linarith [hdet]

/-- The other way round as well. -/
theorem genGinv_mul_genG {A B C S : ℝ → ℝ → ℝ} {x : Coords 4}
    (hD : det2 A B C (x 0) (x 1) ≠ 0) (hS : S (x 0) (x 1) ≠ 0) (hs : sin (x 2) ≠ 0)
    (i k : Fin 4) :
    ∑ j, genGinv A B C S i j x * genG A B C S j k x = if i = k then 1 else 0 := by
  have hdet : det2 A B C (x 0) (x 1)
      = A (x 0) (x 1) * B (x 0) (x 1) + C (x 0) (x 1) * C (x 0) (x 1) := rfl
  fin_cases i <;> fin_cases k <;>
    simp +decide only [genG, genGinv, sep2, gTR, gΘ, ginvTR, ginvΘ, negA, zero2, sin2, constOne,
      Fin.sum_univ_four, ite_true, ite_false] <;>
    field_simp <;>
    linarith [hdet]

/-- Steps 1 and 2 are the special case without a cross term and with the distance label chosen as
the radius of the spheres. -/
theorem genG_diagonal (A B : ℝ → ℝ → ℝ) :
    genG A B zero2 (onlyR sqF) = changingG A B := by
  funext i j x
  fin_cases i <;> fin_cases j <;>
    simp [genG, changingG, diag, changingDiag, sep2, gTR, gΘ, gtr, gθ, zero2]

/-! ## The pieces of the connection

Every entry of the connection is one of these functions of time and distance, times a function of
the pole angle. The first six belong to the time-distance part alone. -/

/-- Numerator of the connection entry "time; time, time". -/
noncomputable def n000 (A B C : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ :=
  B t ρ * dt A t ρ + C t ρ * (2 * dt C t ρ + dr A t ρ)

/-- Numerator of the connection entry "time; time, distance". -/
noncomputable def n001 (A B C : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ :=
  B t ρ * dr A t ρ + C t ρ * dt B t ρ

/-- Numerator of the connection entry "time; distance, distance". -/
noncomputable def n011 (B C : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ :=
  C t ρ * dr B t ρ - B t ρ * (2 * dr C t ρ - dt B t ρ)

/-- Numerator of the connection entry "distance; time, time". -/
noncomputable def n100 (A C : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ :=
  A t ρ * (2 * dt C t ρ + dr A t ρ) - C t ρ * dt A t ρ

/-- Numerator of the connection entry "distance; time, distance". -/
noncomputable def n101 (A B C : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ :=
  A t ρ * dt B t ρ - C t ρ * dr A t ρ

/-- Numerator of the connection entry "distance; distance, distance". -/
noncomputable def n111 (A B C : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ :=
  A t ρ * dr B t ρ + C t ρ * (2 * dr C t ρ - dt B t ρ)

/-- Numerator of the connection entry "time; angle, angle". -/
noncomputable def m0 (B C S : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ :=
  B t ρ * dt S t ρ - C t ρ * dr S t ρ

/-- Numerator of the connection entry "distance; angle, angle". -/
noncomputable def m1 (A C S : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ :=
  -(C t ρ * dt S t ρ + A t ρ * dr S t ρ)

/-- The number 1, in the form the general formula hands it over: `S / S`. -/
noncomputable def oneS (S : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ := (S t ρ)⁻¹ * S t ρ

/-! ## The connection, written out -/

/-- The time-and-distance part of each entry of the connection. -/
noncomputable def trPartG (A B C S : ℝ → ℝ → ℝ) (a b c : Fin 4) : ℝ → ℝ → ℝ :=
  if a = 0 ∧ b = 0 ∧ c = 0 then half (n000 A B C) (det2 A B C)
  else if a = 0 ∧ ((b = 0 ∧ c = 1) ∨ (b = 1 ∧ c = 0)) then half (n001 A B C) (det2 A B C)
  else if a = 0 ∧ b = 1 ∧ c = 1 then half (n011 B C) (det2 A B C)
  else if a = 1 ∧ b = 0 ∧ c = 0 then half (n100 A C) (det2 A B C)
  else if a = 1 ∧ ((b = 0 ∧ c = 1) ∨ (b = 1 ∧ c = 0)) then half (n101 A B C) (det2 A B C)
  else if a = 1 ∧ b = 1 ∧ c = 1 then half (n111 A B C) (det2 A B C)
  else if a = 0 ∧ ((b = 2 ∧ c = 2) ∨ (b = 3 ∧ c = 3)) then half (m0 B C S) (det2 A B C)
  else if a = 1 ∧ ((b = 2 ∧ c = 2) ∨ (b = 3 ∧ c = 3)) then half (m1 A C S) (det2 A B C)
  else if (a = 2 ∧ ((b = 0 ∧ c = 2) ∨ (b = 2 ∧ c = 0)))
      ∨ (a = 3 ∧ ((b = 0 ∧ c = 3) ∨ (b = 3 ∧ c = 0))) then half (dt S) S
  else if (a = 2 ∧ ((b = 1 ∧ c = 2) ∨ (b = 2 ∧ c = 1)))
      ∨ (a = 3 ∧ ((b = 1 ∧ c = 3) ∨ (b = 3 ∧ c = 1))) then half (dr S) S
  else if (a = 2 ∧ b = 3 ∧ c = 3) ∨ (a = 3 ∧ ((b = 2 ∧ c = 3) ∨ (b = 3 ∧ c = 2))) then oneS S
  else zero2

/-- The pole-angle part of each entry of the connection. -/
noncomputable def θPartG (a b c : Fin 4) : ℝ → ℝ :=
  if (a = 0 ∨ a = 1) ∧ b = 3 ∧ c = 3 then sin2
  else if a = 2 ∧ b = 3 ∧ c = 3 then scF
  else if a = 3 ∧ ((b = 0 ∧ c = 3) ∨ (b = 3 ∧ c = 0) ∨ (b = 1 ∧ c = 3) ∨ (b = 3 ∧ c = 1)) then oneθ
  else if a = 3 ∧ ((b = 2 ∧ c = 3) ∨ (b = 3 ∧ c = 2)) then cotF
  else constOne

/-- The connection of the general round shape, written out. -/
noncomputable def genΓ (A B C S : ℝ → ℝ → ℝ) (a b c : Fin 4) : Coords 4 → ℝ :=
  sep2 (trPartG A B C S a b c) (θPartG a b c)

theorem genΓ_apply (A B C S : ℝ → ℝ → ℝ) (a b c : Fin 4) (x : Coords 4) :
    genΓ A B C S a b c x = trPartG A B C S a b c (x 0) (x 1) * θPartG a b c (x 2) := rfl

theorem slope_genΓ_t (A B C S : ℝ → ℝ → ℝ) (a b c : Fin 4) (x : Coords 4) :
    slope 0 (genΓ A B C S a b c) x
      = dt (trPartG A B C S a b c) (x 0) (x 1) * θPartG a b c (x 2) :=
  slope_sep2_t _ _ x

theorem slope_genΓ_r (A B C S : ℝ → ℝ → ℝ) (a b c : Fin 4) (x : Coords 4) :
    slope 1 (genΓ A B C S a b c) x
      = dr (trPartG A B C S a b c) (x 0) (x 1) * θPartG a b c (x 2) :=
  slope_sep2_r _ _ x

theorem slope_genΓ_θ (A B C S : ℝ → ℝ → ℝ) (a b c : Fin 4) (x : Coords 4) :
    slope 2 (genΓ A B C S a b c) x
      = trPartG A B C S a b c (x 0) (x 1) * deriv (θPartG a b c) (x 2) :=
  slope_sep2_θ _ _ x

theorem slope_genΓ_φ (A B C S : ℝ → ℝ → ℝ) (a b c : Fin 4) (x : Coords 4) :
    slope 3 (genΓ A B C S a b c) x = 0 := slope_sep2_φ _ _ x

/-- **The connection.** The general formula, applied to the general round length measure, gives
exactly the table `genΓ`, at every point and for all four functions. -/
theorem christoffel_gen (A B C S : ℝ → ℝ → ℝ) (a b c : Fin 4) (x : Coords 4) :
    christoffel (genG A B C S) (genGinv A B C S) a b c x = genΓ A B C S a b c x := by
  simp only [christoffel, Fin.sum_univ_four]
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    (conv_lhs =>
      simp [genGinv, ginvTR, ginvΘ, genG, slope_sep2_t, slope_sep2_r, slope_sep2_θ,
        slope_sep2_φ, gTR, gΘ, dt_negA, dr_negA, dt_zero2, dr_zero2, deriv_sin2, deriv_constOne,
        negA, zero2, sin2, constOne]) <;>
    (conv_rhs =>
      simp [genΓ_apply, trPartG, θPartG, half, n000, n001, n011, n100, n101, n111, m0, m1, oneS,
        scF, cotF, oneθ, sin2, constOne, zero2]) <;>
    ring

/-- The same as an equality of whole tables. -/
theorem christoffel_gen_eq (A B C S : ℝ → ℝ → ℝ) :
    christoffel (genG A B C S) (genGinv A B C S) = genΓ A B C S := by
  funext a b c x
  exact christoffel_gen A B C S a b c x

end GravityInLean
