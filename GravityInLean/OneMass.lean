/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import GravityInLean.ClockRate

import Mathlib.Tactic

/-!
# Piece B: Schwarzschild's solution really does solve the equations for empty space

Around one heavy mass that sits still and does not spin, everything looks the same at all times and
from every side. Space and time can then be described by just two functions of the distance `r`
(the "circle" distance of Piece A):

* `A r`: how fast clocks run there, squared;
* `B r`: how much a ruler pointing at the mass is stretched, squared.

Einstein's equations for empty space say that a certain measure of curvature (the Ricci tensor)
is zero. For this simple, round and unchanging situation that tensor has only three independent
parts, and each is an ordinary formula in `A`, `B` and their slopes. They are `ricciTT`, `ricciRR`
and `ricciAng` below.

**What is proved here:** Schwarzschild's functions `A = 1 - 2M/r`, `B = 1/(1 - 2M/r)` make all three
parts vanish at every distance outside the rim (`r > 2M`).

**What is NOT proved here (the gap):** that Einstein's full equations, written for a general
space-time, come down to exactly these three formulas in the round, unchanging case. That step is
taken from the textbooks. It cannot yet be checked by machine in a standard way, because the
standard library (mathlib) has no curvature for space-times. Closing this gap is the first rung
of the plan.
-/

@[expose] public section

namespace GravityInLean

open Filter Topology

/-! ## The three parts of the curvature, as formulas -/

/-- The time-time part of the curvature of a round, unchanging space-time
`-A dt² + B dr² + r² (dθ² + sin² θ dφ²)`, given the values of `A`, its first and second slope,
`B` and its slope, at distance `r`. -/
noncomputable def ricciTT (A A' A'' B B' r : ℝ) : ℝ :=
  A'' / (2 * B) - A' ^ 2 / (4 * A * B) - A' * B' / (4 * B ^ 2) + A' / (r * B)

/-- The distance-distance part of the same curvature. -/
noncomputable def ricciRR (A A' A'' B B' r : ℝ) : ℝ :=
  -A'' / (2 * A) + A' ^ 2 / (4 * A ^ 2) + A' * B' / (4 * A * B) + B' / (r * B)

/-- The part of the same curvature along the directions around the mass. -/
noncomputable def ricciAng (A A' B B' r : ℝ) : ℝ :=
  1 - 1 / B + r * B' / (2 * B ^ 2) - r * A' / (2 * A * B)

/-- "Space is empty at distance `r`": all three parts of the curvature vanish there,
for the functions `A` and `B`. -/
def IsEmptySpaceAt (A B : ℝ → ℝ) (r : ℝ) : Prop :=
  ricciTT (A r) (deriv A r) (deriv (deriv A) r) (B r) (deriv B r) r = 0 ∧
  ricciRR (A r) (deriv A r) (deriv (deriv A) r) (B r) (deriv B r) r = 0 ∧
  ricciAng (A r) (deriv A r) (B r) (deriv B r) r = 0

/-! ## Schwarzschild's two functions and their slopes -/

/-- Schwarzschild's clock function: `A = 1 - 2M/r`. -/
noncomputable def schwA (M r : ℝ) : ℝ := 1 - 2 * M / r

/-- Schwarzschild's ruler function: `B = 1 / (1 - 2M/r)`. -/
noncomputable def schwB (M r : ℝ) : ℝ := (1 - 2 * M / r)⁻¹

/-- The slope of `A`: `2M / r²`. -/
theorem hasDerivAt_schwA (M : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (schwA M) (2 * M / r ^ 2) r := by
  have h := ((hasDerivAt_inv hr).const_mul (2 * M)).const_sub 1
  convert h using 1
  · funext y; simp [schwA, div_eq_mul_inv]
  · ring

/-- The slope of the slope of `A`: `-4M / r³`. -/
theorem hasDerivAt_deriv_schwA (M : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (deriv (schwA M)) (-4 * M / r ^ 3) r := by
  have hev : deriv (schwA M) =ᶠ[𝓝 r] fun x => 2 * M / x ^ 2 := by
    filter_upwards [isOpen_ne.mem_nhds hr] with x hx
    exact (hasDerivAt_schwA M hx).deriv
  have h : HasDerivAt (fun x : ℝ => 2 * M / x ^ 2) (-4 * M / r ^ 3) r := by
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by simpa using hasDerivAt_pow 2 r
    have h2 := (h1.inv (pow_ne_zero 2 hr)).const_mul (2 * M)
    convert h2 using 1
    · funext x; simp [div_eq_mul_inv]
    · field_simp
      ring
  exact h.congr_of_eventuallyEq hev

/-- The slope of `B`. -/
theorem hasDerivAt_schwB (M : ℝ) {r : ℝ} (hr : r ≠ 0) (hh : 1 - 2 * M / r ≠ 0) :
    HasDerivAt (schwB M) (-(2 * M / r ^ 2) / (1 - 2 * M / r) ^ 2) r :=
  (hasDerivAt_schwA M hr).inv hh

/-! ## The result -/

/-- **Piece B.** Outside the rim, Schwarzschild's functions make every part of the curvature
vanish: they describe empty space around one mass. -/
theorem schwarzschild_isEmptySpace (M : ℝ) {r : ℝ} (hr : 0 < r) (hrim : 2 * M < r) :
    IsEmptySpaceAt (schwA M) (schwB M) r := by
  have hr0 : r ≠ 0 := hr.ne'
  have hpos : 0 < 1 - 2 * M / r := by rw [sub_pos, div_lt_one hr]; exact hrim
  have hh : 1 - 2 * M / r ≠ 0 := hpos.ne'
  have hne : r - 2 * M ≠ 0 := (sub_pos.mpr hrim).ne'
  have dA := (hasDerivAt_schwA M hr0).deriv
  have ddA := (hasDerivAt_deriv_schwA M hr0).deriv
  have dB := (hasDerivAt_schwB M hr0 hh).deriv
  unfold IsEmptySpaceAt
  rw [dA, ddA, dB]
  refine ⟨?_, ?_, ?_⟩
  · simp only [ricciTT, schwA, schwB]
    field_simp
    ring
  · simp only [ricciRR, schwA, schwB]
    field_simp
    ring
  · simp only [ricciAng, schwA, schwB]
    field_simp
    ring

/-- The link to Piece A: Schwarzschild's clock function is the textbook clock rate, squared. -/
theorem schwA_eq_clockRate_sq (M : ℝ) {r : ℝ} (hr : 0 < r) (hrim : 2 * M < r) :
    schwA M r = clockRateTextbook M r ^ 2 := by
  have hpos : 0 < 1 - 2 * M / r := by rw [sub_pos, div_lt_one hr]; exact hrim
  unfold schwA clockRateTextbook
  rw [Real.sq_sqrt hpos.le]

/-- Clock function times ruler function is exactly 1 for Schwarzschild's solution. -/
theorem schwA_mul_schwB (M : ℝ) {r : ℝ} (hr : 0 < r) (hrim : 2 * M < r) :
    schwA M r * schwB M r = 1 := by
  have hpos : 0 < 1 - 2 * M / r := by rw [sub_pos, div_lt_one hr]; exact hrim
  unfold schwA schwB
  exact mul_inv_cancel₀ hpos.ne'

end GravityInLean
