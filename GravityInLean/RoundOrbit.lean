/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.OneMass

import Mathlib.Tactic

/-!
# Piece C: the clock on a round orbit, and the budget

A small thing circling the heavy mass at a fixed distance `r` is falling freely the whole time.
Two facts describe it. Write `tdot` for how many far seconds pass per second of its own clock, and
`φdot` for how fast it goes round per second of its own clock.

1. Its own clock measures its own time: `A · tdot² - r² · φdot² = 1`.
2. It stays at the same distance while falling freely: `A' · tdot² = 2 r · φdot²`
   (`A'` is the slope of the clock function `A`).

**What is proved here:** from these two facts alone, the clock on the orbit runs at
`√(1 - 3M/r)` of a far clock, and it circles at the rate Kepler found, `(φdot/tdot)² = M/r³`.
This is the formula the page uses for the light mass.

**Where the two facts come from:** this file takes them as given. `FreeFall.lean` then proves
that they are exactly what the general equation of free fall says for a round orbit
(`roundOrbit_isFreeFall_iff`, `roundOrbit_keepsOwnTime_iff`), and states the result once more
without them (`roundOrbit_clockRate_of_freeFall`).

The last theorem is the "budget" that started this whole project: how fast something goes through
time, squared, plus how fast it goes through space, squared, always adds up to the same total.
-/

@[expose] public section

namespace GravityInLean

/-- For any clock function `A` with slope `A'`: the two facts fix the orbit's clock rate. -/
theorem orbit_clockRate_sq {A A' r tdot φdot : ℝ}
    (hown : A * tdot ^ 2 - r ^ 2 * φdot ^ 2 = 1)
    (hfall : A' * tdot ^ 2 = 2 * r * φdot ^ 2) :
    (1 / tdot) ^ 2 = A - r * A' / 2 := by
  have h : (A - r * A' / 2) * tdot ^ 2 = 1 := by linear_combination hown - (r / 2) * hfall
  rw [one_div, inv_pow]
  exact (eq_inv_of_mul_eq_one_left h).symm

/-- **Piece C.** Around Schwarzschild's mass, a clock on a round orbit at distance `r`
runs at `√(1 - 3M/r)` of a far clock. -/
theorem roundOrbit_clockRate {M r tdot φdot : ℝ} (hM : 0 < M) (hr : 3 * M < r) (ht : 0 < tdot)
    (hown : schwA M r * tdot ^ 2 - r ^ 2 * φdot ^ 2 = 1)
    (hfall : 2 * M / r ^ 2 * tdot ^ 2 = 2 * r * φdot ^ 2) :
    1 / tdot = Real.sqrt (1 - 3 * M / r) := by
  have hr0 : 0 < r := by linarith
  have h := orbit_clockRate_sq hown hfall
  have h2 : schwA M r - r * (2 * M / r ^ 2) / 2 = 1 - 3 * M / r := by
    unfold schwA
    field_simp
    ring
  rw [h2] at h
  rw [← h, Real.sqrt_sq (by positivity)]

/-- Kepler's rule, exactly as in Newton's gravity when counted in far seconds:
the square of the rate of going round is `M / r³`. -/
theorem roundOrbit_kepler {M r tdot φdot : ℝ} (hr : 0 < r) (ht : 0 < tdot)
    (hfall : 2 * M / r ^ 2 * tdot ^ 2 = 2 * r * φdot ^ 2) :
    (φdot / tdot) ^ 2 = M / r ^ 3 := by
  have hr0 : r ≠ 0 := hr.ne'
  have ht0 : tdot ≠ 0 := ht.ne'
  have h : M * tdot ^ 2 = r ^ 3 * φdot ^ 2 := by
    field_simp at hfall
    linarith
  rw [div_pow, div_eq_div_iff (pow_ne_zero 2 ht0) (pow_ne_zero 3 hr0)]
  linarith

/-- A round orbit only exists outside `r = 3M`: closer in, the clock rate formula has nothing
left under the square root. (Light itself circles at exactly `r = 3M`.) -/
theorem roundOrbit_needs_room {M r : ℝ} (hr : 0 < r) :
    0 < 1 - 3 * M / r ↔ 3 * M < r := by
  rw [sub_pos, div_lt_one hr]

/-- The two orbit facts can really be met: at every distance outside `r = 3M` there is such an
orbit. So the theorems above are not statements about nothing. -/
theorem roundOrbit_exists {M r : ℝ} (hM : 0 < M) (hr : 3 * M < r) :
    ∃ tdot φdot : ℝ, 0 < tdot ∧
      schwA M r * tdot ^ 2 - r ^ 2 * φdot ^ 2 = 1 ∧
      2 * M / r ^ 2 * tdot ^ 2 = 2 * r * φdot ^ 2 := by
  have hr0 : 0 < r := by linarith
  have hd : 0 < r - 3 * M := by linarith
  have hr' : r ≠ 0 := hr0.ne'
  -- `u` stands for `1 / (r - 3M)`
  obtain ⟨u, hu0, hu⟩ : ∃ u : ℝ, 0 < u ∧ u * (r - 3 * M) = 1 :=
    ⟨(r - 3 * M)⁻¹, inv_pos.mpr hd, inv_mul_cancel₀ hd.ne'⟩
  have h1 : 0 < r * u := mul_pos hr0 hu0
  have h2 : 0 < M * u / r ^ 2 := div_pos (mul_pos hM hu0) (pow_pos hr0 2)
  have e1 : (1 - 2 * M / r) * r = r - 2 * M := by field_simp
  have e2 : r ^ 2 * (M * u / r ^ 2) = M * u := by field_simp
  refine ⟨Real.sqrt (r * u), Real.sqrt (M * u / r ^ 2), Real.sqrt_pos.mpr h1, ?_, ?_⟩
  · rw [Real.sq_sqrt h1.le, Real.sq_sqrt h2.le]
    unfold schwA
    linear_combination u * e1 - e2 + hu
  · rw [Real.sq_sqrt h1.le, Real.sq_sqrt h2.le]
    ring

/-- **The budget.** `N` is the clock rate where you are, `β` your speed as a fraction of light
speed. Your own clock then runs at `N √(1 - β²)`, and you cross space at `N β` (both as a far
observer counts them). Their squares always add up to `N²`: what you spend on moving through
space is missing from your moving through time. -/
theorem budget (N β : ℝ) (hβ : β ^ 2 ≤ 1) :
    (N * Real.sqrt (1 - β ^ 2)) ^ 2 + (N * β) ^ 2 = N ^ 2 := by
  have h : Real.sqrt (1 - β ^ 2) ^ 2 = 1 - β ^ 2 := Real.sq_sqrt (by linarith)
  rw [mul_pow, h]
  ring

/-- Light spends the whole budget on space: at `β = 1` nothing is left for time. -/
theorem budget_light (N : ℝ) : N * Real.sqrt (1 - (1 : ℝ) ^ 2) = 0 := by
  simp

end GravityInLean
