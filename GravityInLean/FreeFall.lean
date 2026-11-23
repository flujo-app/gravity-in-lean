/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import GravityInLean.RoundSpacetime
public import GravityInLean.RoundOrbit

import Mathlib.Tactic

/-!
# Step 1, second half: the round orbit really is free fall

Piece C started from two facts about a round orbit and took them on trust. This file derives them
from the general equation of free fall.

The orbit is a path through the round space-time: it stays at distance `r` in the plane through
the middle (`θ = π/2`), while far time and the angle around both run on at steady rates `tdot`
and `φdot` per second of the orbit's own clock.

**What is proved here.**

* `roundOrbit_isFreeFall_iff`: this path falls freely exactly when fact 2 of Piece C holds.
  Of the four free-fall equations, three hold by themselves and the fourth is fact 2.
* `roundOrbit_keepsOwnTime_iff`: the path is timed by its own clock exactly when fact 1 holds.
* `roundOrbit_clockRate_of_freeFall`: so around Schwarzschild's mass, a clock that falls freely
  on a round orbit runs at `√(1 - 3M/r)` of a far clock. Nothing is taken from a textbook here
  except the definitions themselves.
* `roundOrbit_freeFall_exists`: such free-falling orbits exist at every distance outside `r = 3M`.

**What is still assumed.** Free fall is *defined* by the classic coordinate equation (see
`Curvature.lean`).
-/

@[expose] public section

namespace GravityInLean

open Real

/-- A round orbit in the plane `θ = π/2` at the fixed distance `r`: where it is after `τ` seconds
of its own clock. -/
noncomputable def roundOrbit (r tdot φdot τ : ℝ) : Coords 4 := fun i =>
  if i = 0 then tdot * τ else if i = 1 then r else if i = 2 then π / 2 else φdot * τ

/-- The steady rates of the orbit, coordinate by coordinate. -/
noncomputable def orbitRate (tdot φdot : ℝ) (i : Fin 4) : ℝ :=
  if i = 0 then tdot else if i = 3 then φdot else 0

/-- Each coordinate of the orbit changes at its steady rate. -/
theorem deriv_roundOrbit (r tdot φdot τ : ℝ) (i : Fin 4) :
    deriv (fun s => roundOrbit r tdot φdot s i) τ = orbitRate tdot φdot i := by
  fin_cases i <;> simp [roundOrbit, orbitRate]

/-- The rates themselves never change. -/
theorem deriv_deriv_roundOrbit (r tdot φdot τ : ℝ) (i : Fin 4) :
    deriv (deriv fun s => roundOrbit r tdot φdot s i) τ = 0 := by
  have h : (deriv fun s => roundOrbit r tdot φdot s i) = fun _ => orbitRate tdot φdot i := by
    funext s
    exact deriv_roundOrbit r tdot φdot s i
  rw [h]
  simp

/-- The free-fall equation for the distance, on the round orbit. -/
theorem freeFallExpr_roundOrbit_r (A B : ℝ → ℝ) (r tdot φdot τ : ℝ) :
    freeFallExpr (roundΓ A B) (roundOrbit r tdot φdot) τ 1
      = qF A B r * tdot ^ 2 + sF B r * φdot ^ 2 := by
  simp only [freeFallExpr, deriv_deriv_roundOrbit, deriv_roundOrbit, Fin.sum_univ_four,
    roundΓ_apply]
  conv_lhs => simp [orbitRate, roundOrbit, rPart, θPart, constOne, constZero, sin2]
  ring

/-- The other three free-fall equations hold by themselves on the round orbit. -/
theorem freeFallExpr_roundOrbit_other (A B : ℝ → ℝ) (r tdot φdot τ : ℝ) {a : Fin 4}
    (ha : a ≠ 1) : freeFallExpr (roundΓ A B) (roundOrbit r tdot φdot) τ a = 0 := by
  fin_cases a
  · simp only [freeFallExpr, deriv_deriv_roundOrbit, deriv_roundOrbit, Fin.sum_univ_four,
      roundΓ_apply]
    simp [orbitRate, roundOrbit, rPart, θPart, constOne, constZero]
  · exact absurd rfl ha
  · simp only [freeFallExpr, deriv_deriv_roundOrbit, deriv_roundOrbit, Fin.sum_univ_four,
      roundΓ_apply]
    simp [orbitRate, roundOrbit, rPart, θPart, constOne, constZero, scF]
  · simp only [freeFallExpr, deriv_deriv_roundOrbit, deriv_roundOrbit, Fin.sum_univ_four,
      roundΓ_apply]
    simp [orbitRate, roundOrbit, rPart, θPart, constOne, constZero]

/-- **Fact 2 of Piece C, derived.** The round orbit falls freely exactly when
`A' · tdot² = 2 r · φdot²`. -/
theorem roundOrbit_isFreeFall_iff {A B : ℝ → ℝ} {r tdot φdot : ℝ} (hB : B r ≠ 0) :
    (∀ τ, IsFreeFallAt (roundΓ A B) (roundOrbit r tdot φdot) τ)
      ↔ deriv A r * tdot ^ 2 = 2 * r * φdot ^ 2 := by
  have alg : qF A B r * tdot ^ 2 + sF B r * φdot ^ 2 = 0
      ↔ deriv A r * tdot ^ 2 = 2 * r * φdot ^ 2 := by
    have e : qF A B r * tdot ^ 2 + sF B r * φdot ^ 2
        = (deriv A r * tdot ^ 2 - 2 * r * φdot ^ 2) * (2 * B r)⁻¹ := by
      unfold qF sF
      ring
    rw [e, mul_eq_zero, or_iff_left (inv_ne_zero (mul_ne_zero two_ne_zero hB)), sub_eq_zero]
  constructor
  · intro h
    have h1 := h 0 1
    rw [freeFallExpr_roundOrbit_r] at h1
    exact alg.mp h1
  · intro h τ a
    by_cases ha : a = 1
    · subst ha
      rw [freeFallExpr_roundOrbit_r]
      exact alg.mpr h
    · exact freeFallExpr_roundOrbit_other A B r tdot φdot τ ha

/-- **Fact 1 of Piece C, derived.** The round orbit is timed by its own clock exactly when
`A · tdot² - r² · φdot² = 1`. -/
theorem roundOrbit_keepsOwnTime_iff {A B : ℝ → ℝ} {r tdot φdot : ℝ} (τ : ℝ) :
    KeepsOwnTimeAt (roundG A B) (roundOrbit r tdot φdot) τ
      ↔ A r * tdot ^ 2 - r ^ 2 * φdot ^ 2 = 1 := by
  have e : ∑ a, ∑ b, roundG A B a b (roundOrbit r tdot φdot τ)
        * deriv (fun s => roundOrbit r tdot φdot s a) τ
        * deriv (fun s => roundOrbit r tdot φdot s b) τ
      = -(A r * tdot ^ 2 - r ^ 2 * φdot ^ 2) := by
    simp only [deriv_roundOrbit, Fin.sum_univ_four]
    conv_lhs =>
      simp [roundG, diag, roundDiag, sep, gr, gθ, negF, sqF, sin2, constOne, orbitRate,
        roundOrbit]
    ring
  unfold KeepsOwnTimeAt
  rw [e, neg_eq_iff_eq_neg, neg_neg]

/-- **Piece C, from the definitions.** Around Schwarzschild's mass, a clock that falls freely on
a round orbit at distance `r`, and is timed by itself, runs at `√(1 - 3M/r)` of a far clock. -/
theorem roundOrbit_clockRate_of_freeFall {M r tdot φdot : ℝ} (hM : 0 < M) (hr : 3 * M < r)
    (ht : 0 < tdot)
    (hfree : ∀ τ, IsFreeFallAt
      (christoffel (roundG (schwA M) (schwB M)) (roundGinv (schwA M) (schwB M)))
      (roundOrbit r tdot φdot) τ)
    (hown : ∀ τ, KeepsOwnTimeAt (roundG (schwA M) (schwB M)) (roundOrbit r tdot φdot) τ) :
    1 / tdot = Real.sqrt (1 - 3 * M / r) := by
  have hr0 : 0 < r := by linarith
  have hpos : 0 < 1 - 2 * M / r := by rw [sub_pos, div_lt_one hr0]; linarith
  have hB : schwB M r ≠ 0 := inv_ne_zero hpos.ne'
  rw [christoffel_round_eq] at hfree
  have hfall := (roundOrbit_isFreeFall_iff hB).mp hfree
  rw [(hasDerivAt_schwA M hr0.ne').deriv] at hfall
  exact roundOrbit_clockRate hM hr ht ((roundOrbit_keepsOwnTime_iff 0).mp (hown 0)) hfall

/-- Such orbits exist: at every distance outside `r = 3M` there is a round orbit that falls
freely and is timed by its own clock. So the theorem above is not a statement about nothing. -/
theorem roundOrbit_freeFall_exists {M r : ℝ} (hM : 0 < M) (hr : 3 * M < r) :
    ∃ tdot φdot : ℝ, 0 < tdot ∧
      (∀ τ, IsFreeFallAt
        (christoffel (roundG (schwA M) (schwB M)) (roundGinv (schwA M) (schwB M)))
        (roundOrbit r tdot φdot) τ) ∧
      (∀ τ, KeepsOwnTimeAt (roundG (schwA M) (schwB M)) (roundOrbit r tdot φdot) τ) := by
  obtain ⟨tdot, φdot, ht, hown, hfall⟩ := roundOrbit_exists hM hr
  have hr0 : 0 < r := by linarith
  have hpos : 0 < 1 - 2 * M / r := by rw [sub_pos, div_lt_one hr0]; linarith
  have hB : schwB M r ≠ 0 := inv_ne_zero hpos.ne'
  refine ⟨tdot, φdot, ht, ?_, fun τ => (roundOrbit_keepsOwnTime_iff τ).mpr hown⟩
  rw [christoffel_round_eq]
  apply (roundOrbit_isFreeFall_iff hB).mpr
  rw [(hasDerivAt_schwA M hr0.ne').deriv]
  exact hfall

end GravityInLean
