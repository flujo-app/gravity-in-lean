/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.SameSpacetime

import Mathlib.Tactic

/-!
# Schwarzschild's space-time is empty on both sides of the rim

Board item `task:bothways-offrim`. The older results `schwarzschild_isEmptySpace`,
`schwarzschild_regular`, `schwarzschild_ricciFlat` and `schwarzschild_ricciFlat_inNewCoords` ask
for a point outside the rim, `2 * M < r`. Their proofs use this for two things only: the
distance `r` is not zero, and `1 - 2 * M / r` is not zero. Both hold as soon as `0 < r` and
`r ≠ 2 * M`, that is, outside the rim and inside it alike. This file states and proves the four
results under these weaker conditions, with the same tables `roundG` and `roundGinv`. The mass
`M` may be any real number.

* `schwA_ne_zero_offRim`: off the rim, `1 - 2 * M / r` is not zero;
* `schwarzschild_isEmptySpace_offRim`: the three formulas of Piece B vanish off the rim;
* `schwarzschild_regular_offRim`: the conditions of step 1 hold off the rim;
* `eventually_offRim`: near a point off the rim, every point is off the rim;
* `schwarzschild_ricciFlat_offRim`: all sixteen parts of the curvature vanish off the rim;
* `schwarzschild_ricciFlat_inNewCoords_offRim`: the same in any coordinates.
-/

@[expose] public section

namespace GravityInLean

open Real Filter Topology Set

/-- Off the rim, Schwarzschild's clock function `1 - 2M/r` is not zero. -/
theorem schwA_ne_zero_offRim {M r : ℝ} (hr : 0 < r) (hrim : r ≠ 2 * M) :
    1 - 2 * M / r ≠ 0 := by
  have h1 : 2 * M / r ≠ 1 := fun h => hrim ((div_eq_one_iff_eq hr.ne').mp h).symm
  exact sub_ne_zero.mpr h1.symm

/-- Off the rim, on either side of it, Schwarzschild's functions make every part of the
curvature vanish: they describe empty space around one mass, inside the rim as well as
outside. -/
theorem schwarzschild_isEmptySpace_offRim (M : ℝ) {r : ℝ} (hr : 0 < r) (hrim : r ≠ 2 * M) :
    IsEmptySpaceAt (schwA M) (schwB M) r := by
  have hr0 : r ≠ 0 := hr.ne'
  have hh : 1 - 2 * M / r ≠ 0 := schwA_ne_zero_offRim hr hrim
  have hne : r - 2 * M ≠ 0 := sub_ne_zero.mpr hrim
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

/-- Off the rim and away from the poles, Schwarzschild's functions meet all the conditions of
step 1, inside the rim as well as outside. -/
theorem schwarzschild_regular_offRim (M : ℝ) {x : Coords 4} (hr : 0 < x 1)
    (hrim : x 1 ≠ 2 * M) (hs : sin (x 2) ≠ 0) : Regular (schwA M) (schwB M) x := by
  have hr0 : x 1 ≠ 0 := hr.ne'
  have hh : 1 - 2 * M / x 1 ≠ 0 := schwA_ne_zero_offRim hr hrim
  exact
    { r_ne := hr0
      sin_ne := hs
      A_ne := hh
      B_ne := inv_ne_zero hh
      diffA := (hasDerivAt_schwA M hr0).differentiableAt
      diffA' := (hasDerivAt_deriv_schwA M hr0).differentiableAt
      diffB := (hasDerivAt_schwB M hr0 hh).differentiableAt }

/-- Near a point off the rim and away from the poles, every point is off the rim and away from
the poles. -/
theorem eventually_offRim {M : ℝ} {p : Coords 4} (hr : 0 < p 1) (hrim : p 1 ≠ 2 * M)
    (hs : sin (p 2) ≠ 0) : ∀ᶠ z in 𝓝 p, 0 < z 1 ∧ z 1 ≠ 2 * M ∧ sin (z 2) ≠ 0 := by
  have c1 : ContinuousAt (fun z : Coords 4 => z 1) p := (continuous_apply 1).continuousAt
  have c2 : ContinuousAt (fun z : Coords 4 => sin (z 2)) p :=
    (Real.continuous_sin.comp (continuous_apply 2)).continuousAt
  exact (c1.eventually (lt_mem_nhds hr)).and
    ((c1.eventually_ne hrim).and (c2.eventually_ne hs))

/-- **Schwarzschild's space-time is empty on both sides of the rim.** At every point with
positive distance, not on the rim and away from the poles, all sixteen parts of the curvature of
Schwarzschild's table, computed from the general definitions, vanish. -/
theorem schwarzschild_ricciFlat_offRim (M : ℝ) {x : Coords 4} (hr : 0 < x 1)
    (hrim : x 1 ≠ 2 * M) (hs : sin (x 2) ≠ 0) :
    IsRicciFlatAt (roundG (schwA M) (schwB M)) (roundGinv (schwA M) (schwB M)) x :=
  (round_ricciFlat_iff (schwarzschild_regular_offRim M hr hrim hs)).mpr
    (schwarzschild_isEmptySpace_offRim M hr hrim)

/-- **Schwarzschild's space-time is empty in any coordinates, on both sides of the rim.** Take
any change of coordinates `Φ` that is three times smoothly differentiable near `x` and lands off
the rim, away from the poles. If the re-written length measure has an inverse `ginv'` near `x`,
it makes space empty at `x`. -/
theorem schwarzschild_ricciFlat_inNewCoords_offRim (M : ℝ) {Φ : Coords 4 → Coords 4}
    {ginv' : Fin 4 → Fin 4 → Coords 4 → ℝ} {x : Coords 4}
    (hΦ : ∀ α, ContDiffAt ℝ 3 (fun z => Φ z α) x) (hr : 0 < Φ x 1) (hrim : Φ x 1 ≠ 2 * M)
    (hs : sin (Φ x 2) ≠ 0)
    (hinv' : ∀ᶠ y in 𝓝 x, ∀ μ κ,
      ∑ ν, inNewCoords Φ (roundG (schwA M) (schwB M)) μ ν y * ginv' ν κ y
        = if μ = κ then 1 else 0) :
    IsRicciFlatAt (inNewCoords Φ (roundG (schwA M) (schwB M))) ginv' x := by
  have hr0 : Φ x 1 ≠ 0 := hr.ne'
  have hh : 1 - 2 * M / Φ x 1 ≠ 0 := schwA_ne_zero_offRim hr hrim
  have hA := contDiffAt_schwA M hr0
  have hB := contDiffAt_schwB M hr0 hh
  refine (isRicciFlatAt_inNewCoords hΦ (fun α β => contDiffAt_roundG hA hB α β)
    (Eventually.of_forall fun z α β => roundG_symm _ _ α β z)
    ((eventually_offRim hr hrim hs).mono fun z hz α γ =>
      roundG_mul_roundGinv (schwarzschild_regular_offRim M hz.1 hz.2.1 hz.2.2) α γ)
    hinv').mpr ?_
  exact schwarzschild_ricciFlat_offRim M hr hrim hs

end GravityInLean
