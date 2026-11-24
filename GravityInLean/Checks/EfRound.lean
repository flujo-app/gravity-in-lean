/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.Tests
public import GravityInLean.Join.UsableSlope
public import GravityInLean.SameSpacetime

import Mathlib.Tactic

/-!
# Tests, group 1: the rim is round, but the size of the spheres is no usable distance there

Board item `task:checks-ef-round`. Two of the tests of `Goals/Tests.lean`, both for
Schwarzschild's space-time in Eddington's coordinates (`Tests.efG`), which are good on the rim of
the black hole:

* `Tests.efIsRoundOn`: it looks the same from every side, rim included;
* `Tests.efNotUsableOnRim`: on the rim the size of the spheres is not a usable distance. The
  only step that the length measure turns into the slope of the squared size has the squared
  length zero there: the spheres grow along a path of light.

The first is proved for every table of the general round shape `genG`, so that other tests can
use it:

* `roundShape_pos_on_angles`: on the two angle directions such a table gives every step a
  positive squared length, if its entry for the pole angle is positive;
* `roundShape_isRoundOn`: such a table looks the same from every side on an open region off the
  poles, if its entries can be differentiated there and its entry for the pole angle is positive.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Filter Topology Set

/-- On the two angle directions, a table of the general round shape gives every step a positive
squared length, wherever its entry for the pole angle is positive. -/
theorem roundShape_pos_on_angles {A B C S : ℝ → ℝ → ℝ} {x : Coords 4}
    (hS : 0 < S (x 0) (x 1)) (hs : sin (x 2) ≠ 0) (v : Coords 4)
    (hv : v ∈ Submodule.span ℝ (Set.range ![(Pi.single 2 1 : Coords 4), Pi.single 3 1]))
    (hne : v ≠ 0) : 0 < tableMeasure (genG A B C S) x v v := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
  have hc : c 0 ≠ 0 ∨ c 1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hne
    simp [Fin.sum_univ_two, hcon.1, hcon.2]
  -- The four parts of the step: none along time and distance, `c 0` and `c 1` along the angles.
  have v0 : (∑ i, c i • ![(Pi.single 2 1 : Coords 4), Pi.single 3 1] i) 0 = 0 := by
    simp [Fin.sum_univ_two]
  have v1 : (∑ i, c i • ![(Pi.single 2 1 : Coords 4), Pi.single 3 1] i) 1 = 0 := by
    simp [Fin.sum_univ_two]
  have v2 : (∑ i, c i • ![(Pi.single 2 1 : Coords 4), Pi.single 3 1] i) 2 = c 0 := by
    simp [Fin.sum_univ_two]
  have v3 : (∑ i, c i • ![(Pi.single 2 1 : Coords 4), Pi.single 3 1] i) 3 = c 1 := by
    simp [Fin.sum_univ_two]
  have e : tableMeasure (genG A B C S) x
        (∑ i, c i • ![(Pi.single 2 1 : Coords 4), Pi.single 3 1] i)
        (∑ i, c i • ![(Pi.single 2 1 : Coords 4), Pi.single 3 1] i)
      = S (x 0) (x 1) * c 0 ^ 2 + S (x 0) (x 1) * sin (x 2) ^ 2 * c 1 ^ 2 := by
    rw [Join.tableMeasure_of_genG (fun _ _ ↦ rfl), v0, v1, v2, v3]
    ring
  rw [e]
  have h2 : 0 < sin (x 2) ^ 2 := sq_pos_iff.mpr hs
  rcases hc with h | h
  · have h3 : 0 < c 0 ^ 2 := sq_pos_iff.mpr h
    nlinarith [mul_pos hS h3, mul_nonneg (mul_pos hS h2).le (sq_nonneg (c 1))]
  · have h3 : 0 < c 1 ^ 2 := sq_pos_iff.mpr h
    nlinarith [mul_pos (mul_pos hS h2) h3, mul_nonneg hS.le (sq_nonneg (c 0))]

/-- **A table of the general round shape looks the same from every side,** in the sense of
`Basic.lean`, on every open region off the poles on which its entries can be differentiated and
its entry for the pole angle is positive: the three turns of ordinary space are smooth, leave the
length measure unchanged, combine the way turns do, and sweep out surfaces on which all lengths
are positive. -/
theorem roundShape_isRoundOn {A B C S : ℝ → ℝ → ℝ} {s : Set (Coords 4)} (hopen : IsOpen s)
    (hsin : ∀ x ∈ s, sin (x 2) ≠ 0)
    (hd : ∀ x ∈ s, ∀ a b, DifferentiableAt ℝ (genG A B C S a b) x)
    (hS : ∀ x ∈ s, 0 < S (x 0) (x 1)) :
    IsRoundOn (flatMeasure (tableMeasure (genG A B C S))) turns s where
  isOpen := hopen
  smooth := by
    intro i
    fin_cases i
    · exact contMDiffOn_arrows_iff.mpr (contDiffOn_pi.2 fun k x hx ↦
        (smooth_rotY (z := x) (hsin x hx) k).contDiffWithinAt)
    · exact contMDiffOn_arrows_iff.mpr (contDiffOn_pi.2 fun k x hx ↦
        (smooth_rotX (z := x) (hsin x hx) k).contDiffWithinAt)
    · exact contMDiffOn_arrows_iff.mpr (contDiffOn_pi.2 fun k x _ ↦
        (smooth_rotZ x k).contDiffWithinAt)
  unchanged := by
    intro i x hx
    have hg := hd x hx
    have hround := genG_isRound A B C S (hsin x hx)
    fin_cases i
    · exact (leavesUnchangedAt_table_iff hg (differentiableAt_rotY (hsin x hx))).mpr hround.2.1
    · exact (leavesUnchangedAt_table_iff hg (differentiableAt_rotX (hsin x hx))).mpr hround.1
    · exact (leavesUnchangedAt_table_iff hg (differentiableAt_rotZ x)).mpr hround.2.2
  likeTurns := fun x hx ↦
    ⟨bracket_rotY_rotX (hsin x hx), bracket_rotX_rotZ (hsin x hx), bracket_rotZ_rotY (hsin x hx)⟩
  surfaces := fun x _ ↦ by
    have h := finrank_span_angles
    rw [← span_turns x] at h
    exact h
  positive := fun x hx v hv hne ↦ by
    have hv' : (v : Coords 4)
        ∈ Submodule.span ℝ (Set.range fun i : Fin 3 ↦ (turns i x : Coords 4)) := hv
    rw [span_turns] at hv'
    exact roundShape_pos_on_angles (hS x hx) (hsin x hx) v hv' hne

namespace Tests

/-- The region of Eddington's coordinates off the centre and off the poles is open: a point
close to one of its points is in it too. -/
theorem efRegion_isOpen : IsOpen efRegion :=
  (isOpen_lt continuous_const (continuous_apply 1)).inter
    (isOpen_ne_fun (Real.continuous_sin.comp (continuous_apply 2)) continuous_const)

/-- **Test 1, third part.** In Eddington's coordinates Schwarzschild's space-time looks the same
from every side, on the rim as well as off it. -/
theorem efIsRoundOn : EfIsRoundOn := fun M ↦
  roundShape_isRoundOn efRegion_isOpen (fun _ hx ↦ hx.2)
    (fun x hx a b ↦
      (contDiffAt_genG (twiceSmooth_onlyR (contDiffAt_schwA M hx.1.ne') (x 0))
        (twiceSmooth_zero2 (x 0) (x 1)) (twiceSmooth_one2 (x 0) (x 1))
        (twiceSmooth_onlyR (contDiffAt_sqF (x 1)) (x 0)) a b).differentiableAt (by norm_num))
    (fun x hx ↦ show 0 < x 1 ^ 2 from pow_pos hx.1 2)

/-- **Test 1, fourth part.** On the rim of the black hole the size of the spheres is not a
usable distance. The step that the length measure turns into the slope of the squared size is
fixed by the table, and on the rim its own squared length is zero. -/
theorem efNotUsableOnRim : EfNotUsableOnRim := by
  intro M hM x hr hs hu
  -- On the rim the clock function `1 - 2M/r` is zero.
  have hA : schwA M (x 1) = 0 := by
    rw [schwA, hr]
    field_simp
    ring
  -- Near `x` the squared size of the spheres is the square of the distance label.
  have hev : sizeSq (flatMeasure (tableMeasure (efG M))) turns
      =ᶠ[𝓝 x] fun y ↦ coordL 1 y ^ 2 := by
    have hopen : IsOpen {y : Coords 4 | sin (y 2) ≠ 0} :=
      isOpen_ne_fun (Real.continuous_sin.comp (continuous_apply 2)) continuous_const
    filter_upwards [hopen.mem_nhds hs] with y hy
    rw [Join.sizeSq_of_genG (h := efG M) (fun _ _ ↦ rfl) hy]
    simp [genG, sep2, gTR, gΘ, constOne, onlyR, sqF]
  have hd := ((coordL (n := 4) 1).hasFDerivAt (x := x)).pow 2
  -- The step that the usable distance gives, in the words of tables.
  obtain ⟨n, hn, hnn⟩ : ∃ n : Coords 4,
      (∀ w : Coords 4, tableMeasure (efG M) x n w = 2 * x 1 * w 1)
        ∧ tableMeasure (efG M) x n n ≠ 0 := by
    obtain ⟨n, hn, hnn⟩ := hu
    refine ⟨n, fun w ↦ ?_, hnn⟩
    have hw := hn w
    rw [mvfderiv_flat, hev.fderiv_eq, hd.fderiv] at hw
    have e : ((2 • coordL (n := 4) 1 x ^ (2 - 1)) • coordL (n := 4) 1) w = 2 * x 1 * w 1 := by
      simp
    rw [← e]
    exact hw
  -- The table of Eddington's form on the rim, written out for the step `n`.
  have hform : ∀ w : Coords 4, tableMeasure (efG M) x n w
      = n 0 * w 1 + n 1 * w 0 + x 1 ^ 2 * n 2 * w 2 + x 1 ^ 2 * sin (x 2) ^ 2 * n 3 * w 3 := by
    intro w
    have h1 : tableMeasure (efG M) x n w
        = -schwA M (x 1) * n 0 * w 0 + 1 * (n 0 * w 1 + n 1 * w 0) + 0 * n 1 * w 1
          + x 1 ^ 2 * n 2 * w 2 + x 1 ^ 2 * sin (x 2) ^ 2 * n 3 * w 3 :=
      Join.tableMeasure_of_genG (h := efG M) (fun _ _ ↦ rfl) n w
    rw [h1, hA]
    ring
  -- Measured against a step in time, the step `n` gives its part along the distance: zero.
  have hn1 : n 1 = 0 := by
    have h0 := hn (Pi.single 0 1)
    rw [hform] at h0
    simpa using h0
  -- So its own squared length is zero.
  apply hnn
  rw [hn n, hn1, mul_zero]

end Tests

end GravityInLean.Curved
