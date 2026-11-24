/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.Tests
public import GravityInLean.Join.UsableSlope

import Mathlib.Tactic

/-!
# Tests, group 2: spheres of one fixed size

Board item `task:checks-cyl`. The table `cylG` of `Goals/Tests.lean` is a flat plane of time and
distance, times a sphere of size one: `-dt² + dρ² + dθ² + sin²θ dφ²`. Its spheres all have the
same size. This file proves the three tests about it:

* `cylIsRoundOn`: it looks the same from every side, off the poles;
* `cylNotUsable`: the size of its spheres is nowhere a usable distance, because that size does
  not change at all: its slope is zero, and the zero step has the length zero;
* `cylNotEmpty`: it is not empty: the part of its curvature along the sphere is 1, not 0.

So "usable distance" does not accept a size that does not change, and "the same from every
side" does not need the size of the spheres to be a coordinate.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean

open Real Filter Topology Set

open scoped Manifold ContDiff

namespace Curved

namespace Tests

/-! ## The table, written out -/

/-- The region off the poles is open. -/
theorem cyl_isOpen : IsOpen {x : Coords 4 | sin (x 2) ≠ 0} :=
  isOpen_ne_fun (Real.continuous_sin.comp (continuous_apply 2)) continuous_const

/-- Every entry of the table is smooth of every order, at every point. -/
theorem cyl_contDiff (i j : Fin 4) : ContDiff ℝ ∞ (cylG i j) := by
  have hΘ : ContDiff ℝ ∞ (gΘ i j) := by
    unfold gΘ
    split_ifs
    · exact Real.contDiff_sin.pow 2
    · exact contDiff_const
  have hTR : ∃ c : ℝ,
      gTR (fun _ _ ↦ 1) (fun _ _ ↦ 1) zero2 (fun _ _ ↦ 1) i j = fun _ _ ↦ c := by
    unfold gTR
    split_ifs
    exacts [⟨-1, rfl⟩, ⟨0, rfl⟩, ⟨1, rfl⟩, ⟨1, rfl⟩, ⟨0, rfl⟩]
  obtain ⟨c, hc⟩ := hTR
  have e : cylG i j = fun x : Coords 4 ↦ c * gΘ i j (x 2) := by
    funext x
    change gTR (fun _ _ ↦ 1) (fun _ _ ↦ 1) zero2 (fun _ _ ↦ 1) i j (x 0) (x 1) * gΘ i j (x 2)
      = c * gΘ i j (x 2)
    rw [hc]
  rw [e]
  exact contDiff_const.mul (hΘ.comp (contDiff_apply ℝ (fun _ : Fin 4 ↦ ℝ) 2))

/-- The time-distance part of the table is not degenerate: `1 · 1 + 0 · 0 = 1`. -/
theorem cyl_det2 (t ρ : ℝ) : det2 (fun _ _ ↦ 1) (fun _ _ ↦ 1) zero2 t ρ = 1 := by
  change (1 : ℝ) * 1 + 0 * 0 = 1
  norm_num

/-- The table is good off the poles: smooth, the same when its two slots are swapped, and with
an inverse. -/
theorem cyl_regularTable :
    IsRegularTableOn cylG (genGinv (fun _ _ ↦ 1) (fun _ _ ↦ 1) zero2 (fun _ _ ↦ 1))
      {x : Coords 4 | sin (x 2) ≠ 0} where
  isOpen := cyl_isOpen
  smooth := fun a b ↦ (cyl_contDiff a b).contDiffOn
  symm := fun x _ a b ↦ genG_symm _ _ _ _ a b x
  inverse := fun x hx a c ↦
    genG_mul_genGinv (by rw [cyl_det2]; exact one_ne_zero) one_ne_zero hx a c

/-- The length that the table gives two steps, written out: minus for time, plus for distance,
and the sphere of size one for the two angles. -/
theorem cyl_measure_apply (x v w : Coords 4) :
    tableMeasure cylG x v w
      = -(v 0 * w 0) + v 1 * w 1 + v 2 * w 2 + sin (x 2) ^ 2 * v 3 * w 3 := by
  rw [Join.tableMeasure_of_genG (A := fun _ _ ↦ 1) (B := fun _ _ ↦ 1) (C := zero2)
    (S := fun _ _ ↦ 1) (fun _ _ ↦ rfl)]
  simp only [zero2]
  ring

/-! ## It looks the same from every side -/

/-- On the two angle directions the table gives every step a positive squared length. -/
theorem cyl_pos_on_angles {x : Coords 4} (hs : sin (x 2) ≠ 0) (v : Coords 4)
    (hv : v ∈ Submodule.span ℝ (Set.range ![(Pi.single 2 1 : Coords 4), Pi.single 3 1]))
    (hne : v ≠ 0) : 0 < tableMeasure cylG x v v := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
  have hc : c 0 ≠ 0 ∨ c 1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hne
    simp [Fin.sum_univ_two, hcon.1, hcon.2]
  have h0 : (∑ i, c i • ![(Pi.single 2 1 : Coords 4), Pi.single 3 1] i) 0 = 0 := by
    simp [Fin.sum_univ_two]
  have h1 : (∑ i, c i • ![(Pi.single 2 1 : Coords 4), Pi.single 3 1] i) 1 = 0 := by
    simp [Fin.sum_univ_two]
  have h2 : (∑ i, c i • ![(Pi.single 2 1 : Coords 4), Pi.single 3 1] i) 2 = c 0 := by
    simp [Fin.sum_univ_two]
  have h3 : (∑ i, c i • ![(Pi.single 2 1 : Coords 4), Pi.single 3 1] i) 3 = c 1 := by
    simp [Fin.sum_univ_two]
  rw [cyl_measure_apply, h0, h1, h2, h3]
  have hsin : 0 < sin (x 2) ^ 2 := sq_pos_iff.mpr hs
  rcases hc with h | h
  · have hsq : 0 < c 0 ^ 2 := sq_pos_iff.mpr h
    nlinarith [mul_nonneg hsin.le (sq_nonneg (c 1))]
  · have hsq : 0 < c 1 ^ 2 := sq_pos_iff.mpr h
    nlinarith [mul_pos hsin hsq, sq_nonneg (c 0)]

/-- The table of spheres of one fixed size looks the same from every side, off the poles: the
three turns of ordinary space are smooth, leave the length measure unchanged, combine the way
turns do, and sweep out surfaces on which all lengths are positive. -/
theorem cyl_isRoundOn :
    IsRoundOn (flatMeasure (tableMeasure cylG)) turns {x : Coords 4 | sin (x 2) ≠ 0} where
  isOpen := cyl_isOpen
  smooth := by
    intro i
    fin_cases i
    · exact contMDiffOn_arrows_iff.mpr (contDiffOn_pi.2 fun k x hx ↦
        (smooth_rotY (z := x) hx k).contDiffWithinAt)
    · exact contMDiffOn_arrows_iff.mpr (contDiffOn_pi.2 fun k x hx ↦
        (smooth_rotX (z := x) hx k).contDiffWithinAt)
    · exact contMDiffOn_arrows_iff.mpr (contDiffOn_pi.2 fun k x _ ↦
        (smooth_rotZ x k).contDiffWithinAt)
  unchanged := by
    intro i x hx
    have hg := fun a b ↦ cyl_regularTable.differentiableAt hx a b
    have hround := genG_isRound (fun _ _ ↦ 1) (fun _ _ ↦ 1) zero2 (fun _ _ ↦ 1) hx
    fin_cases i
    · exact (leavesUnchangedAt_table_iff hg (differentiableAt_rotY hx)).mpr hround.2.1
    · exact (leavesUnchangedAt_table_iff hg (differentiableAt_rotX hx)).mpr hround.1
    · exact (leavesUnchangedAt_table_iff hg (differentiableAt_rotZ x)).mpr hround.2.2
  likeTurns := fun _ hx ↦ ⟨bracket_rotY_rotX hx, bracket_rotX_rotZ hx, bracket_rotZ_rotY hx⟩
  surfaces := fun x _ ↦ by
    have h := finrank_span_angles
    rw [← span_turns x] at h
    exact h
  positive := fun x hx v hv hne ↦ by
    have hv' : (v : Coords 4)
        ∈ Submodule.span ℝ (Set.range fun i : Fin 3 ↦ (turns i x : Coords 4)) := hv
    rw [span_turns] at hv'
    exact cyl_pos_on_angles hx v hv' hne

/-- **Test 2, first part.** Spheres of one fixed size look the same from every side. Here the
size of the spheres is not a coordinate, and the definition still holds. -/
theorem cylIsRoundOn : CylIsRoundOn :=
  cyl_isRoundOn

/-! ## The size of the spheres is no usable distance -/

/-- Off the poles, the squared size of the spheres of this table is 1. -/
theorem cyl_sizeSq {x : Coords 4} (hs : sin (x 2) ≠ 0) :
    sizeSq (flatMeasure (tableMeasure cylG)) turns x = 1 := by
  rw [Join.sizeSq_of_genG (A := fun _ _ ↦ 1) (B := fun _ _ ↦ 1) (C := zero2)
    (S := fun _ _ ↦ 1) (fun _ _ ↦ rfl) hs]
  simp [genG, sep2, gTR, gΘ, constOne]

/-- **Test 2, second part.** The size of the spheres is nowhere a usable distance: it is the same
everywhere, so its slope is zero. A step that the length measure turns into the slope zero has
the squared length zero, which "usable distance" does not allow. -/
theorem cylNotUsable : CylNotUsable := by
  rintro x hs ⟨n, hn, hnn⟩
  -- Near `x` the squared size of the spheres is the constant 1, so its slope at `x` is zero.
  have hev : sizeSq (flatMeasure (tableMeasure cylG)) turns =ᶠ[𝓝 x] fun _ ↦ (1 : ℝ) := by
    filter_upwards [cyl_isOpen.mem_nhds hs] with y hy
    exact cyl_sizeSq hy
  have h0 : fderiv ℝ (sizeSq (flatMeasure (tableMeasure cylG)) turns) x = 0 := by
    rw [hev.fderiv_eq]
    exact fderiv_const_apply 1
  -- The step `n` measured against itself is the slope applied to `n`, which is zero.
  have h := hn n
  rw [mvfderiv_flat, h0] at h
  exact hnn h

/-! ## It is not empty -/

/-- For this table the part of the curvature along the sphere is 1: nothing changes with time or
distance, so only the curvature of the sphere of size one is left. -/
theorem cyl_ricciAngG (t ρ : ℝ) :
    ricciAngG (fun _ _ ↦ 1) (fun _ _ ↦ 1) zero2 (fun _ _ ↦ 1) t ρ = 1 := by
  have hdt : dt (fun _ _ ↦ (1 : ℝ)) = zero2 := dt_one2_fun
  have hdr : dr (fun _ _ ↦ (1 : ℝ)) = zero2 := dr_one2_fun
  simp only [ricciAngG, hessTT, hessTR, hessRR, hdt, hdr, dt_zero2, dr_zero2]
  simp only [zero2]
  ring

/-- **Test 2, third part.** Spheres of one fixed size are not empty space: at a point of the
equator the part of the curvature along the sphere is 1, and Einstein's equation without matter
asks for 0. -/
theorem cylNotEmpty : CylNotEmpty := by
  intro hE
  have hs : sin ((fun _ ↦ π / 2 : Coords 4) 2) ≠ 0 := by
    change sin (π / 2) ≠ 0
    rw [Real.sin_pi_div_two]
    exact one_ne_zero
  have hflat := cyl_regularTable.isEmptyOn_iff.mp hE (fun _ ↦ π / 2) hs
  have hreg : RegularG (fun _ _ ↦ 1) (fun _ _ ↦ 1) zero2 (fun _ _ ↦ 1)
      (fun _ ↦ π / 2 : Coords 4) :=
    { sin_ne := hs
      det_ne := by
        rw [cyl_det2]
        exact one_ne_zero
      S_ne := one_ne_zero
      smoothA := twiceSmooth_one2 _ _
      smoothB := twiceSmooth_one2 _ _
      smoothC := twiceSmooth_zero2 _ _
      smoothS := twiceSmooth_one2 _ _ }
  have h1 := ((gen_ricciFlat_iff hreg).mp hflat).2.2.2
  rw [cyl_ricciAngG] at h1
  exact one_ne_zero h1

end Tests

end Curved

end GravityInLean
