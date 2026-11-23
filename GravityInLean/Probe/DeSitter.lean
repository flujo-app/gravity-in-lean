/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.RoundSpacetime

import Mathlib.Tactic

/-!
# A second probe: de Sitter's space-time

Showing that a curvature is zero cannot catch every mistake in the definitions: a wrong sign in
front of a term that happens to vanish would go unnoticed. The first probe (`Sphere.lean`) tested
the definitions on a curved surface. This one tests them in four dimensions, with a time
direction, on a space-time whose curvature is known and is **not** zero.

De Sitter's space-time of 1917 is the empty universe with a cosmological constant. In round,
unchanging coordinates its clock function is `1 - r² / L²` and its ruler function is one over
that. The textbooks say: its curvature equals its own length measure times `3 / L²`.

**What is proved here.** `ricci_deSitter`: computed from the general definitions, all sixteen
parts of the curvature of de Sitter's space-time equal `3 / L²` times the same part of its length
measure, everywhere inside its horizon (`0 < r < L`), away from the poles. In particular the sign
is the textbooks' sign, in the time direction as well as in the space directions.
-/

@[expose] public section

namespace GravityInLean

open Real Filter Topology

/-- De Sitter's clock function: `1 - r² / L²`. -/
noncomputable def dsA (L r : ℝ) : ℝ := 1 - r ^ 2 / L ^ 2

/-- De Sitter's ruler function: `1 / (1 - r² / L²)`. -/
noncomputable def dsB (L r : ℝ) : ℝ := (1 - r ^ 2 / L ^ 2)⁻¹

theorem hasDerivAt_dsA (L r : ℝ) : HasDerivAt (dsA L) (-(2 * r) / L ^ 2) r := by
  have h : HasDerivAt (fun y : ℝ => y ^ 2) (2 * r) r := by simpa using hasDerivAt_pow 2 r
  have h2 : HasDerivAt (fun y : ℝ => 1 - y ^ 2 / L ^ 2) (-(2 * r / L ^ 2)) r :=
    (h.div_const (L ^ 2)).const_sub 1
  exact h2.congr_deriv (by ring)

theorem hasDerivAt_deriv_dsA (L r : ℝ) : HasDerivAt (deriv (dsA L)) (-2 / L ^ 2) r := by
  have e : deriv (dsA L) = fun y => -(2 * y) / L ^ 2 :=
    funext fun y => (hasDerivAt_dsA L y).deriv
  rw [e]
  have h : HasDerivAt (fun y : ℝ => -(2 * y) / L ^ 2) (-(2 * 1) / L ^ 2) r :=
    (((hasDerivAt_id' r).const_mul 2).neg).div_const (L ^ 2)
  exact h.congr_deriv (by ring)

theorem hasDerivAt_dsB (L : ℝ) {r : ℝ} (hh : 1 - r ^ 2 / L ^ 2 ≠ 0) :
    HasDerivAt (dsB L) (-(-(2 * r) / L ^ 2) / (1 - r ^ 2 / L ^ 2) ^ 2) r :=
  (hasDerivAt_dsA L r).inv hh

/-- Inside the horizon and away from the poles, de Sitter's functions meet all the conditions of
the computation of step 1. -/
theorem deSitter_regular {L : ℝ} {x : Coords 4} (hr : 0 < x 1) (hL : x 1 < L)
    (hs : sin (x 2) ≠ 0) : Regular (dsA L) (dsB L) x := by
  have hL0 : 0 < L := hr.trans hL
  have hpos : 0 < 1 - x 1 ^ 2 / L ^ 2 := by
    rw [sub_pos, div_lt_one (pow_pos hL0 2)]
    exact pow_lt_pow_left₀ hL hr.le two_ne_zero
  exact
    { r_ne := hr.ne'
      sin_ne := hs
      A_ne := hpos.ne'
      B_ne := inv_ne_zero hpos.ne'
      diffA := (hasDerivAt_dsA L (x 1)).differentiableAt
      diffA' := (hasDerivAt_deriv_dsA L (x 1)).differentiableAt
      diffB := (hasDerivAt_dsB L hpos.ne').differentiableAt }

/-- **The second probe.** The curvature of de Sitter's space-time, computed from the general
definitions, is `3 / L²` times its own length measure: all sixteen parts, with the textbooks'
sign. -/
theorem ricci_deSitter {L : ℝ} {x : Coords 4} (hr : 0 < x 1) (hL : x 1 < L)
    (hs : sin (x 2) ≠ 0) (i j : Fin 4) :
    ricci (christoffel (roundG (dsA L) (dsB L)) (roundGinv (dsA L) (dsB L))) i j x
      = 3 / L ^ 2 * roundG (dsA L) (dsB L) i j x := by
  have hL0 : 0 < L := hr.trans hL
  have hLne : L ≠ 0 := hL0.ne'
  have hr0 : x 1 ≠ 0 := hr.ne'
  have hpos : 0 < 1 - x 1 ^ 2 / L ^ 2 := by
    rw [sub_pos, div_lt_one (pow_pos hL0 2)]
    exact pow_lt_pow_left₀ hL hr.le two_ne_zero
  have hh : 1 - x 1 ^ 2 / L ^ 2 ≠ 0 := hpos.ne'
  have hne : L ^ 2 - x 1 ^ 2 ≠ 0 := by
    have : 0 < L ^ 2 - x 1 ^ 2 := sub_pos.mpr (pow_lt_pow_left₀ hL hr.le two_ne_zero)
    exact this.ne'
  have hreg := deSitter_regular hr hL hs
  have dA := (hasDerivAt_dsA L (x 1)).deriv
  have ddA := (hasDerivAt_deriv_dsA L (x 1)).deriv
  have dB := (hasDerivAt_dsB L hh).deriv
  have c0 : ricci (roundΓ (dsA L) (dsB L)) 0 0 x = 3 / L ^ 2 * roundG (dsA L) (dsB L) 0 0 x := by
    rw [ricci_roundΓ_tt hreg, dA, ddA, dB]
    simp [ricciTT, dsA, dsB, roundG, diag, roundDiag, sep, gr, gθ, negF, constOne]
    field_simp
    ring
  have c1 : ricci (roundΓ (dsA L) (dsB L)) 1 1 x = 3 / L ^ 2 * roundG (dsA L) (dsB L) 1 1 x := by
    rw [ricci_roundΓ_rr hreg, dA, ddA, dB]
    simp [ricciRR, dsA, dsB, roundG, diag, roundDiag, sep, gr, gθ, constOne]
    field_simp
    ring
  have c2 : ricci (roundΓ (dsA L) (dsB L)) 2 2 x = 3 / L ^ 2 * roundG (dsA L) (dsB L) 2 2 x := by
    rw [ricci_roundΓ_θθ hreg, dA, dB]
    simp [ricciAng, dsA, dsB, roundG, diag, roundDiag, sep, gr, gθ, sqF, constOne]
    field_simp
    ring
  have c3 : ricci (roundΓ (dsA L) (dsB L)) 3 3 x = 3 / L ^ 2 * roundG (dsA L) (dsB L) 3 3 x := by
    rw [ricci_roundΓ_φφ hreg, dA, dB]
    simp [ricciAng, dsA, dsB, roundG, diag, roundDiag, sep, gr, gθ, sqF, sin2]
    field_simp
    ring
  rw [christoffel_round_eq]
  by_cases hij : i = j
  · subst hij
    fin_cases i
    · exact c0
    · exact c1
    · exact c2
    · exact c3
  · rw [ricci_roundΓ_offdiag (dsA L) (dsB L) hr0 hs hij]
    simp [roundG, diag, hij]

end GravityInLean
