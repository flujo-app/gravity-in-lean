/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.ExactlyWhen
public import GravityInLean.Probe.DeSitter
public import GravityInLean.SameSpacetime
public import Mathlib.Analysis.Calculus.ContDiff.Operations

import Mathlib.Tactic

/-!
# "Empty" can fail: De Sitter's table

Board item `task:bothways-notempty`. Birkhoff's theorem in coordinates, read both ways
(`BirkhoffExactlyWhenInCoordinates`), says of a round table whose spheres give a usable distance:
it is empty exactly when it is Schwarzschild's after new labels. Such a statement would be worth
little if every round table were empty. This file shows that this is not so.

De Sitter's table (the empty universe with a cosmological constant, radius `L`) inside its
horizon, `0 < r < L`, at all times and off the poles:

* is a round table in the sense of `RoundSetting` (`deSitter_roundSetting`): smooth of every
  order, symmetric, the same from every side, of the space-time kind, with `roundGinv` as its
  inverse;
* has spheres whose size is a usable distance (`deSitter_sizeSlopeOf_ne_zero`);
* is not empty (`deSitter_not_ricciFlat`): its curvature is `3 / L²` times the table itself
  (`ricci_deSitter`), and that is not zero.

These three, and the lemmas that lead to them, carry the name `DeSitterTable` in front.

Together: `exactlyWhenNotAlwaysEmpty`, one of the statements fixed in `Goals/ExactlyWhen.lean`.
-/

@[expose] public section

namespace GravityInLean

open Real Set

open scoped ContDiff

/- The helping lemmas about De Sitter's table live under this name, so that they cannot clash
with lemmas of the same kind in other files. -/
namespace DeSitterTable

/-! ## The entries of De Sitter's table -/

/-- The time-time entry of De Sitter's table is minus its clock function. -/
theorem deSitter_entry_tt (L : ℝ) (x : Coords 4) :
    roundG (dsA L) (dsB L) 0 0 x = -dsA L (x 1) := by
  simp [roundG, diag, roundDiag, sep, gr, gθ, negF, constOne]

/-- The distance-distance entry of De Sitter's table is its ruler function. -/
theorem deSitter_entry_rr (L : ℝ) (x : Coords 4) :
    roundG (dsA L) (dsB L) 1 1 x = dsB L (x 1) := by
  simp [roundG, diag, roundDiag, sep, gr, gθ, constOne]

/-- De Sitter's table has no cross term between time and distance. -/
theorem deSitter_entry_tr (L : ℝ) (x : Coords 4) : roundG (dsA L) (dsB L) 0 1 x = 0 := by
  simp [roundG, diag]

/-- The entry for the pole angle is the square of the distance label: the spheres have the
radius `r`. -/
theorem deSitter_entry_θθ (L : ℝ) (x : Coords 4) : roundG (dsA L) (dsB L) 2 2 x = x 1 ^ 2 := by
  simp [roundG, diag, roundDiag, sep, gr, gθ, sqF, constOne]

/-- Inside the horizon De Sitter's clock function is positive. -/
theorem deSitter_clock_pos {L r : ℝ} (hr : 0 < r) (hL : r < L) : 0 < dsA L r := by
  have hL0 : 0 < L := hr.trans hL
  change 0 < 1 - r ^ 2 / L ^ 2
  rw [sub_pos, div_lt_one (pow_pos hL0 2)]
  exact pow_lt_pow_left₀ hL hr.le two_ne_zero

/-- De Sitter's ruler function is one over its clock function. -/
theorem dsB_eq_inv (L r : ℝ) : dsB L r = (dsA L r)⁻¹ := rfl

/-! ## Smooth of every order -/

/-- De Sitter's clock function is smooth of every order. -/
theorem contDiff_dsA (L : ℝ) : ContDiff ℝ ∞ (dsA L) := by
  have e : dsA L = fun r : ℝ => 1 - r ^ 2 / L ^ 2 := rfl
  rw [e]
  exact contDiff_const.sub ((contDiff_id.pow 2).div_const (L ^ 2))

/-- De Sitter's ruler function is smooth of every order where its clock function is not zero. -/
theorem contDiffAt_dsB (L : ℝ) {r : ℝ} (h : dsA L r ≠ 0) : ContDiffAt ℝ ∞ (dsB L) r := by
  have e : dsB L = fun r : ℝ => (dsA L r)⁻¹ := rfl
  rw [e]
  exact (contDiff_dsA L).contDiffAt.inv h

/-- A function of the form `f(r) · h(θ)` is smooth of every order where its two factors are. -/
theorem contDiffAt_top_sep {f h : ℝ → ℝ} {z : Coords 4} (hf : ContDiffAt ℝ ∞ f (z 1))
    (hh : ContDiffAt ℝ ∞ h (z 2)) : ContDiffAt ℝ ∞ (sep f h) z := by
  have h1 : ContDiffAt ℝ ∞ (fun y : Coords 4 => f (y 1)) z :=
    ContDiffAt.comp (g := f) z hf (contDiffAt_apply ℝ (fun _ : Fin 4 => ℝ) 1 z)
  have h2 : ContDiffAt ℝ ∞ (fun y : Coords 4 => h (y 2)) z :=
    ContDiffAt.comp (g := h) z hh (contDiffAt_apply ℝ (fun _ : Fin 4 => ℝ) 2 z)
  exact h1.mul h2

/-- Every entry of a round, unchanging table is smooth of every order where its clock and ruler
functions are. -/
theorem contDiffAt_top_roundG {a b : ℝ → ℝ} {z : Coords 4} (ha : ContDiffAt ℝ ∞ a (z 1))
    (hb : ContDiffAt ℝ ∞ b (z 1)) (i j : Fin 4) : ContDiffAt ℝ ∞ (roundG a b i j) z := by
  by_cases hij : i = j
  · subst hij
    have e : roundG a b i i = sep (gr a b i) (gθ i) := by
      funext w
      simp [roundG, diag, roundDiag]
    rw [e]
    have hgr : ContDiffAt ℝ ∞ (gr a b i) (z 1) := by
      unfold gr
      split_ifs
      · exact ha.neg
      · exact hb
      · exact contDiffAt_id.pow 2
    have hgθ : ContDiffAt ℝ ∞ (gθ i) (z 2) := by
      unfold gθ
      split_ifs
      · exact (Real.contDiff_sin.contDiffAt).pow 2
      · exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (1 : ℝ)) (z 2))
    exact contDiffAt_top_sep hgr hgθ
  · have e : roundG a b i j = fun _ => 0 := by
      funext w
      simp [roundG, diag, hij]
    rw [e]
    exact contDiffAt_const

/-! ## The same from every side -/

/-- A round, unchanging table looks the same from every side, off the poles, whatever its clock
and ruler functions are. (`schwarzschild_isRound` is the case of Schwarzschild's functions.) -/
theorem roundG_isRound (A B : ℝ → ℝ) {p : Coords 4} (hs : sin (p 2) ≠ 0) :
    IsRoundAt (roundG A B) p := by
  have e : roundG A B = genG (fun _ r => A r) (fun _ r => B r) zero2 (onlyR sqF) := by
    rw [genG_diagonal, changingG_static]
  rw [e]
  exact genG_isRound _ _ _ _ hs

/-! ## The three parts of the statement -/

/-- **De Sitter's table is a round table inside its horizon:** at all times, for distance labels
between the centre and the horizon, off the poles. -/
theorem deSitter_roundSetting {L : ℝ} (_hL : 0 < L) :
    RoundSetting (roundG (dsA L) (dsB L)) (roundGinv (dsA L) (dsB L)) univ (Ioo 0 L) where
  openJ := isOpen_univ
  onePieceJ := isPreconnected_univ
  openI := isOpen_Ioo
  onePieceI := isPreconnected_Ioo
  smooth := fun x hx i j =>
    contDiffAt_top_roundG (contDiff_dsA L).contDiffAt
      (contDiffAt_dsB L (deSitter_clock_pos hx.2.1.1 hx.2.1.2).ne') i j
  symm := fun x _ i j => roundG_symm _ _ i j x
  round := fun _ hx => roundG_isRound _ _ hx.sin_ne
  spaceTime := fun x hx => by
    have hA : 0 < dsA L (x 1) := deSitter_clock_pos hx.2.1.1 hx.2.1.2
    have hr : 0 < x 1 := hx.2.1.1
    rw [deSitter_entry_θθ, deSitter_entry_tt, deSitter_entry_rr, deSitter_entry_tr, dsB_eq_inv]
    refine ⟨pow_pos hr 2, ?_⟩
    have h1 : -dsA L (x 1) * (dsA L (x 1))⁻¹ - 0 * 0 = -1 := by
      field_simp
      ring
    rw [h1]
    exact neg_one_lt_zero
  inverse := fun _ hx i k =>
    roundG_mul_roundGinv (deSitter_regular hx.2.1.1 hx.2.1.2 hx.sin_ne) i k

/-- For De Sitter's table the number `sizeSlopeOf`, the squared slope of the size of the spheres,
is the clock function times `4 r²`. -/
theorem deSitter_sizeSlopeOf (L : ℝ) (x : Coords 4) :
    sizeSlopeOf (roundG (dsA L) (dsB L)) x = dsA L (x 1) * (4 * x 1 ^ 2) := by
  have e : roundG (dsA L) (dsB L) 2 2 = sep sqF constOne := by
    funext w
    simp [roundG, diag, roundDiag, gr, gθ]
  unfold sizeSlopeOf
  rw [e, slope_sep_t, slope_sep_r, deriv_sqF, deSitter_entry_tt]
  simp only [constOne]
  ring

/-- **Inside its horizon the size of De Sitter's spheres is a usable distance.** -/
theorem deSitter_sizeSlopeOf_ne_zero {L : ℝ} {x : Coords 4} (hx : InRegion univ (Ioo 0 L) x) :
    sizeSlopeOf (roundG (dsA L) (dsB L)) x ≠ 0 := by
  have hA : 0 < dsA L (x 1) := deSitter_clock_pos hx.2.1.1 hx.2.1.2
  have hr : 0 < x 1 := hx.2.1.1
  rw [deSitter_sizeSlopeOf]
  exact (mul_pos hA (mul_pos four_pos (pow_pos hr 2))).ne'

/-- **De Sitter's table is not empty.** At the point half way to the horizon, on the equator, the
part of its curvature for the pole angle is `3 / L² · (L / 2)²`, which is not zero. -/
theorem deSitter_not_ricciFlat {L : ℝ} (hL : 0 < L) :
    ¬ ∀ x, InRegion univ (Ioo 0 L) x →
      IsRicciFlatAt (roundG (dsA L) (dsB L)) (roundGinv (dsA L) (dsB L)) x := by
  intro hall
  have hL0 : L ≠ 0 := hL.ne'
  have e1 : (![0, L / 2, π / 2, 0] : Coords 4) 1 = L / 2 := by simp
  have e2 : (![0, L / 2, π / 2, 0] : Coords 4) 2 = π / 2 := by simp
  have hx : InRegion univ (Ioo 0 L) (![0, L / 2, π / 2, 0] : Coords 4) := by
    refine ⟨mem_univ _, ?_, ?_, ?_⟩
    · rw [e1]
      exact ⟨half_pos hL, half_lt_self hL⟩
    · rw [e2]
      exact half_pos Real.pi_pos
    · rw [e2]
      exact half_lt_self Real.pi_pos
  have h1 := hall _ hx 2 2
  rw [ricci_deSitter hx.2.1.1 hx.2.1.2 hx.sin_ne, deSitter_entry_θθ, e1] at h1
  exact mul_ne_zero (div_ne_zero three_ne_zero (pow_ne_zero 2 hL0))
    (pow_ne_zero 2 (div_ne_zero hL0 two_ne_zero)) h1

end DeSitterTable

open DeSitterTable in
/-- **"Empty" can fail.** De Sitter's table is a round table inside its horizon, the size of its
spheres is a usable distance there, and it is not empty. So Birkhoff's theorem read both ways
does not hold for the silly reason that every round table is empty. -/
theorem exactlyWhenNotAlwaysEmpty : ExactlyWhenNotAlwaysEmpty :=
  fun _ hL => ⟨deSitter_roundSetting hL, fun _ hx => deSitter_sizeSlopeOf_ne_zero hx,
    deSitter_not_ricciFlat hL⟩

end GravityInLean
