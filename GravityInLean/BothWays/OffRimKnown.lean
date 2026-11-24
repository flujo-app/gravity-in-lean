/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Curved.Goal
public import GravityInLean.BothWays.OffRim

import Mathlib.Tactic

/-!
# The known answers for Schwarzschild's table, on both sides of the rim at once

Board item `task:bothways-known`. The files of the known answers treat Schwarzschild's table
outside the rim (`outside m`) and inside it (`inside m`) as two separate regions. A chart of a
curved space may land outside the rim at some points and inside it at others, so here the same
facts are proved on the one region `offRim m`: the distance label is positive and is not `2 * m`,
and the angle is off the poles. The mass `m` may be any real number.

* `offRim`, `isOpen_offRim`, `mem_offRim`: the region, which is open and contains both older
  regions;
* `schwarzschild_regularTable_offRim`: the table is good there;
* `schwarzschild_ricciFlat_on_offRim`: all sixteen parts of its curvature vanish there;
* `schwarzschild_isSpaceTimeOn_offRim`: one time direction at every point of it;
* `schwarzschild_isRoundOn_offRim`: it looks the same from every side there;
* `schwarzschild_usable_offRim`: the size of the spheres is a usable distance there.
-/

@[expose] public section

namespace GravityInLean.BothWays

open GravityInLean.Curved

open Real Filter Topology Set

/-- Off the rim of the black hole, on either side of it, away from the centre and the poles. -/
def offRim (m : ℝ) : Set (Coords 4) := {x | 0 < x 1 ∧ x 1 ≠ 2 * m ∧ sin (x 2) ≠ 0}

/-- The region off the rim is open: a point close to one of its points is in it too. -/
theorem isOpen_offRim (m : ℝ) : IsOpen (offRim m) :=
  (isOpen_lt continuous_const (continuous_apply 1)).inter
    ((isOpen_ne_fun (continuous_apply 1) continuous_const).inter
      (isOpen_ne_fun (Real.continuous_sin.comp (continuous_apply 2)) continuous_const))

/-- A point outside the rim, or inside it, is off the rim. -/
theorem mem_offRim {m : ℝ} {x : Coords 4} (h : x ∈ outside m ∨ x ∈ inside m) :
    x ∈ offRim m := by
  rcases h with h | h
  · exact ⟨h.1, h.2.1.ne', h.2.2⟩
  · exact ⟨h.1, h.2.1.ne, h.2.2⟩

/-- A point off the rim is outside the rim or inside it. -/
theorem outside_or_inside_of_mem_offRim {m : ℝ} {x : Coords 4} (hx : x ∈ offRim m) :
    x ∈ outside m ∨ x ∈ inside m := by
  rcases lt_or_gt_of_ne hx.2.1 with h | h
  · exact Or.inr ⟨hx.1, h, hx.2.2⟩
  · exact Or.inl ⟨hx.1, h, hx.2.2⟩

/-- Off the rim, Schwarzschild's clock function `1 - 2m/r` is not zero. -/
theorem schwA_ne_zero_of_mem_offRim {m : ℝ} {x : Coords 4} (hx : x ∈ offRim m) :
    schwA m (x 1) ≠ 0 :=
  schwA_ne_zero_offRim hx.1 hx.2.1

/-- Schwarzschild's table is good off the rim, on both sides of it at once: smooth, the same
when its two slots are swapped, and with an inverse. -/
theorem schwarzschild_regularTable_offRim (m : ℝ) :
    IsRegularTableOn (roundG (schwA m) (schwB m)) (roundGinv (schwA m) (schwB m)) (offRim m) :=
  round_regular (isOpen_offRim m) (fun _ hx ↦ smooth_schwA m hx.1.ne')
    (fun _ hx ↦ smooth_schwB m hx.1.ne' (schwA_ne_zero_of_mem_offRim hx))
    (fun _ hx ↦ schwarzschild_regular_offRim m hx.1 hx.2.1 hx.2.2)

/-- At every point off the rim, all sixteen parts of the curvature of Schwarzschild's table
vanish: it is empty on both sides of the rim. -/
theorem schwarzschild_ricciFlat_on_offRim (m : ℝ) :
    ∀ x ∈ offRim m,
      IsRicciFlatAt (roundG (schwA m) (schwB m)) (roundGinv (schwA m) (schwB m)) x :=
  fun _ hx ↦ schwarzschild_ricciFlat_offRim m hx.1 hx.2.1 hx.2.2

/-- Schwarzschild's space-time is a space-time in the sense of `Basic.lean` off the rim: at
every point there is exactly one time direction. Outside the rim it is the time label, inside
the rim it is the distance label. -/
theorem schwarzschild_isSpaceTimeOn_offRim (m : ℝ) :
    IsSpaceTimeOn (flatMeasure (tableMeasure (roundG (schwA m) (schwB m)))) (offRim m) where
  symm := fun _ hx v w ↦ (schwarzschild_regularTable_offRim m).measure_symm hx v w
  oneTime := fun _ hx ↦ by
    rcases lt_or_gt_of_ne hx.2.1 with h | h
    · exact round_oneTime_of_neg (schwA_neg_inside hx.1 h)
        (inv_lt_zero.mpr (schwA_neg_inside hx.1 h)) hx.1.ne' hx.2.2
    · exact round_oneTime_of_pos (schwA_pos_outside hx.1 h)
        (inv_pos.mpr (schwA_pos_outside hx.1 h)) hx.1.ne' hx.2.2
  smooth := (schwarzschild_regularTable_offRim m).isSmoothOn

/-- Schwarzschild's space-time is empty in the sense of `Basic.lean` off the rim, on both sides
of it at once. -/
theorem schwarzschild_isEmptyOn_offRim (m : ℝ) :
    Curved.IsEmptyOn (flatMeasure (tableMeasure (roundG (schwA m) (schwB m)))) (offRim m) :=
  (schwarzschild_regularTable_offRim m).isEmptyOn (schwarzschild_ricciFlat_on_offRim m)

/-- Schwarzschild's space-time looks the same from every side off the rim, on both sides of it
at once: the three turns of ordinary space are smooth, leave the length measure unchanged,
combine the way turns do, and sweep out surfaces on which all lengths are positive. -/
theorem schwarzschild_isRoundOn_offRim (m : ℝ) :
    IsRoundOn (flatMeasure (tableMeasure (roundG (schwA m) (schwB m)))) turns (offRim m) where
  isOpen := isOpen_offRim m
  smooth := by
    intro i
    fin_cases i
    · exact contMDiffOn_arrows_iff.mpr (contDiffOn_pi.2 fun k x hx ↦
        (smooth_rotY (z := x) hx.2.2 k).contDiffWithinAt)
    · exact contMDiffOn_arrows_iff.mpr (contDiffOn_pi.2 fun k x hx ↦
        (smooth_rotX (z := x) hx.2.2 k).contDiffWithinAt)
    · exact contMDiffOn_arrows_iff.mpr (contDiffOn_pi.2 fun k x _ ↦
        (smooth_rotZ x k).contDiffWithinAt)
  unchanged := by
    intro i x hx
    have hg := fun a b ↦ (schwarzschild_regularTable_offRim m).differentiableAt hx a b
    have hround := schwarzschild_isRound m hx.2.2
    fin_cases i
    · exact (leavesUnchangedAt_table_iff hg (differentiableAt_rotY hx.2.2)).mpr hround.2.1
    · exact (leavesUnchangedAt_table_iff hg (differentiableAt_rotX hx.2.2)).mpr hround.1
    · exact (leavesUnchangedAt_table_iff hg (differentiableAt_rotZ x)).mpr hround.2.2
  likeTurns := fun _ hx ↦
    ⟨bracket_rotY_rotX hx.2.2, bracket_rotX_rotZ hx.2.2, bracket_rotZ_rotY hx.2.2⟩
  surfaces := fun x _ ↦ by
    have h := finrank_span_angles
    rw [← span_turns x] at h
    exact h
  positive := fun x hx v hv hne ↦ by
    have hv' : (v : Coords 4)
        ∈ Submodule.span ℝ (Set.range fun i : Fin 3 ↦ (turns i x : Coords 4)) := hv
    rw [span_turns] at hv'
    exact round_pos_on_angles hx.1.ne' hx.2.2 v hv' hne

/-- At every point off the rim, on either side of it, the size of the spheres of
Schwarzschild's space-time is a usable distance. -/
theorem schwarzschild_usable_offRim (m : ℝ) {x : Coords 4} (hx : x ∈ offRim m) :
    UsableDistanceAt (flatMeasure (tableMeasure (roundG (schwA m) (schwB m)))) turns x :=
  round_usable _ _ hx.1.ne' (inv_ne_zero (schwA_ne_zero_of_mem_offRim hx)) hx.2.2

end GravityInLean.BothWays
