/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.OneMass.MassGenG
public import GravityInLean.Join.Patch

import Mathlib.Tactic

/-!
# On a patch, the mass is the same at all points near the equator point

Board item `task:checks-mass-box`. The first half of `birkhoff_patch` (`Join/Patch.lean`), which
does not use the usable distance: on a box around the point the table has the general round shape
and is in the setting of the general theorem, so the mass function is the same at all points of
the box (`massFn_const_of_sizeEquations`). With `massAt_of_genG` this is a statement about the
mass said without coordinates.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Mass

open GravityInLean.Curved GravityInLean.Join

open Real Filter Topology Set

open scoped ContDiff

/-- **The mass is the same near the equator point.** A table on an open set around a point with
the angles of the equator point, that is smooth, symmetric, unchanged by the three turns, empty,
with one time direction and spheres of positive size, has at every point near that point the mass
that its mass function gives at that point. No usable distance is assumed. -/
theorem patch_box_mass {h hinv : Fin 4 → Fin 4 → Coords 4 → ℝ} {W : Set (Coords 4)}
    {y₀ : Coords 4} (hW : IsOpen W) (hy₀ : y₀ ∈ W) (h2 : y₀ 2 = π / 2) (h3 : y₀ 3 = 0)
    (hsmooth : ∀ y ∈ W, ∀ i j, ContDiffAt ℝ ∞ (h i j) y)
    (hsymm : ∀ y ∈ W, ∀ i j, h i j y = h j i y)
    (hround : ∀ y ∈ W, IsRoundAt h y)
    (hinverse : ∀ y ∈ W, ∀ i k, ∑ j, h i j y * hinv j k y = if i = k then 1 else 0)
    (hflat : ∀ y ∈ W, IsRicciFlatAt h hinv y)
    (htime : ∀ y ∈ W, Curved.HasOneTimeDirection fun v w : Coords 4 ↦
      Curved.tableMeasure h y v w)
    (hpos : ∀ y ∈ W, 0 < h 2 2 y) :
    ∀ᶠ y in 𝓝 y₀, MassAt (flatMeasure (tableMeasure h)) turns y
      (massFn (clockOf h) (rulerOf h) (crossOf h) (sizeOf h) (y₀ 0) (y₀ 1)) := by
  have hy0 : onEquator (y₀ 0) (y₀ 1) = y₀ := onEquator_self h2 h3
  -- A box inside `W`: the shape, the setting and the size equations hold on it.
  obtain ⟨J, I, δ, hJ, hJc, hI, hIc, ht, hρ, hδ, hδ', hbox⟩ := exists_box_subset hW hy₀ h2 h3
  have hshape := shape_of_round_box hδ hδ' (fun x hx => hsymm x (hbox x hx))
    (fun x hx i j => (hsmooth x (hbox x hx) i j).differentiableAt (by simp))
    (fun x hx => hround x (hbox x hx))
  obtain ⟨hset, hsize, -, -, -, -⟩ := setting_of_box (hinv := hinv) hJ hJc hI hIc hδ hδ'
    (fun x hx => hsmooth x (hbox x hx)) (fun x hx => hsymm x (hbox x hx))
    (fun x hx => hround x (hbox x hx)) (fun x hx => hinverse x (hbox x hx))
    (fun x hx => hflat x (hbox x hx)) (fun x hx => htime x (hbox x hx))
    (fun x hx => hpos x (hbox x hx))
  -- The point lies in the box, and the box is open.
  have hy₀box : InBox J I δ y₀ := by
    have hb := inBox_onEquator (J := J) (I := I) hδ ht hρ
    rwa [hy0] at hb
  have hopen : IsOpen {y | InBox J I δ y} := isOpen_inBox hJ hI δ
  have hev : ∀ᶠ y in 𝓝 y₀, InBox J I δ y := hopen.mem_nhds hy₀box
  refine hev.mono fun y hyb => ?_
  -- Near `y` the table has the round shape, so its mass at `y` is the mass function there,
  have hnear : ∀ᶠ z in 𝓝 y, InBox J I δ z := hopen.mem_nhds hyb
  have hm := massAt_of_genG (hnear.mono fun z hz => hshape z hz) (hyb.sin_ne hδ')
    (hset.S_pos _ hyb.1 _ hyb.2.1) (hset.spaceTime _ hyb.1 _ hyb.2.1).ne'
    ((hsmooth y (hbox y hyb) 2 2).differentiableAt (by simp))
  -- and the mass function has the same value at all points of the box.
  rw [massFn_const_of_sizeEquations hset hsize (y 0) hyb.1 (y₀ 0) ht (y 1) hyb.2.1 (y₀ 1) hρ]
    at hm
  exact hm

end GravityInLean.Mass
