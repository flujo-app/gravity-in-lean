/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.ExactlyWhen
public import GravityInLean.Join.NewTime

import Mathlib.Tactic

/-!
# From "empty" to "Schwarzschild's after new labels", in coordinates

Board item `task:bothways-coords-forward`. One direction of the "exactly when" in coordinates
(`BirkhoffExactlyWhenInCoordinates`, `Goals/ExactlyWhen.lean`): a round table that is empty, on a
region where the size of the spheres is a usable distance, is Schwarzschild's after new labels
for time and distance (`IsSchwarzschildRelabelled`).

This is Birkhoff's theorem from symmetry (`birkhoff_of_round`, `BirkhoffFromSymmetry.lean`) with
three things added to its conclusion: the new time is smooth of every order, the radius is smooth
of every order, and the radius is nowhere `2 M`. The proof follows that of `birkhoff_of_round`
up to the size equations, and ends with the smooth form of the general theorem
(`Join.birkhoff_general_smooth`, `Join/NewTime.lean`) in place of the differentiable one.

* `RoundSetting.roundEmpty`: a round table that is empty is a round, empty space-time;
* `RoundSetting.contDiffOn_equator`: every entry of a round table, read on the equator, is a
  smooth function of time and distance;
* `relabelled_of_empty`: the result.
-/

@[expose] public section

namespace GravityInLean

open Real Filter Topology Set

open scoped ContDiff

/-- A round table (`RoundSetting`) on which space is empty is a round, empty space-time
(`RoundEmpty`): smooth of every order is in particular twice smooth. -/
theorem RoundSetting.roundEmpty {g ginv : Fin 4 → Fin 4 → Coords 4 → ℝ} {J I : Set ℝ}
    (h : RoundSetting g ginv J I)
    (hempty : ∀ x, InRegion J I x → IsRicciFlatAt g ginv x) : RoundEmpty g ginv J I where
  openJ := h.openJ
  onePieceJ := h.onePieceJ
  openI := h.openI
  onePieceI := h.onePieceI
  smooth := fun x hx i j => (h.smooth x hx i j).of_le (by simp)
  symm := h.symm
  round := h.round
  spaceTime := h.spaceTime
  inverse := h.inverse
  empty := hempty

/-- Every entry of a round table, read on the equator, is a smooth function of time and
distance, of every order, at the times and distance labels of the region. -/
theorem RoundSetting.contDiffOn_equator {g ginv : Fin 4 → Fin 4 → Coords 4 → ℝ} {J I : Set ℝ}
    (h : RoundSetting g ginv J I) (i j : Fin 4) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => g i j (onEquator q.1 q.2)) (J ×ˢ I) := by
  -- The point of the equator depends smoothly on time and distance.
  have heq : ContDiff ℝ ∞ (fun q : ℝ × ℝ => onEquator q.1 q.2) := by
    refine contDiff_pi.2 fun k => ?_
    fin_cases k
    · exact contDiff_fst
    · exact contDiff_snd
    · exact contDiff_const
    · exact contDiff_const
  intro q hq
  exact ((h.smooth _ (onEquator_inRegion hq.1 hq.2) i j).comp q heq.contDiffAt).contDiffWithinAt

/-- **From "empty" to "Schwarzschild's after new labels".** Take a round table on a region where
the size of the spheres is a usable distance. If space is empty on the region, then there are a
mass `M` and a new time `T`, smooth of every order, such that with `T` for time and "radius of
the sphere" for distance the radius is smooth too, the two new labels really are coordinates
near every point, the radius is nowhere `2 M`, and the length of every step equals
Schwarzschild's length of the same step. -/
theorem relabelled_of_empty {g ginv : Fin 4 → Fin 4 → Coords 4 → ℝ} {J I : Set ℝ}
    (h : RoundSetting g ginv J I)
    (husable : ∀ x, InRegion J I x → sizeSlopeOf g x ≠ 0)
    (hempty : ∀ x, InRegion J I x → IsRicciFlatAt g ginv x) :
    IsSchwarzschildRelabelled g J I := by
  have hre : RoundEmpty g ginv J I := h.roundEmpty hempty
  -- Symmetry gives the shape.
  have hshape := shape_of_round hre.symm
    (fun x hx i j => (hre.smooth x hx i j).differentiableAt (by simp)) hre.round
  have hset := hre.settingG
  -- The four functions read off on the equator are smooth of every order.
  have hA : ContDiffOn ℝ ∞ (Function.uncurry (clockOf g)) (J ×ˢ I) :=
    (h.contDiffOn_equator 0 0).neg
  have hB : ContDiffOn ℝ ∞ (Function.uncurry (rulerOf g)) (J ×ˢ I) := h.contDiffOn_equator 1 1
  have hC : ContDiffOn ℝ ∞ (Function.uncurry (crossOf g)) (J ×ˢ I) := h.contDiffOn_equator 0 1
  have hS : ContDiffOn ℝ ∞ (Function.uncurry (sizeOf g)) (J ×ˢ I) := h.contDiffOn_equator 2 2
  -- Empty, in the sense of the general round shape, at every point of the equator.
  have hsize : ∀ t ∈ J, ∀ ρ ∈ I,
      SizeEquations (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) t ρ := by
    intro t ht ρ hρ
    have hx : InRegion J I (onEquator t ρ) := onEquator_inRegion ht hρ
    have hnear : ∀ᶠ y in 𝓝 (onEquator t ρ), InRegion J I y :=
      (isOpen_inRegion h.openJ h.openI).mem_nhds hx
    have hg : ∀ i j, g i j
        =ᶠ[𝓝 (onEquator t ρ)] genG (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) i j :=
      fun i j => hnear.mono fun y hy => hshape y hy i j
    have hgi : ∀ i j, ginv i j
        =ᶠ[𝓝 (onEquator t ρ)] genGinv (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) i j := by
      intro i j
      refine hnear.mono fun y hy => ?_
      have hu := inverse_unique (m := fun i j => g i j y) (a := fun i j => ginv i j y)
        (b := fun i j => genGinv (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) i j y)
        (h.inverse y hy) (fun i k => by
          simp only [hshape y hy]
          exact genG_mul_genGinv (hset.spaceTime _ hy.1 _ hy.2.1).ne'
            (hset.S_pos _ hy.1 _ hy.2.1).ne' hy.sin_ne i k)
      exact congrFun (congrFun hu i) j
    have hflat := (isRicciFlatAt_congr hg hgi).mp (hempty _ hx)
    have hreg := hset.regular (x := onEquator t ρ) ht hρ hx.sin_ne
    exact sizeEquations (hset.spaceTime t ht ρ hρ).ne' (hset.S_pos t ht ρ hρ).ne'
      ((gen_ricciFlat_iff hreg).mp hflat)
  -- The size of the spheres is a usable distance.
  have hn : ∀ t ∈ J, ∀ ρ ∈ I,
      sizeSlopeSq (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) t ρ ≠ 0 := by
    intro t ht ρ hρ
    have hu := husable _ (onEquator_inRegion (J := J) (I := I) ht hρ)
    have e : sizeSlopeSq (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) t ρ
        = sizeSlopeOf g (onEquator t ρ) := by
      simp only [sizeSlopeSq, sizeSlopeOf, slope_zero_onEquator, slope_one_onEquator]
      rfl
    rwa [e]
  -- The general theorem, with smooth new labels and the radius off the rim.
  obtain ⟨M, T, hT, hR, hall⟩ := Join.birkhoff_general_smooth hset hA hB hC hS hsize hn
  refine ⟨M, T, hT, hR, fun x hx => ?_⟩
  obtain ⟨-, hrim, hjac, hlen⟩ := hall x hx.1 hx.2.1
  refine ⟨hjac, fun e => hrim e.symm, fun v => ?_⟩
  rw [← hlen v]
  simp only [stepLength, hshape x hx]

end GravityInLean
