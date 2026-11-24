/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.BirkhoffFromSymmetry
public import GravityInLean.Join.ShapeBox
public import GravityInLean.Join.Signature

import Mathlib.Tactic

/-!
# From a round, empty table on a box to the setting of the general theorem

Board item `task:join-setting`. Take a table `h` of sixteen functions on a box of angles around
the equator point (`InBox`, `ShapeBox.lean`). Let it be smooth, symmetric, unchanged by the three
standard turns, empty, with one time direction and with spheres of positive size. Then the four
functions of time and distance read off on the equator (`clockOf h`, `rulerOf h`, `crossOf h`,
`sizeOf h`) meet all that the general form of Birkhoff's theorem
(`birkhoff_general_of_sizeEquations`, `BirkhoffGeneral.lean`) asks for:

* they are in its setting `SettingG`: smooth, of the space-time kind, spheres of positive size;
* they solve the size equations at every time and distance of the box;
* they are smooth, as often as one likes, as functions of time and distance.

The proof follows `birkhoff_of_round` (`BirkhoffFromSymmetry.lean`) up to the size equations, with
the box in place of the region of all angles. "Of the space-time kind" is not assumed here as a
sign of a determinant: it comes from "one time direction" (`det2_pos_of_oneTime`,
`Signature.lean`).

* `isOpen_inBox`: the box is open;
* `genG_onEquator`, `eq_gTR_of_shape`: the general round shape, read on the equator;
* `contDiff_onEquator`: the equator point depends smoothly on time and distance;
* `setting_of_box`: the result.
-/

@[expose] public section

namespace GravityInLean.Join

open Real Filter Topology Set

open scoped ContDiff

/-- The box is open when the stretches of time and distance are. -/
theorem isOpen_inBox {J I : Set ℝ} (hJ : IsOpen J) (hI : IsOpen I) (δ : ℝ) :
    IsOpen {x : Coords 4 | InBox J I δ x} := by
  have h0 : IsOpen {x : Coords 4 | x 0 ∈ J} := hJ.preimage (continuous_apply 0)
  have h1 : IsOpen {x : Coords 4 | x 1 ∈ I} := hI.preimage (continuous_apply 1)
  have h2 : IsOpen {x : Coords 4 | |x 2 - π / 2| < δ} :=
    isOpen_lt ((continuous_apply 2).sub continuous_const).abs continuous_const
  have h3 : IsOpen {x : Coords 4 | |x 3| < δ} :=
    isOpen_lt (continuous_apply 3).abs continuous_const
  exact h0.inter (h1.inter (h2.inter h3))

/-- On the equator the angle factor of the general round shape is `1`: each entry is its
time-and-distance part. -/
theorem genG_onEquator (A B C S : ℝ → ℝ → ℝ) (i j : Fin 4) (t ρ : ℝ) :
    genG A B C S i j (onEquator t ρ) = gTR A B C S i j t ρ := by
  have h1 : gΘ i j (π / 2) = 1 := by
    unfold gΘ
    split_ifs <;> simp [sin2, constOne]
  have e : genG A B C S i j (onEquator t ρ) = gTR A B C S i j t ρ * gΘ i j (π / 2) := by
    simp [genG, sep2, onEquator]
  rw [e, h1, mul_one]

/-- The point of the equator depends smoothly on time and distance. -/
theorem contDiff_onEquator {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun q : ℝ × ℝ => onEquator q.1 q.2) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · exact contDiff_fst
  · exact contDiff_snd
  · exact contDiff_const
  · exact contDiff_const

/-- **From a round, empty table on a box to the setting of the general theorem.** A table on a box
of angles that is smooth, symmetric, unchanged by the three turns, empty, with one time direction
and with spheres of positive size gives four functions of time and distance that are in the
setting of the general theorem, solve the size equations, and are smooth. -/
theorem setting_of_box {h hinv : Fin 4 → Fin 4 → Coords 4 → ℝ} {J I : Set ℝ} {δ : ℝ}
    (hJ : IsOpen J) (hJc : IsPreconnected J) (hI : IsOpen I) (hIc : IsPreconnected I)
    (hδ : 0 < δ) (hδ' : δ < π / 2)
    (hsmooth : ∀ x, InBox J I δ x → ∀ i j, ContDiffAt ℝ ∞ (h i j) x)
    (hsymm : ∀ x, InBox J I δ x → ∀ i j, h i j x = h j i x)
    (hround : ∀ x, InBox J I δ x → IsRoundAt h x)
    (hinverse : ∀ x, InBox J I δ x → ∀ i k, ∑ j, h i j x * hinv j k x = if i = k then 1 else 0)
    (hflat : ∀ x, InBox J I δ x → IsRicciFlatAt h hinv x)
    (htime : ∀ x, InBox J I δ x →
      Curved.HasOneTimeDirection fun v w : Coords 4 ↦ Curved.tableMeasure h x v w)
    (hpos : ∀ x, InBox J I δ x → 0 < h 2 2 x) :
    SettingG (clockOf h) (rulerOf h) (crossOf h) (sizeOf h) J I ∧
    (∀ t ∈ J, ∀ ρ ∈ I, SizeEquations (clockOf h) (rulerOf h) (crossOf h) (sizeOf h) t ρ) ∧
    ContDiffOn ℝ ∞ (Function.uncurry (clockOf h)) (J ×ˢ I) ∧
    ContDiffOn ℝ ∞ (Function.uncurry (rulerOf h)) (J ×ˢ I) ∧
    ContDiffOn ℝ ∞ (Function.uncurry (crossOf h)) (J ×ˢ I) ∧
    ContDiffOn ℝ ∞ (Function.uncurry (sizeOf h)) (J ×ˢ I) := by
  -- Symmetry gives the shape, on the box.
  have hshape := shape_of_round_box hδ hδ' hsymm
    (fun x hx i j => (hsmooth x hx i j).differentiableAt (by simp)) hround
  have heq : ∀ {t ρ : ℝ}, t ∈ J → ρ ∈ I → InBox J I δ (onEquator t ρ) :=
    fun ht hρ => inBox_onEquator hδ ht hρ
  -- Smooth along the equator, as often as one likes.
  have hsm : ∀ i j, ∀ q ∈ J ×ˢ I,
      ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => h i j (onEquator q.1 q.2)) q :=
    fun i j q hq => (hsmooth _ (heq hq.1 hq.2) i j).comp q contDiff_onEquator.contDiffAt
  -- Twice, for the setting.
  have hsm2 : ∀ i j, ∀ t ∈ J, ∀ ρ ∈ I, TwiceSmooth (fun t ρ => h i j (onEquator t ρ)) t ρ :=
    fun i j t ht ρ hρ =>
      twiceSmooth_of_equator ((hsmooth _ (heq ht hρ) i j).of_le (by simp))
  -- Of the space-time kind, from "one time direction".
  have hdet : ∀ t ∈ J, ∀ ρ ∈ I, 0 < det2 (clockOf h) (rulerOf h) (crossOf h) t ρ := by
    intro t ht ρ hρ
    have he := heq ht hρ
    have hval : ∀ i j, h i j (onEquator t ρ)
        = gTR (clockOf h) (rulerOf h) (crossOf h) (sizeOf h) i j t ρ :=
      fun i j => (hshape _ he i j).trans (genG_onEquator _ _ _ _ i j t ρ)
    have z02 : h 0 2 (onEquator t ρ) = 0 := by rw [hval]; simp [gTR, zero2]
    have z03 : h 0 3 (onEquator t ρ) = 0 := by rw [hval]; simp [gTR, zero2]
    have z12 : h 1 2 (onEquator t ρ) = 0 := by rw [hval]; simp [gTR, zero2]
    have z13 : h 1 3 (onEquator t ρ) = 0 := by rw [hval]; simp [gTR, zero2]
    have z23 : h 2 3 (onEquator t ρ) = 0 := by rw [hval]; simp [gTR, zero2]
    have z20 : h 2 0 (onEquator t ρ) = 0 := by rw [hval]; simp [gTR, zero2]
    have z30 : h 3 0 (onEquator t ρ) = 0 := by rw [hval]; simp [gTR, zero2]
    have z21 : h 2 1 (onEquator t ρ) = 0 := by rw [hval]; simp [gTR, zero2]
    have z31 : h 3 1 (onEquator t ρ) = 0 := by rw [hval]; simp [gTR, zero2]
    have z32 : h 3 2 (onEquator t ρ) = 0 := by rw [hval]; simp [gTR, zero2]
    have e10 : h 1 0 (onEquator t ρ) = h 0 1 (onEquator t ρ) := hsymm _ he 1 0
    have e33 : h 3 3 (onEquator t ρ) = h 2 2 (onEquator t ρ) := by
      rw [hval 3 3]
      simp [gTR, sizeOf]
    have hk := det2_pos_of_oneTime (T := fun a b => h a b (onEquator t ρ))
      (h 0 0 (onEquator t ρ)) (h 0 1 (onEquator t ρ)) (h 1 1 (onEquator t ρ))
      (h 2 2 (onEquator t ρ)) (h 2 2 (onEquator t ρ))
      (by
        intro v w
        rw [Curved.formOf_apply]
        simp only [Fin.sum_univ_four, z02, z03, z12, z13, z23, z20, z30, z21, z31, z32, e10, e33]
        ring)
      (hpos _ he) (hpos _ he) (htime _ he)
    change 0 < -h 0 0 (onEquator t ρ) * h 1 1 (onEquator t ρ)
      + h 0 1 (onEquator t ρ) * h 0 1 (onEquator t ρ)
    linarith
  have hset : SettingG (clockOf h) (rulerOf h) (crossOf h) (sizeOf h) J I :=
    { openJ := hJ
      onePieceJ := hJc
      openI := hI
      onePieceI := hIc
      smoothA := fun t ht ρ hρ => (hsm2 0 0 t ht ρ hρ).neg
      smoothB := fun t ht ρ hρ => hsm2 1 1 t ht ρ hρ
      smoothC := fun t ht ρ hρ => hsm2 0 1 t ht ρ hρ
      smoothS := fun t ht ρ hρ => hsm2 2 2 t ht ρ hρ
      spaceTime := hdet
      S_pos := fun _ ht _ hρ => hpos _ (heq ht hρ) }
  -- Empty, in the sense of the general round shape, at every point of the equator.
  have hsize : ∀ t ∈ J, ∀ ρ ∈ I,
      SizeEquations (clockOf h) (rulerOf h) (crossOf h) (sizeOf h) t ρ := by
    intro t ht ρ hρ
    have hx : InBox J I δ (onEquator t ρ) := heq ht hρ
    have hnear : ∀ᶠ y in 𝓝 (onEquator t ρ), InBox J I δ y :=
      (isOpen_inBox hJ hI δ).mem_nhds hx
    have hg : ∀ i j, h i j
        =ᶠ[𝓝 (onEquator t ρ)] genG (clockOf h) (rulerOf h) (crossOf h) (sizeOf h) i j :=
      fun i j => hnear.mono fun y hy => hshape y hy i j
    have hgi : ∀ i j, hinv i j
        =ᶠ[𝓝 (onEquator t ρ)] genGinv (clockOf h) (rulerOf h) (crossOf h) (sizeOf h) i j := by
      intro i j
      refine hnear.mono fun y hy => ?_
      have hu := inverse_unique (m := fun i j => h i j y) (a := fun i j => hinv i j y)
        (b := fun i j => genGinv (clockOf h) (rulerOf h) (crossOf h) (sizeOf h) i j y)
        (hinverse y hy) (fun i k => by
          simp only [hshape y hy]
          exact genG_mul_genGinv (hset.spaceTime _ hy.1 _ hy.2.1).ne'
            (hset.S_pos _ hy.1 _ hy.2.1).ne' (hy.sin_ne hδ') i k)
      exact congrFun (congrFun hu i) j
    have hfl := (isRicciFlatAt_congr hg hgi).mp (hflat _ hx)
    have hreg := hset.regular (x := onEquator t ρ) ht hρ (hx.sin_ne hδ')
    exact sizeEquations (hset.spaceTime t ht ρ hρ).ne' (hset.S_pos t ht ρ hρ).ne'
      ((gen_ricciFlat_iff hreg).mp hfl)
  exact ⟨hset, hsize,
    fun q hq => ((hsm 0 0 q hq).neg).contDiffWithinAt,
    fun q hq => (hsm 1 1 q hq).contDiffWithinAt,
    fun q hq => (hsm 0 1 q hq).contDiffWithinAt,
    fun q hq => (hsm 2 2 q hq).contDiffWithinAt⟩

end GravityInLean.Join
