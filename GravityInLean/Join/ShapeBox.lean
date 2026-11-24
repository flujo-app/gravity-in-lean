/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Symmetry

import Mathlib.Tactic

/-!
# The round shape on a small box of angles

Board item `task:join-shape`. `shape_of_round` (`Symmetry.lean`) says: a length measure that is
unchanged by the three standard turns, for all angles, has the general round shape `genG` of four
functions of time and distance. Coordinates that fit the turns (`turnsCoordinates`) only cover a
small box of angles around the point of the equator with angles `(π / 2, 0)`. This file proves the
same shape on such a box.

The proof of `shape_of_round` reads the second turn at the angle `π / 2` around the axis, which a
small box does not contain. Here all is read at the angle `0`: there the first turn `rotX` ties
the entries together, and the second turn `rotY` says that the rest does not depend on the pole
angle. Every step moves the two angles only along straight pieces inside the box.

* `InBox J I δ x`: times in `J`, distance labels in `I`, both angles closer than `δ` to those of
  the equator point.
* `shape_of_round_box`: the shape, on a box.
-/

@[expose] public section

namespace GravityInLean.Join

open Real Filter Topology Set

/-- The box the theorem speaks about: times in `J`, distance labels in `I`, the pole angle closer
than `δ` to `π / 2` and the angle around the axis closer than `δ` to `0`. -/
def InBox (J I : Set ℝ) (δ : ℝ) (x : Coords 4) : Prop :=
  x 0 ∈ J ∧ x 1 ∈ I ∧ |x 2 - π / 2| < δ ∧ |x 3| < δ

/-- In a box of half-width less than `π / 2` the pole angle stays strictly between the poles. -/
theorem InBox.pole {J I : Set ℝ} {δ : ℝ} {x : Coords 4} (hδ' : δ < π / 2) (h : InBox J I δ x) :
    0 < x 2 ∧ x 2 < π := by
  have h2 := abs_lt.1 h.2.2.1
  exact ⟨by linarith [h2.1], by linarith [h2.2]⟩

/-- In a box of half-width less than `π / 2` the sine of the pole angle is not zero. -/
theorem InBox.sin_ne {J I : Set ℝ} {δ : ℝ} {x : Coords 4} (hδ' : δ < π / 2) (h : InBox J I δ x) :
    sin (x 2) ≠ 0 :=
  (Real.sin_pos_of_pos_of_lt_pi (h.pole hδ').1 (h.pole hδ').2).ne'

/-- A box is inside the region of all angles between the poles. -/
theorem InBox.inRegion {J I : Set ℝ} {δ : ℝ} {x : Coords 4} (hδ' : δ < π / 2)
    (h : InBox J I δ x) : InRegion J I x :=
  ⟨h.1, h.2.1, (h.pole hδ').1, (h.pole hδ').2⟩

/-- Moving the angle around the axis to another value in the box stays in the box. -/
theorem InBox.update_three {J I : Set ℝ} {δ : ℝ} {x : Coords 4} (h : InBox J I δ x) {s : ℝ}
    (hs : |s| < δ) : InBox J I δ (Function.update x 3 s) :=
  ⟨by simpa using h.1, by simpa using h.2.1, by simpa using h.2.2.1, by simpa using hs⟩

/-- Moving the pole angle to another value in the box stays in the box. -/
theorem InBox.update_two {J I : Set ℝ} {δ : ℝ} {x : Coords 4} (h : InBox J I δ x) {s : ℝ}
    (hs : |s - π / 2| < δ) : InBox J I δ (Function.update x 2 s) :=
  ⟨by simpa using h.1, by simpa using h.2.1, by simpa using hs, by simpa using h.2.2.2⟩

/-- The point of the equator with time `t` and distance label `ρ` is in the box. -/
theorem inBox_onEquator {J I : Set ℝ} {δ : ℝ} (hδ : 0 < δ) {t ρ : ℝ} (ht : t ∈ J) (hρ : ρ ∈ I) :
    InBox J I δ (onEquator t ρ) :=
  ⟨by simpa [onEquator] using ht, by simpa [onEquator] using hρ, by simpa [onEquator] using hδ,
    by simpa [onEquator] using hδ⟩

/-- **Symmetry gives the shape, on a box.** A length measure that is symmetric, differentiable and
unchanged by the three turns, on a box of angles around the equator point, has the general round
shape there: all sixteen entries are given by four functions of time and distance, read off on the
equator. -/
theorem shape_of_round_box {g : Fin 4 → Fin 4 → Coords 4 → ℝ} {J I : Set ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < π / 2)
    (hsymm : ∀ x, InBox J I δ x → ∀ i j, g i j x = g j i x)
    (hdiff : ∀ x, InBox J I δ x → ∀ i j, DifferentiableAt ℝ (g i j) x)
    (hround : ∀ x, InBox J I δ x → IsRoundAt g x) :
    ∀ x, InBox J I δ x → ∀ i j,
      g i j x = genG (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) i j x := by
  have h0δ : |(0 : ℝ)| < δ := by simpa using hδ
  -- Step 1: nothing depends on the angle around the axis, inside the box.
  have hφslope : ∀ y, InBox J I δ y → ∀ i j, slope 3 (g i j) y = 0 := by
    intro y hy i j
    rw [← lieD_rotZ]
    exact (hround y hy).2.2 i j
  have hφ : ∀ x, InBox J I δ x → ∀ i j, g i j (Function.update x 3 0) = g i j x := by
    intro x hx i j
    have hreg : ∀ u ∈ Ioo (-δ) δ, InBox J I δ (Function.update x 3 u) :=
      fun u hu => hx.update_three (abs_lt.2 ⟨hu.1, hu.2⟩)
    have hd : DifferentiableOn ℝ (fun u => g i j (Function.update x 3 u)) (Ioo (-δ) δ) := by
      intro u hu
      have h := differentiableAt_line (hdiff _ (hreg u hu) i j) 3
      simp only [Function.update_idem, Function.update_self] at h
      exact h.differentiableWithinAt
    have hd0 : (Ioo (-δ) δ).EqOn (deriv fun u => g i j (Function.update x 3 u)) 0 := by
      intro u hu
      have h := hφslope _ (hreg u hu) i j
      simpa [slope] using h
    have hs0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
    have hx3 : x 3 ∈ Ioo (-δ) δ := abs_lt.1 hx.2.2.2
    have hc := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hd hd0 hs0 hx3
    simpa using hc
  -- Step 2: the other two turns, with the first one used.
  have hX : ∀ y, InBox J I δ y → ∀ i j,
      -sin (y 3) * slope 2 (g i j) y
        + g 2 j y * slope i (rotX 2) y + g 3 j y * slope i (rotX 3) y
        + g i 2 y * slope j (rotX 2) y + g i 3 y * slope j (rotX 3) y = 0 := by
    intro y hy i j
    have h := (hround y hy).1 i j
    rw [lieD_rotX, hφslope y hy i j] at h
    linear_combination h
  have hY : ∀ y, InBox J I δ y → ∀ i j,
      cos (y 3) * slope 2 (g i j) y
        + g 2 j y * slope i (rotY 2) y + g 3 j y * slope i (rotY 3) y
        + g i 2 y * slope j (rotY 2) y + g i 3 y * slope j (rotY 3) y = 0 := by
    intro y hy i j
    have h := (hround y hy).2.1 i j
    rw [lieD_rotY, hφslope y hy i j] at h
    linear_combination h
  -- Step 3: the turn `rotX`, read at the angle `0` around the axis, ties the entries together.
  have f03 : ∀ x, InBox J I δ x → g 0 3 x = 0 := by
    intro x hx
    simpa [slope_rotX_two, slope_rotX_three, hφ x hx, deriv_negCot (hx.sin_ne hδ'),
      hx.sin_ne hδ'] using hX _ (hx.update_three h0δ) 0 2
  have f02 : ∀ x, InBox J I δ x → g 0 2 x = 0 := by
    intro x hx
    simpa [slope_rotX_two, slope_rotX_three, hφ x hx, deriv_negCot (hx.sin_ne hδ'),
      hx.sin_ne hδ'] using hX _ (hx.update_three h0δ) 0 3
  have f13 : ∀ x, InBox J I δ x → g 1 3 x = 0 := by
    intro x hx
    simpa [slope_rotX_two, slope_rotX_three, hφ x hx, deriv_negCot (hx.sin_ne hδ'),
      hx.sin_ne hδ'] using hX _ (hx.update_three h0δ) 1 2
  have f12 : ∀ x, InBox J I δ x → g 1 2 x = 0 := by
    intro x hx
    simpa [slope_rotX_two, slope_rotX_three, hφ x hx, deriv_negCot (hx.sin_ne hδ'),
      hx.sin_ne hδ'] using hX _ (hx.update_three h0δ) 1 3
  have f23 : ∀ x, InBox J I δ x → g 2 3 x = 0 := by
    intro x hx
    have hs := hx.sin_ne hδ'
    have h32 := hsymm x hx 3 2
    have h := hX _ (hx.update_three h0δ) 2 2
    simp [slope_rotX_two, slope_rotX_three, hφ x hx, deriv_negCot hs] at h
    field_simp at h
    linarith
  have f33 : ∀ x, InBox J I δ x → g 3 3 x = sin (x 2) ^ 2 * g 2 2 x := by
    intro x hx
    have hs := hx.sin_ne hδ'
    have h := hX _ (hx.update_three h0δ) 2 3
    simp [slope_rotX_two, slope_rotX_three, hφ x hx, deriv_negCot hs] at h
    field_simp at h
    linarith
  -- Step 4: the turn `rotY`, read at the angle `0` around the axis, says the rest does not depend
  -- on the pole angle either.
  have hθslope : ∀ z, InBox J I δ z → z 3 = 0 → ∀ i j, i ≠ 3 → j ≠ 3 →
      slope 2 (g i j) z = 0 := by
    intro z hz hz3 i j hi hj
    simpa [slope_rotY_two, slope_rotY_three, hz3, hi, hj] using hY z hz i j
  have hθ : ∀ x, InBox J I δ x → ∀ i j, i ≠ 3 → j ≠ 3 →
      g i j x = g i j (onEquator (x 0) (x 1)) := by
    intro x hx i j hi hj
    have hx0 : InBox J I δ (Function.update x 3 0) := hx.update_three h0δ
    have hreg : ∀ s ∈ Ioo (π / 2 - δ) (π / 2 + δ),
        InBox J I δ (Function.update (Function.update x 3 0) 2 s) :=
      fun s hs => hx0.update_two (abs_lt.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    have hd : DifferentiableOn ℝ
        (fun s => g i j (Function.update (Function.update x 3 0) 2 s))
        (Ioo (π / 2 - δ) (π / 2 + δ)) := by
      intro s hs
      have h := differentiableAt_line (hdiff _ (hreg s hs) i j) 2
      simp only [Function.update_idem, Function.update_self] at h
      exact h.differentiableWithinAt
    have hd0 : (Ioo (π / 2 - δ) (π / 2 + δ)).EqOn
        (deriv fun s => g i j (Function.update (Function.update x 3 0) 2 s)) 0 := by
      intro s hs
      have h := hθslope _ (hreg s hs) (by simp) i j hi hj
      simpa [slope] using h
    have hmid : π / 2 ∈ Ioo (π / 2 - δ) (π / 2 + δ) := ⟨by linarith, by linarith⟩
    have hx2 : x 2 ∈ Ioo (π / 2 - δ) (π / 2 + δ) := by
      have h2 := abs_lt.1 hx.2.2.1
      exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
    have hc := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hd hd0 hx2 hmid
    have e1 : Function.update (Function.update x 3 0) 2 (x 2) = Function.update x 3 0 := by
      funext k
      fin_cases k <;> simp
    have e2 : Function.update (Function.update x 3 0) 2 (π / 2) = onEquator (x 0) (x 1) := by
      funext k
      fin_cases k <;> simp [onEquator]
    simp only [e1, e2] at hc
    rw [← hc]
    exact (hφ x hx i j).symm
  -- Putting the sixteen entries together.
  intro x hx i j
  have c00 : g 0 0 x = genG (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) 0 0 x := by
    simpa [genG, sep2, gTR, gΘ, negA, constOne, clockOf] using
      hθ x hx 0 0 (by decide) (by decide)
  have c01 : g 0 1 x = genG (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) 0 1 x := by
    simpa [genG, sep2, gTR, gΘ, constOne, crossOf] using hθ x hx 0 1 (by decide) (by decide)
  have c10 : g 1 0 x = genG (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) 1 0 x := by
    rw [hsymm x hx 1 0]
    simpa [genG, sep2, gTR, gΘ, constOne, crossOf] using hθ x hx 0 1 (by decide) (by decide)
  have c11 : g 1 1 x = genG (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) 1 1 x := by
    simpa [genG, sep2, gTR, gΘ, constOne, rulerOf] using hθ x hx 1 1 (by decide) (by decide)
  have c22 : g 2 2 x = genG (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) 2 2 x := by
    simpa [genG, sep2, gTR, gΘ, constOne, sizeOf] using hθ x hx 2 2 (by decide) (by decide)
  have c33 : g 3 3 x = genG (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) 3 3 x := by
    rw [f33 x hx, hθ x hx 2 2 (by decide) (by decide)]
    simp [genG, sep2, gTR, gΘ, sin2, sizeOf]
    ring
  have c02 : g 0 2 x = genG (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) 0 2 x := by
    simpa [genG, sep2, gTR, gΘ, zero2] using f02 x hx
  have c03 : g 0 3 x = genG (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) 0 3 x := by
    simpa [genG, sep2, gTR, gΘ, zero2] using f03 x hx
  have c12 : g 1 2 x = genG (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) 1 2 x := by
    simpa [genG, sep2, gTR, gΘ, zero2] using f12 x hx
  have c13 : g 1 3 x = genG (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) 1 3 x := by
    simpa [genG, sep2, gTR, gΘ, zero2] using f13 x hx
  have c23 : g 2 3 x = genG (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) 2 3 x := by
    simpa [genG, sep2, gTR, gΘ, zero2] using f23 x hx
  have c20 : g 2 0 x = genG (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) 2 0 x := by
    rw [hsymm x hx 2 0]
    simpa [genG, sep2, gTR, gΘ, zero2] using f02 x hx
  have c30 : g 3 0 x = genG (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) 3 0 x := by
    rw [hsymm x hx 3 0]
    simpa [genG, sep2, gTR, gΘ, zero2] using f03 x hx
  have c21 : g 2 1 x = genG (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) 2 1 x := by
    rw [hsymm x hx 2 1]
    simpa [genG, sep2, gTR, gΘ, zero2] using f12 x hx
  have c31 : g 3 1 x = genG (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) 3 1 x := by
    rw [hsymm x hx 3 1]
    simpa [genG, sep2, gTR, gΘ, zero2] using f13 x hx
  have c32 : g 3 2 x = genG (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) 3 2 x := by
    rw [hsymm x hx 3 2]
    simpa [genG, sep2, gTR, gΘ, zero2] using f23 x hx
  fin_cases i <;> fin_cases j
  · exact c00
  · exact c01
  · exact c02
  · exact c03
  · exact c10
  · exact c11
  · exact c12
  · exact c13
  · exact c20
  · exact c21
  · exact c22
  · exact c23
  · exact c30
  · exact c31
  · exact c32
  · exact c33

end GravityInLean.Join
