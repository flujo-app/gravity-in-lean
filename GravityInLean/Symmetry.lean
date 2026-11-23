/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.GeneralShape
public import Mathlib.Analysis.Calculus.Deriv.Pi

import Mathlib.Tactic

/-!
# Looking the same from every side

Until now the round shape of the length measure was the starting point. This file derives it.

"Looks the same from every side" is made precise in the usual way: turning space around any axis
through the centre leaves the length measure unchanged. A turn by a small angle moves every point
along a field of arrows; the three fields `rotX`, `rotY`, `rotZ` below belong to the turns around
three axes at right angles. "Unchanged" means that the change of the length measure along the
field, `lieD` (the Lie derivative of the textbooks), is zero. That is Killing's equation.

**What is proved here.**

* `rotX_turns`, `rotY_turns`, `rotZ_turns`: the three fields really are the three turns of
  ordinary space. Each moves the point `(sin θ cos φ, sin θ sin φ, cos θ)` of the unit sphere the
  way a turn around its axis does.
* `shape_of_round`: a length measure that is symmetric, differentiable and unchanged by the three
  turns has the general round shape of `GeneralShape.lean`: its sixteen entries are given by four
  functions of time and distance.
* `genG_isRound`: conversely, the general round shape is unchanged by the three turns. So the
  shape is exactly what the symmetry allows: nothing is lost and nothing is smuggled in.

**What is still assumed.** That there are coordinates `(t, ρ, θ, φ)` in which the turns move only
the two angles, in the usual way. The textbooks get such coordinates from an abstract description
of the symmetry; that needs geometry the standard library does not have yet.
-/

@[expose] public section

namespace GravityInLean

open Real Filter Topology Set

/-! ## How a length measure changes along a field of arrows -/

/-- The change of the length measure `g` when every point is moved a little along the field of
arrows `ξ` (the Lie derivative of the textbooks). -/
noncomputable def lieD {n : ℕ} (g : Fin n → Fin n → Coords n → ℝ) (ξ : Fin n → Coords n → ℝ)
    (i j : Fin n) (x : Coords n) : ℝ :=
  ∑ k, (ξ k x * slope k (g i j) x + g k j x * slope i (ξ k) x + g i k x * slope j (ξ k) x)

/-- Moving along the field `ξ` leaves the length measure `g` unchanged at the point `x`
(Killing's equation). -/
def LeavesUnchangedAt {n : ℕ} (g : Fin n → Fin n → Coords n → ℝ) (ξ : Fin n → Coords n → ℝ)
    (x : Coords n) : Prop :=
  ∀ i j, lieD g ξ i j x = 0

/-- How fast the function `f` changes when the point moves along the field `ξ`. -/
noncomputable def along {n : ℕ} (ξ : Fin n → Coords n → ℝ) (f : Coords n → ℝ) (x : Coords n) :
    ℝ :=
  ∑ k, ξ k x * slope k f x

/-! ## Functions of the two angles -/

/-- A function of the form `f(θ) · h(φ)`, seen as a function of all four coordinates. -/
noncomputable def sepA (f h : ℝ → ℝ) (x : Coords 4) : ℝ := f (x 2) * h (x 3)

theorem slope_sepA_t (f h : ℝ → ℝ) (x : Coords 4) : slope 0 (sepA f h) x = 0 := by
  simp [slope, sepA]

theorem slope_sepA_r (f h : ℝ → ℝ) (x : Coords 4) : slope 1 (sepA f h) x = 0 := by
  simp [slope, sepA]

theorem slope_sepA_θ (f h : ℝ → ℝ) (x : Coords 4) :
    slope 2 (sepA f h) x = deriv f (x 2) * h (x 3) := by
  simp [slope, sepA, deriv_mul_const_field]

theorem slope_sepA_φ (f h : ℝ → ℝ) (x : Coords 4) :
    slope 3 (sepA f h) x = f (x 2) * deriv h (x 3) := by
  simp [slope, sepA, deriv_const_mul_field]

/-- `-cos θ / sin θ`. -/
noncomputable def negCot (θ : ℝ) : ℝ := -(cos θ / sin θ)

/-- `-sin φ`. -/
noncomputable def negSin (φ : ℝ) : ℝ := -sin φ

theorem deriv_negCot {θ : ℝ} (hs : sin θ ≠ 0) : deriv negCot θ = (sin θ ^ 2)⁻¹ := by
  have h : HasDerivAt negCot (-((-sin θ * sin θ - cos θ * cos θ) / sin θ ^ 2)) θ :=
    ((Real.hasDerivAt_cos θ).div (Real.hasDerivAt_sin θ) hs).neg
  rw [h.deriv]
  field_simp
  linear_combination Real.sin_sq_add_cos_sq θ

theorem deriv_negSin (φ : ℝ) : deriv negSin φ = -cos φ := by
  change deriv (fun y => -sin y) φ = -cos φ
  simp

/-! ## The three turns -/

/-- The turn around the axis through the two poles: only the angle around the axis moves. -/
noncomputable def rotZ (k : Fin 4) : Coords 4 → ℝ :=
  if k = 3 then fun _ => 1 else fun _ => 0

/-- The turn around a second axis, through the equator. -/
noncomputable def rotX (k : Fin 4) : Coords 4 → ℝ :=
  if k = 2 then sepA constOne negSin else if k = 3 then sepA negCot cos else fun _ => 0

/-- The turn around the third axis, through the equator at a right angle to the second. -/
noncomputable def rotY (k : Fin 4) : Coords 4 → ℝ :=
  if k = 2 then sepA constOne cos else if k = 3 then sepA negCot sin else fun _ => 0

/-- "Looks the same from every side" at the point `x`: each of the three turns leaves the length
measure unchanged there. -/
def IsRoundAt (g : Fin 4 → Fin 4 → Coords 4 → ℝ) (x : Coords 4) : Prop :=
  LeavesUnchangedAt g rotX x ∧ LeavesUnchangedAt g rotY x ∧ LeavesUnchangedAt g rotZ x

/-- **The field `rotZ` is the turn around the third axis of ordinary space.** A point of the unit
sphere has the three ordinary coordinates `X = sin θ cos φ`, `Y = sin θ sin φ`, `Z = cos θ`. Moving
along `rotZ` changes them at the rates `(-Y, X, 0)`. -/
theorem rotZ_turns (x : Coords 4) :
    along rotZ (sepA sin cos) x = -sepA sin sin x ∧ along rotZ (sepA sin sin) x = sepA sin cos x ∧
      along rotZ (sepA cos constOne) x = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [along, Fin.sum_univ_four, rotZ, slope_sepA_φ, sepA, deriv_constOne]

/-- **The field `rotX` is the turn around the first axis:** it changes `(X, Y, Z)` at the rates
`(0, -Z, Y)`. -/
theorem rotX_turns {x : Coords 4} (hs : sin (x 2) ≠ 0) :
    along rotX (sepA sin cos) x = 0 ∧ along rotX (sepA sin sin) x = -sepA cos constOne x ∧
      along rotX (sepA cos constOne) x = sepA sin sin x := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [along, Fin.sum_univ_four]
    simp [rotX, slope_sepA_θ, slope_sepA_φ, sepA, constOne, negSin, negCot]
    field_simp
    ring
  · simp only [along, Fin.sum_univ_four]
    simp [rotX, slope_sepA_θ, slope_sepA_φ, sepA, constOne, negSin, negCot]
    field_simp
    linear_combination -cos (x 2) * Real.sin_sq_add_cos_sq (x 3)
  · simp only [along, Fin.sum_univ_four]
    simp [rotX, slope_sepA_θ, slope_sepA_φ, sepA, constOne, negSin, negCot, deriv_constOne]
    ring

/-- **The field `rotY` is the turn around the second axis:** it changes `(X, Y, Z)` at the rates
`(Z, 0, -X)`. -/
theorem rotY_turns {x : Coords 4} (hs : sin (x 2) ≠ 0) :
    along rotY (sepA sin cos) x = sepA cos constOne x ∧ along rotY (sepA sin sin) x = 0 ∧
      along rotY (sepA cos constOne) x = -sepA sin cos x := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [along, Fin.sum_univ_four]
    simp [rotY, slope_sepA_θ, slope_sepA_φ, sepA, constOne, negCot]
    field_simp
    linear_combination cos (x 2) * Real.sin_sq_add_cos_sq (x 3)
  · simp only [along, Fin.sum_univ_four]
    simp [rotY, slope_sepA_θ, slope_sepA_φ, sepA, constOne, negCot]
    field_simp
    ring
  · simp only [along, Fin.sum_univ_four]
    simp [rotY, slope_sepA_θ, slope_sepA_φ, sepA, constOne, negCot, deriv_constOne]
    ring

/-! ## The change of a length measure along the three turns, written out -/

theorem lieD_rotZ (g : Fin 4 → Fin 4 → Coords 4 → ℝ) (i j : Fin 4) (x : Coords 4) :
    lieD g rotZ i j x = slope 3 (g i j) x := by
  simp [lieD, Fin.sum_univ_four, rotZ, slope_const]

theorem slope_rotY_two (i : Fin 4) (x : Coords 4) :
    slope i (rotY 2) x = if i = 3 then -sin (x 3) else 0 := by
  fin_cases i <;>
    simp [rotY, slope_sepA_t, slope_sepA_r, slope_sepA_θ, slope_sepA_φ, deriv_constOne, constOne]

theorem slope_rotY_three (i : Fin 4) (x : Coords 4) :
    slope i (rotY 3) x = if i = 2 then deriv negCot (x 2) * sin (x 3)
      else if i = 3 then negCot (x 2) * cos (x 3) else 0 := by
  fin_cases i <;> simp [rotY, slope_sepA_t, slope_sepA_r, slope_sepA_θ, slope_sepA_φ]

theorem slope_rotX_two (i : Fin 4) (x : Coords 4) :
    slope i (rotX 2) x = if i = 3 then -cos (x 3) else 0 := by
  fin_cases i <;>
    simp [rotX, slope_sepA_t, slope_sepA_r, slope_sepA_θ, slope_sepA_φ, deriv_constOne, constOne,
      deriv_negSin]

theorem slope_rotX_three (i : Fin 4) (x : Coords 4) :
    slope i (rotX 3) x = if i = 2 then deriv negCot (x 2) * cos (x 3)
      else if i = 3 then -(negCot (x 2) * sin (x 3)) else 0 := by
  fin_cases i <;> simp [rotX, slope_sepA_t, slope_sepA_r, slope_sepA_θ, slope_sepA_φ]

theorem lieD_rotY (g : Fin 4 → Fin 4 → Coords 4 → ℝ) (i j : Fin 4) (x : Coords 4) :
    lieD g rotY i j x
      = cos (x 3) * slope 2 (g i j) x + negCot (x 2) * sin (x 3) * slope 3 (g i j) x
        + g 2 j x * slope i (rotY 2) x + g 3 j x * slope i (rotY 3) x
        + g i 2 x * slope j (rotY 2) x + g i 3 x * slope j (rotY 3) x := by
  have h0 : rotY 0 = fun _ => 0 := by simp [rotY]
  have h1 : rotY 1 = fun _ => 0 := by simp [rotY]
  have h2 : rotY 2 x = cos (x 3) := by simp [rotY, sepA, constOne]
  have h3 : rotY 3 x = negCot (x 2) * sin (x 3) := by simp [rotY, sepA]
  simp only [lieD, Fin.sum_univ_four]
  rw [h0, h1, h2, h3]
  simp only [slope_const, mul_zero, zero_mul, add_zero, zero_add]
  ring

theorem lieD_rotX (g : Fin 4 → Fin 4 → Coords 4 → ℝ) (i j : Fin 4) (x : Coords 4) :
    lieD g rotX i j x
      = -sin (x 3) * slope 2 (g i j) x + negCot (x 2) * cos (x 3) * slope 3 (g i j) x
        + g 2 j x * slope i (rotX 2) x + g 3 j x * slope i (rotX 3) x
        + g i 2 x * slope j (rotX 2) x + g i 3 x * slope j (rotX 3) x := by
  have h0 : rotX 0 = fun _ => 0 := by simp [rotX]
  have h1 : rotX 1 = fun _ => 0 := by simp [rotX]
  have h2 : rotX 2 x = -sin (x 3) := by simp [rotX, sepA, constOne, negSin]
  have h3 : rotX 3 x = negCot (x 2) * cos (x 3) := by simp [rotX, sepA]
  simp only [lieD, Fin.sum_univ_four]
  rw [h0, h1, h2, h3]
  simp only [slope_const, mul_zero, zero_mul, add_zero, zero_add]
  ring

/-! ## The region -/

/-- The region the theorem speaks about: times in `J`, distance labels in `I`, and the pole angle
strictly between the two poles. The angle around the axis is free. -/
def InRegion (J I : Set ℝ) (x : Coords 4) : Prop := x 0 ∈ J ∧ x 1 ∈ I ∧ 0 < x 2 ∧ x 2 < π

theorem InRegion.sin_ne {J I : Set ℝ} {x : Coords 4} (h : InRegion J I x) : sin (x 2) ≠ 0 :=
  (Real.sin_pos_of_pos_of_lt_pi h.2.2.1 h.2.2.2).ne'

theorem InRegion.update_three {J I : Set ℝ} {x : Coords 4} (h : InRegion J I x) (s : ℝ) :
    InRegion J I (Function.update x 3 s) :=
  ⟨by simpa using h.1, by simpa using h.2.1, by simpa using h.2.2.1, by simpa using h.2.2.2⟩

theorem InRegion.update_two {J I : Set ℝ} {x : Coords 4} (h : InRegion J I x) {s : ℝ}
    (h0 : 0 < s) (hπ : s < π) : InRegion J I (Function.update x 2 s) :=
  ⟨by simpa using h.1, by simpa using h.2.1, by simpa using h0, by simpa using hπ⟩

/-- A function that can be differentiated at a point can be differentiated along each coordinate
line through it. -/
theorem differentiableAt_line {n : ℕ} {f : Coords n → ℝ} {x : Coords n}
    (hf : DifferentiableAt ℝ f x) (k : Fin n) :
    DifferentiableAt ℝ (fun s => f (Function.update x k s)) (x k) := by
  have h1 : DifferentiableAt ℝ (Function.update x k) (x k) :=
    (hasDerivAt_update x k (x k)).differentiableAt
  have h2 : DifferentiableAt ℝ f (Function.update x k (x k)) := by
    rwa [Function.update_eq_self]
  exact h2.comp (x k) h1

/-! ## The shape that symmetry allows -/

/-- The clock function read off from a length measure: minus its time-time entry on the
equator. -/
noncomputable def clockOf (g : Fin 4 → Fin 4 → Coords 4 → ℝ) (t ρ : ℝ) : ℝ :=
  -g 0 0 (onEquator t ρ)

/-- The cross term read off from a length measure. -/
noncomputable def crossOf (g : Fin 4 → Fin 4 → Coords 4 → ℝ) (t ρ : ℝ) : ℝ :=
  g 0 1 (onEquator t ρ)

/-- The ruler function read off from a length measure. -/
noncomputable def rulerOf (g : Fin 4 → Fin 4 → Coords 4 → ℝ) (t ρ : ℝ) : ℝ :=
  g 1 1 (onEquator t ρ)

/-- The size of the spheres read off from a length measure. -/
noncomputable def sizeOf (g : Fin 4 → Fin 4 → Coords 4 → ℝ) (t ρ : ℝ) : ℝ :=
  g 2 2 (onEquator t ρ)

/-- **Symmetry gives the shape.** A length measure that is symmetric, differentiable and
unchanged by the three turns, on a region, has the general round shape there: all sixteen entries
are given by four functions of time and distance, read off on the equator. -/
theorem shape_of_round {g : Fin 4 → Fin 4 → Coords 4 → ℝ} {J I : Set ℝ}
    (hsymm : ∀ x, InRegion J I x → ∀ i j, g i j x = g j i x)
    (hdiff : ∀ x, InRegion J I x → ∀ i j, DifferentiableAt ℝ (g i j) x)
    (hround : ∀ x, InRegion J I x → IsRoundAt g x) :
    ∀ x, InRegion J I x → ∀ i j,
      g i j x = genG (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) i j x := by
  -- Step 1: nothing depends on the angle around the axis.
  have hφslope : ∀ y, InRegion J I y → ∀ i j, slope 3 (g i j) y = 0 := by
    intro y hy i j
    rw [← lieD_rotZ]
    exact (hround y hy).2.2 i j
  have hφ : ∀ x, InRegion J I x → ∀ i j s, g i j (Function.update x 3 s) = g i j x := by
    intro x hx i j s
    have hf : Differentiable ℝ (fun s => g i j (Function.update x 3 s)) := by
      intro u
      have h := differentiableAt_line (hdiff _ (hx.update_three u) i j) 3
      simpa using h
    have hf0 : ∀ u, deriv (fun s => g i j (Function.update x 3 s)) u = 0 := by
      intro u
      have h := hφslope _ (hx.update_three u) i j
      simpa [slope] using h
    have h := is_const_of_deriv_eq_zero hf hf0 s (x 3)
    simpa using h
  -- Step 2: the second turn, with the first one used.
  have hY : ∀ y, InRegion J I y → ∀ i j,
      cos (y 3) * slope 2 (g i j) y
        + g 2 j y * slope i (rotY 2) y + g 3 j y * slope i (rotY 3) y
        + g i 2 y * slope j (rotY 2) y + g i 3 y * slope j (rotY 3) y = 0 := by
    intro y hy i j
    have h := (hround y hy).2.1 i j
    rw [lieD_rotY, hφslope y hy i j] at h
    linear_combination h
  -- Step 3: read at the angle `π / 2` around the axis, it ties the entries together.
  have f03 : ∀ x, InRegion J I x → g 0 3 x = 0 := by
    intro x hx
    simpa [slope_rotY_two, slope_rotY_three, hφ x hx, deriv_negCot hx.sin_ne, hx.sin_ne] using
      hY _ (hx.update_three (π / 2)) 0 2
  have f02 : ∀ x, InRegion J I x → g 0 2 x = 0 := by
    intro x hx
    simpa [slope_rotY_two, slope_rotY_three, hφ x hx, deriv_negCot hx.sin_ne, hx.sin_ne] using
      hY _ (hx.update_three (π / 2)) 0 3
  have f13 : ∀ x, InRegion J I x → g 1 3 x = 0 := by
    intro x hx
    simpa [slope_rotY_two, slope_rotY_three, hφ x hx, deriv_negCot hx.sin_ne, hx.sin_ne] using
      hY _ (hx.update_three (π / 2)) 1 2
  have f12 : ∀ x, InRegion J I x → g 1 2 x = 0 := by
    intro x hx
    simpa [slope_rotY_two, slope_rotY_three, hφ x hx, deriv_negCot hx.sin_ne, hx.sin_ne] using
      hY _ (hx.update_three (π / 2)) 1 3
  have f23 : ∀ x, InRegion J I x → g 2 3 x = 0 := by
    intro x hx
    have hs := hx.sin_ne
    have h32 := hsymm x hx 3 2
    have h := hY _ (hx.update_three (π / 2)) 2 2
    simp [slope_rotY_two, slope_rotY_three, hφ x hx, deriv_negCot hx.sin_ne] at h
    field_simp at h
    linarith
  have f33 : ∀ x, InRegion J I x → g 3 3 x = sin (x 2) ^ 2 * g 2 2 x := by
    intro x hx
    have hs := hx.sin_ne
    have h := hY _ (hx.update_three (π / 2)) 2 3
    simp [slope_rotY_two, slope_rotY_three, hφ x hx, deriv_negCot hx.sin_ne] at h
    field_simp at h
    linarith
  -- Step 4: read at the angle `0` around the axis, it says the rest does not depend on the pole
  -- angle either.
  have hθslope : ∀ z, InRegion J I z → z 3 = 0 → ∀ i j, i ≠ 3 → j ≠ 3 →
      slope 2 (g i j) z = 0 := by
    intro z hz hz3 i j hi hj
    simpa [slope_rotY_two, slope_rotY_three, hz3, hi, hj] using hY z hz i j
  have hθ : ∀ x, InRegion J I x → ∀ i j, i ≠ 3 → j ≠ 3 →
      g i j x = g i j (onEquator (x 0) (x 1)) := by
    intro x hx i j hi hj
    have hx0 : InRegion J I (Function.update x 3 0) := hx.update_three 0
    have hreg : ∀ s ∈ Ioo (0 : ℝ) π,
        InRegion J I (Function.update (Function.update x 3 0) 2 s) :=
      fun s hs => hx0.update_two hs.1 hs.2
    have hd : DifferentiableOn ℝ
        (fun s => g i j (Function.update (Function.update x 3 0) 2 s)) (Ioo 0 π) := by
      intro s hs
      have h := differentiableAt_line (hdiff _ (hreg s hs) i j) 2
      simp only [Function.update_idem, Function.update_self] at h
      exact h.differentiableWithinAt
    have hd0 : (Ioo (0 : ℝ) π).EqOn
        (deriv fun s => g i j (Function.update (Function.update x 3 0) 2 s)) 0 := by
      intro s hs
      have h := hθslope _ (hreg s hs) (by simp) i j hi hj
      simpa [slope] using h
    have hmid : π / 2 ∈ Ioo (0 : ℝ) π := ⟨by positivity, by linarith [Real.pi_pos]⟩
    have hx2 : x 2 ∈ Ioo (0 : ℝ) π := ⟨hx.2.2.1, hx.2.2.2⟩
    have hc := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hd hd0 hx2 hmid
    have e1 : Function.update (Function.update x 3 0) 2 (x 2) = Function.update x 3 0 := by
      funext k
      fin_cases k <;> simp
    have e2 : Function.update (Function.update x 3 0) 2 (π / 2) = onEquator (x 0) (x 1) := by
      funext k
      fin_cases k <;> simp [onEquator]
    simp only [e1, e2] at hc
    rw [← hc]
    exact (hφ x hx i j 0).symm
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

/-- **The shape has the symmetry.** Conversely, the general round shape is unchanged by each of
the three turns, away from the poles and for any four functions. Together with `shape_of_round`:
the general round shape is exactly what "looks the same from every side" allows. -/
theorem genG_isRound (A B C S : ℝ → ℝ → ℝ) {x : Coords 4} (hs : sin (x 2) ≠ 0) :
    IsRoundAt (genG A B C S) x := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · rw [lieD_rotX]
    fin_cases i <;> fin_cases j <;>
      simp [slope_rotX_two, slope_rotX_three, genG, slope_sep2_θ, slope_sep2_φ, sep2, gTR, gΘ,
        deriv_sin2, deriv_constOne, deriv_negCot hs, negA, zero2, sin2, constOne, negCot] <;>
      field_simp <;>
      ring
  · rw [lieD_rotY]
    fin_cases i <;> fin_cases j <;>
      simp [slope_rotY_two, slope_rotY_three, genG, slope_sep2_θ, slope_sep2_φ, sep2, gTR, gΘ,
        deriv_sin2, deriv_constOne, deriv_negCot hs, negA, zero2, sin2, constOne, negCot] <;>
      field_simp <;>
      ring
  · rw [lieD_rotZ]
    exact slope_sep2_φ _ _ x

end GravityInLean
