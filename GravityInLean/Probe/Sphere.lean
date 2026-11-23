/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Algebra.BigOperators.Fin

import Mathlib.Tactic

/-!
# Probe: curvature from the general formulas, tried on a sphere

Pieces B and C start from formulas taken out of textbooks. To close that gap one has to compute
curvature *from its general definition*. The standard library has no curvature yet, so this file
tries the most direct route: the classic coordinate formulas.

* `slope i f x`: how fast `f` changes when only coordinate `i` moves.
* `christoffel g ginv`: the "connection" belonging to a way of measuring lengths `g`
  (it says how straight lines look in the chosen coordinates).
* `ricci Γ`: the curvature built from a connection.

These three definitions work for any number of coordinates, so they also cover a space-time.
As a first test they are run on the simplest curved thing there is, the surface of a ball of
radius 1, with the pole angle `x 0` and the angle around `x 1` as coordinates.

**Result:** the curvature of the sphere comes out equal to its own length measure
(`ricci = 1` along the pole angle, `ricci = sin²` around), as every textbook says.
That is the same kind of computation the one-mass solution needs, only smaller.
-/

@[expose] public section

namespace GravityInLean

open Real

/-- A point described by `n` coordinates. -/
abbrev Coords (n : ℕ) := Fin n → ℝ

/-- How fast `f` changes at `x` when only coordinate `i` moves. -/
noncomputable def slope {n : ℕ} (i : Fin n) (f : Coords n → ℝ) (x : Coords n) : ℝ :=
  deriv (fun s => f (Function.update x i s)) (x i)

/-- If `f` only looks at coordinate `i`, its slope along `i` is the ordinary slope. -/
theorem slope_along {n : ℕ} (i : Fin n) (F : ℝ → ℝ) (x : Coords n) :
    slope i (fun y => F (y i)) x = deriv F (x i) := by
  simp [slope]

/-- If `f` only looks at another coordinate `j`, it does not change along `i`. -/
theorem slope_across {n : ℕ} {i j : Fin n} (h : j ≠ i) (F : ℝ → ℝ) (x : Coords n) :
    slope i (fun y => F (y j)) x = 0 := by
  simp [slope, Function.update_of_ne h]

/-- Something that is the same everywhere has no slope. -/
theorem slope_const {n : ℕ} (i : Fin n) (c : ℝ) (x : Coords n) :
    slope i (fun _ => c) x = 0 := by
  simp [slope]

/-- The connection belonging to a length measure `g` with inverse `ginv`
(the Christoffel symbols of the textbooks). -/
noncomputable def christoffel {n : ℕ} (g ginv : Fin n → Fin n → Coords n → ℝ)
    (a b c : Fin n) : Coords n → ℝ := fun x =>
  (1 / 2) * ∑ d, ginv a d x * (slope b (g d c) x + slope c (g d b) x - slope d (g b c) x)

/-- The curvature built from a connection `Γ` (the Ricci tensor of the textbooks). -/
noncomputable def ricci {n : ℕ} (Γ : Fin n → Fin n → Fin n → Coords n → ℝ)
    (b c : Fin n) (x : Coords n) : ℝ :=
  ∑ a, slope a (Γ a b c) x - ∑ a, slope c (Γ a b a) x
    + ∑ a, ∑ d, Γ a a d x * Γ d b c x - ∑ a, ∑ d, Γ a c d x * Γ d b a x

/-! ## The sphere of radius 1 -/

/-- Lengths on the sphere: one step in the pole angle has length 1, one step around has length
`sin` of the pole angle. -/
noncomputable def sphereG (i j : Fin 2) : Coords 2 → ℝ := fun x =>
  if i = j then (if i = 0 then 1 else sin (x 0) ^ 2) else 0

/-- The inverse of `sphereG`. -/
noncomputable def sphereGinv (i j : Fin 2) : Coords 2 → ℝ := fun x =>
  if i = j then (if i = 0 then 1 else (sin (x 0) ^ 2)⁻¹) else 0

/-- `sphereGinv` really is the inverse of `sphereG`, away from the poles. -/
theorem sphereG_mul_sphereGinv {x : Coords 2} (h : sin (x 0) ≠ 0) (i k : Fin 2) :
    ∑ j, sphereG i j x * sphereGinv j k x = if i = k then 1 else 0 := by
  fin_cases i <;> fin_cases k <;> simp [sphereG, sphereGinv, h]

/-- The connection of the sphere, written out, as a function of the pole angle. -/
noncomputable def sphereΓ (a b c : Fin 2) : ℝ → ℝ := fun θ =>
  if a = 0 ∧ b = 1 ∧ c = 1 then -(sin θ * cos θ)
  else if a = 1 ∧ ((b = 0 ∧ c = 1) ∨ (b = 1 ∧ c = 0)) then (sin θ ^ 2)⁻¹ * (sin θ * cos θ)
  else 0

theorem slope_sin_sq_zero (x : Coords 2) :
    slope 0 (fun y : Coords 2 => sin (y 0) ^ 2) x = 2 * sin (x 0) * cos (x 0) := by
  rw [slope_along 0 (fun t => sin t ^ 2) x]
  have hs : HasDerivAt sin (cos (x 0)) (x 0) := Real.hasDerivAt_sin (x 0)
  have h : HasDerivAt (fun t => sin t ^ 2) (2 * sin (x 0) * cos (x 0)) (x 0) := by
    convert HasDerivAt.pow hs 2 using 1
    simp
  exact h.deriv

theorem slope_sin_sq_one (x : Coords 2) :
    slope 1 (fun y : Coords 2 => sin (y 0) ^ 2) x = 0 :=
  slope_across (by decide) (fun t => sin t ^ 2) x

/-- The general formula for the connection, applied to the sphere, gives `sphereΓ`. -/
theorem christoffel_sphere (a b c : Fin 2) :
    christoffel sphereG sphereGinv a b c = fun x => sphereΓ a b c (x 0) := by
  funext x
  unfold christoffel sphereG sphereGinv sphereΓ
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [slope_const, slope_sin_sq_zero, slope_sin_sq_one] <;>
    ring

/-- The slope of `-(sin · cos)`. -/
theorem hasDerivAt_sphereΓ_011 (θ : ℝ) :
    HasDerivAt (sphereΓ 0 1 1) (-(cos θ ^ 2 - sin θ ^ 2)) θ := by
  have hs : HasDerivAt sin (cos θ) θ := Real.hasDerivAt_sin θ
  have hc : HasDerivAt cos (-sin θ) θ := Real.hasDerivAt_cos θ
  have h : HasDerivAt (fun t => -(sin t * cos t)) (-(cos θ * cos θ + sin θ * -sin θ)) θ :=
    HasDerivAt.neg (HasDerivAt.mul hs hc)
  convert h using 1
  · funext t; simp [sphereΓ]
  · ring

/-- The slope of `cos / sin`, written as `(sin²)⁻¹ · (sin · cos)`, away from the poles. -/
theorem hasDerivAt_sphereΓ_101 {θ : ℝ} (h : sin θ ≠ 0) :
    HasDerivAt (sphereΓ 1 0 1) (-(sin θ ^ 2)⁻¹) θ := by
  have hs : HasDerivAt sin (cos θ) θ := Real.hasDerivAt_sin θ
  have hc : HasDerivAt cos (-sin θ) θ := Real.hasDerivAt_cos θ
  have hsq : HasDerivAt (fun t => sin t ^ 2) (2 * sin θ * cos θ) θ := by
    convert HasDerivAt.pow hs 2 using 1
    simp
  have h1 : HasDerivAt (fun t => (sin t ^ 2)⁻¹) (-(2 * sin θ * cos θ) / (sin θ ^ 2) ^ 2) θ :=
    HasDerivAt.inv hsq (pow_ne_zero 2 h)
  have h2 : HasDerivAt (fun t => (sin t ^ 2)⁻¹ * (sin t * cos t))
      (-(2 * sin θ * cos θ) / (sin θ ^ 2) ^ 2 * (sin θ * cos θ)
        + (sin θ ^ 2)⁻¹ * (cos θ * cos θ + sin θ * -sin θ)) θ :=
    HasDerivAt.mul h1 (HasDerivAt.mul hs hc)
  convert h2 using 1
  · funext t; simp [sphereΓ]
  · have hc2 : cos θ ^ 2 = 1 - sin θ ^ 2 := by linarith [Real.sin_sq_add_cos_sq θ]
    field_simp
    ring_nf
    rw [hc2]
    ring

/-- **Probe result, part 1.** Along the pole angle the curvature of the sphere is 1. -/
theorem ricci_sphere_00 {x : Coords 2} (h : sin (x 0) ≠ 0) :
    ricci (christoffel sphereG sphereGinv) 0 0 x = 1 := by
  have d101 := (hasDerivAt_sphereΓ_101 h).deriv
  simp only [ricci, christoffel_sphere, Fin.sum_univ_two]
  rw [slope_along 0 (sphereΓ 0 0 0) x, slope_along 0 (sphereΓ 1 0 1) x,
    slope_across (by decide) (sphereΓ 1 0 0) x, d101]
  simp [sphereΓ]
  field_simp
  ring_nf
  linarith [Real.sin_sq_add_cos_sq (x 0)]

/-- **Probe result, part 2.** Around the sphere the curvature is `sin²` of the pole angle:
again exactly the sphere's own length measure. -/
theorem ricci_sphere_11 {x : Coords 2} (h : sin (x 0) ≠ 0) :
    ricci (christoffel sphereG sphereGinv) 1 1 x = sin (x 0) ^ 2 := by
  have d011 := (hasDerivAt_sphereΓ_011 (x 0)).deriv
  simp only [ricci, christoffel_sphere, Fin.sum_univ_two]
  rw [slope_along 0 (sphereΓ 0 1 1) x, slope_across (by decide) (sphereΓ 1 1 1) x,
    slope_across (by decide) (sphereΓ 0 1 0) x, d011]
  simp [sphereΓ]
  field_simp
  ring

/-- A part of the connection that is zero everywhere has no slope. -/
theorem deriv_sphereΓ_001 (θ : ℝ) : deriv (sphereΓ 0 0 1) θ = 0 := by
  have h : sphereΓ 0 0 1 = fun _ => 0 := by
    funext t
    simp [sphereΓ]
  rw [h]
  simp

/-- A part of the connection that is zero everywhere has no slope. -/
theorem deriv_sphereΓ_111 (θ : ℝ) : deriv (sphereΓ 1 1 1) θ = 0 := by
  have h : sphereΓ 1 1 1 = fun _ => 0 := by
    funext t
    simp [sphereΓ]
  rw [h]
  simp

/-- **Probe result, part 3.** The mixed part of the sphere's curvature vanishes. -/
theorem ricci_sphere_01 (x : Coords 2) :
    ricci (christoffel sphereG sphereGinv) 0 1 x = 0 := by
  simp only [ricci, christoffel_sphere, Fin.sum_univ_two]
  rw [slope_along 0 (sphereΓ 0 0 1) x, slope_across (by decide) (sphereΓ 1 0 1) x,
    slope_across (by decide) (sphereΓ 0 0 0) x, deriv_sphereΓ_001]
  simp [sphereΓ]

/-- **Probe result, part 4.** The same for the other mixed part. -/
theorem ricci_sphere_10 (x : Coords 2) :
    ricci (christoffel sphereG sphereGinv) 1 0 x = 0 := by
  simp only [ricci, christoffel_sphere, Fin.sum_univ_two]
  rw [slope_along 0 (sphereΓ 0 1 0) x, slope_across (by decide) (sphereΓ 1 1 0) x,
    slope_along 0 (sphereΓ 1 1 1) x, deriv_sphereΓ_111]
  simp [sphereΓ]

/-- **Probe result, all parts together.** Away from the poles, the curvature of the sphere,
computed from the general formulas, equals the sphere's own length measure. -/
theorem ricci_sphere {x : Coords 2} (h : sin (x 0) ≠ 0) :
    ∀ i j : Fin 2, ricci (christoffel sphereG sphereGinv) i j x = sphereG i j x := by
  simp only [Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [ricci_sphere_00 h]
    simp [sphereG]
  · rw [ricci_sphere_01 x]
    simp [sphereG]
  · rw [ricci_sphere_10 x]
    simp [sphereG]
  · rw [ricci_sphere_11 h]
    simp [sphereG]

end GravityInLean
