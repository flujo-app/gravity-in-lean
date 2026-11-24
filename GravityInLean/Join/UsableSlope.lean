/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Curved.Goal
public import GravityInLean.BirkhoffFromSymmetry

import Mathlib.Tactic

/-!
# "The size of the spheres is a usable distance", in the words of the coordinate theorem

Board item `task:join-usable-slope`. The goal with no coordinates assumes that the size of the
spheres is a usable distance at the point (`Curved.UsableDistanceAt`): there is a step that the
length measure turns into the slope of the squared size, and its own squared length is not zero.
Birkhoff's theorem in coordinates (`BirkhoffFromSymmetry.lean`) assumes instead that a number is
not zero: `sizeSlopeOf`, the slope of the size, squared and measured by the time-distance part of
the table. This file shows that for a table of the round shape `genG` the first gives the second.

* `tableMeasure_of_genG`: the measure of a table that has the round shape at a point, written
  out: a block for time and distance plus two entries for the angles.
* `sizeSq_of_genG`: for such a table the squared size of the spheres, read off from the three
  standard turns, is the entry for the pole angle.
* `sizeSlopeOf_ne_zero_of_usable`: usable distance gives `sizeSlopeOf ≠ 0`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Join

open Real Filter Topology

/-- The measure of a table that has the round shape `genG` at the point `y`, written out: the
block `-A`, `C`, `B` for time and distance, `S` for the pole angle and `S sin² θ` for the other
angle. -/
theorem tableMeasure_of_genG {h : Fin 4 → Fin 4 → Coords 4 → ℝ} {A B C S : ℝ → ℝ → ℝ}
    {y : Coords 4} (hy : ∀ i j, h i j y = genG A B C S i j y) (v w : Coords 4) :
    Curved.tableMeasure h y v w
      = -A (y 0) (y 1) * v 0 * w 0 + C (y 0) (y 1) * (v 0 * w 1 + v 1 * w 0)
        + B (y 0) (y 1) * v 1 * w 1 + S (y 0) (y 1) * v 2 * w 2
        + S (y 0) (y 1) * sin (y 2) ^ 2 * v 3 * w 3 := by
  change Curved.formOf (fun a b ↦ h a b y) v w = _
  rw [Curved.formOf_apply]
  simp +decide only [Fin.sum_univ_four, hy, genG, sep2, gTR, gΘ, negA, zero2, sin2, constOne,
    ite_true, ite_false]
  ring

/-- For a table that has the round shape at the point `y`, off the poles, the squared size of the
spheres that the three standard turns sweep out is the table's entry for the pole angle. -/
theorem sizeSq_of_genG {h : Fin 4 → Fin 4 → Coords 4 → ℝ} {A B C S : ℝ → ℝ → ℝ}
    {y : Coords 4} (hy : ∀ i j, h i j y = genG A B C S i j y) (hs : sin (y 2) ≠ 0) :
    Curved.sizeSq (Curved.flatMeasure (Curved.tableMeasure h)) Curved.turns y = h 2 2 y := by
  have hN : negCot (y 2) ^ 2 * sin (y 2) ^ 2 = cos (y 2) ^ 2 := by
    rw [negCot]
    field_simp
  have hθ := Real.sin_sq_add_cos_sq (y 2)
  have hφ := Real.sin_sq_add_cos_sq (y 3)
  have e : Curved.sizeSq (Curved.flatMeasure (Curved.tableMeasure h)) Curved.turns y
      = (Curved.tableMeasure h y (fun k ↦ rotY k y) (fun k ↦ rotY k y)
        + Curved.tableMeasure h y (fun k ↦ rotX k y) (fun k ↦ rotX k y)
        + Curved.tableMeasure h y (fun k ↦ rotZ k y) (fun k ↦ rotZ k y)) / 2 := rfl
  have h22 : h 2 2 y = S (y 0) (y 1) := by
    rw [hy]
    simp [genG, sep2, gTR, gΘ, constOne]
  rw [e, h22]
  simp +decide only [tableMeasure_of_genG hy, rotX, rotY, rotZ, sepA, constOne, negSin,
    ite_true, ite_false]
  linear_combination (S (y 0) (y 1) / 2 * (1 + cos (y 2) ^ 2)) * hφ + (S (y 0) (y 1) / 2) * hθ
    + (S (y 0) (y 1) / 2 * (sin (y 3) ^ 2 + cos (y 3) ^ 2)) * hN

/-- **Usable distance, in the words of the coordinate theorem.** Take a table `h` that has the
round shape near `y₀`, off the poles, with a pole-angle entry that is not zero and a
time-distance block that is not degenerate. If the size of the spheres is a usable distance at
`y₀`, then the slope of the size, squared and measured by the time-distance block, is not zero
there. -/
theorem sizeSlopeOf_ne_zero_of_usable {h : Fin 4 → Fin 4 → Coords 4 → ℝ} {A B C S : ℝ → ℝ → ℝ}
    {y₀ : Coords 4} (hshape : ∀ᶠ y in 𝓝 y₀, ∀ i j, h i j y = genG A B C S i j y)
    (hs : sin (y₀ 2) ≠ 0) (hS : h 2 2 y₀ ≠ 0)
    (hdet : h 0 0 y₀ * h 1 1 y₀ - h 0 1 y₀ * h 0 1 y₀ ≠ 0)
    (hd : DifferentiableAt ℝ (h 2 2) y₀)
    (hu : Curved.UsableDistanceAt (Curved.flatMeasure (Curved.tableMeasure h)) Curved.turns y₀) :
    sizeSlopeOf h y₀ ≠ 0 := by
  have hy0 : ∀ i j, h i j y₀ = genG A B C S i j y₀ := hshape.self_of_nhds
  -- Near `y₀` the squared size of the spheres is the entry for the pole angle.
  have hev : Curved.sizeSq (Curved.flatMeasure (Curved.tableMeasure h)) Curved.turns
      =ᶠ[𝓝 y₀] h 2 2 := by
    have hopen : IsOpen {y : Coords 4 | sin (y 2) ≠ 0} :=
      isOpen_ne_fun (Real.continuous_sin.comp (continuous_apply 2)) continuous_const
    filter_upwards [hshape, hopen.mem_nhds hs] with y hy hsy
    exact sizeSq_of_genG hy hsy
  -- That entry does not change along the two angles.
  have key : ∀ a : Fin 4, a ≠ 0 → a ≠ 1 → fderiv ℝ (h 2 2) y₀ (Pi.single a 1) = 0 := by
    intro a ha0 ha1
    rw [← slope_eq_fderiv hd a]
    unfold slope
    have ht : Tendsto (fun s : ℝ ↦ Function.update y₀ a s) (𝓝 (y₀ a)) (𝓝 y₀) := by
      have hc := ((continuous_const (y := y₀)).update a
        (continuous_id (X := ℝ))).continuousAt.tendsto (x := y₀ a)
      simpa only [id_eq, Function.update_eq_self] using hc
    have he : (fun s ↦ h 2 2 (Function.update y₀ a s))
        =ᶠ[𝓝 (y₀ a)] fun _ ↦ S (y₀ 0) (y₀ 1) := by
      filter_upwards [ht.eventually hshape] with s hs'
      rw [hs']
      simp [genG, sep2, gTR, gΘ, constOne, Function.update_of_ne (Ne.symm ha0),
        Function.update_of_ne (Ne.symm ha1)]
    rw [he.deriv_eq]
    simp
  -- The step that the usable distance gives, in the words of tables.
  obtain ⟨n, hn, hnn⟩ : ∃ n : Coords 4,
      (∀ w : Coords 4, Curved.tableMeasure h y₀ n w = fderiv ℝ (h 2 2) y₀ w)
        ∧ Curved.tableMeasure h y₀ n n ≠ 0 := by
    obtain ⟨n, hn, hnn⟩ := hu
    refine ⟨n, fun w ↦ ?_, hnn⟩
    have hw := hn w
    rw [Curved.mvfderiv_flat, hev.fderiv_eq] at hw
    exact hw
  have hform := tableMeasure_of_genG hy0
  -- The entries of the table at `y₀` that are used.
  have g00 : h 0 0 y₀ = -A (y₀ 0) (y₀ 1) := by
    rw [hy0]
    simp [genG, sep2, gTR, gΘ, negA, constOne]
  have g01 : h 0 1 y₀ = C (y₀ 0) (y₀ 1) := by
    rw [hy0]
    simp [genG, sep2, gTR, gΘ, constOne]
  have g11 : h 1 1 y₀ = B (y₀ 0) (y₀ 1) := by
    rw [hy0]
    simp [genG, sep2, gTR, gΘ, constOne]
  have g22 : h 2 2 y₀ = S (y₀ 0) (y₀ 1) := by
    rw [hy0]
    simp [genG, sep2, gTR, gΘ, constOne]
  have hS' : S (y₀ 0) (y₀ 1) ≠ 0 := by
    rw [← g22]
    exact hS
  -- What the step does to the four coordinate steps.
  have e0 : -A (y₀ 0) (y₀ 1) * n 0 + C (y₀ 0) (y₀ 1) * n 1
      = fderiv ℝ (h 2 2) y₀ (Pi.single 0 1) := by
    rw [← hn (Pi.single 0 1), hform]
    simp +decide only [Pi.single_apply, ite_true, ite_false]
    ring
  have e1 : C (y₀ 0) (y₀ 1) * n 0 + B (y₀ 0) (y₀ 1) * n 1
      = fderiv ℝ (h 2 2) y₀ (Pi.single 1 1) := by
    rw [← hn (Pi.single 1 1), hform]
    simp +decide only [Pi.single_apply, ite_true, ite_false]
    ring
  have e2 : S (y₀ 0) (y₀ 1) * n 2 = 0 := by
    rw [← key 2 (by decide) (by decide), ← hn (Pi.single 2 1), hform]
    simp +decide only [Pi.single_apply, ite_true, ite_false]
    ring
  have e3 : S (y₀ 0) (y₀ 1) * sin (y₀ 2) ^ 2 * n 3 = 0 := by
    rw [← key 3 (by decide) (by decide), ← hn (Pi.single 3 1), hform]
    simp +decide only [Pi.single_apply, ite_true, ite_false]
    ring
  -- The step has no part along the angles.
  have n2 : n 2 = 0 := (mul_eq_zero.mp e2).resolve_left hS'
  have n3 : n 3 = 0 := (mul_eq_zero.mp e3).resolve_left (mul_ne_zero hS' (pow_ne_zero 2 hs))
  -- The squared length of the step, times the determinant of the block, is minus the number of
  -- the coordinate theorem.
  have hQ : (h 0 0 y₀ * h 1 1 y₀ - h 0 1 y₀ * h 0 1 y₀) * Curved.tableMeasure h y₀ n n
      = -sizeSlopeOf h y₀ := by
    unfold sizeSlopeOf
    rw [hform, slope_eq_fderiv hd 0, slope_eq_fderiv hd 1, ← e0, ← e1, g00, g01, g11, n2, n3]
    ring
  intro hz
  rw [hz, neg_zero] at hQ
  rcases mul_eq_zero.mp hQ with h1 | h1
  · exact hdet h1
  · exact hnn h1

end GravityInLean.Join
