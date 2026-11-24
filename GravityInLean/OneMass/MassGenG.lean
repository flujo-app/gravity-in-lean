/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.OneMass.Mass
public import GravityInLean.BirkhoffGeneral
public import GravityInLean.Join.UsableSlope

import Mathlib.Tactic

/-!
# The mass of a table of the general round shape is its mass function

Board item `task:checks-mass-geng`. For a table that has the general round shape `genG A B C S`
near a point, the mass at that point, said without coordinates (`MassAt`, with the three standard
turns), is the mass function `massFn A B C S` of the coordinate theorem.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Mass

open GravityInLean.Curved GravityInLean.Join

open Real Filter Topology

/-- **The mass of the general round shape.** Take a table `h` that has the round shape near
`y₀`, off the poles, with a time-distance block that is not degenerate. Then the mass at `y₀` is
the mass function of the four functions, taken at the time and distance labels of `y₀`. The step
that points the way the spheres grow has parts `((C S_ρ - B S_t) / D, (A S_ρ + C S_t) / D, 0, 0)`
with `D = A B + C²`; its squared length is `sizeSlopeSq / D`. -/
theorem massAt_of_genG {h : Fin 4 → Fin 4 → Coords 4 → ℝ} {A B C S : ℝ → ℝ → ℝ}
    {y₀ : Coords 4} (hshape : ∀ᶠ y in 𝓝 y₀, ∀ i j, h i j y = genG A B C S i j y)
    (hs : sin (y₀ 2) ≠ 0) (hS : 0 < S (y₀ 0) (y₀ 1)) (hdet : det2 A B C (y₀ 0) (y₀ 1) ≠ 0)
    (hd : DifferentiableAt ℝ (h 2 2) y₀) :
    MassAt (flatMeasure (tableMeasure h)) turns y₀ (massFn A B C S (y₀ 0) (y₀ 1)) := by
  -- That the entry for the pole angle is positive is not used by this proof: the formula
  -- `massOf` is read the same way for any number. It stays in the statement for the callers.
  have _ := hS
  have hy0 : ∀ i j, h i j y₀ = genG A B C S i j y₀ := hshape.self_of_nhds
  -- Near `y₀` the squared size of the spheres is the entry for the pole angle.
  have hev : sizeSq (flatMeasure (tableMeasure h)) turns =ᶠ[𝓝 y₀] h 2 2 := by
    have hopen : IsOpen {y : Coords 4 | sin (y 2) ≠ 0} :=
      isOpen_ne_fun (Real.continuous_sin.comp (continuous_apply 2)) continuous_const
    filter_upwards [hshape, hopen.mem_nhds hs] with y hy hsy
    exact sizeSq_of_genG hy hsy
  have hsz : sizeSq (flatMeasure (tableMeasure h)) turns y₀ = S (y₀ 0) (y₀ 1) := by
    rw [sizeSq_of_genG hy0 hs, hy0]
    simp [genG, sep2, gTR, gΘ, constOne]
  -- Moving one coordinate of `y₀` a little stays near `y₀`.
  have ht : ∀ a : Fin 4, Tendsto (fun s : ℝ ↦ Function.update y₀ a s) (𝓝 (y₀ a)) (𝓝 y₀) := by
    intro a
    have hc := ((continuous_const (y := y₀)).update a
      (continuous_id (X := ℝ))).continuousAt.tendsto (x := y₀ a)
    simpa only [id_eq, Function.update_eq_self] using hc
  -- The slopes of that entry: those of `S` along time and distance, none along the angles.
  have s0 : slope 0 (h 2 2) y₀ = dt S (y₀ 0) (y₀ 1) := by
    unfold slope dt
    have he : (fun s ↦ h 2 2 (Function.update y₀ 0 s)) =ᶠ[𝓝 (y₀ 0)] fun s ↦ S s (y₀ 1) := by
      filter_upwards [(ht 0).eventually hshape] with s hs'
      rw [hs']
      simp [genG, sep2, gTR, gΘ, constOne]
    rw [he.deriv_eq]
  have s1 : slope 1 (h 2 2) y₀ = dr S (y₀ 0) (y₀ 1) := by
    unfold slope dr
    have he : (fun s ↦ h 2 2 (Function.update y₀ 1 s)) =ᶠ[𝓝 (y₀ 1)] fun s ↦ S (y₀ 0) s := by
      filter_upwards [(ht 1).eventually hshape] with s hs'
      rw [hs']
      simp [genG, sep2, gTR, gΘ, constOne]
    rw [he.deriv_eq]
  have key : ∀ a : Fin 4, a ≠ 0 → a ≠ 1 → slope a (h 2 2) y₀ = 0 := by
    intro a ha0 ha1
    unfold slope
    have he : (fun s ↦ h 2 2 (Function.update y₀ a s))
        =ᶠ[𝓝 (y₀ a)] fun _ ↦ S (y₀ 0) (y₀ 1) := by
      filter_upwards [(ht a).eventually hshape] with s hs'
      rw [hs']
      simp [genG, sep2, gTR, gΘ, constOne, Function.update_of_ne (Ne.symm ha0),
        Function.update_of_ne (Ne.symm ha1)]
    rw [he.deriv_eq]
    simp
  -- So the slope of the squared size along any step is this.
  have hfd : ∀ w : Coords 4, fderiv ℝ (h 2 2) y₀ w
      = w 0 * dt S (y₀ 0) (y₀ 1) + w 1 * dr S (y₀ 0) (y₀ 1) := by
    intro w
    rw [fderiv_eq_sum_slope hd, Fin.sum_univ_four, s0, s1, key 2 (by decide) (by decide),
      key 3 (by decide) (by decide)]
    ring
  -- The determinant of the time-distance block, under one letter.
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ,
      D = A (y₀ 0) (y₀ 1) * B (y₀ 0) (y₀ 1) + C (y₀ 0) (y₀ 1) * C (y₀ 0) (y₀ 1) := ⟨_, rfl⟩
  have hdet2 : det2 A B C (y₀ 0) (y₀ 1) = D := hDdef.symm
  have hD : D ≠ 0 := by
    rw [← hdet2]
    exact hdet
  -- The step that points the way the spheres grow, by its four parts.
  obtain ⟨n, n0, n1, n2, n3⟩ : ∃ n : Coords 4,
      n 0 = (C (y₀ 0) (y₀ 1) * dr S (y₀ 0) (y₀ 1) - B (y₀ 0) (y₀ 1) * dt S (y₀ 0) (y₀ 1)) / D
      ∧ n 1 = (A (y₀ 0) (y₀ 1) * dr S (y₀ 0) (y₀ 1) + C (y₀ 0) (y₀ 1) * dt S (y₀ 0) (y₀ 1)) / D
      ∧ n 2 = 0 ∧ n 3 = 0 :=
    ⟨![(C (y₀ 0) (y₀ 1) * dr S (y₀ 0) (y₀ 1) - B (y₀ 0) (y₀ 1) * dt S (y₀ 0) (y₀ 1)) / D,
        (A (y₀ 0) (y₀ 1) * dr S (y₀ 0) (y₀ 1) + C (y₀ 0) (y₀ 1) * dt S (y₀ 0) (y₀ 1)) / D, 0, 0],
      rfl, rfl, rfl, rfl⟩
  -- The table turns this step into the slope of the squared size.
  have h1 : ∀ w : Coords 4, tableMeasure h y₀ n w = fderiv ℝ (h 2 2) y₀ w := by
    intro w
    rw [tableMeasure_of_genG hy0, hfd, n0, n1, n2, n3]
    field_simp
    rw [hDdef]
    ring
  -- Its squared length is `sizeSlopeSq / D`.
  have hnn : tableMeasure h y₀ n n
      = sizeSlopeSq A B C S (y₀ 0) (y₀ 1) / det2 A B C (y₀ 0) (y₀ 1) := by
    rw [h1 n, hfd, n0, n1, hdet2]
    unfold sizeSlopeSq
    ring
  refine ⟨n, fun w ↦ ?_, ?_⟩
  · rw [mvfderiv_flat, hev.fderiv_eq]
    exact h1 w
  · change massOf (sizeSq (flatMeasure (tableMeasure h)) turns y₀) (tableMeasure h y₀ n n) = _
    rw [hsz, hnn]
    unfold massOf massFn radiusSlopeSq
    ring

end GravityInLean.Mass
