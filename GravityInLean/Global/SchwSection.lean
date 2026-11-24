/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.SphereSection

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# From ordinary space labels back to distance and angles, on small pieces

Every point of ordinary space and time off the centre has a neighbourhood on which the map
`sphericalToSpace`, followed by a turn or mirror of space, has a smooth inverse.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

/-- **Distance and angles near every point off the centre.** There are a turn or mirror `R` of
space, an open set `U` around `z` and a map `ψ`, smooth on `U`, into the region of
Schwarzschild's table (distance positive, off the poles), such that `sphericalToSpace (ψ y)`
followed by `R` gives back `y`. -/
theorem exists_sphericalToSpace_section {z : Coords 4} (hz : 0 < z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2) :
    ∃ (R : Matrix (Fin 3) (Fin 3) ℝ) (U : Set (Coords 4)) (ψ : Coords 4 → Coords 4),
      R.transpose * R = 1 ∧ IsOpen U ∧ z ∈ U ∧ ContDiffOn ℝ ∞ ψ U ∧
      ∀ y ∈ U, 0 < ψ y 1 ∧ sin (ψ y 2) ≠ 0 ∧ schwSym 1 0 R (sphericalToSpace (ψ y)) = y := by
  have hy₀ : 0 < (![z 1, z 2, z 3] : Fin 3 → ℝ) 0 ^ 2 + (![z 1, z 2, z 3] : Fin 3 → ℝ) 1 ^ 2
      + (![z 1, z 2, z 3] : Fin 3 → ℝ) 2 ^ 2 := by
    simpa only [Matrix.cons_val] using hz
  obtain ⟨R, U, θ, φ, hR, hU, hmem, hθ, hφ, h⟩ := exists_sphere_section hy₀
  -- the three space labels of a point, and the square of its distance from the centre
  have c : ∀ j : Fin 4, ContDiff ℝ ∞ (fun y : Coords 4 ↦ y j) :=
    fun j ↦ contDiff_apply ℝ (fun _ : Fin 4 ↦ ℝ) j
  have hp : ContDiff ℝ ∞ (fun y : Coords 4 ↦ (![y 1, y 2, y 3] : Fin 3 → ℝ)) := by
    refine contDiff_pi.mpr fun i ↦ ?_
    fin_cases i
    · exact c 1
    · exact c 2
    · exact c 3
  have hsq : ContDiff ℝ ∞ (fun y : Coords 4 ↦ y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) :=
    (((c 1).pow 2).add ((c 2).pow 2)).add ((c 3).pow 2)
  -- what the angles of the sphere give at the space labels of a point of the open set
  have key : ∀ y : Coords 4, (![y 1, y 2, y 3] : Fin 3 → ℝ) ∈ U →
      0 < y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 ∧ sin (θ ![y 1, y 2, y 3]) ≠ 0 ∧
        R.mulVec ![sin (θ ![y 1, y 2, y 3]) * cos (φ ![y 1, y 2, y 3]),
            sin (θ ![y 1, y 2, y 3]) * sin (φ ![y 1, y 2, y 3]), cos (θ ![y 1, y 2, y 3])]
          = (√(y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2))⁻¹ • (![y 1, y 2, y 3] : Fin 3 → ℝ) := by
    intro y hy
    have h' := h _ hy
    simp only [Matrix.cons_val] at h'
    exact h'
  refine ⟨R, (fun y : Coords 4 ↦ (![y 1, y 2, y 3] : Fin 3 → ℝ)) ⁻¹' U,
    fun y ↦ ![y 0, √(y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2), θ ![y 1, y 2, y 3], φ ![y 1, y 2, y 3]],
    hR, hU.preimage hp.continuous, hmem, ?_, ?_⟩
  · refine contDiffOn_pi.mpr fun i ↦ ?_
    fin_cases i
    · exact (c 0).contDiffOn
    · exact hsq.contDiffOn.sqrt fun y hy ↦ (key y hy).1.ne'
    · exact hθ.comp hp.contDiffOn fun y hy ↦ hy
    · exact hφ.comp hp.contDiffOn fun y hy ↦ hy
  · intro y hy
    obtain ⟨hpos, hsin, hR'⟩ := key y hy
    have hρ : 0 < √(y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) := Real.sqrt_pos.mpr hpos
    refine ⟨by simpa only [Matrix.cons_val] using hρ,
      by simpa only [Matrix.cons_val] using hsin, ?_⟩
    -- the three rows of `R` applied to the direction, read one by one
    have e0 := congrFun hR' 0
    have e1 := congrFun hR' 1
    have e2 := congrFun hR' 2
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val, Pi.smul_apply,
      smul_eq_mul] at e0 e1 e2
    funext i
    simp only [schwSym, sphericalToSpace, Matrix.cons_val]
    fin_cases i
    · simp
    · change R 0 0 * _ + R 0 1 * _ + R 0 2 * _ = y 1
      calc _ = √(y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) * ((√(y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2))⁻¹ * y 1) := by
            rw [← e0]
            ring
        _ = y 1 := mul_inv_cancel_left₀ hρ.ne' _
    · change R 1 0 * _ + R 1 1 * _ + R 1 2 * _ = y 2
      calc _ = √(y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) * ((√(y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2))⁻¹ * y 2) := by
            rw [← e1]
            ring
        _ = y 2 := mul_inv_cancel_left₀ hρ.ne' _
    · change R 2 0 * _ + R 2 1 * _ + R 2 2 * _ = y 3
      calc _ = √(y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) * ((√(y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2))⁻¹ * y 3) := by
            rw [← e2]
            ring
        _ = y 3 := mul_inv_cancel_left₀ hρ.ne' _

end GravityInLean.Curved
