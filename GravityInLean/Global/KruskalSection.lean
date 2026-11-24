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
# Wrapping Kruskal's table round the sphere can be undone on small pieces

Every point of Kruskal's whole space-time has a neighbourhood on which the wrapping map
`kruskalWrap`, followed by a turn or mirror of the sphere, has a smooth inverse into the region
of Kruskal's table.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

/-- **Wrapping can be undone near every point of Kruskal's whole space-time.** There are a turn
or mirror `R` of the sphere, an open set `U` of lists of five numbers around `p` and a map `ψ`,
smooth on `U`, that sends the points of Kruskal's space-time in `U` into the region of Kruskal's
table, such that wrapping `ψ y` round the sphere and applying `R` gives back `y`. -/
theorem exists_kruskalWrap_section {p : Coords 5} (hp : p ∈ kruskalSpace) :
    ∃ (R : Matrix (Fin 3) (Fin 3) ℝ) (U : Set (Coords 5)) (ψ : Coords 5 → Coords 4),
      R.transpose * R = 1 ∧ IsOpen U ∧ p ∈ U ∧ ContDiffOn ℝ ∞ ψ U ∧
      ∀ y ∈ U, y ∈ kruskalSpace →
        ψ y ∈ kruskalRegion ∧ kruskalSym 1 R (kruskalWrap (ψ y)) = y := by
  -- the last three numbers of `p` are a direction: a point of the unit sphere
  have hy : 0 < (![p 2, p 3, p 4] : Fin 3 → ℝ) 0 ^ 2 + (![p 2, p 3, p 4] : Fin 3 → ℝ) 1 ^ 2
      + (![p 2, p 3, p 4] : Fin 3 → ℝ) 2 ^ 2 := by
    have h : (![p 2, p 3, p 4] : Fin 3 → ℝ) 0 ^ 2 + (![p 2, p 3, p 4] : Fin 3 → ℝ) 1 ^ 2
        + (![p 2, p 3, p 4] : Fin 3 → ℝ) 2 ^ 2 = 1 := hp.2
    rw [h]
    exact one_pos
  obtain ⟨R, V, θ, φ, hR, hV, hpV, hθ, hφ, hsec⟩ := exists_sphere_section hy
  -- taking the last three numbers is smooth
  have hc : ∀ j : Fin 5, ContDiff ℝ ∞ (fun y : Coords 5 ↦ y j) :=
    fun j ↦ contDiff_apply ℝ (fun _ : Fin 5 ↦ ℝ) j
  have hπ : ContDiff ℝ ∞ (fun y : Coords 5 ↦ (![y 2, y 3, y 4] : Fin 3 → ℝ)) := by
    refine contDiff_pi.mpr fun i ↦ ?_
    fin_cases i
    · exact hc 2
    · exact hc 3
    · exact hc 4
  refine ⟨R, (fun y : Coords 5 ↦ (![y 2, y 3, y 4] : Fin 3 → ℝ)) ⁻¹' V,
    fun y ↦ ![y 0, y 1, θ ![y 2, y 3, y 4], φ ![y 2, y 3, y 4]], hR,
    hV.preimage hπ.continuous, hpV, ?_, ?_⟩
  · -- the inverse is smooth, part by part
    refine contDiffOn_pi.mpr fun i ↦ ?_
    fin_cases i
    · exact (hc 0).contDiffOn
    · exact (hc 1).contDiffOn
    · exact hθ.comp hπ.contDiffOn fun y hy ↦ hy
    · exact hφ.comp hπ.contDiffOn fun y hy ↦ hy
  · intro y hyU hyK
    obtain ⟨-, hsin, hmul⟩ := hsec ![y 2, y 3, y 4] hyU
    -- on Kruskal's space-time the last three numbers have length one
    have hone : (![y 2, y 3, y 4] : Fin 3 → ℝ) 0 ^ 2 + (![y 2, y 3, y 4] : Fin 3 → ℝ) 1 ^ 2
        + (![y 2, y 3, y 4] : Fin 3 → ℝ) 2 ^ 2 = 1 := hyK.2
    rw [hone, Real.sqrt_one, inv_one, one_smul] at hmul
    refine ⟨⟨hyK.1, hsin⟩, ?_⟩
    -- the three parts of the turned direction
    have h0 : R 0 0 * (sin (θ ![y 2, y 3, y 4]) * cos (φ ![y 2, y 3, y 4]))
        + R 0 1 * (sin (θ ![y 2, y 3, y 4]) * sin (φ ![y 2, y 3, y 4]))
        + R 0 2 * cos (θ ![y 2, y 3, y 4]) = y 2 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun hmul 0
    have h1 : R 1 0 * (sin (θ ![y 2, y 3, y 4]) * cos (φ ![y 2, y 3, y 4]))
        + R 1 1 * (sin (θ ![y 2, y 3, y 4]) * sin (φ ![y 2, y 3, y 4]))
        + R 1 2 * cos (θ ![y 2, y 3, y 4]) = y 3 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun hmul 1
    have h2 : R 2 0 * (sin (θ ![y 2, y 3, y 4]) * cos (φ ![y 2, y 3, y 4]))
        + R 2 1 * (sin (θ ![y 2, y 3, y 4]) * sin (φ ![y 2, y 3, y 4]))
        + R 2 2 * cos (θ ![y 2, y 3, y 4]) = y 4 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun hmul 2
    funext i
    fin_cases i
    · simp [kruskalSym, kruskalWrap]
    · simp [kruskalSym, kruskalWrap]
    · simpa [kruskalSym, kruskalWrap] using h0
    · simpa [kruskalSym, kruskalWrap] using h1
    · simpa [kruskalSym, kruskalWrap] using h2

end GravityInLean.Curved
