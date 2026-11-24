/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Turns.Chart
public import GravityInLean.Turns.ChartSlopes
public import GravityInLean.Turns.Transport
public import GravityInLean.Turns.TransportSelf

import Mathlib.Tactic

/-!
# The two relations that the new coordinates obey

Board item `task:turns-relations`. Step 5 of the route, the part with the flows. Let `η 0`,
`η 1`, `η 2` combine the way turns do on the region `U`, let the chart (see `Chart.lean`) be
built from the flows of `η 0` and `η 2` and a surface on which `η 1` is zero. Then at every `y`
of the domain, with `q = chart σ χ ψ y`:

* the slope of the chart along `y 2` is `cos (y 3) • η 0 q - sin (y 3) • η 1 q`
  (`fderiv_chart_two`, then `fderiv_flow_pair` for the flow of `η 2` and the pair `η 0`, `η 1`);
* `sin (y 3) • η 0 q + cos (y 3) • η 1 q + (cos (y 2) / sin (y 2)) • η 2 q = 0`.

For the second: with `z = σ (y 0, y 1)`, `τ = y 2 - π / 2`, `x = χ τ z`, the flow of `η 0` and
the pair `η 1`, `η 2` give `0 = Dχ_τ(z) (η 1 z) = cos τ • η 1 x - sin τ • η 2 x
= sin (y 2) • η 1 x + cos (y 2) • η 2 x`. Apply `Dψ_{y 3}(x)` to this and use `fderiv_flow_pair`
(second part) and `fderiv_flow_self` for the flow of `η 2`; divide by `sin (y 2)`.
-/

@[expose] public section

namespace GravityInLean.Turns

open Set Metric Topology Real

open scoped ContDiff

/-- The two relations of the new coordinates: the slope along `y 2`, and the one relation
between the three fields at the place reached. -/
theorem chart_relations {η : Fin 3 → Coords 4 → Coords 4} {U : Set (Coords 4)} {p : Coords 4}
    {δ ε₀ ε₂ : ℝ} {σ : ℝ × ℝ → Coords 4} {χ ψ : ℝ → Coords 4 → Coords 4} (hU : IsOpen U)
    (hη : ∀ i, ContDiffOn ℝ ∞ (η i) U)
    (h01 : ∀ x ∈ U, lieB (η 0) (η 1) x = η 2 x) (h12 : ∀ x ∈ U, lieB (η 1) (η 2) x = η 0 x)
    (h20 : ∀ x ∈ U, lieB (η 2) (η 0) x = η 1 x)
    (h : ChartData (η 0) (η 2) U p δ ε₀ ε₂ σ χ ψ)
    (hσ1 : ∀ u ∈ ball (0 : ℝ × ℝ) δ, η 1 (σ u) = 0) {y : Coords 4}
    (hy : y ∈ chartDomain σ χ p δ ε₀ ε₂) :
    fderiv ℝ (chart σ χ ψ) y (Pi.single 2 1) =
        cos (y 3) • η 0 (chart σ χ ψ y) - sin (y 3) • η 1 (chart σ χ ψ y) ∧
      sin (y 3) • η 0 (chart σ χ ψ y) + cos (y 3) • η 1 (chart σ χ ψ y) +
        (cos (y 2) / sin (y 2)) • η 2 (chart σ χ ψ y) = 0 := by
  obtain ⟨hu, hτ, hz, h3, hx, hsin⟩ := hy
  have hq : chart σ χ ψ y = ψ (y 3) (χ (y 2 - π / 2) (σ (y 0, y 1))) := rfl
  -- the brackets the other way round
  have h21 : ∀ x ∈ U, lieB (η 2) (η 1) x = -η 0 x := by
    intro x hxU
    rw [← h12 x hxU]
    simp [lieB]
  have h02 : ∀ x ∈ U, lieB (η 0) (η 2) x = -η 1 x := by
    intro x hxU
    rw [← h20 x hxU]
    simp [lieB]
  -- (A) the flow of `η 2` carries the pair `η 0`, `η 1`
  have hA := fderiv_flow_pair (Z := η 2) (Y₀ := η 0) (Y₁ := η 1) hU (hη 2) (hη 0) (hη 1) h20 h21
    h.flow₂ hx h3
  -- (B) the flow of `η 0` carries the pair `η 1`, `η 2`; `η 1` is zero on the surface
  have hB0 := (fderiv_flow_pair (Z := η 0) (Y₀ := η 1) (Y₁ := η 2) hU (hη 0) (hη 1) (hη 2) h01
    h02 h.flow₀ hz hτ).1
  rw [hσ1 _ hu, map_zero, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two, neg_smul,
    sub_neg_eq_add] at hB0
  -- (C) carry (B) on by the slope of the flow of `η 2`
  have hC := congrArg (fderiv ℝ (ψ (y 3)) (χ (y 2 - π / 2) (σ (y 0, y 1)))) hB0
  simp only [map_add, map_smul, map_zero] at hC
  rw [hA.2, fderiv_flow_self hU (hη 2) h.flow₂ hx h3] at hC
  rw [hq]
  refine ⟨?_, ?_⟩
  · rw [fderiv_chart_two h ⟨hu, hτ, hz, h3, hx, hsin⟩]
    exact hA.1
  · have e : sin (y 2) * (cos (y 2) / sin (y 2)) = cos (y 2) := by field_simp
    have key : sin (y 2) • (sin (y 3) • η 0 (ψ (y 3) (χ (y 2 - π / 2) (σ (y 0, y 1)))) +
        cos (y 3) • η 1 (ψ (y 3) (χ (y 2 - π / 2) (σ (y 0, y 1)))) +
        (cos (y 2) / sin (y 2)) • η 2 (ψ (y 3) (χ (y 2 - π / 2) (σ (y 0, y 1))))) = 0 := by
      rw [smul_add, smul_smul, e]
      exact hC.symm
    exact (smul_eq_zero.mp key).resolve_left hsin

end GravityInLean.Turns
