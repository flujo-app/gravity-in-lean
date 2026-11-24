/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Turns.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

import Mathlib.Tactic

/-!
# The new coordinates

Board item `task:turns-chart`. Step 4 of the route, first half. From a surface `σ` of two
numbers and the flows `χ`, `ψ` of two fields `Z₀`, `Z₂` near `p`, the change of coordinates is

  `chart σ χ ψ y = ψ (y 3) (χ (y 2 - π / 2) (σ (y 0, y 1)))`:

start on the surface at `(y 0, y 1)`, follow `Z₀` for the time `y 2 - π / 2`, then `Z₂` for the
time `y 3`. `chartDomain` is the set of new coordinates on which all of this is defined and
`sin (y 2) ≠ 0`; `chartStart = (0, 0, π / 2, 0)`. `ChartData` collects what is assumed.

This file shows: the domain is open, contains the start, the chart sends the start to `p` and
stays in the region. That the chart is smooth on the domain is in `ChartSmooth.lean`.
-/

@[expose] public section

namespace GravityInLean.Turns

open Set Metric Topology Real

open scoped ContDiff

/-- The change of coordinates: start on the surface `σ` at `(y 0, y 1)`, follow the first flow
for the time `y 2 - π / 2`, then the second for the time `y 3`. -/
noncomputable def chart (σ : ℝ × ℝ → Coords 4) (χ ψ : ℝ → Coords 4 → Coords 4) (y : Coords 4) :
    Coords 4 :=
  ψ (y 3) (χ (y 2 - π / 2) (σ (y 0, y 1)))

/-- The new coordinates on which the chart is defined: the surface is defined at `(y 0, y 1)`,
both flows are defined at the times and places asked for, and `sin (y 2) ≠ 0`. -/
def chartDomain (σ : ℝ × ℝ → Coords 4) (χ : ℝ → Coords 4 → Coords 4) (p : Coords 4)
    (δ ε₀ ε₂ : ℝ) : Set (Coords 4) :=
  {y | (y 0, y 1) ∈ ball (0 : ℝ × ℝ) δ ∧ y 2 - π / 2 ∈ Ioo (-ε₀) ε₀ ∧
    σ (y 0, y 1) ∈ ball p ε₀ ∧ y 3 ∈ Ioo (-ε₂) ε₂ ∧
    χ (y 2 - π / 2) (σ (y 0, y 1)) ∈ ball p ε₂ ∧ sin (y 2) ≠ 0}

/-- The new coordinates of the point `p`: on the equator, at angle zero. -/
noncomputable def chartStart : Coords 4 := ![0, 0, π / 2, 0]

/-- What the chart is built from: a smooth surface `σ` through `p`, defined within `δ` of the
start, and flows `χ` of `Z₀` and `ψ` of `Z₂` near `p`. -/
structure ChartData (Z₀ Z₂ : Coords 4 → Coords 4) (U : Set (Coords 4)) (p : Coords 4)
    (δ ε₀ ε₂ : ℝ) (σ : ℝ × ℝ → Coords 4) (χ ψ : ℝ → Coords 4 → Coords 4) : Prop where
  /-- The surface is defined on a ball of positive size. -/
  δpos : 0 < δ
  /-- The surface is smooth. -/
  σsmooth : ContDiffOn ℝ ∞ σ (ball 0 δ)
  /-- The surface starts at `p`. -/
  σzero : σ 0 = p
  /-- `χ` is the flow of `Z₀` near `p`. -/
  flow₀ : IsLocalFlow Z₀ U p ε₀ χ
  /-- `ψ` is the flow of `Z₂` near `p`. -/
  flow₂ : IsLocalFlow Z₂ U p ε₂ ψ

variable {Z₀ Z₂ : Coords 4 → Coords 4} {U : Set (Coords 4)} {p : Coords 4} {δ ε₀ ε₂ : ℝ}
  {σ : ℝ × ℝ → Coords 4} {χ ψ : ℝ → Coords 4 → Coords 4}

/-- The four numbers of the start, one by one. -/
theorem chartStart_apply :
    chartStart 0 = 0 ∧ chartStart 1 = 0 ∧ chartStart 2 = π / 2 ∧ chartStart 3 = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The start is in the domain of the chart. -/
theorem chartStart_mem (h : ChartData Z₀ Z₂ U p δ ε₀ ε₂ σ χ ψ) :
    chartStart ∈ chartDomain σ χ p δ ε₀ ε₂ := by
  obtain ⟨e0, e1, e2, e3⟩ := chartStart_apply
  have h00 : ((0 : ℝ), (0 : ℝ)) = (0 : ℝ × ℝ) := rfl
  have hχ : χ 0 p = p := h.flow₀.zero p (mem_ball_self h.flow₀.pos)
  unfold chartDomain
  rw [mem_ofPred_eq, e0, e1, e2, e3, sub_self, h00, h.σzero, hχ, Real.sin_pi_div_two]
  exact ⟨mem_ball_self h.δpos, ⟨neg_lt_zero.mpr h.flow₀.pos, h.flow₀.pos⟩,
    mem_ball_self h.flow₀.pos, ⟨neg_lt_zero.mpr h.flow₂.pos, h.flow₂.pos⟩,
    mem_ball_self h.flow₂.pos, one_ne_zero⟩

/-- The chart sends the start to `p`. -/
theorem chart_chartStart (h : ChartData Z₀ Z₂ U p δ ε₀ ε₂ σ χ ψ) :
    chart σ χ ψ chartStart = p := by
  obtain ⟨e0, e1, e2, e3⟩ := chartStart_apply
  have h00 : ((0 : ℝ), (0 : ℝ)) = (0 : ℝ × ℝ) := rfl
  have hχ : χ 0 p = p := h.flow₀.zero p (mem_ball_self h.flow₀.pos)
  unfold chart
  rw [e0, e1, e2, e3, sub_self, h00, h.σzero, hχ]
  exact h.flow₂.zero p (mem_ball_self h.flow₂.pos)

/-- The domain of the chart is open. The conditions are taken one after the other: first those
on the new coordinates alone, then that the point of the surface is near `p` (the surface is
continuous where it is defined), then that the first flow has stayed near `p` (the flow is
continuous in time and starting point where it is defined). -/
theorem isOpen_chartDomain (h : ChartData Z₀ Z₂ U p δ ε₀ ε₂ σ χ ψ) :
    IsOpen (chartDomain σ χ p δ ε₀ ε₂) := by
  have c0 : Continuous fun y : Coords 4 ↦ y 0 := continuous_apply 0
  have c1 : Continuous fun y : Coords 4 ↦ y 1 := continuous_apply 1
  have c2 : Continuous fun y : Coords 4 ↦ y 2 := continuous_apply 2
  have c3 : Continuous fun y : Coords 4 ↦ y 3 := continuous_apply 3
  have c01 : Continuous fun y : Coords 4 ↦ (y 0, y 1) := c0.prodMk c1
  have ct : Continuous fun y : Coords 4 ↦ y 2 - π / 2 := c2.sub continuous_const
  -- the conditions on the new coordinates alone
  have o1 : IsOpen {y : Coords 4 | (y 0, y 1) ∈ ball (0 : ℝ × ℝ) δ} := isOpen_ball.preimage c01
  have o2 : IsOpen {y : Coords 4 | y 2 - π / 2 ∈ Ioo (-ε₀) ε₀} := isOpen_Ioo.preimage ct
  have o3 : IsOpen {y : Coords 4 | y 3 ∈ Ioo (-ε₂) ε₂} := isOpen_Ioo.preimage c3
  have o4 : IsOpen {y : Coords 4 | sin (y 2) ≠ 0} :=
    isOpen_ne_fun (Real.continuous_sin.comp c2) continuous_const
  have oA : IsOpen {y : Coords 4 | (y 0, y 1) ∈ ball (0 : ℝ × ℝ) δ ∧
      y 2 - π / 2 ∈ Ioo (-ε₀) ε₀ ∧ y 3 ∈ Ioo (-ε₂) ε₂ ∧ sin (y 2) ≠ 0} :=
    o1.and (o2.and (o3.and o4))
  -- the point of the surface is near `p`
  have fA : ContinuousOn (fun y : Coords 4 ↦ σ (y 0, y 1))
      {y : Coords 4 | (y 0, y 1) ∈ ball (0 : ℝ × ℝ) δ ∧
        y 2 - π / 2 ∈ Ioo (-ε₀) ε₀ ∧ y 3 ∈ Ioo (-ε₂) ε₂ ∧ sin (y 2) ≠ 0} :=
    h.σsmooth.continuousOn.comp c01.continuousOn (fun y hy ↦ hy.1)
  have oB : IsOpen ({y : Coords 4 | (y 0, y 1) ∈ ball (0 : ℝ × ℝ) δ ∧
      y 2 - π / 2 ∈ Ioo (-ε₀) ε₀ ∧ y 3 ∈ Ioo (-ε₂) ε₂ ∧ sin (y 2) ≠ 0} ∩
      (fun y : Coords 4 ↦ σ (y 0, y 1)) ⁻¹' ball p ε₀) :=
    fA.isOpen_inter_preimage oA isOpen_ball
  -- the first flow has stayed near `p`
  have gB : ContinuousOn (fun y : Coords 4 ↦ χ (y 2 - π / 2) (σ (y 0, y 1)))
      ({y : Coords 4 | (y 0, y 1) ∈ ball (0 : ℝ × ℝ) δ ∧
        y 2 - π / 2 ∈ Ioo (-ε₀) ε₀ ∧ y 3 ∈ Ioo (-ε₂) ε₂ ∧ sin (y 2) ≠ 0} ∩
        (fun y : Coords 4 ↦ σ (y 0, y 1)) ⁻¹' ball p ε₀) :=
    h.flow₀.smooth.continuousOn.comp (f := fun y : Coords 4 ↦ (y 2 - π / 2, σ (y 0, y 1)))
      (ct.continuousOn.prodMk (fA.mono inter_subset_left))
      (fun y hy ↦ Set.mk_mem_prod hy.1.2.1 hy.2)
  have oC : IsOpen (({y : Coords 4 | (y 0, y 1) ∈ ball (0 : ℝ × ℝ) δ ∧
      y 2 - π / 2 ∈ Ioo (-ε₀) ε₀ ∧ y 3 ∈ Ioo (-ε₂) ε₂ ∧ sin (y 2) ≠ 0} ∩
      (fun y : Coords 4 ↦ σ (y 0, y 1)) ⁻¹' ball p ε₀) ∩
      (fun y : Coords 4 ↦ χ (y 2 - π / 2) (σ (y 0, y 1))) ⁻¹' ball p ε₂) :=
    gB.isOpen_inter_preimage oB isOpen_ball
  have hEq : chartDomain σ χ p δ ε₀ ε₂ =
      ({y : Coords 4 | (y 0, y 1) ∈ ball (0 : ℝ × ℝ) δ ∧
        y 2 - π / 2 ∈ Ioo (-ε₀) ε₀ ∧ y 3 ∈ Ioo (-ε₂) ε₂ ∧ sin (y 2) ≠ 0} ∩
        (fun y : Coords 4 ↦ σ (y 0, y 1)) ⁻¹' ball p ε₀) ∩
        (fun y : Coords 4 ↦ χ (y 2 - π / 2) (σ (y 0, y 1))) ⁻¹' ball p ε₂ := by
    ext y
    constructor
    · rintro ⟨a, b, c, d, e, f⟩
      exact ⟨⟨⟨a, b, d, f⟩, c⟩, e⟩
    · rintro ⟨⟨⟨a, b, d, f⟩, c⟩, e⟩
      exact ⟨a, b, c, d, e, f⟩
  rw [hEq]
  exact oC

/-- The chart stays in the region. -/
theorem chart_mem (h : ChartData Z₀ Z₂ U p δ ε₀ ε₂ σ χ ψ) {y : Coords 4}
    (hy : y ∈ chartDomain σ χ p δ ε₀ ε₂) : chart σ χ ψ y ∈ U :=
  h.flow₂.mem _ hy.2.2.2.2.1 _ hy.2.2.2.1

end GravityInLean.Turns
