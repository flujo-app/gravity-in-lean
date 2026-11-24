/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.Turns
public import GravityInLean.Flows.SmoothFlow

import Mathlib.Tactic

/-!
# Coordinates that fit the turns: the words used by all files of `Turns/`

Board item `task:turns-basic`. Three words, and the flow of a field taken from `smoothFlow`:

* `vec ξ`: a field of arrows given by its four parts, as one map from points to arrows;
* `lieB X Y`: the bracket of two fields that are maps from points to arrows, written with the
  library's slope `fderiv`;
* `IsLocalFlow X U x₀ ε flow`: what `smoothFlow` gives, as one word.
-/

@[expose] public section

namespace GravityInLean.Turns

open Set Metric Topology

open scoped ContDiff

/-- A field of arrows given by its four parts, as one map from points to arrows. -/
def vec (ξ : Fin 4 → Coords 4 → ℝ) : Coords 4 → Coords 4 := fun x k ↦ ξ k x

/-- The bracket of two fields `X`, `Y` (maps from points to arrows) at the point `x`: how `Y`
changes along `X`, minus how `X` changes along `Y`. -/
noncomputable def lieB {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (X Y : E → E)
    (x : E) : E :=
  fderiv ℝ Y x (X x) - fderiv ℝ X x (Y x)

/-- `flow` follows the field `X` inside the region `U`, for starting points within `ε` of `x₀`
and times between `-ε` and `ε`, and is smooth in time and starting point together. This is what
`smoothFlow` gives. -/
structure IsLocalFlow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (X : E → E)
    (U : Set E) (x₀ : E) (ε : ℝ) (flow : ℝ → E → E) : Prop where
  /-- The time span is positive. -/
  pos : 0 < ε
  /-- Smooth in time and starting point together. -/
  smooth : ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ flow p.1 p.2) (Ioo (-ε) ε ×ˢ ball x₀ ε)
  /-- At time zero nothing has moved. -/
  zero : ∀ x ∈ ball x₀ ε, flow 0 x = x
  /-- The path stays in the region. -/
  mem : ∀ x ∈ ball x₀ ε, ∀ t ∈ Ioo (-ε) ε, flow t x ∈ U
  /-- The path moves with the velocity the field gives at the place it has reached. -/
  deriv : ∀ x ∈ ball x₀ ε, ∀ t ∈ Ioo (-ε) ε, HasDerivAt (fun r ↦ flow r x) (X (flow t x)) t

/-- Every smooth field on an open region has a flow near every point of the region
(`smoothFlow`, in the words of this folder). -/
theorem exists_isLocalFlow {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {X : E → E} {U : Set E} (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ (ε : ℝ) (flow : ℝ → E → E), IsLocalFlow X U x₀ ε flow := by
  obtain ⟨ε, flow, hε, hsm, h0, hd⟩ := smoothFlow E X U hU hX x₀ hx₀
  exact ⟨ε, flow, hε, hsm, h0, fun x hx t ht ↦ (hd x hx t ht).1, fun x hx t ht ↦ (hd x hx t ht).2⟩

end GravityInLean.Turns
