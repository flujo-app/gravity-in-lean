/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Turns.Basic
public import GravityInLean.Turns.LinearUnique
public import GravityInLean.Turns.Variational
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

import Mathlib.Tactic

/-!
# How a field is carried along the flow of another

Board item `task:turns-transport`. Step 2 of the route. Let `flow` follow the field `Z`. The
slope of `flow t` in the starting point, applied to an arrow of a second field at the start, is a
fixed mix of fields at the place reached:

* `fderiv_flow_pair`: two fields `Y₀`, `Y₁` whose brackets with `Z` are `Y₁` and `-Y₀` are
  carried to mixes of the two with the cosine and the sine of the time.

(`fderiv_flow_self` in `TransportSelf.lean`: the field `Z` itself is carried to itself.) The two
sides solve the same linear equation `A' = DZ(flow t x) A`
(`hasDerivAt_fderiv_flow` for the left side) with the same value at time zero
(`fderiv_flow_zero`), so they are equal (`linear_ode_unique`).
-/

@[expose] public section

namespace GravityInLean.Turns

open Set Metric Topology Real

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E} {x₀ : E} {ε : ℝ}
  {flow : ℝ → E → E}

/-- The common step: if the numbers `c t`, `d t` change in time the way the cosine and the sine
do (`c' = d`, `d' = -c`), then the flow of `Z` carries the mix `c 0 • Y₀ + d 0 • Y₁` at the start
to the mix `c t • Y₀ + d t • Y₁` at the place reached. Both sides solve the same linear
equation with the same value at time zero. -/
theorem fderiv_flow_mix {Z Y₀ Y₁ : E → E} (hU : IsOpen U) (hZ : ContDiffOn ℝ ∞ Z U)
    (hY₀ : ContDiffOn ℝ ∞ Y₀ U) (hY₁ : ContDiffOn ℝ ∞ Y₁ U)
    (h₀ : ∀ x ∈ U, lieB Z Y₀ x = Y₁ x) (h₁ : ∀ x ∈ U, lieB Z Y₁ x = -Y₀ x)
    (hf : IsLocalFlow Z U x₀ ε flow) {x : E} (hx : x ∈ ball x₀ ε) {t : ℝ}
    (ht : t ∈ Ioo (-ε) ε) (c d : ℝ → ℝ) (hc : ∀ s, HasDerivAt c (d s) s)
    (hd : ∀ s, HasDerivAt d (-c s) s) :
    fderiv ℝ (flow t) x (c 0 • Y₀ x + d 0 • Y₁ x)
      = c t • Y₀ (flow t x) + d t • Y₁ (flow t x) := by
  -- a smooth field, read along the path, changes at the rate "its slope along `Z`"
  have hpath : ∀ Y : E → E, ContDiffOn ℝ ∞ Y U → ∀ s ∈ Ioo (-ε) ε,
      HasDerivAt (fun r ↦ Y (flow r x)) (fderiv ℝ Y (flow s x) (Z (flow s x))) s := by
    intro Y hY s hs
    have hYd : DifferentiableAt ℝ Y (flow s x) :=
      (hY.contDiffAt (hU.mem_nhds (hf.mem x hx s hs))).differentiableAt (by simp)
    have h : HasDerivAt (Y ∘ fun r ↦ flow r x) (fderiv ℝ Y (flow s x) (Z (flow s x))) s :=
      hYd.hasFDerivAt.comp_hasDerivAt s (hf.deriv x hx s hs)
    exact h
  -- the right side solves the linear equation
  have hB : ∀ s ∈ Ioo (-ε) ε,
      HasDerivAt (fun r ↦ c r • Y₀ (flow r x) + d r • Y₁ (flow r x))
        (fderiv ℝ Z (flow s x) (c s • Y₀ (flow s x) + d s • Y₁ (flow s x))) s := by
    intro s hs
    have hq : flow s x ∈ U := hf.mem x hx s hs
    have e0 : fderiv ℝ Z (flow s x) (Y₀ (flow s x))
        = fderiv ℝ Y₀ (flow s x) (Z (flow s x)) - Y₁ (flow s x) := by
      rw [← h₀ _ hq, lieB]; abel
    have e1 : fderiv ℝ Z (flow s x) (Y₁ (flow s x))
        = fderiv ℝ Y₁ (flow s x) (Z (flow s x)) + Y₀ (flow s x) := by
      have h : Y₀ (flow s x) = -(lieB Z Y₁ (flow s x)) := by rw [h₁ _ hq, neg_neg]
      rw [h, lieB]; abel
    have h : HasDerivAt (fun r ↦ c r • Y₀ (flow r x) + d r • Y₁ (flow r x))
        ((c s • fderiv ℝ Y₀ (flow s x) (Z (flow s x)) + d s • Y₀ (flow s x))
          + (d s • fderiv ℝ Y₁ (flow s x) (Z (flow s x)) + (-c s) • Y₁ (flow s x))) s :=
      ((hc s).smul (hpath Y₀ hY₀ s hs)).add ((hd s).smul (hpath Y₁ hY₁ s hs))
    have key : fderiv ℝ Z (flow s x) (c s • Y₀ (flow s x) + d s • Y₁ (flow s x))
        = (c s • fderiv ℝ Y₀ (flow s x) (Z (flow s x)) + d s • Y₀ (flow s x))
          + (d s • fderiv ℝ Y₁ (flow s x) (Z (flow s x)) + (-c s) • Y₁ (flow s x)) := by
      rw [map_add, map_smul, map_smul, e0, e1]
      module
    rw [key]
    exact h
  -- the two sides agree at time zero
  have h0 : fderiv ℝ (flow 0) x (c 0 • Y₀ x + d 0 • Y₁ x)
      = c 0 • Y₀ (flow 0 x) + d 0 • Y₁ (flow 0 x) := by
    rw [fderiv_flow_zero hf hx, hf.zero x hx]
    rfl
  exact linear_ode_unique (fun r ↦ fderiv ℝ Z (flow r x))
    (continuousOn_fderiv_along_flow hU hZ hf hx)
    (fun r ↦ fderiv ℝ (flow r) x (c 0 • Y₀ x + d 0 • Y₁ x))
    (fun r ↦ c r • Y₀ (flow r x) + d r • Y₁ (flow r x))
    (fun s hs ↦ hasDerivAt_fderiv_flow hU hZ hf hx hs _) hB h0 t ht

/-- Two fields `Y₀`, `Y₁` whose brackets with `Z` are `Y₁` and `-Y₀` are carried by the flow of
`Z` to mixes of the two, with the cosine and the sine of the time. -/
theorem fderiv_flow_pair {Z Y₀ Y₁ : E → E} (hU : IsOpen U) (hZ : ContDiffOn ℝ ∞ Z U)
    (hY₀ : ContDiffOn ℝ ∞ Y₀ U) (hY₁ : ContDiffOn ℝ ∞ Y₁ U)
    (h₀ : ∀ x ∈ U, lieB Z Y₀ x = Y₁ x) (h₁ : ∀ x ∈ U, lieB Z Y₁ x = -Y₀ x)
    (hf : IsLocalFlow Z U x₀ ε flow) {x : E} (hx : x ∈ ball x₀ ε) {t : ℝ}
    (ht : t ∈ Ioo (-ε) ε) :
    fderiv ℝ (flow t) x (Y₀ x) = cos t • Y₀ (flow t x) - sin t • Y₁ (flow t x) ∧
      fderiv ℝ (flow t) x (Y₁ x) = sin t • Y₀ (flow t x) + cos t • Y₁ (flow t x) := by
  constructor
  · have h := fderiv_flow_mix hU hZ hY₀ hY₁ h₀ h₁ hf hx ht cos (fun s ↦ -sin s)
      (fun s ↦ hasDerivAt_cos s) (fun s ↦ (hasDerivAt_sin s).neg)
    simp only [cos_zero, sin_zero, neg_zero, one_smul, zero_smul, add_zero, neg_smul] at h
    rw [h, sub_eq_add_neg]
  · have h := fderiv_flow_mix hU hZ hY₀ hY₁ h₀ h₁ hf hx ht sin cos
      (fun s ↦ hasDerivAt_sin s) (fun s ↦ hasDerivAt_cos s)
    simp only [cos_zero, sin_zero, one_smul, zero_smul, zero_add] at h
    exact h

end GravityInLean.Turns
