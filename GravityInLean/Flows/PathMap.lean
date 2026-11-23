/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Flows.ComposeSmooth
public import GravityInLean.Flows.Integrate

import Mathlib.Tactic

/-!
# The equation of a path, written for whole paths at once

Board item `task:flows-path-map`.

A path `γ` on the times from `0` to `1` follows the field `s • X` from the starting point `x`
exactly if `γ = (the path that stays at x) + s • (integral of X along γ)`. `pathMap X` is the
difference of the two sides, so the paths we want are where it is zero. The time span is always
from `0` to `1`; the true time is the factor `s`.
-/

@[expose] public section

namespace GravityInLean.Flows

open Set Metric Topology

open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The equation of a path.** For a factor `s`, a starting point `x` and a path `γ`:
`γ - (the path that stays at x) - s • (integral of X along γ)`. It is zero exactly if `γ` follows
`s • X` from `x`. -/
noncomputable def pathMap (X : E → E) (p : (ℝ × E) × C(unitInterval, E)) : C(unitInterval, E) :=
  p.2 - ContinuousMap.const unitInterval p.1.2 - p.1.1 • primL E (compMap X p.2)

/-- Sending a point `x` to the path that stays at `x` is a linear and continuous map from points
to paths. -/
noncomputable def constPathL (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    F →L[ℝ] C(unitInterval, F) where
  toFun := ContinuousMap.const unitInterval
  map_add' x y := by ext t; simp
  map_smul' c x := by ext t; simp
  cont := ContinuousMap.continuous_const'

/-- `constPathL` of `x` is the path that stays at `x`. -/
theorem constPathL_apply {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (x : F) :
    constPathL F x = ContinuousMap.const unitInterval x := rfl

/-- The equation of a path, written out with the linear map `constPathL` for "the path that
stays at `x`". -/
theorem pathMap_eq (X : E → E) :
    pathMap X = fun p : (ℝ × E) × C(unitInterval, E) ↦
      p.2 - constPathL E p.1.2 - p.1.1 • primL E (compMap X p.2) := rfl

/-- If the field `X` is smooth on the open region `U`, the equation of a path is smooth in the
factor, the starting point and the path together, for paths that stay in `U`. -/
theorem contDiffOn_pathMap {X : E → E} {U : Set E} (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U) :
    ContDiffOn ℝ ∞ (pathMap X) (univ ×ˢ pathsIn unitInterval U) := by
  -- the path itself
  have h1 : ContDiffOn ℝ ∞ (fun p : (ℝ × E) × C(unitInterval, E) ↦ p.2)
      (univ ×ˢ pathsIn unitInterval U) := contDiff_snd.contDiffOn
  -- the path that stays at the starting point
  have h2 : ContDiffOn ℝ ∞ (fun p : (ℝ × E) × C(unitInterval, E) ↦ constPathL E p.1.2)
      (univ ×ˢ pathsIn unitInterval U) :=
    ((constPathL E).contDiff.comp (contDiff_snd.comp contDiff_fst)).contDiffOn
  -- the factor
  have h3 : ContDiffOn ℝ ∞ (fun p : (ℝ × E) × C(unitInterval, E) ↦ p.1.1)
      (univ ×ˢ pathsIn unitInterval U) := (contDiff_fst.comp contDiff_fst).contDiffOn
  -- the integral of `X` along the path
  have h5 : ContDiffOn ℝ ∞ (fun p : (ℝ × E) × C(unitInterval, E) ↦ compMap X p.2)
      (univ ×ˢ pathsIn unitInterval U) :=
    (contDiffOn_compMap hU hX).comp contDiff_snd.contDiffOn fun p hp ↦ hp.2
  have h4 : ContDiffOn ℝ ∞ (fun p : (ℝ × E) × C(unitInterval, E) ↦ primL E (compMap X p.2))
      (univ ×ˢ pathsIn unitInterval U) :=
    (primL E).contDiff.comp_contDiffOn h5
  rw [pathMap_eq]
  exact (h1.sub h2).sub (h3.smul h4)

/-- At factor `0`, starting point `x₀` and the path that stays at `x₀`, the slope of the equation
of a path in the directions of the path alone has an inverse (it is the map that changes
nothing). -/
theorem isInvertible_fderiv_pathMap {X : E → E} {U : Set E} (hU : IsOpen U)
    (hX : ContDiffOn ℝ ∞ X U) {x₀ : E} (hx₀ : x₀ ∈ U) :
    (fderiv ℝ (pathMap X) ((0, x₀), ContinuousMap.const unitInterval x₀) ∘L
      ContinuousLinearMap.inr ℝ (ℝ × E) C(unitInterval, E)).IsInvertible := by
  -- the equation of a path can be differentiated at this point: it is smooth near it
  have hmem : (univ : Set (ℝ × E)) ×ˢ pathsIn unitInterval U ∈
      𝓝 (((0 : ℝ), x₀), ContinuousMap.const unitInterval x₀) :=
    (isOpen_univ.prod (isOpen_pathsIn hU)).mem_nhds ⟨mem_univ _, const_mem_pathsIn hx₀⟩
  have hdiff : DifferentiableAt ℝ (pathMap X)
      (((0 : ℝ), x₀), ContinuousMap.const unitInterval x₀) :=
    ((contDiffOn_pathMap hU hX).contDiffAt hmem).differentiableAt (by simp)
  -- chain rule: the slope in the directions of the path is the slope of `γ ↦ pathMap X (0, x₀, γ)`
  have h : HasFDerivAt (pathMap X ∘ fun γ : C(unitInterval, E) ↦ (((0 : ℝ), x₀), γ))
      (fderiv ℝ (pathMap X) ((0, x₀), ContinuousMap.const unitInterval x₀) ∘L
        ContinuousLinearMap.inr ℝ (ℝ × E) C(unitInterval, E))
      (ContinuousMap.const unitInterval x₀) :=
    HasFDerivAt.comp (ContinuousMap.const unitInterval x₀) hdiff.hasFDerivAt
      (hasFDerivAt_prodMk_right ((0 : ℝ), x₀) (ContinuousMap.const unitInterval x₀))
  -- at factor `0` that function is `γ ↦ γ - (the path that stays at x₀)`
  have heq : (pathMap X ∘ fun γ : C(unitInterval, E) ↦ (((0 : ℝ), x₀), γ)) =
      fun γ ↦ γ - ContinuousMap.const unitInterval x₀ := by
    funext γ
    simp [pathMap]
  rw [heq] at h
  have h' : HasFDerivAt (fun γ : C(unitInterval, E) ↦ γ - ContinuousMap.const unitInterval x₀)
      (ContinuousLinearMap.id ℝ C(unitInterval, E)) (ContinuousMap.const unitInterval x₀) :=
    hasFDerivAt_sub_const _
  rw [h.unique h']
  exact ⟨ContinuousLinearEquiv.refl ℝ C(unitInterval, E), rfl⟩

end GravityInLean.Flows
