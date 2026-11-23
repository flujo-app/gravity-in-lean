/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.UnitInterval
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

import Mathlib.Tactic

/-!
# Spaces of paths: the words the other files of `Flows/` share

A *path* here is a continuous function from a compact space `K` (later: the times from `0` to
`1`) into a space of vectors `E`. All such paths form a complete space of vectors `C(K, E)` of
their own; the length of a path is the largest length it reaches.

* `pathsIn K U`: the paths that stay inside the region `U`. An open set of paths if `U` is open.
* `compMap f`: apply the function `f` to every point of a path. This gives a path again as long
  as `f` is continuous where the path runs. (Elsewhere the answer is the path that stays at `0`;
  this never matters.)
-/

@[expose] public section

namespace GravityInLean.Flows

open Set Metric Topology

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The paths that stay inside the region `U`. -/
def pathsIn (K : Type*) [TopologicalSpace K] (U : Set E) : Set C(K, E) := {γ | ∀ t, γ t ∈ U}

omit [CompactSpace K] [NormedSpace ℝ E] in
/-- A path is in `pathsIn K U` exactly if each of its points is in `U`. -/
theorem mem_pathsIn {U : Set E} {γ : C(K, E)} : γ ∈ pathsIn K U ↔ ∀ t, γ t ∈ U := Iff.rfl

omit [NormedSpace ℝ E] in
/-- If the region `U` is open, so is the set of paths that stay inside it: a path close enough to
one that stays in `U` stays in `U` too. -/
theorem isOpen_pathsIn {U : Set E} (hU : IsOpen U) : IsOpen (pathsIn K U) := by
  have h : pathsIn K U = {γ : C(K, E) | MapsTo γ univ U} := by
    ext γ
    simp [pathsIn, MapsTo]
  rw [h]
  exact ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ hU

omit [CompactSpace K] [NormedSpace ℝ E] in
/-- The path that stays at one point of `U` stays inside `U`. -/
theorem const_mem_pathsIn {U : Set E} {x : E} (hx : x ∈ U) :
    ContinuousMap.const K x ∈ pathsIn K U := fun _ ↦ hx

open Classical in
/-- **Apply `f` along a path:** the path `t ↦ f (γ t)`. If that is not continuous (which cannot
happen when `f` is continuous where `γ` runs), the answer is the path that stays at `0`. -/
noncomputable def compMap (f : E → F) (γ : C(K, E)) : C(K, F) :=
  if h : Continuous (fun t ↦ f (γ t)) then ⟨fun t ↦ f (γ t), h⟩ else 0

omit [CompactSpace K] [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Where `f` is continuous on `U` and the path `γ` stays in `U`, `compMap f γ` at `t` is
`f (γ t)`. -/
theorem compMap_apply {f : E → F} {U : Set E} (hf : ContinuousOn f U) {γ : C(K, E)}
    (hγ : γ ∈ pathsIn K U) (t : K) : compMap f γ t = f (γ t) := by
  have h : Continuous (fun t ↦ f (γ t)) := hf.comp_continuous γ.continuous hγ
  simp [compMap, h]

end GravityInLean.Flows
