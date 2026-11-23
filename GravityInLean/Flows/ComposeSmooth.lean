/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Flows.ComposeDeriv

import Mathlib.Tactic

/-!
# "Apply `f` along a path" is smooth if `f` is

Board item `task:flows-compose-smooth`.
-/

@[expose] public section

namespace GravityInLean.Flows

open Set Metric Topology

open scoped ContDiff

universe u

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The same with a finite count of derivatives, and one derivative lost: if `f` can be
differentiated `n + 1` times with continuous result on the open region `U`, then "apply `f` along
a path" can be differentiated `n` times with continuous result on the paths that stay in `U`.
This holds for every target space `G` at once, which is what lets the count go up one step at a
time: the slope of `f` is a function of the same kind, into the space of linear maps. -/
theorem contDiffOn_compMap_nat {U : Set E} (hU : IsOpen U) (n : ℕ) :
    ∀ (G : Type u) [NormedAddCommGroup G] [NormedSpace ℝ G] (f : E → G),
      ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) f U →
        ContDiffOn ℝ n (compMap f : C(K, E) → C(K, G)) (pathsIn K U) := by
  induction n with
  | zero =>
    intro G _ _ f hf
    have hf1 : ContDiffOn ℝ 1 f U := hf.of_le le_add_self
    rw [Nat.cast_zero, contDiffOn_zero]
    intro γ hγ
    exact (hasFDerivAt_compMap hU hf1 hγ).continuousAt.continuousWithinAt
  | succ n ih =>
    intro G _ _ f hf
    have hf1 : ContDiffOn ℝ 1 f U := hf.of_le le_add_self
    rw [Nat.cast_add, Nat.cast_one] at hf ⊢
    -- the slope of `f` is a function of the same kind, with one derivative less
    have hd : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) (fderiv ℝ f) U := hf.fderiv_of_isOpen hU le_rfl
    have key : ContDiffOn ℝ n (compMap (fderiv ℝ f) : C(K, E) → C(K, E →L[ℝ] G)) (pathsIn K U) :=
      ih (E →L[ℝ] G) (fderiv ℝ f) hd
    rw [contDiffOn_succ_iff_fderiv_of_isOpen (isOpen_pathsIn hU)]
    refine ⟨fun γ hγ ↦ (hasFDerivAt_compMap hU hf1 hγ).differentiableAt.differentiableWithinAt,
      fun h ↦ absurd h (WithTop.natCast_ne_top n), ?_⟩
    -- the slope of "apply `f` along a path" is "apply the slope of `f` along the path",
    -- followed by a continuous linear map
    refine ((appL K E G).contDiff.comp_contDiffOn key).congr fun γ hγ ↦ ?_
    exact (hasFDerivAt_compMap hU hf1 hγ).fderiv

/-- If `f` is smooth on the open region `U`, then "apply `f` along a path" is smooth, as a map
from paths to paths, on the paths that stay in `U`. -/
theorem contDiffOn_compMap {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (compMap f : C(K, E) → C(K, F)) (pathsIn K U) := by
  rw [contDiffOn_infty]
  intro n
  have hn : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f U := contDiffOn_infty.1 hf (n + 1)
  rw [Nat.cast_add, Nat.cast_one] at hn
  exact contDiffOn_compMap_nat hU n F f hn

end GravityInLean.Flows
