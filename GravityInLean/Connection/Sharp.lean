/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Curved.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

import Mathlib.Tactic

/-!
# Turning a measurement back into a step

Board item `task:checks-connection-sharp`. Part of the proof that every length measure has a
connection. This file is linear algebra only; no curved space appears.

Let `b` measure pairs of steps of a finite-dimensional space, such that no step is at right
angles to all steps. Then every rule `φ` that assigns a number to each step, linearly, is
"measure against `v`" for exactly one step `v`. The textbooks call the passage from `φ` to `v`
raising an index. Here it is `sharp b φ`. For measures with all lengths positive the standard
library has this (Riesz); a space-time has a time direction, so it is redone here from "no step
is at right angles to all steps" and a count of dimensions.
-/

@[expose] public section

namespace GravityInLean.Curved

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

/-- "Measure against `v`", as a linear function of the step `v`. -/
def flat (b : V →L[ℝ] V →L[ℝ] ℝ) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ where
  toFun v := (b v).toLinearMap
  map_add' v w := by ext u; simp
  map_smul' c v := by ext u; simp

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] in
/-- What `flat` does: it measures. -/
@[simp] theorem flat_apply (b : V →L[ℝ] V →L[ℝ] ℝ) (v w : V) : flat b v w = b v w := rfl

open Classical in
/-- **From a measurement back to a step.** If every linear rule `φ` is "measure against `v`" for
exactly one step `v`, then `sharp b φ` is that step; otherwise it is zero. -/
noncomputable def sharp (b : V →L[ℝ] V →L[ℝ] ℝ) : (V →ₗ[ℝ] ℝ) →ₗ[ℝ] V :=
  if h : Function.Bijective (flat b) then (LinearEquiv.ofBijective (flat b) h).symm.toLinearMap
  else 0

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] in
/-- If no step is at right angles to all steps, then (the space being finite-dimensional) every
linear rule is "measure against `v`" for exactly one step `v`. -/
theorem flat_bijective [FiniteDimensional ℝ V] (b : V →L[ℝ] V →L[ℝ] ℝ)
    (h : Nondegenerate fun v w : V ↦ b v w) : Function.Bijective (flat b) := by
  -- Two steps that measure alike are the same step: their difference measures as zero.
  have hinj : Function.Injective (flat b) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    exact h v fun w ↦ congrArg (fun ψ : V →ₗ[ℝ] ℝ ↦ ψ w) hv
  -- There are as many independent linear rules as independent steps.
  have hfin : Module.finrank ℝ V = Module.finrank ℝ (V →ₗ[ℝ] ℝ) :=
    (Subspace.dual_finrank_eq (K := ℝ) (V := V)).symm
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj⟩

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] in
/-- **`sharp b φ` is the step that measures as `φ` says:** if no step is at right angles to all
steps, then measuring `sharp b φ` against any step `w` gives `φ w`. -/
theorem sharp_apply [FiniteDimensional ℝ V] (b : V →L[ℝ] V →L[ℝ] ℝ)
    (h : Nondegenerate fun v w : V ↦ b v w) (φ : V →ₗ[ℝ] ℝ) (w : V) :
    b (sharp b φ) w = φ w := by
  have hb := flat_bijective b h
  have e : flat b (sharp b φ) = φ := by
    rw [sharp, dite_eq_left hb]
    exact (LinearEquiv.ofBijective (flat b) hb).apply_symm_apply φ
  exact congrArg (fun ψ : V →ₗ[ℝ] ℝ ↦ ψ w) e

end GravityInLean.Curved
