/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Turns.Basic
public import GravityInLean.NewCoordinates
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Instances.Matrix

import Mathlib.Tactic

/-!
# The goal file's words, in the words of the library

Board item `task:turns-bracket-fderiv`. The goal file speaks of fields of arrows by their four
parts, of slopes along one coordinate (`slope`), and of the table of slopes `jac` of a change of
coordinates. The library speaks of maps from points to arrows and of the slope `fderiv`, a linear
map. This file translates:

* `bracketOf_eq_lieB`: the bracket of the goal file is the bracket `lieB` of this folder;
* `contDiffOn_vec`: a field with smooth parts is a smooth map from points to arrows;
* `sum_jac_mul`: the table of slopes applied to an arrow is the library's slope applied to it;
* `continuousOn_det_jac`: the determinant of the table of slopes is continuous where the map is
  smooth.
-/

@[expose] public section

namespace GravityInLean.Turns

open GravityInLean Set Topology

open scoped ContDiff

/-- The library's slope of a field of arrows, applied to an arrow `w`, part `k`: the sum over
the coordinates of the part of `w` along that coordinate times the slope of the `k`-th part of
the field along it. -/
theorem fderiv_vec_apply {Z : Fin 4 → Coords 4 → ℝ} {x : Coords 4}
    (hZ : ∀ k, DifferentiableAt ℝ (Z k) x) (w : Coords 4) (k : Fin 4) :
    fderiv ℝ (vec Z) x w k = ∑ m, w m * slope m (Z k) x := by
  have h : fderiv ℝ (vec Z) x = ContinuousLinearMap.pi fun i ↦ fderiv ℝ (Z i) x :=
    (hasFDerivAt_pi.2 fun i ↦ (hZ i).hasFDerivAt).fderiv
  rw [h, ContinuousLinearMap.pi_apply, clm_apply_eq_sum]
  exact Finset.sum_congr rfl fun m _ ↦ by rw [slope_eq_fderiv (hZ k)]

/-- The bracket of two fields as the goal file writes it (with slopes along the coordinates) is
the bracket `lieB` written with the library's slope, part by part. -/
theorem bracketOf_eq_lieB {X Y : Fin 4 → Coords 4 → ℝ} {x : Coords 4}
    (hX : ∀ k, DifferentiableAt ℝ (X k) x) (hY : ∀ k, DifferentiableAt ℝ (Y k) x) (k : Fin 4) :
    bracketOf X Y k x = lieB (vec X) (vec Y) x k := by
  unfold lieB bracketOf
  rw [Pi.sub_apply, fderiv_vec_apply hY, fderiv_vec_apply hX]
  rfl

/-- A field of arrows whose four parts are smooth on a region is smooth there as a map from
points to arrows. -/
theorem contDiffOn_vec {ξ : Fin 4 → Coords 4 → ℝ} {s : Set (Coords 4)}
    (h : ∀ k, ContDiffOn ℝ ∞ (ξ k) s) : ContDiffOn ℝ ∞ (vec ξ) s :=
  contDiffOn_pi.2 h

/-- The table of slopes of a change of coordinates, applied to an arrow `w`, is the library's
slope of the change of coordinates applied to `w` (part `α` of it). -/
theorem sum_jac_mul {Φ : Coords 4 → Coords 4} {y : Coords 4} (hΦ : DifferentiableAt ℝ Φ y)
    (w : Coords 4) (α : Fin 4) : ∑ μ, jac Φ α μ y * w μ = fderiv ℝ Φ y w α := by
  have h := clm_apply_eq_sum
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 ↦ ℝ) α).comp (fderiv ℝ Φ y)) w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at h
  rw [h]
  exact Finset.sum_congr rfl fun μ _ ↦ by rw [jac_eq_fderiv hΦ, mul_comm]

/-- Each entry of the table of slopes of a change of coordinates is continuous on an open set
on which the change of coordinates is smooth. -/
theorem continuousOn_jac {Φ : Coords 4 → Coords 4} {W : Set (Coords 4)} (hW : IsOpen W)
    (hΦ : ContDiffOn ℝ ∞ Φ W) (α μ : Fin 4) : ContinuousOn (jac Φ α μ) W := by
  have hfd : ContinuousOn (fderiv ℝ Φ) W :=
    hΦ.continuousOn_fderiv_of_isOpen hW (by exact_mod_cast le_top)
  have h1 : ContinuousOn (fun y ↦ fderiv ℝ Φ y (Pi.single μ 1) α) W :=
    (continuous_apply α).comp_continuousOn (hfd.clm_apply continuousOn_const)
  refine h1.congr fun y hy ↦ jac_eq_fderiv ?_ α μ
  exact (hΦ.differentiableOn (by simp)).differentiableAt (hW.mem_nhds hy)

/-- The determinant of the table of slopes of a change of coordinates is continuous on an open
set on which the change of coordinates is smooth. -/
theorem continuousOn_det_jac {Φ : Coords 4 → Coords 4} {W : Set (Coords 4)} (hW : IsOpen W)
    (hΦ : ContDiffOn ℝ ∞ Φ W) : ContinuousOn (fun y ↦ (tab (jac Φ) y).det) W := by
  have hmat : ContinuousOn (fun y ↦ tab (jac Φ) y) W :=
    continuousOn_pi.2 fun a ↦ continuousOn_pi.2 fun b ↦ continuousOn_jac hW hΦ a b
  exact (continuous_id.matrix_det).comp_continuousOn hmat

end GravityInLean.Turns
