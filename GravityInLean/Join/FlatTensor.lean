/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Curved.Flat

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# On flat space, the full curvature of any connection only looks at the three steps

Board item `task:join-flattensor`. The full curvature at a point is defined in `Curved/Basic.lean`
by extending three steps to fields of arrows in one fixed way. On coordinate space
`Curved/Flat.lean` shows, for the connection "the plain slope plus a correction", that any other
way of extending the steps gives the same answer, and that every connection of the same length
measure has the same curvature for the fixed way of extending.

This file puts the two together: for **any** connection of a length measure on coordinate space,
the full curvature of three fields of arrows at a point is the full curvature of their three
arrows at that point (`curvatureOfFields_eq_curvatureAt_of_isConnectionOf`). It also says that the
full curvature at a point is a linear function of its first step
(`curvatureAt_eq_curvatureMap_of_isConnectionOf`, `curvatureAt_linear_of_isConnectionOf`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Join

open GravityInLean.Curved

open Bundle

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {g : E → E →L[ℝ] E →L[ℝ] ℝ} {A : E → E →L[ℝ] E →L[ℝ] E} {s : Set E}
  {cov : Transport 𝓘(ℝ, E) E} {x : E}

/-- Any connection of the length measure gives, for three fields of arrows, the same full
curvature as "the plain slope plus a correction" does. The fields need only be differentiable at
the point (the third one twice, with continuous second slope). -/
theorem curvatureOfFields_eq_flat_of_isConnectionOf (hg : IsLengthMeasureOn (flatMeasure g) s)
    (h₀ : IsConnectionOf (flatMeasure g) (flatTransport A) s)
    (h : IsConnectionOf (flatMeasure g) cov s) (hx : x ∈ s) (hA : DifferentiableAt ℝ A x)
    {X Y Z : Arrows 𝓘(ℝ, E) E} (hX : DifferentiableAt ℝ (plain X) x)
    (hY : DifferentiableAt ℝ (plain Y) x) (hZ : ContDiffAt ℝ 2 (plain Z) x) :
    curvatureOfFields cov X Y Z x = curvatureOfFields (flatTransport A) X Y Z x := by
  have hagree : ∀ y ∈ s, ∀ W : Arrows 𝓘(ℝ, E) E, MDiffAt (T% W) y →
      cov W y = flatTransport A W y := fun y hy W hW ↦ h.unique hg h₀ hy hW
  have hs : s ∈ 𝓝 x := h.isOpen.mem_nhds hx
  have hZ1 : DifferentiableAt ℝ (plain Z) x := hZ.differentiableAt (by simp)
  have hZ2 : DifferentiableAt ℝ (fderiv ℝ (plain Z)) x :=
    (hZ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  -- `Z` can be differentiated at every point near `x`, so there the two connections agree on it.
  have hZnear : ∀ᶠ y in 𝓝 x, y ∈ s ∧ DifferentiableAt ℝ (plain Z) y :=
    (Filter.eventually_of_mem hs fun y hy ↦ hy).and
      ((hZ.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by simp))
  have hnear : ∀ W : Arrows 𝓘(ℝ, E) E, ∀ᶠ y in 𝓝 x,
      cov Z y (W y) = flatTransport A Z y (W y) :=
    fun W ↦ hZnear.mono fun y hy ↦ by rw [hagree y hy.1 _ (mdiffAt_arrows_iff.mpr hy.2)]
  -- "`Z` carried along `W`" is a field that can be differentiated at `x`.
  have hdiff : ∀ W : Arrows 𝓘(ℝ, E) E, DifferentiableAt ℝ (plain W) x →
      MDiffAt (T% fun y ↦ flatTransport A Z y (W y)) x := by
    intro W hW
    rw [mdiffAt_arrows_iff]
    have e : plain (fun y ↦ flatTransport A Z y (W y))
        = fun y ↦ fderiv ℝ (plain Z) y (plain W y) + A y (plain Z y) (plain W y) := rfl
    rw [e]
    exact (hZ2.clm_apply hW).add (differentiableAt_apply₂ hA hZ1 hW)
  have hfirst : ∀ W : Arrows 𝓘(ℝ, E) E, DifferentiableAt ℝ (plain W) x →
      cov (fun y ↦ cov Z y (W y)) x
        = flatTransport A (fun y ↦ flatTransport A Z y (W y)) x := by
    intro W hW
    have h0 := hdiff W hW
    have h1 : MDiffAt (T% fun y ↦ cov Z y (W y)) x :=
      h0.congr_of_eventuallyEq ((hnear W).mono fun y hy ↦ congrArg (TotalSpace.mk' E y) hy)
    rw [h.isConnection.congr_of_eventuallyEq h1 h0 hs (hnear W), hagree x hx _ h0]
  unfold curvatureOfFields
  rw [hfirst Y hY, hfirst X hX, hagree x hx _ (mdiffAt_arrows_iff.mpr hZ1)]

/-- **The full curvature of any connection of a length measure on coordinate space only looks at
the three steps at the point.** For three fields of arrows, it is the full curvature of their
three arrows at that point: it does not matter how the steps are extended to fields. -/
theorem curvatureOfFields_eq_curvatureAt_of_isConnectionOf
    (hg : IsLengthMeasureOn (flatMeasure g) s)
    (h₀ : IsConnectionOf (flatMeasure g) (flatTransport A) s)
    (h : IsConnectionOf (flatMeasure g) cov s) (hx : x ∈ s) (hA : DifferentiableAt ℝ A x)
    {X Y Z : Arrows 𝓘(ℝ, E) E} (hX : DifferentiableAt ℝ (plain X) x)
    (hY : DifferentiableAt ℝ (plain Y) x) (hZ : ContDiffAt ℝ 2 (plain Z) x) :
    curvatureOfFields cov X Y Z x = curvatureAt cov x (X x) (Y x) (Z x) := by
  rw [curvatureOfFields_eq_flat_of_isConnectionOf hg h₀ h hx hA hX hY hZ,
    curvatureOfFields_flat_eq_curvatureAt hA hX hY hZ,
    curvatureAt_eq_of_isConnectionOf hg h₀ h hx hA]

/-- The full curvature at a point, for any connection of the length measure, is given by the
formula `curvatureMap` of `Curved/Flat.lean`, which is linear in the first step. -/
theorem curvatureAt_eq_curvatureMap_of_isConnectionOf (hg : IsLengthMeasureOn (flatMeasure g) s)
    (h₀ : IsConnectionOf (flatMeasure g) (flatTransport A) s)
    (h : IsConnectionOf (flatMeasure g) cov s) (hx : x ∈ s) (hA : DifferentiableAt ℝ A x)
    (u v w : E) : curvatureAt cov x u v w = curvatureMap A x v w u := by
  rw [curvatureAt_eq_of_isConnectionOf hg h₀ h hx hA, curvatureAt_flat hA, curvatureMap_apply]

/-- **The full curvature at a point is linear in its first step,** for any connection of a length
measure on coordinate space. -/
theorem curvatureAt_linear_of_isConnectionOf (hg : IsLengthMeasureOn (flatMeasure g) s)
    (h₀ : IsConnectionOf (flatMeasure g) (flatTransport A) s)
    (h : IsConnectionOf (flatMeasure g) cov s) (hx : x ∈ s) (hA : DifferentiableAt ℝ A x)
    (v w : E) : ∃ L : E →L[ℝ] E, ∀ u, curvatureAt cov x u v w = L u :=
  ⟨curvatureMap A x v w, fun u ↦
    curvatureAt_eq_curvatureMap_of_isConnectionOf hg h₀ h hx hA u v w⟩

end GravityInLean.Join
