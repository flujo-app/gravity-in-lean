/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Connection.Candidate

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# The candidate keeps lengths

Board item `task:checks-connection-keepslengths`. Part of the proof that every length measure
has a connection. For the candidate `koszulCov g`: the slope of `g(Y, Z)` along a step is what
the changes of `Y` and of `Z` along that step account for. The two Koszul expressions, for
`(X, Y, Z)` and for `(X, Z, Y)`, add up to twice the slope of `g(Y, Z)` along `X`: everything
else cancels in pairs.
-/

@[expose] public section

namespace GravityInLean.Curved

open Bundle FiberBundle VectorField

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : LengthMeasure I M} {s : Set M} {x : M}

/-- **Keeping lengths, along a field `X`:** the slope of `g(Y, Z)` along `X` is `g` of the change
of `Y` along `X` with `Z`, plus `g` of `Y` with the change of `Z` along `X`. -/
theorem koszulCov_keepsLengths_along (hg : IsLengthMeasureOn g s) (hs : IsOpen s) (hx : x ∈ s)
    {X Y Z : Arrows I M} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    d% (fun y ↦ g y (Y y) (Z y)) x (X x)
      = g x (koszulCov g Y x (X x)) (Z x) + g x (Y x) (koszulCov g Z x (X x)) := by
  -- Koszul's expression, for `(X, Y, Z)` and for `(X, Z, Y)`.
  have e1 : 2 * g x (koszulCov g Y x (X x)) (Z x)
      = d% (fun y ↦ g y (Y y) (Z y)) x (X x) + d% (fun y ↦ g y (Z y) (X y)) x (Y x)
        - d% (fun y ↦ g y (X y) (Y y)) x (Z x)
        - g x (Y x) (mlieBracket I X Z x) - g x (Z x) (mlieBracket I Y X x)
        + g x (X x) (mlieBracket I Z Y x) := koszulCov_spec hg hs hx hX hY hZ
  have e2 : 2 * g x (koszulCov g Z x (X x)) (Y x)
      = d% (fun y ↦ g y (Z y) (Y y)) x (X x) + d% (fun y ↦ g y (Y y) (X y)) x (Z x)
        - d% (fun y ↦ g y (X y) (Z y)) x (Y x)
        - g x (Z x) (mlieBracket I X Y x) - g x (Y x) (mlieBracket I Z X x)
        + g x (X x) (mlieBracket I Y Z x) := koszulCov_spec hg hs hx hX hZ hY
  -- The slopes: the order of the two steps does not matter.
  have d1 : d% (fun y ↦ g y (Z y) (Y y)) x (X x) = d% (fun y ↦ g y (Y y) (Z y)) x (X x) :=
    DFunLike.congr_fun (mvfderiv_measure_swap hg hs hx Z Y) (X x)
  have d2 : d% (fun y ↦ g y (Y y) (X y)) x (Z x) = d% (fun y ↦ g y (X y) (Y y)) x (Z x) :=
    DFunLike.congr_fun (mvfderiv_measure_swap hg hs hx Y X) (Z x)
  have d3 : d% (fun y ↦ g y (X y) (Z y)) x (Y x) = d% (fun y ↦ g y (Z y) (X y)) x (Y x) :=
    DFunLike.congr_fun (mvfderiv_measure_swap hg hs hx X Z) (Y x)
  -- The brackets: a bracket changes sign when its fields are swapped.
  have b1 : g x (Y x) (mlieBracket I X Z x) = -g x (Y x) (mlieBracket I Z X x) := by
    rw [mlieBracket_swap_apply (V := X) (W := Z), map_neg]
  have b2 : g x (Z x) (mlieBracket I Y X x) = -g x (Z x) (mlieBracket I X Y x) := by
    rw [mlieBracket_swap_apply (V := Y) (W := X), map_neg]
  have b3 : g x (X x) (mlieBracket I Z Y x) = -g x (X x) (mlieBracket I Y Z x) := by
    rw [mlieBracket_swap_apply (V := Z) (W := Y), map_neg]
  have s1 : g x (Y x) (koszulCov g Z x (X x)) = g x (koszulCov g Z x (X x)) (Y x) :=
    hg.symm x hx _ _
  linear_combination -(e1 + e2) / 2 - (d1 + d2 - d3 - b1 - b2 + b3) / 2 - s1

/-- **The candidate keeps lengths:** the slope of `g(Y, Z)` along the step `v` is `g` of the
change of `Y` with `Z`, plus `g` of `Y` with the change of `Z`. -/
theorem koszulCov_keepsLengths (hg : IsLengthMeasureOn g s) (hs : IsOpen s) (hx : x ∈ s)
    {Y Z : Arrows I M} (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (v : TangentSpace I x) :
    d% (fun y ↦ g y (Y y) (Z y)) x v
      = g x (koszulCov g Y x v) (Z x) + g x (Y x) (koszulCov g Z x v) := by
  -- Extend the step `v` to a field, in the standard library's way.
  have h := koszulCov_keepsLengths_along hg hs hx (mdifferentiableAt_extend I E v) hY hZ
  rwa [extend_apply_self] at h

end GravityInLean.Curved
