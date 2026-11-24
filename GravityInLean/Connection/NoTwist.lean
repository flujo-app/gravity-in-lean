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
# The candidate has no twist

Board item `task:checks-connection-notwist`. Part of the proof that every length measure has a
connection. For the candidate `koszulCov g`: the change of `Y` along `X` minus the change of `X`
along `Y` is the bracket of the two fields. Measured against any field `Z`, the two Koszul
expressions differ by twice `g([X, Y], Z)`: the slopes cancel because the order of the two steps
does not matter, and the brackets because a bracket changes sign when its fields are swapped.
-/

@[expose] public section

namespace GravityInLean.Curved

open Bundle FiberBundle VectorField

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : LengthMeasure I M} {s : Set M} {x : M}

/-- **No twist, measured against a field `Z`:** the change of `Y` along `X` minus the change of
`X` along `Y`, measured against `Z`, is the bracket of `X` and `Y` measured against `Z`. -/
theorem koszulCov_noTwist_measured (hg : IsLengthMeasureOn g s) (hs : IsOpen s) (hx : x ∈ s)
    {X Y Z : Arrows I M} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    g x (koszulCov g Y x (X x) - koszulCov g X x (Y x)) (Z x)
      = g x (mlieBracket I X Y x) (Z x) := by
  -- Koszul's expression, for `(X, Y, Z)` and for `(Y, X, Z)`.
  have e1 : 2 * g x (koszulCov g Y x (X x)) (Z x)
      = d% (fun y ↦ g y (Y y) (Z y)) x (X x) + d% (fun y ↦ g y (Z y) (X y)) x (Y x)
        - d% (fun y ↦ g y (X y) (Y y)) x (Z x)
        - g x (Y x) (mlieBracket I X Z x) - g x (Z x) (mlieBracket I Y X x)
        + g x (X x) (mlieBracket I Z Y x) := koszulCov_spec hg hs hx hX hY hZ
  have e2 : 2 * g x (koszulCov g X x (Y x)) (Z x)
      = d% (fun y ↦ g y (X y) (Z y)) x (Y x) + d% (fun y ↦ g y (Z y) (Y y)) x (X x)
        - d% (fun y ↦ g y (Y y) (X y)) x (Z x)
        - g x (X x) (mlieBracket I Y Z x) - g x (Z x) (mlieBracket I X Y x)
        + g x (Y x) (mlieBracket I Z X x) := koszulCov_spec hg hs hx hY hX hZ
  -- The slopes: the order of the two steps does not matter.
  have d1 : d% (fun y ↦ g y (Y y) (Z y)) x (X x) = d% (fun y ↦ g y (Z y) (Y y)) x (X x) :=
    DFunLike.congr_fun (mvfderiv_measure_swap hg hs hx Y Z) (X x)
  have d2 : d% (fun y ↦ g y (Z y) (X y)) x (Y x) = d% (fun y ↦ g y (X y) (Z y)) x (Y x) :=
    DFunLike.congr_fun (mvfderiv_measure_swap hg hs hx Z X) (Y x)
  have d3 : d% (fun y ↦ g y (X y) (Y y)) x (Z x) = d% (fun y ↦ g y (Y y) (X y)) x (Z x) :=
    DFunLike.congr_fun (mvfderiv_measure_swap hg hs hx X Y) (Z x)
  -- The brackets: a bracket changes sign when its fields are swapped.
  have b1 : g x (Y x) (mlieBracket I X Z x) = -g x (Y x) (mlieBracket I Z X x) := by
    rw [mlieBracket_swap_apply (V := X) (W := Z), map_neg]
  have b2 : g x (Z x) (mlieBracket I Y X x) = -g x (Z x) (mlieBracket I X Y x) := by
    rw [mlieBracket_swap_apply (V := Y) (W := X), map_neg]
  have b3 : g x (X x) (mlieBracket I Z Y x) = -g x (X x) (mlieBracket I Y Z x) := by
    rw [mlieBracket_swap_apply (V := Z) (W := Y), map_neg]
  have s1 : g x (Z x) (mlieBracket I X Y x) = g x (mlieBracket I X Y x) (Z x) :=
    hg.symm x hx _ _
  rw [map_sub, sub_apply]
  linear_combination (e1 - e2) / 2 + (d1 + d2 - d3 - b1 - b2 + b3) / 2 + s1

/-- **The candidate has no twist:** changing `Y` along `X` minus changing `X` along `Y` is the
bracket of the two fields. -/
theorem koszulCov_noTwist (hg : IsLengthMeasureOn g s) (hs : IsOpen s) (hx : x ∈ s)
    {X Y : Arrows I M} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    koszulCov g Y x (X x) - koszulCov g X x (Y x) = mlieBracket I X Y x := by
  -- A step is known once its measure against every step is known.
  refine hg.eq_of_forall_measure_eq hx fun w ↦ ?_
  have h := koszulCov_noTwist_measured hg hs hx hX hY (mdifferentiableAt_extend I E w)
  rwa [extend_apply_self] at h

end GravityInLean.Curved
