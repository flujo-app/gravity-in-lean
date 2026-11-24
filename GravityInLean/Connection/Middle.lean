/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Connection.Koszul

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Koszul's expression in its middle field: the sum rule and the product rule

Board item `task:checks-connection-middle`. Part of the proof that every length measure has a
connection. The middle field `Y` of `koszulExpr g X Y Z x` is the field that is changed. In it the
expression is not tensorial, and must not be: it obeys the two rules of a connection, said for
the expression. `IsConnection.lean` turns them into the rules for the connection itself.
-/

@[expose] public section

namespace GravityInLean.Curved

open Bundle FiberBundle VectorField

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : LengthMeasure I M} {s : Set M} {x : M}

/-- **The sum rule, for Koszul's expression:** in its middle field it respects sums. -/
theorem koszulExpr_add_middle (hg : IsLengthMeasureOn g s) (hs : IsOpen s) (hx : x ∈ s)
    {X Y Y' Z : Arrows I M} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hY' : MDiffAt (T% Y') x) (hZ : MDiffAt (T% Z) x) :
    koszulExpr g X (Y + Y') Z x = koszulExpr g X Y Z x + koszulExpr g X Y' Z x := by
  -- `g(Y + Y', Z)` is the sum of the functions `g(Y, Z)` and `g(Y', Z)`, and so for `g(X, ·)`.
  have e1 : (fun y ↦ g y ((Y + Y') y) (Z y))
      = (fun y ↦ g y (Y y) (Z y)) + fun y ↦ g y (Y' y) (Z y) := by
    funext y
    simp only [Pi.add_apply, map_add, add_apply]
  have e3 : (fun y ↦ g y (X y) ((Y + Y') y))
      = (fun y ↦ g y (X y) (Y y)) + fun y ↦ g y (X y) (Y' y) := by
    funext y
    simp only [Pi.add_apply, map_add]
  unfold koszulExpr
  rw [e1, e3, mvfderiv_add (mdifferentiableAt_measure hg.smooth hs hx hY hZ)
      (mdifferentiableAt_measure hg.smooth hs hx hY' hZ),
    mvfderiv_add (mdifferentiableAt_measure hg.smooth hs hx hX hY)
      (mdifferentiableAt_measure hg.smooth hs hx hX hY'),
    mlieBracket_add_left hY hY', mlieBracket_add_right hY hY']
  simp only [Pi.add_apply, map_add, add_apply]
  ring

/-- **The product rule, for Koszul's expression:** multiplying the middle field `Y` by a function
`f` multiplies the expression by `f x` and adds twice the slope of `f` along `X` times
`g(Y, Z)`. -/
theorem koszulExpr_smul_middle (hg : IsLengthMeasureOn g s) (hs : IsOpen s) (hx : x ∈ s)
    {X Y Z : Arrows I M} {f : M → ℝ} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) (hf : MDiffAt f x) :
    koszulExpr g X (f • Y) Z x
      = f x * koszulExpr g X Y Z x + 2 * (d% f x (X x) * g x (Y x) (Z x)) := by
  -- `g(f Y, Z)` is the product of the functions `f` and `g(Y, Z)`, and so for `g(X, ·)`.
  have e1 : (fun y ↦ g y ((f • Y) y) (Z y)) = f * fun y ↦ g y (Y y) (Z y) := by
    funext y
    simp only [Pi.smul_apply', Pi.mul_apply, map_smul, smul_apply,
      smul_eq_mul]
  have e3 : (fun y ↦ g y (X y) ((f • Y) y)) = f * fun y ↦ g y (X y) (Y y) := by
    funext y
    simp only [Pi.smul_apply', Pi.mul_apply, map_smul, smul_eq_mul]
  have hsym : g x (Z x) (Y x) = g x (Y x) (Z x) := hg.symm x hx (Z x) (Y x)
  unfold koszulExpr
  rw [e1, e3, mvfderiv_mul hf (mdifferentiableAt_measure hg.smooth hs hx hY hZ),
    mvfderiv_mul hf (mdifferentiableAt_measure hg.smooth hs hx hX hY),
    mlieBracket_smul_left hf hY, mlieBracket_smul_right hf hY]
  simp only [Pi.smul_apply', map_add, map_smul, map_neg, neg_smul, add_apply,
    smul_apply, smul_eq_mul, hsym]
  ring

end GravityInLean.Curved
