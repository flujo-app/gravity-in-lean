/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Connection.Koszul
public import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Koszul's expression depends on its first field only through the step at the point

Board item `task:checks-connection-tensorial1`. Part of the proof that every length measure has a
connection. Koszul's expression `koszulExpr g X Y Z x` contains slopes and brackets of the field
`X`, but they cancel: multiplying `X` by a function `f` multiplies the expression by `f x`, and
it respects sums of fields. In the words of the standard library, it is *tensorial* in `X`. This
is what allows the connection to be a function of the step `X x` alone.
-/

@[expose] public section

namespace GravityInLean.Curved

open Bundle FiberBundle VectorField

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : LengthMeasure I M} {s : Set M} {x : M}

/-- **Koszul's expression is tensorial in its first field** (the direction of the change): it
respects sums, and multiplying `X` by a function `f` multiplies it by `f x`. -/
theorem tensorialAt_koszulExpr_first (hg : IsLengthMeasureOn g s) (hs : IsOpen s) (hx : x ∈ s)
    {Y Z : Arrows I M} (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    TensorialAt I E (koszulExpr g · Y Z x) x where
  smul {f X} hf hX := by
    -- The two slopes that contain `f • X`: the function is `f` times the function for `X`.
    have e2 : (fun y ↦ g y (Z y) ((f • X) y)) = fun y ↦ f y * g y (Z y) (X y) := by
      funext y
      simp
    have e3 : (fun y ↦ g y ((f • X) y) (Y y)) = fun y ↦ f y * g y (X y) (Y y) := by
      funext y
      simp
    -- The product rule for these two slopes, and for the two brackets that contain `f • X`.
    have d2 : d% (fun y ↦ f y * g y (Z y) (X y)) x
        = f x • d% (fun y ↦ g y (Z y) (X y)) x + g x (Z x) (X x) • d% f x :=
      mvfderiv_fun_mul hf (mdifferentiableAt_measure hg.smooth hs hx hZ hX)
    have d3 : d% (fun y ↦ f y * g y (X y) (Y y)) x
        = f x • d% (fun y ↦ g y (X y) (Y y)) x + g x (X x) (Y x) • d% f x :=
      mvfderiv_fun_mul hf (mdifferentiableAt_measure hg.smooth hs hx hX hY)
    have b4 : mlieBracket I (f • X) Z x = -d% f x (Z x) • X x + f x • mlieBracket I X Z x :=
      mlieBracket_smul_left hf hX
    have b5 : mlieBracket I Y (f • X) x = d% f x (Y x) • X x + f x • mlieBracket I Y X x :=
      mlieBracket_smul_right hf hX
    -- What is left over is the slope of `f` along `Z` times `g(Y, X) - g(X, Y)`, which is zero.
    have hsym : g x (X x) (Y x) = g x (Y x) (X x) := hg.symm x hx (X x) (Y x)
    change koszulExpr g (f • X) Y Z x = f x * koszulExpr g X Y Z x
    unfold koszulExpr
    rw [e2, e3, d2, d3, b4, b5]
    simp only [Pi.smul_apply', map_smul, map_add, add_apply, smul_apply, smul_eq_mul]
    rw [hsym]
    ring
  add {X₁ X₂} hX₁ hX₂ := by
    -- The two slopes that contain `X₁ + X₂`: the function is the sum of the two functions.
    have e2 : (fun y ↦ g y (Z y) ((X₁ + X₂) y))
        = fun y ↦ g y (Z y) (X₁ y) + g y (Z y) (X₂ y) := by
      funext y
      simp
    have e3 : (fun y ↦ g y ((X₁ + X₂) y) (Y y))
        = fun y ↦ g y (X₁ y) (Y y) + g y (X₂ y) (Y y) := by
      funext y
      simp
    -- The sum rule for these two slopes, and for the two brackets that contain `X₁ + X₂`.
    have d2 : d% (fun y ↦ g y (Z y) (X₁ y) + g y (Z y) (X₂ y)) x
        = d% (fun y ↦ g y (Z y) (X₁ y)) x + d% (fun y ↦ g y (Z y) (X₂ y)) x :=
      mvfderiv_fun_add (mdifferentiableAt_measure hg.smooth hs hx hZ hX₁)
        (mdifferentiableAt_measure hg.smooth hs hx hZ hX₂)
    have d3 : d% (fun y ↦ g y (X₁ y) (Y y) + g y (X₂ y) (Y y)) x
        = d% (fun y ↦ g y (X₁ y) (Y y)) x + d% (fun y ↦ g y (X₂ y) (Y y)) x :=
      mvfderiv_fun_add (mdifferentiableAt_measure hg.smooth hs hx hX₁ hY)
        (mdifferentiableAt_measure hg.smooth hs hx hX₂ hY)
    have b4 : mlieBracket I (X₁ + X₂) Z x = mlieBracket I X₁ Z x + mlieBracket I X₂ Z x :=
      mlieBracket_add_left hX₁ hX₂
    have b5 : mlieBracket I Y (X₁ + X₂) x = mlieBracket I Y X₁ x + mlieBracket I Y X₂ x :=
      mlieBracket_add_right hX₁ hX₂
    change koszulExpr g (X₁ + X₂) Y Z x = koszulExpr g X₁ Y Z x + koszulExpr g X₂ Y Z x
    unfold koszulExpr
    rw [e2, e3, d2, d3, b4, b5]
    simp only [Pi.add_apply, map_add, add_apply]
    ring

end GravityInLean.Curved
