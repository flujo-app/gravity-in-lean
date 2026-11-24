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
# Koszul's expression depends on its last field only through the step at the point

Board item `task:checks-connection-tensorial3`. Part of the proof that every length measure has a
connection. Koszul's expression `koszulExpr g X Y Z x` contains slopes and brackets of the field
`Z`, but they cancel: multiplying `Z` by a function `f` multiplies the expression by `f x`, and
it respects sums of fields. In the words of the standard library, it is *tensorial* in `Z`. This
is what allows the expression to be read as "a step, measured against the step `Z x`".
-/

@[expose] public section

namespace GravityInLean.Curved

open Bundle FiberBundle VectorField

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : LengthMeasure I M} {s : Set M} {x : M}

/-- Multiplying the last field by a function `f` multiplies Koszul's expression by `f x`. The
slopes of `f` that the product rule and the brackets bring in cancel: what is left of them is
the slope of `f` along `Y` times `g(Z, X) - g(X, Z)`, which is zero. -/
theorem koszulExpr_smul_third (hg : IsLengthMeasureOn g s) (hs : IsOpen s) (hx : x ∈ s)
    {X Y Z : Arrows I M} {f : M → ℝ} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hf : MDiffAt f x) (hZ : MDiffAt (T% Z) x) :
    koszulExpr g X Y (f • Z) x = f x • koszulExpr g X Y Z x := by
  -- The two measures that contain the field `f • Z`, as products of functions.
  have e1 : (fun y ↦ g y (Y y) ((f • Z) y)) = fun y ↦ f y * g y (Y y) (Z y) := by
    funext y
    change g y (Y y) (f y • Z y) = f y * g y (Y y) (Z y)
    rw [map_smul, smul_eq_mul]
  have e2 : (fun y ↦ g y ((f • Z) y) (X y)) = fun y ↦ f y * g y (Z y) (X y) := by
    funext y
    change g y (f y • Z y) (X y) = f y * g y (Z y) (X y)
    rw [map_smul, smul_apply, smul_eq_mul]
  -- The product rule for their slopes.
  have d1 : d% (fun y ↦ f y * g y (Y y) (Z y)) x
      = f x • d% (fun y ↦ g y (Y y) (Z y)) x + g x (Y x) (Z x) • d% f x :=
    mvfderiv_fun_mul hf (mdifferentiableAt_measure hg.smooth hs hx hY hZ)
  have d2 : d% (fun y ↦ f y * g y (Z y) (X y)) x
      = f x • d% (fun y ↦ g y (Z y) (X y)) x + g x (Z x) (X x) • d% f x :=
    mvfderiv_fun_mul hf (mdifferentiableAt_measure hg.smooth hs hx hZ hX)
  -- The two brackets that contain the field `f • Z`.
  have b1 : mlieBracket I X (f • Z) x = d% f x (X x) • Z x + f x • mlieBracket I X Z x :=
    mlieBracket_smul_right hf hZ
  have b2 : mlieBracket I (f • Z) Y x = -d% f x (Y x) • Z x + f x • mlieBracket I Z Y x :=
    mlieBracket_smul_left hf hZ
  have hfz : (f • Z) x = f x • Z x := rfl
  have hsym : g x (Z x) (X x) = g x (X x) (Z x) := hg.symm x hx (Z x) (X x)
  unfold koszulExpr
  rw [e1, e2, d1, d2, b1, b2, hfz]
  simp only [map_add, map_smul, add_apply, smul_apply,
    smul_eq_mul]
  linear_combination (d% f x (Y x)) * hsym

/-- Koszul's expression of a sum of two last fields is the sum of the two expressions: every
term of it respects sums. -/
theorem koszulExpr_add_third (hg : IsLengthMeasureOn g s) (hs : IsOpen s) (hx : x ∈ s)
    {X Y Z₁ Z₂ : Arrows I M} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ₁ : MDiffAt (T% Z₁) x) (hZ₂ : MDiffAt (T% Z₂) x) :
    koszulExpr g X Y (Z₁ + Z₂) x = koszulExpr g X Y Z₁ x + koszulExpr g X Y Z₂ x := by
  -- The two measures that contain the field `Z₁ + Z₂`, as sums of functions.
  have e1 : (fun y ↦ g y (Y y) ((Z₁ + Z₂) y))
      = fun y ↦ g y (Y y) (Z₁ y) + g y (Y y) (Z₂ y) := by
    funext y
    change g y (Y y) (Z₁ y + Z₂ y) = g y (Y y) (Z₁ y) + g y (Y y) (Z₂ y)
    rw [map_add]
  have e2 : (fun y ↦ g y ((Z₁ + Z₂) y) (X y))
      = fun y ↦ g y (Z₁ y) (X y) + g y (Z₂ y) (X y) := by
    funext y
    change g y (Z₁ y + Z₂ y) (X y) = g y (Z₁ y) (X y) + g y (Z₂ y) (X y)
    rw [map_add, add_apply]
  -- The sum rule for their slopes.
  have d1 : d% (fun y ↦ g y (Y y) (Z₁ y) + g y (Y y) (Z₂ y)) x
      = d% (fun y ↦ g y (Y y) (Z₁ y)) x + d% (fun y ↦ g y (Y y) (Z₂ y)) x :=
    mvfderiv_fun_add (mdifferentiableAt_measure hg.smooth hs hx hY hZ₁)
      (mdifferentiableAt_measure hg.smooth hs hx hY hZ₂)
  have d2 : d% (fun y ↦ g y (Z₁ y) (X y) + g y (Z₂ y) (X y)) x
      = d% (fun y ↦ g y (Z₁ y) (X y)) x + d% (fun y ↦ g y (Z₂ y) (X y)) x :=
    mvfderiv_fun_add (mdifferentiableAt_measure hg.smooth hs hx hZ₁ hX)
      (mdifferentiableAt_measure hg.smooth hs hx hZ₂ hX)
  -- The two brackets that contain the field `Z₁ + Z₂`.
  have b1 : mlieBracket I X (Z₁ + Z₂) x = mlieBracket I X Z₁ x + mlieBracket I X Z₂ x :=
    mlieBracket_add_right hZ₁ hZ₂
  have b2 : mlieBracket I (Z₁ + Z₂) Y x = mlieBracket I Z₁ Y x + mlieBracket I Z₂ Y x :=
    mlieBracket_add_left hZ₁ hZ₂
  have hz : (Z₁ + Z₂) x = Z₁ x + Z₂ x := rfl
  unfold koszulExpr
  rw [e1, e2, d1, d2, b1, b2, hz]
  simp only [map_add, add_apply]
  ring

/-- **Koszul's expression is tensorial in its last field** (the field measured against): it
respects sums, and multiplying `Z` by a function `f` multiplies it by `f x`. -/
theorem tensorialAt_koszulExpr_third (hg : IsLengthMeasureOn g s) (hs : IsOpen s) (hx : x ∈ s)
    {X Y : Arrows I M} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    TensorialAt I E (koszulExpr g X Y · x) x where
  smul hf hZ := koszulExpr_smul_third hg hs hx hX hY hf hZ
  add hZ₁ hZ₂ := koszulExpr_add_third hg hs hx hX hY hZ₁ hZ₂

end GravityInLean.Curved
