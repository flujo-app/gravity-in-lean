/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Curved.Unique
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# The expression that fixes the connection of a length measure

Board item `task:checks-connection-skeleton`. First file of the proof that every length measure
has a connection (`Goals/Connection.lean`), after the textbooks' formula of Koszul.

`Unique.lean` shows that a connection of `g` obeys Koszul's formula: twice "the change of `Y`
along `X`, measured against `Z`" equals an expression in slopes of `g` and brackets alone. This
file gives that expression a name (`koszulExpr`), so that the other files can take it as the
*definition* of the connection, and proves the facts about `g` that all of them need:

* `mdifferentiableAt_measure`: `g(Y, Z)` can be differentiated where `Y` and `Z` can;
* `mvfderiv_measure_swap`: the slope of `g(Y, Z)` is the slope of `g(Z, Y)`;
* `IsLengthMeasureOn.eq_of_forall_measure_eq`: a step is known once its measure against every
  step is known.
-/

@[expose] public section

namespace GravityInLean.Curved

open Bundle FiberBundle VectorField

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : LengthMeasure I M} {s : Set M} {x : M}

/-- **Koszul's expression.** For a connection of `g` it equals twice "the change of `Y` along
`X`, measured against `Z`" (`IsConnectionOf.koszul`); it is made of slopes of `g` and of
brackets only. -/
noncomputable def koszulExpr (g : LengthMeasure I M) (X Y Z : Arrows I M) (x : M) : ℝ :=
  d% (fun y ↦ g y (Y y) (Z y)) x (X x) + d% (fun y ↦ g y (Z y) (X y)) x (Y x)
    - d% (fun y ↦ g y (X y) (Y y)) x (Z x)
    - g x (Y x) (mlieBracket I X Z x) - g x (Z x) (mlieBracket I Y X x)
    + g x (X x) (mlieBracket I Z Y x)

/-- A connection of `g` obeys Koszul's formula, said with `koszulExpr`. -/
theorem IsConnectionOf.koszulExpr_eq {cov : Transport I M} (h : IsConnectionOf g cov s)
    (hg : IsLengthMeasureOn g s) (hx : x ∈ s) {X Y Z : Arrows I M} (hX : MDiffAt (T% X) x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    2 * g x (cov Y x (X x)) (Z x) = koszulExpr g X Y Z x :=
  h.koszul hg.symm hx hX hY hZ

/-- **`g(Y, Z)` can be differentiated** at a point of an open region where `g` is smooth, if the
fields `Y` and `Z` can be differentiated there. -/
theorem mdifferentiableAt_measure (hg : IsSmoothOn g s) (hs : IsOpen s) (hx : x ∈ s)
    {Y Z : Arrows I M} (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    MDiffAt (fun y ↦ g y (Y y) (Z y)) x := by
  have hgx : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) y (g y)) x :=
    ((hg x hx).contMDiffAt (hs.mem_nhds hx)).mdifferentiableAt (by simp)
  have key : MDifferentiableAt I (I.prod 𝓘(ℝ))
      (fun m ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) m (g m (Y m) (Z m))) x :=
    MDifferentiableAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hgx hY hZ
  rw [mdifferentiableAt_totalSpace] at key
  exact key.2

/-- **The slope of `g(Y, Z)` is the slope of `g(Z, Y)`**, at a point of an open region where the
order of the two steps does not matter: the two functions agree near the point. -/
theorem mvfderiv_measure_swap (hg : IsLengthMeasureOn g s) (hs : IsOpen s) (hx : x ∈ s)
    (Y Z : Arrows I M) :
    d% (fun y ↦ g y (Y y) (Z y)) x = d% (fun y ↦ g y (Z y) (Y y)) x := by
  have hev : (fun y ↦ g y (Y y) (Z y)) =ᶠ[𝓝 x] fun y ↦ g y (Z y) (Y y) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact hg.symm y hy (Y y) (Z y)
  exact hev.mfderiv_eq

/-- **A step is known once its measure against every step is known:** no step is at right angles
to all steps. -/
theorem IsLengthMeasureOn.eq_of_forall_measure_eq (hg : IsLengthMeasureOn g s) (hx : x ∈ s)
    {u u' : TangentSpace I x} (h : ∀ w : TangentSpace I x, g x u w = g x u' w) : u = u' := by
  refine sub_eq_zero.mp (hg.nondegenerate x hx _ fun w ↦ ?_)
  change g x (u - u') w = 0
  rw [map_sub, sub_apply, h w, sub_self]

end GravityInLean.Curved
