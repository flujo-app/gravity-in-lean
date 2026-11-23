/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Curved.Basic
public import GravityInLean.Goals.Connection
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# A length measure has at most one connection

`Basic.lean` says what "the connection that belongs to a length measure" means. This file shows
that there cannot be two: on every field of arrows that can be differentiated, two connections of
the same length measure agree. So "the" connection is the right word, and "space is empty" cannot
be made true by picking a convenient connection.

* `IsConnectionOf.koszul`: what a connection of `g` does to a field is fixed by `g` alone (the
  textbooks' formula of Koszul).
* `IsConnectionOf.unique`: two connections of `g` agree.
* `connectionUnique`: this proves the statement `ConnectionUniqueStatement` of
  `Goals/Connection.lean`.

That a connection exists at all (`ConnectionExistsStatement`) is not proved here.
-/

@[expose] public section

namespace GravityInLean.Curved

open Bundle FiberBundle VectorField

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : LengthMeasure I M} {cov cov' : Transport I M} {s : Set M}

/-- **What a connection of `g` does is fixed by `g` alone** (Koszul's formula). For three fields
of arrows that can be differentiated at `x`: twice "the change of `Y` along `X`, measured against
`Z`" is a combination of slopes of `g` and of brackets, in which the connection does not appear. -/
theorem IsConnectionOf.koszul (h : IsConnectionOf g cov s)
    (hsymm : ∀ x ∈ s, ∀ v w : TangentSpace I x, g x v w = g x w v) {x : M} (hx : x ∈ s)
    {X Y Z : Arrows I M} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    2 * g x (cov Y x (X x)) (Z x)
      = d% (fun y ↦ g y (Y y) (Z y)) x (X x) + d% (fun y ↦ g y (Z y) (X y)) x (Y x)
        - d% (fun y ↦ g y (X y) (Y y)) x (Z x)
        - g x (Y x) (mlieBracket I X Z x) - g x (Z x) (mlieBracket I Y X x)
        + g x (X x) (mlieBracket I Z Y x) := by
  -- Keeping lengths, used three times.
  have k1 := h.keepsLengths x hx Y Z hY hZ (X x)
  have k2 := h.keepsLengths x hx Z X hZ hX (Y x)
  have k3 := h.keepsLengths x hx X Y hX hY (Z x)
  -- No twist, used three times.
  have t1 := h.noTwist x hx X Z hX hZ
  have t2 := h.noTwist x hx Y X hY hX
  have t3 := h.noTwist x hx Z Y hZ hY
  -- The order of the two steps does not matter.
  have s1 := hsymm x hx (Z x) (cov Y x (X x))
  have s2 := hsymm x hx (X x) (cov Z x (Y x))
  have s3 := hsymm x hx (Y x) (cov X x (Z x))
  rw [← t1, ← t2, ← t3]
  simp only [map_sub]
  linear_combination -k1 - k2 + k3 - s1 + s2 - s3

/-- **A length measure has at most one connection.** Two connections that belong to the same
length measure on a region give the same answer for every field of arrows that can be
differentiated at the point. -/
theorem IsConnectionOf.unique (hg : IsLengthMeasureOn g s) (h : IsConnectionOf g cov s)
    (h' : IsConnectionOf g cov' s) {x : M} (hx : x ∈ s) {Y : Arrows I M}
    (hY : MDiffAt (T% Y) x) : cov Y x = cov' Y x := by
  ext v
  have key : ∀ w : TangentSpace I x, g x (cov Y x v - cov' Y x v) w = 0 := by
    intro w
    have hX : MDiffAt (T% (extend E v)) x := mdifferentiableAt_extend I E v
    have hZ : MDiffAt (T% (extend E w)) x := mdifferentiableAt_extend I E w
    have e1 := h.koszul hg.symm hx hX hY hZ
    have e2 := h'.koszul hg.symm hx hX hY hZ
    simp only [extend_apply_self] at e1 e2
    simp only [map_sub, sub_apply]
    linarith
  exact sub_eq_zero.mp (hg.nondegenerate x hx _ key)

/-- **The statement `ConnectionUniqueStatement` is true.** -/
theorem connectionUnique : ConnectionUniqueStatement :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hg h h' _ hx _ hY ↦ h.unique hg h' hx hY

end GravityInLean.Curved
