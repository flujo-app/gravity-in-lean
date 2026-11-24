/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.Tests
public import Mathlib.Analysis.Calculus.Deriv.Abs

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Tests 3, 10 and 11: zero fields are not round, and kinks are caught

Board item `task:checks-zero-kink`. Four of the tests of `Goals/Tests.lean`, each a case where a
definition of `Curved/Basic.lean` should fail, or should fail for one named reason only.

* `Tests.zeroNotRound`: three fields that are zero everywhere do not make flat space-time "the
  same from every side". What stops them is the clause "they span two directions": zero fields
  span no direction at all.
* `Tests.zeroMeetsOtherClauses`: the zero field does leave lengths unchanged, and its bracket
  with itself is zero. So it is that one clause, and no other, that stops zero fields.
* `Tests.kinkNotUnchanged`: a field with a kink does not "leave lengths unchanged" at the kink,
  because that definition first asks that the field can be differentiated there.
* `Tests.kinkNotSmooth`: a length measure whose distance entries have a kink is not smooth.

Both kink tests come down to one fact of ordinary calculus: the absolute value has no slope at
zero (`not_differentiableAt_abs_coord`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean

open Real Set VectorField

open scoped Manifold ContDiff

namespace Curved

namespace Tests

/-! ## 3. Zero fields are not "round" -/

/-- Three fields that are zero everywhere do not make flat space-time "the same from every
side": at each point they span no direction, not two. -/
theorem zeroNotRound : ZeroNotRound := by
  intro h
  have h1 := h.surfaces 0 (Set.mem_univ _)
  -- Zero arrows span only the zero step.
  have e : Submodule.span ℝ (Set.range fun _ : Fin 3 ↦
      (0 : TangentSpace 𝓘(ℝ, Coords 4) (0 : Coords 4))) = ⊥ := by
    rw [Set.range_const, Submodule.span_zero_singleton]
  have h2 : Module.finrank ℝ (Submodule.span ℝ (Set.range fun _ : Fin 3 ↦
      (0 : TangentSpace 𝓘(ℝ, Coords 4) (0 : Coords 4)))) = 0 := by
    rw [e, finrank_bot]
  have h3 : (0 : ℕ) = 2 := h2.symm.trans h1
  exact absurd h3 (by norm_num)

/-- The zero field leaves the lengths of flat space-time unchanged at every point, and its
bracket with itself is zero. So zero fields pass the clauses "unchanged" and "combine the way
turns do". -/
theorem zeroMeetsOtherClauses : ZeroMeetsOtherClauses := by
  intro x
  have e1 : plain (0 : Arrows 𝓘(ℝ, Coords 4) (Coords 4)) = fun _ ↦ (0 : Coords 4) := rfl
  refine ⟨?_, congrFun mlieBracket_zero_left x⟩
  have hg : DifferentiableAt ℝ (tableMeasure flatG) x :=
    differentiableAt_tableMeasure fun a b ↦ differentiableAt_const _
  have hξ : DifferentiableAt ℝ (plain (0 : Arrows 𝓘(ℝ, Coords 4) (Coords 4))) x := by
    rw [e1]
    exact differentiableAt_const _
  rw [leavesUnchangedAt_flat_iff hg hξ]
  intro y z
  rw [e1]
  simp only [fderiv_fun_const, Pi.zero_apply, map_zero, zero_apply, add_zero]

/-! ## 10 and 11. Kinks -/

/-- The absolute value of the distance coordinate has no slope where that coordinate is zero. -/
theorem not_differentiableAt_abs_coord :
    ¬ DifferentiableAt ℝ (fun p : Coords 4 ↦ |p 1|) 0 := by
  intro h
  -- Walk along the distance direction: `t ↦ (0, t, 0, 0)`.
  have hl : DifferentiableAt ℝ (fun t : ℝ ↦ t • (Pi.single 1 1 : Coords 4)) 0 :=
    (differentiableAt_id (𝕜 := ℝ) (x := (0 : ℝ))).smul_const (Pi.single 1 1 : Coords 4)
  have h' : DifferentiableAt ℝ (fun p : Coords 4 ↦ |p 1|)
      ((0 : ℝ) • (Pi.single 1 1 : Coords 4)) := by
    rw [zero_smul]
    exact h
  have h2 : DifferentiableAt ℝ
      ((fun p : Coords 4 ↦ |p 1|) ∘ fun t : ℝ ↦ t • (Pi.single 1 1 : Coords 4)) 0 :=
    h'.comp (0 : ℝ) hl
  have e : ((fun p : Coords 4 ↦ |p 1|) ∘ fun t : ℝ ↦ t • (Pi.single 1 1 : Coords 4))
      = (abs : ℝ → ℝ) := by
    funext t
    simp only [Function.comp_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  rw [e] at h2
  exact not_differentiableAt_abs_zero h2

/-- A field of arrows with a kink does not "leave lengths unchanged" at the kink: it cannot be
differentiated there, and the definition asks for that first. -/
theorem kinkNotUnchanged : KinkNotUnchanged := by
  intro h
  have h1 : DifferentiableAt ℝ (plain (fieldOf
      ![fun p : Coords 4 ↦ |p 1|, fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0])) 0 :=
    mdiffAt_arrows_iff.mp h.1
  rw [plain_fieldOf] at h1
  -- The time part of the field is the absolute value of the distance coordinate.
  exact not_differentiableAt_abs_coord (differentiableAt_pi.1 h1 0)

/-- A length measure whose distance entries have a kink is not smooth: the squared length of a
fixed step in the distance direction is `1 + |x 1|`, which has no slope at zero. -/
theorem kinkNotSmooth : KinkNotSmooth := by
  intro h
  have h1 : ContDiffOn ℝ ∞ (tableMeasure kinkG) Set.univ := isSmoothOn_flat_iff.mp h
  have h2 : DifferentiableAt ℝ (tableMeasure kinkG) 0 :=
    (h1.contDiffAt Filter.univ_mem).differentiableAt (by simp)
  have h3 : DifferentiableAt ℝ (fun x : Coords 4 ↦
      tableMeasure kinkG x (Pi.single 1 1) (Pi.single 1 1)) 0 :=
    differentiableAt_apply₂ h2 (differentiableAt_const _) (differentiableAt_const _)
  have e : (fun x : Coords 4 ↦ tableMeasure kinkG x (Pi.single 1 1) (Pi.single 1 1))
      = fun x ↦ 1 + |x 1| := by
    funext x
    change formOf (fun a b ↦ kinkG a b x) (Pi.single 1 1) (Pi.single 1 1) = 1 + |x 1|
    rw [formOf_single_single]
    simp [kinkG]
  rw [e] at h3
  have h4 : DifferentiableAt ℝ (fun x : Coords 4 ↦ 1 + |x 1| - 1) 0 := h3.sub_const 1
  have e2 : (fun x : Coords 4 ↦ 1 + |x 1| - 1) = fun x ↦ |x 1| := by
    funext x
    ring
  rw [e2] at h4
  exact not_differentiableAt_abs_coord h4

end Tests

end Curved

end GravityInLean
