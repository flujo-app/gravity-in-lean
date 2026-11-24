/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.SchwKept
public import GravityInLean.Global.SphereRigid

import Mathlib.Tactic

/-!
# A map that keeps Schwarzschild's table of negative mass is, near each point, a symmetry

Board item `task:global-schw-local`. Let `f` be a map of coordinate space that keeps
Schwarzschild's table of a negative mass on an open set (`KeepsSchwOn` of `SchwKept.lean`). Then
near every point of the set, in ordinary space labels, `f` is one symmetry `schwSym ε c R` of
Schwarzschild's whole space-time: a shift of time, possibly turned round, and a turn or mirror
of space (`KeepsSchwOn.local`).

The three facts of `SchwKept.lean` are used as they stand: the distance label is kept, the split
of the steps into the `(t, r)` plane and the sphere is kept, and time is shifted, possibly
turned round. With the first two, what `f` does to the two angles keeps the lengths of the unit
sphere (`KeepsSchwOn.keeps_sphere`), so it is a turn or mirror of the sphere (`sphere_rigid` of
`SphereRigid.lean`). The distance label times the point of the sphere is the place in ordinary
space labels.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

variable {m : ℝ} {f : Coords 4 → Coords 4} {W : Set (Coords 4)} {x x₀ : Coords 4}

/-- One of the last two of four labels is the third or the fourth. -/
theorem fin_four_two_or_three (i : Fin 4) (hi : 2 ≤ i.val) : i = 2 ∨ i = 3 := by
  fin_cases i
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **What the map does to the two angles keeps the lengths of the unit sphere.** For a map that
keeps Schwarzschild's table of negative mass, the rates of change of the two new angles along
the two old angles satisfy what `dθ² + sin² θ dφ²` kept says, entry by entry. -/
theorem KeepsSchwOn.keeps_sphere (hm : m < 0) (h : KeepsSchwOn m f W) (hx : x ∈ W)
    (i j : Fin 4) (hi : 2 ≤ i.val) (hj : 2 ≤ j.val) :
    jac f 2 i x * jac f 2 j x + sin (f x 2) ^ 2 * (jac f 3 i x * jac f 3 j x)
      = if i = j then (if i = 2 then 1 else sin (x 2) ^ 2) else 0 := by
  have hfd : DifferentiableAt ℝ f x := (h.2.2.2 x hx).1.differentiableAt (by simp)
  have hpos : 0 < x 1 := (h.2.1 hx).1
  have hx1 : x 1 ^ 2 ≠ 0 := pow_ne_zero 2 hpos.ne'
  have hr : f x 1 = x 1 := h.radius hm hx
  have keep := (h.2.2.2 x hx).2.self_of_nhds
  have hJ : ∀ a μ : Fin 4, fderiv ℝ f x (Pi.single μ 1) a = jac f a μ x :=
    fun a μ ↦ (jac_eq_fderiv hfd a μ).symm
  -- steps along the sphere get no part in the `(t, r)` plane
  have s0 : jac f 0 i x = 0 := h.split hm hx 0 i (Or.inl ⟨by decide, hi⟩)
  have s1 : jac f 1 i x = 0 := h.split hm hx 1 i (Or.inl ⟨by decide, hi⟩)
  -- the lengths of the two steps along the labels `i` and `j`, before and after
  have key : x 1 ^ 2 * (jac f 2 i x * jac f 2 j x
        + sin (f x 2) ^ 2 * (jac f 3 i x * jac f 3 j x))
      = x 1 ^ 2 * ((Pi.single i 1 : Coords 4) 2 * (Pi.single j 1 : Coords 4) 2
          + sin (x 2) ^ 2 * ((Pi.single i 1 : Coords 4) 3 * (Pi.single j 1 : Coords 4) 3))
        + -schwA m (x 1) * ((Pi.single i 1 : Coords 4) 0 * (Pi.single j 1 : Coords 4) 0)
        + schwB m (x 1) * ((Pi.single i 1 : Coords 4) 1 * (Pi.single j 1 : Coords 4) 1) := by
    have e := keep (Pi.single i 1) (Pi.single j 1)
    rw [schw_apply, schw_apply] at e
    simp only [hJ] at e
    rw [hr] at e
    linear_combination e + (schwA m (x 1) * jac f 0 j x) * s0 - (schwB m (x 1) * jac f 1 j x) * s1
  apply mul_left_cancel₀ hx1
  rw [key]
  rcases fin_four_two_or_three i hi with rfl | rfl <;>
    rcases fin_four_two_or_three j hj with rfl | rfl <;> simp

/-- **A map that keeps Schwarzschild's table of negative mass is, near each point, a symmetry of
Schwarzschild's whole space-time.** In ordinary space labels, near every point of the set the
map is `schwSym ε c R`: time becomes `ε t + c` with `ε = 1` or `ε = -1`, and space is changed by
one turn or mirror `R`. -/
theorem KeepsSchwOn.local (hm : m < 0) (h : KeepsSchwOn m f W) (hx₀ : x₀ ∈ W) :
    ∃ (ε c : ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ), (ε = 1 ∨ ε = -1) ∧ R.transpose * R = 1 ∧
      ∀ᶠ x in 𝓝 x₀, sphericalToSpace (f x) = schwSym ε c R (sphericalToSpace x) := by
  have hW : IsOpen W := h.1
  have hf : ContDiffOn ℝ ∞ f W := fun x hx ↦ (h.2.2.2 x hx).1.contDiffWithinAt
  -- the two angles are changed by a turn or mirror of the sphere
  obtain ⟨R, hR, hsphere⟩ := sphere_rigid hW hx₀ hf
    (fun x hx ↦ ⟨(h.2.1 hx).2.2, (h.2.2.1 x hx).2.2⟩)
    (fun x hx ↦ ⟨h.split hm hx 2 0 (Or.inr ⟨by decide, by decide⟩),
      h.split hm hx 2 1 (Or.inr ⟨by decide, by decide⟩),
      h.split hm hx 3 0 (Or.inr ⟨by decide, by decide⟩),
      h.split hm hx 3 1 (Or.inr ⟨by decide, by decide⟩)⟩)
    (fun x hx i j hi hj ↦ h.keeps_sphere hm hx i j hi hj)
  -- time is shifted, possibly turned round
  obtain ⟨ε, c, hε, htime⟩ := h.time hm hx₀
  refine ⟨ε, c, R, hε, hR, ?_⟩
  filter_upwards [hsphere, htime, hW.mem_nhds hx₀] with x hS hT hxW
  have hr : f x 1 = x 1 := h.radius hm hxW
  have s0 : sin (f x 2) * cos (f x 3) = R 0 0 * (sin (x 2) * cos (x 3))
      + R 0 1 * (sin (x 2) * sin (x 3)) + R 0 2 * cos (x 2) :=
    (congrFun hS 0).trans (mulVec_three R _ 0)
  have s1 : sin (f x 2) * sin (f x 3) = R 1 0 * (sin (x 2) * cos (x 3))
      + R 1 1 * (sin (x 2) * sin (x 3)) + R 1 2 * cos (x 2) :=
    (congrFun hS 1).trans (mulVec_three R _ 1)
  have s2 : cos (f x 2) = R 2 0 * (sin (x 2) * cos (x 3))
      + R 2 1 * (sin (x 2) * sin (x 3)) + R 2 2 * cos (x 2) :=
    (congrFun hS 2).trans (mulVec_three R _ 2)
  funext k
  fin_cases k
  · change f x 0 = ε * x 0 + c
    exact hT
  · change f x 1 * sin (f x 2) * cos (f x 3) = R 0 0 * (x 1 * sin (x 2) * cos (x 3))
      + R 0 1 * (x 1 * sin (x 2) * sin (x 3)) + R 0 2 * (x 1 * cos (x 2))
    rw [hr]
    linear_combination x 1 * s0
  · change f x 1 * sin (f x 2) * sin (f x 3) = R 1 0 * (x 1 * sin (x 2) * cos (x 3))
      + R 1 1 * (x 1 * sin (x 2) * sin (x 3)) + R 1 2 * (x 1 * cos (x 2))
    rw [hr]
    linear_combination x 1 * s1
  · change f x 1 * cos (f x 2) = R 2 0 * (x 1 * sin (x 2) * cos (x 3))
      + R 2 1 * (x 1 * sin (x 2) * sin (x 3)) + R 2 2 * (x 1 * cos (x 2))
    rw [hr]
    linear_combination x 1 * s2

end GravityInLean.Curved
