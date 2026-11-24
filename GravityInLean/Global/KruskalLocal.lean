/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.KruskalPlane
public import GravityInLean.Global.SphereRigid
public import GravityInLean.Rim.Table

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# A map that keeps Kruskal's table is, near every point, a symmetry of Kruskal's whole space-time

Board item `task:global-kruskal-local`. A map `f` of coordinate space that keeps Kruskal's table
(`KeepsKruskalOn`, `Global/KruskalKept.lean`) is, after wrapping the angles round the sphere,
one symmetry `kruskalSym L R` of Kruskal's whole space-time near every point
(`KeepsKruskalOn.local`).

The two halves are known:

* the `(T, X)` part of `f` is a matrix `L` that keeps `-T² + X²` (`KeepsKruskalOn.plane`);
* the angle part of `f` keeps the lengths of the unit sphere (`KeepsKruskalOn.sphere`, shown
  here: Kruskal's table on two steps along the angles is `r²` times the sphere's length, the
  split is kept, and `r²` is kept and positive), so it is a turn or mirror `R` of the sphere
  (`sphere_rigid`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

/-! ## The basic steps along the angles -/

/-- A basic step along one of the two angles has no part along `T` or `X`. -/
theorem single_angle_low (i : Fin 4) (hi : 2 ≤ i.val) :
    (Pi.single i 1 : Coords 4) 0 = 0 ∧ (Pi.single i 1 : Coords 4) 1 = 0 := by
  fin_cases i <;> first | (exfalso; revert hi; decide) | simp

/-- The sphere's length `dθ² + c dφ²` of two basic steps along the angles. -/
theorem single_angle_form (i j : Fin 4) (hi : 2 ≤ i.val) (hj : 2 ≤ j.val) (c : ℝ) :
    (Pi.single i 1 : Coords 4) 2 * (Pi.single j 1 : Coords 4) 2
        + c * ((Pi.single i 1 : Coords 4) 3 * (Pi.single j 1 : Coords 4) 3)
      = if i = j then (if i = 2 then 1 else c) else 0 := by
  fin_cases i <;> fin_cases j <;> first | (exfalso; revert hi hj; decide) | simp

/-! ## The angle part keeps the lengths of the sphere -/

variable {m : ℝ} {f : Coords 4 → Coords 4} {W : Set (Coords 4)} {x₀ : Coords 4}

/-- A map that keeps Kruskal's table is smooth on its region. -/
theorem KeepsKruskalOn.contDiffOn (h : KeepsKruskalOn m f W) : ContDiffOn ℝ ∞ f W :=
  fun x hx ↦ (h.2.2.2 x hx).1.contDiffWithinAt

/-- **The angle part of a map that keeps Kruskal's table keeps the lengths of the unit sphere:**
for two basic steps along the angles, `dθ² + sin² θ dφ²` of the steps as `f` carries them is
`dθ² + sin² θ dφ²` of the steps. -/
theorem KeepsKruskalOn.sphere (hm : 0 < m) (h : KeepsKruskalOn m f W) {x : Coords 4}
    (hx : x ∈ W) (i j : Fin 4) (hi : 2 ≤ i.val) (hj : 2 ≤ j.val) :
    jac f 2 i x * jac f 2 j x + sin (f x 2) ^ 2 * (jac f 3 i x * jac f 3 j x)
      = if i = j then (if i = 2 then 1 else sin (x 2) ^ 2) else 0 := by
  have hd : DifferentiableAt ℝ f x := (h.2.2.2 x hx).1.differentiableAt (by simp)
  -- Kruskal's table on the two basic steps, before and after
  have hc := (h.2.2.2 x hx).2.self_of_nhds (Pi.single i 1) (Pi.single j 1)
  rw [kruskalG_apply, kruskalG_apply, ← jac_eq_fderiv hd 0 i, ← jac_eq_fderiv hd 1 i,
    ← jac_eq_fderiv hd 2 i, ← jac_eq_fderiv hd 3 i, ← jac_eq_fderiv hd 0 j,
    ← jac_eq_fderiv hd 1 j, ← jac_eq_fderiv hd 2 j, ← jac_eq_fderiv hd 3 j] at hc
  -- the split: steps along the angles get no part along `T` or `X`
  have z0i : jac f 0 i x = 0 := h.split hm hx 0 i (Or.inl ⟨by decide, hi⟩)
  have z1i : jac f 1 i x = 0 := h.split hm hx 1 i (Or.inl ⟨by decide, hi⟩)
  obtain ⟨ei0, ei1⟩ := single_angle_low i hi
  -- the size of the spheres is kept, and it is positive
  have hS : kruskalS m (f x 0) (f x 1) = kruskalS m (x 0) (x 1) := by
    unfold kruskalS
    rw [h.radius hm hx]
  have hSpos : 0 < kruskalS m (x 0) (x 1) := kruskalS_pos hm (h.2.1 hx).1
  rw [z0i, z1i, ei0, ei1, hS] at hc
  rw [← single_angle_form i j hi hj (sin (x 2) ^ 2)]
  refine mul_left_cancel₀ hSpos.ne' ?_
  linear_combination hc

/-! ## The result -/

/-- **A map of coordinate space that keeps Kruskal's table is a symmetry of Kruskal's whole
space-time, near every point:** after wrapping round the sphere, it is `kruskalSym L R`, with
`L` a matrix that keeps `-T² + X²` and `R` a turn or mirror of the sphere. -/
theorem KeepsKruskalOn.local (hm : 0 < m) (h : KeepsKruskalOn m f W) (hx₀ : x₀ ∈ W) :
    ∃ (L : Matrix (Fin 2) (Fin 2) ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ),
      L.transpose * lightSign2 * L = lightSign2 ∧ R.transpose * R = 1 ∧
        ∀ᶠ x in 𝓝 x₀, kruskalWrap (f x) = kruskalSym L R (kruskalWrap x) := by
  obtain ⟨L, hL, hplane⟩ := h.plane hm hx₀
  obtain ⟨R, hR, hsphere⟩ := sphere_rigid h.1 hx₀ h.contDiffOn
    (fun x hx ↦ ⟨(h.2.1 hx).2, (h.2.2.1 x hx).2⟩)
    (fun x hx ↦ ⟨h.split hm hx 2 0 (Or.inr ⟨by decide, by decide⟩),
      h.split hm hx 2 1 (Or.inr ⟨by decide, by decide⟩),
      h.split hm hx 3 0 (Or.inr ⟨by decide, by decide⟩),
      h.split hm hx 3 1 (Or.inr ⟨by decide, by decide⟩)⟩)
    (fun x hx i j hi hj ↦ h.sphere hm hx i j hi hj)
  refine ⟨L, R, hL, hR, ?_⟩
  filter_upwards [hplane, hsphere] with x hx1 hx2
  -- the three rows of the turn
  have g0 : sin (f x 2) * cos (f x 3) = R 0 0 * (sin (x 2) * cos (x 3))
      + R 0 1 * (sin (x 2) * sin (x 3)) + R 0 2 * cos (x 2) := by
    have e := congrFun hx2 0
    rw [mulVec_three] at e
    exact e
  have g1 : sin (f x 2) * sin (f x 3) = R 1 0 * (sin (x 2) * cos (x 3))
      + R 1 1 * (sin (x 2) * sin (x 3)) + R 1 2 * cos (x 2) := by
    have e := congrFun hx2 1
    rw [mulVec_three] at e
    exact e
  have g2 : cos (f x 2) = R 2 0 * (sin (x 2) * cos (x 3))
      + R 2 1 * (sin (x 2) * sin (x 3)) + R 2 2 * cos (x 2) := by
    have e := congrFun hx2 2
    rw [mulVec_three] at e
    exact e
  have e : kruskalWrap (f x)
      = ![f x 0, f x 1, sin (f x 2) * cos (f x 3), sin (f x 2) * sin (f x 3), cos (f x 2)] := rfl
  have e' : kruskalSym L R (kruskalWrap x)
      = ![L 0 0 * x 0 + L 0 1 * x 1, L 1 0 * x 0 + L 1 1 * x 1,
        R 0 0 * (sin (x 2) * cos (x 3)) + R 0 1 * (sin (x 2) * sin (x 3)) + R 0 2 * cos (x 2),
        R 1 0 * (sin (x 2) * cos (x 3)) + R 1 1 * (sin (x 2) * sin (x 3)) + R 1 2 * cos (x 2),
        R 2 0 * (sin (x 2) * cos (x 3)) + R 2 1 * (sin (x 2) * sin (x 3)) + R 2 2 * cos (x 2)] :=
    rfl
  rw [e, e', hx1.1, hx1.2, g0, g1, g2]

end GravityInLean.Curved
