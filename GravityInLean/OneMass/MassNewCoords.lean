/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.OneMass.Mass
public import GravityInLean.Join.UsableNew

import Mathlib.Tactic

/-!
# The mass comes back from the coordinates that fit the turns

Board item `task:checks-mass-newcoords`. `turnsCoordinates` gives new coordinates `Φ` on a patch
`W` in which the three given fields, after one fixed rotation `R` among themselves, are the three
standard turns. This file shows that the mass at `y`, said with the new table `inNewCoords Φ g`
and the standard turns, is the mass at `Φ y`, said with the old table and the given fields. It is
`usable_inNewCoords` (`Join/UsableNew.lean`) read the other way, for the mass.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Mass

open GravityInLean.Curved GravityInLean.Join

open Real Filter Topology Matrix

open scoped ContDiff

/-- **The mass does not depend on the coordinates that fit the turns.** Take a good table `g` and
three fields that turn on a region `s`, and new coordinates `Φ` on an open patch `W`, smooth,
landing in `s`, losing no direction, in which the standard turns are a fixed rotation `R` of the
given fields. If the mass at `y` is `m` for the new table and the standard turns, then the mass
at `Φ y` is `m` for the old table and the given fields. -/
theorem massAt_of_inNewCoords {g ginv : Fin 4 → Fin 4 → Coords 4 → ℝ}
    {ξ : Fin 3 → Fin 4 → Coords 4 → ℝ} {s : Set (Coords 4)}
    (hg : Curved.IsRegularTableOn g ginv s) (hξ : TurnsOn g ξ s)
    {Φ : Coords 4 → Coords 4} {R : Matrix (Fin 3) (Fin 3) ℝ} {W : Set (Coords 4)}
    {y : Coords 4} (hW : IsOpen W) (hy : y ∈ W) (hΦs : ∀ y ∈ W, Φ y ∈ s)
    (hΦ : ContDiffOn ℝ ∞ Φ W) (hR : R * R.transpose = 1)
    (hdet : ∀ y ∈ W, sin (y 2) ≠ 0 ∧ (tab (jac Φ) y).det ≠ 0)
    (hturn : ∀ y ∈ W, ∀ i α, ∑ μ, jac Φ α μ y * stdTurn i μ y = ∑ j, R i j * ξ j α (Φ y))
    {m : ℝ}
    (hm : MassAt (Curved.flatMeasure (Curved.tableMeasure (inNewCoords Φ g))) Curved.turns y m) :
    MassAt (Curved.flatMeasure (Curved.tableMeasure g)) (fun i ↦ Curved.fieldOf (ξ i)) (Φ y) m := by
  have hd0 : DifferentiableAt ℝ Φ y := patch_differentiableAt hW hΦ hy
  have hRt : R.transpose * R = 1 := mul_eq_one_comm.mp hR
  have hx : Φ y ∈ s := hΦs y hy
  -- Near `y` the new size of the spheres is the old one, taken at `Φ z`.
  have hev : Curved.sizeSq (Curved.flatMeasure (Curved.tableMeasure (inNewCoords Φ g)))
      Curved.turns =ᶠ[𝓝 y] Curved.sizeSq (Curved.flatMeasure (Curved.tableMeasure g))
        (fun i ↦ Curved.fieldOf (ξ i)) ∘ Φ := by
    filter_upwards [hW.mem_nhds hy] with z hz
    exact sizeSq_inNewCoords (patch_differentiableAt hW hΦ hz) (hturn z hz) hRt
  -- So its slope is the old slope after the slope of the change of coordinates.
  have hf : DifferentiableAt ℝ (Curved.sizeSq (Curved.flatMeasure (Curved.tableMeasure g))
      (fun i ↦ Curved.fieldOf (ξ i))) (Φ y) :=
    differentiableAt_sizeSq (fun a b ↦ hg.differentiableAt hx a b) fun i k ↦
      ((hξ.smooth i k).contDiffAt (hg.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hfd : fderiv ℝ (Curved.sizeSq (Curved.flatMeasure (Curved.tableMeasure (inNewCoords Φ g)))
      Curved.turns) y
      = (fderiv ℝ (Curved.sizeSq (Curved.flatMeasure (Curved.tableMeasure g))
        (fun i ↦ Curved.fieldOf (ξ i))) (Φ y)).comp (fderiv ℝ Φ y) := by
    rw [hev.fderiv_eq]
    exact fderiv_comp y hf hd0
  -- The step that the mass at `y` is read from, in the words of tables.
  obtain ⟨n', hn', hmass⟩ : ∃ n' : Coords 4,
      (∀ w : Coords 4, Curved.tableMeasure (inNewCoords Φ g) y n' w
        = fderiv ℝ (Curved.sizeSq (Curved.flatMeasure (Curved.tableMeasure (inNewCoords Φ g)))
          Curved.turns) y w)
        ∧ massOf (Curved.sizeSq (Curved.flatMeasure (Curved.tableMeasure (inNewCoords Φ g)))
          Curved.turns y) (Curved.tableMeasure (inNewCoords Φ g) y n' n') = m := by
    obtain ⟨n', hn', hmass⟩ := hm
    refine ⟨n', fun w ↦ ?_, hmass⟩
    have hw := hn' w
    rw [Curved.mvfderiv_flat] at hw
    exact hw
  -- The change of coordinates loses no direction: every step at `Φ y` is seen from a step at `y`.
  have hU : IsUnit (tab (jac Φ) y).det := isUnit_iff_ne_zero.mpr (hdet y hy).2
  have hback : ∀ w : Coords 4, fderiv ℝ Φ y ((tab (jac Φ) y)⁻¹.mulVec w) = w := fun w ↦ by
    rw [fderiv_eq_mulVec hd0, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU,
      Matrix.one_mulVec]
  -- The step at `Φ y` is the step at `y`, as the change of coordinates sees it.
  refine ⟨fderiv ℝ Φ y n', fun w ↦ ?_, ?_⟩
  · rw [Curved.mvfderiv_flat]
    change Curved.tableMeasure g (Φ y) (fderiv ℝ Φ y n') w
      = fderiv ℝ (Curved.sizeSq (Curved.flatMeasure (Curved.tableMeasure g))
        (fun i ↦ Curved.fieldOf (ξ i))) (Φ y) w
    have h1 := hn' ((tab (jac Φ) y)⁻¹.mulVec w)
    rw [tableMeasure_inNewCoords g hd0, hfd, ContinuousLinearMap.comp_apply, hback] at h1
    exact h1
  · change massOf (Curved.sizeSq (Curved.flatMeasure (Curved.tableMeasure g))
        (fun i ↦ Curved.fieldOf (ξ i)) (Φ y))
      (Curved.tableMeasure g (Φ y) (fderiv ℝ Φ y n') (fderiv ℝ Φ y n')) = m
    have e1 := tableMeasure_inNewCoords g hd0 n' n'
    have e2 := sizeSq_inNewCoords (g := g) hd0 (hturn y hy) hRt
    rw [← e1, ← e2]
    exact hmass

end GravityInLean.Mass
