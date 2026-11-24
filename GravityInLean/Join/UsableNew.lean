/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Curved.Goal
public import GravityInLean.Join.NewTable

import Mathlib.Tactic

/-!
# The usable distance carries over to the coordinates that fit the turns

Board item `task:join-usable-new`. `turnsCoordinates` gives new coordinates `Φ` on a patch `W` in
which the three given fields, after one fixed rotation `R` among themselves, are the three
standard turns. This file shows that "the size of the spheres is a usable distance"
(`Curved.UsableDistanceAt`) at `Φ y₀`, said with the old table and the given fields, gives the
same at `y₀`, said with the new table `inNewCoords Φ g` and the standard turns.

* `sum_rotated`: the sum of the squared lengths of three steps does not change when the three
  are rotated among themselves.
* `sizeSq_inNewCoords`: the squared size of the spheres at `y`, read off the new table and the
  standard turns, is the squared size at `Φ y`, read off the old table and the given fields.
* `differentiableAt_sizeSq`: the squared size of the spheres of a table can be differentiated
  where the table and the fields can.
* `usable_inNewCoords`: the usable distance carries over.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Join

open Real Filter Topology Matrix

open scoped ContDiff

/-- The sum of the squared lengths of three steps does not change when the three steps are
rotated among themselves: mixed by a fixed table of numbers `R` with `Rᵀ R = 1`. -/
theorem sum_rotated {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : E →L[ℝ] E →L[ℝ] ℝ) (X : Fin 3 → E) {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R.transpose * R = 1) :
    ∑ i, b (∑ j, R i j • X j) (∑ k, R i k • X k) = ∑ j, b (X j) (X j) := by
  have hR' : ∀ j k, ∑ i, R i j * R i k = if j = k then 1 else 0 := by
    intro j k
    have h := congrFun (congrFun hR j) k
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    exact h
  have key : ∀ i, b (∑ j, R i j • X j) (∑ k, R i k • X k)
      = ∑ j, ∑ k, R i j * R i k * b (X j) (X k) := by
    intro i
    simp only [map_sum, map_smul, FunLike.coe_sum, FunLike.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
  calc ∑ i, b (∑ j, R i j • X j) (∑ k, R i k • X k)
      = ∑ i, ∑ j, ∑ k, R i j * R i k * b (X j) (X k) := Finset.sum_congr rfl fun i _ ↦ key i
    _ = ∑ j, ∑ k, ∑ i, R i j * R i k * b (X j) (X k) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_comm
    _ = ∑ j, ∑ k, (if j = k then 1 else 0) * b (X j) (X k) :=
        Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by
          rw [← Finset.sum_mul, hR' j k]
    _ = ∑ j, b (X j) (X j) := Finset.sum_congr rfl fun j _ ↦ by simp

section Size

variable {g : Fin 4 → Fin 4 → Coords 4 → ℝ} {ξ : Fin 3 → Fin 4 → Coords 4 → ℝ}
  {Φ : Coords 4 → Coords 4} {R : Matrix (Fin 3) (Fin 3) ℝ}

/-- **The size of the spheres does not depend on the coordinates.** Where the change of
coordinates turns the three standard turns into a rotated mix of the three given fields, the
squared size of the spheres at `y`, read off the new table and the standard turns, is the squared
size at `Φ y`, read off the old table and the given fields. -/
theorem sizeSq_inNewCoords {y : Coords 4} (hd : DifferentiableAt ℝ Φ y)
    (hturn : ∀ i α, ∑ μ, jac Φ α μ y * stdTurn i μ y = ∑ j, R i j * ξ j α (Φ y))
    (hR : R.transpose * R = 1) :
    Curved.sizeSq (Curved.flatMeasure (Curved.tableMeasure (inNewCoords Φ g))) Curved.turns y
      = Curved.sizeSq (Curved.flatMeasure (Curved.tableMeasure g))
        (fun i ↦ Curved.fieldOf (ξ i)) (Φ y) := by
  have e1 : Curved.sizeSq (Curved.flatMeasure (Curved.tableMeasure (inNewCoords Φ g)))
      Curved.turns y
      = (∑ i : Fin 3, Curved.tableMeasure (inNewCoords Φ g) y (fun k ↦ stdTurn i k y)
        (fun k ↦ stdTurn i k y)) / 2 := by
    rw [Fin.sum_univ_three]
    rfl
  have e2 : Curved.sizeSq (Curved.flatMeasure (Curved.tableMeasure g))
      (fun i ↦ Curved.fieldOf (ξ i)) (Φ y)
      = (∑ j : Fin 3, Curved.tableMeasure g (Φ y) (fun k ↦ ξ j k (Φ y))
        (fun k ↦ ξ j k (Φ y))) / 2 := by
    rw [Fin.sum_univ_three]
    rfl
  -- The change of coordinates sees each standard turn as a mix of the given fields.
  have hD : ∀ i, fderiv ℝ Φ y (fun k ↦ stdTurn i k y)
      = ∑ j, R i j • (fun k ↦ ξ j k (Φ y) : Coords 4) := by
    intro i
    funext α
    rw [fderiv_apply_eq_sum_jac hd, hturn i α, Finset.sum_apply]
    rfl
  rw [e1, e2]
  congr 1
  simp only [tableMeasure_inNewCoords g hd, hD]
  exact sum_rotated (Curved.tableMeasure g (Φ y)) (fun j ↦ (fun k ↦ ξ j k (Φ y) : Coords 4)) hR

/-- The squared size of the spheres, read off a table and three fields given by their parts, can
be differentiated where the table and the fields can. -/
theorem differentiableAt_sizeSq {x : Coords 4} (hg : ∀ a b, DifferentiableAt ℝ (g a b) x)
    (hξ : ∀ i k, DifferentiableAt ℝ (ξ i k) x) :
    DifferentiableAt ℝ (Curved.sizeSq (Curved.flatMeasure (Curved.tableMeasure g))
      (fun i ↦ Curved.fieldOf (ξ i))) x := by
  have hT := Curved.differentiableAt_tableMeasure hg
  have hX : ∀ i, DifferentiableAt ℝ (fun z ↦ (fun k ↦ ξ i k z : Coords 4)) x :=
    fun i ↦ differentiableAt_pi.2 (hξ i)
  have h1 : ∀ i, DifferentiableAt ℝ
      (fun z ↦ Curved.tableMeasure g z (fun k ↦ ξ i k z) (fun k ↦ ξ i k z)) x :=
    fun i ↦ (hT.clm_apply (hX i)).clm_apply (hX i)
  change DifferentiableAt ℝ (fun z ↦
    (Curved.tableMeasure g z (fun k ↦ ξ 0 k z) (fun k ↦ ξ 0 k z)
      + Curved.tableMeasure g z (fun k ↦ ξ 1 k z) (fun k ↦ ξ 1 k z)
      + Curved.tableMeasure g z (fun k ↦ ξ 2 k z) (fun k ↦ ξ 2 k z)) / 2) x
  have h2 := (((h1 0).fun_add (h1 1)).fun_add (h1 2)).mul_const (2⁻¹ : ℝ)
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ ?_)
  simp only [div_eq_mul_inv]

end Size

/-- **The usable distance carries over to the coordinates that fit the turns.** Take a good table
`g` and three fields that turn on a region `s`, and new coordinates `Φ` on an open patch `W`,
smooth, landing in `s`, losing no direction, in which the standard turns are a fixed rotation `R`
of the given fields. If the size of the spheres is a usable distance at `Φ y₀` for the old table
and the given fields, then it is a usable distance at `y₀` for the new table and the standard
turns. -/
theorem usable_inNewCoords {g ginv : Fin 4 → Fin 4 → Coords 4 → ℝ}
    {ξ : Fin 3 → Fin 4 → Coords 4 → ℝ} {s : Set (Coords 4)}
    (hg : Curved.IsRegularTableOn g ginv s) (hξ : TurnsOn g ξ s)
    {Φ : Coords 4 → Coords 4} {R : Matrix (Fin 3) (Fin 3) ℝ} {W : Set (Coords 4)}
    {y₀ : Coords 4} (hW : IsOpen W) (hy₀ : y₀ ∈ W) (hΦs : ∀ y ∈ W, Φ y ∈ s)
    (hΦ : ContDiffOn ℝ ∞ Φ W) (hR : R * R.transpose = 1)
    (hdet : ∀ y ∈ W, sin (y 2) ≠ 0 ∧ (tab (jac Φ) y).det ≠ 0)
    (hturn : ∀ y ∈ W, ∀ i α, ∑ μ, jac Φ α μ y * stdTurn i μ y = ∑ j, R i j * ξ j α (Φ y))
    (hu : Curved.UsableDistanceAt (Curved.flatMeasure (Curved.tableMeasure g))
      (fun i ↦ Curved.fieldOf (ξ i)) (Φ y₀)) :
    Curved.UsableDistanceAt (Curved.flatMeasure (Curved.tableMeasure (inNewCoords Φ g)))
      Curved.turns y₀ := by
  have hd0 : DifferentiableAt ℝ Φ y₀ := patch_differentiableAt hW hΦ hy₀
  have hRt : R.transpose * R = 1 := mul_eq_one_comm.mp hR
  have hx₀ : Φ y₀ ∈ s := hΦs y₀ hy₀
  -- Near `y₀` the new size of the spheres is the old one, taken at `Φ y`.
  have hev : Curved.sizeSq (Curved.flatMeasure (Curved.tableMeasure (inNewCoords Φ g)))
      Curved.turns =ᶠ[𝓝 y₀] Curved.sizeSq (Curved.flatMeasure (Curved.tableMeasure g))
        (fun i ↦ Curved.fieldOf (ξ i)) ∘ Φ := by
    filter_upwards [hW.mem_nhds hy₀] with y hy
    exact sizeSq_inNewCoords (patch_differentiableAt hW hΦ hy) (hturn y hy) hRt
  -- So its slope is the old slope after the slope of the change of coordinates.
  have hf : DifferentiableAt ℝ (Curved.sizeSq (Curved.flatMeasure (Curved.tableMeasure g))
      (fun i ↦ Curved.fieldOf (ξ i))) (Φ y₀) :=
    differentiableAt_sizeSq (fun a b ↦ hg.differentiableAt hx₀ a b) fun i k ↦
      ((hξ.smooth i k).contDiffAt (hg.isOpen.mem_nhds hx₀)).differentiableAt (by simp)
  have hfd : fderiv ℝ (Curved.sizeSq (Curved.flatMeasure (Curved.tableMeasure (inNewCoords Φ g)))
      Curved.turns) y₀
      = (fderiv ℝ (Curved.sizeSq (Curved.flatMeasure (Curved.tableMeasure g))
        (fun i ↦ Curved.fieldOf (ξ i))) (Φ y₀)).comp (fderiv ℝ Φ y₀) := by
    rw [hev.fderiv_eq]
    exact fderiv_comp y₀ hf hd0
  -- The step that the usable distance gives at `Φ y₀`, in the words of tables.
  obtain ⟨n, hn, hnn⟩ : ∃ n : Coords 4,
      (∀ w : Coords 4, Curved.tableMeasure g (Φ y₀) n w
        = fderiv ℝ (Curved.sizeSq (Curved.flatMeasure (Curved.tableMeasure g))
          (fun i ↦ Curved.fieldOf (ξ i))) (Φ y₀) w)
        ∧ Curved.tableMeasure g (Φ y₀) n n ≠ 0 := by
    obtain ⟨n, hn, hnn⟩ := hu
    refine ⟨n, fun w ↦ ?_, hnn⟩
    have hw := hn w
    rw [Curved.mvfderiv_flat] at hw
    exact hw
  -- The change of coordinates loses no direction: a step at `y₀` that it sees as `n`.
  have hU : IsUnit (tab (jac Φ) y₀).det := isUnit_iff_ne_zero.mpr (hdet y₀ hy₀).2
  have hn' : fderiv ℝ Φ y₀ ((tab (jac Φ) y₀)⁻¹.mulVec n) = n := by
    rw [fderiv_eq_mulVec hd0, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU,
      Matrix.one_mulVec]
  refine ⟨(tab (jac Φ) y₀)⁻¹.mulVec n, fun w ↦ ?_, ?_⟩
  · rw [Curved.mvfderiv_flat, hfd]
    change Curved.tableMeasure (inNewCoords Φ g) y₀ ((tab (jac Φ) y₀)⁻¹.mulVec n) w
      = fderiv ℝ (Curved.sizeSq (Curved.flatMeasure (Curved.tableMeasure g))
        (fun i ↦ Curved.fieldOf (ξ i))) (Φ y₀) (fderiv ℝ Φ y₀ w)
    rw [tableMeasure_inNewCoords g hd0, hn', hn]
  · change Curved.tableMeasure (inNewCoords Φ g) y₀ ((tab (jac Φ) y₀)⁻¹.mulVec n)
      ((tab (jac Φ) y₀)⁻¹.mulVec n) ≠ 0
    rw [tableMeasure_inNewCoords g hd0, hn']
    exact hnn

end GravityInLean.Join
