/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.Turns
public import GravityInLean.Turns.Basic
public import GravityInLean.Turns.Rotation
public import GravityInLean.Turns.RotateBracket
public import GravityInLean.Turns.Kernel
public import GravityInLean.Turns.BracketFderiv
public import GravityInLean.Turns.Surface
public import GravityInLean.Turns.Chart
public import GravityInLean.Turns.ChartSmooth
public import GravityInLean.Turns.ChartSlopes
public import GravityInLean.Turns.Relations
public import GravityInLean.Turns.TurnAlgebra

import Mathlib.Tactic

/-!
# Coordinates that fit the turns exist

Board item `task:turns-goal`. This proves statement 2 of `Goals/Turns.lean` from the lemmas of
this folder.

The route. At the point `p` the three fields span two directions, so a unit mix of them is zero
at `p` (`exists_unit_kernel`); a rotation `R` with that mix as its middle row
(`exists_rotation_row`) gives rotated fields `η = rotated R ξ` that still combine the way turns
do (`likeTurns_rotate`), with `η 1 p = 0`. The points near `p` where `η 1` is zero contain a
surface `σ` through `p` (`exists_restSurface`). The new coordinates are `chart σ χ ψ`, with the
flows `χ` of `η 0` and `ψ` of `η 2` (`exists_isLocalFlow`, from `smoothFlow`). They obey two
relations (`chart_relations`), from which the three equations of the standard turns follow by a
computation (`turns_of_relations`). The table of slopes has an inverse at the start
(the four columns are the two directions of `σ`, then `η 0 p`, `η 2 p`), hence nearby
(`continuousOn_det_jac`).
-/

@[expose] public section

namespace GravityInLean

open Set Metric Topology Real Turns

open scoped ContDiff

namespace Turns

/-- The three fields after a fixed rotation `R` among themselves, as maps from points to
arrows. -/
noncomputable def rotated (R : Matrix (Fin 3) (Fin 3) ℝ) (ξ : Fin 3 → Fin 4 → Coords 4 → ℝ)
    (i : Fin 3) : Coords 4 → Coords 4 :=
  fun y ↦ ∑ j, R i j • vec (ξ j) y

/-- The parts of a rotated field, as the goal writes them. -/
theorem rotated_apply (R : Matrix (Fin 3) (Fin 3) ℝ) (ξ : Fin 3 → Fin 4 → Coords 4 → ℝ)
    (i : Fin 3) (y : Coords 4) (α : Fin 4) : rotated R ξ i y α = ∑ j, R i j * ξ j α y := by
  simp [rotated, vec, Finset.sum_apply]

/-- The rotated fields are smooth where the fields are. -/
theorem contDiffOn_rotated {ξ : Fin 3 → Fin 4 → Coords 4 → ℝ} {s : Set (Coords 4)}
    (h : ∀ i k, ContDiffOn ℝ ∞ (ξ i k) s) (R : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (rotated R ξ i) s := by
  unfold rotated
  exact ContDiffOn.sum fun j _ ↦ (contDiffOn_vec (h j)).const_smul (R i j)

/-- The rotated fields combine the way turns do. -/
theorem rotated_likeTurns {g : Fin 4 → Fin 4 → Coords 4 → ℝ}
    {ξ : Fin 3 → Fin 4 → Coords 4 → ℝ} {s : Set (Coords 4)} (hs : IsOpen s)
    (hT : TurnsOn g ξ s) {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R * R.transpose = 1)
    (hdet : R.det = 1) {x : Coords 4} (hx : x ∈ s) :
    lieB (rotated R ξ 0) (rotated R ξ 1) x = rotated R ξ 2 x ∧
      lieB (rotated R ξ 1) (rotated R ξ 2) x = rotated R ξ 0 x ∧
      lieB (rotated R ξ 2) (rotated R ξ 0) x = rotated R ξ 1 x := by
  have hd : ∀ i k, DifferentiableAt ℝ (ξ i k) x := fun i k ↦
    ((hT.smooth i k).contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)
  have hXd : ∀ i, DifferentiableAt ℝ (vec (ξ i)) x := fun i ↦
    ((contDiffOn_vec (hT.smooth i)).contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)
  have hl := hT.likeTurns x hx
  have e01 : lieB (vec (ξ 0)) (vec (ξ 1)) x = vec (ξ 2) x := funext fun k ↦ by
    rw [← bracketOf_eq_lieB (hd 0) (hd 1) k]; exact (hl k).1
  have e12 : lieB (vec (ξ 1)) (vec (ξ 2)) x = vec (ξ 0) x := funext fun k ↦ by
    rw [← bracketOf_eq_lieB (hd 1) (hd 2) k]; exact (hl k).2.1
  have e20 : lieB (vec (ξ 2)) (vec (ξ 0)) x = vec (ξ 1) x := funext fun k ↦ by
    rw [← bracketOf_eq_lieB (hd 2) (hd 0) k]; exact (hl k).2.2
  exact likeTurns_rotate (fun j ↦ vec (ξ j)) R hR hdet x hXd e01 e12 e20

/-- The rotated fields span two directions at every point, as the fields do. -/
theorem rotated_finrank {g : Fin 4 → Fin 4 → Coords 4 → ℝ}
    {ξ : Fin 3 → Fin 4 → Coords 4 → ℝ} {s : Set (Coords 4)} (hT : TurnsOn g ξ s)
    {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R * R.transpose = 1) {x : Coords 4} (hx : x ∈ s) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range fun i ↦ rotated R ξ i x)) = 2 := by
  have h := span_rotate R hR (fun j ↦ vec (ξ j) x)
  have e : (fun i ↦ rotated R ξ i x) = fun i ↦ ∑ j, R i j • vec (ξ j) x := rfl
  rw [e, h]
  exact hT.surfaces x hx

end Turns

/-- **Coordinates that fit the turns exist.** Around every point of a region with three fields
that turn, there are new coordinates in which the fields, after one fixed rotation among
themselves, are exactly the three standard turns. -/
theorem turnsCoordinates : TurnsCoordinatesStatement := by
  intro g ginv ξ s hg hT p hp
  have hs : IsOpen s := hg.isOpen
  obtain ⟨n, hn, hker⟩ := exists_unit_kernel (fun j ↦ vec (ξ j) p) (hT.surfaces p hp)
  obtain ⟨R, hR, hdet, hrow⟩ := exists_rotation_row n hn
  have hηs : ∀ i, ContDiffOn ℝ ∞ (rotated R ξ i) s := contDiffOn_rotated hT.smooth R
  have hbr := fun x (hx : x ∈ s) ↦ rotated_likeTurns hs hT hR hdet hx
  have h1p : rotated R ξ 1 p = 0 := by
    have e : rotated R ξ 1 p = ∑ j, n j • vec (ξ j) p := by simp [rotated, hrow]
    rw [e]
    exact hker
  obtain ⟨δ, σ, hδ, hσ, hσ0, hσs, hσdet⟩ := exists_restSurface (rotated R ξ) s hs p hp hηs
    (fun x hx ↦ rotated_finrank hT hR hx) h1p (hbr p hp).1 (hbr p hp).2.1
  obtain ⟨ε₀, χ, hχ⟩ := exists_isLocalFlow hs (hηs 0) hp
  obtain ⟨ε₂, ψ, hψ⟩ := exists_isLocalFlow hs (hηs 2) hp
  have hD : ChartData (rotated R ξ 0) (rotated R ξ 2) s p δ ε₀ ε₂ σ χ ψ :=
    ⟨hδ, hσ, hσ0, hχ, hψ⟩
  have hDo := isOpen_chartDomain hD
  have hΦs := contDiffOn_chart hD
  have hdiff : ∀ y ∈ chartDomain σ χ p δ ε₀ ε₂, DifferentiableAt ℝ (chart σ χ ψ) y :=
    fun y hy ↦ (hΦs.contDiffAt (hDo.mem_nhds hy)).differentiableAt (by simp)
  have hrel := fun y (hy : y ∈ chartDomain σ χ p δ ε₀ ε₂) ↦
    chart_relations hs hηs (fun x hx ↦ (hbr x hx).1) (fun x hx ↦ (hbr x hx).2.1)
      (fun x hx ↦ (hbr x hx).2.2) hD (fun u hu ↦ (hσs u hu).2) hy
  have hst := chartStart_mem hD
  have hstart : (tab (jac (chart σ χ ψ)) chartStart).det ≠ 0 := by
    have e : tab (jac (chart σ χ ψ)) chartStart = Matrix.of fun α μ : Fin 4 ↦
        (![fderiv ℝ σ 0 (1, 0), fderiv ℝ σ 0 (0, 1), rotated R ξ 0 p, rotated R ξ 2 p] μ) α := by
      have h2 := (hrel chartStart hst).1
      have h3 := fderiv_chart_three hD hst
      rw [chart_chartStart hD] at h2 h3
      have e3 : chartStart 3 = 0 := by simp [chartStart]
      rw [e3] at h2
      simp only [Real.cos_zero, Real.sin_zero, one_smul, zero_smul, sub_zero] at h2
      ext α μ
      simp only [tab, Matrix.of_apply]
      rw [jac_eq_fderiv (hdiff _ hst)]
      fin_cases μ
      · exact congrFun (fderiv_chart_zero_start hD) α
      · exact congrFun (fderiv_chart_one_start hD) α
      · exact congrFun h2 α
      · exact congrFun h3 α
    rw [e]
    exact hσdet
  have hcont := continuousOn_det_jac hDo hΦs
  refine ⟨chart σ χ ψ, R,
    chartDomain σ χ p δ ε₀ ε₂ ∩ (fun y ↦ (tab (jac (chart σ χ ψ)) y).det) ⁻¹' {0}ᶜ,
    chartStart, hcont.isOpen_inter_preimage hDo isOpen_compl_singleton, ⟨hst, hstart⟩,
    chart_chartStart hD, by simp [chartStart], by simp [chartStart],
    fun y hy ↦ chart_mem hD hy.1, hΦs.mono inter_subset_left, hR, hdet,
    fun y hy ↦ ⟨hy.1.2.2.2.2.2, hy.2⟩, ?_⟩
  intro y hy i α
  obtain ⟨hrel2, hrel0⟩ := hrel y hy.1
  have key := turns_of_relations (hdiff y hy.1) (fderiv_chart_three hD hy.1) hrel2 hrel0 α
  refine Eq.trans ?_ (rotated_apply R ξ i (chart σ χ ψ y) α)
  fin_cases i
  · exact key.1
  · exact key.2.1
  · exact key.2.2

end GravityInLean
