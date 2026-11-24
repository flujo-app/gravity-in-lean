/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Curved.Tables
public import GravityInLean.Goals.Turns
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# From the curved-space words on coordinate space to tables of functions

Board item `task:join-flat-table`. On flat coordinate space a length measure in the sense of
`Curved/Basic.lean` is a two-slot function `G x` at every point, and a field of arrows is a
function from points to arrows. The rest of the project computes with tables of functions. This
file reads the tables off and shows that every word carries over:

* `tableOf G`, `partsOf Ξ`: the table of a two-slot function, and the parts of fields of arrows;
* `tableMeasure_tableOf`, `fieldOf_partsOf`: reading the table and then building the length
  measure from it gives back what one started from, and so for the fields;
* `isRegularTableOn_tableOf`: the table of a length measure is a good table, with the inverse
  taken point by point;
* `turnsOn_of_isRoundOn`: "looks the same from every side" gives three fields that turn;
* `isRicciFlatAt_of_isEmptyOn`: "empty" gives the coordinate formula for empty;
* `exists_flatTransport_of_isLengthMeasureOn`: a length measure on coordinate space has a
  connection of the form "the plain slope plus a correction", and the correction can be
  differentiated.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Join

open GravityInLean.Curved

open scoped Manifold ContDiff Topology

variable {n : ℕ}

/-! ## Reading off the table and the parts -/

/-- The table of a two-slot function that changes from point to point: entry `(a, b)` at `x` is
the function applied to the basic steps `a` and `b`. -/
noncomputable def tableOf (G : Coords n → Coords n →L[ℝ] Coords n →L[ℝ] ℝ) (a b : Fin n)
    (x : Coords n) : ℝ :=
  G x (Pi.single a 1) (Pi.single b 1)

/-- The parts of a family of fields of arrows on coordinate space: `partsOf Ξ i k x` is part `k`
of the arrow that the field `Ξ i` has at `x`. -/
noncomputable def partsOf {ι : Type*} (Ξ : ι → Arrows 𝓘(ℝ, Coords n) (Coords n)) (i : ι)
    (k : Fin n)
    (x : Coords n) : ℝ :=
  plain (Ξ i) x k

/-- A two-slot function is given by its table: `G x v w = ∑ a b, T a b x * v a * w b`. -/
theorem apply_eq_sum_tableOf (G : Coords n → Coords n →L[ℝ] Coords n →L[ℝ] ℝ) (x v w : Coords n) :
    G x v w = ∑ a, ∑ b, tableOf G a b x * v a * w b := by
  rw [← formOf_apply]
  symm
  refine eq_of_basis₂ (Pi.basisFun ℝ (Fin n)) (formOf fun a b ↦ tableOf G a b x)
    (fun v w ↦ G x v w) ?_ ?_ ?_ v w
  · intro z
    exact ⟨fun a b ↦ by simp, fun c a ↦ by simp⟩
  · intro y
    exact ⟨fun a b ↦ by simp, fun c a ↦ by simp⟩
  · intro i j
    simp only [Pi.basisFun_apply]
    rw [formOf_single_single]
    rfl

/-- Reading the table off a two-slot function and building the length measure of that table gives
the two-slot function back. -/
theorem tableMeasure_tableOf (G : Coords n → Coords n →L[ℝ] Coords n →L[ℝ] ℝ) :
    tableMeasure (tableOf G) = G := by
  funext x
  refine ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext fun w ↦ ?_
  rw [apply_eq_sum_tableOf G x v w, tableMeasure, formOf_apply]

/-- The same, as length measures on flat coordinate space. -/
theorem flatMeasure_tableOf (G : Coords n → Coords n →L[ℝ] Coords n →L[ℝ] ℝ) :
    flatMeasure (tableMeasure (tableOf G)) = flatMeasure G := by
  rw [tableMeasure_tableOf]

/-- Reading the parts off a field of arrows and building the field with these parts gives the
field back. -/
theorem fieldOf_partsOf {ι : Type*} (Ξ : ι → Arrows 𝓘(ℝ, Coords n) (Coords n)) (i : ι) :
    fieldOf (partsOf Ξ i) = Ξ i := rfl

/-- The same, for the whole family of fields. -/
theorem fieldOf_partsOf_fun {ι : Type*} (Ξ : ι → Arrows 𝓘(ℝ, Coords n) (Coords n)) :
    (fun i ↦ fieldOf (partsOf Ξ i)) = Ξ := rfl

/-! ## The table of a length measure is a good table -/

section Regular

variable {G : Coords n → Coords n →L[ℝ] Coords n →L[ℝ] ℝ} {s' : Set (Coords n)}

/-- The entries of the table of a smooth length measure are smooth. -/
theorem contDiffOn_tableOf (hG : IsLengthMeasureOn (flatMeasure G) s') (a b : Fin n) :
    ContDiffOn ℝ ∞ (tableOf G a b) s' := by
  have h : ContDiffOn ℝ ∞ G s' := isSmoothOn_flat_iff.mp hG.smooth
  exact (h.clm_apply contDiffOn_const).clm_apply contDiffOn_const

/-- The table of a length measure is symmetric. -/
theorem tableOf_symm (hG : IsLengthMeasureOn (flatMeasure G) s') {x : Coords n} (hx : x ∈ s')
    (a b : Fin n) : tableOf G a b x = tableOf G b a x :=
  hG.symm x hx (Pi.single a 1 : Coords n) (Pi.single b 1 : Coords n)

/-- The table of a length measure can be inverted: its determinant is not zero. -/
theorem det_tab_tableOf_ne_zero (hG : IsLengthMeasureOn (flatMeasure G) s') {x : Coords n}
    (hx : x ∈ s') : (tab (tableOf G) x).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hmul⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  apply hv
  refine hG.nondegenerate x hx v fun w ↦ ?_
  change G x v w = 0
  rw [apply_eq_sum_tableOf G x v w, Finset.sum_comm]
  refine Finset.sum_eq_zero fun b _ ↦ ?_
  have hb : ∑ a, v a * tableOf G a b x = 0 := by
    have := congrFun hmul b
    simpa [Matrix.vecMul, dotProduct, tab] using this
  calc ∑ a, tableOf G a b x * v a * w b = (∑ a, v a * tableOf G a b x) * w b := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ ↦ by ring
    _ = 0 := by rw [hb, zero_mul]

/-- **The table of a length measure is a good table,** with the inverse taken point by point. -/
theorem isRegularTableOn_tableOf (hs : IsOpen s') (hG : IsLengthMeasureOn (flatMeasure G) s') :
    IsRegularTableOn (tableOf G) (invT (tableOf G)) s' where
  isOpen := hs
  smooth := contDiffOn_tableOf hG
  symm := fun _ hx a b ↦ tableOf_symm hG hx a b
  inverse := fun x hx a c ↦ by
    have h1 : tab (tableOf G) x * (tab (tableOf G) x)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (det_tab_tableOf_ne_zero hG hx))
    have h2 := congrFun (congrFun h1 a) c
    simpa [Matrix.mul_apply, tab, invT, Matrix.one_apply] using h2

/-- **A length measure on coordinate space has a connection of the form "the plain slope plus a
correction",** and the correction can be differentiated at every point of the region. The
correction is the textbooks' formula for the connection, for the table of the length measure. -/
theorem exists_flatTransport_of_isLengthMeasureOn (hs : IsOpen s')
    (hG : IsLengthMeasureOn (flatMeasure G) s') :
    ∃ A : Coords n → Coords n →L[ℝ] Coords n →L[ℝ] Coords n,
      IsConnectionOf (flatMeasure G) (flatTransport A) s' ∧ ∀ x ∈ s', DifferentiableAt ℝ A x := by
  have h := isRegularTableOn_tableOf hs hG
  refine ⟨tableCorr (christoffel (tableOf G) (invT (tableOf G))), ?_, fun x hx ↦ ?_⟩
  · have h1 := h.isConnectionOf
    rwa [tableMeasure_tableOf] at h1
  · exact differentiableAt_tableCorr fun a b c ↦ h.differentiableAt_christoffel hx a b c

/-- **"Empty" in the sense of curved spaces gives the coordinate formula for empty,** for the
table of the length measure. -/
theorem isRicciFlatAt_of_isEmptyOn (hs : IsOpen s') (hG : IsLengthMeasureOn (flatMeasure G) s')
    (he : Curved.IsEmptyOn (flatMeasure G) s') :
    ∀ x ∈ s', IsRicciFlatAt (tableOf G) (invT (tableOf G)) x := by
  have h := isRegularTableOn_tableOf hs hG
  have he' : Curved.IsEmptyOn (flatMeasure (tableMeasure (tableOf G))) s' := by
    rw [tableMeasure_tableOf]
    exact he
  exact h.isEmptyOn_iff.mp he'

end Regular

/-! ## Three fields that turn -/

section Turns

variable {G : Coords 4 → Coords 4 →L[ℝ] Coords 4 →L[ℝ] ℝ}
  {Ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) (Coords 4)} {s' : Set (Coords 4)}

/-- The parts of a smooth field of arrows are smooth. -/
theorem contDiffOn_partsOf (hΞ : ∀ i, ContDiffOn ℝ ∞ (plain (Ξ i)) s') (i : Fin 3) (k : Fin 4) :
    ContDiffOn ℝ ∞ (partsOf Ξ i k) s' :=
  contDiffOn_pi.mp (hΞ i) k

/-- **"Looks the same from every side" gives three fields that turn.** If the length measure `G`
on coordinate space looks the same from every side with the three fields `Ξ`, then the table of
`G` and the parts of the three fields meet `TurnsOn`. -/
theorem turnsOn_of_isRoundOn (hG : IsLengthMeasureOn (flatMeasure G) s')
    (hr : IsRoundOn (flatMeasure G) Ξ s') : TurnsOn (tableOf G) (partsOf Ξ) s' := by
  have hreg := isRegularTableOn_tableOf hr.isOpen hG
  have hsm : ∀ i k, ContDiffOn ℝ ∞ (partsOf Ξ i k) s' :=
    contDiffOn_partsOf fun i ↦ contMDiffOn_arrows_iff.mp (hr.smooth i)
  have hd : ∀ x ∈ s', ∀ i k, DifferentiableAt ℝ (partsOf Ξ i k) x := fun x hx i k ↦
    ((hsm i k).contDiffAt (hr.isOpen.mem_nhds hx)).differentiableAt (by simp)
  refine ⟨hsm, fun i x hx ↦ ?_, fun x hx k ↦ ?_, fun x hx ↦ ?_, fun x hx v hv hne ↦ ?_⟩
  · have h1 : Curved.LeavesUnchangedAt (flatMeasure (tableMeasure (tableOf G)))
        (fieldOf (partsOf Ξ i)) x := by
      rw [tableMeasure_tableOf]
      exact hr.unchanged i x hx
    exact (leavesUnchangedAt_table_iff (fun a b ↦ hreg.differentiableAt hx a b)
      (hd x hx i)).mp h1
  · have key : ∀ i j l : Fin 3,
        VectorField.mlieBracket 𝓘(ℝ, Coords 4) (Ξ i) (Ξ j) x = Ξ l x →
        bracketOf (partsOf Ξ i) (partsOf Ξ j) k x = partsOf Ξ l k x := by
      intro i j l h
      rw [← mlieBracket_fieldOf_eq (hd x hx i) (hd x hx j) k]
      exact congrArg (fun v : Coords 4 ↦ v k) h
    obtain ⟨h1, h2, h3⟩ := hr.likeTurns x hx
    exact ⟨key 0 1 2 h1, key 1 2 0 h2, key 2 0 1 h3⟩
  · exact hr.surfaces x hx
  · rw [← apply_eq_sum_tableOf G x v v]
    exact hr.positive x hx v hv hne

end Turns

end GravityInLean.Join
