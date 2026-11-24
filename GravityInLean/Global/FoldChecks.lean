/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.FreeFallChecks
public import GravityInLean.Rim.Radius

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# More checks of the foldings, and two facts about the sphere

Asked for by the second reader of `Goals/GlobalComplete.lean`:

* `kruskalFold_comm`: every fold commutes with the turns and mirrors of the sphere, so the three
  turning fields of Kruskal's space-time pass to every folding.
* `kruskalFolds_table`: the arithmetic behind the table of the four foldings. A fold keeps the
  direction of time exactly when the entry `L 0 0` is positive, and keeps the orientation exactly
  when `det L = -1` (the opposite-point map turns the sphere's orientation round).
* `IsKruskalOnto.not_const`: a map that does not move is never a length-keeping map from Kruskal's
  whole space-time. Lean gives every map a slope, zero where there is none; this shows that the
  definition is not fooled by that.
* `turnFixesPoint`, `sphereFreeInvolution`: the statements `TurnFixesPoint` and
  `SphereFreeInvolution` of `Goals/GlobalComplete.lean`, proved. A turn of the sphere leaves a
  point where it is, and the only symmetry of the sphere of order two that moves every point is
  the opposite-point map.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff

/-! ## The folds -/

/-- **Every fold commutes with the turns and mirrors of the sphere.** -/
theorem kruskalFold_comm (L : Matrix (Fin 2) (Fin 2) ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (p : Coords 5) : kruskalFold L (kruskalSym 1 R p) = kruskalSym 1 R (kruskalFold L p) := by
  funext i
  fin_cases i <;> simp [kruskalFold, kruskalSym] <;> ring

/-- **The arithmetic behind the table of the four foldings:** the entry `L 0 0` (positive exactly
when the fold keeps the direction of time) and the determinant of `L` (`-1` exactly when the fold,
together with the opposite-point map of the sphere, keeps the orientation). -/
theorem kruskalFolds_table :
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 ∧ (1 : Matrix (Fin 2) (Fin 2) ℝ).det = 1) ∧
    ((-1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = -1 ∧ (-1 : Matrix (Fin 2) (Fin 2) ℝ).det = 1) ∧
    ((Matrix.diagonal ![-1, 1] : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = -1 ∧
      (Matrix.diagonal ![-1, 1] : Matrix (Fin 2) (Fin 2) ℝ).det = -1) ∧
    ((Matrix.diagonal ![1, -1] : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 ∧
      (Matrix.diagonal ![1, -1] : Matrix (Fin 2) (Fin 2) ℝ).det = -1) := by
  refine ⟨⟨by simp, by simp⟩, ⟨by simp, ?_⟩, ⟨by simp, ?_⟩, ⟨by simp, ?_⟩⟩
  · simp [Matrix.det_fin_two]
  · simp
  · simp

/-- **A map that does not move is never a length-keeping map from Kruskal's whole space-time**,
for a positive mass. -/
theorem IsKruskalOnto.not_const {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M] {m : ℝ} (hm : 0 < m) (g : LengthMeasure 𝓘(ℝ, Coords 4) M)
    (q : M) : ¬ IsKruskalOnto m g (fun _ ↦ q) := by
  rintro ⟨hch, -⟩
  obtain ⟨-, hlen⟩ := hch 1 (by simp)
  set x : Coords 4 := ![0, 0, π / 2, 0] with hxdef
  have hx : x ∈ kruskalRegion := by
    refine ⟨by simp [hxdef], ?_⟩
    simp [hxdef]
  have h := hlen x hx (Pi.single 1 1) (Pi.single 1 1)
  have h0 : ∀ v : TangentSpace 𝓘(ℝ, Coords 4) x,
      mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) (fun y : Coords 4 ↦ q) x v = 0 := fun v ↦ by
    rw [mfderiv_const]
    rfl
  simp only [h0, map_zero] at h
  change tableMeasure (kruskalG m) x (Pi.single 1 1) (Pi.single 1 1) = 0 at h
  rw [kruskalG_apply] at h
  have hr := (kruskalRadiusSpec m hm (x 1 ^ 2 - x 0 ^ 2) (by simp [hxdef])).1
  have hA : 0 < kruskalA m (x 0) (x 1) := by
    unfold kruskalA
    positivity
  simp at h
  linarith

/-! ## Two facts about the sphere -/

/-- A vector that is not zero, scaled to length one. -/
theorem exists_unit_smul {w : Fin 3 → ℝ} (hw : w ≠ 0) :
    ∃ c : ℝ, dotProduct (c • w) (c • w) = 1 := by
  have hnn : 0 ≤ dotProduct w w := Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (w i)
  have hne : dotProduct w w ≠ 0 := fun h ↦ hw (dotProduct_self_eq_zero.mp h)
  have hpos : 0 < dotProduct w w := lt_of_le_of_ne hnn (Ne.symm hne)
  refine ⟨(√(dotProduct w w))⁻¹, ?_⟩
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_inv,
    Real.mul_self_sqrt hnn]
  exact inv_mul_cancel₀ hne

/-- **A turn of the sphere leaves a point where it is:** a turn (an orthogonal matrix with
determinant one) of ordinary space has a fixed point on the unit sphere, its axis. -/
theorem turnFixesPoint : TurnFixesPoint := by
  intro R hR hdet
  have hR' : R * R.transpose = 1 := mul_eq_one_comm.mp hR
  have h1 : R - 1 = R * (1 - R.transpose) := by rw [mul_sub, mul_one, hR']
  have h2 : (R - 1).det = -(R - 1).det := by
    calc (R - 1).det = R.det * (1 - R.transpose).det := by rw [h1, Matrix.det_mul]
      _ = (1 - R).det := by
        rw [hdet, one_mul, show (1 : Matrix (Fin 3) (Fin 3) ℝ) - R.transpose = (1 - R).transpose by
          rw [Matrix.transpose_sub, Matrix.transpose_one], Matrix.det_transpose]
      _ = (-(R - 1)).det := by rw [neg_sub]
      _ = -(R - 1).det := by rw [Matrix.det_neg, Fintype.card_fin]; ring
  have h3 : (R - 1).det = 0 := by linarith
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h3
  have hRv : R.mulVec v = v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv
  obtain ⟨c, hc⟩ := exists_unit_smul hv0
  exact ⟨c • v, hc, by rw [Matrix.mulVec_smul, hRv]⟩

/-- **The only symmetry of the sphere of order two that moves every point is the opposite-point
map.** (Neither "orthogonal" nor more is needed: for any matrix `R` with `R R = 1`, `(R + 1) v` is
left where it is by `R`.) -/
theorem sphereFreeInvolution : SphereFreeInvolution := by
  intro R _ hR2 hfree
  have key : ∀ v : Fin 3 → ℝ, (R + 1).mulVec v = 0 := by
    intro v
    by_contra hne
    have hRw : R.mulVec ((R + 1).mulVec v) = (R + 1).mulVec v := by
      rw [Matrix.mulVec_mulVec, mul_add, hR2, mul_one, add_comm]
    obtain ⟨c, hc⟩ := exists_unit_smul hne
    exact hfree _ hc (by rw [Matrix.mulVec_smul, hRw])
  have hsum : R + 1 = 0 := by
    ext i j
    have := congrFun (key (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  exact eq_neg_of_add_eq_zero_left hsum

end GravityInLean.Curved
