/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Curved.Basic
public import GravityInLean.Turns.RotateBracket
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Tools for "looks the same from every side" on a curved space

"The space-time looks the same from every side on the region `s`, by the three fields `ξ`"
(`IsRoundOn g ξ s` of `Curved/Basic.lean`) is a statement about each point of the region and
the fields near it. This file has three tools that use this, on any curved space:

* `IsRoundOn.mix`: the three fields may be mixed by a fixed rotation `A` (three by three numbers
  with `A * Aᵀ = 1` and `det A = 1`): the three new fields `mixFields A ξ i = ∑ j, A i j • ξ j`
  do the same job. Behind it: `LeavesUnchangedAt.add` and `LeavesUnchangedAt.const_smul` (a sum
  and a fixed multiple of fields that leave the length measure unchanged leave it unchanged)
  and `mlieBracket_mix` (the bracket of two mixes).
* `IsRoundOn.congr`: only the values of the fields on the region matter.
* `isRoundOn_of_local`: it is enough to know it near every point of the region.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open VectorField Matrix

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : LengthMeasure I M} {s : Set M}

/-! ## Sums and fixed multiples of fields that leave the length measure unchanged -/

/-- **The sum of two fields that leave the length measure unchanged at a point leaves it
unchanged there.** -/
theorem LeavesUnchangedAt.add {ξ η : Arrows I M} {x : M} (hξ : LeavesUnchangedAt g ξ x)
    (hη : LeavesUnchangedAt g η x) : LeavesUnchangedAt g (ξ + η) x := by
  refine ⟨mdifferentiableAt_add_section hξ.1 hη.1, fun X Y hX hY ↦ ?_⟩
  have h1 := hξ.2 X Y hX hY
  have h2 := hη.2 X Y hX hY
  have hval : (ξ + η) x = ξ x + η x := rfl
  have e1 : d% (fun y ↦ g y (X y) (Y y)) x (ξ x + η x)
      = d% (fun y ↦ g y (X y) (Y y)) x (ξ x) + d% (fun y ↦ g y (X y) (Y y)) x (η x) :=
    map_add _ _ _
  have add1 : ∀ a b c : TangentSpace I x, g x (a + b) c = g x a c + g x b c := fun a b c ↦ by
    rw [map_add]
    rfl
  have add2 : ∀ a b c : TangentSpace I x, g x a (b + c) = g x a b + g x a c :=
    fun a b c ↦ map_add _ _ _
  rw [hval, e1, mlieBracket_add_left hξ.1 hη.1, mlieBracket_add_left hξ.1 hη.1, add1, add2,
    h1, h2]
  ring

/-- **A fixed multiple of a field that leaves the length measure unchanged at a point leaves it
unchanged there.** -/
theorem LeavesUnchangedAt.const_smul {ξ : Arrows I M} {x : M} (hξ : LeavesUnchangedAt g ξ x)
    (c : ℝ) : LeavesUnchangedAt g (c • ξ) x := by
  refine ⟨hξ.1.smul_const_section, fun X Y hX hY ↦ ?_⟩
  have h1 := hξ.2 X Y hX hY
  have hval : (c • ξ) x = c • ξ x := rfl
  have e1 : d% (fun y ↦ g y (X y) (Y y)) x (c • ξ x)
      = c * d% (fun y ↦ g y (X y) (Y y)) x (ξ x) := by
    rw [map_smul]
    rfl
  have smul1 : ∀ a b : TangentSpace I x, g x (c • a) b = c * g x a b := fun a b ↦ by
    rw [map_smul]
    rfl
  have smul2 : ∀ a b : TangentSpace I x, g x a (c • b) = c * g x a b := fun a b ↦ by
    rw [map_smul]
    rfl
  rw [hval, e1, mlieBracket_const_smul_left hξ.1, mlieBracket_const_smul_left hξ.1, smul1, smul2,
    h1]
  ring

/-- **Only the field near the point matters.** A field that agrees near `x` with a field that
leaves the length measure unchanged at `x` leaves it unchanged at `x`. -/
theorem LeavesUnchangedAt.congr {ξ η : Arrows I M} {x : M} (h : LeavesUnchangedAt g ξ x)
    (he : η =ᶠ[𝓝 x] ξ) : LeavesUnchangedAt g η x := by
  have hx : η x = ξ x := he.self_of_nhds
  have hT : (T% η) =ᶠ[𝓝 x] (T% ξ) :=
    he.mono fun y hy ↦ congrArg (fun v : TangentSpace I y ↦ (⟨y, v⟩ : TangentBundle I M)) hy
  refine ⟨h.1.congr_of_eventuallyEq hT, fun X Y hX hY ↦ ?_⟩
  have b : ∀ Z : Arrows I M, mlieBracket I η Z x = mlieBracket I ξ Z x := fun Z ↦
    Filter.EventuallyEq.mlieBracket_vectorField_eq he Filter.EventuallyEq.rfl
  rw [hx, b X, b Y]
  exact h.2 X Y hX hY

/-! ## Mixing three fields by fixed numbers -/

/-- **Three fields mixed by a fixed table of numbers:** the field number `i` of the mix is
`A i 0 • ξ 0 + A i 1 • ξ 1 + A i 2 • ξ 2`. -/
def mixFields (A : Matrix (Fin 3) (Fin 3) ℝ) (ξ : Fin 3 → Arrows I M) (i : Fin 3) : Arrows I M :=
  A i 0 • ξ 0 + A i 1 • ξ 1 + A i 2 • ξ 2

/-- The mix at a point, written out. -/
theorem mixFields_apply (A : Matrix (Fin 3) (Fin 3) ℝ) (ξ : Fin 3 → Arrows I M) (i : Fin 3)
    (x : M) : mixFields A ξ i x = A i 0 • ξ 0 x + A i 1 • ξ 1 x + A i 2 • ξ 2 x := rfl

/-- **The bracket of two mixes of three fields that combine like turns:** the mix whose three
numbers are the cross product of the numbers of the two mixes. -/
theorem mlieBracket_mix {ξ : Fin 3 → Arrows I M} {x : M} (hd : ∀ i, MDiffAt (T% (ξ i)) x)
    (u v : Fin 3 → ℝ) (h01 : mlieBracket I (ξ 0) (ξ 1) x = ξ 2 x)
    (h12 : mlieBracket I (ξ 1) (ξ 2) x = ξ 0 x) (h20 : mlieBracket I (ξ 2) (ξ 0) x = ξ 1 x) :
    mlieBracket I (u 0 • ξ 0 + u 1 • ξ 1 + u 2 • ξ 2) (v 0 • ξ 0 + v 1 • ξ 1 + v 2 • ξ 2) x
      = (u 1 * v 2 - u 2 * v 1) • ξ 0 x + (u 2 * v 0 - u 0 * v 2) • ξ 1 x
        + (u 0 * v 1 - u 1 * v 0) • ξ 2 x := by
  have hs : ∀ (c : ℝ) (i : Fin 3), MDiffAt (T% (c • ξ i)) x :=
    fun c i ↦ (hd i).smul_const_section
  have hs2 : ∀ (c c' : ℝ) (i j : Fin 3), MDiffAt (T% (c • ξ i + c' • ξ j)) x :=
    fun c c' i j ↦ mdifferentiableAt_add_section (hs c i) (hs c' j)
  have left : ∀ W : Arrows I M, mlieBracket I (u 0 • ξ 0 + u 1 • ξ 1 + u 2 • ξ 2) W x
      = u 0 • mlieBracket I (ξ 0) W x + u 1 • mlieBracket I (ξ 1) W x
        + u 2 • mlieBracket I (ξ 2) W x := fun W ↦ by
    rw [mlieBracket_add_left (hs2 _ _ _ _) (hs _ _), mlieBracket_add_left (hs _ _) (hs _ _),
      mlieBracket_const_smul_left (hd 0), mlieBracket_const_smul_left (hd 1),
      mlieBracket_const_smul_left (hd 2)]
  have right : ∀ V : Arrows I M, mlieBracket I V (v 0 • ξ 0 + v 1 • ξ 1 + v 2 • ξ 2) x
      = v 0 • mlieBracket I V (ξ 0) x + v 1 • mlieBracket I V (ξ 1) x
        + v 2 • mlieBracket I V (ξ 2) x := fun V ↦ by
    rw [mlieBracket_add_right (hs2 _ _ _ _) (hs _ _), mlieBracket_add_right (hs _ _) (hs _ _),
      mlieBracket_const_smul_right (hd 0), mlieBracket_const_smul_right (hd 1),
      mlieBracket_const_smul_right (hd 2)]
  have z : ∀ i, mlieBracket I (ξ i) (ξ i) x = 0 := fun i ↦ by
    rw [mlieBracket_self]
    rfl
  have h10 : mlieBracket I (ξ 1) (ξ 0) x = -ξ 2 x := by rw [mlieBracket_swap_apply, h01]
  have h21 : mlieBracket I (ξ 2) (ξ 1) x = -ξ 0 x := by rw [mlieBracket_swap_apply, h12]
  have h02 : mlieBracket I (ξ 0) (ξ 2) x = -ξ 1 x := by rw [mlieBracket_swap_apply, h20]
  rw [left, right, right, right, z 0, z 1, z 2, h01, h12, h20, h10, h21, h02]
  module

/-- The steps that three fields span at a point are the steps that a mix of them by a table
`A` with `A * Aᵀ = 1` spans there. -/
theorem span_mixFields {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A * A.transpose = 1)
    (ξ : Fin 3 → Arrows I M) (x : M) :
    Submodule.span ℝ (Set.range fun i ↦ mixFields A ξ i x)
      = Submodule.span ℝ (Set.range fun i ↦ ξ i x) := by
  have hA' : A.transpose * A = 1 := mul_eq_one_comm.mp hA
  have hk : ∀ j k : Fin 3, A 0 j * A 0 k + A 1 j * A 1 k + A 2 j * A 2 k
      = (1 : Matrix (Fin 3) (Fin 3) ℝ) j k := fun j k ↦ by
    rw [← hA', Matrix.mul_apply, Fin.sum_univ_three]
    rfl
  have hmem : ∀ j, ξ j x ∈ Submodule.span ℝ (Set.range fun i ↦ ξ i x) :=
    fun j ↦ Submodule.subset_span ⟨j, rfl⟩
  have hmem' : ∀ i, mixFields A ξ i x ∈ Submodule.span ℝ (Set.range fun i ↦ mixFields A ξ i x) :=
    fun i ↦ Submodule.subset_span ⟨i, rfl⟩
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, rfl⟩
    exact add_mem (add_mem (Submodule.smul_mem _ _ (hmem 0)) (Submodule.smul_mem _ _ (hmem 1)))
      (Submodule.smul_mem _ _ (hmem 2))
  · rintro _ ⟨j, rfl⟩
    have e : ξ j x = A 0 j • mixFields A ξ 0 x + A 1 j • mixFields A ξ 1 x
        + A 2 j • mixFields A ξ 2 x := by
      have e1 : A 0 j • mixFields A ξ 0 x + A 1 j • mixFields A ξ 1 x + A 2 j • mixFields A ξ 2 x
          = (A 0 j * A 0 0 + A 1 j * A 1 0 + A 2 j * A 2 0) • ξ 0 x
            + (A 0 j * A 0 1 + A 1 j * A 1 1 + A 2 j * A 2 1) • ξ 1 x
            + (A 0 j * A 0 2 + A 1 j * A 1 2 + A 2 j * A 2 2) • ξ 2 x := by
        rw [mixFields_apply, mixFields_apply, mixFields_apply]
        module
      rw [e1, hk j 0, hk j 1, hk j 2]
      fin_cases j <;> simp
    change ξ j x ∈ Submodule.span ℝ (Set.range fun i ↦ mixFields A ξ i x)
    rw [e]
    exact add_mem (add_mem (Submodule.smul_mem _ _ (hmem' 0)) (Submodule.smul_mem _ _ (hmem' 1)))
      (Submodule.smul_mem _ _ (hmem' 2))

/-- **Three fields that show that the space-time looks the same from every side may be mixed by
a fixed rotation.** If `g` looks the same from every side on `s` by the three fields `ξ`, and
`A` is a rotation (`A * Aᵀ = 1`, `det A = 1`), then it does so by the three mixed fields
`mixFields A ξ` as well. -/
theorem IsRoundOn.mix {ξ : Fin 3 → Arrows I M} (h : IsRoundOn g ξ s)
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A * A.transpose = 1) (hdet : A.det = 1) :
    IsRoundOn g (mixFields A ξ) s where
  isOpen := h.isOpen
  smooth := fun i ↦ by
    have h1 : CMDiff[s] ∞ (T% (A i 0 • ξ 0 + A i 1 • ξ 1 + A i 2 • ξ 2)) :=
      (((h.smooth 0).const_smul_section).add_section ((h.smooth 1).const_smul_section)).add_section
        ((h.smooth 2).const_smul_section)
    exact h1
  unchanged := fun i x hx ↦
    (((h.unchanged 0 x hx).const_smul (A i 0)).add ((h.unchanged 1 x hx).const_smul (A i 1))).add
      ((h.unchanged 2 x hx).const_smul (A i 2))
  likeTurns := fun x hx ↦ by
    obtain ⟨h01, h12, h20⟩ := h.likeTurns x hx
    obtain ⟨c01, c12, c20⟩ := Turns.rotation_rows_cross A hA hdet
    have hd := fun i ↦ (h.unchanged i x hx).1
    have key : ∀ a b c : Fin 3, crossProduct (A a) (A b) = A c →
        mlieBracket I (mixFields A ξ a) (mixFields A ξ b) x = mixFields A ξ c x := by
      intro a b c hc
      have c0 : A c 0 = A a 1 * A b 2 - A a 2 * A b 1 := by
        rw [← hc, cross_apply]
        rfl
      have c1 : A c 1 = A a 2 * A b 0 - A a 0 * A b 2 := by
        rw [← hc, cross_apply]
        rfl
      have c2 : A c 2 = A a 0 * A b 1 - A a 1 * A b 0 := by
        rw [← hc, cross_apply]
        rfl
      rw [mixFields_apply, c0, c1, c2]
      exact mlieBracket_mix hd (A a) (A b) h01 h12 h20
    exact ⟨key 0 1 2 c01, key 1 2 0 c12, key 2 0 1 c20⟩
  surfaces := fun x hx ↦ by
    rw [span_mixFields hA]
    exact h.surfaces x hx
  positive := fun x hx ↦ by
    rw [span_mixFields hA]
    exact h.positive x hx

/-! ## Only the fields on the region matter, and near each point -/

/-- **Only the values of the three fields on the region matter.** The region is open, so fields
that agree on it agree near each of its points. -/
theorem IsRoundOn.congr {ξ η : Fin 3 → Arrows I M} (h : IsRoundOn g ξ s)
    (he : ∀ i, ∀ x ∈ s, η i x = ξ i x) : IsRoundOn g η s where
  isOpen := h.isOpen
  smooth := fun i ↦ (h.smooth i).congr fun y hy ↦
    congrArg (fun v : TangentSpace I y ↦ (⟨y, v⟩ : TangentBundle I M)) (he i y hy)
  unchanged := fun i x hx ↦ (h.unchanged i x hx).congr
    (Filter.eventuallyEq_of_mem (h.isOpen.mem_nhds hx) fun y hy ↦ he i y hy)
  likeTurns := fun x hx ↦ by
    have ev : ∀ i, η i =ᶠ[𝓝 x] ξ i := fun i ↦
      Filter.eventuallyEq_of_mem (h.isOpen.mem_nhds hx) fun y hy ↦ he i y hy
    obtain ⟨h01, h12, h20⟩ := h.likeTurns x hx
    exact ⟨((ev 0).mlieBracket_vectorField_eq (ev 1)).trans (h01.trans (he 2 x hx).symm),
      ((ev 1).mlieBracket_vectorField_eq (ev 2)).trans (h12.trans (he 0 x hx).symm),
      ((ev 2).mlieBracket_vectorField_eq (ev 0)).trans (h20.trans (he 1 x hx).symm)⟩
  surfaces := fun x hx ↦ by
    have e : (fun i ↦ η i x) = fun i ↦ ξ i x := funext fun i ↦ he i x hx
    rw [e]
    exact h.surfaces x hx
  positive := fun x hx ↦ by
    have e : (fun i ↦ η i x) = fun i ↦ ξ i x := funext fun i ↦ he i x hx
    rw [e]
    exact h.positive x hx

/-- **It is enough to look near every point.** If every point of an open region has a
neighbourhood inside the region on which `g` looks the same from every side by the three fields
`ξ`, then it does so on the whole region. -/
theorem isRoundOn_of_local {ξ : Fin 3 → Arrows I M} (hs : IsOpen s)
    (h : ∀ q ∈ s, ∃ u : Set M, q ∈ u ∧ IsRoundOn g ξ u) : IsRoundOn g ξ s where
  isOpen := hs
  smooth := fun i q hq ↦ by
    obtain ⟨u, hqu, hr⟩ := h q hq
    exact ((hr.smooth i).contMDiffAt (hr.isOpen.mem_nhds hqu)).contMDiffWithinAt
  unchanged := fun i q hq ↦ by
    obtain ⟨u, hqu, hr⟩ := h q hq
    exact hr.unchanged i q hqu
  likeTurns := fun q hq ↦ by
    obtain ⟨u, hqu, hr⟩ := h q hq
    exact hr.likeTurns q hqu
  surfaces := fun q hq ↦ by
    obtain ⟨u, hqu, hr⟩ := h q hq
    exact hr.surfaces q hqu
  positive := fun q hq ↦ by
    obtain ⟨u, hqu, hr⟩ := h q hq
    exact hr.positive q hqu

end GravityInLean.Curved
