/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.Checks

import Mathlib.Tactic

/-!
# Uniqueness needs a region in one piece

`GlobalBirkhoffUnique` says that two length-keeping maps on a region in one piece differ by one
symmetry of the model. This file proves the check `GlobalUniqueNeedsOnePiece`: on a region in
two pieces that is false.

**The example.** Take two boxes of Kruskal's table that do not touch: in the first the angle
around the axis is below `1`, in the second it is above `3`. The first map wraps both boxes
round the sphere (`kruskalWrap`). The second map does the same on the first box, and on the
second box it wraps and then turns the sphere by a quarter about its axis.

**Why no single symmetry works.** The point with the angle `0` in the first box and the point
with the angle `2π` in the second box are wrapped to the same point of Kruskal's whole
space-time. The second map sends them to two different points. A symmetry applied after the
first map would send them to the same point.

Two tools that are of use elsewhere:

* `IsKruskalMapOn.congr`: a map that agrees on the region with a length-keeping map is one.
* `IsKruskalMapOn.union`: a map that is length-keeping on two regions is so on both together.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

/-! ## Two tools for length-keeping maps -/

section Tools

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  [IsManifold 𝓘(ℝ, Coords 4) ∞ M] {m : ℝ} {g : LengthMeasure 𝓘(ℝ, Coords 4) M} {s t : Set M}

/-- **A map that agrees with a length-keeping map on the region is length-keeping there.** The
region is open, so the two maps carry every step at a point of the region in the same way. -/
theorem IsKruskalMapOn.congr {D D' : M → Coords 5} (hD : IsKruskalMapOn m g D s)
    (h : ∀ q ∈ s, D' q = D q) : IsKruskalMapOn m g D' s := by
  obtain ⟨hs, hsm, hpt⟩ := hD
  refine ⟨hs, hsm.congr h, fun q hq ↦ ⟨?_, fun v w ↦ ?_⟩⟩
  · rw [h q hq]
    exact (hpt q hq).1
  · have hev : D' =ᶠ[𝓝 q] D := Filter.eventuallyEq_of_mem (hs.mem_nhds hq) fun x hx ↦ h x hx
    have hd : ∀ u : TangentSpace 𝓘(ℝ, Coords 4) q,
        (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 5) D' q u : Coords 5)
          = mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 5) D q u :=
      fun u ↦ DFunLike.congr_fun hev.mfderiv_eq u
    have key : ∀ p p' a a' b b' : Coords 5, p = p' → a = a' → b = b' →
        tableMeasure (kruskalWhole m) p a b = tableMeasure (kruskalWhole m) p' a' b' := by
      rintro p _ a _ b _ rfl rfl rfl
      rfl
    exact ((hpt q hq).2 v w).trans (key _ _ _ _ _ _ (h q hq).symm (hd v).symm (hd w).symm)

/-- **A map that is length-keeping on two regions is length-keeping on the two together.** -/
theorem IsKruskalMapOn.union {D : M → Coords 5} (h1 : IsKruskalMapOn m g D s)
    (h2 : IsKruskalMapOn m g D t) : IsKruskalMapOn m g D (s ∪ t) := by
  refine ⟨h1.1.union h2.1, fun q hq ↦ ?_, fun q hq ↦ ?_⟩
  · rcases hq with hq | hq
    · exact (h1.2.1.contMDiffAt (h1.1.mem_nhds hq)).contMDiffWithinAt
    · exact (h2.2.1.contMDiffAt (h2.1.mem_nhds hq)).contMDiffWithinAt
  · rcases hq with hq | hq
    · exact h1.2.2 q hq
    · exact h2.2.2 q hq

end Tools

/-! ## The example -/

/-- The turn of the sphere by a quarter about its axis: `(y₁, y₂, y₃) ↦ (-y₂, y₁, y₃)`. -/
def quarterTurn : Matrix (Fin 3) (Fin 3) ℝ := !![0, -1, 0; 1, 0, 0; 0, 0, 1]

/-- The first box: the part of `kruskalBox` where the angle around the axis is below `1`. -/
def boxNear : Set (Coords 4) := kruskalBox ∩ {x | x 3 < 1}

/-- The second box: the part of `kruskalBox` where the angle around the axis is above `3`. -/
def boxFar : Set (Coords 4) := kruskalBox ∩ {x | 3 < x 3}

/-- The second map of the example: where the angle around the axis is below `2` (so on the first
box), wrap round the sphere; elsewhere (so on the second box), wrap and then turn the sphere by
a quarter about its axis. -/
noncomputable def wrapTwoWays (x : Coords 4) : Coords 5 :=
  if x 3 < 2 then kruskalWrap x else kruskalSym 1 quarterTurn (kruskalWrap x)

/-- The quarter turn is a turn: it keeps the lengths of ordinary space. -/
theorem quarterTurn_orthogonal : quarterTurn.transpose * quarterTurn = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quarterTurn, Matrix.mul_apply, Fin.sum_univ_three]

/-- Wrapping round the sphere is a length-keeping map on the first box. -/
theorem kruskalWrap_boxNear (m : ℝ) :
    IsKruskalMapOn m (flatMeasure (tableMeasure (kruskalG m))) kruskalWrap boxNear :=
  kruskalWrap_isKruskalMapOn m (isOpen_kruskalBox.inter (isOpen_coord_lt 3 1))
    fun _ hx ↦ (kruskalBox_subset hx.1).1

/-- Wrapping round the sphere is a length-keeping map on the second box. -/
theorem kruskalWrap_boxFar (m : ℝ) :
    IsKruskalMapOn m (flatMeasure (tableMeasure (kruskalG m))) kruskalWrap boxFar :=
  kruskalWrap_isKruskalMapOn m (isOpen_kruskalBox.inter (isOpen_coord_gt 3 3))
    fun _ hx ↦ (kruskalBox_subset hx.1).1

/-- The second map of the example is a length-keeping map on the two boxes together: on the
first box it is the wrapping, on the second the wrapping followed by a symmetry. -/
theorem wrapTwoWays_isKruskalMapOn (m : ℝ) :
    IsKruskalMapOn m (flatMeasure (tableMeasure (kruskalG m))) wrapTwoWays
      (boxNear ∪ boxFar) := by
  refine IsKruskalMapOn.union ((kruskalWrap_boxNear m).congr fun q hq ↦ ?_)
    (((kruskalWrap_boxFar m).sym (L := 1) (R := quarterTurn) (by simp)
      quarterTurn_orthogonal).congr fun q hq ↦ ?_)
  · have h3 : q 3 < 1 := hq.2
    exact ite_eq_left (by linarith)
  · have h3 : 3 < q 3 := hq.2
    exact ite_eq_right (by linarith)

/-- The point with the angle `0` around the axis, where the two rims cross, is in the first
box. -/
theorem near_mem : (![0, 0, π / 2, 0] : Coords 4) ∈ boxNear := by
  simp only [boxNear, kruskalBox, Set.mem_inter_iff, Set.mem_ofPred_eq, Matrix.cons_val]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> linarith [pi_pos]

/-- The point with the angle `2π` around the axis, where the two rims cross, is in the second
box. -/
theorem far_mem : (![0, 0, π / 2, 2 * π] : Coords 4) ∈ boxFar := by
  simp only [boxFar, kruskalBox, Set.mem_inter_iff, Set.mem_ofPred_eq, Matrix.cons_val]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> linarith [pi_pos, two_le_pi]

/-- The two points are wrapped to the same point of Kruskal's whole space-time: the angles `0`
and `2π` around the axis describe the same direction. -/
theorem kruskalWrap_far_eq_near :
    kruskalWrap ![0, 0, π / 2, 2 * π] = kruskalWrap ![0, 0, π / 2, 0] := by
  funext i
  fin_cases i <;> simp [kruskalWrap]

/-- At the point of the first box, the second map gives a point of the sphere whose first
number is `1`. -/
theorem wrapTwoWays_near : wrapTwoWays ![0, 0, π / 2, 0] 2 = 1 := by
  have h : (![0, 0, π / 2, 0] : Coords 4) 3 < 2 := by
    simp only [Matrix.cons_val]
    norm_num
  rw [wrapTwoWays, ite_eq_left h]
  simp [kruskalWrap]

/-- At the point of the second box, the second map gives a point of the sphere whose first
number is `0`: the quarter turn has moved it. -/
theorem wrapTwoWays_far : wrapTwoWays ![0, 0, π / 2, 2 * π] 2 = 0 := by
  have h : ¬ (![0, 0, π / 2, 2 * π] : Coords 4) 3 < 2 := by
    simp only [Matrix.cons_val]
    exact not_lt.mpr (by linarith [two_le_pi])
  rw [wrapTwoWays, ite_eq_right h]
  simp [kruskalSym, kruskalWrap, quarterTurn]

/-- **The region must be in one piece: uniqueness fails on a region in two pieces.** For every
positive mass, the two boxes together are an open region of Kruskal's table with two
length-keeping maps into Kruskal's whole space-time, the wrapping and `wrapTwoWays`, that differ
by no single symmetry: the two maps agree on the first box and differ by a quarter turn on the
second. -/
theorem globalUniqueNeedsOnePiece : GlobalUniqueNeedsOnePiece := by
  intro m _
  refine ⟨boxNear ∪ boxFar, kruskalWrap, wrapTwoWays,
    Set.union_subset (fun x hx ↦ kruskalBox_subset hx.1) (fun x hx ↦ kruskalBox_subset hx.1),
    (kruskalWrap_boxNear m).union (kruskalWrap_boxFar m), wrapTwoWays_isKruskalMapOn m, ?_⟩
  rintro ⟨L, R, -, -, h⟩
  have h1 := h _ (Or.inl near_mem)
  have h2 := h _ (Or.inr far_mem)
  rw [kruskalWrap_far_eq_near] at h2
  have e : wrapTwoWays ![0, 0, π / 2, 0] 2 = wrapTwoWays ![0, 0, π / 2, 2 * π] 2 :=
    congrFun (h1.trans h2.symm) 2
  rw [wrapTwoWays_near, wrapTwoWays_far] at e
  exact one_ne_zero e

end GravityInLean.Curved
