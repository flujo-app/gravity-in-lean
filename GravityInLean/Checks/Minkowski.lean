/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.Tests

import Mathlib.Tactic

/-!
# Test 9: flat space-time in ordinary `x`, `y`, `z`, poles included

Board item `task:checks-minkowski`. The two statements of group 9 in `Goals/Tests.lean` are
proved here. Flat space-time is written in the coordinates `(t, x, y, z)`, and the three turns
are the turns about the `y`-, the `x`- and the `z`-axis, written in these coordinates
(`Tests.cartTurns`). The region is everything except the line through the centre
(`Tests.awayFromCentre`), so the poles of every sphere are included. This is the first test in
which the turns are not written in angles.

* `minkowskiIsRoundOn`: flat space-time looks the same from every side by these turns;
* `minkowskiUsable`: the size of the spheres is a usable distance there.

On the way:

* `bracket_cartTurnY_cartTurnX`, `bracket_cartTurnX_cartTurnZ`, `bracket_cartTurnZ_cartTurnY`:
  the bracket of two of the turns, in the order of the definition, is the third, with the
  standard library's sign of the bracket;
* `finrank_span_cartTurns`: at every point off the centre line the three turns span exactly two
  directions (which two of the three are independent depends on the point);
* `cart_sizeSq`: the squared size of the spheres is `x² + y² + z²`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean

open Real Set

open scoped Manifold ContDiff

namespace Curved

namespace Tests

/-! ## The three turns, by their parts -/

/-- The parts of the turn about the `y`-axis: at `(t, x, y, z)` it is `(0, z, 0, -x)`. -/
noncomputable def cartTurnY : Fin 4 → Coords 4 → ℝ :=
  ![fun _ ↦ 0, fun p ↦ p 3, fun _ ↦ 0, fun p ↦ -p 1]

/-- The parts of the turn about the `x`-axis: at `(t, x, y, z)` it is `(0, 0, -z, y)`. -/
noncomputable def cartTurnX : Fin 4 → Coords 4 → ℝ :=
  ![fun _ ↦ 0, fun _ ↦ 0, fun p ↦ -p 3, fun p ↦ p 2]

/-- The parts of the turn about the `z`-axis: at `(t, x, y, z)` it is `(0, -y, x, 0)`. -/
noncomputable def cartTurnZ : Fin 4 → Coords 4 → ℝ :=
  ![fun _ ↦ 0, fun p ↦ -p 2, fun p ↦ p 1, fun _ ↦ 0]

/-- The first of the three fields of the test is the turn about the `y`-axis. -/
theorem cartTurns_zero : cartTurns 0 = fieldOf cartTurnY := rfl

/-- The second of the three fields of the test is the turn about the `x`-axis. -/
theorem cartTurns_one : cartTurns 1 = fieldOf cartTurnX := rfl

/-- The third of the three fields of the test is the turn about the `z`-axis. -/
theorem cartTurns_two : cartTurns 2 = fieldOf cartTurnZ := rfl

/-- The slope of a coordinate along a coordinate: one along itself, zero along the others. -/
theorem slope_coord (m j : Fin 4) (x : Coords 4) :
    slope m (fun p : Coords 4 ↦ p j) x = if j = m then 1 else 0 := by
  by_cases h : j = m
  · subst h
    have e : slope j (fun p : Coords 4 ↦ p j) x = 1 :=
      (slope_along j (fun s ↦ s) x).trans (congrFun deriv_id'' _)
    simpa using e
  · simpa [h] using slope_across h (fun s ↦ s) x

/-- The slope of minus a coordinate along a coordinate: minus one along itself, zero along the
others. -/
theorem slope_neg_coord (m j : Fin 4) (x : Coords 4) :
    slope m (fun p : Coords 4 ↦ -p j) x = if j = m then -1 else 0 := by
  by_cases h : j = m
  · subst h
    have e : slope j (fun p : Coords 4 ↦ -p j) x = -1 :=
      (slope_along j (fun s ↦ -s) x).trans (hasDerivAt_id (x j)).neg.deriv
    simpa using e
  · simpa [h] using slope_across h (fun s ↦ -s) x

/-- Reading off one coordinate is a smooth function. -/
theorem contDiff_coord (j : Fin 4) : ContDiff ℝ ∞ fun p : Coords 4 ↦ p j :=
  contDiff_apply ℝ (fun _ : Fin 4 ↦ ℝ) j

/-- The parts of the turn about the `y`-axis are smooth functions. -/
theorem contDiff_cartTurnY (k : Fin 4) : ContDiff ℝ ∞ (cartTurnY k) := by
  fin_cases k
  exacts [contDiff_const, contDiff_coord 3, contDiff_const, (contDiff_coord 1).neg]

/-- The parts of the turn about the `x`-axis are smooth functions. -/
theorem contDiff_cartTurnX (k : Fin 4) : ContDiff ℝ ∞ (cartTurnX k) := by
  fin_cases k
  exacts [contDiff_const, contDiff_const, (contDiff_coord 3).neg, contDiff_coord 2]

/-- The parts of the turn about the `z`-axis are smooth functions. -/
theorem contDiff_cartTurnZ (k : Fin 4) : ContDiff ℝ ∞ (cartTurnZ k) := by
  fin_cases k
  exacts [contDiff_const, (contDiff_coord 2).neg, contDiff_coord 1, contDiff_const]

/-- The parts of the turn about the `y`-axis can be differentiated at every point. -/
theorem differentiableAt_cartTurnY (x : Coords 4) (k : Fin 4) :
    DifferentiableAt ℝ (cartTurnY k) x :=
  (contDiff_cartTurnY k).contDiffAt.differentiableAt (by simp)

/-- The parts of the turn about the `x`-axis can be differentiated at every point. -/
theorem differentiableAt_cartTurnX (x : Coords 4) (k : Fin 4) :
    DifferentiableAt ℝ (cartTurnX k) x :=
  (contDiff_cartTurnX k).contDiffAt.differentiableAt (by simp)

/-- The parts of the turn about the `z`-axis can be differentiated at every point. -/
theorem differentiableAt_cartTurnZ (x : Coords 4) (k : Fin 4) :
    DifferentiableAt ℝ (cartTurnZ k) x :=
  (contDiff_cartTurnZ k).contDiffAt.differentiableAt (by simp)

/-! ## Each turn leaves the flat length measure unchanged -/

/-- The entries of the flat table do not change from point to point. -/
theorem slope_flatG (i j k : Fin 4) (x : Coords 4) : slope k (flatG i j) x = 0 :=
  slope_const _ _ _

/-- The turn about the `y`-axis leaves the flat table unchanged: Killing's equation, entry by
entry. -/
theorem cartTurnY_unchanged (x : Coords 4) :
    GravityInLean.LeavesUnchangedAt flatG cartTurnY x := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [lieD, Fin.sum_univ_four, slope_flatG, cartTurnY, flatG, slope_coord, slope_neg_coord,
      slope_const]

/-- The turn about the `x`-axis leaves the flat table unchanged. -/
theorem cartTurnX_unchanged (x : Coords 4) :
    GravityInLean.LeavesUnchangedAt flatG cartTurnX x := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [lieD, Fin.sum_univ_four, slope_flatG, cartTurnX, flatG, slope_coord, slope_neg_coord,
      slope_const]

/-- The turn about the `z`-axis leaves the flat table unchanged. -/
theorem cartTurnZ_unchanged (x : Coords 4) :
    GravityInLean.LeavesUnchangedAt flatG cartTurnZ x := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [lieD, Fin.sum_univ_four, slope_flatG, cartTurnZ, flatG, slope_coord, slope_neg_coord,
      slope_const]

/-! ## The turns combine the way turns do -/

/-- The bracket of two fields given by their parts is the field with the parts `Z`, once the
coordinate formula for the bracket gives `Z` part by part. -/
theorem bracket_of_parts {X Y Z : Fin 4 → Coords 4 → ℝ} {x : Coords 4}
    (hX : ∀ k, DifferentiableAt ℝ (X k) x) (hY : ∀ k, DifferentiableAt ℝ (Y k) x)
    (h : ∀ k, ∑ m, X m x * slope m (Y k) x - ∑ m, Y m x * slope m (X k) x = Z k x) :
    VectorField.mlieBracket 𝓘(ℝ, Coords 4) (fieldOf X) (fieldOf Y) x = fieldOf Z x :=
  funext fun k ↦ (mlieBracket_fieldOf hX hY k).trans (h k)

/-- **The bracket of the turn about `y` with the turn about `x` is the turn about `z`.** -/
theorem bracket_cartTurnY_cartTurnX (x : Coords 4) :
    VectorField.mlieBracket 𝓘(ℝ, Coords 4) (fieldOf cartTurnY) (fieldOf cartTurnX) x
      = fieldOf cartTurnZ x := by
  refine bracket_of_parts (differentiableAt_cartTurnY x) (differentiableAt_cartTurnX x) ?_
  intro k
  fin_cases k <;>
    simp [cartTurnY, cartTurnX, cartTurnZ, slope_coord, slope_neg_coord, slope_const]

/-- **The bracket of the turn about `x` with the turn about `z` is the turn about `y`.** -/
theorem bracket_cartTurnX_cartTurnZ (x : Coords 4) :
    VectorField.mlieBracket 𝓘(ℝ, Coords 4) (fieldOf cartTurnX) (fieldOf cartTurnZ) x
      = fieldOf cartTurnY x := by
  refine bracket_of_parts (differentiableAt_cartTurnX x) (differentiableAt_cartTurnZ x) ?_
  intro k
  fin_cases k <;>
    simp [cartTurnY, cartTurnX, cartTurnZ, slope_coord, slope_neg_coord, slope_const]

/-- **The bracket of the turn about `z` with the turn about `y` is the turn about `x`.** -/
theorem bracket_cartTurnZ_cartTurnY (x : Coords 4) :
    VectorField.mlieBracket 𝓘(ℝ, Coords 4) (fieldOf cartTurnZ) (fieldOf cartTurnY) x
      = fieldOf cartTurnX x := by
  refine bracket_of_parts (differentiableAt_cartTurnZ x) (differentiableAt_cartTurnY x) ?_
  intro k
  fin_cases k <;>
    simp [cartTurnY, cartTurnX, cartTurnZ, slope_coord, slope_neg_coord, slope_const]

/-! ## The turns span two directions, poles included -/

/-- A set of steps spans exactly two directions when two of its steps are independent and every
step of the set, stretched by some factor that is not zero, is a combination of these two. -/
theorem finrank_span_eq_two {V : Type*} [AddCommGroup V] [Module ℝ V] {s : Set V} {a b : V}
    (ha : a ∈ s) (hb : b ∈ s) (hli : LinearIndependent ℝ ![a, b])
    (hs : ∀ v ∈ s, ∃ t c d : ℝ, t ≠ 0 ∧ t • v = c • a + d • b) :
    Module.finrank ℝ (Submodule.span ℝ s) = 2 := by
  have e : Submodule.span ℝ s = Submodule.span ℝ (Set.range ![a, b]) := by
    apply le_antisymm
    · refine Submodule.span_le.2 fun v hv ↦ ?_
      obtain ⟨t, c, d, ht, h⟩ := hs v hv
      have hv' : v = t⁻¹ • (c • a + d • b) := by
        rw [← h, smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [hv']
      exact Submodule.smul_mem _ _ (Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      fin_cases i
      exacts [Submodule.subset_span ha, Submodule.subset_span hb]
  rw [e, finrank_span_eq_card hli]
  simp

/-- The step of the turn about the `y`-axis at the point `x`. -/
noncomputable def stepY (x : Coords 4) : Coords 4 := fun k ↦ cartTurnY k x

/-- The step of the turn about the `x`-axis at the point `x`. -/
noncomputable def stepX (x : Coords 4) : Coords 4 := fun k ↦ cartTurnX k x

/-- The step of the turn about the `z`-axis at the point `x`. -/
noncomputable def stepZ (x : Coords 4) : Coords 4 := fun k ↦ cartTurnZ k x

/-- At every point the three turns obey one relation: `y` times the first plus `x` times the
second plus `z` times the third is zero. (So they never span more than two directions.) -/
theorem cartTurns_relation (x : Coords 4) :
    x 2 • stepY x + x 1 • stepX x + x 3 • stepZ x = 0 := by
  funext k
  fin_cases k <;> simp [stepY, stepX, stepZ, cartTurnY, cartTurnX, cartTurnZ] <;> ring

/-- The steps of the three turns at `x`, as a set, are the three steps named above. -/
theorem mem_range_cartTurns {x : Coords 4} {v : Coords 4}
    (hv : v ∈ Set.range fun i : Fin 3 ↦ (cartTurns i x : Coords 4)) :
    v = stepY x ∨ v = stepX x ∨ v = stepZ x := by
  obtain ⟨i, rfl⟩ := hv
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- **At every point off the centre line the three turns span exactly two directions.** Which
two of the three are independent depends on the point: where `z ≠ 0` the turns about `y` and
`x`, where `x ≠ 0` the turns about `y` and `z`, where `y ≠ 0` the turns about `x` and `z`. -/
theorem finrank_span_cartTurns {x : Coords 4} (hx : x ∈ awayFromCentre) :
    Module.finrank ℝ
      (Submodule.span ℝ (Set.range fun i : Fin 3 ↦ (cartTurns i x : Coords 4))) = 2 := by
  have hx' : x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 ≠ 0 := hx
  have hrel := cartTurns_relation x
  have hcases : x 3 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hx'
    rw [hcon.1, hcon.2.1, hcon.2.2]
    norm_num
  rcases hcases with hz | hxx | hy
  · -- `z ≠ 0`: the turns about `y` and about `x` are independent.
    refine finrank_span_eq_two (a := stepY x) (b := stepX x) ⟨0, rfl⟩ ⟨1, rfl⟩ ?_ ?_
    · rw [LinearIndependent.pair_iff]
      intro c d h
      have h1 : c * x 3 + d * 0 = 0 := congrFun h 1
      have h2 : c * 0 + d * -x 3 = 0 := congrFun h 2
      have hc : c * x 3 = 0 := by linear_combination h1
      have hd : d * x 3 = 0 := by linear_combination -h2
      exact ⟨(mul_eq_zero.mp hc).resolve_right hz, (mul_eq_zero.mp hd).resolve_right hz⟩
    · intro v hv
      rcases mem_range_cartTurns hv with rfl | rfl | rfl
      · exact ⟨1, 1, 0, one_ne_zero, by simp⟩
      · exact ⟨1, 0, 1, one_ne_zero, by simp⟩
      · exact ⟨x 3, -x 2, -x 1, hz, by
          rw [neg_smul, neg_smul]
          linear_combination (exp := 1) hrel⟩
  · -- `x ≠ 0`: the turns about `y` and about `z` are independent.
    refine finrank_span_eq_two (a := stepY x) (b := stepZ x) ⟨0, rfl⟩ ⟨2, rfl⟩ ?_ ?_
    · rw [LinearIndependent.pair_iff]
      intro c d h
      have h1 : c * -x 1 + d * 0 = 0 := congrFun h 3
      have h2 : c * 0 + d * x 1 = 0 := congrFun h 2
      have hc : c * x 1 = 0 := by linear_combination -h1
      have hd : d * x 1 = 0 := by linear_combination h2
      exact ⟨(mul_eq_zero.mp hc).resolve_right hxx, (mul_eq_zero.mp hd).resolve_right hxx⟩
    · intro v hv
      rcases mem_range_cartTurns hv with rfl | rfl | rfl
      · exact ⟨1, 1, 0, one_ne_zero, by simp⟩
      · exact ⟨x 1, -x 2, -x 3, hxx, by
          rw [neg_smul, neg_smul]
          linear_combination (exp := 1) hrel⟩
      · exact ⟨1, 0, 1, one_ne_zero, by simp⟩
  · -- `y ≠ 0`: the turns about `x` and about `z` are independent.
    refine finrank_span_eq_two (a := stepX x) (b := stepZ x) ⟨1, rfl⟩ ⟨2, rfl⟩ ?_ ?_
    · rw [LinearIndependent.pair_iff]
      intro c d h
      have h1 : c * x 2 + d * 0 = 0 := congrFun h 3
      have h2 : c * 0 + d * -x 2 = 0 := congrFun h 1
      have hc : c * x 2 = 0 := by linear_combination h1
      have hd : d * x 2 = 0 := by linear_combination -h2
      exact ⟨(mul_eq_zero.mp hc).resolve_right hy, (mul_eq_zero.mp hd).resolve_right hy⟩
    · intro v hv
      rcases mem_range_cartTurns hv with rfl | rfl | rfl
      · exact ⟨x 2, -x 1, -x 3, hy, by
          rw [neg_smul, neg_smul]
          linear_combination (exp := 1) hrel⟩
      · exact ⟨1, 1, 0, one_ne_zero, by simp⟩
      · exact ⟨1, 0, 1, one_ne_zero, by simp⟩

/-! ## On the spheres all lengths are positive -/

/-- The flat length measure of two steps: minus the product of the time parts plus the products
of the three space parts. -/
theorem flat_measure_apply (x v w : Coords 4) :
    tableMeasure flatG x v w = -(v 0 * w 0) + v 1 * w 1 + v 2 * w 2 + v 3 * w 3 := by
  simp [tableMeasure, formOf_apply, Fin.sum_univ_four, flatG]

/-- The flat length measure of a step with no time part and any other step. -/
theorem flat_measure_spaceStep (x : Coords 4) (a b c : ℝ) (w : Coords 4) :
    tableMeasure flatG x ![0, a, b, c] w = a * w 1 + b * w 2 + c * w 3 := by
  rw [flat_measure_apply]
  simp

/-- A step in the directions that the three turns span has no time part. -/
theorem time_part_zero {x v : Coords 4}
    (hv : v ∈ Submodule.span ℝ (Set.range fun i : Fin 3 ↦ (cartTurns i x : Coords 4))) :
    v 0 = 0 := by
  have hle : Submodule.span ℝ (Set.range fun i : Fin 3 ↦ (cartTurns i x : Coords 4))
      ≤ LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 ↦ ℝ) 0) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> rfl
  exact hle hv

/-- In the directions that the three turns span, every step that is not zero has a positive
squared length. -/
theorem flat_pos_on_cartTurns {x v : Coords 4}
    (hv : v ∈ Submodule.span ℝ (Set.range fun i : Fin 3 ↦ (cartTurns i x : Coords 4)))
    (hne : v ≠ 0) : 0 < tableMeasure flatG x v v := by
  have h0 := time_part_zero hv
  rw [flat_measure_apply, h0]
  by_contra hcon
  have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
  have h2 : v 2 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
  have h3 : v 3 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
  apply hne
  funext k
  fin_cases k
  exacts [h0, h1, h2, h3]

/-! ## The first statement -/

/-- The region off the centre line is open. -/
theorem isOpen_awayFromCentre : IsOpen awayFromCentre :=
  isOpen_ne_fun (by fun_prop) continuous_const

/-- **Test 9, first half.** Flat space-time looks the same from every side by the three turns
written in ordinary `x`, `y`, `z`, everywhere off the centre line, poles included: the turns are
smooth, leave the length measure unchanged, combine the way turns do, span two directions, and
all lengths in these directions are positive. -/
theorem minkowskiIsRoundOn : MinkowskiIsRoundOn where
  isOpen := isOpen_awayFromCentre
  smooth := by
    intro i
    fin_cases i
    · exact contMDiffOn_arrows_iff.mpr
        (contDiffOn_pi.2 fun k ↦ (contDiff_cartTurnY k).contDiffOn)
    · exact contMDiffOn_arrows_iff.mpr
        (contDiffOn_pi.2 fun k ↦ (contDiff_cartTurnX k).contDiffOn)
    · exact contMDiffOn_arrows_iff.mpr
        (contDiffOn_pi.2 fun k ↦ (contDiff_cartTurnZ k).contDiffOn)
  unchanged := by
    intro i x _
    have hg := fun a b ↦ flatG_regular.differentiableAt (Set.mem_univ x) a b
    fin_cases i
    · exact (leavesUnchangedAt_table_iff hg (differentiableAt_cartTurnY x)).mpr
        (cartTurnY_unchanged x)
    · exact (leavesUnchangedAt_table_iff hg (differentiableAt_cartTurnX x)).mpr
        (cartTurnX_unchanged x)
    · exact (leavesUnchangedAt_table_iff hg (differentiableAt_cartTurnZ x)).mpr
        (cartTurnZ_unchanged x)
  likeTurns := fun x _ ↦
    ⟨bracket_cartTurnY_cartTurnX x, bracket_cartTurnX_cartTurnZ x,
      bracket_cartTurnZ_cartTurnY x⟩
  surfaces := fun _ hx ↦ finrank_span_cartTurns hx
  positive := fun _ _ _ hv hne ↦ flat_pos_on_cartTurns hv hne

/-! ## The second statement -/

/-- The squared size of the spheres that the three turns sweep out is `x² + y² + z²`. -/
theorem cart_sizeSq (y : Coords 4) :
    sizeSq (flatMeasure (tableMeasure flatG)) cartTurns y = y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 := by
  have e : sizeSq (flatMeasure (tableMeasure flatG)) cartTurns y
      = (tableMeasure flatG y (stepY y) (stepY y) + tableMeasure flatG y (stepX y) (stepX y)
        + tableMeasure flatG y (stepZ y) (stepZ y)) / 2 := rfl
  rw [e]
  simp only [flat_measure_apply]
  simp [stepY, stepX, stepZ, cartTurnY, cartTurnX, cartTurnZ]
  ring

/-- **Test 9, second half.** Everywhere off the centre line the size of the spheres is a usable
distance: the step `(0, 2x, 2y, 2z)` points the way the spheres grow, and its squared length
`4 (x² + y² + z²)` is not zero. -/
theorem minkowskiUsable : MinkowskiUsable := by
  intro x hx
  have hx' : x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 ≠ 0 := hx
  have hfun : sizeSq (flatMeasure (tableMeasure flatG)) cartTurns
      = fun y : Coords 4 ↦ coordL 1 y ^ 2 + coordL 2 y ^ 2 + coordL 3 y ^ 2 :=
    funext cart_sizeSq
  have hd : HasFDerivAt (fun y : Coords 4 ↦ coordL 1 y ^ 2 + coordL 2 y ^ 2 + coordL 3 y ^ 2)
      ((2 • coordL 1 x ^ (2 - 1)) • coordL 1 + (2 • coordL 2 x ^ (2 - 1)) • coordL 2
        + (2 • coordL 3 x ^ (2 - 1)) • coordL 3) x :=
    ((((coordL (n := 4) 1).hasFDerivAt (x := x)).pow 2).add
      (((coordL (n := 4) 2).hasFDerivAt (x := x)).pow 2)).add
      (((coordL (n := 4) 3).hasFDerivAt (x := x)).pow 2)
  refine ⟨(![0, 2 * x 1, 2 * x 2, 2 * x 3] : Coords 4), fun w ↦ ?_, ?_⟩
  · rw [mvfderiv_flat, hfun, hd.fderiv]
    change tableMeasure flatG x ![0, 2 * x 1, 2 * x 2, 2 * x 3] w = _
    rw [flat_measure_spaceStep]
    simp
  · change tableMeasure flatG x ![0, 2 * x 1, 2 * x 2, 2 * x 3] ![0, 2 * x 1, 2 * x 2, 2 * x 3]
      ≠ 0
    rw [flat_measure_spaceStep]
    have e : 2 * x 1 * (![0, 2 * x 1, 2 * x 2, 2 * x 3] : Coords 4) 1
        + 2 * x 2 * (![0, 2 * x 1, 2 * x 2, 2 * x 3] : Coords 4) 2
        + 2 * x 3 * (![0, 2 * x 1, 2 * x 2, 2 * x 3] : Coords 4) 3
        = 4 * (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) := by
      simp
      ring
    rw [e]
    exact mul_ne_zero four_ne_zero hx'

end Tests

end Curved

end GravityInLean
