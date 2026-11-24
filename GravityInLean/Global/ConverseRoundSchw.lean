/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.Checks
public import GravityInLean.Checks.Minkowski
public import GravityInLean.BothWays.PullRound
public import GravityInLean.BothWays.PullSpaceTime
public import GravityInLean.Join.Atlas

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# A space-time with a length-keeping map into Schwarzschild's whole space-time is round

The `round` half of the converse of the theorem for a whole space-time, for a mass that is zero
or negative. If `D` is a length-keeping map from the region `s` into Schwarzschild's whole
space-time (in ordinary space labels) that misses the centre, then the space-time looks the same
from every side on `s`.

The three fields are defined on all of `s` through `D` itself: at `q`, the step that `D` carries
to the turn of ordinary space at `D q` (`turnFieldOf`). The proof has three parts.

* In ordinary space labels, Schwarzschild's whole table looks the same from every side by the
  three turns of ordinary space, everywhere off the centre line (`schwSpace_isRoundOn`). The
  turns, their brackets and the directions they span are those of flat space-time
  (`Checks/Minkowski.lean`); what is new is that each turn leaves Schwarzschild's table
  unchanged, and that lengths on the spheres are positive.
* "Looks the same from every side" only looks at the fields near each point
  (`isRoundOn_of_locally`).
* Near each point `D` is a chart of the curved space (`IsSchwarzschildMapOn.exists_chart_self`),
  in that chart the length measure reads as Schwarzschild's table, and the fields defined
  through `D` are the turns taken to the curved space by that chart
  (`turnFieldOf_eq_pushField`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set Filter VectorField

open scoped Manifold ContDiff Topology

/-! ## Functions of the distance from the centre -/

/-- The slope of `x₁² + x₂² + x₃²`, as a function of the four labels. -/
theorem hasFDerivAt_sumSq (x : Coords 4) :
    HasFDerivAt (fun y : Coords 4 ↦ y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2)
      ((2 * x 1) • (ContinuousLinearMap.proj 1 : Coords 4 →L[ℝ] ℝ)
        + (2 * x 2) • (ContinuousLinearMap.proj 2 : Coords 4 →L[ℝ] ℝ)
        + (2 * x 3) • (ContinuousLinearMap.proj 3 : Coords 4 →L[ℝ] ℝ)) x := by
  have h : ∀ i : Fin 4, HasFDerivAt (fun y : Coords 4 ↦ y i ^ 2)
      ((2 * x i) • (ContinuousLinearMap.proj i : Coords 4 →L[ℝ] ℝ)) x := fun i ↦ by
    have h1 := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 ↦ ℝ) i).hasFDerivAt
      (x := x)).pow 2
    refine h1.congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)
    simp
  exact ((h 1).add (h 2)).add (h 3)

/-- A function of `x₁² + x₂² + x₃²` can be differentiated where its outer function can. -/
theorem differentiableAt_radial {F : ℝ → ℝ} {x : Coords 4}
    (hF : DifferentiableAt ℝ F (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2)) :
    DifferentiableAt ℝ (fun y : Coords 4 ↦ F (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2)) x :=
  (HasDerivAt.comp_hasFDerivAt (h₂ := F) (f := fun y : Coords 4 ↦ y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2)
    x hF.hasDerivAt (hasFDerivAt_sumSq x)).differentiableAt

/-- The slopes of a function of `x₁² + x₂² + x₃²`: none along time, and along the space label
`x_k` the slope of the outer function times `2 x_k`. -/
theorem slope_radial {F : ℝ → ℝ} {x : Coords 4}
    (hF : DifferentiableAt ℝ F (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2)) (k : Fin 4) :
    slope k (fun y : Coords 4 ↦ F (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2)) x
      = deriv F (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) * (if k = 0 then 0 else 2 * x k) := by
  have hc := HasDerivAt.comp_hasFDerivAt (h₂ := F)
    (f := fun y : Coords 4 ↦ y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) x hF.hasDerivAt (hasFDerivAt_sumSq x)
  have e : slope k (fun y : Coords 4 ↦ F (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2)) x
      = (deriv F (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2)
        • ((2 * x 1) • (ContinuousLinearMap.proj 1 : Coords 4 →L[ℝ] ℝ)
          + (2 * x 2) • (ContinuousLinearMap.proj 2 : Coords 4 →L[ℝ] ℝ)
          + (2 * x 3) • (ContinuousLinearMap.proj 3 : Coords 4 →L[ℝ] ℝ))) (Pi.single k 1) :=
    (slope_eq_fderiv hc.differentiableAt k).trans
      (congrArg (fun A : Coords 4 →L[ℝ] ℝ ↦ A (Pi.single k 1)) hc.fderiv)
  rw [e]
  fin_cases k <;> simp

/-- The time entry of Schwarzschild's table in ordinary space labels, as a function of
`t = x₁² + x₂² + x₃²`. -/
noncomputable def schwTimeOf (m t : ℝ) : ℝ := -schwA m (√t)

/-- The factor of `(x₁ dx₁ + x₂ dx₂ + x₃ dx₃)²` in Schwarzschild's table in ordinary space
labels, as a function of `t = x₁² + x₂² + x₃²`. -/
noncomputable def schwStretchOf (m t : ℝ) : ℝ := 2 * m / (√t ^ 2 * (√t - 2 * m))

/-- The time entry can be differentiated off the centre. -/
theorem differentiableAt_schwTimeOf (m : ℝ) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (schwTimeOf m) t := by
  have hs : DifferentiableAt ℝ Real.sqrt t := (Real.hasDerivAt_sqrt ht.ne').differentiableAt
  have hs0 : √t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have h1 : DifferentiableAt ℝ (fun t : ℝ ↦ 2 * m / √t) t :=
    (differentiableAt_const (2 * m)).div hs hs0
  have h2 : DifferentiableAt ℝ (fun t : ℝ ↦ -(1 - 2 * m / √t)) t :=
    ((differentiableAt_const (1 : ℝ)).sub h1).neg
  exact h2

/-- The factor of the extra term can be differentiated off the centre, for a mass that is zero
or negative. -/
theorem differentiableAt_schwStretchOf {m : ℝ} (hm : m ≤ 0) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (schwStretchOf m) t := by
  have hs : DifferentiableAt ℝ Real.sqrt t := (Real.hasDerivAt_sqrt ht.ne').differentiableAt
  have hpos : 0 < √t := Real.sqrt_pos.mpr ht
  have hne : √t ^ 2 * (√t - 2 * m) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hpos.ne') (by linarith : 0 < √t - 2 * m).ne'
  have h1 : DifferentiableAt ℝ (fun t : ℝ ↦ √t ^ 2 * (√t - 2 * m)) t :=
    (hs.pow 2).mul (hs.sub (differentiableAt_const (2 * m)))
  have h2 : DifferentiableAt ℝ (fun t : ℝ ↦ 2 * m / (√t ^ 2 * (√t - 2 * m))) t :=
    (differentiableAt_const (2 * m)).div h1 hne
  exact h2

/-! ## The entries of Schwarzschild's table in ordinary space labels, and their slopes -/

/-- The entries of Schwarzschild's table in ordinary space labels, written with the two
functions of `x₁² + x₂² + x₃²`. -/
theorem schwSpaceG_value (m : ℝ) (a b : Fin 4) (y : Coords 4) :
    schwSpaceG m a b y
      = (if a = 0 ∧ b = 0 then schwTimeOf m (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) else 0)
        + (if a = 0 ∨ b = 0 then 0
          else (if a = b then 1 else 0)
            + schwStretchOf m (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) * y a * y b) := by
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · simp [schwSpaceG, schwTimeOf, centreDist, ha, hb]
    · simp [schwSpaceG, ha, hb]
  · by_cases hb : b = 0
    · simp [schwSpaceG, ha, hb]
    · simp [schwSpaceG, schwStretchOf, centreDist, ha, hb]

/-- **The entries of Schwarzschild's table in ordinary space labels can be differentiated off
the centre, and their slopes** are given by two numbers `cα`, `cκ` (the slopes of the two
functions of `x₁² + x₂² + x₃²`): a slope along the label `x_k` of such a function is the number
times `2 x_k`. -/
theorem schwSpaceG_slopes {m : ℝ} (hm : m ≤ 0) {x : Coords 4}
    (hx : 0 < x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) :
    (∀ a b, DifferentiableAt ℝ (schwSpaceG m a b) x) ∧ ∃ cα cκ : ℝ, ∀ k a b : Fin 4,
      slope k (schwSpaceG m a b) x
        = (if a = 0 ∧ b = 0 then cα * (if k = 0 then 0 else 2 * x k) else 0)
          + (if a = 0 ∨ b = 0 then 0
            else cκ * (if k = 0 then 0 else 2 * x k) * x a * x b
              + schwStretchOf m (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) * (if a = k then 1 else 0) * x b
              + schwStretchOf m (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) * x a
                * (if b = k then 1 else 0)) := by
  have hα := differentiableAt_schwTimeOf m hx
  have hκ := differentiableAt_schwStretchOf hm hx
  have dα := differentiableAt_radial hα
  have dκ := differentiableAt_radial hκ
  have dc : ∀ j : Fin 4, DifferentiableAt ℝ (fun y : Coords 4 ↦ y j) x := fun j ↦ by fun_prop
  -- the three kinds of entries, as functions
  have e00 : schwSpaceG m 0 0 = fun y ↦ schwTimeOf m (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) :=
    funext fun y ↦ by rw [schwSpaceG_value]; simp
  have e0 : ∀ a b : Fin 4, (a = 0 ∨ b = 0) → ¬(a = 0 ∧ b = 0) →
      schwSpaceG m a b = fun _ ↦ 0 := fun a b h1 h2 ↦
    funext fun y ↦ by rw [schwSpaceG_value, ite_eq_right h2, ite_eq_left h1, add_zero]
  have e1 : ∀ a b : Fin 4, ¬(a = 0 ∨ b = 0) → schwSpaceG m a b
      = fun y ↦ (if a = b then (1 : ℝ) else 0)
        + schwStretchOf m (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) * y a * y b := fun a b h1 ↦
    funext fun y ↦ by
      have h2 : ¬(a = 0 ∧ b = 0) := fun h ↦ h1 (Or.inl h.1)
      rw [schwSpaceG_value, ite_eq_right h2, ite_eq_right h1, zero_add]
  refine ⟨fun a b ↦ ?_, deriv (schwTimeOf m) (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2),
    deriv (schwStretchOf m) (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2), fun k a b ↦ ?_⟩
  · by_cases h1 : a = 0 ∨ b = 0
    · by_cases h2 : a = 0 ∧ b = 0
      · obtain ⟨rfl, rfl⟩ := h2
        rw [e00]
        exact dα
      · rw [e0 a b h1 h2]
        exact differentiableAt_const 0
    · rw [e1 a b h1]
      exact (differentiableAt_const _).add ((dκ.mul (dc a)).mul (dc b))
  · by_cases h1 : a = 0 ∨ b = 0
    · by_cases h2 : a = 0 ∧ b = 0
      · obtain ⟨rfl, rfl⟩ := h2
        have h00 : (0 : Fin 4) = 0 ∧ (0 : Fin 4) = 0 := ⟨rfl, rfl⟩
        rw [e00, slope_radial hα, ite_eq_left h00, ite_eq_left h1, add_zero]
      · rw [e0 a b h1 h2, slope_const, ite_eq_right h2, ite_eq_left h1, add_zero]
    · have s1 : slope k (fun y : Coords 4 ↦ schwStretchOf m (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) * y a) x
          = slope k (fun y : Coords 4 ↦ schwStretchOf m (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2)) x * x a
            + schwStretchOf m (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2)
              * slope k (fun y : Coords 4 ↦ y a) x :=
        slope_mul dκ (dc a) k
      have s2 : slope k
          (fun y : Coords 4 ↦ schwStretchOf m (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) * y a * y b) x
          = slope k (fun y : Coords 4 ↦ schwStretchOf m (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) * y a) x
              * x b
            + schwStretchOf m (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) * x a
              * slope k (fun y : Coords 4 ↦ y b) x :=
        slope_mul (dκ.mul (dc a)) (dc b) k
      have s3 : slope k (fun y : Coords 4 ↦ (if a = b then (1 : ℝ) else 0)
            + schwStretchOf m (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) * y a * y b) x
          = slope k (fun _ : Coords 4 ↦ (if a = b then (1 : ℝ) else 0)) x
            + slope k
              (fun y : Coords 4 ↦ schwStretchOf m (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) * y a * y b) x :=
        slope_add (differentiableAt_const _) ((dκ.mul (dc a)).mul (dc b)) k
      have h2 : ¬(a = 0 ∧ b = 0) := fun h ↦ h1 (Or.inl h.1)
      rw [e1 a b h1, s3, s2, s1, slope_const, slope_radial hκ, Tests.slope_coord,
        Tests.slope_coord, ite_eq_right h2, ite_eq_right h1]
      ring

/-! ## Each turn of ordinary space leaves Schwarzschild's table unchanged -/

/-- The turn about the `y`-axis leaves Schwarzschild's table in ordinary space labels unchanged,
off the centre: Killing's equation, entry by entry. -/
theorem cartTurnY_unchanged_schw {m : ℝ} (hm : m ≤ 0) {x : Coords 4}
    (hx : 0 < x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) :
    GravityInLean.LeavesUnchangedAt (schwSpaceG m) Tests.cartTurnY x := by
  obtain ⟨-, cα, cκ, hs⟩ := schwSpaceG_slopes hm hx
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [lieD, Fin.sum_univ_four, hs, schwSpaceG_value, Tests.cartTurnY, Tests.slope_coord,
      Tests.slope_neg_coord, slope_const] <;> ring

/-- The turn about the `x`-axis leaves Schwarzschild's table in ordinary space labels unchanged,
off the centre. -/
theorem cartTurnX_unchanged_schw {m : ℝ} (hm : m ≤ 0) {x : Coords 4}
    (hx : 0 < x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) :
    GravityInLean.LeavesUnchangedAt (schwSpaceG m) Tests.cartTurnX x := by
  obtain ⟨-, cα, cκ, hs⟩ := schwSpaceG_slopes hm hx
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [lieD, Fin.sum_univ_four, hs, schwSpaceG_value, Tests.cartTurnX, Tests.slope_coord,
      Tests.slope_neg_coord, slope_const] <;> ring

/-- The turn about the `z`-axis leaves Schwarzschild's table in ordinary space labels unchanged,
off the centre. -/
theorem cartTurnZ_unchanged_schw {m : ℝ} (hm : m ≤ 0) {x : Coords 4}
    (hx : 0 < x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) :
    GravityInLean.LeavesUnchangedAt (schwSpaceG m) Tests.cartTurnZ x := by
  obtain ⟨-, cα, cκ, hs⟩ := schwSpaceG_slopes hm hx
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [lieD, Fin.sum_univ_four, hs, schwSpaceG_value, Tests.cartTurnZ, Tests.slope_coord,
      Tests.slope_neg_coord, slope_const] <;> ring

/-! ## Lengths on the spheres are positive -/

/-- A step in the directions that the three turns span is at right angles, in the ordinary
sense, to the line from the centre. -/
theorem perp_of_mem_span_cartTurns {x v : Coords 4}
    (hv : v ∈ Submodule.span ℝ (Set.range fun i : Fin 3 ↦ (Tests.cartTurns i x : Coords 4))) :
    x 1 * v 1 + x 2 * v 2 + x 3 * v 3 = 0 := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, rfl⟩ := hv
    fin_cases i
    · exact (by ring : x 1 * x 3 + x 2 * 0 + x 3 * -x 1 = 0)
    · exact (by ring : x 1 * 0 + x 2 * -x 3 + x 3 * x 2 = 0)
    · exact (by ring : x 1 * -x 2 + x 2 * x 1 + x 3 * 0 = 0)
  | zero => simp
  | add u w _ _ hu hw =>
    simp only [Pi.add_apply]
    linear_combination hu + hw
  | smul c u _ hu =>
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination c * hu

/-- In the directions that the three turns span, every step that is not zero has a positive
squared length in Schwarzschild's table: there the table gives the ordinary squared length. -/
theorem schwSpace_pos_on_cartTurns (m : ℝ) {x v : Coords 4}
    (hv : v ∈ Submodule.span ℝ (Set.range fun i : Fin 3 ↦ (Tests.cartTurns i x : Coords 4)))
    (hne : v ≠ 0) : 0 < tableMeasure (schwSpaceG m) x v v := by
  have h0 := Tests.time_part_zero hv
  have hperp := perp_of_mem_span_cartTurns hv
  have hflat := Tests.flat_pos_on_cartTurns hv hne
  rw [Tests.flat_measure_apply, h0] at hflat
  rw [schwSpace_apply, hperp, h0]
  linarith

/-! ## Schwarzschild's whole table is round -/

/-- **Schwarzschild's table in ordinary space labels looks the same from every side** by the
three turns of ordinary space, everywhere off the centre line, for a mass that is zero or
negative. -/
theorem schwSpace_isRoundOn {m : ℝ} (hm : m ≤ 0) :
    IsRoundOn (flatMeasure (tableMeasure (schwSpaceG m))) Tests.cartTurns
      Tests.awayFromCentre := by
  have hM : IsRoundOn (flatMeasure (tableMeasure flatG)) Tests.cartTurns Tests.awayFromCentre :=
    Tests.minkowskiIsRoundOn
  refine ⟨hM.isOpen, hM.smooth, fun i x hx ↦ ?_, hM.likeTurns, hM.surfaces,
    fun x _ v hv hne ↦ schwSpace_pos_on_cartTurns m hv hne⟩
  have hx' : 0 < x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hx)
  obtain ⟨hg, -⟩ := schwSpaceG_slopes hm hx'
  fin_cases i
  · exact (leavesUnchangedAt_table_iff hg (Tests.differentiableAt_cartTurnY x)).mpr
      (cartTurnY_unchanged_schw hm hx')
  · exact (leavesUnchangedAt_table_iff hg (Tests.differentiableAt_cartTurnX x)).mpr
      (cartTurnX_unchanged_schw hm hx')
  · exact (leavesUnchangedAt_table_iff hg (Tests.differentiableAt_cartTurnZ x)).mpr
      (cartTurnZ_unchanged_schw hm hx')

/-! ## "Looks the same from every side" only looks at the fields near each point -/

section Glue

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **"Unchanged along a field" only looks at the field near the point.** If two fields agree
near `q` and moving along one of them leaves the length measure unchanged at `q`, then so does
moving along the other. -/
theorem leavesUnchangedAt_of_eventuallyEq {g : LengthMeasure I M} {ξ η : Arrows I M} {q : M}
    (h : ∀ᶠ y in 𝓝 q, ξ y = η y) (hη : LeavesUnchangedAt g η q) : LeavesUnchangedAt g ξ q := by
  have hq : ξ q = η q := h.self_of_nhds
  have hb : ∀ Z : Arrows I M, mlieBracket I ξ Z q = mlieBracket I η Z q := fun Z ↦ by
    refine Filter.EventuallyEq.mlieBracket_vectorField_eq ?_ Filter.EventuallyEq.rfl
    exact h
  refine ⟨hη.1.congr_of_eventuallyEq (h.mono fun y hy ↦ by simp only [hy]), fun X Y hX hY ↦ ?_⟩
  rw [hq, hb X, hb Y]
  exact hη.2 X Y hX hY

/-- **"Looks the same from every side" only looks at the fields near each point.** If around
every point of the open region `s` there is a smaller region on which the space-time looks the
same from every side by three fields that agree there with the three fields `ξ`, then the
space-time looks the same from every side on `s` by `ξ`. -/
theorem isRoundOn_of_locally {g : LengthMeasure I M} {ξ : Fin 3 → Arrows I M} {s : Set M}
    (hs : IsOpen s)
    (h : ∀ q ∈ s, ∃ (t : Set M) (η : Fin 3 → Arrows I M), q ∈ t ∧ t ⊆ s ∧ IsRoundOn g η t ∧
      ∀ i, ∀ q' ∈ t, ξ i q' = η i q') : IsRoundOn g ξ s where
  isOpen := hs
  smooth := fun i q hq ↦ by
    obtain ⟨t, η, hqt, -, hη, he⟩ := h q hq
    have hev : ∀ᶠ y in 𝓝 q, ξ i y = η i y :=
      Filter.eventually_of_mem (hη.isOpen.mem_nhds hqt) (he i)
    have h1 := (hη.smooth i q hqt).contMDiffAt (hη.isOpen.mem_nhds hqt)
    exact (h1.congr_of_eventuallyEq (hev.mono fun y hy ↦ by simp only [hy])).contMDiffWithinAt
  unchanged := fun i q hq ↦ by
    obtain ⟨t, η, hqt, -, hη, he⟩ := h q hq
    exact leavesUnchangedAt_of_eventuallyEq
      (Filter.eventually_of_mem (hη.isOpen.mem_nhds hqt) (he i)) (hη.unchanged i q hqt)
  likeTurns := fun q hq ↦ by
    obtain ⟨t, η, hqt, -, hη, he⟩ := h q hq
    have hb : ∀ i j, mlieBracket I (ξ i) (ξ j) q = mlieBracket I (η i) (η j) q := fun i j ↦ by
      refine Filter.EventuallyEq.mlieBracket_vectorField_eq ?_ ?_
      · exact Filter.eventually_of_mem (hη.isOpen.mem_nhds hqt) (he i)
      · exact Filter.eventually_of_mem (hη.isOpen.mem_nhds hqt) (he j)
    rw [hb 0 1, hb 1 2, hb 2 0, he 0 q hqt, he 1 q hqt, he 2 q hqt]
    exact hη.likeTurns q hqt
  surfaces := fun q hq ↦ by
    obtain ⟨t, η, hqt, -, hη, he⟩ := h q hq
    have e : (fun i ↦ ξ i q) = fun i ↦ η i q := funext fun i ↦ he i q hqt
    rw [e]
    exact hη.surfaces q hqt
  positive := fun q hq ↦ by
    obtain ⟨t, η, hqt, -, hη, he⟩ := h q hq
    have e : (fun i ↦ ξ i q) = fun i ↦ η i q := funext fun i ↦ he i q hqt
    rw [e]
    exact hη.positive q hqt

end Glue

/-! ## A length-keeping map into Schwarzschild's whole space-time is a chart near each point -/

section Round

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  [IsManifold 𝓘(ℝ, Coords 4) ∞ M] {m : ℝ} {g : LengthMeasure 𝓘(ℝ, Coords 4) M} {s : Set M}

omit [IsManifold 𝓘(ℝ, Coords 4) ∞ M] in
/-- **Chain rule for a map that is, near a point, a map of coordinate space after a map into
coordinate space.** If near `q` the map `D` is `F` after `f`, then `D` carries a step at `q` to
where the slope of `F` carries the step that `f` makes of it. -/
theorem mfderiv_of_eventuallyEq_comp_four {D : M → Coords 4} {F : Coords 4 → Coords 4}
    {f : M → Coords 4} {q : M} (hF : DifferentiableAt ℝ F (f q))
    (hf : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) f q) (hev : D =ᶠ[𝓝 q] F ∘ f)
    (v : TangentSpace 𝓘(ℝ, Coords 4) q) :
    mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D q v
      = fderiv ℝ F (f q) (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) f q v) := by
  have hF' : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) F (f q) := hF.mdifferentiableAt
  have h1 : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) (F ∘ f) q := hF'.comp q hf
  have h2 : mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D q
      = mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) (F ∘ f) q :=
    (h1.hasMFDerivAt.congr_of_eventuallyEq_abuse hev).mfderiv
  have h3 : mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D q v
      = mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) (F ∘ f) q v :=
    congrArg (fun A : Coords 4 →L[ℝ] Coords 4 ↦ A v) h2
  rw [h3, mfderiv_comp_apply q hF' hf v, mfderiv_eq_fderiv]
  rfl

/-- **A length-keeping map into Schwarzschild's whole space-time is itself a chart near each
point.** Around `q`, and inside any open set `U` of coordinate space that contains `D q`, there
is a chart `ψ` of the curved space with domain inside the region, landing in `U`, that is `D` on
its domain. -/
theorem IsSchwarzschildMapOn.exists_chart_self {D : M → Coords 4}
    (hD : IsSchwarzschildMapOn m g D s) (hg : IsSpaceTimeOn g s) {q : M} (hq : q ∈ s)
    {U : Set (Coords 4)} (hU : IsOpen U) (hqU : D q ∈ U) :
    ∃ ψ : OpenPartialHomeomorph M (Coords 4),
      ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M ∧ q ∈ ψ.source ∧ ψ.source ⊆ s ∧
      ψ.target ⊆ U ∧ ∀ q' ∈ ψ.source, ψ q' = D q' := by
  have hinjD := hD.mfderiv_injective hg hq
  obtain ⟨hs, hsm, -⟩ := hD
  -- a chart of the curved space to start from
  obtain ⟨c, hcdef⟩ : ∃ c : OpenPartialHomeomorph M (Coords 4), c = chartAt (Coords 4) q :=
    ⟨_, rfl⟩
  have hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M := by
    rw [hcdef]
    exact IsManifold.chart_mem_maximalAtlas q
  have hqc : q ∈ c.source := by
    rw [hcdef]
    exact mem_chart_source _ q
  have hcsurj : Function.Surjective (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) c q) := by
    rw [hcdef]
    exact (mdifferentiable_chart (I := 𝓘(ℝ, Coords 4)) q).mfderiv_surjective
      (mem_chart_source _ q)
  have hcd : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) c q :=
    (contMDiffAt_of_mem_maximalAtlas hc hqc).mdifferentiableAt (by simp)
  -- the points of the region that `D` sends into `U`, and the same set read in the chart
  have hV : IsOpen (s ∩ D ⁻¹' U) := hsm.continuousOn.isOpen_inter_preimage hs hU
  have hqV : q ∈ s ∩ D ⁻¹' U := ⟨hq, hqU⟩
  have hW : IsOpen (c.target ∩ c.symm ⁻¹' (s ∩ D ⁻¹' U)) := c.isOpen_inter_preimage_symm hV
  have hcqW : c q ∈ c.target ∩ c.symm ⁻¹' (s ∩ D ⁻¹' U) := by
    refine ⟨c.map_source hqc, ?_⟩
    change c.symm (c q) ∈ s ∩ D ⁻¹' U
    rw [c.left_inv hqc]
    exact hqV
  -- the map `Φ`: back to the curved space, then `D`
  have hΦ : ContDiffOn ℝ ∞ (D ∘ c.symm) (c.target ∩ c.symm ⁻¹' (s ∩ D ⁻¹' U)) := by
    have h1 : ContMDiffOn 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) ∞ (D ∘ c.symm)
        (c.target ∩ c.symm ⁻¹' (s ∩ D ⁻¹' U)) :=
      hsm.comp ((contMDiffOn_symm_of_mem_maximalAtlas hc).mono inter_subset_left)
        fun y hy ↦ hy.2.1
    exact contMDiffOn_iff_contDiffOn.1 h1
  have hΦc : ∀ q' ∈ c.source, (D ∘ c.symm) (c q') = D q' := fun q' hq' ↦ by
    change D (c.symm (c q')) = D q'
    rw [c.left_inv hq']
  -- the slope of `Φ` at `c q` carries no step to zero, because `D` carries none to zero
  have hΦd : DifferentiableAt ℝ (D ∘ c.symm) (c q) :=
    (hΦ.contDiffAt (hW.mem_nhds hcqW)).differentiableAt (by simp)
  have hinj : Function.Injective (fderiv ℝ (D ∘ c.symm) (c q)) := by
    refine (injective_iff_map_eq_zero _).mpr fun u hu ↦ ?_
    obtain ⟨v, hv⟩ := hcsurj u
    have hev : D =ᶠ[𝓝 q] (D ∘ c.symm) ∘ c :=
      Filter.eventuallyEq_of_mem (c.open_source.mem_nhds hqc) fun q' hq' ↦ (hΦc q' hq').symm
    have h1 : mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D q v = 0 := by
      rw [mfderiv_of_eventuallyEq_comp_four hΦd hcd hev v, hv, hu]
    have hv0 : v = 0 := hinjD (h1.trans (map_zero _).symm)
    rw [← hv, hv0, map_zero]
  have hunit : IsUnit (fderiv ℝ (D ∘ c.symm) (c q)) :=
    ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.2
      ((LinearMap.isUnit_iff_ker_eq_bot _).2 (LinearMap.ker_eq_bot.2 hinj))
  -- the chart: `Φ` after `c`, near `q`
  obtain ⟨φ, hφ, hqφ, hsub, hφeq, -⟩ :=
    Join.exists_chart_of_localDiffeo hc hqc hV hqV hW hΦ hcqW hunit
  have heq : ∀ q' ∈ φ.source, φ q' = D q' := fun q' hq' ↦ by
    rw [hφeq q']
    exact hΦc q' (hsub hq').1.1
  refine ⟨φ, hφ, hqφ, fun q' hq' ↦ (hsub hq').1.2.1, fun y hy ↦ ?_, heq⟩
  have h1 : φ (φ.symm y) = y := φ.right_inv hy
  have h2 : D (φ.symm y) ∈ U := (hsub (φ.map_target hy)).1.2.2
  rw [← h1, heq _ (φ.map_target hy)]
  exact h2

/-! ## The three fields, defined through the map -/

/-- **The `i`-th turn, brought to the curved space by the map `D`:** at `q`, the step that `D`
carries to the `i`-th turn of ordinary space at the point `D q` (zero if there is no such
step). -/
noncomputable def turnFieldOf (D : M → Coords 4) (i : Fin 3) : Arrows 𝓘(ℝ, Coords 4) M :=
  fun q ↦
    open Classical in
    if h : ∃ v : TangentSpace 𝓘(ℝ, Coords 4) q,
        mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D q v = Tests.cartTurns i (D q)
    then h.choose else 0

omit [IsManifold 𝓘(ℝ, Coords 4) ∞ M] in
/-- **Where `D` is a chart, the fields defined through `D` are the turns taken to the curved
space by that chart.** -/
theorem turnFieldOf_eq_pushField {D : M → Coords 4} {ψ : OpenPartialHomeomorph M (Coords 4)}
    (hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M) {q : M} (hq : q ∈ ψ.source)
    (hinj : Function.Injective (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D q))
    (heq : ∀ q' ∈ ψ.source, ψ q' = D q') (i : Fin 3) :
    turnFieldOf D i q = Join.pushField ψ (Tests.cartTurns i) q := by
  have hd : (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) ψ q : Coords 4 →L[ℝ] Coords 4)
      = mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D q :=
    Filter.EventuallyEq.mfderiv_eq (Filter.eventuallyEq_of_mem (ψ.open_source.mem_nhds hq) heq)
  -- `D` carries the turn taken to the curved space by `ψ` to the turn at `D q`
  have h1 : mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) ψ q
      (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) ψ.symm (ψ q) (Tests.cartTurns i (ψ q)))
        = Tests.cartTurns i (ψ q) :=
    BothWays.mfderiv_symm_comp_at hψ hq _
  have h2 : (Tests.cartTurns i (ψ q) : Coords 4) = Tests.cartTurns i (D q) :=
    congrArg (fun z : Coords 4 ↦ (Tests.cartTurns i z : Coords 4)) (heq q hq)
  have h3 : mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D q (Join.pushField ψ (Tests.cartTurns i) q)
      = mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) ψ q (Join.pushField ψ (Tests.cartTurns i) q) :=
    congrArg (fun A : Coords 4 →L[ℝ] Coords 4 ↦ A (Join.pushField ψ (Tests.cartTurns i) q))
      hd.symm
  have hw : mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D q (Join.pushField ψ (Tests.cartTurns i) q)
      = Tests.cartTurns i (D q) := h3.trans (h1.trans h2)
  -- so the step chosen in the definition exists, and is that one
  have hex : ∃ v : TangentSpace 𝓘(ℝ, Coords 4) q,
      mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D q v = Tests.cartTurns i (D q) := ⟨_, hw⟩
  have hdef : turnFieldOf D i q = hex.choose := dite_eq_left hex
  rw [hdef]
  exact hinj (hex.choose_spec.trans hw.symm)

/-! ## The space-time is round -/

/-- **A space-time with a length-keeping map into Schwarzschild's whole space-time, mass zero or
negative, that misses the centre looks the same from every side.** The three fields are the
turns of ordinary space, brought to the curved space by the map. -/
theorem IsSchwarzschildMapOn.exists_round {D : M → Coords 4} (hm : m ≤ 0)
    (hD : IsSchwarzschildMapOn m g D s) (hg : IsSpaceTimeOn g s)
    (hoff : ∀ q ∈ s, 0 < D q 1 ^ 2 + D q 2 ^ 2 + D q 3 ^ 2) :
    ∃ ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M, IsRoundOn g ξ s := by
  refine ⟨turnFieldOf D, isRoundOn_of_locally (I := 𝓘(ℝ, Coords 4)) hD.1 fun q hq ↦ ?_⟩
  have hqU : D q ∈ Tests.awayFromCentre := (hoff q hq).ne'
  obtain ⟨ψ, hψ, hqψ, hsub, htar, heq⟩ :=
    hD.exists_chart_self hg hq Tests.isOpen_awayFromCentre hqU
  -- in the chart `ψ` the length measure reads as Schwarzschild's table
  have hread : BothWays.ReadsAs ψ g (tableMeasure (schwSpaceG m)) := fun q' hq' v w ↦ by
    have hd : (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) ψ q' : Coords 4 →L[ℝ] Coords 4)
        = mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D q' :=
      Filter.EventuallyEq.mfderiv_eq
        (Filter.eventuallyEq_of_mem (ψ.open_source.mem_nhds hq') heq)
    have key : ∀ (z : Coords 4) (A : Coords 4 →L[ℝ] Coords 4), z = D q' →
        A = mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D q' →
        flatMeasure (tableMeasure (schwSpaceG m)) z (A v) (A w)
          = flatMeasure (tableMeasure (schwSpaceG m)) (D q')
            (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D q' v)
            (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D q' w) := by
      rintro z A rfl rfl
      rfl
    exact ((hD.2.2 q' (hsub hq')).2 v w).trans (key _ _ (heq q' hq') hd).symm
  have hround := BothWays.isRoundOn_pull hψ hread
    (isRoundOn_sub (schwSpace_isRoundOn hm) ψ.open_target htar)
  exact ⟨ψ.source, fun i ↦ Join.pushField ψ (Tests.cartTurns i), hqψ, hsub, hround,
    fun i q' hq' ↦
      turnFieldOf_eq_pushField hψ hq' (hD.mfderiv_injective hg (hsub hq')) heq i⟩

end Round

end GravityInLean.Curved
