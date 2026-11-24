/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Rim.RadiusSmooth
public import GravityInLean.Join.Atlas
public import GravityInLean.Join.UsableSlope
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Schwarzschild's space-time inside the rim is a piece of Kruskal's

Board item `task:rim-schw-inside`. Half of `KruskalHoldsSchwarzschild`: around every point
inside the rim, Schwarzschild's length measure for a positive mass is Kruskal's in some chart.

The chart is the map `insideMap m`: it sends Schwarzschild's labels `(t, r, θ, φ)` with
`0 < r < 2m` to Kruskal's labels `(T, X, θ, φ)` with

* `T = √(-F) · cosh (t / 4m)` and `X = √(-F) · sinh (t / 4m)`, where `F = kruskalF m r`.

Inside the rim `-1 < F < 0`, so the square root is that of a positive number, `X² - T² = F`,
and Kruskal's radius at the new point is `r` again. The file shows that the map is smooth
(`contDiffOn_insideMap`), gives its slope (`insideMap_slope`), shows that the slope can be
undone (`insideMap_isUnit`), and checks by a computation with the four parts of a step that
Schwarzschild's table gives two steps the length that Kruskal's table gives to the two steps as
the map sees them (`insideMap_measure`). The chart itself then comes from
`Join.exists_chart_of_localDiffeo` (`kruskalHoldsSchwarzschild_inside`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean

open Set

open scoped Manifold ContDiff

namespace Curved

/-! ## Plain algebra -/

/-- Two numbers `p`, `q` that the slope of the map sends to zero are zero: the two equations
have a determinant that is not zero. -/
theorem inside_kernel {s ch sh k F' p q : ℝ} (hs : s ≠ 0) (hk : 0 < k) (hF' : 0 < F')
    (hc : ch ^ 2 = sh ^ 2 + 1)
    (h0 : s * (sh * k) * p + ch * (-F' / (2 * s)) * q = 0)
    (h1 : s * (ch * k) * p + sh * (-F' / (2 * s)) * q = 0) : p = 0 ∧ q = 0 := by
  have hs' : s * (-F' / (2 * s)) = -F' / 2 := by field_simp
  have hp : p * (k * F' / 2) = 0 := by
    linear_combination (sh * (-F' / (2 * s))) * h0 - (ch * (-F' / (2 * s))) * h1
      + p * (-k * (sh ^ 2 - ch ^ 2)) * hs' - p * (k * F' / 2) * hc
  have hq : q * (k * F' / 2) = 0 := by
    linear_combination (s * (sh * k)) * h1 - (s * (ch * k)) * h0
      + q * (-k * (sh ^ 2 - ch ^ 2)) * hs' - q * (k * F' / 2) * hc
  have hne : k * F' / 2 ≠ 0 := by positivity
  exact ⟨(mul_eq_zero.1 hp).resolve_right hne, (mul_eq_zero.1 hq).resolve_right hne⟩

/-- The computation behind the change of labels: Kruskal's `-K dT² + K dX²`, with the slopes
of `T` and `X` put in, is `-a dt² + b dr²`, given what the factors multiply out to. -/
theorem inside_alg {K k s s' ch sh P a b v0 v1 w0 w1 : ℝ} (hc : ch ^ 2 = sh ^ 2 + 1)
    (hs2 : s ^ 2 = P) (c0 : K * (P * k ^ 2) = -a) (c1 : K * s' ^ 2 = -b) :
    -K * (s * (sh * k) * v0 + ch * s' * v1) * (s * (sh * k) * w0 + ch * s' * w1)
        + K * (s * (ch * k) * v0 + sh * s' * v1) * (s * (ch * k) * w0 + sh * s' * w1)
      = -a * v0 * w0 + b * v1 * w1 := by
  linear_combination (K * s ^ 2 * k ^ 2 * (v0 * w0) - K * s' ^ 2 * (v1 * w1)) * hc
    + (K * k ^ 2 * (v0 * w0)) * hs2 + (v0 * w0) * c0 - (v1 * w1) * c1

/-- The factor in front of `dt²`: Kruskal's factor times `-F / (4m)²` is `-(1 - 2m / r)`. -/
theorem inside_coef0 {m r E : ℝ} (hm : 0 < m) (hr : 0 < r) (hE : 0 < E) :
    32 * m ^ 3 / r * E⁻¹ * ((1 - r / (2 * m)) * E * (1 / (4 * m)) ^ 2)
      = -(1 - 2 * m / r) := by
  have hm' : m ≠ 0 := hm.ne'
  have hr' : r ≠ 0 := hr.ne'
  have hE' : E ≠ 0 := hE.ne'
  field_simp
  ring

/-- The factor in front of `dr²`: Kruskal's factor times the squared slope of `√(-F)` is
`-1 / (1 - 2m / r)`. -/
theorem inside_coef1 {m r E s : ℝ} (hm : 0 < m) (hr : 0 < r) (hr2 : r < 2 * m) (hE : 0 < E)
    (hs2 : s ^ 2 = (1 - r / (2 * m)) * E) :
    32 * m ^ 3 / r * E⁻¹ * (-(r / (4 * m ^ 2) * E) / (2 * s)) ^ 2
      = -(1 - 2 * m / r)⁻¹ := by
  have hm' : m ≠ 0 := hm.ne'
  have hr' : r ≠ 0 := hr.ne'
  have hE' : E ≠ 0 := hE.ne'
  have h1 : 1 - r / (2 * m) ≠ 0 := by
    have h : 0 < 1 - r / (2 * m) := by
      rw [sub_pos, div_lt_one (by positivity)]
      exact hr2
    exact h.ne'
  -- the two factors `1 - 2m / r` and `1 - r / 2m` differ by the factor `-2m / r`
  have hD : 1 - 2 * m / r = -(2 * m / r) * (1 - r / (2 * m)) := by
    field_simp
    ring
  have gen : (-(r / (4 * m ^ 2) * E) / (2 * s)) ^ 2
      = (r / (4 * m ^ 2) * E) ^ 2 / (4 * ((1 - r / (2 * m)) * E)) := by
    rw [← hs2, div_pow, neg_sq, mul_pow (2 : ℝ) s]
    norm_num
  rw [gen, hD]
  generalize 1 - r / (2 * m) = P at h1 ⊢
  field_simp
  ring

/-! ## The map -/

/-- Inside the rim `kruskalF m r` is negative. -/
theorem kruskalF_neg_inside {m r : ℝ} (hm : 0 < m) (hr : r < 2 * m) : kruskalF m r < 0 := by
  have h1 : r / (2 * m) - 1 < 0 := by
    rw [sub_neg, div_lt_one (by positivity)]
    exact hr
  unfold kruskalF
  exact mul_neg_of_neg_of_pos h1 (Real.exp_pos _)

/-- **The map from Schwarzschild's labels inside the rim to Kruskal's labels:**
`T = √(-F) · cosh (t / 4m)`, `X = √(-F) · sinh (t / 4m)` with `F = kruskalF m r`. The two
angles stay as they are. -/
noncomputable def insideMap (m : ℝ) (x : Coords 4) : Coords 4 :=
  ![√(-kruskalF m (x 1)) * Real.cosh (x 0 / (4 * m)),
    √(-kruskalF m (x 1)) * Real.sinh (x 0 / (4 * m)), x 2, x 3]

/-- At the new point, `X² - T²` is `kruskalF m r`. -/
theorem insideMap_sq_sub_sq {m : ℝ} (hm : 0 < m) {x : Coords 4} (hx : x ∈ inside m) :
    insideMap m x 1 ^ 2 - insideMap m x 0 ^ 2 = kruskalF m (x 1) := by
  have hs : √(-kruskalF m (x 1)) ^ 2 = -kruskalF m (x 1) :=
    Real.sq_sqrt (neg_nonneg.2 (kruskalF_neg_inside hm hx.2.1).le)
  have hc := Real.cosh_sq (x 0 / (4 * m))
  change (√(-kruskalF m (x 1)) * Real.sinh (x 0 / (4 * m))) ^ 2
    - (√(-kruskalF m (x 1)) * Real.cosh (x 0 / (4 * m))) ^ 2 = kruskalF m (x 1)
  linear_combination (-1 : ℝ) * hs - √(-kruskalF m (x 1)) ^ 2 * hc

/-- The map sends the inside of the rim into Kruskal's region. -/
theorem insideMap_mem_kruskalRegion {m : ℝ} (hm : 0 < m) {x : Coords 4} (hx : x ∈ inside m) :
    insideMap m x ∈ kruskalRegion := by
  have h := neg_one_lt_kruskalF hm hx.1
  rw [← insideMap_sq_sub_sq hm hx] at h
  exact ⟨h, hx.2.2⟩

/-- The map is smooth inside the rim. -/
theorem contDiffOn_insideMap {m : ℝ} (hm : 0 < m) :
    ContDiffOn ℝ ∞ (insideMap m) (inside m) := by
  have hF0 : ContDiff ℝ ∞ (fun r : ℝ ↦ (r / (2 * m) - 1) * Real.exp (r / (2 * m))) := by
    fun_prop
  have hF : ContDiff ℝ ∞ (kruskalF m) := hF0
  intro x hx
  have hx0 : ContDiffAt ℝ ∞ (fun y : Coords 4 ↦ y 0 / (4 * m)) x :=
    (contDiff_apply ℝ (fun _ : Fin 4 ↦ ℝ) 0).contDiffAt.div_const _
  have hx1 : ContDiffAt ℝ ∞ (fun y : Coords 4 ↦ -kruskalF m (y 1)) x :=
    (hF.contDiffAt.comp x (contDiff_apply ℝ (fun _ : Fin 4 ↦ ℝ) 1).contDiffAt).neg
  have hs : ContDiffAt ℝ ∞ (fun y : Coords 4 ↦ √(-kruskalF m (y 1))) x :=
    hx1.sqrt (neg_pos.2 (kruskalF_neg_inside hm hx.2.1)).ne'
  refine ContDiffAt.contDiffWithinAt (contDiffAt_pi.2 fun i ↦ ?_)
  fin_cases i
  · exact hs.mul hx0.cosh
  · exact hs.mul hx0.sinh
  · exact (contDiff_apply ℝ (fun _ : Fin 4 ↦ ℝ) 2).contDiffAt
  · exact (contDiff_apply ℝ (fun _ : Fin 4 ↦ ℝ) 3).contDiffAt

/-- The slope of a product of a function of the distance label and a function of the time
label, along any step. -/
theorem inside_hasFDerivAt_mul {g h : ℝ → ℝ} {g' h' : ℝ} {x : Coords 4}
    (hg : HasDerivAt g g' (x 1)) (hh : HasDerivAt h h' (x 0)) :
    ∃ L : Coords 4 →L[ℝ] ℝ, HasFDerivAt (fun y : Coords 4 ↦ g (y 1) * h (y 0)) L x ∧
      ∀ v : Coords 4, L v = g (x 1) * h' * v 0 + h (x 0) * g' * v 1 := by
  have h1 : HasFDerivAt (fun y : Coords 4 ↦ y 1) (coordL 1) x :=
    (coordL (n := 4) 1).hasFDerivAt
  have h0 : HasFDerivAt (fun y : Coords 4 ↦ y 0) (coordL 0) x :=
    (coordL (n := 4) 0).hasFDerivAt
  have hg1 : HasFDerivAt (fun y : Coords 4 ↦ g (y 1)) (g' • coordL 1) x :=
    hg.comp_hasFDerivAt x h1
  have hh0 : HasFDerivAt (fun y : Coords 4 ↦ h (y 0)) (h' • coordL 0) x :=
    hh.comp_hasFDerivAt x h0
  refine ⟨g (x 1) • (h' • coordL 0) + h (x 0) • (g' • coordL 1), hg1.mul hh0, fun v ↦ ?_⟩
  change g (x 1) * (h' * v 0) + h (x 0) * (g' * v 1) = _
  ring

/-- **The slope of the map** at a point inside the rim, with the four parts of the step it
gives written out. -/
theorem insideMap_slope {m : ℝ} (hm : 0 < m) {x : Coords 4} (hx : x ∈ inside m) :
    ∃ L : Coords 4 →L[ℝ] Coords 4, HasFDerivAt (insideMap m) L x ∧ ∀ v : Coords 4,
      L v 0 = √(-kruskalF m (x 1)) * (Real.sinh (x 0 / (4 * m)) * (1 / (4 * m))) * v 0
        + Real.cosh (x 0 / (4 * m))
          * (-(x 1 / (4 * m ^ 2) * Real.exp (x 1 / (2 * m))) / (2 * √(-kruskalF m (x 1))))
          * v 1 ∧
      L v 1 = √(-kruskalF m (x 1)) * (Real.cosh (x 0 / (4 * m)) * (1 / (4 * m))) * v 0
        + Real.sinh (x 0 / (4 * m))
          * (-(x 1 / (4 * m ^ 2) * Real.exp (x 1 / (2 * m))) / (2 * √(-kruskalF m (x 1))))
          * v 1 ∧
      L v 2 = v 2 ∧ L v 3 = v 3 := by
  have hs : HasDerivAt (fun r : ℝ ↦ √(-kruskalF m r))
      (-(x 1 / (4 * m ^ 2) * Real.exp (x 1 / (2 * m))) / (2 * √(-kruskalF m (x 1)))) (x 1) :=
    (hasDerivAt_kruskalF hm.ne' (x 1)).neg.sqrt
      (neg_pos.2 (kruskalF_neg_inside hm hx.2.1)).ne'
  have hk : HasDerivAt (fun t : ℝ ↦ t / (4 * m)) (1 / (4 * m)) (x 0) :=
    (hasDerivAt_id (x 0)).div_const (4 * m)
  obtain ⟨L0, hL0, e0⟩ := inside_hasFDerivAt_mul hs hk.cosh
  obtain ⟨L1, hL1, e1⟩ := inside_hasFDerivAt_mul hs hk.sinh
  refine ⟨ContinuousLinearMap.pi ![L0, L1, coordL 2, coordL 3], ?_,
    fun v ↦ ⟨e0 v, e1 v, rfl, rfl⟩⟩
  refine (hasFDerivAt_pi (φ := fun i y ↦ insideMap m y i)
    (φ' := ![L0, L1, coordL 2, coordL 3])).2 fun i ↦ ?_
  fin_cases i
  · exact hL0
  · exact hL1
  · exact (coordL (n := 4) 2).hasFDerivAt
  · exact (coordL (n := 4) 3).hasFDerivAt

/-- **The slope of the map can be undone** at every point inside the rim. -/
theorem insideMap_isUnit {m : ℝ} (hm : 0 < m) {x : Coords 4} (hx : x ∈ inside m) :
    IsUnit (fderiv ℝ (insideMap m) x) := by
  obtain ⟨L, hL, hLv⟩ := insideMap_slope hm hx
  rw [hL.fderiv]
  have hs : 0 < √(-kruskalF m (x 1)) :=
    Real.sqrt_pos.2 (neg_pos.2 (kruskalF_neg_inside hm hx.2.1))
  have hF' : 0 < x 1 / (4 * m ^ 2) * Real.exp (x 1 / (2 * m)) :=
    mul_pos (div_pos hx.1 (by positivity)) (Real.exp_pos _)
  have hk : 0 < 1 / (4 * m) := by positivity
  refine ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.2
    ((LinearMap.isUnit_iff_ker_eq_bot _).2 (LinearMap.ker_eq_bot'.2 fun v hv ↦ ?_))
  have hv' : L v = 0 := hv
  obtain ⟨e0, e1, e2, e3⟩ := hLv v
  rw [hv'] at e0 e1 e2 e3
  obtain ⟨h0, h1⟩ :=
    inside_kernel hs.ne' hk hF' (Real.cosh_sq (x 0 / (4 * m))) e0.symm e1.symm
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact e2.symm
  · exact e3.symm

/-! ## The two tables agree along the map -/

/-- The measure of a round table, written out with the four parts of the two steps. -/
theorem inside_round_measure (A B : ℝ → ℝ) (x v w : Coords 4) :
    tableMeasure (roundG A B) x v w
      = -A (x 1) * v 0 * w 0 + B (x 1) * v 1 * w 1 + x 1 ^ 2 * v 2 * w 2
        + x 1 ^ 2 * Real.sin (x 2) ^ 2 * v 3 * w 3 := by
  rw [round_measure_apply]
  simp +decide only [Fin.sum_univ_four, roundDiag, sep, gr, gθ, negF, sqF, sin2, constOne,
    ite_true, ite_false]
  ring

/-- **Schwarzschild's table inside the rim is Kruskal's table along the map.** Two steps at a
point inside the rim have, measured with Schwarzschild's table, the length that Kruskal's table
gives at the new point to the two steps as the map sees them. -/
theorem insideMap_measure {m : ℝ} (hm : 0 < m) {q : Coords 4} (hq : q ∈ inside m)
    {y : Coords 4} (hy : y = insideMap m q) (v w : Coords 4) :
    tableMeasure (roundG (schwA m) (schwB m)) q v w
      = tableMeasure (kruskalG m) y (fderiv ℝ (insideMap m) q v)
        (fderiv ℝ (insideMap m) q w) := by
  subst hy
  obtain ⟨L, hL, hLv⟩ := insideMap_slope hm hq
  obtain ⟨a0, a1, a2, a3⟩ := hLv v
  obtain ⟨b0, b1, b2, b3⟩ := hLv w
  have hF : kruskalF m (q 1) < 0 := kruskalF_neg_inside hm hq.2.1
  -- Kruskal's radius at the new point is the old distance label
  have hR : kruskalR m (insideMap m q 1 ^ 2 - insideMap m q 0 ^ 2) = q 1 := by
    rw [insideMap_sq_sub_sq hm hq, kruskalR_kruskalF hm hq.1]
  have hA : kruskalA m (insideMap m q 0) (insideMap m q 1)
      = 32 * m ^ 3 / q 1 * (Real.exp (q 1 / (2 * m)))⁻¹ := by
    unfold kruskalA
    rw [hR, neg_div, Real.exp_neg]
  have hS : kruskalS m (insideMap m q 0) (insideMap m q 1) = q 1 ^ 2 := by
    unfold kruskalS
    rw [hR]
  have h2 : insideMap m q 2 = q 2 := rfl
  have hs2 : √(-kruskalF m (q 1)) ^ 2
      = (1 - q 1 / (2 * m)) * Real.exp (q 1 / (2 * m)) := by
    rw [Real.sq_sqrt (neg_nonneg.2 hF.le)]
    unfold kruskalF
    ring
  have key := inside_alg (v0 := v 0) (v1 := v 1) (w0 := w 0) (w1 := w 1)
    (Real.cosh_sq (q 0 / (4 * m))) hs2
    (inside_coef0 hm hq.1 (Real.exp_pos (q 1 / (2 * m))))
    (inside_coef1 hm hq.1 hq.2.1 (Real.exp_pos (q 1 / (2 * m))) hs2)
  rw [hL.fderiv, inside_round_measure,
    Join.tableMeasure_of_genG (h := kruskalG m) (A := kruskalA m) (B := kruskalA m)
      (C := zero2) (S := kruskalS m) (fun _ _ ↦ rfl),
    hA, hS, h2, a0, a1, a2, a3, b0, b1, b2, b3]
  unfold schwA schwB zero2
  linear_combination (-1 : ℝ) * key

/-! ## The chart -/

/-- **Schwarzschild's space-time inside the rim is, near each of its points, a piece of
Kruskal's:** for a positive mass, around every point inside the rim there is a chart into
Kruskal's region in which Schwarzschild's length measure is Kruskal's. -/
theorem kruskalHoldsSchwarzschild_inside {m : ℝ} (hm : 0 < m) {p : Coords 4}
    (hp : p ∈ inside m) :
    IsKruskalNear m (flatMeasure (tableMeasure (roundG (schwA m) (schwB m)))) p := by
  obtain ⟨φ, hφ, hpφ, hsrc, hφeq, hmf⟩ :=
    Join.exists_chart_of_localDiffeo (M := Coords 4)
      (c := OpenPartialHomeomorph.ofSet (inside m) (isOpen_inside m))
      (StructureGroupoid.mem_maximalAtlas_of_mem_groupoid _
        (ofSet_mem_contDiffGroupoid (isOpen_inside m)))
      (p := p) hp (isOpen_inside m) hp (isOpen_inside m) (contDiffOn_insideMap hm) hp
      (insideMap_isUnit hm hp)
  refine ⟨φ, hφ, hpφ, fun q hq ↦ ?_⟩
  have hq' : q ∈ inside m := (hsrc hq).1.2
  have hφq : φ q = insideMap m q := hφeq q
  refine ⟨?_, fun v w ↦ ?_⟩
  · rw [hφq]
    exact insideMap_mem_kruskalRegion hm hq'
  · have e : mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4)
        (OpenPartialHomeomorph.ofSet (inside m) (isOpen_inside m)) q
        = ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, Coords 4) q) := mfderiv_id
    rw [hmf q hq v, hmf q hq w, e]
    exact insideMap_measure hm hq' hφq v w

end Curved

end GravityInLean
