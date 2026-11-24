/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Rim.RadiusSmooth
public import GravityInLean.Join.Atlas
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Schwarzschild's space-time outside the rim is a piece of Kruskal's

Board item `task:rim-schw-outside`. Half of `KruskalHoldsSchwarzschild`: around every point of
Schwarzschild's space-time outside the rim (`r > 2m`, positive mass) there is a chart in which
its length measure is Kruskal's.

The chart is the map `kruskalOut m`: it sends the time `t` and the radius `r` to Kruskal's labels

  `T = √F · sinh (t / 4m)`,  `X = √F · cosh (t / 4m)`,  with `F = kruskalF m r > 0`,

and leaves the two angles alone. Then `X² - T² = F`, so Kruskal's radius at the new point is `r`
again. The slope of the map can be undone, because `cosh² - sinh² = 1`. And a computation with
the slope of `kruskalF` shows that Kruskal's table, at the new point, gives the steps as the map
sees them the length that Schwarzschild's table gives the steps themselves.

Every name in this file carries `Out` or `outside`; the file for the inside of the rim is
separate.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean

open Real Set

open scoped Manifold ContDiff Topology

namespace Curved

/-! ## The map -/

/-- Outside the rim (`r > 2m`, positive mass) the number `kruskalF m r` is positive. -/
theorem kruskalF_pos_outside {m r : ℝ} (hm : 0 < m) (hr : 2 * m < r) : 0 < kruskalF m r := by
  have h : 0 < r / (2 * m) - 1 := by
    rw [sub_pos, one_lt_div (by positivity)]
    exact hr
  exact mul_pos h (Real.exp_pos _)

/-- `kruskalF m` is smooth, as a function of the radius. -/
theorem contDiff_kruskalF_outside (m : ℝ) : ContDiff ℝ ∞ (kruskalF m) := by
  have h : ContDiff ℝ ∞ fun r : ℝ ↦ (r / (2 * m) - 1) * Real.exp (r / (2 * m)) := by fun_prop
  exact h

/-- **From Schwarzschild's coordinates to Kruskal's, outside the rim.** The time `t` and the
radius `r` go to `T = √F · sinh (t / 4m)` and `X = √F · cosh (t / 4m)` with `F = kruskalF m r`;
the two angles stay. -/
noncomputable def kruskalOut (m : ℝ) (x : Coords 4) : Coords 4 :=
  ![√(kruskalF m (x 1)) * sinh (x 0 / (4 * m)), √(kruskalF m (x 1)) * cosh (x 0 / (4 * m)),
    x 2, x 3]

/-- The slope of `√F` along the radius: `F' / (2 √F)` with `F' = (r / 4m²) · exp (r / 2m)`. -/
noncomputable def kruskalOutD (m r : ℝ) : ℝ :=
  r / (4 * m ^ 2) * Real.exp (r / (2 * m)) / (2 * √(kruskalF m r))

/-- Outside the rim the slope of `√F` along the radius is positive. -/
theorem kruskalOutD_pos {m r : ℝ} (hm : 0 < m) (hr : 2 * m < r) : 0 < kruskalOutD m r := by
  have hr0 : 0 < r := by linarith
  exact div_pos (mul_pos (div_pos hr0 (by positivity)) (Real.exp_pos _))
    (mul_pos two_pos (Real.sqrt_pos.2 (kruskalF_pos_outside hm hr)))

/-- At the new point `X² - T²` is `kruskalF m r`. -/
theorem kruskalOut_sq_sub {m r : ℝ} (hm : 0 < m) (hr : 2 * m < r) (τ : ℝ) :
    (√(kruskalF m r) * cosh τ) ^ 2 - (√(kruskalF m r) * sinh τ) ^ 2 = kruskalF m r := by
  rw [mul_pow, mul_pow, Real.sq_sqrt (kruskalF_pos_outside hm hr).le, Real.cosh_sq]
  ring

/-- At the new point Kruskal's radius is Schwarzschild's radius `r`. -/
theorem kruskalR_kruskalOut {m r : ℝ} (hm : 0 < m) (hr : 2 * m < r) (τ : ℝ) :
    kruskalR m ((√(kruskalF m r) * cosh τ) ^ 2 - (√(kruskalF m r) * sinh τ) ^ 2) = r := by
  rw [kruskalOut_sq_sub hm hr, kruskalR_kruskalF hm (by linarith)]

/-- The map sends the outside of the rim into Kruskal's region. -/
theorem kruskalOut_mem_kruskalRegion {m : ℝ} (hm : 0 < m) {x : Coords 4} (hx : x ∈ outside m) :
    kruskalOut m x ∈ kruskalRegion := by
  have h : -1 < (√(kruskalF m (x 1)) * cosh (x 0 / (4 * m))) ^ 2
      - (√(kruskalF m (x 1)) * sinh (x 0 / (4 * m))) ^ 2 := by
    rw [kruskalOut_sq_sub hm hx.2.1]
    linarith [kruskalF_pos_outside hm hx.2.1]
  exact ⟨h, hx.2.2⟩

/-- The map is smooth outside the rim. -/
theorem contDiffOn_kruskalOut {m : ℝ} (hm : 0 < m) :
    ContDiffOn ℝ ∞ (kruskalOut m) (outside m) := by
  intro x hx
  have hpr : ∀ i : Fin 4, ContDiff ℝ ∞ fun y : Coords 4 ↦ y i := fun i ↦
    contDiff_apply ℝ (fun _ : Fin 4 ↦ ℝ) i
  have hs : ContDiffAt ℝ ∞ (fun y : Coords 4 ↦ √(kruskalF m (y 1))) x := by
    have h1 : ContDiffAt ℝ ∞ (fun y : Coords 4 ↦ kruskalF m (y 1)) x :=
      ((contDiff_kruskalF_outside m).comp (hpr 1)).contDiffAt
    exact h1.sqrt (kruskalF_pos_outside hm hx.2.1).ne'
  have hsh : ContDiffAt ℝ ∞ (fun y : Coords 4 ↦ sinh (y 0 / (4 * m))) x :=
    (Real.contDiff_sinh.comp ((hpr 0).div_const (4 * m))).contDiffAt
  have hch : ContDiffAt ℝ ∞ (fun y : Coords 4 ↦ cosh (y 0 / (4 * m))) x :=
    (Real.contDiff_cosh.comp ((hpr 0).div_const (4 * m))).contDiffAt
  refine (contDiffAt_pi.2 fun i ↦ ?_).contDiffWithinAt
  fin_cases i
  · exact hs.mul hsh
  · exact hs.mul hch
  · exact (hpr 2).contDiffAt
  · exact (hpr 3).contDiffAt

/-! ## Its slope -/

/-- **The slope of the map,** applied to a step `v`: the time and radius parts of `v` mix into
the parts along `T` and `X`; the parts along the angles stay. -/
theorem fderiv_kruskalOut_apply {m : ℝ} (hm : 0 < m) {x : Coords 4} (hx : x ∈ outside m)
    (v : Coords 4) :
    fderiv ℝ (kruskalOut m) x v
      = ![√(kruskalF m (x 1)) * (cosh (x 0 / (4 * m)) * (1 / (4 * m))) * v 0
            + sinh (x 0 / (4 * m)) * kruskalOutD m (x 1) * v 1,
          √(kruskalF m (x 1)) * (sinh (x 0 / (4 * m)) * (1 / (4 * m))) * v 0
            + cosh (x 0 / (4 * m)) * kruskalOutD m (x 1) * v 1,
          v 2, v 3] := by
  have hd : DifferentiableAt ℝ (kruskalOut m) x :=
    ((contDiffOn_kruskalOut hm).contDiffAt ((isOpen_outside m).mem_nhds hx)).differentiableAt
      (by simp)
  -- part `i` of the slope is the slope of part `i`
  have key : ∀ i : Fin 4,
      fderiv ℝ (kruskalOut m) x v i = fderiv ℝ (fun y ↦ kruskalOut m y i) x v := fun i ↦ by
    rw [fderiv_apply hd i]
    rfl
  -- the slope of `√F`, as a function of the point
  have hg : HasDerivAt (fun r ↦ √(kruskalF m r)) (kruskalOutD m (x 1)) (x 1) :=
    (hasDerivAt_kruskalF hm.ne' (x 1)).sqrt (kruskalF_pos_outside hm hx.2.1).ne'
  have hs : HasFDerivAt (fun y : Coords 4 ↦ √(kruskalF m (y 1)))
      (kruskalOutD m (x 1) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 ↦ ℝ) 1) x :=
    HasDerivAt.comp_hasFDerivAt (f := fun y : Coords 4 ↦ y 1) x hg
      (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 4) x)
  -- the slopes of `sinh (t / 4m)` and `cosh (t / 4m)`, as functions of the point
  have hsh1 : HasDerivAt (fun t ↦ sinh (t / (4 * m))) (cosh (x 0 / (4 * m)) * (1 / (4 * m)))
      (x 0) :=
    (Real.hasDerivAt_sinh _).comp (x 0) ((hasDerivAt_id' (x 0)).div_const (4 * m))
  have hch1 : HasDerivAt (fun t ↦ cosh (t / (4 * m))) (sinh (x 0 / (4 * m)) * (1 / (4 * m)))
      (x 0) :=
    (Real.hasDerivAt_cosh _).comp (x 0) ((hasDerivAt_id' (x 0)).div_const (4 * m))
  have hsh : HasFDerivAt (fun y : Coords 4 ↦ sinh (y 0 / (4 * m)))
      ((cosh (x 0 / (4 * m)) * (1 / (4 * m)))
        • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 ↦ ℝ) 0) x :=
    HasDerivAt.comp_hasFDerivAt (f := fun y : Coords 4 ↦ y 0) x hsh1
      (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) x)
  have hch : HasFDerivAt (fun y : Coords 4 ↦ cosh (y 0 / (4 * m)))
      ((sinh (x 0 / (4 * m)) * (1 / (4 * m)))
        • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 ↦ ℝ) 0) x :=
    HasDerivAt.comp_hasFDerivAt (f := fun y : Coords 4 ↦ y 0) x hch1
      (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) x)
  -- the four parts
  have h0 : HasFDerivAt (fun y : Coords 4 ↦ kruskalOut m y 0) _ x := hs.mul hsh
  have h1 : HasFDerivAt (fun y : Coords 4 ↦ kruskalOut m y 1) _ x := hs.mul hch
  have h2 : HasFDerivAt (fun y : Coords 4 ↦ kruskalOut m y 2) _ x :=
    hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) x
  have h3 : HasFDerivAt (fun y : Coords 4 ↦ kruskalOut m y 3) _ x :=
    hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) x
  have c0 : fderiv ℝ (kruskalOut m) x v 0
      = √(kruskalF m (x 1)) * (cosh (x 0 / (4 * m)) * (1 / (4 * m))) * v 0
        + sinh (x 0 / (4 * m)) * kruskalOutD m (x 1) * v 1 := by
    rw [key, h0.fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    ring
  have c1 : fderiv ℝ (kruskalOut m) x v 1
      = √(kruskalF m (x 1)) * (sinh (x 0 / (4 * m)) * (1 / (4 * m))) * v 0
        + cosh (x 0 / (4 * m)) * kruskalOutD m (x 1) * v 1 := by
    rw [key, h1.fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    ring
  have c2 : fderiv ℝ (kruskalOut m) x v 2 = v 2 := by
    rw [key, h2.fderiv]
    rfl
  have c3 : fderiv ℝ (kruskalOut m) x v 3 = v 3 := by
    rw [key, h3.fderiv]
    rfl
  funext i
  fin_cases i
  exacts [c0, c1, c2, c3]

/-- **The slope of the map can be undone** at every point outside the rim: a step that the map
sees as no step is no step, because `cosh² - sinh² = 1`. -/
theorem isUnit_fderiv_kruskalOut {m : ℝ} (hm : 0 < m) {x : Coords 4} (hx : x ∈ outside m) :
    IsUnit (fderiv ℝ (kruskalOut m) x) := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot,
    LinearMap.ker_eq_bot']
  intro v hv
  have hv' : fderiv ℝ (kruskalOut m) x v = 0 := hv
  rw [fderiv_kruskalOut_apply hm hx v] at hv'
  have e0 : √(kruskalF m (x 1)) * (cosh (x 0 / (4 * m)) * (1 / (4 * m))) * v 0
      + sinh (x 0 / (4 * m)) * kruskalOutD m (x 1) * v 1 = 0 := congrFun hv' 0
  have e1 : √(kruskalF m (x 1)) * (sinh (x 0 / (4 * m)) * (1 / (4 * m))) * v 0
      + cosh (x 0 / (4 * m)) * kruskalOutD m (x 1) * v 1 = 0 := congrFun hv' 1
  have e2 : v 2 = 0 := congrFun hv' 2
  have e3 : v 3 = 0 := congrFun hv' 3
  have hcs : cosh (x 0 / (4 * m)) ^ 2 - sinh (x 0 / (4 * m)) ^ 2 = 1 := by
    rw [Real.cosh_sq]
    ring
  have hs : √(kruskalF m (x 1)) ≠ 0 := (Real.sqrt_pos.2 (kruskalF_pos_outside hm hx.2.1)).ne'
  have hk : 1 / (4 * m) ≠ 0 := by positivity
  have hD : kruskalOutD m (x 1) ≠ 0 := (kruskalOutD_pos hm hx.2.1).ne'
  have p0 : √(kruskalF m (x 1)) * (1 / (4 * m)) * v 0 = 0 := by
    linear_combination cosh (x 0 / (4 * m)) * e0 - sinh (x 0 / (4 * m)) * e1
      - √(kruskalF m (x 1)) * (1 / (4 * m)) * v 0 * hcs
  have p1 : kruskalOutD m (x 1) * v 1 = 0 := by
    linear_combination cosh (x 0 / (4 * m)) * e1 - sinh (x 0 / (4 * m)) * e0
      - kruskalOutD m (x 1) * v 1 * hcs
  have q0 : v 0 = 0 := (mul_eq_zero.1 p0).resolve_left (mul_ne_zero hs hk)
  have q1 : v 1 = 0 := (mul_eq_zero.1 p1).resolve_left hD
  funext i
  fin_cases i
  exacts [q0, q1, e2, e3]

/-! ## The two tables, written out -/

/-- Schwarzschild's length measure of two steps, written out. -/
theorem schwOut_measure_apply (m : ℝ) (x v w : Coords 4) :
    tableMeasure (roundG (schwA m) (schwB m)) x v w
      = -schwA m (x 1) * v 0 * w 0 + schwB m (x 1) * v 1 * w 1 + x 1 ^ 2 * v 2 * w 2
        + x 1 ^ 2 * sin (x 2) ^ 2 * v 3 * w 3 := by
  simp only [tableMeasure, formOf_apply, Fin.sum_univ_four]
  simp [roundG, diag, roundDiag, sep, gr, gθ, negF, sqF, sin2, constOne]

/-- Kruskal's length measure of two steps, written out, at a point and for steps given by
their four parts. -/
theorem kruskalOut_measure_apply (m T X θ φ a b c d a' b' c' d' : ℝ) :
    tableMeasure (kruskalG m) ![T, X, θ, φ] ![a, b, c, d] ![a', b', c', d']
      = -kruskalA m T X * a * a' + kruskalA m T X * b * b' + kruskalS m T X * c * c'
        + kruskalS m T X * sin θ ^ 2 * d * d' := by
  simp only [tableMeasure, formOf_apply, Fin.sum_univ_four]
  simp [kruskalG, genG, sep2, gTR, gΘ, negA, zero2, sin2, constOne]

/-! ## The computation -/

/-- Kruskal's factor times the square of the slope of the map along time is Schwarzschild's
clock function `1 - 2m/r`. -/
theorem kruskalOut_factor_time {m r : ℝ} (hm : 0 < m) (hr : 2 * m < r) :
    32 * m ^ 3 / r * Real.exp (-r / (2 * m)) * √(kruskalF m r) ^ 2 * (1 / (4 * m)) ^ 2
      = schwA m r := by
  have hr0 : r ≠ 0 := by
    have : 0 < r := by linarith
    exact this.ne'
  have hm0 : m ≠ 0 := hm.ne'
  have hE : Real.exp (r / (2 * m)) ≠ 0 := (Real.exp_pos _).ne'
  have e1 : -r / (2 * m) = -(r / (2 * m)) := by ring
  rw [Real.sq_sqrt (kruskalF_pos_outside hm hr).le, e1, Real.exp_neg]
  unfold kruskalF schwA
  field_simp
  ring

/-- Kruskal's factor times the square of the slope of `√F` along the radius is Schwarzschild's
ruler function `1 / (1 - 2m/r)`. -/
theorem kruskalOut_factor_radius {m r : ℝ} (hm : 0 < m) (hr : 2 * m < r) :
    32 * m ^ 3 / r * Real.exp (-r / (2 * m)) * kruskalOutD m r ^ 2 = schwB m r := by
  have hr0 : r ≠ 0 := by
    have : 0 < r := by linarith
    exact this.ne'
  have hm0 : m ≠ 0 := hm.ne'
  have hδ : r - 2 * m ≠ 0 := (sub_pos.2 hr).ne'
  have hE : Real.exp (r / (2 * m)) ≠ 0 := (Real.exp_pos _).ne'
  have e1 : -r / (2 * m) = -(r / (2 * m)) := by ring
  have h1 : 1 - 2 * m / r = (r - 2 * m) / r := by
    field_simp
  have h2 : r / (2 * m) - 1 = (r - 2 * m) / (2 * m) := by
    field_simp
  unfold kruskalOutD schwB
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (kruskalF_pos_outside hm hr).le, e1, Real.exp_neg]
  unfold kruskalF
  rw [h1, h2]
  field_simp
  ring

/-- The sum behind the computation: with `ch² - sh² = 1` the mixed terms cancel, and what is
left has the two factors `K s² k²` and `K D²`. -/
theorem kruskalOut_algebra (K s k D ch sh a b r2 sn v0 v1 v2 v3 w0 w1 w2 w3 : ℝ)
    (hcs : ch ^ 2 - sh ^ 2 = 1) (h1 : K * s ^ 2 * k ^ 2 = a) (h2 : K * D ^ 2 = b) :
    -a * v0 * w0 + b * v1 * w1 + r2 * v2 * w2 + r2 * sn * v3 * w3
      = -K * (s * (ch * k) * v0 + sh * D * v1) * (s * (ch * k) * w0 + sh * D * w1)
        + K * (s * (sh * k) * v0 + ch * D * v1) * (s * (sh * k) * w0 + ch * D * w1)
        + r2 * v2 * w2 + r2 * sn * v3 * w3 := by
  linear_combination (K * s ^ 2 * k ^ 2 * v0 * w0 - K * D ^ 2 * v1 * w1) * hcs
    + v0 * w0 * h1 - v1 * w1 * h2

/-- **The two length measures agree.** Outside the rim, Schwarzschild's table gives two steps
the length that Kruskal's table gives, at the new point, to the two steps as the map sees
them. -/
theorem schwOut_eq_kruskal {m : ℝ} (hm : 0 < m) {x : Coords 4} (hx : x ∈ outside m)
    (v w : Coords 4) :
    tableMeasure (roundG (schwA m) (schwB m)) x v w
      = tableMeasure (kruskalG m) (kruskalOut m x) (fderiv ℝ (kruskalOut m) x v)
        (fderiv ℝ (kruskalOut m) x w) := by
  have hcs : cosh (x 0 / (4 * m)) ^ 2 - sinh (x 0 / (4 * m)) ^ 2 = 1 := by
    rw [Real.cosh_sq]
    ring
  have hA : kruskalA m (√(kruskalF m (x 1)) * sinh (x 0 / (4 * m)))
      (√(kruskalF m (x 1)) * cosh (x 0 / (4 * m)))
      = 32 * m ^ 3 / x 1 * Real.exp (-x 1 / (2 * m)) := by
    unfold kruskalA
    rw [kruskalR_kruskalOut hm hx.2.1]
  have hS : kruskalS m (√(kruskalF m (x 1)) * sinh (x 0 / (4 * m)))
      (√(kruskalF m (x 1)) * cosh (x 0 / (4 * m))) = x 1 ^ 2 := by
    unfold kruskalS
    rw [kruskalR_kruskalOut hm hx.2.1]
  rw [schwOut_measure_apply, fderiv_kruskalOut_apply hm hx v, fderiv_kruskalOut_apply hm hx w]
  unfold kruskalOut
  rw [kruskalOut_measure_apply, hA, hS]
  exact kruskalOut_algebra _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcs
    (kruskalOut_factor_time hm hx.2.1) (kruskalOut_factor_radius hm hx.2.1)

/-! ## The chart -/

/-- **Schwarzschild's space-time outside the rim is, near each of its points, a piece of
Kruskal's:** for a positive mass, around every point outside the rim there is a chart into
Kruskal's region in which Schwarzschild's length measure is Kruskal's. -/
theorem kruskalHoldsSchwarzschild_outside {m : ℝ} (hm : 0 < m) {p : Coords 4}
    (hp : p ∈ outside m) :
    IsKruskalNear m (flatMeasure (tableMeasure (roundG (schwA m) (schwB m)))) p := by
  have ho := isOpen_outside m
  obtain ⟨φ, hφ, hpφ, hsrc, hφe, hmf⟩ :=
    Join.exists_chart_of_localDiffeo (M := Coords 4)
      (c := OpenPartialHomeomorph.ofSet (outside m) ho)
      (StructureGroupoid.mem_maximalAtlas_of_mem_groupoid _ (ofSet_mem_contDiffGroupoid ho))
      (p := p) hp ho hp ho (contDiffOn_kruskalOut hm) hp (isUnit_fderiv_kruskalOut hm hp)
  refine ⟨φ, hφ, hpφ, fun q hq ↦ ?_⟩
  have hqo : q ∈ outside m := (hsrc hq).1.2
  refine ⟨?_, fun v w ↦ ?_⟩
  · rw [hφe q]
    exact kruskalOut_mem_kruskalRegion hm hqo
  · have e : mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4)
        (OpenPartialHomeomorph.ofSet (outside m) ho) q
        = ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, Coords 4) q) := mfderiv_id
    have hφq : φ q = kruskalOut m q := hφe q
    have h := schwOut_eq_kruskal hm hqo v w
    rw [← hφq] at h
    rw [hmf q hq v, hmf q hq w, e]
    exact h

end Curved

end GravityInLean
