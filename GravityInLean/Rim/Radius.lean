/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.EveryPoint
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue

import Mathlib.Tactic

/-!
# Kruskal's radius is well defined

Board item `task:rim-radius`. The function `kruskalF m r = (r / 2m - 1) · exp (r / 2m)` has the
slope `(r / 4m²) · exp (r / 2m)`, which is positive for `r > 0`. It tends to `-1` as `r` tends
to `0` from above, and it grows without bound. So for a positive mass and a number `u > -1`
there is exactly one positive `r` with `kruskalF m r = u`, and `kruskalR m u`, the infimum of
such `r`, is that `r`.
-/

@[expose] public section

namespace GravityInLean

open Real Set

namespace Curved

/-- The slope of `kruskalF m` at `r` is `(r / 4m²) · exp (r / 2m)`. -/
theorem hasDerivAt_kruskalF {m : ℝ} (hm : m ≠ 0) (r : ℝ) :
    HasDerivAt (kruskalF m) (r / (4 * m ^ 2) * Real.exp (r / (2 * m))) r := by
  have h1 : HasDerivAt (fun r : ℝ => r / (2 * m)) (1 / (2 * m)) r :=
    (hasDerivAt_id' r).div_const (2 * m)
  have h2 : HasDerivAt (fun r : ℝ => r / (2 * m) - 1) (1 / (2 * m)) r := h1.sub_const 1
  have h3 : HasDerivAt (fun r : ℝ => Real.exp (r / (2 * m)))
      (Real.exp (r / (2 * m)) * (1 / (2 * m))) r := h1.exp
  have h4 : HasDerivAt (fun r : ℝ => (r / (2 * m) - 1) * Real.exp (r / (2 * m)))
      (1 / (2 * m) * Real.exp (r / (2 * m)) +
        (r / (2 * m) - 1) * (Real.exp (r / (2 * m)) * (1 / (2 * m)))) r := h2.mul h3
  have h5 : kruskalF m = fun r : ℝ => (r / (2 * m) - 1) * Real.exp (r / (2 * m)) := rfl
  rw [h5]
  convert h4 using 1
  field_simp
  ring

/-- At the centre, `r = 0`, the function `kruskalF m` has the value `-1`. -/
theorem kruskalF_zero (m : ℝ) : kruskalF m 0 = -1 := by
  simp [kruskalF]

/-- `kruskalF m` is continuous in `r`. -/
theorem continuous_kruskalF {m : ℝ} (hm : m ≠ 0) : Continuous (kruskalF m) :=
  continuous_iff_continuousAt.2 fun r => (hasDerivAt_kruskalF hm r).continuousAt

/-- For a positive mass, `kruskalF m` grows strictly with `r` on `r ≥ 0`. -/
theorem kruskalF_strictMonoOn {m : ℝ} (hm : 0 < m) : StrictMonoOn (kruskalF m) (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) (continuous_kruskalF hm.ne').continuousOn ?_
  intro r hr
  rw [interior_Ici] at hr
  have hr' : 0 < r := hr
  rw [(hasDerivAt_kruskalF hm.ne' r).deriv]
  positivity

/-- For a positive mass, two positive radii with the same value of `kruskalF m` are equal. -/
theorem kruskalF_inj {m : ℝ} (hm : 0 < m) {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r')
    (h : kruskalF m r = kruskalF m r') : r = r' :=
  (kruskalF_strictMonoOn hm).injOn (mem_Ici.2 hr.le) (mem_Ici.2 hr'.le) h

/-- For a positive mass, every number `u > -1` is a value of `kruskalF m` at some positive
radius. -/
theorem exists_kruskalF_eq {m : ℝ} (hm : 0 < m) {u : ℝ} (hu : -1 < u) :
    ∃ r : ℝ, 0 < r ∧ kruskalF m r = u := by
  have hR0 : (0 : ℝ) ≤ 2 * m * (|u| + 2) := by positivity
  have hfR : u ≤ kruskalF m (2 * m * (|u| + 2)) := by
    have ha : 2 * m * (|u| + 2) / (2 * m) = |u| + 2 := by
      field_simp
    have h1 : (1 : ℝ) ≤ Real.exp (|u| + 2) := Real.one_le_exp (by positivity)
    have h2 : (0 : ℝ) ≤ |u| := abs_nonneg u
    have h3 : u ≤ |u| := le_abs_self u
    unfold kruskalF
    rw [ha]
    nlinarith [mul_nonneg h2 (sub_nonneg.2 h1)]
  obtain ⟨r, hr, hru⟩ := intermediate_value_Icc hR0 (continuous_kruskalF hm.ne').continuousOn
    (show u ∈ Icc (kruskalF m 0) (kruskalF m (2 * m * (|u| + 2))) from
      ⟨by rw [kruskalF_zero]; exact hu.le, hfR⟩)
  refine ⟨r, lt_of_le_of_ne hr.1 ?_, hru⟩
  intro h0
  rw [← h0, kruskalF_zero] at hru
  exact hu.ne hru

/-- **The radius is well defined.** For a positive mass and `u > -1` there is exactly one
positive `r` with `kruskalF m r = u`, and `kruskalR m u` is that `r`. -/
theorem kruskalRadiusSpec : KruskalRadiusSpec := by
  intro m hm u hu
  obtain ⟨r₀, hr₀, hru⟩ := exists_kruskalF_eq hm hu
  have huniq : ∀ r : ℝ, 0 < r → kruskalF m r = u → r = r₀ := fun r hr h =>
    kruskalF_inj hm hr hr₀ (h.trans hru.symm)
  have hset : {r : ℝ | 0 < r ∧ kruskalF m r = u} = {r₀} := by
    ext r
    rw [mem_ofPred_eq, mem_singleton_iff]
    exact ⟨fun h => huniq r h.1 h.2, fun h => by rw [h]; exact ⟨hr₀, hru⟩⟩
  have hR : kruskalR m u = r₀ := by
    unfold kruskalR
    rw [hset, csInf_singleton]
  rw [hR]
  exact ⟨hr₀, hru, huniq⟩

end Curved

end GravityInLean
