/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.Checks
public import GravityInLean.Rim.SchwInside

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Schwarzschild's table inside the rim maps into Kruskal's whole space-time

Board item `task:global-ks-inside`. The inside half of `KruskalMapOfSchwarzschild`
(`Goals/Global.lean`): for a positive mass, the textbook map `kruskalInside m` of Kruskal and
Szekeres is a length-keeping map from Schwarzschild's table on `inside m` into Kruskal's whole
space-time.

The map is made of two maps that are known already:

* `insideMap m` (`Rim/SchwInside.lean`) sends Schwarzschild's labels `(t, r, θ, φ)` inside the
  rim to Kruskal's labels `(T, X, θ, φ)` and turns Schwarzschild's table into Kruskal's table of
  `Goals/EveryPoint.lean` (`insideMap_measure`);
* `kruskalWrap` (`Global/Checks.lean`) wraps the two angles round the unit sphere and turns
  Kruskal's table into Kruskal's whole table (`kruskalWrap_pullback`).

`kruskalInside m` is the second after the first (`kruskalInside_eq_wrap`): the only thing to
check is that the factor `√(1 - r / 2m) · exp (r / 4m)` of the textbook is the factor
`√(-kruskalF m r)` of `insideMap`. The rest is the rule for the slope of one map after another.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

/-- The textbook factor `√(1 - r / 2m) · exp (r / 4m)` is the square root of `-kruskalF m r`,
for every mass and every `r`. -/
theorem sqrt_neg_kruskalF (m r : ℝ) :
    √(-kruskalF m r) = √(1 - r / (2 * m)) * exp (r / (4 * m)) := by
  have e : exp (r / (2 * m)) = exp (r / (4 * m)) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have h : -kruskalF m r = (1 - r / (2 * m)) * exp (r / (4 * m)) ^ 2 := by
    unfold kruskalF
    rw [e]
    ring
  rw [h, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (exp_pos _).le]

/-- **The textbook map inside the rim is `insideMap`, wrapped round the sphere:** first go from
Schwarzschild's labels to Kruskal's labels, then send the two angles to the point of the unit
sphere they describe. -/
theorem kruskalInside_eq_wrap (m : ℝ) (x : Coords 4) :
    kruskalInside m x = kruskalWrap (insideMap m x) := by
  have e0 : insideMap m x 0 = √(-kruskalF m (x 1)) * cosh (x 0 / (4 * m)) := rfl
  have e1 : insideMap m x 1 = √(-kruskalF m (x 1)) * sinh (x 0 / (4 * m)) := rfl
  have e2 : insideMap m x 2 = x 2 := rfl
  have e3 : insideMap m x 3 = x 3 := rfl
  unfold kruskalInside kruskalWrap
  rw [e0, e1, e2, e3, sqrt_neg_kruskalF]

/-- The textbook map inside the rim is smooth there. -/
theorem contDiffOn_kruskalInside {m : ℝ} (hm : 0 < m) :
    ContDiffOn ℝ ∞ (kruskalInside m) (inside m) := by
  have hfun : kruskalInside m = kruskalWrap ∘ insideMap m := funext (kruskalInside_eq_wrap m)
  rw [hfun]
  exact contDiff_kruskalWrap.comp_contDiffOn (contDiffOn_insideMap hm)

/-- **Schwarzschild's table inside the rim is Kruskal's whole table along the textbook map:**
two steps at a point inside the rim have, measured with Schwarzschild's table, the length that
Kruskal's whole table gives to the two steps as the textbook map carries them. -/
theorem kruskalInside_pullback {m : ℝ} (hm : 0 < m) {q : Coords 4} (hq : q ∈ inside m)
    (v w : Coords 4) :
    tableMeasure (roundG (schwA m) (schwB m)) q v w
      = tableMeasure (kruskalWhole m) (kruskalInside m q) (fderiv ℝ (kruskalInside m) q v)
          (fderiv ℝ (kruskalInside m) q w) := by
  have hfun : kruskalInside m = kruskalWrap ∘ insideMap m := funext (kruskalInside_eq_wrap m)
  have hd : DifferentiableAt ℝ (insideMap m) q :=
    ((contDiffOn_insideMap hm).contDiffAt ((isOpen_inside m).mem_nhds hq)).differentiableAt
      (by simp)
  have hw : DifferentiableAt ℝ kruskalWrap (insideMap m q) :=
    (contDiff_kruskalWrap.differentiable (by simp)).differentiableAt
  rw [hfun, fderiv_comp q hw hd]
  change tableMeasure (roundG (schwA m) (schwB m)) q v w
    = tableMeasure (kruskalWhole m) (kruskalWrap (insideMap m q))
        (fderiv ℝ kruskalWrap (insideMap m q) (fderiv ℝ (insideMap m) q v))
        (fderiv ℝ kruskalWrap (insideMap m q) (fderiv ℝ (insideMap m) q w))
  rw [insideMap_measure hm hq rfl v w]
  exact kruskalWrap_pullback m _ _ _

/-- **Schwarzschild's space-time inside the rim maps into Kruskal's whole space-time by the
textbook formulas,** keeping every length, for every positive mass. This is the inside half of
`KruskalMapOfSchwarzschild`. -/
theorem kruskalInside_isKruskalMapOn (m : ℝ) (hm : 0 < m) :
    IsKruskalMapOn m (flatMeasure (tableMeasure (roundG (schwA m) (schwB m))))
      (kruskalInside m) (inside m) := by
  refine ⟨isOpen_inside m, (contDiffOn_kruskalInside hm).contMDiffOn,
    fun q hq ↦ ⟨?_, fun v w ↦ ?_⟩⟩
  · rw [kruskalInside_eq_wrap]
    exact kruskalWrap_mem (insideMap_mem_kruskalRegion hm hq).1
  · rw [mfderiv_eq_fderiv]
    exact kruskalInside_pullback hm hq v w

end GravityInLean.Curved
