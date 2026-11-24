/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.Checks
public import GravityInLean.Rim.SchwOutside

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Schwarzschild's table outside the rim maps into Kruskal's whole space-time

Board item `task:global-ks-outside`. The outside half of `KruskalMapOfSchwarzschild`
(`Goals/Global.lean`): for a positive mass, the textbook map `kruskalOutside m` of Kruskal and
Szekeres is a length-keeping map from Schwarzschild's table on `outside m` into Kruskal's whole
space-time.

The map is made of two maps that are known already:

* `kruskalOut m` (`Rim/SchwOutside.lean`) sends Schwarzschild's labels `(t, r, θ, φ)` outside
  the rim to Kruskal's labels `(T, X, θ, φ)` and turns Schwarzschild's table into Kruskal's table
  of `Goals/EveryPoint.lean` (`schwOut_eq_kruskal`);
* `kruskalWrap` (`Global/Checks.lean`) wraps the two angles round the unit sphere and turns
  Kruskal's table into Kruskal's whole table (`kruskalWrap_pullback`).

`kruskalOutside m` is the second after the first (`kruskalOutside_eq_wrap`): the only thing to
check is that the factor `√(r / 2m - 1) · exp (r / 4m)` of the textbook is the factor
`√(kruskalF m r)` of `kruskalOut`. The rest is the rule for the slope of one map after another.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

/-- The textbook factor `√(r / 2m - 1) · exp (r / 4m)` is the square root of `kruskalF m r`,
for every mass and every `r`. -/
theorem sqrt_kruskalF (m r : ℝ) :
    √(kruskalF m r) = √(r / (2 * m) - 1) * exp (r / (4 * m)) := by
  have e : exp (r / (2 * m)) = exp (r / (4 * m)) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have h : kruskalF m r = (r / (2 * m) - 1) * exp (r / (4 * m)) ^ 2 := by
    unfold kruskalF
    rw [e]
  rw [h, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (exp_pos _).le]

/-- **The textbook map outside the rim is `kruskalOut`, wrapped round the sphere:** first go
from Schwarzschild's labels to Kruskal's labels, then send the two angles to the point of the
unit sphere they describe. -/
theorem kruskalOutside_eq_wrap (m : ℝ) (x : Coords 4) :
    kruskalOutside m x = kruskalWrap (kruskalOut m x) := by
  have e0 : kruskalOut m x 0 = √(kruskalF m (x 1)) * sinh (x 0 / (4 * m)) := rfl
  have e1 : kruskalOut m x 1 = √(kruskalF m (x 1)) * cosh (x 0 / (4 * m)) := rfl
  have e2 : kruskalOut m x 2 = x 2 := rfl
  have e3 : kruskalOut m x 3 = x 3 := rfl
  unfold kruskalOutside kruskalWrap
  rw [e0, e1, e2, e3, sqrt_kruskalF]

/-- The textbook map outside the rim is smooth there. -/
theorem contDiffOn_kruskalOutside {m : ℝ} (hm : 0 < m) :
    ContDiffOn ℝ ∞ (kruskalOutside m) (outside m) := by
  have hfun : kruskalOutside m = kruskalWrap ∘ kruskalOut m :=
    funext (kruskalOutside_eq_wrap m)
  rw [hfun]
  exact contDiff_kruskalWrap.comp_contDiffOn (contDiffOn_kruskalOut hm)

/-- **Schwarzschild's table outside the rim is Kruskal's whole table along the textbook map:**
two steps at a point outside the rim have, measured with Schwarzschild's table, the length that
Kruskal's whole table gives to the two steps as the textbook map carries them. -/
theorem kruskalOutside_pullback {m : ℝ} (hm : 0 < m) {q : Coords 4} (hq : q ∈ outside m)
    (v w : Coords 4) :
    tableMeasure (roundG (schwA m) (schwB m)) q v w
      = tableMeasure (kruskalWhole m) (kruskalOutside m q) (fderiv ℝ (kruskalOutside m) q v)
          (fderiv ℝ (kruskalOutside m) q w) := by
  have hfun : kruskalOutside m = kruskalWrap ∘ kruskalOut m :=
    funext (kruskalOutside_eq_wrap m)
  have hd : DifferentiableAt ℝ (kruskalOut m) q :=
    ((contDiffOn_kruskalOut hm).contDiffAt ((isOpen_outside m).mem_nhds hq)).differentiableAt
      (by simp)
  have hw : DifferentiableAt ℝ kruskalWrap (kruskalOut m q) :=
    (contDiff_kruskalWrap.differentiable (by simp)).differentiableAt
  rw [hfun, fderiv_comp q hw hd]
  change tableMeasure (roundG (schwA m) (schwB m)) q v w
    = tableMeasure (kruskalWhole m) (kruskalWrap (kruskalOut m q))
        (fderiv ℝ kruskalWrap (kruskalOut m q) (fderiv ℝ (kruskalOut m) q v))
        (fderiv ℝ kruskalWrap (kruskalOut m q) (fderiv ℝ (kruskalOut m) q w))
  rw [schwOut_eq_kruskal hm hq v w]
  exact kruskalWrap_pullback m _ _ _

/-- **Schwarzschild's space-time outside the rim maps into Kruskal's whole space-time by the
textbook formulas,** keeping every length, for every positive mass. This is the outside half of
`KruskalMapOfSchwarzschild`. -/
theorem kruskalOutside_isKruskalMapOn (m : ℝ) (hm : 0 < m) :
    IsKruskalMapOn m (flatMeasure (tableMeasure (roundG (schwA m) (schwB m))))
      (kruskalOutside m) (outside m) := by
  refine ⟨isOpen_outside m, (contDiffOn_kruskalOutside hm).contMDiffOn,
    fun q hq ↦ ⟨?_, fun v w ↦ ?_⟩⟩
  · rw [kruskalOutside_eq_wrap]
    exact kruskalWrap_mem (kruskalOut_mem_kruskalRegion hm hq).1
  · rw [mfderiv_eq_fderiv]
    exact kruskalOutside_pullback hm hq v w

end GravityInLean.Curved
