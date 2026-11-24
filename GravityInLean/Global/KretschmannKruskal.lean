/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.KretschmannGen
public import GravityInLean.Rim.Empty

import Mathlib.Tactic

/-!
# The curvature scalar of Kruskal's table

The curvature scalar `kretschmann` of Kruskal's table is `-48 m² / r⁶`, at every point of its
region, the rim included. So a map that keeps Kruskal's table keeps the radius `r`.

(The textbooks' scalar `R_abcd R^abcd` is `48 m² / r⁶`; the trace form used by `kretschmann`
gives minus that.)

* `kruskal_radiusSlopeSq`: on Kruskal's table the radius of the spheres grows at the rate
  `|∇r|² = 1 - 2m / r`.
* `kretschmann_kruskal`: the scalar.
-/

@[expose] public section

namespace GravityInLean.Curved

open Real

variable {m : ℝ}

/-- **On Kruskal's table the radius of the spheres grows at the rate `1 - 2m / r`,** squared and
measured with the table, at every `T`, `X` with `X² - T² > -1`. -/
theorem kruskal_radiusSlopeSq {T X : ℝ} (hm : 0 < m) (h : -1 < X ^ 2 - T ^ 2) :
    radiusSlopeSq (kruskalA m) (kruskalA m) zero2 (kruskalS m) T X
      = 1 - 2 * m / kruskalR m (X ^ 2 - T ^ 2) := by
  have hS : kruskalS m = sqDiff (kruskalSu m) := rfl
  have s1 : ∀ u, -1 < u → HasDerivAt (kruskalSu m) (kruskalSu1 m u) u :=
    fun _ hu => hasDerivAt_kruskalSu hm hu
  have hSt : dt (kruskalS m) T X = -2 * T * kruskalSu1 m (X ^ 2 - T ^ 2) := hS ▸ dt_sqDiff s1 h
  have hSr : dr (kruskalS m) T X = 2 * X * kruskalSu1 m (X ^ 2 - T ^ 2) := hS ▸ dr_sqDiff s1 h
  have hA : kruskalA m T X
      = 32 * m ^ 3 / kruskalR m (X ^ 2 - T ^ 2) * kruskalW m (X ^ 2 - T ^ 2) := rfl
  have hSv : kruskalS m T X = kruskalR m (X ^ 2 - T ^ 2) ^ 2 := rfl
  have hm' : m ≠ 0 := hm.ne'
  have hr : kruskalR m (X ^ 2 - T ^ 2) ≠ 0 := (kruskalR_pos hm h).ne'
  have hw : kruskalW m (X ^ 2 - T ^ 2) ≠ 0 := (kruskalW_pos m _).ne'
  -- the equation that ties the radius to `X² - T²`
  have hrel : X ^ 2 - T ^ 2
      = (kruskalR m (X ^ 2 - T ^ 2) / (2 * m) - 1) * (kruskalW m (X ^ 2 - T ^ 2))⁻¹ := by
    have hF : kruskalF m (kruskalR m (X ^ 2 - T ^ 2)) = X ^ 2 - T ^ 2 := kruskalF_kruskalR hm h
    rw [kruskalF, exp_eq_inv_kruskalW] at hF
    exact hF.symm
  rw [radiusSlopeSq, sizeSlopeSq, det2, hSt, hSr, hA, hSv]
  simp only [zero2, kruskalSu1]
  generalize kruskalW m (X ^ 2 - T ^ 2) = w at hw hrel ⊢
  generalize kruskalR m (X ^ 2 - T ^ 2) = r at hr hrel ⊢
  have e : 32 * m ^ 3 / r * w * (2 * X * (8 * m ^ 2 * w) * (2 * X * (8 * m ^ 2 * w)))
        + 2 * 0 * (-2 * T * (8 * m ^ 2 * w) * (2 * X * (8 * m ^ 2 * w)))
        - 32 * m ^ 3 / r * w * (-2 * T * (8 * m ^ 2 * w) * (-2 * T * (8 * m ^ 2 * w)))
      = 8192 * m ^ 7 * w ^ 3 / r * (X ^ 2 - T ^ 2) := by
    ring
  rw [e, hrel]
  field_simp
  ring

/-- **The curvature scalar of Kruskal's table is `-48 m² / r⁶`,** at every point of its region,
the rim included. -/
theorem kretschmann_kruskal (hm : 0 < m) {x : Coords 4} (hx : x ∈ kruskalRegion) :
    kretschmann (kruskalG m) (genGinv (kruskalA m) (kruskalA m) zero2 (kruskalS m)) x
      = -48 * m ^ 2 / kruskalR m (x 1 ^ 2 - x 0 ^ 2) ^ 6 := by
  have hr : kruskalR m (x 1 ^ 2 - x 0 ^ 2) ≠ 0 := (kruskalR_pos hm hx.1).ne'
  have hSv : kruskalS m (x 0) (x 1) = kruskalR m (x 1 ^ 2 - x 0 ^ 2) ^ 2 := rfl
  have key := kretschmann_gen_empty (kruskal_regularG hm hx) (kruskal_isEmptyG hm hx.1)
  rw [kruskal_radiusSlopeSq hm hx.1, hSv] at key
  rw [kruskalG, key]
  field_simp
  ring

end GravityInLean.Curved
