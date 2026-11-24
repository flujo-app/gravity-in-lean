/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.KretschmannGen
public import GravityInLean.Global.KretschmannKept
public import GravityInLean.Global.TableHess
public import GravityInLean.BothWays.OffRimKnown
public import GravityInLean.BirkhoffFromSymmetry

import Mathlib.Tactic

/-!
# The scalars of Schwarzschild's table that tell the radius, the mass and the split

For Schwarzschild's table of distance and angles, `roundG (schwA m) (schwB m)`, with its inverse
table `roundGinv (schwA m) (schwB m)`, for every mass `m` (positive, zero or negative), at every
point off the rim (`BothWays.offRim m`: distance positive and not `2m`, off the poles):

* `kretschmann_schw`: the curvature scalar is `-48 m² / r⁶`;
* `gradSq_schwRad`: the distance label grows at the rate `|∇r|² = 1 - 2m / r`;
* `hessT_schwRad`: the second slope of the distance label is `(m / r²)` times the table on the
  `(t, r)` plane and `((r - 2m) / r²)` times the table on the sphere.

On the way: `kretschmann_congr` (the curvature scalar only looks at the tables near the point),
`roundGinv_eq_genGinv` (the two ways to write the inverse of a round table agree), and
`schw_regularG`, `schw_isEmptyG`, `schw_radiusSlopeSq` (Schwarzschild's table as a table of the
general round shape).

That Schwarzschild's table is a good table off the rim, and outside it, is in the project
already: `BothWays.schwarzschild_regularTable_offRim`, `schwarzschild_regularTable_outside`.
-/

@[expose] public section

namespace GravityInLean.Curved

open Real Filter Topology

/-- **The curvature scalar only looks at the tables near the point:** two tables that agree
near `x`, with inverse tables that agree near `x`, have the same curvature scalar at `x`. -/
theorem kretschmann_congr {n : ℕ} {g g' ginv ginv' : Fin n → Fin n → Coords n → ℝ}
    {x : Coords n} (hg : ∀ i j, g i j =ᶠ[𝓝 x] g' i j)
    (hinv : ∀ i j, ginv i j =ᶠ[𝓝 x] ginv' i j) :
    kretschmann g ginv x = kretschmann g' ginv' x := by
  have hΓ : ∀ᶠ y in 𝓝 x, ∀ a b c,
      christoffel g ginv a b c y = christoffel g' ginv' a b c y :=
    eventually_all.2 fun a ↦ eventually_all.2 fun b ↦ eventually_all.2 fun c ↦
      _root_.GravityInLean.christoffel_congr hg hinv a b c
  have hR : ∀ ρ μ, riemM (christoffel g ginv) ρ μ x = riemM (christoffel g' ginv') ρ μ x :=
    fun ρ μ ↦ riemM_congr hΓ ρ μ
  have hv : ∀ i j, ginv i j x = ginv' i j x := fun i j ↦ (hinv i j).eq_of_nhds
  simp only [kretschmann, hR, hv]

/-- A round table is a table of the general round shape, without a cross term and with the
distance label as the radius of the spheres. -/
theorem roundG_eq_genG (A B : ℝ → ℝ) :
    roundG A B = genG (onlyR A) (onlyR B) zero2 (onlyR sqF) := by
  change roundG A B = genG (fun _ r => A r) (fun _ r => B r) zero2 (onlyR sqF)
  rw [genG_diagonal, changingG_static]

/-- The two ways to write the inverse of a round table agree, where the clock and ruler
functions are not zero. -/
theorem roundGinv_eq_genGinv {A B : ℝ → ℝ} {y : Coords 4} (hA : A (y 1) ≠ 0)
    (hB : B (y 1) ≠ 0) (a b : Fin 4) :
    roundGinv A B a b y = genGinv (onlyR A) (onlyR B) zero2 (onlyR sqF) a b y := by
  have h00 : (-A (y 1))⁻¹ = -B (y 1) / (A (y 1) * B (y 1)) := by
    field_simp
  have h11 : (B (y 1))⁻¹ = A (y 1) / (A (y 1) * B (y 1)) := by
    field_simp
  have h33 : (sin (y 2) ^ 2)⁻¹ * (y 1 ^ 2)⁻¹ = (y 1 ^ 2)⁻¹ * (sin (y 2) ^ 2)⁻¹ := mul_comm _ _
  fin_cases a <;> fin_cases b <;>
    simp [roundGinv, diag, roundDiag, sep, gr, gθ, genGinv, ginvTR, ginvΘ, det2, zero2, negF,
      sqF, sin2, constOne, onlyR, h00, h11, h33]

section Schw

variable {m : ℝ} {x : Coords 4}

/-- Near a point off the rim the two ways to write the inverse of Schwarzschild's table
agree. -/
theorem schw_ginv_eventuallyEq (hx : x ∈ BothWays.offRim m) (i j : Fin 4) :
    roundGinv (schwA m) (schwB m) i j
      =ᶠ[𝓝 x] genGinv (onlyR (schwA m)) (onlyR (schwB m)) zero2 (onlyR sqF) i j := by
  filter_upwards [(BothWays.isOpen_offRim m).mem_nhds hx] with y hy
  have hA : schwA m (y 1) ≠ 0 := BothWays.schwA_ne_zero_of_mem_offRim hy
  have hB : schwB m (y 1) ≠ 0 := inv_ne_zero hA
  exact roundGinv_eq_genGinv (A := schwA m) (B := schwB m) hA hB i j

/-- The conditions under which the formulas for the general round shape are the curvature hold
for Schwarzschild's table at every point off the rim. -/
theorem schw_regularG (hx : x ∈ BothWays.offRim m) :
    RegularG (onlyR (schwA m)) (onlyR (schwB m)) zero2 (onlyR sqF) x where
  sin_ne := hx.2.2
  det_ne := by
    have hA : schwA m (x 1) ≠ 0 := BothWays.schwA_ne_zero_of_mem_offRim hx
    have hB : schwB m (x 1) ≠ 0 := inv_ne_zero hA
    have e : det2 (onlyR (schwA m)) (onlyR (schwB m)) zero2 (x 0) (x 1)
        = schwA m (x 1) * schwB m (x 1) := by
      simp [det2, zero2, onlyR]
    rw [e]
    exact mul_ne_zero hA hB
  S_ne := pow_ne_zero 2 hx.1.ne'
  smoothA := twiceSmooth_onlyR (smooth_schwA m hx.1.ne') _
  smoothB := twiceSmooth_onlyR
    (smooth_schwB m hx.1.ne' (BothWays.schwA_ne_zero_of_mem_offRim hx)) _
  smoothC := twiceSmooth_zero2 _ _
  smoothS := twiceSmooth_onlyR (contDiffAt_id.pow 2) _

/-- The four formulas for the curvature of the general round shape vanish for Schwarzschild's
table, off the rim. -/
theorem schw_isEmptyG (hx : x ∈ BothWays.offRim m) :
    IsEmptyG (onlyR (schwA m)) (onlyR (schwB m)) zero2 (onlyR sqF) (x 0) (x 1) := by
  refine (gen_ricciFlat_iff (schw_regularG hx)).mp ?_
  refine (isRicciFlatAt_congr (fun i j ↦ ?_) (schw_ginv_eventuallyEq hx)).mp
    (BothWays.schwarzschild_ricciFlat_on_offRim m x hx)
  exact Filter.EventuallyEq.of_eq (congrFun (congrFun (roundG_eq_genG _ _) i) j)

/-- On Schwarzschild's table the radius of the spheres grows at the rate `1 - 2m / r`, squared
and measured with the table. -/
theorem schw_radiusSlopeSq (hx : x ∈ BothWays.offRim m) :
    radiusSlopeSq (onlyR (schwA m)) (onlyR (schwB m)) zero2 (onlyR sqF) (x 0) (x 1)
      = 1 - 2 * m / x 1 := by
  have hr : x 1 ≠ 0 := hx.1.ne'
  have hA : schwA m (x 1) ≠ 0 := BothWays.schwA_ne_zero_of_mem_offRim hx
  have hBA : schwB m (x 1) = (schwA m (x 1))⁻¹ := rfl
  simp only [radiusSlopeSq, sizeSlopeSq, det2, dt_onlyR, dr_onlyR, deriv_sqF, onlyR, zero2, sqF]
  rw [hBA]
  change _ = schwA m (x 1)
  field_simp
  ring

/-- **The curvature scalar of Schwarzschild's table is `-48 m² / r⁶`,** for every mass, at every
point off the rim. -/
theorem kretschmann_schw (hx : x ∈ BothWays.offRim m) :
    kretschmann (roundG (schwA m) (schwB m)) (roundGinv (schwA m) (schwB m)) x
      = -48 * m ^ 2 / x 1 ^ 6 := by
  have hr : x 1 ≠ 0 := hx.1.ne'
  rw [kretschmann_congr
      (fun i j ↦ Filter.EventuallyEq.of_eq (congrFun (congrFun (roundG_eq_genG _ _) i) j))
      (schw_ginv_eventuallyEq hx),
    kretschmann_gen_empty (schw_regularG hx) (schw_isEmptyG hx), schw_radiusSlopeSq hx]
  simp only [onlyR, sqF]
  field_simp
  ring

/-- The slope of the distance label: one along the distance, zero along the other labels. -/
theorem slope_radius (a : Fin 4) (y : Coords 4) :
    slope a (fun z : Coords 4 ↦ z 1) y = if a = 1 then 1 else 0 := by
  by_cases h : a = 1
  · subst h
    have e : slope 1 (fun z : Coords 4 ↦ z 1) y = 1 :=
      (slope_along 1 (fun s ↦ s) y).trans (congrFun deriv_id'' _)
    simpa using e
  · simpa [h] using slope_across (Ne.symm h) (fun s ↦ s) y

/-- **On Schwarzschild's table the distance label grows at the rate `1 - 2m / r`,** squared and
measured with the table. (Read as a formula, this holds at every point.) -/
theorem gradSq_schwRad (m : ℝ) (x : Coords 4) :
    gradSq (roundGinv (schwA m) (schwB m)) (fun y ↦ y 1) x = 1 - 2 * m / x 1 := by
  have h11 : roundGinv (schwA m) (schwB m) 1 1 x = 1 - 2 * m / x 1 := by
    simp [roundGinv, diag, roundDiag, sep, gr, gθ, constOne, schwB]
  simp [gradSq, slope_radius, h11]

/-- **The second slope of the distance label on Schwarzschild's table** is `m / r²` times the
table on the `(t, r)` plane, and `(r - 2m) / r²` times the table on the sphere. -/
theorem hessT_schwRad (hx : x ∈ BothWays.offRim m) (a b : Fin 4) :
    hessT (roundG (schwA m) (schwB m)) (roundGinv (schwA m) (schwB m)) (fun y ↦ y 1) a b x
      = (if a.val < 2 ∧ b.val < 2 then m / x 1 ^ 2
          else if 2 ≤ a.val ∧ 2 ≤ b.val then (x 1 - 2 * m) / x 1 ^ 2 else 0)
        * roundG (schwA m) (schwB m) a b x := by
  have hr : x 1 ≠ 0 := hx.1.ne'
  have hh : 1 - 2 * m / x 1 ≠ 0 := BothWays.schwA_ne_zero_of_mem_offRim hx
  have hrm : x 1 - 2 * m ≠ 0 := sub_ne_zero.mpr hx.2.1
  have dA : deriv (schwA m) (x 1) = 2 * m / x 1 ^ 2 := (hasDerivAt_schwA m hr).deriv
  have dB : deriv (schwB m) (x 1) = -(2 * m / x 1 ^ 2) / (1 - 2 * m / x 1) ^ 2 :=
    (hasDerivAt_schwB m hr hh).deriv
  have hF : slope b (fun z : Coords 4 ↦ z 1) = fun _ ↦ if b = 1 then 1 else 0 :=
    funext fun y ↦ slope_radius b y
  have key : hessT (roundG (schwA m) (schwB m)) (roundGinv (schwA m) (schwB m))
      (fun y ↦ y 1) a b x = -roundΓ (schwA m) (schwB m) 1 a b x := by
    rw [hessT, hF, slope_const, zero_sub]
    simp [christoffel_round, slope_radius]
  rw [key]
  fin_cases a <;> fin_cases b <;>
    simp [roundΓ_apply, rPart, θPart, qF, rF, sF, roundG, diag, roundDiag, sep, gr, gθ, negF,
      sqF, sin2, constOne, constZero, dA, dB, schwA, schwB] <;>
    field_simp
  ring

end Schw

end GravityInLean.Curved
