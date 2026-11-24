/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Rim.RadiusSmooth
public import GravityInLean.Join.UsableSlope

import Mathlib.Tactic

/-!
# On the rim of Kruskal's table the size of the spheres is no usable distance

Board item `task:rim-not-usable`. In Kruskal's table the squared size of the spheres is `r²`,
with `r = kruskalR m (X² - T²)`. Its slope is a multiple of `X dX - T dT`. The only step that
the length measure turns into that slope is a multiple of `(T, X, 0, 0)`, and the squared length
of that step is a multiple of `X² - T²`: zero on the rim, and where the two rims cross. So
`UsableDistanceAt` fails there (`kruskalNotUsableOnRim`).

* `kruskalA_pos'`: the factor in front of `-dT² + dX²` is positive on Kruskal's region;
* `kruskal_sizeSq_eventuallyEq`: near a point off the poles the squared size of the spheres is
  `r²`;
* `hasFDerivAt_kruskal_sizeSq`: the slope of `r²`, as a function of the four coordinates;
* `kruskalNotUsableOnRim`: the statement of `Goals/EveryPoint.lean`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Filter Topology Set

/-- For a positive mass, the factor in front of `-dT² + dX²` in Kruskal's table is positive
wherever `X² - T² > -1`. -/
theorem kruskalA_pos' {m T X : ℝ} (hm : 0 < m) (hu : -1 < X ^ 2 - T ^ 2) :
    0 < kruskalA m T X :=
  mul_pos (div_pos (by positivity) (kruskalR_pos hm hu)) (Real.exp_pos _)

/-- Near a point off the poles, the squared size of the spheres of Kruskal's table is `r²`, with
`r` the radius that belongs to `X² - T²`. -/
theorem kruskal_sizeSq_eventuallyEq (m : ℝ) {x : Coords 4} (hs : sin (x 2) ≠ 0) :
    sizeSq (flatMeasure (tableMeasure (kruskalG m))) turns
      =ᶠ[𝓝 x] fun y ↦ kruskalR m (coordL 1 y ^ 2 - coordL 0 y ^ 2) ^ 2 := by
  have hopen : IsOpen {y : Coords 4 | sin (y 2) ≠ 0} :=
    isOpen_ne_fun (Real.continuous_sin.comp (continuous_apply 2)) continuous_const
  filter_upwards [hopen.mem_nhds hs] with y hy
  rw [Join.sizeSq_of_genG (h := kruskalG m) (fun _ _ ↦ rfl) hy]
  simp [kruskalG, genG, sep2, gTR, gΘ, constOne, kruskalS]

/-- The slope of `r²` as a function of the four coordinates, where `r` is the radius that belongs
to `X² - T²` and `c` is the slope of the radius there: it is `4 r c (X dX - T dT)`. -/
theorem hasFDerivAt_kruskal_sizeSq {m c : ℝ} {x : Coords 4}
    (hR : HasDerivAt (kruskalR m) c (x 1 ^ 2 - x 0 ^ 2)) :
    HasFDerivAt (fun y : Coords 4 ↦ kruskalR m (coordL 1 y ^ 2 - coordL 0 y ^ 2) ^ 2)
      ((4 * kruskalR m (x 1 ^ 2 - x 0 ^ 2) * c)
        • (x 1 • coordL (n := 4) 1 - x 0 • coordL (n := 4) 0)) x := by
  have h1 : HasFDerivAt (fun y : Coords 4 ↦ coordL 1 y ^ 2) _ x :=
    ((coordL (n := 4) 1).hasFDerivAt (x := x)).pow 2
  have h0 : HasFDerivAt (fun y : Coords 4 ↦ coordL 0 y ^ 2) _ x :=
    ((coordL (n := 4) 0).hasFDerivAt (x := x)).pow 2
  have h2 : HasFDerivAt (fun y : Coords 4 ↦ coordL 1 y ^ 2 - coordL 0 y ^ 2) _ x := h1.sub h0
  have h3 : HasFDerivAt (fun y : Coords 4 ↦ kruskalR m (coordL 1 y ^ 2 - coordL 0 y ^ 2)) _ x :=
    HasDerivAt.comp_hasFDerivAt (f := fun y : Coords 4 ↦ coordL 1 y ^ 2 - coordL 0 y ^ 2) x hR h2
  have h4 : HasFDerivAt
      (fun y : Coords 4 ↦ kruskalR m (coordL 1 y ^ 2 - coordL 0 y ^ 2) ^ 2) _ x := h3.pow 2
  refine h4.congr_fderiv ?_
  ext w
  simp only [smul_apply, sub_apply, coordL_apply,
    smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  ring

/-- **On the rim of Kruskal's table the size of the spheres is not a usable distance,** and
neither where the two rims cross. The step that the length measure turns into the slope of the
squared size is fixed by the table, and where `X² = T²` its own squared length is zero. -/
theorem kruskalNotUsableOnRim : KruskalNotUsableOnRim := by
  intro m hm x hx hrim hu
  have hA : 0 < kruskalA m (x 0) (x 1) := kruskalA_pos' hm hx.1
  -- The slope of the radius at `X² - T²`; its value plays no part.
  obtain ⟨c, hR⟩ : ∃ c, HasDerivAt (kruskalR m) c (x 1 ^ 2 - x 0 ^ 2) :=
    ⟨_, hasDerivAt_kruskalR hm hx.1⟩
  have hev := kruskal_sizeSq_eventuallyEq m hx.2
  have hd := hasFDerivAt_kruskal_sizeSq hR
  -- The step that the usable distance gives, in the words of tables.
  obtain ⟨n, hn, hnn⟩ : ∃ n : Coords 4,
      (∀ w : Coords 4, tableMeasure (kruskalG m) x n w
          = 4 * kruskalR m (x 1 ^ 2 - x 0 ^ 2) * c * (x 1 * w 1 - x 0 * w 0))
        ∧ tableMeasure (kruskalG m) x n n ≠ 0 := by
    obtain ⟨n, hn, hnn⟩ := hu
    refine ⟨n, fun w ↦ ?_, hnn⟩
    have hw := hn w
    rw [mvfderiv_flat, hev.fderiv_eq, hd.fderiv] at hw
    have e : ((4 * kruskalR m (x 1 ^ 2 - x 0 ^ 2) * c)
          • (x 1 • coordL (n := 4) 1 - x 0 • coordL (n := 4) 0)) w
        = 4 * kruskalR m (x 1 ^ 2 - x 0 ^ 2) * c * (x 1 * w 1 - x 0 * w 0) := by
      simp
    rw [← e]
    exact hw
  -- Kruskal's table, written out for the step `n`.
  have hform : ∀ w : Coords 4, tableMeasure (kruskalG m) x n w
      = -kruskalA m (x 0) (x 1) * n 0 * w 0 + kruskalA m (x 0) (x 1) * n 1 * w 1
        + kruskalS m (x 0) (x 1) * n 2 * w 2
        + kruskalS m (x 0) (x 1) * sin (x 2) ^ 2 * n 3 * w 3 := by
    intro w
    have h1 : tableMeasure (kruskalG m) x n w
        = -kruskalA m (x 0) (x 1) * n 0 * w 0 + zero2 (x 0) (x 1) * (n 0 * w 1 + n 1 * w 0)
          + kruskalA m (x 0) (x 1) * n 1 * w 1 + kruskalS m (x 0) (x 1) * n 2 * w 2
          + kruskalS m (x 0) (x 1) * sin (x 2) ^ 2 * n 3 * w 3 :=
      Join.tableMeasure_of_genG (h := kruskalG m) (fun _ _ ↦ rfl) n w
    have hz : zero2 (x 0) (x 1) = 0 := rfl
    rw [h1, hz]
    ring
  -- Measured against a step along `T`, and against a step along `X`.
  have s00 : (Pi.single 0 1 : Coords 4) 0 = 1 := by simp
  have s01 : (Pi.single 0 1 : Coords 4) 1 = 0 := by simp
  have s02 : (Pi.single 0 1 : Coords 4) 2 = 0 := by simp
  have s03 : (Pi.single 0 1 : Coords 4) 3 = 0 := by simp
  have s10 : (Pi.single 1 1 : Coords 4) 0 = 0 := by simp
  have s11 : (Pi.single 1 1 : Coords 4) 1 = 1 := by simp
  have s12 : (Pi.single 1 1 : Coords 4) 2 = 0 := by simp
  have s13 : (Pi.single 1 1 : Coords 4) 3 = 0 := by simp
  have hn0 : kruskalA m (x 0) (x 1) * n 0
      = 4 * kruskalR m (x 1 ^ 2 - x 0 ^ 2) * c * x 0 := by
    have h0 := hn (Pi.single 0 1)
    rw [hform, s00, s01, s02, s03] at h0
    linarith
  have hn1 : kruskalA m (x 0) (x 1) * n 1
      = 4 * kruskalR m (x 1 ^ 2 - x 0 ^ 2) * c * x 1 := by
    have h1 := hn (Pi.single 1 1)
    rw [hform, s10, s11, s12, s13] at h1
    linarith
  -- So the squared length of `n` is a multiple of `X² - T²`: zero.
  apply hnn
  rw [hn n]
  have hmul : kruskalA m (x 0) (x 1)
      * (4 * kruskalR m (x 1 ^ 2 - x 0 ^ 2) * c * (x 1 * n 1 - x 0 * n 0)) = 0 := by
    linear_combination (4 * kruskalR m (x 1 ^ 2 - x 0 ^ 2) * c * x 1) * hn1
      - (4 * kruskalR m (x 1 ^ 2 - x 0 ^ 2) * c * x 0) * hn0
      + (4 * kruskalR m (x 1 ^ 2 - x 0 ^ 2) * c) ^ 2 * hrim
  exact (mul_eq_zero.mp hmul).resolve_left hA.ne'

end GravityInLean.Curved
