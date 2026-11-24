/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Rim.RadiusSmooth
public import GravityInLean.Checks.EfRound

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Kruskal's table is round, and it is "Kruskal's in a chart"

Board item `task:rim-round`. Two of the statements of `Goals/EveryPoint.lean`, both about
Kruskal's table alone:

* `kruskalIsRound`: for a positive mass, Kruskal's table looks the same from every side on all
  of its region, the rim included. The table has the general round shape `genG`, its entry for
  the pole angle is the squared radius, which is positive, and all its entries are smooth
  because the radius is. So `roundShape_isRoundOn` applies.
* `kruskalMeetsConclusion`: Kruskal's own table is "Kruskal's in a chart" around each of its
  points: the chart that does nothing, cut down to Kruskal's region.

What is needed on the way (names end in `'` where another file of this folder proves the same):

* `isOpen_kruskalRegion'`: Kruskal's region is open;
* `twiceSmooth_kruskalR'`, `twiceSmooth_kruskalA'`, `twiceSmooth_kruskalS'`: the radius, the
  factor in front of `-dT² + dX²` and the squared radius are twice smoothly differentiable as
  functions of the two labels `T` and `X`, wherever `X² - T² > -1`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Filter Topology Set

open scoped Manifold ContDiff

/-- Kruskal's region is open: a point close to one of its points is in it too. -/
theorem isOpen_kruskalRegion' : IsOpen kruskalRegion :=
  (isOpen_lt continuous_const
    (((continuous_apply (1 : Fin 4)).pow 2).sub ((continuous_apply (0 : Fin 4)).pow 2))).inter
    (isOpen_ne_fun (Real.continuous_sin.comp (continuous_apply 2)) continuous_const)

/-- For a positive mass, the radius is twice smoothly differentiable as a function of the two
labels `T` and `X`, wherever `X² - T² > -1`. -/
theorem twiceSmooth_kruskalR' {m T X : ℝ} (hm : 0 < m) (h : -1 < X ^ 2 - T ^ 2) :
    TwiceSmooth (fun T X : ℝ ↦ kruskalR m (X ^ 2 - T ^ 2)) T X := by
  have h1 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ ↦ p.2 ^ 2 - p.1 ^ 2) (T, X) :=
    (contDiffAt_snd.pow 2).sub (contDiffAt_fst.pow 2)
  have h2 : ContDiffAt ℝ 2 (kruskalR m) (X ^ 2 - T ^ 2) :=
    (contDiffAt_kruskalR hm h).of_le (by norm_num)
  exact ContDiffAt.comp (g := kruskalR m) (f := fun p : ℝ × ℝ ↦ p.2 ^ 2 - p.1 ^ 2) (T, X) h2 h1

/-- For a positive mass, the factor in front of `-dT² + dX²` in Kruskal's form is twice smoothly
differentiable as a function of the two labels, wherever `X² - T² > -1`. -/
theorem twiceSmooth_kruskalA' {m T X : ℝ} (hm : 0 < m) (h : -1 < X ^ 2 - T ^ 2) :
    TwiceSmooth (kruskalA m) T X := by
  have hR : ContDiffAt ℝ 2 (fun p : ℝ × ℝ ↦ kruskalR m (p.2 ^ 2 - p.1 ^ 2)) (T, X) :=
    twiceSmooth_kruskalR' hm h
  have hne : kruskalR m (X ^ 2 - T ^ 2) ≠ 0 := (kruskalR_pos hm h).ne'
  have h1 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ ↦ 32 * m ^ 3 / kruskalR m (p.2 ^ 2 - p.1 ^ 2)) (T, X) :=
    contDiffAt_const.div hR hne
  have h2 : ContDiffAt ℝ 2
      (fun p : ℝ × ℝ ↦ Real.exp (-(kruskalR m (p.2 ^ 2 - p.1 ^ 2)) / (2 * m))) (T, X) :=
    (hR.neg.div_const (2 * m)).exp
  exact h1.mul h2

/-- For a positive mass, the squared radius is twice smoothly differentiable as a function of
the two labels, wherever `X² - T² > -1`. -/
theorem twiceSmooth_kruskalS' {m T X : ℝ} (hm : 0 < m) (h : -1 < X ^ 2 - T ^ 2) :
    TwiceSmooth (kruskalS m) T X := by
  have hR : ContDiffAt ℝ 2 (fun p : ℝ × ℝ ↦ kruskalR m (p.2 ^ 2 - p.1 ^ 2)) (T, X) :=
    twiceSmooth_kruskalR' hm h
  exact hR.pow 2

/-- **Kruskal's looks the same from every side,** rim included: for a positive mass, the three
standard turns are smooth, leave Kruskal's length measure unchanged, combine the way turns do,
and sweep out surfaces on which all lengths are positive, on all of Kruskal's region. -/
theorem kruskalIsRound : KruskalIsRound := fun m hm ↦
  roundShape_isRoundOn (A := kruskalA m) (B := kruskalA m) (C := zero2) (S := kruskalS m)
    isOpen_kruskalRegion' (fun _ hx ↦ hx.2)
    (fun x hx a b ↦
      (contDiffAt_genG (twiceSmooth_kruskalA' hm hx.1) (twiceSmooth_kruskalA' hm hx.1)
        (twiceSmooth_zero2 (x 0) (x 1)) (twiceSmooth_kruskalS' hm hx.1) a b).differentiableAt
        (by norm_num))
    (fun x hx ↦ show 0 < kruskalR m (x 1 ^ 2 - x 0 ^ 2) ^ 2 from
      pow_pos (kruskalR_pos hm hx.1) 2)

/-- **Kruskal's own table is "Kruskal's in a chart"** around each of its points, with the chart
that does nothing, cut down to Kruskal's region. So the conclusion of the theorem at every point
is formed the right way round: lengths in the space-time are Kruskal's lengths of the steps as
the chart sees them. -/
theorem kruskalMeetsConclusion : KruskalMeetsConclusion := by
  intro m _ p hp
  refine ⟨OpenPartialHomeomorph.ofSet kruskalRegion isOpen_kruskalRegion',
    StructureGroupoid.mem_maximalAtlas_of_mem_groupoid _
      (ofSet_mem_contDiffGroupoid isOpen_kruskalRegion'), hp, fun q hq ↦ ⟨hq, fun v w ↦ ?_⟩⟩
  have e : mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4)
      (OpenPartialHomeomorph.ofSet kruskalRegion isOpen_kruskalRegion') q
      = ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, Coords 4) q) := mfderiv_id
  rw [e]
  rfl

end GravityInLean.Curved
