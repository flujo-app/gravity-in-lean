/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Curved.KnownAnswers
public import Mathlib.Geometry.Manifold.IsManifold.Basic

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# The goal: Birkhoff's theorem with no coordinates at all

This file states the theorem that the work on curved spaces is aiming at. **It is a statement,
not a theorem: `BirkhoffNoCoordinates` is not proved anywhere in this project yet.**

In words: take a space-time with four dimensions that is empty and looks the same from every
side. Then around every point where the size of the spheres can serve as a distance, there is a
chart in which the length measure is exactly Schwarzschild's.

Two more notions are needed to say that, and both are tested here on Schwarzschild's space-time
before they are used:

* `sizeSq`: the squared size of the spheres, read off from the three turning fields
  (`schwarzschild_sizeSq`: for Schwarzschild's space-time it is `r²`).
* `UsableDistanceAt`: the size of the spheres is a usable distance at a point
  (`schwarzschild_usable`: true everywhere off the rim).

**The assumptions can be met.** Schwarzschild's space-time meets all assumptions of the goal at
once (`schwarzschild_meets_goal`). So the goal is not a statement about nothing.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Filter Topology Set

open scoped Manifold ContDiff

/-! ## The size of the spheres -/

section Size

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **The squared size of the spheres** that the three turning fields sweep out: half the sum of
the squared lengths of the three fields. On a sphere of radius `r` in ordinary space the three
turns have squared lengths that add up to `2 r²`, so this is `r²`. No coordinates are needed to
say it. -/
noncomputable def sizeSq (g : LengthMeasure I M) (ξ : Fin 3 → Arrows I M) (x : M) : ℝ :=
  (g x (ξ 0 x) (ξ 0 x) + g x (ξ 1 x) (ξ 1 x) + g x (ξ 2 x) (ξ 2 x)) / 2

/-- **The size of the spheres is a usable distance at `p`.** There is a step `n` at `p` that
points the way the spheres grow (it turns the length measure into the slope of `sizeSq`), and its
own squared length is not zero: the spheres do not grow along a path of light. On the rim of a
black hole this fails. -/
def UsableDistanceAt (g : LengthMeasure I M) (ξ : Fin 3 → Arrows I M) (p : M) : Prop :=
  ∃ n : TangentSpace I p,
    (∀ w : TangentSpace I p, g p n w = d% (sizeSq g ξ) p w) ∧ g p n n ≠ 0

end Size

/-! ## Both notions, tested on Schwarzschild's space-time -/

section Tests

/-- For a round table, the squared size of the spheres is the square of the distance label. -/
theorem round_sizeSq (A B : ℝ → ℝ) {x : Coords 4} (hs : sin (x 2) ≠ 0) :
    sizeSq (flatMeasure (tableMeasure (roundG A B))) turns x = x 1 ^ 2 := by
  have hN : negCot (x 2) ^ 2 * sin (x 2) ^ 2 = cos (x 2) ^ 2 := by
    rw [negCot]
    field_simp
  have hθ := Real.sin_sq_add_cos_sq (x 2)
  have hφ := Real.sin_sq_add_cos_sq (x 3)
  have e : sizeSq (flatMeasure (tableMeasure (roundG A B))) turns x
      = (tableMeasure (roundG A B) x (fun k ↦ rotY k x) (fun k ↦ rotY k x)
        + tableMeasure (roundG A B) x (fun k ↦ rotX k x) (fun k ↦ rotX k x)
        + tableMeasure (roundG A B) x (fun k ↦ rotZ k x) (fun k ↦ rotZ k x)) / 2 := rfl
  rw [e]
  simp only [round_measure_apply, Fin.sum_univ_four]
  simp [roundDiag, sep, gr, gθ, sqF, sin2, constOne, rotX, rotY, rotZ, sepA, negSin]
  linear_combination (x 1 ^ 2 / 2 * (1 + cos (x 2) ^ 2)) * hφ + (x 1 ^ 2 / 2) * hθ
    + (x 1 ^ 2 / 2 * (sin (x 3) ^ 2 + cos (x 3) ^ 2)) * hN

/-- For a round table, the size of the spheres is a usable distance wherever the table is good:
away from the centre and the poles, and where the ruler function is not zero. -/
theorem round_usable (A B : ℝ → ℝ) {x : Coords 4} (hr : x 1 ≠ 0) (hB : B (x 1) ≠ 0)
    (hs : sin (x 2) ≠ 0) :
    UsableDistanceAt (flatMeasure (tableMeasure (roundG A B))) turns x := by
  -- Near `x` the squared size of the spheres is the square of the distance label.
  have hev : sizeSq (flatMeasure (tableMeasure (roundG A B))) turns
      =ᶠ[𝓝 x] fun y ↦ coordL 1 y ^ 2 := by
    have hopen : IsOpen {y : Coords 4 | sin (y 2) ≠ 0} :=
      isOpen_ne_fun (Real.continuous_sin.comp (continuous_apply 2)) continuous_const
    filter_upwards [hopen.mem_nhds hs] with y hy
    exact round_sizeSq A B hy
  have hd := ((coordL (n := 4) 1).hasFDerivAt (x := x)).pow 2
  refine ⟨(2 * x 1 / B (x 1)) • (Pi.single 1 1 : Coords 4), fun w ↦ ?_, ?_⟩
  · rw [mvfderiv_flat, hev.fderiv_eq, hd.fderiv]
    change tableMeasure (roundG A B) x ((2 * x 1 / B (x 1)) • Pi.single 1 1) w
      = ((2 • coordL 1 x ^ (2 - 1)) • coordL 1) w
    rw [round_measure_apply]
    simp [Fin.sum_univ_four, roundDiag, sep, gr, gθ, constOne]
    field_simp
    exact Or.inl trivial
  · change tableMeasure (roundG A B) x ((2 * x 1 / B (x 1)) • Pi.single 1 1)
      ((2 * x 1 / B (x 1)) • Pi.single 1 1) ≠ 0
    rw [round_measure_apply]
    have e : ∑ a, roundDiag A B a x * ((2 * x 1 / B (x 1)) • (Pi.single 1 1 : Coords 4)) a
          * ((2 * x 1 / B (x 1)) • (Pi.single 1 1 : Coords 4)) a
        = 4 * x 1 ^ 2 / B (x 1) := by
      simp [Fin.sum_univ_four, roundDiag, sep, gr, gθ, constOne]
      field_simp
      ring
    rw [e]
    exact div_ne_zero (mul_ne_zero four_ne_zero (pow_ne_zero 2 hr)) hB

/-- For Schwarzschild's space-time the squared size of the spheres is `r²`. -/
theorem schwarzschild_sizeSq (M : ℝ) {x : Coords 4} (hs : sin (x 2) ≠ 0) :
    sizeSq (flatMeasure (tableMeasure (roundG (schwA M) (schwB M)))) turns x = x 1 ^ 2 :=
  round_sizeSq _ _ hs

/-- For Schwarzschild's space-time the size of the spheres is a usable distance everywhere
outside the rim. -/
theorem schwarzschild_usable (M : ℝ) {x : Coords 4} (hx : x ∈ outside M) :
    UsableDistanceAt (flatMeasure (tableMeasure (roundG (schwA M) (schwB M)))) turns x :=
  round_usable _ _ hx.1.ne' (inv_ne_zero (schwA_pos_outside hx.1 hx.2.1).ne') hx.2.2

/-- And inside the rim as well. Only on the rim itself it is not. -/
theorem schwarzschild_usable_inside (M : ℝ) {x : Coords 4} (hx : x ∈ inside M) :
    UsableDistanceAt (flatMeasure (tableMeasure (roundG (schwA M) (schwB M)))) turns x :=
  round_usable _ _ hx.1.ne' (inv_ne_zero (schwA_neg_inside hx.1 hx.2.1).ne) hx.2.2

end Tests

/-! ## The goal -/

/-- **The goal: Birkhoff's theorem with no coordinates at all.** A statement, not yet a theorem.

Take a curved space `M` with four dimensions, a length measure `g` on it and three fields of
arrows `ξ`, and an open region `s` on which

* `g` is a space-time: smooth, with exactly one time direction;
* space is empty: Einstein's equation without matter holds;
* the space-time looks the same from every side: the three fields leave `g` unchanged, combine
  the way turns do, and sweep out surfaces on which all lengths are positive.

Then around every point `p` of the region where the size of the spheres is a usable distance,
there are a mass `m` and a chart `φ` of the curved space in which `g` is Schwarzschild's length
measure for the mass `m`: the length of any two steps at a point `q`, measured with `g`, is what
Schwarzschild's table gives at the point `φ q` for the two steps as the chart sees them. The
chart lands off the rim, off the centre and off the poles, where Schwarzschild's table is good.

No coordinates are given at the start. The proof has to find them. -/
def BirkhoffNoCoordinates : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M]
    (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M) (s : Set M),
    IsOpen s → IsSpaceTimeOn g s → IsEmptyOn g s → IsRoundOn g ξ s →
    ∀ p ∈ s, UsableDistanceAt g ξ p →
      ∃ (m : ℝ) (φ : OpenPartialHomeomorph M (Coords 4)),
        φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M ∧ p ∈ φ.source ∧
        ∀ q ∈ φ.source, (φ q ∈ outside m ∨ φ q ∈ inside m) ∧
          ∀ v w : TangentSpace 𝓘(ℝ, Coords 4) q,
            g q v w = flatMeasure (tableMeasure (roundG (schwA m) (schwB m))) (φ q)
              (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q v)
              (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q w)

/-- **The assumptions of the goal can be met.** Schwarzschild's space-time, outside the rim,
meets all of them at once: it is a space-time, it is empty, it looks the same from every side,
and the size of its spheres is a usable distance at every point. -/
theorem schwarzschild_meets_goal (M : ℝ) :
    IsOpen (outside M)
      ∧ IsSpaceTimeOn (flatMeasure (tableMeasure (roundG (schwA M) (schwB M)))) (outside M)
      ∧ IsEmptyOn (flatMeasure (tableMeasure (roundG (schwA M) (schwB M)))) (outside M)
      ∧ IsRoundOn (flatMeasure (tableMeasure (roundG (schwA M) (schwB M)))) turns (outside M)
      ∧ ∀ p ∈ outside M,
        UsableDistanceAt (flatMeasure (tableMeasure (roundG (schwA M) (schwB M)))) turns p :=
  ⟨isOpen_outside M, schwarzschild_isSpaceTimeOn_outside M, schwarzschild_isEmptyOn M,
    schwarzschild_isRoundOn M, fun _ hp ↦ schwarzschild_usable M hp⟩

end GravityInLean.Curved
