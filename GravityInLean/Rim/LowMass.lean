/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.OneMass.Local

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# A point whose mass is zero or negative is on Schwarzschild's space-time

Board item `task:rim-goal`, first half. For a mass that is zero or negative there is no rim: the
size of the spheres is a usable distance at every point, so the theorem that is proved already
(`localMass`) gives Schwarzschild's chart, with the mass of the point.

* `sizeSq_pos`: in a region that looks the same from every side, the squared size of the spheres
  is positive at every point;
* `usable_of_massAt_nonpos`: at a point of such a region whose mass is zero or negative, the size
  of the spheres is a usable distance. The mass is `(√σ / 2) · (1 - N / (4 σ))` with `σ > 0` the
  squared size and `N` the squared length of the step along which the spheres grow; if `N` were
  zero the mass would be `√σ / 2`, which is positive;
* `schwarzschild_of_massAt_nonpos`: so around such a point the length measure is Schwarzschild's
  of that mass in some chart.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Rim

open GravityInLean.Curved GravityInLean.Mass

open scoped Manifold ContDiff Topology

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  [IsManifold 𝓘(ℝ, Coords 4) ∞ M]

/-- **The spheres have a positive size.** In a region that looks the same from every side, the
squared size of the spheres is positive at every point: the three turning fields are not all
zero there, because they sweep out a surface, and every step on that surface has a positive
squared length. -/
theorem sizeSq_pos {g : LengthMeasure 𝓘(ℝ, Coords 4) M} {ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M}
    {s : Set M} (hr : IsRoundOn g ξ s) {p : M} (hp : p ∈ s) : 0 < sizeSq g ξ p := by
  -- The squared length of each of the three fields at `p` is zero or more.
  have hnn : ∀ i, 0 ≤ g p (ξ i p) (ξ i p) := by
    intro i
    by_cases h : ξ i p = 0
    · rw [h]
      simp
    · exact (hr.positive p hp (ξ i p) (Submodule.subset_span ⟨i, rfl⟩) h).le
  -- One of the three fields is not zero at `p`: else they would sweep out no surface.
  obtain ⟨i, hi⟩ : ∃ i, ξ i p ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hbot : Submodule.span ℝ (Set.range fun i ↦ ξ i p) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨i, rfl⟩
      exact hcon i
    have h2 := hr.surfaces p hp
    rw [hbot, finrank_bot] at h2
    exact absurd h2 (by norm_num)
  have hpos : 0 < g p (ξ i p) (ξ i p) :=
    hr.positive p hp (ξ i p) (Submodule.subset_span ⟨i, rfl⟩) hi
  -- So the sum of the three squared lengths is positive.
  have hsum : 0 < ∑ i : Fin 3, g p (ξ i p) (ξ i p) :=
    Finset.sum_pos' (fun i _ ↦ hnn i) ⟨i, Finset.mem_univ i, hpos⟩
  rw [Fin.sum_univ_three] at hsum
  rw [sizeSq]
  linarith

/-- **With a mass that is zero or negative, the size of the spheres is a usable distance.** At a
point of a region that looks the same from every side, if the mass of the point is zero or
negative, the step along which the spheres grow has a squared length that is not zero: with a
squared length zero the mass would be half the size of the sphere, which is positive. -/
theorem usable_of_massAt_nonpos {g : LengthMeasure 𝓘(ℝ, Coords 4) M}
    {ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M} {s : Set M} (hr : IsRoundOn g ξ s) {p : M}
    (hp : p ∈ s) {m : ℝ} (hmass : MassAt g ξ p m) (hm : m ≤ 0) : UsableDistanceAt g ξ p := by
  obtain ⟨n, hn, rfl⟩ := hmass
  refine ⟨n, hn, fun h0 ↦ ?_⟩
  have hσ : 0 < sizeSq g ξ p := sizeSq_pos hr hp
  have hpos : 0 < massOf (sizeSq g ξ p) (g p n n) := by
    rw [h0, massOf, zero_div, sub_zero, mul_one]
    exact half_pos (Real.sqrt_pos.mpr hσ)
  exact absurd hm (not_le.mpr hpos)

variable (M) in
/-- **A point whose mass is zero or negative is on Schwarzschild's space-time.** In a space-time
that is empty and looks the same from every side, a point of the region that has the mass `m`,
zero or negative, has a chart around it in which the length measure is Schwarzschild's of
mass `m`. -/
theorem schwarzschild_of_massAt_nonpos
    (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M) (s : Set M)
    (hs : IsOpen s) (hg : IsSpaceTimeOn g s) (he : Curved.IsEmptyOn g s) (hr : IsRoundOn g ξ s)
    (p : M) (hp : p ∈ s) {m : ℝ} (hm : m ≤ 0) (hmass : MassAt g ξ p m) :
    IsSchwarzschildWith m g p := by
  obtain ⟨m', hm', hS⟩ := localMass M g ξ s hs hg he hr p hp
  -- The mass of the chart is the mass of the point: a point has at most one mass.
  have hnd : Nondegenerate fun v w : TangentSpace 𝓘(ℝ, Coords 4) p ↦ g p v w :=
    (hg.oneTime p hp).nondegenerate (hg.symm p hp)
  have e : m' = m := massAt_unique hnd hm'.self_of_nhds hmass
  rw [← e]
  exact hS (usable_of_massAt_nonpos hr hp hmass hm)

end GravityInLean.Rim
