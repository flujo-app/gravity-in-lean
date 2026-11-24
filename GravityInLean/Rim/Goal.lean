/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.EveryPoint
public import GravityInLean.Rim.LowMass
public import GravityInLean.Rim.HighMass
public import GravityInLean.OneMass.Connected

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Birkhoff's theorem at every point, the rim included

Board item `task:rim-goal`, second half. The two last statements of `Goals/EveryPoint.lean`.

Every point of the region has a mass, said without coordinates (`MassAt`), and at most one; near
every point the mass is the same (`localMass`). The two cases:

* the mass is positive: the length measure is Kruskal's of that mass in a chart around the point
  (`Rim.kruskalNear_of_massAt_pos`), whether the point is on the rim or not;
* the mass is zero or negative: the size of the spheres is a usable distance, and the length
  measure is Schwarzschild's of that mass in a chart around the point
  (`Rim.schwarzschild_of_massAt_nonpos`).

On a region in one piece the mass is the same at all points (`exists_const_of_locally`), so one
of the two cases holds for the whole region.
-/

@[expose] public section

namespace GravityInLean.Curved

open GravityInLean.Mass

open scoped Manifold ContDiff Topology

/-- **Birkhoff's theorem at every point, the rim included.** Around every point of a region on
which the length measure is a space-time, is empty and looks the same from every side, the
length measure is Kruskal's of a positive mass in some chart, or Schwarzschild's of a mass that
is zero or negative in some chart. Nothing is asked of the size of the spheres at the point. -/
theorem birkhoffAtEveryPoint : BirkhoffAtEveryPoint := by
  intro M _ _ _ g ξ s hs hg he hr p hp
  -- The mass of the point.
  obtain ⟨m, hm, -⟩ := localMass M g ξ s hs hg he hr p hp
  have hmass : MassAt g ξ p m := hm.self_of_nhds
  rcases lt_or_ge 0 m with h | h
  · exact Or.inl ⟨m, h, Rim.kruskalNear_of_massAt_pos M g ξ s hs hg he hr p hp h hmass⟩
  · exact Or.inr ⟨m, h, Rim.schwarzschild_of_massAt_nonpos M g ξ s hs hg he hr p hp h hmass⟩

/-- **The same, with one mass for a whole region.** On an open region in one piece where the
length measure is a space-time, is empty and looks the same from every side, there is either one
positive mass such that the length measure is Kruskal's of that mass around every point, or one
mass that is zero or negative such that it is Schwarzschild's of that mass around every point. -/
theorem birkhoffAtEveryPointOneMass : BirkhoffAtEveryPointOneMass := by
  intro M _ _ _ g ξ s hs hconn hg he hr
  have hnd : ∀ q ∈ s, Nondegenerate fun v w : TangentSpace 𝓘(ℝ, Coords 4) q ↦ g q v w :=
    fun q hq ↦ (hg.oneTime q hq).nondegenerate (hg.symm q hq)
  -- One mass for all points of the region.
  obtain ⟨m, hm⟩ := exists_const_of_locally hconn (R := fun q m ↦ MassAt g ξ q m)
    (fun q hq m m' h h' ↦ massAt_unique (hnd q hq) h h')
    (fun p hp ↦ (localMass M g ξ s hs hg he hr p hp).imp fun m h ↦ h.1)
  rcases lt_or_ge 0 m with h | h
  · exact Or.inl ⟨m, h, fun p hp ↦
      Rim.kruskalNear_of_massAt_pos M g ξ s hs hg he hr p hp h (hm p hp)⟩
  · exact Or.inr ⟨m, h, fun p hp ↦
      Rim.schwarzschild_of_massAt_nonpos M g ξ s hs hg he hr p hp h (hm p hp)⟩

end GravityInLean.Curved
