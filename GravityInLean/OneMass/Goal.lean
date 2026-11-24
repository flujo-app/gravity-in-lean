/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.OneMass
public import GravityInLean.OneMass.Local
public import GravityInLean.OneMass.Connected

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# One mass for a whole region

Board item `task:checks-mass-goal`. The statement `OneMassStatement` of `Goals/OneMass.lean`.
Every point of the region has a mass, said without coordinates (`MassAt`), and at most one. Near
every point the mass is the same (`localMass`), so on a region in one piece it is the same
everywhere (`exists_const_of_locally`). At a point where the size of the spheres is a usable
distance, the chart that shows the length measure to be Schwarzschild's does so with the mass of
that point, which is the mass of the region.
-/

@[expose] public section

namespace GravityInLean

open GravityInLean.Curved GravityInLean.Mass

open scoped Manifold ContDiff Topology

/-- **One mass for a whole region.** On an open region in one piece where the length measure is a
space-time, is empty and looks the same from every side, there is one mass `m` such that around
every point of the region where the size of the spheres is a usable distance, the length measure
is Schwarzschild's of that mass `m` in some chart. -/
theorem oneMass : Curved.OneMassStatement := by
  intro M _ _ _ g ξ s hs hconn hg he hr
  have hnd : ∀ q ∈ s, Nondegenerate fun v w : TangentSpace 𝓘(ℝ, Coords 4) q ↦ g q v w :=
    fun q hq ↦ (hg.oneTime q hq).nondegenerate (hg.symm q hq)
  -- One mass for all points of the region.
  obtain ⟨m, hm⟩ := exists_const_of_locally hconn (R := fun q m ↦ MassAt g ξ q m)
    (fun q hq m m' h h' ↦ massAt_unique (hnd q hq) h h')
    (fun p hp ↦ (localMass M g ξ s hs hg he hr p hp).imp fun m h ↦ h.1)
  refine ⟨m, fun p hp hu ↦ ?_⟩
  -- At a point with a usable distance, the chart has the mass of that point.
  obtain ⟨m', hm', hS⟩ := localMass M g ξ s hs hg he hr p hp
  have e : m' = m := massAt_unique (hnd p hp) hm'.self_of_nhds (hm p hp)
  rw [← e]
  exact hS hu

end GravityInLean
