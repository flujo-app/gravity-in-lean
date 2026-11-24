/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.UniqueKruskal
public import GravityInLean.Global.UniqueSchw
public import GravityInLean.Global.UniqueFlat

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# The length-keeping map is unique up to a symmetry

The three cases put together: Kruskal's (positive mass), Schwarzschild's whole space-time of
negative mass, and flat space-time.
-/

@[expose] public section

namespace GravityInLean.Curved

open scoped Manifold ContDiff

/-- **The map is unique up to a symmetry:** two length-keeping maps from a region in one piece
into the same model space-time differ by one symmetry of that model. -/
theorem globalBirkhoffUnique : GlobalBirkhoffUnique := fun _ _ _ _ g s hs hg ↦
  ⟨fun _ hm D D' hD hD' ↦ unique_kruskal hs hg hm D D' hD hD',
    fun _ hm D D' hD hD' ↦ unique_schw hs hg hm D D' hD hD',
    fun D D' hD hD' ↦ unique_flat g s hs hg D D' hD hD'⟩

end GravityInLean.Curved
