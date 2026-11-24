/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.ConverseEmpty
public import GravityInLean.Global.ConverseRoundKruskal
public import GravityInLean.Global.ConverseRoundSchw

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# A space-time with a length-keeping map into a model is round and empty

The two halves ("empty", "round") for the two kinds of model, put together.
-/

@[expose] public section

namespace GravityInLean.Curved

open scoped Manifold ContDiff

/-- **The other way round:** a space-time with a length-keeping map into Kruskal's whole
space-time, or into Schwarzschild's whole space-time of a mass that is zero or negative missing
the centre, is empty and looks the same from every side. -/
theorem globalBirkhoffConverse : GlobalBirkhoffConverse := by
  intro M _ _ _ g s hg h
  rcases h with ⟨m, hm, D, hD⟩ | ⟨m, hm, D, hD, hoff⟩
  · obtain ⟨ξ, hξ⟩ := hD.exists_round hm hg
    exact ⟨ξ, hD.isEmptyOn hm hg, hξ⟩
  · obtain ⟨ξ, hξ⟩ := hD.exists_round hm hg hoff
    exact ⟨ξ, hD.isEmptyOn hm hg, hξ⟩

end GravityInLean.Curved
