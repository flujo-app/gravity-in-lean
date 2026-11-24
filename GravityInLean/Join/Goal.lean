/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Join.ResultA
public import GravityInLean.Join.ResultB
public import GravityInLean.Join.Atlas

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Birkhoff's theorem with no coordinates at all

Board item `task:join-goal`. The goal of `Curved/Goal.lean`, from Result A (a chart in which the
space-time is a table of functions), Result B (Birkhoff's theorem for a table in any
coordinates) and the chain rule.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean

open GravityInLean.Curved GravityInLean.Join

open scoped Manifold ContDiff Topology

/-- **Birkhoff's theorem with no coordinates at all.** A space-time on a curved space that is
empty and looks the same from every side is Schwarzschild's, in a chart around every point where
the size of the spheres is a usable distance. -/
theorem birkhoffNoCoordinates : Curved.BirkhoffNoCoordinates := by
  intro M _ _ _ g ξ s hs hg he hr p hp hu
  obtain ⟨c, g', g'inv, ξ', hc, hpc, hreg, hturn, hflat, htime, hu', hform⟩ :=
    resultA M g ξ s hs hg he hr p hp hu
  obtain ⟨m, Ψ, hx₀, -, hΨ, hΨ', hB⟩ :=
    resultB g' g'inv ξ' c.target (c p) hreg hturn hflat htime (c.map_source hpc) hu'
  refine ⟨m, c.trans Ψ, trans_mem_maximalAtlas hc hΨ hΨ', ?_, fun q hq ↦ ?_⟩
  · rw [OpenPartialHomeomorph.trans_source]
    exact ⟨hpc, hx₀⟩
  · have hq' := hq
    rw [OpenPartialHomeomorph.trans_source] at hq'
    obtain ⟨hqc, hqΨ⟩ := hq'
    have hq2 : c q ∈ Ψ.source := hqΨ
    obtain ⟨hreg', hlen⟩ := hB (c q) hq2
    refine ⟨hreg', fun v w ↦ ?_⟩
    rw [hform q hqc v w, hlen, mfderiv_trans_apply hc hΨ hq v,
      mfderiv_trans_apply hc hΨ hq w]
    rfl

end GravityInLean
