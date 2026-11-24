/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.OneMass
public import GravityInLean.OneMass.ResultAMass
public import GravityInLean.OneMass.TableMass
public import GravityInLean.Join.Atlas

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Near every point of the region there is one mass

Board item `task:checks-mass-local`. Result A and Result B with the mass, put together as in
`Join/Goal.lean`: every point of the region, usable distance or not, has a mass that all points
near it have too; and if the size of the spheres is a usable distance at the point, the length
measure is Schwarzschild's of that mass in a chart around the point.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Mass

open GravityInLean.Curved GravityInLean.Join

open scoped Manifold ContDiff Topology

/-- **One mass near every point.** In a space-time that is empty and looks the same from every
side, every point `p` of the region has a mass `m` that all points near `p` have too. If the size
of the spheres is a usable distance at `p`, the length measure is Schwarzschild's of the mass `m`
in a chart around `p`. -/
theorem localMass (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M]
    (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M) (s : Set M)
    (hs : IsOpen s) (hg : IsSpaceTimeOn g s) (he : Curved.IsEmptyOn g s) (hr : IsRoundOn g ξ s)
    (p : M) (hp : p ∈ s) :
    ∃ m : ℝ, (∀ᶠ q in 𝓝 p, MassAt g ξ q m) ∧
      (UsableDistanceAt g ξ p → IsSchwarzschildWith m g p) := by
  obtain ⟨c, g', g'inv, ξ', hc, hpc, hreg, hturn, hflat, htime, hu', hmass, hform⟩ :=
    resultA_mass M g ξ s hs hg he hr p hp
  obtain ⟨m, hm, hB⟩ :=
    tableMass g' g'inv ξ' c.target (c p) hreg hturn hflat htime (c.map_source hpc)
  refine ⟨m, ?_, fun hu ↦ ?_⟩
  · -- The mass comes back along the chart, at all points near `p`.
    have h1 : ∀ᶠ q in 𝓝 p, q ∈ c.source := c.open_source.mem_nhds hpc
    have h2 : ∀ᶠ q in 𝓝 p,
        MassAt (flatMeasure (tableMeasure g')) (fun i ↦ fieldOf (ξ' i)) (c q) m :=
      (c.continuousAt hpc).eventually hm
    filter_upwards [h1, h2] with q hq hq2
    exact hmass q hq m hq2
  · -- The chart of the goal, as in `birkhoffNoCoordinates`.
    obtain ⟨Ψ, hx₀, -, hΨ, hΨ', hB⟩ := hB (hu' hu)
    refine ⟨c.trans Ψ, trans_mem_maximalAtlas hc hΨ hΨ', ?_, fun q hq ↦ ?_⟩
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

end GravityInLean.Mass
