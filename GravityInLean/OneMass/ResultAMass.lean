/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.OneMass.MassCarry
public import GravityInLean.Join.ResultA

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Result A with the mass: around every point the space-time is a table of functions

Board item `task:checks-mass-result-a`. `resultA` (`Join/ResultA.lean`) again, for every point
of the region, usable distance or not. Added: the usable distance carries over to the chart if it
holds at the point, and the mass comes back from the chart at every point of the chart's domain.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Mass

open GravityInLean.Curved GravityInLean.Join

open scoped Manifold ContDiff Topology

/-- **Result A with the mass.** A space-time on a curved space that is empty and looks the same
from every side is, in a chart around any point `p` of the region, a good table of functions with
three fields that turn; the table is empty and has one time direction on the whole image of the
chart. If the size of the spheres is a usable distance at `p`, it is one at the image of `p`. A
mass that the table has at the image of a point of the chart's domain is the mass of that
point. -/
theorem resultA_mass (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M]
    (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M) (s : Set M)
    (hs : IsOpen s) (hg : IsSpaceTimeOn g s) (he : Curved.IsEmptyOn g s) (hr : IsRoundOn g ξ s)
    (p : M) (hp : p ∈ s) :
    ∃ (c : OpenPartialHomeomorph M (Coords 4)) (g' g'inv : Fin 4 → Fin 4 → Coords 4 → ℝ)
      (ξ' : Fin 3 → Fin 4 → Coords 4 → ℝ),
      c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M ∧ p ∈ c.source ∧
      IsRegularTableOn g' g'inv c.target ∧ TurnsOn g' ξ' c.target ∧
      (∀ x ∈ c.target, IsRicciFlatAt g' g'inv x) ∧
      (∀ x ∈ c.target, HasOneTimeDirection fun v w : Coords 4 ↦ tableMeasure g' x v w) ∧
      (UsableDistanceAt g ξ p →
        UsableDistanceAt (flatMeasure (tableMeasure g')) (fun i ↦ fieldOf (ξ' i)) (c p)) ∧
      (∀ q ∈ c.source, ∀ m : ℝ,
        MassAt (flatMeasure (tableMeasure g')) (fun i ↦ fieldOf (ξ' i)) (c q) m →
          MassAt g ξ q m) ∧
      ∀ q ∈ c.source, ∀ v w : TangentSpace 𝓘(ℝ, Coords 4) q,
        g q v w = tableMeasure g' (c q) (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) c q v)
          (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) c q w) := by
  -- The chart at `p`, cut down to the region.
  have hc₀ : chartAt (Coords 4) p ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M :=
    IsManifold.chart_mem_maximalAtlas p
  set c : OpenPartialHomeomorph M (Coords 4) := (chartAt (Coords 4) p).restrOpen s hs with hcdef
  have hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M :=
    chart_restrOpen_mem_maximalAtlas hc₀ hs
  have hsrc : c.source ⊆ s := fun q hq ↦ by
    rw [hcdef, chart_restrOpen_source] at hq
    exact hq.2
  have hpc : p ∈ c.source := by
    rw [hcdef, chart_restrOpen_source]
    exact ⟨mem_chart_source (Coords 4) p, hp⟩
  -- Everything carries over to coordinate space.
  have hST := isSpaceTimeOn_carry hc hsrc hg
  have hRd := isRoundOn_carry hc hsrc hr
  have hLM := hST.isLengthMeasureOn
  have hopen : IsOpen c.target := c.open_target
  obtain ⟨A, hA₀, hAd⟩ := exists_flatTransport_of_isLengthMeasureOn hopen hLM
  have hEm : Curved.IsEmptyOn (flatMeasure (carryMeasure c g)) c.target := by
    obtain ⟨cov, hcov, hric⟩ := he
    have h' := isConnectionOf_carry hc hsrc hg.smooth hcov
    refine isEmptyOn_carry_of hc hsrc h' hric
      (fun q hq u v w ↦ curvatureAt_carry hc hsrc hcov hLM hA₀ h' hAd hq u v w)
      (fun q hq v' w' ↦ curvatureAt_linear_of_isConnectionOf hLM hA₀ h' (c.map_source hq)
        (hAd _ (c.map_source hq)) v' w')
  -- The fields of the table are the carried fields.
  have e : (fun i ↦ fieldOf (partsOf (fun i ↦ carryField c (ξ i)) i))
      = fun i ↦ carryField c (ξ i) := funext fun i ↦ fieldOf_partsOf _ i
  -- From the words of curved spaces to tables.
  refine ⟨c, tableOf (carryMeasure c g), invT (tableOf (carryMeasure c g)),
    partsOf (fun i ↦ carryField c (ξ i)), hc, hpc, isRegularTableOn_tableOf hopen hLM,
    turnsOn_of_isRoundOn hLM hRd, isRicciFlatAt_of_isEmptyOn hopen hLM hEm, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [tableMeasure_tableOf]
    exact hST.oneTime x hx
  · intro hu
    rw [tableMeasure_tableOf, e]
    exact usableDistanceAt_carry hc hsrc hg hr hpc hu
  · intro q hq m hm
    rw [tableMeasure_tableOf, e] at hm
    exact massAt_of_carry hc hq hm
  · intro q hq v w
    rw [tableMeasure_tableOf]
    exact carryMeasure_formula hc g hq v w

end GravityInLean.Mass
