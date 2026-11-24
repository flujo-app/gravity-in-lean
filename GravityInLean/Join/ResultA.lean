/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Curved.Goal
public import GravityInLean.Goals.Turns
public import GravityInLean.NewCoordinates
public import GravityInLean.Join.Carry
public import GravityInLean.Join.CarryPointwise
public import GravityInLean.Join.FlatTensor
public import GravityInLean.Join.Atlas
public import GravityInLean.Join.CarryConnection
public import GravityInLean.Join.CarryRicci
public import GravityInLean.Join.FlatToTable
public import GravityInLean.Join.CarryRound
public import GravityInLean.Join.CarryCurvature
public import GravityInLean.Join.CarryUsable

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Result A: from the curved space to a table of functions

Board item `task:join-result-a`. Around a point `p` of the region there is a chart `c` of the
curved space in which the length measure is a good table of functions `g'` and the three fields
are three fields that turn, given by their parts `ξ'`. Everything the goal assumes carries over:
empty, one time direction, the usable distance at the point. The last line is the formula that
gives `g` back from the table and the slope of the chart.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Join

open GravityInLean.Curved

open scoped Manifold ContDiff Topology

/-- **Result A.** A space-time on a curved space that is empty and looks the same from every side
is, in a chart around any point of the region, a good table of functions with three fields that
turn; the table is empty and has one time direction on the whole image of the chart, and the size
of the spheres is still a usable distance at the image of the point. -/
theorem resultA (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M]
    (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M) (s : Set M)
    (hs : IsOpen s) (hg : IsSpaceTimeOn g s) (he : Curved.IsEmptyOn g s) (hr : IsRoundOn g ξ s)
    (p : M) (hp : p ∈ s) (hu : UsableDistanceAt g ξ p) :
    ∃ (c : OpenPartialHomeomorph M (Coords 4)) (g' g'inv : Fin 4 → Fin 4 → Coords 4 → ℝ)
      (ξ' : Fin 3 → Fin 4 → Coords 4 → ℝ),
      c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M ∧ p ∈ c.source ∧
      IsRegularTableOn g' g'inv c.target ∧ TurnsOn g' ξ' c.target ∧
      (∀ x ∈ c.target, IsRicciFlatAt g' g'inv x) ∧
      (∀ x ∈ c.target, HasOneTimeDirection fun v w : Coords 4 ↦ tableMeasure g' x v w) ∧
      UsableDistanceAt (flatMeasure (tableMeasure g')) (fun i ↦ fieldOf (ξ' i)) (c p) ∧
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
  have hUs := usableDistanceAt_carry hc hsrc hg hr hpc hu
  -- From the words of curved spaces to tables.
  refine ⟨c, tableOf (carryMeasure c g), invT (tableOf (carryMeasure c g)),
    partsOf (fun i ↦ carryField c (ξ i)), hc, hpc, isRegularTableOn_tableOf hopen hLM,
    turnsOn_of_isRoundOn hLM hRd, isRicciFlatAt_of_isEmptyOn hopen hLM hEm, ?_, ?_, ?_⟩
  · intro x hx
    rw [tableMeasure_tableOf]
    exact hST.oneTime x hx
  · rw [tableMeasure_tableOf]
    have e : (fun i ↦ fieldOf (partsOf (fun i ↦ carryField c (ξ i)) i))
        = fun i ↦ carryField c (ξ i) := funext fun i ↦ fieldOf_partsOf _ i
    rw [e]
    exact hUs
  · intro q hq v w
    rw [tableMeasure_tableOf]
    exact carryMeasure_formula hc g hq v w

end GravityInLean.Join
