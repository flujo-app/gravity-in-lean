/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.ChartChange
public import GravityInLean.Global.KruskalChart
public import GravityInLean.Global.SchwChart

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# The mass is fixed by the space-time: from tables to the curved space

`GlobalMassUnique` (`Goals/Global.lean`) says that length-keeping maps into models of two
different masses never both exist on the same region. Here it is reduced to three facts about
tables on coordinate space (`globalMassUnique_of_tables`): a map of coordinate space cannot
carry Kruskal's table of one mass to Kruskal's table of another, nor Schwarzschild's table of
one mass (zero or negative) to that of another, nor Kruskal's table to Schwarzschild's of a mass
that is zero or negative.

The step: around a point of the region each of the two length-keeping maps gives a chart of the
curved space that reads the length measure as its model's table (`KruskalChart.lean`,
`SchwChart.lean`); the change of charts is a map of coordinate space that carries the first
table to the second (`ChartChange.lean`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  {g : LengthMeasure 𝓘(ℝ, Coords 4) M}

/-- **Two charts around one point that read the length measure as two tables give a map of
coordinate space that carries the first table to the second.** The first chart lands in the set
`P`, the second in `P'`; the map (the change of charts) is defined on an open set `W` inside
`P` that is not empty, and sends it into `P'`. -/
theorem exists_carries_of_charts {G H : Fin 4 → Fin 4 → Coords 4 → ℝ} {P P' : Set (Coords 4)}
    {q : M}
    (hc : ∃ φ : OpenPartialHomeomorph M (Coords 4),
      φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M ∧ q ∈ φ.source ∧
      ∀ q' ∈ φ.source, φ q' ∈ P ∧ ∀ v w : TangentSpace 𝓘(ℝ, Coords 4) q',
        g q' v w = flatMeasure (tableMeasure G) (φ q')
          (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q' v)
          (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q' w))
    (hc' : ∃ φ : OpenPartialHomeomorph M (Coords 4),
      φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M ∧ q ∈ φ.source ∧
      ∀ q' ∈ φ.source, φ q' ∈ P' ∧ ∀ v w : TangentSpace 𝓘(ℝ, Coords 4) q',
        g q' v w = flatMeasure (tableMeasure H) (φ q')
          (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q' v)
          (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q' w)) :
    ∃ (f : Coords 4 → Coords 4) (W : Set (Coords 4)), IsOpen W ∧ W.Nonempty ∧ W ⊆ P ∧
      (∀ x ∈ W, f x ∈ P') ∧ ∀ x ∈ W, CarriesTableAt G H f x := by
  obtain ⟨φ, hφ, hqφ, h⟩ := hc
  obtain ⟨φ', hφ', hqφ', h'⟩ := hc'
  refine ⟨φ' ∘ φ.symm, φ.target ∩ φ.symm ⁻¹' φ'.source, isOpen_chartChange_domain φ φ',
    ⟨φ q, φ.map_source hqφ, ?_⟩, fun z hz ↦ ?_, fun z hz ↦ (h' (φ.symm z) hz.2).1,
    fun z hz ↦ carriesTableAt_chartChange hφ hφ' (fun p hp ↦ (h p hp.1).2)
      (fun p hp ↦ (h' p hp.2).2) hz.1 hz.2⟩
  · rw [mem_preimage, φ.left_inv hqφ]
    exact hqφ'
  · have hz' := (h (φ.symm z) (φ.map_target hz.1)).1
    rwa [φ.right_inv hz.1] at hz'

variable [IsManifold 𝓘(ℝ, Coords 4) ∞ M]

/-- For a mass that is zero or negative, a chart that reads the length measure as
Schwarzschild's table lands outside the rim: there is no inside. -/
theorem IsSchwarzschildWith.chart_outside {m : ℝ} (hm : m ≤ 0) {q : M}
    (h : IsSchwarzschildWith m g q) :
    ∃ φ : OpenPartialHomeomorph M (Coords 4),
      φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M ∧ q ∈ φ.source ∧
      ∀ q' ∈ φ.source, φ q' ∈ outside m ∧ ∀ v w : TangentSpace 𝓘(ℝ, Coords 4) q',
        g q' v w = flatMeasure (tableMeasure (roundG (schwA m) (schwB m))) (φ q')
          (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q' v)
          (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q' w) := by
  obtain ⟨φ, hφ, hqφ, hall⟩ := h
  refine ⟨φ, hφ, hqφ, fun q' hq' ↦ ⟨(hall q' hq').1.resolve_right fun hin ↦ ?_, (hall q' hq').2⟩⟩
  obtain ⟨h1, h2, -⟩ := hin
  linarith

/-- **The mass is fixed by the space-time, given three facts about tables.** If no map of
coordinate space carries Kruskal's table of one positive mass to that of another (`hKK`), nor
Schwarzschild's table of one mass that is zero or negative to that of another (`hSS`), nor
Kruskal's table to Schwarzschild's of a mass that is zero or negative (`hKS`), then
`GlobalMassUnique` holds. -/
theorem globalMassUnique_of_tables
    (hKK : ∀ m m' : ℝ, 0 < m → 0 < m' → ∀ (f : Coords 4 → Coords 4) (W : Set (Coords 4)),
      IsOpen W → W.Nonempty → W ⊆ kruskalRegion → (∀ x ∈ W, f x ∈ kruskalRegion) →
      (∀ x ∈ W, CarriesTableAt (kruskalG m) (kruskalG m') f x) → m = m')
    (hSS : ∀ m m' : ℝ, m ≤ 0 → m' ≤ 0 → ∀ (f : Coords 4 → Coords 4) (W : Set (Coords 4)),
      IsOpen W → W.Nonempty → W ⊆ outside m → (∀ x ∈ W, f x ∈ outside m') →
      (∀ x ∈ W, CarriesTableAt (roundG (schwA m) (schwB m))
        (roundG (schwA m') (schwB m')) f x) → m = m')
    (hKS : ∀ m m' : ℝ, 0 < m → m' ≤ 0 → ∀ (f : Coords 4 → Coords 4) (W : Set (Coords 4)),
      IsOpen W → W.Nonempty → W ⊆ kruskalRegion → (∀ x ∈ W, f x ∈ outside m') →
      (∀ x ∈ W, CarriesTableAt (kruskalG m) (roundG (schwA m') (schwB m')) f x) → False) :
    GlobalMassUnique := by
  intro M _ _ _ g s hne hg
  obtain ⟨q, hq⟩ := hne
  refine ⟨fun m m' hm hm' D D' hD hD' ↦ ?_, fun m m' hm hm' D D' hD hD' ↦ ?_,
    fun m m' hm hm' D D' hD hD' ↦ ?_⟩
  · obtain ⟨f, W, hW, hWne, hsub, hland, hcar⟩ :=
      exists_carries_of_charts (hD.isKruskalNear hg hq) (hD'.isKruskalNear hg hq)
    exact hKK m m' hm hm' f W hW hWne hsub hland hcar
  · obtain ⟨f, W, hW, hWne, hsub, hland, hcar⟩ :=
      exists_carries_of_charts ((hD.isSchwarzschildWith hm hg hq).chart_outside hm)
        ((hD'.isSchwarzschildWith hm' hg hq).chart_outside hm')
    exact hSS m m' hm hm' f W hW hWne hsub hland hcar
  · obtain ⟨f, W, hW, hWne, hsub, hland, hcar⟩ :=
      exists_carries_of_charts (hD.isKruskalNear hg hq)
        ((hD'.isSchwarzschildWith hm' hg hq).chart_outside hm')
    exact hKS m m' hm hm' f W hW hWne hsub hland hcar

end GravityInLean.Curved
