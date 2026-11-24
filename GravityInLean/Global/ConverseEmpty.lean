/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.KruskalChart
public import GravityInLean.Global.SchwChart
public import GravityInLean.BothWays.NoCoordinates
public import GravityInLean.Connection.Exists
public import GravityInLean.Rim.Empty

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# A space-time with a length-keeping map into a model is empty

Board item `task:global-converse-empty`. The "empty" half of `GlobalBirkhoffConverse`
(`Goals/Global.lean`): a space-time on a region that has a length-keeping map into Kruskal's
whole space-time (positive mass), or into Schwarzschild's whole space-time (mass zero or
negative), is empty on that region.

"Empty on the region" asks for **one** connection of the length measure on the whole region,
with curvature zero at every point. A map gives, around every point, a chart in which the length
measure is the model's table (`IsKruskalMapOn.exists_chart`,
`IsSchwarzschildMapOn.isSchwarzschildWith`), and the table is empty by the coordinate formula.
The two are joined like this:

* the length measure has a connection on the whole region (`connectionExists`);
* the curvature of **any** connection of the length measure, at a point of a chart in which the
  length measure reads as a good table, is the coordinate formula of that table
  (`ricciAt_eq_zero_of_readsAs`; the same computation as `BothWays.isEmptyOn_pull`, for a
  connection that is given instead of one that is made from the chart);
* so a length measure that reads as an empty good table in a chart around every point of an
  open region is empty on the region (`isEmptyOn_of_charts`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open GravityInLean.Join GravityInLean.BothWays

open Real Set

open scoped Manifold ContDiff Topology

section ConverseEmpty

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  [IsManifold 𝓘(ℝ, Coords 4) ∞ M] {m : ℝ} {g : LengthMeasure 𝓘(ℝ, Coords 4) M} {s : Set M}

/-- **The curvature of any connection of the length measure vanishes where a chart reads the
length measure as an empty table.** Let `cov` be a connection of `g` on a region that contains
the domain of the chart `c`, and let `c` read `g` as the length measure of a good table whose
coordinate formula for the curvature vanishes on the range of the chart. Then the curvature of
`cov` vanishes at every point of the chart's domain. -/
theorem ricciAt_eq_zero_of_readsAs {c : OpenPartialHomeomorph M (Coords 4)}
    {g' ginv' : Fin 4 → Fin 4 → Coords 4 → ℝ} {cov : Transport 𝓘(ℝ, Coords 4) M}
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M) (hs : c.source ⊆ s)
    (hcov : IsConnectionOf g cov s) (hread : ReadsAs c g (tableMeasure g'))
    (hreg : IsRegularTableOn g' ginv' c.target) (hflat : ∀ x ∈ c.target, IsRicciFlatAt g' ginv' x)
    {q : M} (hq : q ∈ c.source) (v w : TangentSpace 𝓘(ℝ, Coords 4) q) :
    ricciAt cov q v w = 0 := by
  -- On the range of the chart, `g` read in the chart is the measure of the table.
  have heq : ∀ x ∈ c.target,
      flatMeasure (tableMeasure g') x = flatMeasure (carryMeasure c g) x :=
    fun x hx ↦ (carryMeasure_eq_on_target hc hread hx).symm
  have hLM : IsLengthMeasureOn (flatMeasure (carryMeasure c g)) c.target :=
    isLengthMeasureOn_congr hreg.isLengthMeasureOn heq
  -- The connection, read in the chart, belongs to `g` read in the chart.
  have h' : IsConnectionOf (flatMeasure (carryMeasure c g)) (carryTransport c cov) c.target :=
    { isOpen := c.open_target
      isConnection := isCovariantDerivativeOn_carry hc hs hcov.isConnection
      noTwist := fun _ hx X Y hX hY ↦
        carryTransport_noTwist hc hs hcov.noTwist hx X Y hX hY
      keepsLengths := fun _ hx Y Z hY hZ v ↦
        carryTransport_keepsLengths hc hs hcov.keepsLengths hx Y Z hY hZ v }
  -- So it belongs to the measure of the table.
  have h'G : IsConnectionOf (flatMeasure (tableMeasure g')) (carryTransport c cov) c.target :=
    isConnectionOf_congr h' fun x hx ↦ (heq x hx).symm
  obtain ⟨A, hA₀, hAd⟩ := exists_flatTransport_of_isLengthMeasureOn c.open_target hLM
  -- The curvature at `q` is the curvature in the chart at `c q`, and that is the formula.
  rw [ricciAt_carry hc hq
    (fun u v w ↦ curvatureAt_carry hc hs hcov hLM hA₀ h' hAd hq u v w)
    (fun v' w' ↦ curvatureAt_linear_of_isConnectionOf hLM hA₀ h' (c.map_source hq)
      (hAd _ (c.map_source hq)) v' w') v w,
    hreg.ricciAt_of_isConnectionOf h'G (c.map_source hq), formOf_apply]
  exact Finset.sum_eq_zero fun b _ ↦ Finset.sum_eq_zero fun d _ ↦ by
    rw [hflat _ (c.map_source hq) d b, zero_mul, zero_mul]

/-- **Empty chart by chart is empty.** A space-time on an open region that, around every point
of the region, reads in some chart inside the region as a good table whose coordinate formula
for the curvature vanishes, is empty on the region: one connection for the whole region, with
curvature zero everywhere. -/
theorem isEmptyOn_of_charts (hs : IsOpen s) (hg : IsSpaceTimeOn g s)
    (h : ∀ q ∈ s, ∃ (c : OpenPartialHomeomorph M (Coords 4))
      (g' ginv' : Fin 4 → Fin 4 → Coords 4 → ℝ),
      c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M ∧ q ∈ c.source ∧ c.source ⊆ s ∧
      ReadsAs c g (tableMeasure g') ∧ IsRegularTableOn g' ginv' c.target ∧
      ∀ x ∈ c.target, IsRicciFlatAt g' ginv' x) :
    IsEmptyOn g s := by
  obtain ⟨cov, hcov⟩ := connectionExists _ _ _ _ g s hs hg.isLengthMeasureOn
  refine ⟨cov, hcov, fun q hq v w ↦ ?_⟩
  obtain ⟨c, g', ginv', hc, hqc, hsub, hread, hreg, hflat⟩ := h q hq
  exact ricciAt_eq_zero_of_readsAs hc hsub hcov hread hreg hflat hqc v w

/-- **A space-time with a length-keeping map into Kruskal's whole space-time is empty** on the
region of the map, for a positive mass. -/
theorem IsKruskalMapOn.isEmptyOn {D : M → Coords 5} (hm : 0 < m) (hD : IsKruskalMapOn m g D s)
    (hg : IsSpaceTimeOn g s) : IsEmptyOn g s := by
  refine isEmptyOn_of_charts hD.1 hg fun q hq ↦ ?_
  obtain ⟨R, φ, -, hφ, hqφ, hsub, h⟩ := hD.exists_chart hg hq
  -- the chart lands in the region of Kruskal's table
  have htar : φ.target ⊆ kruskalRegion := fun x hx ↦ by
    have h1 : φ (φ.symm x) ∈ kruskalRegion := (h (φ.symm x) (φ.map_target hx)).1
    rwa [φ.right_inv hx] at h1
  have hread : ReadsAs φ g (tableMeasure (kruskalG m)) := fun q' hq' v w ↦ (h q' hq').2.2 v w
  exact ⟨φ, kruskalG m, genGinv (kruskalA m) (kruskalA m) zero2 (kruskalS m), hφ, hqφ, hsub,
    hread, isRegularTableOn_mono (kruskal_regular hm) φ.open_target htar,
    fun x hx ↦ (gen_ricciFlat_iff (kruskal_regularG hm (htar hx))).mpr
      (kruskal_isEmptyG hm (htar hx).1)⟩

/-- **A space-time with a length-keeping map into Schwarzschild's whole space-time is empty** on
the region of the map, for a mass that is zero or negative (flat space-time for mass zero, the
centre included). -/
theorem IsSchwarzschildMapOn.isEmptyOn {D : M → Coords 4} (hm : m ≤ 0)
    (hD : IsSchwarzschildMapOn m g D s) (hg : IsSpaceTimeOn g s) : IsEmptyOn g s := by
  refine isEmptyOn_of_charts hD.1 hg fun q hq ↦ ?_
  obtain ⟨φ, hφ, hqφ, h⟩ := hD.isSchwarzschildWith hm hg hq
  -- cut the chart down to the region
  have hsrc : ∀ q' ∈ (φ.restrOpen s hD.1).source, q' ∈ φ.source ∧ q' ∈ s := fun _ hq' ↦ hq'
  have hoff : ∀ q' ∈ (φ.restrOpen s hD.1).source,
      (φ.restrOpen s hD.1) q' ∈ outside m ∨ (φ.restrOpen s hD.1) q' ∈ inside m :=
    fun q' hq' ↦ (h q' (hsrc q' hq').1).1
  have htar : (φ.restrOpen s hD.1).target ⊆ offRim m := target_subset_offRim hoff
  have hread : ReadsAs (φ.restrOpen s hD.1) g (tableMeasure (roundG (schwA m) (schwB m))) :=
    fun q' hq' v w ↦ (h q' (hsrc q' hq').1).2 v w
  exact ⟨φ.restrOpen s hD.1, roundG (schwA m) (schwB m), roundGinv (schwA m) (schwB m),
    chart_restrOpen_mem_maximalAtlas hφ hD.1, ⟨hqφ, hq⟩, fun q' hq' ↦ (hsrc q' hq').2, hread,
    isRegularTableOn_mono (schwarzschild_regularTable_offRim m)
      (φ.restrOpen s hD.1).open_target htar,
    fun x hx ↦ schwarzschild_ricciFlat_on_offRim m x (htar hx)⟩

end ConverseEmpty

end GravityInLean.Curved
