/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.BothWays.Pull
public import GravityInLean.BothWays.PullConnection
public import GravityInLean.Join.ResultA

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# "Empty" comes back from a chart to the curved space

Board item `task:bothways-pull-empty`. A chart `c` of the curved space reads the length measure
`g` as the length measure of a good table of functions `g'` (`ReadsAs`, `Pull.lean`). If the
table is empty in the sense of coordinates (the formula for the curvature vanishes on the range
of the chart), then `g` is empty on the domain of the chart, in the sense of `Curved/Basic.lean`.

No curvature is computed here. The connection of the table is taken to the curved space
(`isConnectionOf_pull`, `PullConnection.lean`). Then the lemmas of `Join/` are used forward, as
in `Join/ResultA.lean`: the curvature of that connection at a point of the curved space is the
curvature, at the image of the point, of the same connection read in the chart again. Read in
the chart again it is a connection of the table's length measure, and the curvature of any such
connection is the coordinate formula (`IsRegularTableOn.ricciAt_of_isConnectionOf`).

* `carryMeasure_eq_on_target`: a length measure that reads as `G` in a chart, read in that chart,
  is `G` on the range of the chart.
* `isLengthMeasureOn_congr`, `isConnectionOf_congr`: "length measure on a region" and "connection
  of a length measure on a region" only look at the length measure on the region.
* `isEmptyOn_pull`: the result.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.BothWays

open GravityInLean.Curved GravityInLean.Join

open scoped Manifold ContDiff Topology

/-! ## Two notions only look at the length measure on the region -/

section Congr

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Two length measures that agree at every point of a region: if one is a length measure on the
region (symmetric, no step at right angles to all steps, smooth), so is the other. -/
theorem isLengthMeasureOn_congr {g₁ g₂ : LengthMeasure I M} {s : Set M}
    (h : IsLengthMeasureOn g₁ s) (he : ∀ x ∈ s, g₁ x = g₂ x) : IsLengthMeasureOn g₂ s where
  symm := fun x hx v w ↦ by
    rw [← he x hx]
    exact h.symm x hx v w
  nondegenerate := fun x hx ↦ by
    rw [← he x hx]
    exact h.nondegenerate x hx
  smooth := by
    have hs : IsSmoothOn g₁ s := h.smooth
    unfold IsSmoothOn at hs ⊢
    exact hs.congr fun y hy ↦ by rw [he y hy]

/-- Two length measures that agree at every point of an open region: a connection that belongs
to one of them on the region belongs to the other. -/
theorem isConnectionOf_congr {g₁ g₂ : LengthMeasure I M} {cov : Transport I M} {s : Set M}
    (h : IsConnectionOf g₁ cov s) (he : ∀ x ∈ s, g₁ x = g₂ x) : IsConnectionOf g₂ cov s where
  isOpen := h.isOpen
  isConnection := h.isConnection
  noTwist := h.noTwist
  keepsLengths := fun x hx Y Z hY hZ v ↦ by
    -- Near `x` the two functions to differentiate are the same.
    have hev : (fun y ↦ g₂ y (Y y) (Z y)) =ᶠ[𝓝 x] fun y ↦ g₁ y (Y y) (Z y) := by
      filter_upwards [h.isOpen.mem_nhds hx] with y hy
      rw [he y hy]
    have e : d% (fun y ↦ g₂ y (Y y) (Z y)) x = d% (fun y ↦ g₁ y (Y y) (Z y)) x :=
      hev.mfderiv_eq
    rw [e, ← he x hx]
    exact h.keepsLengths x hx Y Z hY hZ v

end Congr

/-! ## Reading in the chart what reads as `G` -/

section Read

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {c : OpenPartialHomeomorph M E} {g : LengthMeasure 𝓘(ℝ, E) M} {G : E → E →L[ℝ] E →L[ℝ] ℝ}

/-- A length measure of the curved space that reads as `G` in the chart `c`, read in the chart
(`carryMeasure`), is `G` at every point of the range of the chart. -/
theorem carryMeasure_eq_on_target (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hread : ReadsAs c g G) {x : E} (hx : x ∈ c.target) : carryMeasure c g x = G x := by
  have key : ∀ y : E, y = x → ∀ a b : E, flatMeasure G y a b = G x a b := by
    rintro y rfl a b
    rfl
  ext v w
  rw [carryMeasure_apply, hread _ (c.map_target hx)]
  refine (key _ (c.right_inv hx) _ _).trans ?_
  rw [chart_mfderiv_comp_symm hc hx, chart_mfderiv_comp_symm hc hx]

end Read

/-! ## The result -/

/-- **"Empty" comes back along a chart.** Let the chart `c` read the length measure `g` of the
curved space as the length measure of a good table of functions `g'` on the range of the chart.
If the coordinate formula for the curvature of the table vanishes on the range of the chart,
then `g` is empty on the domain of the chart: it has a connection there, and the curvature of
that connection vanishes. -/
theorem isEmptyOn_pull {M : Type*} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M] {c : OpenPartialHomeomorph M (Coords 4)}
    {g : LengthMeasure 𝓘(ℝ, Coords 4) M} {g' ginv' : Fin 4 → Fin 4 → Coords 4 → ℝ}
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M) (hread : ReadsAs c g (tableMeasure g'))
    (hreg : IsRegularTableOn g' ginv' c.target) (hflat : ∀ x ∈ c.target, IsRicciFlatAt g' ginv' x) :
    Curved.IsEmptyOn g c.source := by
  -- The connection of the table, taken to the curved space.
  have hcov : IsConnectionOf g
      (pullTransport c (flatTransport (tableCorr (christoffel g' ginv')))) c.source :=
    isConnectionOf_pull hc hread hreg.isConnectionOf
  set cov : Transport 𝓘(ℝ, Coords 4) M :=
    pullTransport c (flatTransport (tableCorr (christoffel g' ginv'))) with hcovdef
  -- On the range of the chart, `g` read in the chart is the measure of the table.
  have heq : ∀ x ∈ c.target,
      flatMeasure (tableMeasure g') x = flatMeasure (carryMeasure c g) x :=
    fun x hx ↦ (carryMeasure_eq_on_target hc hread hx).symm
  have hLM : IsLengthMeasureOn (flatMeasure (carryMeasure c g)) c.target :=
    isLengthMeasureOn_congr hreg.isLengthMeasureOn heq
  -- The connection, read in the chart again, belongs to `g` read in the chart.
  have h' : IsConnectionOf (flatMeasure (carryMeasure c g)) (carryTransport c cov) c.target :=
    { isOpen := c.open_target
      isConnection := isCovariantDerivativeOn_carry hc subset_rfl hcov.isConnection
      noTwist := fun _ hx X Y hX hY ↦
        carryTransport_noTwist hc subset_rfl hcov.noTwist hx X Y hX hY
      keepsLengths := fun _ hx Y Z hY hZ v ↦
        carryTransport_keepsLengths hc subset_rfl hcov.keepsLengths hx Y Z hY hZ v }
  -- So it belongs to the measure of the table.
  have h'G : IsConnectionOf (flatMeasure (tableMeasure g')) (carryTransport c cov) c.target :=
    isConnectionOf_congr h' fun x hx ↦ (heq x hx).symm
  obtain ⟨A, hA₀, hAd⟩ := exists_flatTransport_of_isLengthMeasureOn c.open_target hLM
  refine ⟨cov, hcov, fun q hq v w ↦ ?_⟩
  -- The curvature at `q` is the curvature in the chart at `c q`, and that is the formula.
  rw [ricciAt_carry hc hq
    (fun u v w ↦ curvatureAt_carry hc subset_rfl hcov hLM hA₀ h' hAd hq u v w)
    (fun v' w' ↦ curvatureAt_linear_of_isConnectionOf hLM hA₀ h' (c.map_source hq)
      (hAd _ (c.map_source hq)) v' w') v w,
    hreg.ricciAt_of_isConnectionOf h'G (c.map_source hq), formOf_apply]
  exact Finset.sum_eq_zero fun b _ ↦ Finset.sum_eq_zero fun d _ ↦ by
    rw [hflat _ (c.map_source hq) d b, zero_mul, zero_mul]

end GravityInLean.BothWays
