/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.FreeFallChecks
public import GravityInLean.Global.ChartChange
public import GravityInLean.Join.CarryPointwise
public import GravityInLean.Join.CarrySmooth
public import GravityInLean.Join.FlatToTable
public import GravityInLean.Join.NewTable
public import GravityInLean.Join.Atlas
public import GravityInLean.SamePath

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# The equation of free fall does not depend on the chart

`FallsFreelyIn g φ γ τ` (`Goals/GlobalComplete.lean`) reads the equation of free fall in one
chart. Here: where `g` is a length measure and the curve is smooth, two charts of the curved
space that both see the point `γ τ` give the same answer (`fallsFreelyIn_iff_of_mem_maximalAtlas`).
So asking the equation in the chart that the curved space provides, as `IsFreeFallPath` does,
is no choice at all. The statement `FreeFallAnyChart` follows (`freeFallAnyChart`).

The proof puts together what the project already has: the change of charts carries the table of
one chart to the table of the other (`carriesTableAt_chartChange`), and free fall in coordinates
does not depend on the coordinates (`isFreeFallAt_inNewCoords`, `SamePath.lean`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set Filter Topology

open scoped Manifold ContDiff

/-! ## Two small facts: slopes and free fall only look near the point -/

section Local

variable {n : ℕ}

/-- The slope of a function at a point only depends on the function near the point. -/
theorem slope_congr_nhds {f f' : Coords n → ℝ} {x : Coords n} (h : f =ᶠ[𝓝 x] f') (i : Fin n) :
    slope i f x = slope i f' x := by
  unfold slope
  apply Filter.EventuallyEq.deriv_eq
  have hc : Continuous fun s : ℝ ↦ Function.update x i s :=
    continuous_const.update i continuous_id
  have ht : Tendsto (fun s : ℝ ↦ Function.update x i s) (𝓝 (x i)) (𝓝 x) := by
    have := hc.tendsto (x i)
    simpa using this
  exact ht.eventually h

/-- The connection at a point only looks at the table near the point. -/
theorem christoffel_congr_nhds {G G' ginv : Fin n → Fin n → Coords n → ℝ} {x : Coords n}
    (h : ∀ a b, G a b =ᶠ[𝓝 x] G' a b) (a b c : Fin n) :
    christoffel G ginv a b c x = christoffel G' ginv a b c x := by
  have hs : ∀ d e i, slope i (G d e) x = slope i (G' d e) x :=
    fun d e i ↦ slope_congr_nhds (h d e) i
  simp only [christoffel, hs]

/-- The equation of free fall at `τ` only looks at the path near `τ`. -/
theorem isFreeFallAt_congr_path {Γ : Fin n → Fin n → Fin n → Coords n → ℝ}
    {γ γ' : ℝ → Coords n} {τ : ℝ} (h : γ =ᶠ[𝓝 τ] γ') :
    IsFreeFallAt Γ γ τ ↔ IsFreeFallAt Γ γ' τ := by
  have hτ : γ τ = γ' τ := h.eq_of_nhds
  have h1 : ∀ a, (fun s ↦ γ s a) =ᶠ[𝓝 τ] fun s ↦ γ' s a := fun a ↦
    h.mono fun s hs ↦ by simp only [hs]
  have hd : ∀ a, deriv (fun s ↦ γ s a) τ = deriv (fun s ↦ γ' s a) τ := fun a ↦
    (h1 a).deriv_eq
  have hdd : ∀ a, deriv (deriv fun s ↦ γ s a) τ = deriv (deriv fun s ↦ γ' s a) τ := fun a ↦
    (h1 a).deriv.deriv_eq
  simp only [IsFreeFallAt, freeFallExpr, hτ, hd, hdd]

end Local

/-! ## The table of a chart -/

section Chart

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  [IsManifold 𝓘(ℝ, Coords 4) ∞ M] {g : LengthMeasure 𝓘(ℝ, Coords 4) M}

omit [IsManifold 𝓘(ℝ, Coords 4) ∞ M] in
/-- The table of a chart is the table of the length measure carried into the chart. -/
theorem chartTable_eq_tableOf (g : LengthMeasure 𝓘(ℝ, Coords 4) M)
    (φ : OpenPartialHomeomorph M (Coords 4)) :
    chartTable g φ = Join.tableOf (Join.carryMeasure φ g) := rfl

omit [IsManifold 𝓘(ℝ, Coords 4) ∞ M] in
/-- In its chart, `g` is the length measure of the chart's table. -/
theorem readsAs_chartTable {φ : OpenPartialHomeomorph M (Coords 4)}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M) {q : M} (hq : q ∈ φ.source)
    (v w : TangentSpace 𝓘(ℝ, Coords 4) q) :
    g q v w = flatMeasure (tableMeasure (chartTable g φ)) (φ q)
      (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q v)
      (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q w) := by
  rw [chartTable_eq_tableOf, Join.tableMeasure_tableOf]
  exact Join.carryMeasure_formula hφ g hq v w

/-- Where `g` is a length measure on a region that holds the domain of the chart, `g` read in the
chart is a length measure on the range of the chart. -/
theorem isLengthMeasureOn_carryMeasure {φ : OpenPartialHomeomorph M (Coords 4)}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M) {s : Set M} (hs : φ.source ⊆ s)
    (hg : IsLengthMeasureOn g s) :
    IsLengthMeasureOn (flatMeasure (Join.carryMeasure φ g)) φ.target where
  symm := fun x hx v w ↦ Join.carryMeasure_symm g (hg.symm _ (hs (φ.map_target hx))) v w
  nondegenerate := fun x hx v hv ↦ by
    have hq : φ.symm x ∈ s := hs (φ.map_target hx)
    have h0 : mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ.symm x v = 0 := by
      refine hg.nondegenerate _ hq _ fun w' ↦ ?_
      have e := hv (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ (φ.symm x) w')
      change Join.carryMeasure φ g x v _ = 0 at e
      rw [Join.carryMeasure_apply, Join.mfderiv_comp_symm' hφ hx] at e
      exact e
    have h1 := Join.mfderiv_symm_comp hφ hx v
    rw [h0, map_zero] at h1
    exact h1.symm
  smooth := Join.isSmoothOn_carryMeasure hφ hs hg.smooth

/-- The table of a chart, where `g` is a length measure, has an inverse matrix. -/
theorem chartTable_mul_inv {φ : OpenPartialHomeomorph M (Coords 4)}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M) {s : Set M} (hs : φ.source ⊆ s)
    (hg : IsLengthMeasureOn g s) {x : Coords 4} (hx : x ∈ φ.target) (a c : Fin 4) :
    ∑ b, chartTable g φ a b x * chartTableInv g φ b c x = if a = c then 1 else 0 := by
  have hdet := Join.det_tab_tableOf_ne_zero (isLengthMeasureOn_carryMeasure hφ hs hg) hx
  have hm := Matrix.mul_nonsing_inv (tab (chartTable g φ) x) (isUnit_iff_ne_zero.mpr hdet)
  have e := congrFun (congrFun hm a) c
  simp only [Matrix.mul_apply, Matrix.one_apply] at e
  exact e

/-- The table of a chart is smooth on the range of the chart. -/
theorem contDiffOn_chartTable {φ : OpenPartialHomeomorph M (Coords 4)}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M) {s : Set M} (hs : φ.source ⊆ s)
    (hg : IsLengthMeasureOn g s) (a b : Fin 4) :
    ContDiffOn ℝ ∞ (chartTable g φ a b) φ.target :=
  Join.contDiffOn_carryMeasure hφ hs hg.smooth _ _

end Chart

/-! ## Two charts give the same answer -/

section TwoCharts

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  [IsManifold 𝓘(ℝ, Coords 4) ∞ M] {g : LengthMeasure 𝓘(ℝ, Coords 4) M}

/-- **Two charts give the same answer,** when both charts lie inside a region where `g` is a
length measure. -/
theorem fallsFreelyIn_iff_of_subset {φ φ' : OpenPartialHomeomorph M (Coords 4)}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M)
    (hφ' : φ' ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M) {s : Set M}
    (hs : φ.source ⊆ s) (hs' : φ'.source ⊆ s) (hg : IsLengthMeasureOn g s)
    {γ : ℝ → M} {τ : ℝ} (hγ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Coords 4) ∞ γ τ)
    (hp : γ τ ∈ φ.source) (hp' : γ τ ∈ φ'.source) :
    FallsFreelyIn g φ γ τ ↔ FallsFreelyIn g φ' γ τ := by
  set G := chartTable g φ with hGdef
  set H := chartTable g φ' with hHdef
  set Φ : Coords 4 → Coords 4 := φ' ∘ φ.symm with hΦdef
  set c : ℝ → Coords 4 := fun s ↦ φ (γ s) with hcdef
  have hx0 : c τ ∈ φ.target := φ.map_source hp
  have hx0' : φ.symm (c τ) ∈ φ'.source := by
    simp only [hcdef, φ.left_inv hp]
    exact hp'
  have hΦc : Φ (c τ) = φ' (γ τ) := by
    simp only [hΦdef, hcdef, Function.comp, φ.left_inv hp]
  -- The change of charts carries one table to the other.
  have hcarry : CarriesTableAt G H Φ (c τ) :=
    carriesTableAt_chartChange hφ hφ' (fun q hq v w ↦ readsAs_chartTable hφ hq.1 v w)
      (fun q hq v w ↦ readsAs_chartTable hφ' hq.2 v w) hx0 hx0'
  -- So near `c τ` the table of `φ` is the table of `φ'` in new coordinates.
  have hW := isOpen_chartChange_domain φ φ'
  have hΦW := contDiffOn_chartChange hφ hφ'
  have hnear : ∀ a b, G a b =ᶠ[𝓝 (c τ)] inNewCoords Φ H a b := by
    intro a b
    filter_upwards [hcarry.2, hW.mem_nhds ⟨hx0, hx0'⟩] with y hy hyW
    have hd : DifferentiableAt ℝ Φ y :=
      (hΦW.contDiffAt (hW.mem_nhds hyW)).differentiableAt (by simp)
    have e1 := hy (Pi.single a 1) (Pi.single b 1)
    rw [← Join.tableMeasure_inNewCoords H hd] at e1
    rw [show G a b y = tableMeasure G y (Pi.single a 1) (Pi.single b 1) from
        (formOf_single_single (fun a b ↦ G a b y) a b).symm, ← e1]
    exact formOf_single_single (fun a b ↦ inNewCoords Φ H a b y) a b
  have hat : ∀ a b, G a b (c τ) = inNewCoords Φ H a b (c τ) := fun a b ↦ (hnear a b).eq_of_nhds
  -- The two hypotheses of smoothness.
  have hΦ2 : ∀ α, ContDiffAt ℝ 2 (fun z ↦ Φ z α) (c τ) := fun α ↦
    ((contDiffAt_pi.mp hcarry.1) α).of_le (by simp)
  have hcs : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Coords 4) ∞ c τ :=
    (contMDiffAt_of_mem_maximalAtlas hφ hp).comp τ hγ
  have hc2 : ∀ μ, ContDiffAt ℝ 2 (fun s ↦ c s μ) τ := fun μ ↦
    ((contDiffAt_pi.mp (contMDiffAt_iff_contDiffAt.mp hcs)) μ).of_le (by simp)
  -- The table of `φ'` at the point.
  have hy' : φ' (γ τ) ∈ φ'.target := φ'.map_source hp'
  have hHd : ∀ α β, DifferentiableAt ℝ (H α β) (Φ (c τ)) := fun α β ↦ by
    rw [hΦc]
    exact ((contDiffOn_chartTable hφ' hs' hg α β).contDiffAt
      (φ'.open_target.mem_nhds hy')).differentiableAt (by simp)
  have hHsymm : ∀ α β, H α β (Φ (c τ)) = H β α (Φ (c τ)) := fun α β ↦ by
    rw [hΦc]
    exact (isLengthMeasureOn_carryMeasure hφ' hs' hg).symm _ hy' _ _
  have hHinv : ∀ α δ, ∑ β, H α β (Φ (c τ)) * chartTableInv g φ' β δ (Φ (c τ))
      = if α = δ then 1 else 0 := fun α δ ↦ by
    rw [hΦc]
    exact chartTable_mul_inv hφ' hs' hg hy' α δ
  have hGinv : ∀ μ κ, ∑ ν, inNewCoords Φ H μ ν (c τ) * chartTableInv g φ ν κ (c τ)
      = if μ = κ then 1 else 0 := fun μ κ ↦ by
    simp only [← hat]
    exact chartTable_mul_inv hφ hs hg hx0 μ κ
  have key := isFreeFallAt_inNewCoords (Φ := Φ) (g := H) (ginv := chartTableInv g φ')
    (ginv' := chartTableInv g φ) (γ := c) (τ := τ) hΦ2 hc2 hHd hHsymm hHinv hGinv
  -- The left side is free fall read in `φ`.
  have hL : FallsFreelyIn g φ γ τ
      ↔ IsFreeFallAt (christoffel (inNewCoords Φ H) (chartTableInv g φ)) c τ :=
    isFreeFallAt_congr fun a b c' ↦ christoffel_congr_nhds hnear a b c'
  -- The right side is free fall read in `φ'`.
  have hev : (fun s ↦ Φ (c s)) =ᶠ[𝓝 τ] fun s ↦ φ' (γ s) := by
    have hcont : ContinuousAt γ τ := hγ.continuousAt
    filter_upwards [hcont.preimage_mem_nhds (φ.open_source.mem_nhds hp)] with s hs
    simp only [hΦdef, hcdef, Function.comp, φ.left_inv hs]
  have hR : IsFreeFallAt (christoffel H (chartTableInv g φ')) (fun s ↦ Φ (c s)) τ
      ↔ FallsFreelyIn g φ' γ τ :=
    isFreeFallAt_congr_path hev
  exact hL.trans (key.trans hR)

/-- **The equation of free fall does not depend on the chart.** Where `g` is a length measure
on an open region around `γ τ` and the curve is smooth at `τ`, any two charts of the curved
space's smooth structure that see `γ τ` give the same answer. -/
theorem fallsFreelyIn_iff_of_mem_maximalAtlas {φ φ' : OpenPartialHomeomorph M (Coords 4)}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M)
    (hφ' : φ' ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M) {s : Set M} (hso : IsOpen s)
    (hg : IsLengthMeasureOn g s) {γ : ℝ → M} {τ : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Coords 4) ∞ γ τ) (hps : γ τ ∈ s)
    (hp : γ τ ∈ φ.source) (hp' : γ τ ∈ φ'.source) :
    FallsFreelyIn g φ γ τ ↔ FallsFreelyIn g φ' γ τ := by
  have e1 : FallsFreelyIn g φ γ τ ↔ FallsFreelyIn g (φ.restrOpen s hso) γ τ := Iff.rfl
  have e2 : FallsFreelyIn g φ' γ τ ↔ FallsFreelyIn g (φ'.restrOpen s hso) γ τ := Iff.rfl
  rw [e1, e2]
  exact fallsFreelyIn_iff_of_subset (Join.chart_restrOpen_mem_maximalAtlas hφ hso)
    (Join.chart_restrOpen_mem_maximalAtlas hφ' hso) inter_subset_right inter_subset_right hg
    hγ ⟨hp, hps⟩ ⟨hp', hps⟩

end TwoCharts

/-- **The statement `FreeFallAnyChart` of `Goals/GlobalComplete.lean`, proved.** -/
theorem freeFallAnyChart : FreeFallAnyChart := by
  intro M _ _ _ g s γ τ φ hso hps hg hγ hφ hp
  exact fallsFreelyIn_iff_of_mem_maximalAtlas hφ (IsManifold.chart_mem_maximalAtlas (γ τ)) hso hg
    hγ hps hp (mem_chart_source _ _)

end GravityInLean.Curved
