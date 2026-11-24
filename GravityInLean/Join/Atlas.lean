/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Curved.Goal
public import GravityInLean.NewCoordinates
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.LinearAlgebra.Determinant

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# The chart of the goal

Board item `task:join-atlas`. Part C of the route: how a chart of the curved space and a change
of coordinates on coordinate space give the chart that the goal asks for.

* `trans_mem_maximalAtlas`: a chart of the curved space, followed by a change of coordinates
  that is smooth with a smooth inverse, is again a chart of the curved space.
* `mfderiv_trans_apply`: the slope of the combined chart is the slope of the change of
  coordinates after the slope of the chart (chain rule).
* `chart_restr_mem_maximalAtlas`, `chart_restrOpen_mem_maximalAtlas`, `chart_restrOpen_source`,
  `chart_restrOpen_apply`, `mfderiv_restrOpen`: a chart cut down to an open set is again a
  chart, with the same slope.
* `exists_localDiffeo`, `exists_localDiffeo_of_det`: a smooth map of coordinate space whose
  slope at a point can be undone is, near that point, a change of coordinates that is smooth
  with a smooth inverse (inverse function theorem).
* `exists_chart_of_localDiffeo`: all of it together, in the form the goal needs.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Join

open Set

open scoped Manifold ContDiff Topology

section Charts

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  [IsManifold 𝓘(ℝ, Coords 4) ∞ M]

/-- A chart of the curved space, followed by a change of coordinates `Ψ` that is smooth with a
smooth inverse, is again a chart of the curved space. -/
theorem trans_mem_maximalAtlas {c : OpenPartialHomeomorph M (Coords 4)}
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M)
    {Ψ : OpenPartialHomeomorph (Coords 4) (Coords 4)}
    (hΨ : ContDiffOn ℝ ∞ Ψ Ψ.source) (hΨ' : ContDiffOn ℝ ∞ Ψ.symm Ψ.target) :
    c.trans Ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M := by
  have hc1 := contMDiffOn_of_mem_maximalAtlas hc
  have hc2 := contMDiffOn_symm_of_mem_maximalAtlas hc
  refine (c.trans Ψ).mem_maximalAtlas_of_contMDiffOn ?_ ?_
  · rw [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source]
    exact (contMDiffOn_iff_contDiffOn.2 hΨ).comp (hc1.mono inter_subset_left)
      inter_subset_right
  · rw [OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.trans_target]
    exact hc2.comp ((contMDiffOn_iff_contDiffOn.2 hΨ').mono inter_subset_left)
      inter_subset_right

omit [IsManifold 𝓘(ℝ, Coords 4) ∞ M] in
/-- Chain rule for the combined chart: its slope at `q` is the slope of the change of
coordinates `Ψ` at `c q`, applied after the slope of the chart `c` at `q`. -/
theorem mfderiv_trans_apply {c : OpenPartialHomeomorph M (Coords 4)}
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M)
    {Ψ : OpenPartialHomeomorph (Coords 4) (Coords 4)}
    (hΨ : ContDiffOn ℝ ∞ Ψ Ψ.source) {q : M} (hq : q ∈ (c.trans Ψ).source)
    (v : TangentSpace 𝓘(ℝ, Coords 4) q) :
    mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) (c.trans Ψ) q v
      = fderiv ℝ Ψ (c q) (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) c q v) := by
  rw [OpenPartialHomeomorph.trans_source] at hq
  have hc' : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) c q :=
    (contMDiffAt_of_mem_maximalAtlas hc hq.1).mdifferentiableAt (by simp)
  have hΨd : DifferentiableAt ℝ Ψ (c q) :=
    (hΨ.contDiffAt (Ψ.open_source.mem_nhds hq.2)).differentiableAt (by simp)
  have hΨ' : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) Ψ (c q) :=
    hΨd.mdifferentiableAt
  have e : mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) (c.trans Ψ) q
      = (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) Ψ (c q)).comp
        (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) c q) :=
    mfderiv_comp (I := 𝓘(ℝ, Coords 4)) (I' := 𝓘(ℝ, Coords 4)) (I'' := 𝓘(ℝ, Coords 4))
      (g := Ψ) (f := c) q hΨ' hc'
  rw [e, mfderiv_eq_fderiv]
  rfl

end Charts

section Restriction

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]

/-- A chart of the curved space, cut down to an open set, is again a chart. (Form with
`restr`.) -/
theorem chart_restr_mem_maximalAtlas {c : OpenPartialHomeomorph M (Coords 4)}
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M) {U : Set M} (hU : IsOpen U) :
    c.restr U ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M :=
  _root_.restr_mem_maximalAtlas (contDiffGroupoid ∞ 𝓘(ℝ, Coords 4)) hc hU

/-- A chart of the curved space, cut down to an open set, is again a chart. (Form with
`restrOpen`, whose domain is `c.source ∩ U` by definition.) -/
theorem chart_restrOpen_mem_maximalAtlas {c : OpenPartialHomeomorph M (Coords 4)}
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M) {U : Set M} (hU : IsOpen U) :
    c.restrOpen U hU ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M := by
  have key : ∀ (V : Set M) (hV : IsOpen V), V = U → c.restrOpen V hV = c.restrOpen U hU := by
    rintro V hV rfl
    rfl
  have h := chart_restr_mem_maximalAtlas hc hU
  rwa [OpenPartialHomeomorph.restr, key _ isOpen_interior hU.interior_eq] at h

omit [ChartedSpace (Coords 4) M] in
/-- The domain of the cut-down chart: the points of the chart's domain that lie in `U`. -/
theorem chart_restrOpen_source (c : OpenPartialHomeomorph M (Coords 4)) {U : Set M}
    (hU : IsOpen U) : (c.restrOpen U hU).source = c.source ∩ U := rfl

omit [ChartedSpace (Coords 4) M] in
/-- The cut-down chart is the same map as the chart. -/
theorem chart_restrOpen_apply (c : OpenPartialHomeomorph M (Coords 4)) {U : Set M} (hU : IsOpen U)
    (q : M) : c.restrOpen U hU q = c q := rfl

/-- The cut-down chart has the same slope as the chart, at every point. -/
theorem mfderiv_restrOpen (c : OpenPartialHomeomorph M (Coords 4)) {U : Set M} (hU : IsOpen U)
    (q : M) :
    mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) (c.restrOpen U hU) q
      = mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) c q := rfl

end Restriction

section InverseFunction

/-- **Inverse function theorem, as a change of coordinates.** A map `Φ` of coordinate space that
is smooth on an open set `W`, and whose slope at a point `y₀` of `W` can be undone, is near `y₀`
a change of coordinates: one-to-one on an open set around `y₀` inside `W`, smooth there, with a
smooth inverse. -/
theorem exists_localDiffeo {Φ : Coords 4 → Coords 4} {W : Set (Coords 4)} (hW : IsOpen W)
    (hΦ : ContDiffOn ℝ ∞ Φ W) {y₀ : Coords 4} (hy₀ : y₀ ∈ W)
    (hunit : IsUnit (fderiv ℝ Φ y₀)) :
    ∃ e : OpenPartialHomeomorph (Coords 4) (Coords 4), y₀ ∈ e.source ∧ e.source ⊆ W ∧
      (∀ y, e y = Φ y) ∧ ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  -- at every point of `W` with a slope that can be undone, `Φ` has that slope as an equivalence
  have hequiv : ∀ y ∈ W, IsUnit (fderiv ℝ Φ y) →
      ∃ f' : Coords 4 ≃L[ℝ] Coords 4, HasFDerivAt Φ (f' : Coords 4 →L[ℝ] Coords 4) y := by
    rintro y hy ⟨u, hu⟩
    refine ⟨ContinuousLinearEquiv.ofUnit u, ?_⟩
    have e : (ContinuousLinearEquiv.ofUnit u : Coords 4 →L[ℝ] Coords 4) = fderiv ℝ Φ y := by
      rw [← hu]
      rfl
    rw [e]
    exact ((hΦ.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
  have hcd : ContDiffAt ℝ ∞ Φ y₀ := hΦ.contDiffAt (hW.mem_nhds hy₀)
  obtain ⟨f', hf'⟩ := hequiv y₀ hy₀ hunit
  -- the set of points of `W` where the slope can be undone is open
  have hV : IsOpen (W ∩ fderiv ℝ Φ ⁻¹' {A : Coords 4 →L[ℝ] Coords 4 | IsUnit A}) :=
    (hΦ.continuousOn_fderiv_of_isOpen hW (by simp)).isOpen_inter_preimage hW Units.isOpen
  refine ⟨(hcd.toOpenPartialHomeomorph Φ hf' (by simp)).restrOpen _ hV,
    ⟨hcd.mem_toOpenPartialHomeomorph_source hf' (by simp), hy₀, hunit⟩,
    fun y hy ↦ hy.2.1, fun y ↦ rfl, hΦ.mono fun y hy ↦ hy.2.1, fun z hz ↦ ?_⟩
  set e := (hcd.toOpenPartialHomeomorph Φ hf' (by simp)).restrOpen _ hV with he
  have hs : e.symm z ∈ e.source := e.map_target hz
  obtain ⟨f'', hf''⟩ := hequiv (e.symm z) hs.2.1 hs.2.2
  exact (e.contDiffAt_symm hz (f₀' := f'') hf''
    (hΦ.contDiffAt (hW.mem_nhds hs.2.1))).contDiffWithinAt

/-- If the table of slopes of `Φ` at `y` has a determinant that is not zero, then the slope of
`Φ` at `y` can be undone. -/
theorem isUnit_fderiv_of_det {Φ : Coords 4 → Coords 4} {y : Coords 4}
    (hd : DifferentiableAt ℝ Φ y) (hdet : (tab (jac Φ) y).det ≠ 0) :
    IsUnit (fderiv ℝ Φ y) := by
  have e : tab (jac Φ) y
      = LinearMap.toMatrix' (fderiv ℝ Φ y : Coords 4 →ₗ[ℝ] Coords 4) := by
    ext a b
    rw [LinearMap.toMatrix'_apply]
    exact jac_eq_fderiv hd a b
  rw [e, LinearMap.det_toMatrix'] at hdet
  exact ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.2
    ((LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))

/-- **Inverse function theorem, as a change of coordinates,** in the language of tables: the
table of slopes of `Φ` at `y₀` has a determinant that is not zero. -/
theorem exists_localDiffeo_of_det {Φ : Coords 4 → Coords 4} {W : Set (Coords 4)}
    (hW : IsOpen W) (hΦ : ContDiffOn ℝ ∞ Φ W) {y₀ : Coords 4} (hy₀ : y₀ ∈ W)
    (hdet : (tab (jac Φ) y₀).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph (Coords 4) (Coords 4), y₀ ∈ e.source ∧ e.source ⊆ W ∧
      (∀ y, e y = Φ y) ∧ ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target :=
  exists_localDiffeo hW hΦ hy₀
    (isUnit_fderiv_of_det ((hΦ.contDiffAt (hW.mem_nhds hy₀)).differentiableAt (by simp)) hdet)

end InverseFunction

section Together

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  [IsManifold 𝓘(ℝ, Coords 4) ∞ M]

/-- **The chart of the goal.** Take a chart `c` of the curved space with `p` in its domain, an
open set `U` of the curved space around `p`, and a map `Φ` of coordinate space that is smooth on
an open set `W` around `c p` with a slope at `c p` that can be undone. Then there is a chart `φ`
of the curved space around `p`, with domain inside the domain of `c`, inside `U` and inside the
points that `c` sends to `W`, which is `Φ` after `c`, and whose slope is the slope of `Φ` after
the slope of `c`. -/
theorem exists_chart_of_localDiffeo {c : OpenPartialHomeomorph M (Coords 4)}
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M) {p : M} (hp : p ∈ c.source)
    {U : Set M} (hU : IsOpen U) (hpU : p ∈ U)
    {Φ : Coords 4 → Coords 4} {W : Set (Coords 4)} (hW : IsOpen W) (hΦ : ContDiffOn ℝ ∞ Φ W)
    (hpW : c p ∈ W) (hunit : IsUnit (fderiv ℝ Φ (c p))) :
    ∃ φ : OpenPartialHomeomorph M (Coords 4),
      φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M ∧ p ∈ φ.source ∧
      φ.source ⊆ c.source ∩ U ∩ c ⁻¹' W ∧ (∀ q, φ q = Φ (c q)) ∧
      ∀ q ∈ φ.source, ∀ v : TangentSpace 𝓘(ℝ, Coords 4) q,
        mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q v
          = fderiv ℝ Φ (c q) (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) c q v) := by
  obtain ⟨e, hpe, heW, heΦ, he1, he2⟩ := exists_localDiffeo hW hΦ hpW hunit
  have hcU := chart_restrOpen_mem_maximalAtlas hc hU
  have hfun : (e : Coords 4 → Coords 4) = Φ := funext heΦ
  refine ⟨(c.restrOpen U hU).trans e, trans_mem_maximalAtlas hcU he1 he2, ⟨⟨hp, hpU⟩, hpe⟩,
    fun q hq ↦ ⟨hq.1, heW hq.2⟩, fun q ↦ heΦ (c q), fun q hq v ↦ ?_⟩
  rw [mfderiv_trans_apply hcU he1 hq v, hfun]
  rfl

end Together

end GravityInLean.Join
