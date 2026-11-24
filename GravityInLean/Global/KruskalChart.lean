/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.KruskalSection
public import GravityInLean.Join.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# A length-keeping map into Kruskal's gives charts in which the length measure is Kruskal's table

Around every point of its region a length-keeping map `D` into Kruskal's whole space-time is,
up to a turn or mirror of the sphere, the wrapping map after a chart of the curved space; in
that chart the length measure is Kruskal's table.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

section KruskalChart

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  [IsManifold 𝓘(ℝ, Coords 4) ∞ M] {m : ℝ} {g : LengthMeasure 𝓘(ℝ, Coords 4) M} {s : Set M}

omit [IsManifold 𝓘(ℝ, Coords 4) ∞ M] in
/-- **Chain rule for a map that is, near a point, a map of coordinate space after a map into
coordinate space.** If near `q` the map `D` is `F` after `f`, then `D` carries a step at `q` to
where the slope of `F` carries the step that `f` makes of it. -/
theorem mfderiv_of_eventuallyEq_comp {D : M → Coords 5} {F : Coords 4 → Coords 5}
    {f : M → Coords 4} {q : M} (hF : DifferentiableAt ℝ F (f q))
    (hf : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) f q) (hev : D =ᶠ[𝓝 q] F ∘ f)
    (v : TangentSpace 𝓘(ℝ, Coords 4) q) :
    mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 5) D q v
      = fderiv ℝ F (f q) (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) f q v) := by
  have hF' : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 5) F (f q) := hF.mdifferentiableAt
  have h1 : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 5) (F ∘ f) q := hF'.comp q hf
  have h2 : mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 5) D q
      = mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 5) (F ∘ f) q :=
    (h1.hasMFDerivAt.congr_of_eventuallyEq_abuse hev).mfderiv
  have h3 : mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 5) D q v
      = mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 5) (F ∘ f) q v :=
    congrArg (fun A : Coords 4 →L[ℝ] Coords 5 ↦ A v) h2
  rw [h3, mfderiv_comp_apply q hF' hf v, mfderiv_eq_fderiv]
  rfl

/-- Wrapping round the sphere and then turning the sphere is smooth. -/
theorem contDiff_kruskalSym_wrap (L : Matrix (Fin 2) (Fin 2) ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) :
    ContDiff ℝ ∞ (kruskalSym L R ∘ kruskalWrap) :=
  (contDiff_kruskalSym L R).comp contDiff_kruskalWrap

/-- The slope of "wrap round the sphere, then apply the symmetry": the symmetry applied to the
wrapped step. -/
theorem fderiv_kruskalSym_wrap (L : Matrix (Fin 2) (Fin 2) ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (x u : Coords 4) :
    fderiv ℝ (kruskalSym L R ∘ kruskalWrap) x u = kruskalSym L R (fderiv ℝ kruskalWrap x u) := by
  have h1 : DifferentiableAt ℝ (kruskalSym L R) (kruskalWrap x) :=
    ((contDiff_kruskalSym L R).differentiable (by simp)).differentiableAt
  have h2 : DifferentiableAt ℝ kruskalWrap x :=
    (contDiff_kruskalWrap.differentiable (by simp)).differentiableAt
  rw [fderiv_comp x h1 h2, ContinuousLinearMap.comp_apply, fderiv_kruskalSym]

/-- **A length-keeping map into Kruskal's is, near each point, wrapping after a chart.** Around
`q` there are a chart `φ` of the curved space with domain inside the region, landing in the
region of Kruskal's table, and a turn or mirror `R` of the sphere, such that `D` is `φ`, then
wrapping, then `R`; and in the chart `φ` the length measure is Kruskal's table. -/
theorem IsKruskalMapOn.exists_chart {D : M → Coords 5} (hD : IsKruskalMapOn m g D s)
    (hg : IsSpaceTimeOn g s) {q : M} (hq : q ∈ s) :
    ∃ (R : Matrix (Fin 3) (Fin 3) ℝ) (φ : OpenPartialHomeomorph M (Coords 4)),
      R.transpose * R = 1 ∧ φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M ∧ q ∈ φ.source ∧
      φ.source ⊆ s ∧
      ∀ q' ∈ φ.source, φ q' ∈ kruskalRegion ∧ D q' = kruskalSym 1 R (kruskalWrap (φ q')) ∧
        ∀ v w : TangentSpace 𝓘(ℝ, Coords 4) q',
          g q' v w = flatMeasure (tableMeasure (kruskalG m)) (φ q')
            (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q' v)
            (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q' w) := by
  have hinjD := hD.mfderiv_injective hg hq
  obtain ⟨hs, hsm, hpt⟩ := hD
  -- undo the wrapping near `D q`
  obtain ⟨R, U, ψ, hR, hU, hpU, hψ, hsec⟩ := exists_kruskalWrap_section (hpt q hq).1
  have hL : (1 : Matrix (Fin 2) (Fin 2) ℝ).transpose * lightSign2 * 1 = lightSign2 := by simp
  have hFd : ∀ x : Coords 4, DifferentiableAt ℝ (kruskalSym 1 R ∘ kruskalWrap) x := fun x ↦
    ((contDiff_kruskalSym_wrap 1 R).differentiable (by simp)).differentiableAt
  -- a chart of the curved space to start from
  obtain ⟨c, hcdef⟩ : ∃ c : OpenPartialHomeomorph M (Coords 4), c = chartAt (Coords 4) q :=
    ⟨_, rfl⟩
  have hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M := by
    rw [hcdef]
    exact IsManifold.chart_mem_maximalAtlas q
  have hqc : q ∈ c.source := by
    rw [hcdef]
    exact mem_chart_source _ q
  have hcsurj : Function.Surjective (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) c q) := by
    rw [hcdef]
    exact (mdifferentiable_chart (I := 𝓘(ℝ, Coords 4)) q).mfderiv_surjective
      (mem_chart_source _ q)
  have hcd : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) c q :=
    (contMDiffAt_of_mem_maximalAtlas hc hqc).mdifferentiableAt (by simp)
  -- the points of the region that `D` sends into `U`, and the same set read in the chart
  have hV : IsOpen (s ∩ D ⁻¹' U) := hsm.continuousOn.isOpen_inter_preimage hs hU
  have hqV : q ∈ s ∩ D ⁻¹' U := ⟨hq, hpU⟩
  have hW : IsOpen (c.target ∩ c.symm ⁻¹' (s ∩ D ⁻¹' U)) := c.isOpen_inter_preimage_symm hV
  have hcqW : c q ∈ c.target ∩ c.symm ⁻¹' (s ∩ D ⁻¹' U) := by
    refine ⟨c.map_source hqc, ?_⟩
    change c.symm (c q) ∈ s ∩ D ⁻¹' U
    rw [c.left_inv hqc]
    exact hqV
  -- the map `Φ`: back to the curved space, then `D`, then undo the wrapping
  have hΦ : ContDiffOn ℝ ∞ (ψ ∘ D ∘ c.symm) (c.target ∩ c.symm ⁻¹' (s ∩ D ⁻¹' U)) := by
    have h1 : ContMDiffOn 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 5) ∞ (D ∘ c.symm)
        (c.target ∩ c.symm ⁻¹' (s ∩ D ⁻¹' U)) :=
      hsm.comp ((contMDiffOn_symm_of_mem_maximalAtlas hc).mono inter_subset_left)
        fun y hy ↦ hy.2.1
    exact hψ.comp (contMDiffOn_iff_contDiffOn.1 h1) fun y hy ↦ hy.2.2
  -- on the chart's domain, `Φ` after the chart undoes the wrapping of `D`
  have hΦc : ∀ q' ∈ c.source, (ψ ∘ D ∘ c.symm) (c q') = ψ (D q') := fun q' hq' ↦ by
    change ψ (D (c.symm (c q'))) = ψ (D q')
    rw [c.left_inv hq']
  have hback : ∀ q' ∈ c.source ∩ (s ∩ D ⁻¹' U),
      D q' = kruskalSym 1 R (kruskalWrap ((ψ ∘ D ∘ c.symm) (c q'))) := fun q' hq' ↦ by
    rw [hΦc q' hq'.1]
    exact ((hsec (D q') hq'.2.2 (hpt q' hq'.2.1).1).2).symm
  -- the slope of `Φ` at `c q` carries no step to zero, because `D` carries none to zero
  have hΦd : DifferentiableAt ℝ (ψ ∘ D ∘ c.symm) (c q) :=
    (hΦ.contDiffAt (hW.mem_nhds hcqW)).differentiableAt (by simp)
  have hinj : Function.Injective (fderiv ℝ (ψ ∘ D ∘ c.symm) (c q)) := by
    refine (injective_iff_map_eq_zero _).mpr fun u hu ↦ ?_
    obtain ⟨v, hv⟩ := hcsurj u
    have hev : D =ᶠ[𝓝 q] ((kruskalSym 1 R ∘ kruskalWrap) ∘ (ψ ∘ D ∘ c.symm)) ∘ c :=
      Filter.eventuallyEq_of_mem ((c.open_source.inter hV).mem_nhds ⟨hqc, hqV⟩) hback
    have h1 : mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 5) D q v = 0 := by
      rw [mfderiv_of_eventuallyEq_comp ((hFd _).comp (c q) hΦd) hcd hev v,
        fderiv_comp (c q) (hFd _) hΦd, ContinuousLinearMap.comp_apply, hv, hu, map_zero]
    have hv0 : v = 0 := hinjD (h1.trans (map_zero _).symm)
    rw [← hv, hv0, map_zero]
  have hunit : IsUnit (fderiv ℝ (ψ ∘ D ∘ c.symm) (c q)) :=
    ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.2
      ((LinearMap.isUnit_iff_ker_eq_bot _).2 (LinearMap.ker_eq_bot.2 hinj))
  -- the chart: `Φ` after `c`, near `q`
  obtain ⟨φ, hφ, hqφ, hsub, hφeq, -⟩ :=
    Join.exists_chart_of_localDiffeo hc hqc hV hqV hW hΦ hcqW hunit
  have hD' : ∀ q' ∈ φ.source, D q' = kruskalSym 1 R (kruskalWrap (φ q')) := fun q' hq' ↦ by
    rw [hφeq q']
    exact hback q' ⟨(hsub hq').1.1, (hsub hq').1.2⟩
  refine ⟨R, φ, hR, hφ, hqφ, fun q' hq' ↦ (hsub hq').1.2.1, fun q' hq' ↦ ⟨?_, hD' q' hq', ?_⟩⟩
  · rw [hφeq q', hΦc q' (hsub hq').1.1]
    exact (hsec (D q') (hsub hq').1.2.2 (hpt q' (hsub hq').1.2.1).1).1
  · intro v w
    have hφd : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q' :=
      (contMDiffAt_of_mem_maximalAtlas hφ hq').mdifferentiableAt (by simp)
    have hev : D =ᶠ[𝓝 q'] (kruskalSym 1 R ∘ kruskalWrap) ∘ φ :=
      Filter.eventuallyEq_of_mem (φ.open_source.mem_nhds hq') hD'
    have key : ∀ a b : Coords 4,
        tableMeasure (kruskalWhole m) (D q') (kruskalSym 1 R (fderiv ℝ kruskalWrap (φ q') a))
          (kruskalSym 1 R (fderiv ℝ kruskalWrap (φ q') b))
          = tableMeasure (kruskalG m) (φ q') a b := fun a b ↦ by
      rw [hD' q' hq', kruskalSym_measure m hL hR, ← kruskalWrap_pullback]
    rw [(hpt q' (hsub hq').1.2.1).2 v w, mfderiv_of_eventuallyEq_comp (hFd _) hφd hev v,
      mfderiv_of_eventuallyEq_comp (hFd _) hφd hev w, fderiv_kruskalSym_wrap,
      fderiv_kruskalSym_wrap]
    exact key _ _

/-- **A space-time with a length-keeping map into Kruskal's is Kruskal's in a chart around
every point of the region.** -/
theorem IsKruskalMapOn.isKruskalNear {D : M → Coords 5} (hD : IsKruskalMapOn m g D s)
    (hg : IsSpaceTimeOn g s) {q : M} (hq : q ∈ s) : IsKruskalNear m g q := by
  obtain ⟨R, φ, -, hφ, hqφ, -, h⟩ := hD.exists_chart hg hq
  exact ⟨φ, hφ, hqφ, fun q' hq' ↦ ⟨(h q' hq').1, (h q' hq').2.2⟩⟩

end KruskalChart

end GravityInLean.Curved
