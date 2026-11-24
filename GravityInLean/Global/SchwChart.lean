/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.SchwSection
public import GravityInLean.Global.SchwSym
public import GravityInLean.Join.Atlas
public import GravityInLean.Join.CarryBracket

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# A length-keeping map into Schwarzschild's whole space-time gives charts with Schwarzschild's table

Around every point that a length-keeping map `D` sends off the centre, `D` is, up to a turn or
mirror of space, the map `sphericalToSpace` after a chart of the curved space; in that chart the
length measure is Schwarzschild's table of distance and angles.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

section SchwChart

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  [IsManifold 𝓘(ℝ, Coords 4) ∞ M] {m : ℝ} {g : LengthMeasure 𝓘(ℝ, Coords 4) M} {s : Set M}

omit [IsManifold 𝓘(ℝ, Coords 4) ∞ M] in
/-- **Chain rule for a map that is `sphericalToSpace` and a symmetry after another map.** If,
near `q`, the map `D` is `φ`, then `sphericalToSpace`, then the turn or mirror `R`, then the
slope of `D` at `q` is the slope of `φ`, then the slope of `sphericalToSpace`, then the slope of
the symmetry. -/
theorem mfderiv_of_eq_schwSym_sphericalToSpace {D φ : M → Coords 4}
    {R : Matrix (Fin 3) (Fin 3) ℝ} {q : M}
    (hφ : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q)
    (h : D =ᶠ[𝓝 q] schwSym 1 0 R ∘ (sphericalToSpace ∘ φ))
    (v : TangentSpace 𝓘(ℝ, Coords 4) q) :
    mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D q v
      = fderiv ℝ (schwSym 1 0 R) (sphericalToSpace (φ q))
          (fderiv ℝ sphericalToSpace (φ q) (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q v)) := by
  have hS : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) (schwSym 1 0 R)
      ((sphericalToSpace ∘ φ) q) :=
    ((contDiff_schwSym 1 0 R).contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  have hT : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) sphericalToSpace (φ q) :=
    (contDiff_sphericalToSpace.contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  have hTφ : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) (sphericalToSpace ∘ φ) q :=
    hT.comp q hφ
  have e : mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D q
      = mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) (schwSym 1 0 R ∘ (sphericalToSpace ∘ φ)) q :=
    ((hS.comp q hTφ).hasMFDerivAt.congr_of_eventuallyEq_abuse h).mfderiv
  calc mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D q v
      = mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) (schwSym 1 0 R ∘ (sphericalToSpace ∘ φ)) q v :=
        DFunLike.congr_fun e v
    _ = fderiv ℝ (schwSym 1 0 R) (sphericalToSpace (φ q))
          (fderiv ℝ sphericalToSpace (φ q)
            (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q v)) := by
        rw [mfderiv_comp_apply q hS hTφ v, mfderiv_comp_apply q hT hφ v, mfderiv_eq_fderiv,
          mfderiv_eq_fderiv]
        rfl

/-- **A length-keeping map into Schwarzschild's whole space-time is, near each point it sends
off the centre, `sphericalToSpace` after a chart.** Around `q` there are a chart `φ` of the
curved space with domain inside the region, landing where the distance label is positive and off
the poles, and a turn or mirror `R` of space, such that `D` is `φ`, then `sphericalToSpace`,
then `R`; and in the chart `φ` the length measure is Schwarzschild's table. -/
theorem IsSchwarzschildMapOn.exists_chart {D : M → Coords 4} (hm : m ≤ 0)
    (hD : IsSchwarzschildMapOn m g D s) (hg : IsSpaceTimeOn g s) {q : M} (hq : q ∈ s)
    (hoff : 0 < D q 1 ^ 2 + D q 2 ^ 2 + D q 3 ^ 2) :
    ∃ (R : Matrix (Fin 3) (Fin 3) ℝ) (φ : OpenPartialHomeomorph M (Coords 4)),
      R.transpose * R = 1 ∧ φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M ∧ q ∈ φ.source ∧
      φ.source ⊆ s ∧
      ∀ q' ∈ φ.source, φ q' ∈ outside m ∧ D q' = schwSym 1 0 R (sphericalToSpace (φ q')) ∧
        ∀ v w : TangentSpace 𝓘(ℝ, Coords 4) q',
          g q' v w = flatMeasure (tableMeasure (roundG (schwA m) (schwB m))) (φ q')
            (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q' v)
            (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q' w) := by
  have hs : IsOpen s := hD.1
  have hsm : ContMDiffOn 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) ∞ D s := hD.2.1
  obtain ⟨R, U, ψ, hR, hU, hzU, hψ, hψU⟩ := exists_sphericalToSpace_section hoff
  -- a chart `c` of the curved space around `q`
  obtain ⟨c, hc, hqc⟩ : ∃ c : OpenPartialHomeomorph M (Coords 4),
      c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M ∧ q ∈ c.source :=
    ⟨chartAt (Coords 4) q, IsManifold.chart_mem_maximalAtlas q, mem_chart_source (Coords 4) q⟩
  -- the points of the region that `D` sends into `U`, and their labels in the chart `c`
  have hV : IsOpen (s ∩ D ⁻¹' U) := hsm.continuousOn.isOpen_inter_preimage hs hU
  have hW : IsOpen (c.target ∩ c.symm ⁻¹' (s ∩ D ⁻¹' U)) := c.isOpen_inter_preimage_symm hV
  have hN : IsOpen (c.source ∩ (s ∩ D ⁻¹' U)) := c.open_source.inter hV
  -- distance and angles of `D`, read in the chart `c`
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : Coords 4 → Coords 4, ∀ y, Φ y = ψ (D (c.symm y)) :=
    ⟨fun y ↦ ψ (D (c.symm y)), fun y ↦ rfl⟩
  have hDc : ContDiffOn ℝ ∞ (D ∘ c.symm) (c.target ∩ c.symm ⁻¹' (s ∩ D ⁻¹' U)) :=
    contMDiffOn_iff_contDiffOn.1
      (hsm.comp ((contMDiffOn_symm_of_mem_maximalAtlas hc).mono inter_subset_left)
        fun y hy ↦ hy.2.1)
  have hΦ : ContDiffOn ℝ ∞ Φ (c.target ∩ c.symm ⁻¹' (s ∩ D ⁻¹' U)) :=
    (hψ.comp hDc fun y hy ↦ hy.2.2).congr fun y _ ↦ hΦdef y
  have hpW : c q ∈ c.target ∩ c.symm ⁻¹' (s ∩ D ⁻¹' U) := by
    refine ⟨c.map_source hqc, ?_⟩
    rw [mem_preimage, c.left_inv hqc]
    exact ⟨hq, hzU⟩
  -- on that open set, `D` is `Φ ∘ c`, then `sphericalToSpace`, then the turn `R`
  have hfact : ∀ q' ∈ c.source ∩ (s ∩ D ⁻¹' U),
      D q' = (schwSym 1 0 R ∘ (sphericalToSpace ∘ (Φ ∘ c))) q' := by
    intro q' hq'
    change D q' = schwSym 1 0 R (sphericalToSpace (Φ (c q')))
    rw [hΦdef, c.left_inv hq'.1]
    exact (hψU _ hq'.2.2).2.2.symm
  have hev : D =ᶠ[𝓝 q] schwSym 1 0 R ∘ (sphericalToSpace ∘ (Φ ∘ c)) :=
    Filter.eventuallyEq_of_mem (hN.mem_nhds ⟨hqc, hq, hzU⟩) hfact
  -- the slope of `Φ` at `c q` carries no step to zero, because the slope of `D` carries none
  have hcq : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) c q :=
    (contMDiffAt_of_mem_maximalAtlas hc hqc).mdifferentiableAt (by simp)
  have hΦd : DifferentiableAt ℝ Φ (c q) :=
    (hΦ.contDiffAt (hW.mem_nhds hpW)).differentiableAt (by simp)
  have hΦm : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) Φ (c q) := hΦd.mdifferentiableAt
  have hΦc : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) (Φ ∘ c) q := hΦm.comp q hcq
  have hsurj : ∀ u : Coords 4, ∃ v : TangentSpace 𝓘(ℝ, Coords 4) q,
      mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) c q v = u := by
    obtain ⟨e, he⟩ := Join.chart_isInvertible_mfderiv hc hqc
    exact fun u ↦ ⟨e.symm u, by rw [← he]; exact e.apply_symm_apply u⟩
  have hslope : ∀ v : TangentSpace 𝓘(ℝ, Coords 4) q,
      mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D q v
        = fderiv ℝ (schwSym 1 0 R) (sphericalToSpace (Φ (c q)))
            (fderiv ℝ sphericalToSpace (Φ (c q))
              (fderiv ℝ Φ (c q) (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) c q v))) := by
    intro v
    rw [mfderiv_of_eq_schwSym_sphericalToSpace hΦc hev v, mfderiv_comp_apply q hΦm hcq v,
      mfderiv_eq_fderiv]
    rfl
  have hinj : Function.Injective (fderiv ℝ Φ (c q)) := by
    refine (injective_iff_map_eq_zero _).mpr fun u hu ↦ ?_
    obtain ⟨v, rfl⟩ := hsurj u
    have h0 : mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D q v = 0 := by
      rw [hslope v, hu, map_zero, map_zero]
    have hv : v = 0 := hD.mfderiv_injective hg hq (h0.trans (map_zero _).symm)
    rw [hv, map_zero]
  have hunit : IsUnit (fderiv ℝ Φ (c q)) :=
    ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.2
      ((LinearMap.isUnit_iff_ker_eq_bot _).2 (LinearMap.ker_eq_bot.2 hinj))
  -- so `Φ` after `c` is a chart of the curved space near `q`
  obtain ⟨φ, hφ, hqφ, hφsub, hφeq, -⟩ :=
    Join.exists_chart_of_localDiffeo hc hqc hs hq hW hΦ hpW hunit
  -- on the chart's domain, `φ` is the distance and angles of `D`
  have hall : ∀ q' ∈ φ.source, D q' ∈ U ∧ φ q' = ψ (D q') := by
    intro q' hq'
    obtain ⟨⟨hq'c, -⟩, hq'W⟩ := hφsub hq'
    have hU' : D (c.symm (c q')) ∈ U := hq'W.2.2
    rw [c.left_inv hq'c] at hU'
    refine ⟨hU', ?_⟩
    rw [hφeq, hΦdef, c.left_inv hq'c]
  have hback : ∀ q' ∈ φ.source, D q' = schwSym 1 0 R (sphericalToSpace (φ q')) := by
    intro q' hq'
    rw [(hall q' hq').2]
    exact (hψU _ (hall q' hq').1).2.2.symm
  refine ⟨R, φ, hR, hφ, hqφ, fun q' hq' ↦ (hφsub hq').1.2, fun q' hq' ↦ ?_⟩
  have hq's : q' ∈ s := (hφsub hq').1.2
  obtain ⟨hr, hsin, -⟩ := hψU _ (hall q' hq').1
  rw [← (hall q' hq').2] at hr hsin
  refine ⟨⟨hr, by linarith, hsin⟩, hback q' hq', fun v w ↦ ?_⟩
  -- lengths: the slope of `D` is the slope of `φ`, then of `sphericalToSpace`, then of the turn
  have hφm : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q' :=
    (contMDiffAt_of_mem_maximalAtlas hφ hq').mdifferentiableAt (by simp)
  have hev' : D =ᶠ[𝓝 q'] schwSym 1 0 R ∘ (sphericalToSpace ∘ φ) :=
    Filter.eventuallyEq_of_mem (φ.open_source.mem_nhds hq') hback
  have e1 := schwSym_measure (ε := 1) (c := 0) m (Or.inl rfl) hR (sphericalToSpace (φ q'))
    (fderiv ℝ sphericalToSpace (φ q') (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q' v))
    (fderiv ℝ sphericalToSpace (φ q') (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q' w))
  have e2 := sphericalToSpace_pullback m hr (by linarith : φ q' 1 ≠ 2 * m)
    (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q' v)
    (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q' w)
  rw [(hD.2.2 q' hq's).2 v w, mfderiv_of_eq_schwSym_sphericalToSpace hφm hev' v,
    mfderiv_of_eq_schwSym_sphericalToSpace hφm hev' w, hback q' hq']
  exact e1.trans e2.symm

/-- **A space-time with a length-keeping map into Schwarzschild's whole space-time (mass zero
or negative) is Schwarzschild's in a chart around every point of the region.** For mass zero a
point sent to the centre is first shifted off it. -/
theorem IsSchwarzschildMapOn.isSchwarzschildWith {D : M → Coords 4} (hm : m ≤ 0)
    (hD : IsSchwarzschildMapOn m g D s) (hg : IsSpaceTimeOn g s) {q : M} (hq : q ∈ s) :
    IsSchwarzschildWith m g q := by
  -- off the centre, the chart of `exists_chart` is the chart asked for
  have key : ∀ {D : M → Coords 4}, IsSchwarzschildMapOn m g D s →
      0 < D q 1 ^ 2 + D q 2 ^ 2 + D q 3 ^ 2 → IsSchwarzschildWith m g q := by
    intro D hD hoff
    obtain ⟨R, φ, -, hφ, hqφ, -, hall⟩ := hD.exists_chart hm hg hq hoff
    exact ⟨φ, hφ, hqφ, fun q' hq' ↦ ⟨Or.inl (hall q' hq').1, (hall q' hq').2.2⟩⟩
  by_cases hoff : 0 < D q 1 ^ 2 + D q 2 ^ 2 + D q 3 ^ 2
  · exact key hD hoff
  · -- at the centre the mass is zero; shift the map by one unit along the first space label
    have hreg : m = 0 ∨ 0 < D q 1 ^ 2 + D q 2 ^ 2 + D q 3 ^ 2 := (hD.2.2 q hq).1
    have hm0 : m = 0 := hreg.resolve_right hoff
    subst hm0
    have hle : D q 1 ^ 2 + D q 2 ^ 2 + D q 3 ^ 2 ≤ 0 := not_lt.mp hoff
    have hsq : ∀ a b c : ℝ, a ^ 2 + b ^ 2 + c ^ 2 ≤ 0 → a = 0 := fun a b c h ↦
      (pow_eq_zero_iff two_ne_zero).1 (by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c])
    have h1 : D q 1 = 0 := hsq (D q 1) (D q 2) (D q 3) hle
    have h2 : D q 2 = 0 := hsq (D q 2) (D q 1) (D q 3) (by linarith)
    have h3 : D q 3 = 0 := hsq (D q 3) (D q 1) (D q 2) (by linarith)
    have hD' := hD.lorentz (Λ := 1) (by simp) (![0, 1, 0, 0] : Coords 4)
    refine key hD' ?_
    have e : ∀ i : Fin 4,
        ((1 : Matrix (Fin 4) (Fin 4) ℝ).mulVec (D q) + (![0, 1, 0, 0] : Coords 4)) i
          = D q i + (![0, 1, 0, 0] : Coords 4) i := fun i ↦ by
      rw [Matrix.one_mulVec]
      rfl
    change 0 < ((1 : Matrix (Fin 4) (Fin 4) ℝ).mulVec (D q) + (![0, 1, 0, 0] : Coords 4)) 1 ^ 2
      + ((1 : Matrix (Fin 4) (Fin 4) ℝ).mulVec (D q) + (![0, 1, 0, 0] : Coords 4)) 2 ^ 2
      + ((1 : Matrix (Fin 4) (Fin 4) ℝ).mulVec (D q) + (![0, 1, 0, 0] : Coords 4)) 3 ^ 2
    rw [e 1, e 2, e 3, h1, h2, h3]
    simp

end SchwChart

end GravityInLean.Curved
