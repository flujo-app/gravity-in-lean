/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.FlatRigid
public import GravityInLean.Global.SchwSym
public import GravityInLean.Join.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.LinearAlgebra.Matrix.ToLin

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Two length-keeping maps into flat space-time differ by a Lorentz transformation and a shift

The third part of `GlobalBirkhoffUnique` (`Goals/Global.lean`): `unique_flat`.

The steps:

* `IsSchwarzschildMapOn.exists_chart_eq`: near each point of its region a length-keeping map
  into Schwarzschild's whole space-time (any mass) **is** a chart of the curved space; so it
  carries the points near a point onto the points near its image
  (`IsSchwarzschildMapOn.map_nhds`).
* `IsSchwarzschildMapOn.exists_lorentz_near`: for mass zero, a second length-keeping map read
  in that chart keeps the flat length measure, so it is a linear map and a shift
  (`eventually_affine_of_keeps_form_self`, `Global/FlatRigid.lean`); the linear map is a Lorentz
  transformation (`lorentz_of_flat`).
* `IsSchwarzschildMapOn.lorentz_unique`: the transformation and the shift are fixed by the two
  maps near one point.
* So the pair is the same near every point, and the same on a region in one piece
  (`exists_const_of_locally'`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

section Chain

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]

/-- Two maps into coordinate space that agree near a point carry a step at that point to the
same step, if the second has a slope there. -/
theorem mfderiv_apply_congr_of_eventuallyEq {k : ℕ} {D D₂ : M → Coords k} {q : M}
    (h : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords k) D₂ q) (hev : D =ᶠ[𝓝 q] D₂)
    (v : TangentSpace 𝓘(ℝ, Coords 4) q) :
    mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords k) D q v
      = mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords k) D₂ q v := by
  have h2 : mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords k) D q
      = mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords k) D₂ q :=
    (h.hasMFDerivAt.congr_of_eventuallyEq_abuse hev).mfderiv
  exact congrArg (fun A : Coords 4 →L[ℝ] Coords k ↦ A v) h2

/-- **Chain rule for a map that is, near a point, a map of coordinate space after a map into
coordinate space,** for a target of any number of labels: if near `q` the map `D` is `F` after
`f`, then `D` carries a step at `q` to where the slope of `F` carries the step that `f` makes
of it. -/
theorem mfderiv_apply_of_eventuallyEq_comp {k : ℕ} {D : M → Coords k}
    {F : Coords 4 → Coords k} {f : M → Coords 4} {q : M} (hF : DifferentiableAt ℝ F (f q))
    (hf : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) f q) (hev : D =ᶠ[𝓝 q] F ∘ f)
    (v : TangentSpace 𝓘(ℝ, Coords 4) q) :
    mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords k) D q v
      = fderiv ℝ F (f q) (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) f q v) := by
  have hF' : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords k) F (f q) := hF.mdifferentiableAt
  rw [mfderiv_apply_congr_of_eventuallyEq (hF'.comp q hf) hev v, mfderiv_comp_apply q hF' hf v,
    mfderiv_eq_fderiv]
  rfl

end Chain

/-! ## The flat length measure -/

/-- The flat length of two steps does not mind their order. -/
theorem flat_symm (z u w : Coords 4) :
    tableMeasure (schwSpaceG 0) z u w = tableMeasure (schwSpaceG 0) z w u := by
  rw [schwSpace_zero_apply, schwSpace_zero_apply]
  ring

/-- The flat length of two steps is the same at every point. -/
theorem flat_base (z z' u w : Coords 4) :
    tableMeasure (schwSpaceG 0) z u w = tableMeasure (schwSpaceG 0) z' u w := by
  rw [schwSpace_zero_apply, schwSpace_zero_apply]

/-- In flat space-time only the zero step is at right angles to every step. -/
theorem flat_nondegenerate (z y : Coords 4)
    (h : ∀ w : Coords 4, tableMeasure (schwSpaceG 0) z y w = 0) : y = 0 := by
  have e := h ![-y 0, y 1, y 2, y 3]
  rw [schwSpace_zero_apply] at e
  have e' : -(y 0 * -y 0) + (y 1 * y 1 + y 2 * y 2 + y 3 * y 3) = 0 := by
    simpa only [Matrix.cons_val] using e
  have n0 := sq_nonneg (y 0)
  have n1 := sq_nonneg (y 1)
  have n2 := sq_nonneg (y 2)
  have n3 := sq_nonneg (y 3)
  have s0 : y 0 ^ 2 = 0 := by nlinarith
  have s1 : y 1 ^ 2 = 0 := by nlinarith
  have s2 : y 2 ^ 2 = 0 := by nlinarith
  have s3 : y 3 ^ 2 = 0 := by nlinarith
  have h0 : y 0 = 0 := (pow_eq_zero_iff two_ne_zero).mp s0
  have h1 : y 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp s1
  have h2 : y 2 = 0 := (pow_eq_zero_iff two_ne_zero).mp s2
  have h3 : y 3 = 0 := (pow_eq_zero_iff two_ne_zero).mp s3
  funext i
  fin_cases i
  exacts [h0, h1, h2, h3]

/-- **A matrix that keeps the flat length of every two steps is a Lorentz transformation.**
(The other way round is `lorentz_flat`.) -/
theorem lorentz_of_flat {Λ : Matrix (Fin 4) (Fin 4) ℝ}
    (H : ∀ u w : Coords 4, -(Λ.mulVec u 0 * Λ.mulVec w 0) + (Λ.mulVec u 1 * Λ.mulVec w 1
        + Λ.mulVec u 2 * Λ.mulVec w 2 + Λ.mulVec u 3 * Λ.mulVec w 3)
      = -(u 0 * w 0) + (u 1 * w 1 + u 2 * w 2 + u 3 * w 3)) :
    Λ.transpose * lightSign4 * Λ = lightSign4 := by
  have h : ∀ u w : Coords 4, u ⬝ᵥ (Λ.transpose * lightSign4 * Λ).mulVec w
      = u ⬝ᵥ lightSign4.mulVec w := fun u w ↦ by
    rw [← Matrix.mulVec_mulVec w (Λ.transpose * lightSign4) Λ,
      ← Matrix.mulVec_mulVec (Λ.mulVec w) Λ.transpose lightSign4,
      Matrix.dotProduct_mulVec u Λ.transpose, Matrix.vecMul_transpose, lightSign4_dot,
      lightSign4_dot]
    exact H u w
  refine Matrix.ext fun i j ↦ ?_
  simpa [Matrix.mulVec_single_one, single_one_dotProduct] using
    h (Pi.single i 1) (Pi.single j 1)

section UniqueFlat

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  [IsManifold 𝓘(ℝ, Coords 4) ∞ M] {m : ℝ} {g : LengthMeasure 𝓘(ℝ, Coords 4) M} {s : Set M}

/-- **A length-keeping map into Schwarzschild's whole space-time is, near each point, a chart
of the curved space.** Around `q` there is a chart `φ` with domain inside the region that is
equal to `D` on its domain. For every mass. -/
theorem IsSchwarzschildMapOn.exists_chart_eq {D : M → Coords 4}
    (hD : IsSchwarzschildMapOn m g D s) (hg : IsSpaceTimeOn g s) {q : M} (hq : q ∈ s) :
    ∃ φ : OpenPartialHomeomorph M (Coords 4),
      φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M ∧ q ∈ φ.source ∧ φ.source ⊆ s ∧
      ∀ q' ∈ φ.source, φ q' = D q' := by
  have hinjD := hD.mfderiv_injective hg hq
  obtain ⟨hs, hsm, -⟩ := hD
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
  -- the region read in the chart, and `D` read in the chart
  have hW : IsOpen (c.target ∩ c.symm ⁻¹' s) := c.isOpen_inter_preimage_symm hs
  have hcqW : c q ∈ c.target ∩ c.symm ⁻¹' s := by
    refine ⟨c.map_source hqc, ?_⟩
    change c.symm (c q) ∈ s
    rw [c.left_inv hqc]
    exact hq
  have hΦ : ContDiffOn ℝ ∞ (D ∘ c.symm) (c.target ∩ c.symm ⁻¹' s) := by
    have h1 : ContMDiffOn 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) ∞ (D ∘ c.symm)
        (c.target ∩ c.symm ⁻¹' s) :=
      hsm.comp ((contMDiffOn_symm_of_mem_maximalAtlas hc).mono inter_subset_left)
        fun y hy ↦ hy.2
    exact contMDiffOn_iff_contDiffOn.1 h1
  have hΦc : ∀ q' ∈ c.source, (D ∘ c.symm) (c q') = D q' := fun q' hq' ↦ by
    change D (c.symm (c q')) = D q'
    rw [c.left_inv hq']
  -- its slope at `c q` carries no step to zero, because `D` carries none to zero
  have hΦd : DifferentiableAt ℝ (D ∘ c.symm) (c q) :=
    (hΦ.contDiffAt (hW.mem_nhds hcqW)).differentiableAt (by simp)
  have hinj : Function.Injective (fderiv ℝ (D ∘ c.symm) (c q)) := by
    refine (injective_iff_map_eq_zero _).mpr fun u hu ↦ ?_
    obtain ⟨v, hv⟩ := hcsurj u
    have hev : D =ᶠ[𝓝 q] (D ∘ c.symm) ∘ c :=
      Filter.eventuallyEq_of_mem (c.open_source.mem_nhds hqc) fun q' hq' ↦ (hΦc q' hq').symm
    have h1 : mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D q v = 0 := by
      rw [mfderiv_apply_of_eventuallyEq_comp hΦd hcd hev v, hv, hu]
    have hv0 : v = 0 := hinjD (h1.trans (map_zero _).symm)
    rw [← hv, hv0, map_zero]
  have hunit : IsUnit (fderiv ℝ (D ∘ c.symm) (c q)) :=
    ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.2
      ((LinearMap.isUnit_iff_ker_eq_bot _).2 (LinearMap.ker_eq_bot.2 hinj))
  -- the chart: `D` read in `c`, after `c`
  obtain ⟨φ, hφ, hqφ, hsub, hφeq, -⟩ :=
    Join.exists_chart_of_localDiffeo hc hqc hs hq hW hΦ hcqW hunit
  exact ⟨φ, hφ, hqφ, fun q' hq' ↦ (hsub hq').1.2,
    fun q' hq' ↦ by rw [hφeq q', hΦc q' (hsub hq').1.1]⟩

/-- **A length-keeping map into Schwarzschild's whole space-time carries the points near a
point onto the points near its image:** what holds near `D q` is what holds at `D q'` for `q'`
near `q`. -/
theorem IsSchwarzschildMapOn.map_nhds {D : M → Coords 4} (hD : IsSchwarzschildMapOn m g D s)
    (hg : IsSpaceTimeOn g s) {q : M} (hq : q ∈ s) : Filter.map D (𝓝 q) = 𝓝 (D q) := by
  obtain ⟨φ, -, hqφ, -, hφeq⟩ := hD.exists_chart_eq hg hq
  have hev : D =ᶠ[𝓝 q] φ :=
    Filter.eventuallyEq_of_mem (φ.open_source.mem_nhds hqφ) fun q' hq' ↦ (hφeq q' hq').symm
  rw [Filter.map_congr hev, φ.map_nhds_eq hqφ, hφeq q hqφ]

/-- **Near each point, two length-keeping maps into flat space-time differ by a Lorentz
transformation and a shift.** -/
theorem IsSchwarzschildMapOn.exists_lorentz_near {D D' : M → Coords 4}
    (hD : IsSchwarzschildMapOn 0 g D s) (hD' : IsSchwarzschildMapOn 0 g D' s)
    (hg : IsSpaceTimeOn g s) {q : M} (hq : q ∈ s) :
    ∃ (Λ : Matrix (Fin 4) (Fin 4) ℝ) (b : Coords 4),
      Λ.transpose * lightSign4 * Λ = lightSign4 ∧
      ∀ᶠ q' in 𝓝 q, D' q' = Λ.mulVec (D q') + b := by
  obtain ⟨φ, hφ, hqφ, hsub, hφeq⟩ := hD.exists_chart_eq hg hq
  obtain ⟨-, -, hpt⟩ := hD
  obtain ⟨-, hsm', hpt'⟩ := hD'
  have hφmd : φ.MDifferentiable 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas hφ).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas hφ).mdifferentiableOn (by simp)⟩
  -- `D'` read in the chart `φ`, which is `D`
  have hf : ContDiffOn ℝ ∞ (D' ∘ φ.symm) φ.target := by
    have h1 : ContMDiffOn 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) ∞ (D' ∘ φ.symm) φ.target :=
      hsm'.comp (contMDiffOn_symm_of_mem_maximalAtlas hφ) fun y hy ↦ hsub (φ.map_target hy)
    exact contMDiffOn_iff_contDiffOn.1 h1
  have hfφ : ∀ q' ∈ φ.source, (D' ∘ φ.symm) (φ q') = D' q' := fun q' hq' ↦ by
    change D' (φ.symm (φ q')) = D' q'
    rw [φ.left_inv hq']
  -- it keeps the flat length measure: both maps give the lengths of `g`
  have hkeep : ∀ x ∈ φ.target, ∀ u v : Coords 4,
      tableMeasure (schwSpaceG 0) 0 (fderiv ℝ (D' ∘ φ.symm) x u) (fderiv ℝ (D' ∘ φ.symm) x v)
        = tableMeasure (schwSpaceG 0) 0 u v := by
    intro x hx u v
    have hq' : φ.symm x ∈ φ.source := φ.map_target hx
    have hxφ : φ (φ.symm x) = x := φ.right_inv hx
    obtain ⟨a, ha⟩ := hφmd.mfderiv_surjective hq' u
    obtain ⟨b, hb⟩ := hφmd.mfderiv_surjective hq' v
    have hφd : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ (φ.symm x) :=
      (contMDiffAt_of_mem_maximalAtlas hφ hq').mdifferentiableAt (by simp)
    have hfd : DifferentiableAt ℝ (D' ∘ φ.symm) (φ (φ.symm x)) := by
      rw [hxφ]
      exact (hf.contDiffAt (φ.open_target.mem_nhds hx)).differentiableAt (by simp)
    have hevD : D =ᶠ[𝓝 (φ.symm x)] φ :=
      Filter.eventuallyEq_of_mem (φ.open_source.mem_nhds hq') fun p hp ↦ (hφeq p hp).symm
    have hevD' : D' =ᶠ[𝓝 (φ.symm x)] (D' ∘ φ.symm) ∘ φ :=
      Filter.eventuallyEq_of_mem (φ.open_source.mem_nhds hq') fun p hp ↦ (hfφ p hp).symm
    have e1 : g (φ.symm x) a b = tableMeasure (schwSpaceG 0) 0 u v := by
      rw [(hpt _ (hsub hq')).2 a b, mfderiv_apply_congr_of_eventuallyEq hφd hevD a,
        mfderiv_apply_congr_of_eventuallyEq hφd hevD b, ha, hb]
      exact flat_base _ _ _ _
    have e2 : g (φ.symm x) a b = tableMeasure (schwSpaceG 0) 0
        (fderiv ℝ (D' ∘ φ.symm) x u) (fderiv ℝ (D' ∘ φ.symm) x v) := by
      rw [(hpt' _ (hsub hq')).2 a b, mfderiv_apply_of_eventuallyEq_comp hfd hφd hevD' a,
        mfderiv_apply_of_eventuallyEq_comp hfd hφd hevD' b, ha, hb, hxφ]
      exact flat_base _ _ _ _
    exact e2.symm.trans e1
  -- so it is a linear map that keeps the flat lengths, and a shift, near `φ q`
  obtain ⟨Λ, b, hΛ, hev⟩ := eventually_affine_of_keeps_form_self
    (B := tableMeasure (schwSpaceG 0) 0) (fun y z ↦ flat_symm 0 y z)
    (fun y h ↦ flat_nondegenerate 0 y h) φ.open_target
    (hf.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ ∞)) hkeep (φ.map_source hqφ)
  -- the linear map as a matrix
  have hmul : ∀ y : Coords 4,
      (LinearMap.toMatrix' (Λ : Coords 4 →ₗ[ℝ] Coords 4)).mulVec y = Λ y := fun y ↦ by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  refine ⟨LinearMap.toMatrix' (Λ : Coords 4 →ₗ[ℝ] Coords 4), b, ?_, ?_⟩
  · refine lorentz_of_flat fun u w ↦ ?_
    rw [hmul, hmul, ← schwSpace_zero_apply 0 (Λ u) (Λ w), ← schwSpace_zero_apply 0 u w]
    exact hΛ u w
  · filter_upwards [(φ.continuousAt hqφ).eventually hev, φ.open_source.mem_nhds hqφ]
      with q' h1 h2
    rw [hmul, ← hφeq q' h2, ← h1]
    exact (hfφ q' h2).symm

/-- **The Lorentz transformation and the shift are fixed by the two maps near one point:** a
length-keeping map fills a neighbourhood of its image, and a linear map with a shift is known
from its values on an open set. -/
theorem IsSchwarzschildMapOn.lorentz_unique {D D' : M → Coords 4}
    (hD : IsSchwarzschildMapOn m g D s) (hg : IsSpaceTimeOn g s) {q : M} (hq : q ∈ s)
    {Λ Λ' : Matrix (Fin 4) (Fin 4) ℝ} {b b' : Coords 4}
    (h : ∀ᶠ q' in 𝓝 q, D' q' = Λ.mulVec (D q') + b)
    (h' : ∀ᶠ q' in 𝓝 q, D' q' = Λ'.mulVec (D q') + b') : Λ = Λ' ∧ b = b' := by
  have hev : ∀ᶠ x in 𝓝 (D q), Λ.mulVec x + b = Λ'.mulVec x + b' := by
    rw [← hD.map_nhds hg hq]
    exact Filter.eventually_map.mpr ((h.and h').mono fun q' hq' ↦ hq'.1.symm.trans hq'.2)
  have hfd : fderiv ℝ (fun x : Coords 4 ↦ Λ.mulVec x + b) (D q)
      = fderiv ℝ (fun x : Coords 4 ↦ Λ'.mulVec x + b') (D q) := Filter.EventuallyEq.fderiv_eq hev
  have hΛ : Λ = Λ' := Matrix.mulVec_injective (funext fun u ↦ by
    rw [← fderiv_mulVec_add Λ b (D q) u, hfd, fderiv_mulVec_add])
  have h0 : Λ.mulVec (D q) + b = Λ'.mulVec (D q) + b' := hev.self_of_nhds
  subst hΛ
  exact ⟨rfl, add_left_cancel h0⟩

/-- **Two length-keeping maps into flat space-time differ by one Lorentz transformation and
one shift,** on a region in one piece. This is the third part of `GlobalBirkhoffUnique`. -/
theorem unique_flat (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (s : Set M) (hs : IsPreconnected s)
    (hg : IsSpaceTimeOn g s) (D D' : M → Coords 4) (hD : IsSchwarzschildMapOn 0 g D s)
    (hD' : IsSchwarzschildMapOn 0 g D' s) :
    ∃ (Λ : Matrix (Fin 4) (Fin 4) ℝ) (b : Coords 4),
      Λ.transpose * lightSign4 * Λ = lightSign4 ∧ ∀ q ∈ s, D' q = Λ.mulVec (D q) + b := by
  -- an empty region: the transformation that does nothing serves
  rcases s.eq_empty_or_nonempty with rfl | ⟨q₀, hq₀⟩
  · exact ⟨1, 0, by simp, fun q hq ↦ absurd hq (Set.notMem_empty q)⟩
  -- the label of a point: a Lorentz transformation and a shift that serve near it
  obtain ⟨l, hl⟩ := exists_const_of_locally' hs
    (R := fun (q : M) (l : Matrix (Fin 4) (Fin 4) ℝ × Coords 4) ↦
      l.1.transpose * lightSign4 * l.1 = lightSign4
        ∧ ∀ᶠ q' in 𝓝 q, D' q' = l.1.mulVec (D q') + l.2)
    (fun q hq l l' h h' ↦
      Prod.ext (hD.lorentz_unique hg hq h.2 h'.2).1 (hD.lorentz_unique hg hq h.2 h'.2).2)
    (fun p hp ↦ by
      obtain ⟨Λ, b, hΛ, hev⟩ := hD.exists_lorentz_near hD' hg hp
      exact ⟨(Λ, b), hev.eventually_nhds.mono fun q' hq' ↦ ⟨hΛ, hq'⟩⟩)
  exact ⟨l.1, l.2, (hl q₀ hq₀).1, fun q hq ↦ (hl q hq).2.self_of_nhds⟩

end UniqueFlat

end GravityInLean.Curved
