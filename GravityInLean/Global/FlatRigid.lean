/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Topology.Connected.Basic

import Mathlib.Tactic

/-!
# A map that keeps a constant length measure is a straight map

Two tools without any curved space in them.

* `exists_const_of_locally'`: a label (of any kind) that is the same near every point of a
  region in one piece is the same on the whole region.
* `affine_of_keeps_form`: a smooth map between flat spaces whose slope carries one constant
  length measure to another has second slope zero (`snd_fderiv_eq_zero_of_keeps_form`), so on a
  region in one piece it is a linear map followed by a shift. `affine_of_keeps_form_self` and
  `eventually_affine_of_keeps_form_self` are the same for a map of one flat space of finitely
  many dimensions to itself that keeps one constant length measure: there the slope can always
  be undone, and the linear map keeps the length measure.
-/

@[expose] public section

namespace GravityInLean.Curved

open Filter Topology Set

/-- **The same near every point, so the same everywhere,** for labels of any kind. `R q l` says
"the point `q` has the label `l`". If a point of the region has at most one label, and every
point of the region has a label that all points near it have too, then one label serves the
whole region, as long as the region is in one piece. -/
theorem exists_const_of_locally' {X : Type*} [TopologicalSpace X] {L : Type*} [Nonempty L]
    {s : Set X} (hs : IsPreconnected s) {R : X → L → Prop}
    (huniq : ∀ q ∈ s, ∀ l l' : L, R q l → R q l' → l = l')
    (hloc : ∀ p ∈ s, ∃ l : L, ∀ᶠ q in 𝓝 p, R q l) : ∃ l : L, ∀ q ∈ s, R q l := by
  -- An empty region: any label serves.
  rcases s.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · exact ⟨Classical.arbitrary L, fun q hq ↦ absurd hq (Set.notMem_empty q)⟩
  -- Otherwise take the label `l₀` of one point `p₀`.
  obtain ⟨l₀, hl₀⟩ := hloc p₀ hp₀
  refine ⟨l₀, fun q hq ↦ ?_⟩
  -- The points near which the label is `l₀` form an open set ...
  have hUo : IsOpen {q : X | ∀ᶠ q' in 𝓝 q, R q' l₀} :=
    isOpen_iff_eventually.mpr fun q hq ↦ eventually_eventually_nhds.mpr hq
  -- ... and so do the points near which it is one other label.
  have hVo : IsOpen {q : X | ∃ l : L, l ≠ l₀ ∧ ∀ᶠ q' in 𝓝 q, R q' l} :=
    isOpen_iff_eventually.mpr fun q ⟨l, hl, hq⟩ ↦
      (eventually_eventually_nhds.mpr hq).mono fun q' hq' ↦ ⟨l, hl, hq'⟩
  -- The two sets cover the region.
  have hcover : s ⊆ {q : X | ∀ᶠ q' in 𝓝 q, R q' l₀}
      ∪ {q : X | ∃ l : L, l ≠ l₀ ∧ ∀ᶠ q' in 𝓝 q, R q' l} := fun q' hq' ↦ by
    obtain ⟨l, hl⟩ := hloc q' hq'
    by_cases h : l = l₀
    · exact Or.inl (h ▸ hl)
    · exact Or.inr ⟨l, h, hl⟩
  -- They do not meet inside the region: a point there has one label only.
  have hdisj : ¬ (s ∩ ({q : X | ∀ᶠ q' in 𝓝 q, R q' l₀}
      ∩ {q : X | ∃ l : L, l ≠ l₀ ∧ ∀ᶠ q' in 𝓝 q, R q' l})).Nonempty := by
    rintro ⟨q', hq', hqU, l, hl, hqV⟩
    exact hl (huniq q' hq' l l₀ hqV.self_of_nhds hqU.self_of_nhds)
  -- The region is in one piece and the first set meets it, so the second does not.
  rcases hcover hq with h | h
  · exact h.self_of_nhds
  · exact absurd (hs _ _ hUo hVo hcover ⟨p₀, hp₀, hl₀⟩ ⟨q, hq, h⟩) hdisj

section Rigid

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **A map that keeps a constant length measure has second slope zero.** `B` is a constant
length measure on the target (symmetric, and only the zero step is at right angles to every
step), `B₀` any constant table on the source. If the slope of `f` carries `B₀` to `B` at every
point of an open set, and can reach every step of the target, then the second slope of `f` is
zero there. (Differentiate `B (f' u) (f' v) = B₀ u v` and permute the three steps.) -/
theorem snd_fderiv_eq_zero_of_keeps_form {B : F →L[ℝ] F →L[ℝ] ℝ}
    (hsymm : ∀ y z, B y z = B z y) (hnd : ∀ y, (∀ z, B y z = 0) → y = 0) {B₀ : E → E → ℝ}
    {f : E → F} {W : Set E} (hW : IsOpen W) (hf : ContDiffOn ℝ 2 f W)
    (hsurj : ∀ x ∈ W, Function.Surjective (fderiv ℝ f x))
    (hkeep : ∀ x ∈ W, ∀ u v, B (fderiv ℝ f x u) (fderiv ℝ f x v) = B₀ u v) {x : E}
    (hx : x ∈ W) : fderiv ℝ (fderiv ℝ f) x = 0 := by
  have hfx : ContDiffAt ℝ 2 f x := hf.contDiffAt (hW.mem_nhds hx)
  -- the second slope does not mind the order of its two steps
  have hsym2 : ∀ v w, fderiv ℝ (fderiv ℝ f) x v w = fderiv ℝ (fderiv ℝ f) x w v :=
    hfx.isSymmSndFDerivAt (by simp)
  have hd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    ((hfx.fderiv_right (m := 1) one_add_one_eq_two.le).differentiableAt one_ne_zero).hasFDerivAt
  have hu : ∀ u : E, HasFDerivAt (fun y ↦ fderiv ℝ f y u)
      ((fderiv ℝ (fderiv ℝ f) x).flip u) x := fun u ↦ by
    simpa using hd.clm_apply (hasFDerivAt_const u x)
  -- differentiate `B (f' u) (f' v) = B₀ u v` in the direction `w`
  have key : ∀ u v w : E, B (fderiv ℝ f x u) (fderiv ℝ (fderiv ℝ f) x w v)
      + B (fderiv ℝ (fderiv ℝ f) x w u) (fderiv ℝ f x v) = 0 := fun u v w ↦ by
    have hc : HasFDerivAt (fun y ↦ B (fderiv ℝ f y u))
        (B.comp ((fderiv ℝ (fderiv ℝ f) x).flip u)) x := B.hasFDerivAt.comp x (hu u)
    have h1 := hc.clm_apply (hu v)
    have h2 : HasFDerivAt (fun y ↦ B (fderiv ℝ f y u) (fderiv ℝ f y v)) (0 : E →L[ℝ] ℝ) x :=
      (hasFDerivAt_const (B₀ u v) x).congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (hW.mem_nhds hx) fun y hy ↦ hkeep y hy u v)
    have h3 := congrArg (fun A : E →L[ℝ] ℝ ↦ A w) (h1.unique h2)
    simpa using h3
  -- the table `T w u v = B (f'' w u) (f' v)`: the same with `w`, `u` swapped, and the
  -- opposite with `u`, `v` swapped
  obtain ⟨T, hT⟩ : ∃ T : E → E → E → ℝ, ∀ w u v,
      T w u v = B (fderiv ℝ (fderiv ℝ f) x w u) (fderiv ℝ f x v) := ⟨_, fun _ _ _ ↦ rfl⟩
  have sym : ∀ w u v, T w u v = T u w v := fun w u v ↦ by rw [hT, hT, hsym2 w u]
  have anti : ∀ w u v, T w u v = -T w v u := fun w u v ↦ by
    have h := key u v w
    rw [hsymm (fderiv ℝ f x u)] at h
    rw [hT, hT]
    linarith
  have zero : ∀ w u v, T w u v = 0 := fun w u v ↦ by
    have h : T w u v = -T w u v :=
      calc T w u v = -T w v u := anti w u v
        _ = -T v w u := by rw [sym w v u]
        _ = T v u w := by rw [anti v w u, neg_neg]
        _ = T u v w := sym v u w
        _ = -T u w v := anti u v w
        _ = -T w u v := by rw [sym u w v]
    linarith
  -- so `f'' w u` is at right angles to every step
  refine ContinuousLinearMap.ext fun w ↦ ContinuousLinearMap.ext fun u ↦ ?_
  rw [zero_apply, zero_apply]
  refine hnd _ fun z ↦ ?_
  obtain ⟨v, rfl⟩ := hsurj x hx z
  rw [← hT]
  exact zero w u v

/-- **A map that keeps a constant length measure is a linear map followed by a shift,** on an
open region in one piece: `f y = Λ y + b` there, and `Λ` is the slope of `f` at every point of
the region. Assumptions as in `snd_fderiv_eq_zero_of_keeps_form`. -/
theorem affine_of_keeps_form {B : F →L[ℝ] F →L[ℝ] ℝ}
    (hsymm : ∀ y z, B y z = B z y) (hnd : ∀ y, (∀ z, B y z = 0) → y = 0) {B₀ : E → E → ℝ}
    {f : E → F} {W : Set E} (hW : IsOpen W) (hWc : IsPreconnected W) (hf : ContDiffOn ℝ 2 f W)
    (hsurj : ∀ x ∈ W, Function.Surjective (fderiv ℝ f x))
    (hkeep : ∀ x ∈ W, ∀ u v, B (fderiv ℝ f x u) (fderiv ℝ f x v) = B₀ u v) :
    ∃ (Λ : E →L[ℝ] F) (b : F), ∀ y ∈ W, f y = Λ y + b ∧ fderiv ℝ f y = Λ := by
  rcases W.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, 0, fun y hy ↦ absurd hy (Set.notMem_empty y)⟩
  -- the slope is the same at every point
  have hdf : DifferentiableOn ℝ (fderiv ℝ f) W :=
    (hf.fderiv_of_isOpen (m := 1) hW one_add_one_eq_two.le).differentiableOn one_ne_zero
  have hconst : ∀ y ∈ W, fderiv ℝ f y = fderiv ℝ f x₀ := fun y hy ↦
    hW.is_const_of_fderiv_eq_zero hWc hdf
      (fun x hx ↦ snd_fderiv_eq_zero_of_keeps_form hsymm hnd hW hf hsurj hkeep hx) hy hx₀
  -- so `f` less that linear map has slope zero
  have hfd : DifferentiableOn ℝ f W := hf.differentiableOn two_ne_zero
  have hg : DifferentiableOn ℝ (fun y ↦ f y - fderiv ℝ f x₀ y) W :=
    hfd.sub (fderiv ℝ f x₀).differentiable.differentiableOn
  have hg' : W.EqOn (fderiv ℝ (fun y ↦ f y - fderiv ℝ f x₀ y)) 0 := fun y hy ↦ by
    have h1 : HasFDerivAt (fun y ↦ f y - fderiv ℝ f x₀ y) (fderiv ℝ f y - fderiv ℝ f x₀) y :=
      ((hfd.differentiableAt (hW.mem_nhds hy)).hasFDerivAt).sub (fderiv ℝ f x₀).hasFDerivAt
    rw [h1.fderiv, hconst y hy, sub_self]
    rfl
  refine ⟨fderiv ℝ f x₀, f x₀ - fderiv ℝ f x₀ x₀, fun y hy ↦ ⟨?_, hconst y hy⟩⟩
  have h : f y - fderiv ℝ f x₀ y = f x₀ - fderiv ℝ f x₀ x₀ :=
    hW.is_const_of_fderiv_eq_zero hWc hg hg' hy hx₀
  rw [← h]
  abel

/-- **A map of a flat space to itself that keeps a constant length measure is a linear map
that keeps the measure, followed by a shift,** on an open region in one piece. `B` is symmetric,
and only the zero step is at right angles to every step. -/
theorem affine_of_keeps_form_self [FiniteDimensional ℝ E] {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hsymm : ∀ y z, B y z = B z y) (hnd : ∀ y, (∀ z, B y z = 0) → y = 0)
    {f : E → E} {W : Set E} (hW : IsOpen W) (hWc : IsPreconnected W) (hf : ContDiffOn ℝ 2 f W)
    (hkeep : ∀ x ∈ W, ∀ u v, B (fderiv ℝ f x u) (fderiv ℝ f x v) = B u v) :
    ∃ (Λ : E →L[ℝ] E) (b : E), (∀ u v, B (Λ u) (Λ v) = B u v)
      ∧ ∀ y ∈ W, f y = Λ y + b ∧ fderiv ℝ f y = Λ := by
  rcases W.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨ContinuousLinearMap.id ℝ E, 0, fun u v ↦ rfl, fun y hy ↦ absurd hy (Set.notMem_empty y)⟩
  -- the slope carries no step to zero, so it reaches every step
  have hsurj : ∀ x ∈ W, Function.Surjective (fderiv ℝ f x) := fun x hx ↦ by
    have hinj : Function.Injective (fderiv ℝ f x : E →ₗ[ℝ] E) := by
      refine (injective_iff_map_eq_zero _).mpr fun u hu ↦ hnd u fun z ↦ ?_
      have hu' : fderiv ℝ f x u = 0 := hu
      rw [← hkeep x hx u z, hu', map_zero, zero_apply]
    exact LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨Λ, b, h⟩ := affine_of_keeps_form hsymm hnd hW hWc hf hsurj hkeep
  refine ⟨Λ, b, fun u v ↦ ?_, h⟩
  rw [← (h x₀ hx₀).2]
  exact hkeep x₀ hx₀ u v

/-- **The same near one point,** with no assumption on the shape of the open set: near every
point of it the map is a linear map that keeps the measure, followed by a shift. -/
theorem eventually_affine_of_keeps_form_self [FiniteDimensional ℝ E] {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hsymm : ∀ y z, B y z = B z y) (hnd : ∀ y, (∀ z, B y z = 0) → y = 0)
    {f : E → E} {W : Set E} (hW : IsOpen W) (hf : ContDiffOn ℝ 2 f W)
    (hkeep : ∀ x ∈ W, ∀ u v, B (fderiv ℝ f x u) (fderiv ℝ f x v) = B u v) {x₀ : E}
    (hx₀ : x₀ ∈ W) :
    ∃ (Λ : E →L[ℝ] E) (b : E), (∀ u v, B (Λ u) (Λ v) = B u v)
      ∧ ∀ᶠ y in 𝓝 x₀, f y = Λ y + b := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hW x₀ hx₀
  obtain ⟨Λ, b, hΛ, h⟩ := affine_of_keeps_form_self hsymm hnd Metric.isOpen_ball
    (convex_ball x₀ ε).isPreconnected (hf.mono hball) fun x hx ↦ hkeep x (hball hx)
  exact ⟨Λ, b, hΛ, Filter.eventually_of_mem (Metric.ball_mem_nhds x₀ hε) fun y hy ↦ (h y hy).1⟩

end Rigid

end GravityInLean.Curved
