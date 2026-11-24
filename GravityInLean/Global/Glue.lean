/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.Develop
public import GravityInLean.Global.LocalMaps
public import GravityInLean.Global.TwoPieces
public import GravityInLean.Global.SchwSym
public import GravityInLean.Global.UniqueKruskal
public import GravityInLean.Global.UniqueSchw
public import GravityInLean.Rim.Goal

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# The length-keeping maps near every point, glued to one map on a region without holes

Around every point of a round, empty space-time there is a length-keeping map into the model
(`LocalMaps.lean`); two of them on a piece that is in one piece differ by one symmetry of the
model. On a region without holes the gluing theorem of `Develop.lean` makes one map of them:
Birkhoff's theorem for a whole space-time.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

/-! ## The gluing theorem, for maps on a region of a bigger space -/

/-- **From maps near every point of a region to one map on the region.** The gluing theorem of
`Develop.lean`, for an open region `s` without holes of a space `M`, and "good maps" that are
maps of all of `M`, good on open sets. Uniqueness up to a symmetry is only asked on sets inside
the region. -/
theorem exists_global_map_on {M X : Type} [TopologicalSpace M] {s : Set M} (hs : IsOpen s)
    [SimplyConnectedSpace s] [LocallyPathConnectedSpace s] (x₀ : X)
    (P : (M → X) → Set M → Prop) (Γ : Set (X → X))
    (hopen : ∀ D U, P D U → IsOpen U)
    (hmono : ∀ D U V, P D U → IsOpen V → V ⊆ U → P D V)
    (hcongr : ∀ D D' U, P D U → (∀ q ∈ U, D' q = D q) → P D' U)
    (hglue : ∀ (D : M → X) (𝒰 : Set (Set M)), (∀ U ∈ 𝒰, P D U) → P D (⋃₀ 𝒰))
    (hloc : ∀ q ∈ s, ∃ U D, q ∈ U ∧ P D U)
    (hact : ∀ σ ∈ Γ, ∀ D U, P D U → P (σ ∘ D) U)
    (huniq : ∀ D D' U, U ⊆ s → IsPreconnected U → P D U → P D' U →
      ∃ σ ∈ Γ, ∀ q ∈ U, D' q = σ (D q))
    (hfree : ∀ σ ∈ Γ, ∀ τ ∈ Γ, ∀ D U, U ⊆ s → P D U → U.Nonempty →
      (∀ q ∈ U, σ (D q) = τ (D q)) → σ = τ) :
    ∃ D : M → X, P D s := by
  -- a map on the region, carried on to the whole space
  obtain ⟨ext, hext⟩ : ∃ ext : (s → X) → M → X, ∀ (D : s → X) (q : s), ext D q = D q :=
    ⟨fun D ↦ Function.extend Subtype.val D fun _ ↦ x₀,
      fun D q ↦ Subtype.val_injective.extend_apply D _ q⟩
  suffices h : ∃ D : s → X, P (ext D) (Subtype.val '' univ) by
    obtain ⟨D, hD⟩ := h
    rw [Subtype.coe_image_univ] at hD
    exact ⟨ext D, hD⟩
  refine exists_global_map (S := s) (fun D U ↦ P (ext D) (Subtype.val '' U)) Γ
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro D U h
    rw [← preimage_image_eq U Subtype.val_injective]
    exact (hopen _ _ h).preimage continuous_subtype_val
  · intro D U V h hV hVU
    exact hmono _ _ _ h (hs.isOpenMap_subtype_val V hV) (image_mono hVU)
  · intro D D' U h heq
    refine hcongr _ _ _ h ?_
    rintro _ ⟨q, hq, rfl⟩
    rw [hext, hext]
    exact heq q hq
  · intro D 𝒰 h
    rw [image_sUnion]
    refine hglue _ _ ?_
    rintro _ ⟨U, hU, rfl⟩
    exact h U hU
  · intro q
    obtain ⟨U, D, hqU, hD⟩ := hloc q q.2
    refine ⟨Subtype.val ⁻¹' U, fun q ↦ D q, hqU, ?_⟩
    change P (ext fun q : s ↦ D q) (Subtype.val '' (Subtype.val ⁻¹' U))
    rw [Subtype.image_preimage_coe]
    refine hcongr _ _ _ (hmono _ _ _ hD (hs.inter (hopen _ _ hD)) inter_subset_right) ?_
    rintro x ⟨hx, -⟩
    exact hext (fun q : s ↦ D q) ⟨x, hx⟩
  · intro σ hσ D U h
    refine hcongr _ _ _ (hact σ hσ _ _ h) ?_
    rintro _ ⟨q, hq, rfl⟩
    simp only [Function.comp_apply, hext]
  · intro D D' U hU h h'
    obtain ⟨σ, hσ, hσU⟩ := huniq _ _ _ (Subtype.coe_image_subset s U)
      (hU.image _ continuous_subtype_val.continuousOn) h h'
    refine ⟨σ, hσ, fun q hq ↦ ?_⟩
    have h1 := hσU q ⟨q, hq, rfl⟩
    rw [hext, hext] at h1
    exact h1
  · intro σ hσ τ hτ D U h hne heq
    refine hfree σ hσ τ hτ _ _ (Subtype.coe_image_subset s U) h (hne.image _) ?_
    rintro _ ⟨q, hq, rfl⟩
    rw [hext]
    exact heq q hq

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  [IsManifold 𝓘(ℝ, Coords 4) ∞ M] {m : ℝ} {g : LengthMeasure 𝓘(ℝ, Coords 4) M} {s : Set M}

/-! ## Kruskal's -/

/-- A length-keeping map into Kruskal's is one on every smaller open region. -/
theorem IsKruskalMapOn.mono {D : M → Coords 5} {t : Set M} (hD : IsKruskalMapOn m g D s)
    (ht : IsOpen t) (hts : t ⊆ s) : IsKruskalMapOn m g D t :=
  ⟨ht, hD.2.1.mono hts, fun q hq ↦ hD.2.2 q (hts hq)⟩

/-- A map that is length-keeping into Kruskal's on every region of a family is so on all of
them together. -/
theorem IsKruskalMapOn.sUnion {D : M → Coords 5} {𝒰 : Set (Set M)}
    (h : ∀ U ∈ 𝒰, IsKruskalMapOn m g D U) : IsKruskalMapOn m g D (⋃₀ 𝒰) := by
  refine ⟨isOpen_sUnion fun U hU ↦ (h U hU).1, ?_, ?_⟩
  · rintro q ⟨U, hU, hq⟩
    exact ((h U hU).2.1.contMDiffAt ((h U hU).1.mem_nhds hq)).contMDiffWithinAt
  · rintro q ⟨U, hU, hq⟩
    exact (h U hU).2.2 q hq

/-- The symmetries of Kruskal's whole space-time, as a set of maps. -/
def kruskalSyms : Set (Coords 5 → Coords 5) :=
  {σ | ∃ (L : Matrix (Fin 2) (Fin 2) ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ),
    L.transpose * lightSign2 * L = lightSign2 ∧ R.transpose * R = 1 ∧ σ = kruskalSym L R}

/-- **Kruskal's around every point of a region without holes gives one length-keeping map of
the whole region into Kruskal's whole space-time.** -/
theorem exists_kruskalMap_of_simplyConnected (hm : 0 < m) (hs : IsOpen s)
    (hsc : IsSimplyConnected s) (hg : IsSpaceTimeOn g s) (hloc : ∀ p ∈ s, IsKruskalNear m g p) :
    ∃ D : M → Coords 5, IsKruskalMapOn m g D s := by
  have : SimplyConnectedSpace s := hsc
  have : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace (Coords 4) M
  have : LocallyPathConnectedSpace s := hs.locallyPathConnectedSpace
  refine exists_global_map_on hs (0 : Coords 5) (fun D U ↦ IsKruskalMapOn m g D U) kruskalSyms
    (fun D U h ↦ h.1) (fun D U V h hV hVU ↦ h.mono hV hVU) (fun D D' U h heq ↦ h.congr heq)
    (fun D 𝒰 h ↦ IsKruskalMapOn.sUnion h) (fun q hq ↦ (hloc q hq).exists_map) ?_ ?_ ?_
  · rintro σ ⟨L, R, hL, hR, rfl⟩ D U h
    exact h.sym hL hR
  · intro D D' U hU hpre h h'
    obtain ⟨L, R, hL, hR, hLR⟩ := unique_kruskal hpre (isSpaceTimeOn_sub hg hU) hm D D' h h'
    exact ⟨kruskalSym L R, ⟨L, R, hL, hR, rfl⟩, hLR⟩
  · rintro σ ⟨L, R, hL, hR, rfl⟩ τ ⟨L', R', hL', hR', rfl⟩ D U hU h ⟨q, hq⟩ heq
    obtain ⟨rfl, rfl⟩ := h.sym_unique (isSpaceTimeOn_sub hg hU) hq
      (Filter.eventually_of_mem (h.1.mem_nhds hq) heq)
    rfl

/-! ## Schwarzschild's whole space-time, for a mass that is zero or negative -/

/-- A map that agrees with a length-keeping map into Schwarzschild's whole space-time on the
region is length-keeping there. -/
theorem IsSchwarzschildMapOn.congr {D D' : M → Coords 4} (hD : IsSchwarzschildMapOn m g D s)
    (h : ∀ q ∈ s, D' q = D q) : IsSchwarzschildMapOn m g D' s := by
  obtain ⟨hs, hsm, hpt⟩ := hD
  refine ⟨hs, hsm.congr h, fun q hq ↦ ⟨?_, fun v w ↦ ?_⟩⟩
  · rw [h q hq]
    exact (hpt q hq).1
  · have hev : D' =ᶠ[𝓝 q] D := Filter.eventuallyEq_of_mem (hs.mem_nhds hq) fun x hx ↦ h x hx
    have hd : ∀ u : TangentSpace 𝓘(ℝ, Coords 4) q,
        (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D' q u : Coords 4)
          = mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D q u :=
      fun u ↦ DFunLike.congr_fun hev.mfderiv_eq u
    have key : ∀ p p' a a' b b' : Coords 4, p = p' → a = a' → b = b' →
        tableMeasure (schwSpaceG m) p a b = tableMeasure (schwSpaceG m) p' a' b' := by
      rintro p _ a _ b _ rfl rfl rfl
      rfl
    exact ((hpt q hq).2 v w).trans (key _ _ _ _ _ _ (h q hq).symm (hd v).symm (hd w).symm)

/-- A length-keeping map into Schwarzschild's whole space-time is one on every smaller open
region. -/
theorem IsSchwarzschildMapOn.mono {D : M → Coords 4} {t : Set M}
    (hD : IsSchwarzschildMapOn m g D s) (ht : IsOpen t) (hts : t ⊆ s) :
    IsSchwarzschildMapOn m g D t :=
  ⟨ht, hD.2.1.mono hts, fun q hq ↦ hD.2.2 q (hts hq)⟩

/-- A map that is length-keeping into Schwarzschild's whole space-time on every region of a
family is so on all of them together. -/
theorem IsSchwarzschildMapOn.sUnion {D : M → Coords 4} {𝒰 : Set (Set M)}
    (h : ∀ U ∈ 𝒰, IsSchwarzschildMapOn m g D U) : IsSchwarzschildMapOn m g D (⋃₀ 𝒰) := by
  refine ⟨isOpen_sUnion fun U hU ↦ (h U hU).1, ?_, ?_⟩
  · rintro q ⟨U, hU, hq⟩
    exact ((h U hU).2.1.contMDiffAt ((h U hU).1.mem_nhds hq)).contMDiffWithinAt
  · rintro q ⟨U, hU, hq⟩
    exact (h U hU).2.2 q hq

/-- The symmetries of Schwarzschild's whole space-time of negative mass, as a set of maps. -/
def schwSyms : Set (Coords 4 → Coords 4) :=
  {σ | ∃ (ε c : ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ),
    (ε = 1 ∨ ε = -1) ∧ R.transpose * R = 1 ∧ σ = schwSym ε c R}

/-- **Schwarzschild's of a negative mass around every point of a region without holes gives one
length-keeping map of the whole region into Schwarzschild's whole space-time.** -/
theorem exists_schwMap_of_simplyConnected_neg (hm : m < 0) (hs : IsOpen s)
    (hsc : IsSimplyConnected s) (hg : IsSpaceTimeOn g s)
    (hloc : ∀ p ∈ s, IsSchwarzschildWith m g p) :
    ∃ D : M → Coords 4, IsSchwarzschildMapOn m g D s := by
  have : SimplyConnectedSpace s := hsc
  have : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace (Coords 4) M
  have : LocallyPathConnectedSpace s := hs.locallyPathConnectedSpace
  refine exists_global_map_on hs (0 : Coords 4) (fun D U ↦ IsSchwarzschildMapOn m g D U) schwSyms
    (fun D U h ↦ h.1) (fun D U V h hV hVU ↦ h.mono hV hVU) (fun D D' U h heq ↦ h.congr heq)
    (fun D 𝒰 h ↦ IsSchwarzschildMapOn.sUnion h)
    (fun q hq ↦ (hloc q hq).exists_map hm.le) ?_ ?_ ?_
  · rintro σ ⟨ε, c, R, hε, hR, rfl⟩ D U h
    exact h.sym hε hR
  · intro D D' U hU hpre h h'
    obtain ⟨ε, c, R, hε, hR, hεR⟩ := unique_schw hpre (isSpaceTimeOn_sub hg hU) hm D D' h h'
    exact ⟨schwSym ε c R, ⟨ε, c, R, hε, hR, rfl⟩, hεR⟩
  · rintro σ ⟨ε, c, R, hε, hR, rfl⟩ τ ⟨ε', c', R', hε', hR', rfl⟩ D U hU h ⟨q, hq⟩ heq
    obtain ⟨rfl, rfl, rfl⟩ := h.sym_unique hm (isSpaceTimeOn_sub hg hU) hq
      (Filter.eventually_of_mem (h.1.mem_nhds hq) heq)
    rfl

end GravityInLean.Curved
