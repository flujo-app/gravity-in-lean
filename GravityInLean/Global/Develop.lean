/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import Mathlib.Topology.FiberBundle.Basic
public import Mathlib.Topology.Homotopy.Lifting

import Mathlib.Tactic

/-!
# From maps near every point to one map on the whole region

Pure topology, no gravity. A region `S` without holes carries, near every point, a "map" into
a model (`IsMap D U`: the map `D` is good on the open set `U`). Two maps on a piece that is in
one piece differ by exactly one symmetry of the model (a member of `Γ`). Then there is one map
that is good on all of `S` (`exists_global_map`).

The proof glues the pairs (point, symmetry) over the domains of the maps near every point: over
the common part of two domains, the symmetry `v` over the first is the symmetry `σ` over the
second when `σ` after the second map is `v` after the first map. The result is a space that
covers `S`, with the symmetries as its sheets. A region without holes has a continuous choice of
a sheet over every point (the lifting theorem for covering maps), and that choice names the map.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Set Filter

open scoped Topology

namespace Develop

variable {S X : Type} [TopologicalSpace S]

/-- A symmetry of the model, as a point of a space in which every point stands alone. -/
@[ext]
structure Sym (Γ : Set (X → X)) where
  /-- The symmetry, as a map of the model to itself. -/
  val : X → X
  /-- It is one of the symmetries. -/
  mem : val ∈ Γ

instance (Γ : Set (X → X)) : TopologicalSpace (Sym Γ) := ⊥

instance (Γ : Set (X → X)) : DiscreteTopology (Sym Γ) := ⟨rfl⟩

/-- A map with a domain on which it is good. -/
structure LocalMap (IsMap : (S → X) → Set S → Prop) where
  /-- The map. -/
  map : S → X
  /-- Its domain. -/
  dom : Set S
  /-- The map is good on its domain. -/
  isMap : IsMap map dom

/-- What the argument needs to know about good maps and symmetries: domains are open, a good map
stays good on a smaller open set and after a symmetry, two good maps on a set in one piece differ
by a symmetry, and a symmetry is known from what it does after one good map. -/
structure Rules (IsMap : (S → X) → Set S → Prop) (Γ : Set (X → X)) : Prop where
  /-- Domains are open. -/
  isOpen : ∀ D U, IsMap D U → IsOpen U
  /-- A good map stays good on a smaller open set. -/
  mono : ∀ D U V, IsMap D U → IsOpen V → V ⊆ U → IsMap D V
  /-- A symmetry after a good map is a good map. -/
  act : ∀ σ ∈ Γ, ∀ D U, IsMap D U → IsMap (σ ∘ D) U
  /-- Two good maps on a set in one piece differ by a symmetry. -/
  uniq : ∀ D D' U, IsPreconnected U → IsMap D U → IsMap D' U →
    ∃ σ ∈ Γ, ∀ q ∈ U, D' q = σ (D q)
  /-- Two symmetries that do the same after a good map are the same. -/
  free : ∀ σ ∈ Γ, ∀ τ ∈ Γ, ∀ D U, IsMap D U → U.Nonempty →
    (∀ q ∈ U, σ (D q) = τ (D q)) → σ = τ

variable {IsMap : (S → X) → Set S → Prop} {Γ : Set (X → X)}

open Classical in
/-- **The change of symmetry from one map to another, at a point:** the symmetry `σ` with
`σ` after the second map equal to `v` after the first map near the point, if there is one (and
`v` itself if there is none, which does not happen on the common domain). -/
noncomputable def transition (i j : LocalMap IsMap) (x : S) (v : Sym Γ) : Sym Γ :=
  if h : ∃ σ : Sym Γ, ∀ᶠ y in 𝓝 x, σ.val (j.map y) = v.val (i.map y) then h.choose else v

/-- If some symmetry does the job of the change of symmetry, then the change of symmetry does
it. -/
theorem transition_spec {i j : LocalMap IsMap} {x : S} {v : Sym Γ}
    (h : ∃ σ : Sym Γ, ∀ᶠ y in 𝓝 x, σ.val (j.map y) = v.val (i.map y)) :
    ∀ᶠ y in 𝓝 x, (transition i j x v).val (j.map y) = v.val (i.map y) := by
  rw [transition, dite_eq_left h]
  exact h.choose_spec

/-- Two symmetries that do the same after a good map near a point of its domain are the
same. -/
theorem sym_eq_of_eventually (H : Rules IsMap Γ) {j : LocalMap IsMap} {x : S} (hx : x ∈ j.dom)
    {σ τ : Sym Γ} (h : ∀ᶠ y in 𝓝 x, σ.val (j.map y) = τ.val (j.map y)) : σ = τ := by
  obtain ⟨W, hW, hWo, hxW⟩ := eventually_nhds_iff.mp h
  have hm : IsMap j.map (W ∩ j.dom) :=
    H.mono _ _ _ j.isMap (hWo.inter (H.isOpen _ _ j.isMap)) inter_subset_right
  exact Sym.ext (H.free σ.val σ.mem τ.val τ.mem j.map _ hm ⟨x, hxW, hx⟩ fun q hq ↦ hW q hq.1)

/-- A symmetry that does the job of the change of symmetry is the change of symmetry. -/
theorem transition_eq (H : Rules IsMap Γ) {i j : LocalMap IsMap} {x : S} (hx : x ∈ j.dom)
    {v σ : Sym Γ} (h : ∀ᶠ y in 𝓝 x, σ.val (j.map y) = v.val (i.map y)) :
    transition i j x v = σ := by
  refine sym_eq_of_eventually H hx ?_
  filter_upwards [transition_spec ⟨σ, h⟩, h] with y h1 h2
  exact h1.trans h2.symm

/-- **On the common domain of two maps there is a change of symmetry, the same one on a whole
open set around the point.** -/
theorem exists_transition [LocallyConnectedSpace S] (H : Rules IsMap Γ) {i j : LocalMap IsMap}
    {x : S} (hxi : x ∈ i.dom) (hxj : x ∈ j.dom) (v : Sym Γ) :
    ∃ (σ : Sym Γ) (W : Set S), IsOpen W ∧ x ∈ W ∧ W ⊆ i.dom ∩ j.dom ∧
      ∀ y ∈ W, σ.val (j.map y) = v.val (i.map y) := by
  have hO : IsOpen (i.dom ∩ j.dom) := (H.isOpen _ _ i.isMap).inter (H.isOpen _ _ j.isMap)
  have hWo : IsOpen (connectedComponentIn (i.dom ∩ j.dom) x) := hO.connectedComponentIn
  have hWs : connectedComponentIn (i.dom ∩ j.dom) x ⊆ i.dom ∩ j.dom :=
    connectedComponentIn_subset _ _
  have hxW : x ∈ connectedComponentIn (i.dom ∩ j.dom) x := mem_connectedComponentIn ⟨hxi, hxj⟩
  have h1 : IsMap j.map (connectedComponentIn (i.dom ∩ j.dom) x) :=
    H.mono _ _ _ j.isMap hWo (hWs.trans inter_subset_right)
  have h2 : IsMap (v.val ∘ i.map) (connectedComponentIn (i.dom ∩ j.dom) x) :=
    H.act _ v.mem _ _ (H.mono _ _ _ i.isMap hWo (hWs.trans inter_subset_left))
  obtain ⟨σ, hσ, hσW⟩ := H.uniq _ _ _ isPreconnected_connectedComponentIn h1 h2
  exact ⟨⟨σ, hσ⟩, _, hWo, hxW, hWs, fun y hy ↦ (hσW y hy).symm⟩

/-- On the common domain of two maps the change of symmetry does its job: it, after the second
map, is `v` after the first map, near the point. -/
theorem transition_eventually [LocallyConnectedSpace S] (H : Rules IsMap Γ)
    {i j : LocalMap IsMap} {x : S} (hxi : x ∈ i.dom) (hxj : x ∈ j.dom) (v : Sym Γ) :
    ∀ᶠ y in 𝓝 x, (transition i j x v).val (j.map y) = v.val (i.map y) := by
  obtain ⟨σ, W, hWo, hxW, -, hσ⟩ := exists_transition H hxi hxj v
  exact transition_spec ⟨σ, eventually_of_mem (hWo.mem_nhds hxW) hσ⟩

/-- In a space in which every point stands alone, the points near a point are that point. -/
theorem eventually_eq_of_discrete {α : Type} [TopologicalSpace α] [DiscreteTopology α] (c : α) :
    ∀ᶠ v in 𝓝 c, v = c := by
  rw [nhds_discrete]
  exact eventually_pure.mpr rfl

/-- **The glued space of pairs (point, symmetry),** as the gluing data that the library turns
into a space over `S`: the pieces are the domains of the good maps, the fibre is the set of
symmetries, and the pieces are glued by the changes of symmetry. -/
noncomputable def core [LocallyConnectedSpace S] (H : Rules IsMap Γ)
    (hloc : ∀ q : S, ∃ U D, q ∈ U ∧ IsMap D U) : FiberBundleCore (LocalMap IsMap) S (Sym Γ) where
  baseSet i := i.dom
  isOpen_baseSet i := H.isOpen _ _ i.isMap
  indexAt x := ⟨(hloc x).choose_spec.choose, (hloc x).choose, (hloc x).choose_spec.choose_spec.2⟩
  mem_baseSet_at x := (hloc x).choose_spec.choose_spec.1
  coordChange := transition
  coordChange_self i x hx v := transition_eq H hx (Eventually.of_forall fun _ ↦ rfl)
  continuousOn_coordChange i j := by
    have hO : IsOpen ((i.dom ∩ j.dom) ×ˢ (univ : Set (Sym Γ))) :=
      ((H.isOpen _ _ i.isMap).inter (H.isOpen _ _ j.isMap)).prod isOpen_univ
    refine hO.continuousOn_iff.mpr ?_
    rintro ⟨x, v⟩ ⟨⟨hxi, hxj⟩, -⟩
    obtain ⟨σ, W, hWo, hxW, hWs, hσ⟩ := exists_transition H hxi hxj v
    have hev : ∀ᶠ p : S × Sym Γ in 𝓝 (x, v), transition i j p.1 p.2 = σ := by
      have hN : W ×ˢ ({v} : Set (Sym Γ)) ∈ 𝓝 (x, v) :=
        prod_mem_nhds (hWo.mem_nhds hxW) ((isOpen_discrete _).mem_nhds rfl)
      filter_upwards [hN] with p hp
      have hp2 : p.2 = v := hp.2
      rw [hp2]
      exact transition_eq H (hWs hp.1).2 (eventually_of_mem (hWo.mem_nhds hp.1) hσ)
    exact continuousAt_const.congr (hev.mono fun p hp ↦ hp.symm)
  coordChange_comp i j k x hx v := by
    obtain ⟨⟨hxi, hxj⟩, hxk⟩ := hx
    refine (transition_eq H hxk ?_).symm
    filter_upwards [transition_eventually H hxi hxj v,
      transition_eventually H hxj hxk (transition i j x v)] with y e1 e2
    exact e2.trans e1

end Develop

open Develop in
/-- **From maps near every point to one map on the whole region.** Let `S` be a region without
holes in which every point has small neighbourhoods in one piece. Let "good maps" on open sets
be given that stay good on smaller open sets, after a change that is not seen on the set, on
unions, and after a symmetry; let every point lie in the domain of a good map; let two good maps
on a set in one piece differ by a symmetry, and let a symmetry be known from what it does after
one good map. Then there is one map that is good on all of `S`. -/
theorem exists_global_map {S X : Type} [TopologicalSpace S] [SimplyConnectedSpace S]
    [LocallyPathConnectedSpace S]
    (IsMap : (S → X) → Set S → Prop) (Γ : Set (X → X))
    (hopen : ∀ D U, IsMap D U → IsOpen U)
    (hmono : ∀ D U V, IsMap D U → IsOpen V → V ⊆ U → IsMap D V)
    (hcongr : ∀ D D' U, IsMap D U → (∀ q ∈ U, D' q = D q) → IsMap D' U)
    (hglue : ∀ (D : S → X) (𝒰 : Set (Set S)), (∀ U ∈ 𝒰, IsMap D U) → IsMap D (⋃₀ 𝒰))
    (hloc : ∀ q : S, ∃ U D, q ∈ U ∧ IsMap D U)
    (hact : ∀ σ ∈ Γ, ∀ D U, IsMap D U → IsMap (σ ∘ D) U)
    (huniq : ∀ D D' U, IsPreconnected U → IsMap D U → IsMap D' U →
      ∃ σ ∈ Γ, ∀ q ∈ U, D' q = σ (D q))
    (hfree : ∀ σ ∈ Γ, ∀ τ ∈ Γ, ∀ D U, IsMap D U → U.Nonempty →
      (∀ q ∈ U, σ (D q) = τ (D q)) → σ = τ) :
    ∃ D : S → X, IsMap D univ := by
  have H : Rules IsMap Γ := ⟨hopen, hmono, hact, huniq, hfree⟩
  -- the glued space of pairs (point, symmetry) covers `S`
  let Z : FiberBundleCore (LocalMap IsMap) S (Sym Γ) := core H hloc
  have cov : IsCoveringMap (Bundle.TotalSpace.proj : Z.TotalSpace → S) :=
    FiberBundle.isCoveringMap (F := Sym Γ) (E := Z.Fiber)
  -- a point to start from, and a symmetry over it
  obtain ⟨a₀⟩ : Nonempty S := inferInstance
  obtain ⟨v₀⟩ : Nonempty (Sym Γ) := by
    obtain ⟨U, D, -, hD⟩ := hloc a₀
    have hm : IsMap D (connectedComponentIn U a₀) :=
      hmono D U _ hD (hopen _ _ hD).connectedComponentIn (connectedComponentIn_subset U a₀)
    obtain ⟨σ, hσ, -⟩ := huniq D D _ isPreconnected_connectedComponentIn hm hm
    exact ⟨⟨σ, hσ⟩⟩
  -- a continuous choice of a symmetry over every point
  obtain ⟨F, ⟨-, hF⟩, -⟩ :=
    cov.existsUnique_continuousMap_lifts (ContinuousMap.id S) a₀ ⟨a₀, v₀⟩ rfl
  have hF' : ∀ q : S, (F q).1 = q := fun q ↦ congrFun hF q
  -- the map: at each point, the chosen symmetry after the map near that point
  let D : S → X := fun q ↦ Sym.val (F q).2 ((Z.indexAt (F q).1).map (F q).1)
  -- near every point it is one symmetry after one good map
  have hlocal : ∀ q₀ : S, ∃ W : Set S, q₀ ∈ W ∧ IsMap D W := by
    intro q₀
    have hq₀ : q₀ ∈ (Z.indexAt q₀).dom := Z.mem_baseSet_at q₀
    generalize Z.indexAt q₀ = i at hq₀
    have hsrc : F q₀ ∈ (Z.localTriv i).source := by
      change (F q₀).1 ∈ i.dom
      rw [hF']
      exact hq₀
    have hc0 : ContinuousAt (Z.localTriv i) (F q₀) :=
      (Z.localTriv i).toOpenPartialHomeomorph.continuousAt hsrc
    have hc : ContinuousAt (fun q ↦ ((Z.localTriv i) (F q)).2) q₀ :=
      (ContinuousAt.comp (g := Z.localTriv i) (f := F) (x := q₀) hc0
        F.continuous.continuousAt).snd
    obtain ⟨σ, hσ⟩ : ∃ σ : Sym Γ, ((Z.localTriv i) (F q₀)).2 = σ := ⟨_, rfl⟩
    have hN : ∀ᶠ q in 𝓝 q₀, ((Z.localTriv i) (F q)).2 = σ := by
      have := Tendsto.eventually hc (eventually_eq_of_discrete (((Z.localTriv i) (F q₀)).2))
      rw [hσ] at this
      exact this
    obtain ⟨W, hW, hWo, hqW⟩ :=
      eventually_nhds_iff.mp (hN.and ((hopen _ _ i.isMap).eventually_mem hq₀))
    refine ⟨W, hqW, hcongr (σ.val ∘ i.map) D W
      (hact _ σ.mem _ _ (hmono _ _ _ i.isMap hWo fun q hq ↦ (hW q hq).2)) fun q hq ↦ ?_⟩
    have h1 : transition (Z.indexAt (F q).1) i (F q).1 (F q).2 = σ := (hW q hq).1
    have hxa : (F q).1 ∈ (Z.indexAt (F q).1).dom := Z.mem_baseSet_at _
    have hxi : (F q).1 ∈ i.dom := by
      rw [hF']
      exact (hW q hq).2
    have h2 : (transition (Z.indexAt (F q).1) i (F q).1 (F q).2).val (i.map (F q).1) = D q :=
      (transition_eventually H hxa hxi (F q).2).self_of_nhds
    exact (h2.symm.trans (congrArg (fun τ : Sym Γ ↦ τ.val (i.map (F q).1)) h1)).trans
      (congrArg (fun y ↦ σ.val (i.map y)) (hF' q))
  -- so it is good on the union of open sets around every point, which is everything
  have hall : ⋃₀ {U : Set S | IsMap D U} = univ :=
    eq_univ_of_forall fun q ↦ by
      obtain ⟨W, hqW, hW⟩ := hlocal q
      exact mem_sUnion.mpr ⟨W, hW, hqW⟩
  refine ⟨D, ?_⟩
  rw [← hall]
  exact hglue D _ fun U hU ↦ hU

end GravityInLean.Curved
