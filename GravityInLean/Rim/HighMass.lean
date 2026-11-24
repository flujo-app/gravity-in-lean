/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Rim.Patch
public import GravityInLean.OneMass.Local

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# A point of positive mass has a chart in which the space-time is Kruskal's

Board item `task:rim-high-mass`. The counterparts of `tableMass` (`OneMass/TableMass.lean`) and
`localMass` (`OneMass/Local.lean`) for a positive mass, with no usable distance assumed.

* `tableKruskal`: a good table with three fields that turn, empty, with one time direction, has
  near every point one mass; if that mass is positive there is a change of coordinates that
  shows the table to be Kruskal's of that mass. From `kruskal_patch` (`Patch.lean`), as
  `tableMass` is from `birkhoff_patch_mass`.
* `kruskalNear_of_massAt_pos`: on a curved space: a point of the region that has the positive
  mass `m` has a chart around it in which the length measure is Kruskal's of mass `m`. From
  `resultA_mass` and `tableKruskal`, as `localMass` is from `resultA_mass` and `tableMass`; the
  mass of the table is the mass of the point because a point has at most one mass
  (`massAt_unique`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Rim

open GravityInLean.Curved GravityInLean.Join GravityInLean.Mass

open Real Filter Topology Set

open scoped Manifold ContDiff

/-- **A table with its mass, and Kruskal's chart if the mass is positive.** -/
theorem tableKruskal (g' g'inv : Fin 4 → Fin 4 → Coords 4 → ℝ) (ξ' : Fin 3 → Fin 4 → Coords 4 → ℝ)
    (s' : Set (Coords 4)) (x₀ : Coords 4) (hreg : IsRegularTableOn g' g'inv s')
    (hturn : TurnsOn g' ξ' s') (hflat : ∀ x ∈ s', IsRicciFlatAt g' g'inv x)
    (htime : ∀ x ∈ s', HasOneTimeDirection fun v w : Coords 4 ↦ tableMeasure g' x v w)
    (hx₀ : x₀ ∈ s') :
    ∃ m : ℝ,
      (∀ᶠ x in 𝓝 x₀, MassAt (flatMeasure (tableMeasure g')) (fun i ↦ fieldOf (ξ' i)) x m) ∧
      (0 < m →
        ∃ Ψ : OpenPartialHomeomorph (Coords 4) (Coords 4),
          x₀ ∈ Ψ.source ∧ Ψ.source ⊆ s' ∧ ContDiffOn ℝ ∞ Ψ Ψ.source ∧
          ContDiffOn ℝ ∞ Ψ.symm Ψ.target ∧
          ∀ x ∈ Ψ.source, Ψ x ∈ kruskalRegion ∧
            ∀ v w : Coords 4, tableMeasure g' x v w
              = tableMeasure (kruskalG m) (Ψ x) (fderiv ℝ Ψ x v) (fderiv ℝ Ψ x w)) := by
  -- coordinates that fit the turns
  obtain ⟨Φ, R, W, y₀, hW, hy₀, hΦy₀, h2, h3, hΦs, hΦ, hRR, hRdet, hdet, hturnΦ⟩ :=
    turnsCoordinates g' g'inv ξ' s' hreg hturn x₀ hx₀
  refine ⟨massFn (clockOf (inNewCoords Φ g')) (rulerOf (inNewCoords Φ g'))
    (crossOf (inNewCoords Φ g')) (sizeOf (inNewCoords Φ g')) (y₀ 0) (y₀ 1), ?_, fun hmpos ↦ ?_⟩
  · -- the mass near `y₀`, for the new table and the standard turns
    have hbox := patch_box_mass (h := inNewCoords Φ g') (hinv := invT (inNewCoords Φ g')) hW hy₀
      h2 h3 (newTable_smooth hreg hW hΦs hΦ) (newTable_symm hreg hΦs)
      (isRoundAt_inNewCoords hreg hturn hW hΦs hΦ hdet hturnΦ)
      (newTable_inverse hreg hW hΦs hΦ hdet)
      (newTable_isRicciFlatAt hreg hW hΦs hΦ hdet hflat)
      (newTable_hasOneTimeDirection hW hΦs hΦ hdet htime)
      (newTable_pos_two_two hturn hΦs hdet hturnΦ)
    -- the new coordinates as a map that can be undone, near `y₀`
    obtain ⟨e₀, hy₀0, he₀W, he₀Φ, -, -⟩ :=
      exists_localDiffeo_of_det hW hΦ hy₀ (hdet y₀ hy₀).2
    have hx₀e : x₀ = e₀ y₀ := by rw [he₀Φ, hΦy₀]
    have hx₀t : x₀ ∈ e₀.target := by
      rw [hx₀e]
      exact e₀.map_source hy₀0
    have hback : e₀.symm x₀ = y₀ := by rw [hx₀e, e₀.left_inv hy₀0]
    -- a point near `x₀` comes from a point near `y₀`
    have htend : Tendsto e₀.symm (𝓝 x₀) (𝓝 y₀) := by
      have hc : ContinuousAt e₀.symm x₀ := e₀.continuousAt_symm hx₀t
      rwa [ContinuousAt, hback] at hc
    filter_upwards [htend.eventually hbox, e₀.open_target.eventually_mem hx₀t] with x hx hxt
    have hyW : e₀.symm x ∈ W := he₀W (e₀.map_target hxt)
    have hΦx : Φ (e₀.symm x) = x := by
      rw [← he₀Φ]
      exact e₀.right_inv hxt
    have hm := massAt_of_inNewCoords hreg hturn hW hyW hΦs hΦ hRR hdet hturnΦ hx
    rwa [hΦx] at hm
  · -- with a positive mass: the table is Kruskal's on a patch around `y₀`
    obtain ⟨Θ, W', hW', hy₀', hW'W, hΘ, hΘdet, hΘB⟩ :=
      kruskal_patch (h := inNewCoords Φ g') (hinv := invT (inNewCoords Φ g')) hW hy₀ h2 h3
        (newTable_smooth hreg hW hΦs hΦ) (newTable_symm hreg hΦs)
        (isRoundAt_inNewCoords hreg hturn hW hΦs hΦ hdet hturnΦ)
        (newTable_inverse hreg hW hΦs hΦ hdet)
        (newTable_isRicciFlatAt hreg hW hΦs hΦ hdet hflat)
        (newTable_hasOneTimeDirection hW hΦs hΦ hdet htime)
        (newTable_pos_two_two hturn hΦs hdet hturnΦ) rfl hmpos
    -- both changes of coordinates, as maps that can be undone, near `y₀`
    obtain ⟨e₁, hy₀1, he₁W, he₁Φ, -, he₁'⟩ :=
      exists_localDiffeo_of_det hW' (hΦ.mono hW'W) hy₀' (hdet y₀ hy₀).2
    obtain ⟨e₂, hy₀2, -, he₂Θ, he₂, he₂'⟩ :=
      exists_localDiffeo_of_det hW' hΘ hy₀' (hΘdet y₀ hy₀')
    have he₁ : ContDiffOn ℝ ∞ e₁ e₁.source := by
      have e : (e₁ : Coords 4 → Coords 4) = Φ := funext he₁Φ
      rw [e]
      exact hΦ.mono fun y hy ↦ hW'W (he₁W hy)
    have hsrc : ∀ x ∈ (e₁.symm.trans e₂).source, x ∈ e₁.target ∧ e₁.symm x ∈ e₂.source ∧
        e₁.symm x ∈ W' ∧ Φ (e₁.symm x) = x := by
      intro x hx
      rw [OpenPartialHomeomorph.trans_source] at hx
      have h1 : x ∈ e₁.target := hx.1
      refine ⟨h1, hx.2, he₁W (e₁.map_target h1), ?_⟩
      rw [← he₁Φ]
      exact e₁.right_inv h1
    have hx₀e : x₀ = e₁ y₀ := by rw [he₁Φ, hΦy₀]
    refine ⟨e₁.symm.trans e₂, ?_, fun x hx ↦ ?_, ?_, ?_, fun x hx ↦ ?_⟩
    · rw [OpenPartialHomeomorph.trans_source]
      refine ⟨?_, ?_⟩
      · rw [hx₀e]
        exact e₁.map_source hy₀1
      · change e₁.symm x₀ ∈ e₂.source
        rw [hx₀e, e₁.left_inv hy₀1]
        exact hy₀2
    · obtain ⟨-, -, hyW', hΦy⟩ := hsrc x hx
      rw [← hΦy]
      exact hΦs _ (hW'W hyW')
    · rw [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source]
      exact he₂.comp (he₁'.mono inter_subset_left) inter_subset_right
    · rw [OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.trans_target]
      exact he₁.comp (he₂'.mono inter_subset_left) inter_subset_right
    · obtain ⟨hxt, -, hyW', -⟩ := hsrc x hx
      have hΦd : DifferentiableAt ℝ Φ (e₁.symm x) :=
        (hΦ.contDiffAt (hW.mem_nhds (hW'W hyW'))).differentiableAt (by simp)
      have hΘd : DifferentiableAt ℝ Θ (e₁.symm x) :=
        (hΘ.contDiffAt (hW'.mem_nhds hyW')).differentiableAt (by simp)
      refine ⟨?_, fun v w ↦ ?_⟩
      · have hΨx : (e₁.symm.trans e₂) x = Θ (e₁.symm x) := he₂Θ _
        rw [hΨx]
        exact (hΘB _ hyW').1
      · exact tableMeasure_symm_trans he₁Φ he₂Θ he₁' hxt hΦd hΘd (hΘB _ hyW').2 v w

/-- **A point of positive mass is on Kruskal's space-time.** In a space-time that is empty and
looks the same from every side, a point of the region that has the positive mass `m` has a chart
around it in which the length measure is Kruskal's of mass `m`. Nothing is asked of the size of
the spheres at the point: it may be on the rim. -/
theorem kruskalNear_of_massAt_pos (M : Type) [TopologicalSpace M] [ChartedSpace (Coords 4) M]
    [IsManifold 𝓘(ℝ, Coords 4) ∞ M]
    (g : LengthMeasure 𝓘(ℝ, Coords 4) M) (ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M) (s : Set M)
    (hs : IsOpen s) (hg : IsSpaceTimeOn g s) (he : Curved.IsEmptyOn g s) (hr : IsRoundOn g ξ s)
    (p : M) (hp : p ∈ s) {m : ℝ} (hm : 0 < m) (hmass : MassAt g ξ p m) :
    IsKruskalNear m g p := by
  obtain ⟨c, g', g'inv, ξ', hc, hpc, hreg, hturn, hflat, htime, -, hback, hform⟩ :=
    resultA_mass M g ξ s hs hg he hr p hp
  obtain ⟨m', hm', hB⟩ :=
    tableKruskal g' g'inv ξ' c.target (c p) hreg hturn hflat htime (c.map_source hpc)
  -- The mass of the table at the image of `p` is the mass of `p`: a point has only one.
  have hnd : Nondegenerate fun v w : TangentSpace 𝓘(ℝ, Coords 4) p ↦ g p v w :=
    (hg.oneTime p hp).nondegenerate (hg.symm p hp)
  have e : m' = m := massAt_unique hnd (hback p hpc m' hm'.self_of_nhds) hmass
  rw [e] at hB
  -- The chart of the goal: the chart of the curved space, then the change of coordinates.
  obtain ⟨Ψ, hx₀, -, hΨ, hΨ', hB⟩ := hB hm
  refine ⟨c.trans Ψ, trans_mem_maximalAtlas hc hΨ hΨ', ?_, fun q hq ↦ ?_⟩
  · rw [OpenPartialHomeomorph.trans_source]
    exact ⟨hpc, hx₀⟩
  · have hq' := hq
    rw [OpenPartialHomeomorph.trans_source] at hq'
    obtain ⟨hqc, hqΨ⟩ := hq'
    have hq2 : c q ∈ Ψ.source := hqΨ
    obtain ⟨hreg', hlen⟩ := hB (c q) hq2
    refine ⟨hreg', fun v w ↦ ?_⟩
    rw [hform q hqc v w, hlen, mfderiv_trans_apply hc hΨ hq v,
      mfderiv_trans_apply hc hΨ hq w]
    rfl

end GravityInLean.Rim
