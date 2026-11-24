/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.OneMass.PatchBox
public import GravityInLean.OneMass.PatchMass
public import GravityInLean.OneMass.MassNewCoords
public import GravityInLean.Join.ResultB

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Result B with the mass: a table of functions has one mass near a point

Board item `task:checks-mass-table`. `resultB` (`Join/ResultB.lean`) again, inside coordinates,
with the mass tied down. A good table of functions that is empty, has one time direction and is
left unchanged by three fields that turn has, near any point of the region, one mass (usable
distance or not). Where the size of the spheres is a usable distance, the table is
Schwarzschild's table of that same mass, carried back along a change of coordinates.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Mass

open GravityInLean.Curved GravityInLean.Join

open Real Filter Topology Set

open scoped Manifold ContDiff

/-- **Result B with the mass.** There is a mass `m` that all points near `x₀` have. If the size of
the spheres is a usable distance at `x₀`, there is a change of coordinates `Ψ` as in `resultB`
that shows the table to be Schwarzschild's of this same mass `m`. -/
theorem tableMass (g' g'inv : Fin 4 → Fin 4 → Coords 4 → ℝ) (ξ' : Fin 3 → Fin 4 → Coords 4 → ℝ)
    (s' : Set (Coords 4)) (x₀ : Coords 4) (hreg : IsRegularTableOn g' g'inv s')
    (hturn : TurnsOn g' ξ' s') (hflat : ∀ x ∈ s', IsRicciFlatAt g' g'inv x)
    (htime : ∀ x ∈ s', HasOneTimeDirection fun v w : Coords 4 ↦ tableMeasure g' x v w)
    (hx₀ : x₀ ∈ s') :
    ∃ m : ℝ,
      (∀ᶠ x in 𝓝 x₀, MassAt (flatMeasure (tableMeasure g')) (fun i ↦ fieldOf (ξ' i)) x m) ∧
      (UsableDistanceAt (flatMeasure (tableMeasure g')) (fun i ↦ fieldOf (ξ' i)) x₀ →
        ∃ Ψ : OpenPartialHomeomorph (Coords 4) (Coords 4),
          x₀ ∈ Ψ.source ∧ Ψ.source ⊆ s' ∧ ContDiffOn ℝ ∞ Ψ Ψ.source ∧
          ContDiffOn ℝ ∞ Ψ.symm Ψ.target ∧
          ∀ x ∈ Ψ.source, (Ψ x ∈ outside m ∨ Ψ x ∈ inside m) ∧
            ∀ v w : Coords 4, tableMeasure g' x v w
              = tableMeasure (roundG (schwA m) (schwB m)) (Ψ x) (fderiv ℝ Ψ x v)
                (fderiv ℝ Ψ x w)) := by
  -- coordinates that fit the turns
  obtain ⟨Φ, R, W, y₀, hW, hy₀, hΦy₀, h2, h3, hΦs, hΦ, hRR, hRdet, hdet, hturnΦ⟩ :=
    turnsCoordinates g' g'inv ξ' s' hreg hturn x₀ hx₀
  refine ⟨massFn (clockOf (inNewCoords Φ g')) (rulerOf (inNewCoords Φ g'))
    (crossOf (inNewCoords Φ g')) (sizeOf (inNewCoords Φ g')) (y₀ 0) (y₀ 1), ?_, fun hu ↦ ?_⟩
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
  · -- with a usable distance: the proof of `resultB`, with the mass named
    have hu' : UsableDistanceAt (flatMeasure (tableMeasure (inNewCoords Φ g'))) turns y₀ :=
      usable_inNewCoords hreg hturn hW hy₀ hΦs hΦ hRR hdet hturnΦ (by rw [hΦy₀]; exact hu)
    -- Birkhoff's theorem on the patch, with the mass named
    obtain ⟨m, Θ, W', rfl, hW', hy₀', hW'W, hΘ, hΘdet, hΘB⟩ :=
      birkhoff_patch_mass (h := inNewCoords Φ g') (hinv := invT (inNewCoords Φ g')) hW hy₀ h2 h3
        (newTable_smooth hreg hW hΦs hΦ) (newTable_symm hreg hΦs)
        (isRoundAt_inNewCoords hreg hturn hW hΦs hΦ hdet hturnΦ)
        (newTable_inverse hreg hW hΦs hΦ hdet)
        (newTable_isRicciFlatAt hreg hW hΦs hΦ hdet hflat)
        (newTable_hasOneTimeDirection hW hΦs hΦ hdet htime)
        (newTable_pos_two_two hturn hΦs hdet hturnΦ) hu'
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

end GravityInLean.Mass
