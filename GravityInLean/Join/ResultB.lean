/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Curved.Goal
public import GravityInLean.Goals.Turns
public import GravityInLean.Turns.TurnsCoordinates
public import GravityInLean.Join.Atlas
public import GravityInLean.Join.Mix
public import GravityInLean.Join.NewTable
public import GravityInLean.Join.Patch
public import GravityInLean.Join.UsableNew

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Result B: Birkhoff's theorem for a table of functions, in any coordinates

Board item `task:join-result-b`. Inside coordinates, no curved space. A good table of functions
that is empty, has one time direction and is left unchanged by three fields that turn is, near
any point where the size of the spheres is a usable distance, Schwarzschild's table carried back
along a change of coordinates `Ψ` that is smooth with a smooth inverse.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Join

open GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

/-- Two tables with the same entries at a point measure steps at that point the same way. -/
theorem tableMeasure_congr {h k : Fin 4 → Fin 4 → Coords 4 → ℝ} {y : Coords 4}
    (e : ∀ μ ν, h μ ν y = k μ ν y) : tableMeasure h y = tableMeasure k y := by
  have e' : (fun a b ↦ h a b y) = fun a b ↦ k a b y := funext fun a ↦ funext fun b ↦ e a b
  change formOf (fun a b ↦ h a b y) = formOf (fun a b ↦ k a b y)
  rw [e']

/-- **Two changes of coordinates, one after the other.** Take a table `g'` and a table `S`,
and two changes of coordinates `e₁` (from `Φ`) and `e₂` (from `Θ`) out of the same patch, such
that `g'` written in the coordinates of `Φ` has, at each point of the patch, the entries of `S`
written in the coordinates of `Θ`. Then `g'` gives two steps at `x` the length that `S` gives,
at the point where `e₁` backwards and then `e₂` send `x`, to the two steps as that map sees
them. -/
theorem tableMeasure_symm_trans {g' S : Fin 4 → Fin 4 → Coords 4 → ℝ}
    {Φ Θ : Coords 4 → Coords 4} {e₁ e₂ : OpenPartialHomeomorph (Coords 4) (Coords 4)}
    (he₁Φ : ∀ y, e₁ y = Φ y) (he₂Θ : ∀ y, e₂ y = Θ y)
    (he₁' : ContDiffOn ℝ ∞ e₁.symm e₁.target) {x : Coords 4} (hxt : x ∈ e₁.target)
    (hΦd : DifferentiableAt ℝ Φ (e₁.symm x)) (hΘd : DifferentiableAt ℝ Θ (e₁.symm x))
    (hent : ∀ μ ν, inNewCoords Φ g' μ ν (e₁.symm x) = inNewCoords Θ S μ ν (e₁.symm x))
    (v w : Coords 4) :
    tableMeasure g' x v w
      = tableMeasure S ((e₁.symm.trans e₂) x) (fderiv ℝ (e₁.symm.trans e₂) x v)
        (fderiv ℝ (e₁.symm.trans e₂) x w) := by
  have hΦy : Φ (e₁.symm x) = x := by
    rw [← he₁Φ]
    exact e₁.right_inv hxt
  have hsd : DifferentiableAt ℝ e₁.symm x :=
    (he₁'.contDiffAt (e₁.open_target.mem_nhds hxt)).differentiableAt (by simp)
  have hΨfun : (e₁.symm.trans e₂ : Coords 4 → Coords 4) = Θ ∘ e₁.symm :=
    funext fun z ↦ he₂Θ _
  have hΨx : (e₁.symm.trans e₂) x = Θ (e₁.symm x) := he₂Θ _
  -- chain rule for the combined map
  have hD : fderiv ℝ (e₁.symm.trans e₂) x = (fderiv ℝ Θ (e₁.symm x)).comp (fderiv ℝ e₁.symm x) := by
    rw [hΨfun]
    exact fderiv_comp x hΘd hsd
  -- the slope of `Φ` undoes the slope of `e₁` backwards
  have hid : (fderiv ℝ Φ (e₁.symm x)).comp (fderiv ℝ e₁.symm x)
      = ContinuousLinearMap.id ℝ (Coords 4) := by
    rw [← fderiv_comp x hΦd hsd]
    have hev : Φ ∘ e₁.symm =ᶠ[𝓝 x] id := by
      filter_upwards [e₁.open_target.mem_nhds hxt] with z hz
      change Φ (e₁.symm z) = z
      rw [← he₁Φ]
      exact e₁.right_inv hz
    rw [hev.fderiv_eq]
    exact fderiv_id
  have hback : ∀ u : Coords 4, fderiv ℝ Φ (e₁.symm x) (fderiv ℝ e₁.symm x u) = u := fun u ↦
    congrArg (fun A : Coords 4 →L[ℝ] Coords 4 ↦ A u) hid
  calc tableMeasure g' x v w
      = tableMeasure g' (Φ (e₁.symm x)) (fderiv ℝ Φ (e₁.symm x) (fderiv ℝ e₁.symm x v))
          (fderiv ℝ Φ (e₁.symm x) (fderiv ℝ e₁.symm x w)) := by rw [hback, hback, hΦy]
    _ = tableMeasure (inNewCoords Φ g') (e₁.symm x) (fderiv ℝ e₁.symm x v)
          (fderiv ℝ e₁.symm x w) := (tableMeasure_inNewCoords g' hΦd _ _).symm
    _ = tableMeasure (inNewCoords Θ S) (e₁.symm x) (fderiv ℝ e₁.symm x v)
          (fderiv ℝ e₁.symm x w) := by rw [tableMeasure_congr hent]
    _ = tableMeasure S (Θ (e₁.symm x)) (fderiv ℝ Θ (e₁.symm x) (fderiv ℝ e₁.symm x v))
          (fderiv ℝ Θ (e₁.symm x) (fderiv ℝ e₁.symm x w)) := tableMeasure_inNewCoords S hΘd _ _
    _ = tableMeasure S ((e₁.symm.trans e₂) x) (fderiv ℝ (e₁.symm.trans e₂) x v)
          (fderiv ℝ (e₁.symm.trans e₂) x w) := by
        rw [hΨx, hD]
        rfl

/-- **Result B.** There are a mass `m` and a change of coordinates `Ψ`, smooth with a smooth
inverse, defined near `x₀` inside the region, that lands off the rim, the centre and the poles,
and for which the table `g'` gives any two steps at `x` the length that Schwarzschild's table
gives at `Ψ x` to the two steps as `Ψ` sees them. -/
theorem resultB (g' g'inv : Fin 4 → Fin 4 → Coords 4 → ℝ) (ξ' : Fin 3 → Fin 4 → Coords 4 → ℝ)
    (s' : Set (Coords 4)) (x₀ : Coords 4) (hreg : IsRegularTableOn g' g'inv s')
    (hturn : TurnsOn g' ξ' s') (hflat : ∀ x ∈ s', IsRicciFlatAt g' g'inv x)
    (htime : ∀ x ∈ s', HasOneTimeDirection fun v w : Coords 4 ↦ tableMeasure g' x v w)
    (hx₀ : x₀ ∈ s')
    (hu : UsableDistanceAt (flatMeasure (tableMeasure g')) (fun i ↦ fieldOf (ξ' i)) x₀) :
    ∃ (m : ℝ) (Ψ : OpenPartialHomeomorph (Coords 4) (Coords 4)),
      x₀ ∈ Ψ.source ∧ Ψ.source ⊆ s' ∧ ContDiffOn ℝ ∞ Ψ Ψ.source ∧
      ContDiffOn ℝ ∞ Ψ.symm Ψ.target ∧
      ∀ x ∈ Ψ.source, (Ψ x ∈ outside m ∨ Ψ x ∈ inside m) ∧
        ∀ v w : Coords 4, tableMeasure g' x v w
          = tableMeasure (roundG (schwA m) (schwB m)) (Ψ x) (fderiv ℝ Ψ x v) (fderiv ℝ Ψ x w) := by
  -- coordinates that fit the turns
  obtain ⟨Φ, R, W, y₀, hW, hy₀, hΦy₀, h2, h3, hΦs, hΦ, hRR, hRdet, hdet, hturnΦ⟩ :=
    turnsCoordinates g' g'inv ξ' s' hreg hturn x₀ hx₀
  have hu' : UsableDistanceAt (flatMeasure (tableMeasure (inNewCoords Φ g'))) turns y₀ :=
    usable_inNewCoords hreg hturn hW hy₀ hΦs hΦ hRR hdet hturnΦ (by rw [hΦy₀]; exact hu)
  -- Birkhoff's theorem on the patch
  obtain ⟨m, Θ, W', hW', hy₀', hW'W, hΘ, hΘdet, hΘB⟩ :=
    birkhoff_patch (h := inNewCoords Φ g') (hinv := invT (inNewCoords Φ g')) hW hy₀ h2 h3
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
  refine ⟨m, e₁.symm.trans e₂, ?_, fun x hx ↦ ?_, ?_, ?_, fun x hx ↦ ?_⟩
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

end GravityInLean.Join
