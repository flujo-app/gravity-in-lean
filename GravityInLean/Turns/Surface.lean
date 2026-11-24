/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Turns.Basic
public import GravityInLean.Turns.Gram
public import GravityInLean.Turns.Complete
public import GravityInLean.Turns.LevelSet
public import GravityInLean.Turns.RestMap

import Mathlib.Tactic

/-!
# Where the middle field rests

Board item `task:turns-surface`. Step 3 of the route. Three fields `η 0`, `η 1`, `η 2` span two
directions at every point of a region, combine the way turns do at the point `p`, and `η 1` is
zero at `p`. Then the points near `p` where `η 1` is zero contain a surface through `p`, given by
a smooth map `σ` of two numbers, and the two directions of `σ` at the start together with
`η 0 p`, `η 2 p` are four independent arrows.

The route taken: `η 1` is zero at `q` as soon as it is at right angles (ordinary dot product) to
`η 0 q` and `η 2 q`, as long as these two are independent (`eq_zero_of_dot_eq_zero`). So the
surface is the zero set of the two smooth functions `η 0 ⬝ η 1` and `η 2 ⬝ η 1`
(`exists_levelSurface`). Their slopes at `p` along `η 0 p` and `η 2 p` are known from the
brackets, because `η 1 p = 0`: the slope of `η 1` at `p` along `η 0 p` is `η 2 p`, and along
`η 2 p` it is `-η 0 p`; the determinant asked for by `exists_levelSurface` is then the Gram
determinant of `η 0 p`, `η 2 p`, which is positive (`gram_pos_of_finrank`). The two functions,
their smoothness and their slope at `p` are in `RestMap.lean`; the completion of `η 0 p`, `η 2 p`
to four independent arrows is in `Complete.lean`.
-/

@[expose] public section

namespace GravityInLean.Turns

open Set Metric Topology Matrix

open scoped ContDiff

/-- **Where the middle field rests.** There is a smooth surface `σ` through `p` on which `η 1` is
zero, and whose two directions at the start, with `η 0 p` and `η 2 p`, are four independent
arrows (the determinant of the table with these four columns is not zero). -/
theorem exists_restSurface (η : Fin 3 → Coords 4 → Coords 4) (s : Set (Coords 4))
    (hs : IsOpen s) (p : Coords 4) (hp : p ∈ s) (hη : ∀ i, ContDiffOn ℝ ∞ (η i) s)
    (hrank : ∀ x ∈ s,
      Module.finrank ℝ (Submodule.span ℝ (Set.range fun i ↦ η i x)) = 2)
    (h1 : η 1 p = 0) (h01 : lieB (η 0) (η 1) p = η 2 p) (h12 : lieB (η 1) (η 2) p = η 0 p) :
    ∃ (δ : ℝ) (σ : ℝ × ℝ → Coords 4), 0 < δ ∧ ContDiffOn ℝ ∞ σ (ball 0 δ) ∧ σ 0 = p ∧
      (∀ u ∈ ball (0 : ℝ × ℝ) δ, σ u ∈ s ∧ η 1 (σ u) = 0) ∧
      (Matrix.of fun α μ : Fin 4 ↦
        (![fderiv ℝ σ 0 (1, 0), fderiv ℝ σ 0 (0, 1), η 0 p, η 2 p] μ) α).det ≠ 0 := by
  -- The two outer fields at `p` are independent: their Gram determinant is positive.
  have hgram : 0 < (η 0 p ⬝ᵥ η 0 p) * (η 2 p ⬝ᵥ η 2 p) - (η 0 p ⬝ᵥ η 2 p) ^ 2 :=
    gram_pos_of_finrank (fun i ↦ η i p) (hrank p hp) h1
  have hd : ∀ i, DifferentiableAt ℝ (η i) p := fun i ↦
    ((hη i).contDiffAt (hs.mem_nhds hp)).differentiableAt (by simp)
  -- The slope of the middle field at `p` along the two outer ones, from the brackets.
  have hDa : fderiv ℝ (η 1) p (η 0 p) = η 2 p := by
    have h := h01
    simp only [lieB, h1, map_zero, sub_zero] at h
    exact h
  have hDb : fderiv ℝ (η 1) p (η 2 p) = -η 0 p := by
    have h := h12
    simp only [lieB, h1, map_zero, zero_sub] at h
    exact neg_eq_iff_eq_neg.mp h
  -- The determinant asked for by `exists_levelSurface` is the Gram determinant.
  have hdet : (fderiv ℝ (restMap η) p (η 0 p)).1 * (fderiv ℝ (restMap η) p (η 2 p)).2 -
      (fderiv ℝ (restMap η) p (η 0 p)).2 * (fderiv ℝ (restMap η) p (η 2 p)).1 ≠ 0 := by
    rw [fderiv_restMap hd h1, fderiv_restMap hd h1, hDa, hDb]
    intro h
    simp only [dotProduct_neg, dotProduct_comm (η 2 p) (η 0 p)] at h
    exact hgram.ne' (by linear_combination h)
  have hrest0 : restMap η p = 0 :=
    Prod.ext (by simp [restMap, h1]) (by simp [restMap, h1])
  -- The surface where both dot products are zero.
  obtain ⟨e₁, e₂, hE⟩ := exists_complete (η 0 p) (η 2 p) hgram
  obtain ⟨δ₀, σ, hδ₀, hσsm, hσ0, hσmem, c₁, d₁, c₂, d₂, hσ1, hσ2⟩ :=
    exists_levelSurface (restMap η) s hs p hp (contDiffOn_restMap hη) hrest0 (η 0 p) (η 2 p)
      hdet e₁ e₂
  -- Near the start the two outer fields stay independent along the surface.
  have hc : ContinuousOn (fun u ↦ (η 0 (σ u) ⬝ᵥ η 0 (σ u)) * (η 2 (σ u) ⬝ᵥ η 2 (σ u)) -
      (η 0 (σ u) ⬝ᵥ η 2 (σ u)) ^ 2) (ball 0 δ₀) :=
    (continuousOn_gram hη).comp hσsm.continuousOn fun u hu ↦ (hσmem u hu).1
  have hg0 : (η 0 (σ 0) ⬝ᵥ η 0 (σ 0)) * (η 2 (σ 0) ⬝ᵥ η 2 (σ 0)) -
      (η 0 (σ 0) ⬝ᵥ η 2 (σ 0)) ^ 2 ≠ 0 := by
    rw [hσ0]
    exact hgram.ne'
  have hne : ∀ᶠ u in 𝓝 (0 : ℝ × ℝ), (η 0 (σ u) ⬝ᵥ η 0 (σ u)) * (η 2 (σ u) ⬝ᵥ η 2 (σ u)) -
      (η 0 (σ u) ⬝ᵥ η 2 (σ u)) ^ 2 ≠ 0 :=
    (hc.continuousAt (ball_mem_nhds 0 hδ₀)).eventually_ne hg0
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.eventually_nhds_iff_ball.mp hne
  refine ⟨min δ₀ δ₁, σ, lt_min hδ₀ hδ₁, hσsm.mono (ball_subset_ball (min_le_left _ _)), hσ0,
    ?_, ?_⟩
  · -- there the middle field is zero, being at right angles to two independent arrows
    intro u hu
    have hu0 := ball_subset_ball (min_le_left δ₀ δ₁) hu
    have hu1 := ball_subset_ball (min_le_right δ₀ δ₁) hu
    obtain ⟨hus, hF⟩ := hσmem u hu0
    exact ⟨hus, eq_zero_of_dot_eq_zero (fun i ↦ η i (σ u)) (hrank _ hus) (hball u hu1)
      (congrArg Prod.fst hF) (congrArg Prod.snd hF)⟩
  · -- the four arrows are independent
    rw [hσ1, hσ2, det_complete_add]
    exact hE

end GravityInLean.Turns
