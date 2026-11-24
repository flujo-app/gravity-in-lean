/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic

/-!
# A number that is the same near every point is the same on a region in one piece

Board item `task:checks-mass-connected`. Pure topology. Every point of a region in one piece has
a number, at most one, and near every point of the region all points have the same number. Then
all points of the region have the same number.
-/

@[expose] public section

namespace GravityInLean.Mass

open Filter Topology Set

/-- **The same near every point, so the same everywhere.** `R q m` says "the point `q` has the
number `m`". If a point of the region has at most one number, and every point of the region has a
number that all points near it have too, then one number serves the whole region, as long as the
region is in one piece. -/
theorem exists_const_of_locally {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsPreconnected s) {R : X → ℝ → Prop}
    (huniq : ∀ q ∈ s, ∀ m m' : ℝ, R q m → R q m' → m = m')
    (hloc : ∀ p ∈ s, ∃ m : ℝ, ∀ᶠ q in 𝓝 p, R q m) : ∃ m : ℝ, ∀ q ∈ s, R q m := by
  -- An empty region: any number serves.
  rcases s.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · exact ⟨0, fun q hq ↦ absurd hq (Set.notMem_empty q)⟩
  -- Otherwise take the number `m₀` of one point `p₀`.
  obtain ⟨m₀, hm₀⟩ := hloc p₀ hp₀
  refine ⟨m₀, fun q hq ↦ ?_⟩
  -- The points near which the number is `m₀` form an open set ...
  have hUo : IsOpen {q : X | ∀ᶠ q' in 𝓝 q, R q' m₀} :=
    isOpen_iff_eventually.mpr fun q hq ↦ eventually_eventually_nhds.mpr hq
  -- ... and so do the points near which it is one other number.
  have hVo : IsOpen {q : X | ∃ m : ℝ, m ≠ m₀ ∧ ∀ᶠ q' in 𝓝 q, R q' m} :=
    isOpen_iff_eventually.mpr fun q ⟨m, hm, hq⟩ ↦
      (eventually_eventually_nhds.mpr hq).mono fun q' hq' ↦ ⟨m, hm, hq'⟩
  -- The two sets cover the region.
  have hcover : s ⊆ {q : X | ∀ᶠ q' in 𝓝 q, R q' m₀}
      ∪ {q : X | ∃ m : ℝ, m ≠ m₀ ∧ ∀ᶠ q' in 𝓝 q, R q' m} := fun q' hq' ↦ by
    obtain ⟨m, hm⟩ := hloc q' hq'
    by_cases h : m = m₀
    · exact Or.inl (h ▸ hm)
    · exact Or.inr ⟨m, h, hm⟩
  -- They do not meet inside the region: a point there has one number only.
  have hdisj : ¬ (s ∩ ({q : X | ∀ᶠ q' in 𝓝 q, R q' m₀}
      ∩ {q : X | ∃ m : ℝ, m ≠ m₀ ∧ ∀ᶠ q' in 𝓝 q, R q' m})).Nonempty := by
    rintro ⟨q', hq', hqU, m, hm, hqV⟩
    exact hm (huniq q' hq' m m₀ hqV.self_of_nhds hqU.self_of_nhds)
  -- The region is in one piece and the first set meets it, so the second does not.
  rcases hcover hq with h | h
  · exact h.self_of_nhds
  · exact absurd (hs _ _ hUo hVo hcover ⟨p₀, hp₀, hm₀⟩ ⟨q, hq, h⟩) hdisj

end GravityInLean.Mass
