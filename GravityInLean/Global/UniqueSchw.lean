/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.SchwLocal
public import GravityInLean.Global.SchwChart
public import GravityInLean.Global.ChartChange
public import GravityInLean.Global.UniqueKruskal

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Two length-keeping maps into Schwarzschild's of negative mass differ by a symmetry

The second part of `GlobalBirkhoffUnique` (`Goals/Global.lean`): `unique_schw`. The twin of
`Global/UniqueKruskal.lean`.

The local input is `KeepsSchwOn.local` (`Global/SchwLocal.lean`): a map of coordinate space that
keeps Schwarzschild's table of negative mass is, in ordinary space labels, a symmetry
`schwSym ε c R` near every point.

* `schwSym_comp`, `schwSym_one`: the symmetries one after another.
* `schwSym_eq_of_eventuallyEq`: two symmetries that agree on an open set of ordinary space and
  time are the same.
* `IsSchwarzschildMapOn.sym_unique`: a symmetry is fixed by what it does to a length-keeping map
  near one point (such a map fills a neighbourhood of its image).
* `IsSchwarzschildMapOn.local_unique`: two length-keeping maps differ by a symmetry near every
  point: the change of charts between them keeps Schwarzschild's table
  (`carriesTableAt_chartChange`).
* `unique_schw`: on a region in one piece, two length-keeping maps differ by one symmetry.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

/-! ## The symmetries, one after another -/

/-- Two symmetries of Schwarzschild's whole space-time, one after the other, are a symmetry:
the signs and the matrices multiply, the shifts add up. -/
theorem schwSym_comp (ε c ε' c' : ℝ) (R R' : Matrix (Fin 3) (Fin 3) ℝ) (z : Coords 4) :
    schwSym ε c R (schwSym ε' c' R' z) = schwSym (ε * ε') (ε * c' + c) (R * R') z := by
  funext i
  fin_cases i <;> simp [schwSym, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- The symmetry with sign one, no shift and the unit matrix does nothing. -/
theorem schwSym_one (z : Coords 4) : schwSym 1 0 1 z = z := by
  funext i
  fin_cases i <;> simp [schwSym]

/-- **Two symmetries that agree near one point of ordinary space and time are the same.** -/
theorem schwSym_eq_of_eventuallyEq {ε c ε' c' : ℝ} {R R' : Matrix (Fin 3) (Fin 3) ℝ}
    {z : Coords 4} (h : ∀ᶠ y in 𝓝 z, schwSym ε c R y = schwSym ε' c' R' y) :
    ε = ε' ∧ c = c' ∧ R = R' := by
  -- they have the same slope at `z`, and the slope of a symmetry is its sign and its matrix
  have hfd : fderiv ℝ (schwSym ε c R) z = fderiv ℝ (schwSym ε' c' R') z :=
    Filter.EventuallyEq.fderiv_eq h
  have key : ∀ (u : Coords 4) (i : Fin 4), schwSym ε 0 R u i = schwSym ε' 0 R' u i :=
    fun u i ↦ by
      rw [← fderiv_schwSym ε c R z u, ← fderiv_schwSym ε' c' R' z u, hfd]
  have hε : ε = ε' := by simpa [schwSym] using key ![1, 0, 0, 0] 0
  have hR : R = R' := by
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [schwSym] using key ![0, 1, 0, 0] 1
    · simpa [schwSym] using key ![0, 0, 1, 0] 1
    · simpa [schwSym] using key ![0, 0, 0, 1] 1
    · simpa [schwSym] using key ![0, 1, 0, 0] 2
    · simpa [schwSym] using key ![0, 0, 1, 0] 2
    · simpa [schwSym] using key ![0, 0, 0, 1] 2
    · simpa [schwSym] using key ![0, 1, 0, 0] 3
    · simpa [schwSym] using key ![0, 0, 1, 0] 3
    · simpa [schwSym] using key ![0, 0, 0, 1] 3
  -- the shift: compare the new times at `z`
  have h0 : ε * z 0 + c = ε' * z 0 + c' := congrFun h.self_of_nhds 0
  rw [hε] at h0
  exact ⟨hε, add_left_cancel h0, hR⟩

/-! ## Two length-keeping maps -/

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  [IsManifold 𝓘(ℝ, Coords 4) ∞ M] {m : ℝ} {g : LengthMeasure 𝓘(ℝ, Coords 4) M} {s : Set M}

/-- **Two length-keeping maps into Schwarzschild's whole space-time of negative mass differ by
a symmetry near every point of the region.** -/
theorem IsSchwarzschildMapOn.local_unique {D D' : M → Coords 4} (hm : m < 0)
    (hD : IsSchwarzschildMapOn m g D s) (hD' : IsSchwarzschildMapOn m g D' s)
    (hg : IsSpaceTimeOn g s) {q : M} (hq : q ∈ s) :
    ∃ (ε c : ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ), (ε = 1 ∨ ε = -1) ∧ R.transpose * R = 1 ∧
      ∀ᶠ q' in 𝓝 q, D' q' = schwSym ε c R (D q') := by
  -- for a negative mass both maps miss the centre
  have hoff : 0 < D q 1 ^ 2 + D q 2 ^ 2 + D q 3 ^ 2 := Or.resolve_left (hD.2.2 q hq).1 hm.ne
  have hoff' : 0 < D' q 1 ^ 2 + D' q 2 ^ 2 + D' q 3 ^ 2 :=
    Or.resolve_left (hD'.2.2 q hq).1 hm.ne
  obtain ⟨R₁, φ, hR₁, hφ, hqφ, -, h⟩ := hD.exists_chart hm.le hg hq hoff
  obtain ⟨R₂, φ', hR₂, hφ', hqφ', -, h'⟩ := hD'.exists_chart hm.le hg hq hoff'
  -- the change of charts keeps Schwarzschild's table, so it is a symmetry near `φ q`
  have hK : KeepsSchwOn m (φ' ∘ φ.symm) (φ.target ∩ φ.symm ⁻¹' φ'.source) := by
    refine ⟨isOpen_chartChange_domain φ φ', fun x hx ↦ ?_, fun x hx ↦ (h' (φ.symm x) hx.2).1,
      fun x hx ↦ carriesTableAt_chartChange hφ hφ' (fun p hp ↦ (h p hp.1).2.2)
        (fun p hp ↦ (h' p hp.2).2.2) hx.1 hx.2⟩
    have hmem := (h (φ.symm x) (φ.map_target hx.1)).1
    rwa [φ.right_inv hx.1] at hmem
  have hqW : φ q ∈ φ.target ∩ φ.symm ⁻¹' φ'.source := by
    refine ⟨φ.map_source hqφ, ?_⟩
    rw [mem_preimage, φ.left_inv hqφ]
    exact hqφ'
  obtain ⟨ε, c, R₀, hε, hR₀, hloc⟩ := hK.local hm hqW
  have hpull : ∀ᶠ q' in 𝓝 q, sphericalToSpace (φ' (φ.symm (φ q')))
      = schwSym ε c R₀ (sphericalToSpace (φ q')) := (φ.continuousAt hqφ).eventually hloc
  have hR₁' : R₁.transpose.transpose * R₁.transpose = 1 := by
    rw [Matrix.transpose_transpose]
    exact mul_eq_one_comm.mp hR₁
  refine ⟨ε, c, R₂ * R₀ * R₁.transpose, hε, orthogonal_mul (orthogonal_mul hR₂ hR₀) hR₁', ?_⟩
  filter_upwards [hpull, φ.open_source.mem_nhds hqφ, φ'.open_source.mem_nhds hqφ']
    with q' h1 h2 h3
  -- undo the chart of `D`: the space labels of the chart are a turn of `D`
  have hw : sphericalToSpace (φ q') = schwSym 1 0 R₁.transpose (D q') := by
    rw [(h q' h2).2.1, schwSym_comp, hR₁, one_mul, mul_zero, add_zero, schwSym_one]
  rw [φ.left_inv h2] at h1
  rw [(h' q' h3).2.1, h1, hw, schwSym_comp, schwSym_comp]
  simp only [one_mul, mul_one, mul_zero, add_zero, zero_add, mul_assoc]

/-- **A symmetry is fixed by what it does to a length-keeping map near one point.** -/
theorem IsSchwarzschildMapOn.sym_unique {D : M → Coords 4} (hm : m < 0)
    (hD : IsSchwarzschildMapOn m g D s) (hg : IsSpaceTimeOn g s) {q : M} (hq : q ∈ s)
    {ε c ε' c' : ℝ} {R R' : Matrix (Fin 3) (Fin 3) ℝ}
    (h : ∀ᶠ q' in 𝓝 q, schwSym ε c R (D q') = schwSym ε' c' R' (D q')) :
    ε = ε' ∧ c = c' ∧ R = R' := by
  -- the sign of the mass plays no part in this step; it is in the statement only so that it
  -- reads like its neighbours
  have _ := hm
  -- a length-keeping map fills a neighbourhood of its image
  have hev : ∀ᶠ z in 𝓝 (D q), schwSym ε c R z = schwSym ε' c' R' z := by
    rw [← hD.map_nhds hg hq]
    exact Filter.eventually_map.mpr h
  exact schwSym_eq_of_eventuallyEq hev

/-- **Two length-keeping maps into Schwarzschild's whole space-time of negative mass on a
region in one piece differ by one symmetry:** the second part of `GlobalBirkhoffUnique`. -/
theorem unique_schw (hs : IsPreconnected s) (hg : IsSpaceTimeOn g s) (hm : m < 0)
    (D D' : M → Coords 4) (hD : IsSchwarzschildMapOn m g D s)
    (hD' : IsSchwarzschildMapOn m g D' s) :
    ∃ (ε c : ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ), (ε = 1 ∨ ε = -1) ∧ R.transpose * R = 1 ∧
      ∀ q ∈ s, D' q = schwSym ε c R (D q) := by
  by_cases hne : s.Nonempty
  swap
  · exact ⟨1, 0, 1, Or.inl rfl, by simp, fun q hq ↦ (hne ⟨q, hq⟩).elim⟩
  obtain ⟨q₀, hq₀⟩ := hne
  obtain ⟨ε, c, R, hε, hR, h₀⟩ := hD.local_unique hm hD' hg hq₀
  refine ⟨ε, c, R, hε, hR, ?_⟩
  -- the points near which the symmetry is `(ε, c, R)`, and those near which it is another one
  have hu : IsOpen {q : M | ∀ᶠ q' in 𝓝 q, D' q' = schwSym ε c R (D q')} :=
    isOpen_setOfPred_eventually_nhds
  have hv : IsOpen {q : M | ∃ (ε' c' : ℝ) (R' : Matrix (Fin 3) (Fin 3) ℝ),
      (ε', c', R') ≠ (ε, c, R) ∧ ∀ᶠ q' in 𝓝 q, D' q' = schwSym ε' c' R' (D q')} := by
    rw [isOpen_iff_mem_nhds]
    rintro q ⟨ε', c', R', hne', hq⟩
    filter_upwards [hq.eventually_nhds] with q' hq'
    exact ⟨ε', c', R', hne', hq'⟩
  have hsuv : s ⊆ {q : M | ∀ᶠ q' in 𝓝 q, D' q' = schwSym ε c R (D q')}
      ∪ {q : M | ∃ (ε' c' : ℝ) (R' : Matrix (Fin 3) (Fin 3) ℝ),
        (ε', c', R') ≠ (ε, c, R) ∧ ∀ᶠ q' in 𝓝 q, D' q' = schwSym ε' c' R' (D q')} := by
    intro q hq
    obtain ⟨ε', c', R', -, -, hq'⟩ := hD.local_unique hm hD' hg hq
    by_cases e : (ε', c', R') = (ε, c, R)
    · obtain ⟨rfl, e'⟩ := Prod.mk.inj e
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e'
      exact Or.inl hq'
    · exact Or.inr ⟨ε', c', R', e, hq'⟩
  -- a point near which both hold would have two symmetries
  have hsub : s ⊆ {q : M | ∀ᶠ q' in 𝓝 q, D' q' = schwSym ε c R (D q')} := by
    by_contra hcon
    obtain ⟨q, hq, hqu⟩ := Set.not_subset.1 hcon
    obtain ⟨q₁, hq₁, hq₁u, ε', c', R', hne', hq₁v⟩ :=
      hs _ _ hu hv hsuv ⟨q₀, hq₀, h₀⟩ ⟨q, hq, (hsuv hq).resolve_left hqu⟩
    have hboth : ∀ᶠ q' in 𝓝 q₁, schwSym ε c R (D q') = schwSym ε' c' R' (D q') := by
      filter_upwards [hq₁u, hq₁v] with q' e1 e2
      rw [← e1, ← e2]
    obtain ⟨e1, e2, e3⟩ := hD.sym_unique hm hg hq₁ hboth
    exact hne' (by rw [e1, e2, e3])
  exact fun q hq ↦ (hsub hq).self_of_nhds

end GravityInLean.Curved
