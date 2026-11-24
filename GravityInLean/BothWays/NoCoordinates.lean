/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.BothWays.OffRimKnown
public import GravityInLean.BothWays.PullEmpty
public import GravityInLean.BothWays.PullRound
public import GravityInLean.BothWays.PullSpaceTime
public import GravityInLean.BothWays.PullUsable
public import GravityInLean.Goals.ExactlyWhen
public import GravityInLean.Join.Goal

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Birkhoff's theorem, both ways, with no coordinates

Board item `task:bothways-nocoordinates`. Two statements of `Goals/ExactlyWhen.lean`:

* `schwarzschildIsEmpty`: a length measure that is Schwarzschild's in some chart around a point
  is empty near that point, outside the rim and inside it;
* `schwarzschildExactlyWhen`: around a point, a length measure is a round, empty space-time whose
  spheres give a usable distance exactly when it is Schwarzschild's in some chart.

From "round, empty, usable" to "Schwarzschild's in a chart" is the older theorem
`birkhoffNoCoordinates`. The other way, the region is the whole domain of the chart, and the
three fields are the three turns of coordinate space, taken to the curved space by the chart.
Everything is known for Schwarzschild's table on the set off the rim (`OffRimKnown.lean`) and
comes back along the chart (`PullSpaceTime.lean`, `PullEmpty.lean`, `PullRound.lean`,
`PullUsable.lean`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.BothWays

open GravityInLean.Curved GravityInLean.Join Real

open scoped Manifold ContDiff Topology

section Mono

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A table that is good on a region is good on every smaller open region. -/
theorem isRegularTableOn_mono {n : ℕ} {g ginv : Fin n → Fin n → Coords n → ℝ}
    {s t : Set (Coords n)} (h : IsRegularTableOn g ginv s) (ht : IsOpen t) (hts : t ⊆ s) :
    IsRegularTableOn g ginv t where
  isOpen := ht
  smooth := fun a b ↦ (h.smooth a b).mono hts
  symm := fun x hx ↦ h.symm x (hts hx)
  inverse := fun x hx ↦ h.inverse x (hts hx)

/-- A space-time on a region is a space-time on every smaller region. -/
theorem isSpaceTimeOn_mono {g : LengthMeasure I M} {s t : Set M} (h : IsSpaceTimeOn g s)
    (hts : t ⊆ s) : IsSpaceTimeOn g t where
  symm := fun x hx ↦ h.symm x (hts hx)
  oneTime := fun x hx ↦ h.oneTime x (hts hx)
  smooth := ContMDiffOn.mono h.smooth hts

/-- What looks the same from every side on a region does so on every smaller open region. -/
theorem isRoundOn_mono {g : LengthMeasure I M} {ξ : Fin 3 → Arrows I M} {s t : Set M}
    (h : IsRoundOn g ξ s) (ht : IsOpen t) (hts : t ⊆ s) : IsRoundOn g ξ t where
  isOpen := ht
  smooth := fun i ↦ (h.smooth i).mono hts
  unchanged := fun i x hx ↦ h.unchanged i x (hts hx)
  likeTurns := fun x hx ↦ h.likeTurns x (hts hx)
  surfaces := fun x hx ↦ h.surfaces x (hts hx)
  positive := fun x hx ↦ h.positive x (hts hx)

end Mono

/-- A chart that lands outside the rim or inside it lands in the set off the rim. -/
theorem target_subset_offRim {M : Type} [TopologicalSpace M] {m : ℝ}
    {φ : OpenPartialHomeomorph M (Coords 4)}
    (h : ∀ q ∈ φ.source, φ q ∈ outside m ∨ φ q ∈ inside m) : φ.target ⊆ offRim m := by
  intro x hx
  have h1 := h (φ.symm x) (φ.map_target hx)
  rw [φ.right_inv hx] at h1
  exact mem_offRim h1

end GravityInLean.BothWays

namespace GravityInLean

open GravityInLean.Curved GravityInLean.Join GravityInLean.BothWays

open scoped Manifold ContDiff Topology

/-- **Schwarzschild's in a chart is empty.** A length measure on a curved space that is
Schwarzschild's in some chart around a point, outside the rim or inside it, is empty on the
domain of that chart. No symmetry is assumed. -/
theorem schwarzschildIsEmpty : Curved.SchwarzschildIsEmptyStatement := by
  rintro M _ _ _ g p ⟨m, φ, hφ, hp, h⟩
  have hsub : φ.target ⊆ offRim m := target_subset_offRim fun q hq ↦ (h q hq).1
  exact ⟨φ.source, φ.open_source, hp,
    isEmptyOn_pull hφ (fun q hq ↦ (h q hq).2)
      (isRegularTableOn_mono (schwarzschild_regularTable_offRim m) φ.open_target hsub)
      fun x hx ↦ schwarzschild_ricciFlat_on_offRim m x (hsub hx)⟩

/-- **Birkhoff's theorem, both ways, with no coordinates.** Around a point of a curved space with
four dimensions, a length measure is a round, empty space-time whose spheres give a usable
distance exactly when it is Schwarzschild's in some chart around the point. -/
theorem schwarzschildExactlyWhen : Curved.SchwarzschildExactlyWhen := by
  intro M _ _ _ g p
  constructor
  · rintro ⟨s, ξ, hs, hp, hst, he, hr, hu⟩
    exact birkhoffNoCoordinates M g ξ s hs hst he hr p hp hu
  · rintro ⟨m, φ, hφ, hp, h⟩
    have hsub : φ.target ⊆ offRim m := target_subset_offRim fun q hq ↦ (h q hq).1
    have hread : ReadsAs φ g (tableMeasure (roundG (schwA m) (schwB m))) :=
      fun q hq ↦ (h q hq).2
    exact ⟨φ.source, fun i ↦ pushField φ (turns i), φ.open_source, hp,
      isSpaceTimeOn_pull hφ hread
        (isSpaceTimeOn_mono (schwarzschild_isSpaceTimeOn_offRim m) hsub),
      isEmptyOn_pull hφ hread
        (isRegularTableOn_mono (schwarzschild_regularTable_offRim m) φ.open_target hsub)
        (fun x hx ↦ schwarzschild_ricciFlat_on_offRim m x (hsub hx)),
      isRoundOn_pull hφ hread
        (isRoundOn_mono (schwarzschild_isRoundOn_offRim m) φ.open_target hsub),
      usableDistanceAt_pull hφ hread hp
        (schwarzschild_usable_offRim m (hsub (φ.map_source hp)))⟩

end GravityInLean
