/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.KSOutside
public import GravityInLean.Global.KSInside
public import GravityInLean.Global.KruskalChart
public import GravityInLean.Global.SchwChart
public import GravityInLean.Rim.Finish
public import GravityInLean.Checks.DeSitter

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Two checks of the statements for a whole space-time

Board item `task:global-desitter`. Two of the statements of `Goals/Global.lean`:

* `kruskalMapOfSchwarzschild` (known answer): Schwarzschild's table, outside the rim and inside
  it, maps into Kruskal's whole space-time by the textbook formulas of Kruskal and Szekeres. The
  two halves are `kruskalOutside_isKruskalMapOn` and `kruskalInside_isKruskalMapOn`.
* `globalDeSitterNoMap` (the conclusion can fail): de Sitter's space-time on the region
  `shellBox 0 L` is a space-time, looks the same from every side, and the region is in one piece
  without holes; but it has no length-keeping map into any of the models. A map into Kruskal's
  would make de Sitter's table Kruskal's in a chart (`IsKruskalMapOn.isKruskalNear`), and it is
  Kruskal's in no chart (`deSitterNotKruskal`). A map into Schwarzschild's whole space-time would
  make it Schwarzschild's in a chart (`IsSchwarzschildMapOn.isSchwarzschildWith`), and it is
  Schwarzschild's in no chart (`Tests.deSitterNotSchwarzschild`).
-/

@[expose] public section

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

/-- **Schwarzschild's table maps into Kruskal's whole space-time by the textbook formulas,**
outside the rim and inside it, for every positive mass. -/
theorem kruskalMapOfSchwarzschild : KruskalMapOfSchwarzschild :=
  fun m hm ↦ ⟨kruskalOutside_isKruskalMapOn m hm, kruskalInside_isKruskalMapOn m hm⟩

/-- The region `shellBox 0 L` lies in de Sitter's region: distance label between `0` and `L`,
off the poles. -/
theorem shellBox_subset_deSitterRegion (L : ℝ) : shellBox 0 L ⊆ deSitterRegion L :=
  fun _ ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ ↦ ⟨h1, h2, (Real.sin_pos_of_pos_of_lt_pi h3 h4).ne'⟩

/-- **De Sitter's space-time has no length-keeping map into any of the models.** On
`shellBox 0 L` it is a space-time and looks the same from every side, and the region is in one
piece without holes; but there is no length-keeping map into Kruskal's whole space-time for any
positive mass, nor into Schwarzschild's whole space-time for any mass that is zero or
negative. So the conclusion of `GlobalBirkhoff` really needs "empty". -/
theorem globalDeSitterNoMap : GlobalDeSitterNoMap := by
  intro L hL
  have hsub := shellBox_subset_deSitterRegion L
  have hst : IsSpaceTimeOn (flatMeasure (tableMeasure (roundG (dsA L) (dsB L))))
      (shellBox 0 L) := isSpaceTimeOn_sub (deSitter_isSpaceTimeOn L) hsub
  obtain ⟨q, hq⟩ := shellBox_nonempty hL
  refine ⟨isSimplyConnected_shellBox hL, hst,
    isRoundOn_sub (Tests.deSitterIsRoundOn L) (isOpen_shellBox 0 L) hsub, ?_, ?_⟩
  · rintro ⟨m, hm, D, hD⟩
    exact deSitterNotKruskal L hL m hm q (hsub hq) (hD.isKruskalNear hst hq)
  · rintro ⟨m, hm, D, hD⟩
    exact Tests.deSitterNotSchwarzschild L hL q (hsub hq)
      ((isSchwarzschildNear_iff _ q).mpr ⟨m, hD.isSchwarzschildWith hm hst hq⟩)

end GravityInLean.Curved
