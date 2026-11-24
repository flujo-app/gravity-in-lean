/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.SchwSection
public import GravityInLean.Global.SchwSym
public import GravityInLean.Join.Atlas

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# A length-keeping map into Schwarzschild's whole space-time gives charts with Schwarzschild's table

Around every point that a length-keeping map `D` sends off the centre, `D` is, up to a turn or
mirror of space, the map `sphericalToSpace` after a chart of the curved space; in that chart the
length measure is Schwarzschild's table of distance and angles.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

section SchwChart

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  [IsManifold 𝓘(ℝ, Coords 4) ∞ M] {m : ℝ} {g : LengthMeasure 𝓘(ℝ, Coords 4) M} {s : Set M}

/-- **A length-keeping map into Schwarzschild's whole space-time is, near each point it sends
off the centre, `sphericalToSpace` after a chart.** Around `q` there are a chart `φ` of the
curved space with domain inside the region, landing where the distance label is positive and off
the poles, and a turn or mirror `R` of space, such that `D` is `φ`, then `sphericalToSpace`,
then `R`; and in the chart `φ` the length measure is Schwarzschild's table. -/
theorem IsSchwarzschildMapOn.exists_chart {D : M → Coords 4} (hm : m ≤ 0)
    (hD : IsSchwarzschildMapOn m g D s) (hg : IsSpaceTimeOn g s) {q : M} (hq : q ∈ s)
    (hoff : 0 < D q 1 ^ 2 + D q 2 ^ 2 + D q 3 ^ 2) :
    ∃ (R : Matrix (Fin 3) (Fin 3) ℝ) (φ : OpenPartialHomeomorph M (Coords 4)),
      R.transpose * R = 1 ∧ φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M ∧ q ∈ φ.source ∧
      φ.source ⊆ s ∧
      ∀ q' ∈ φ.source, φ q' ∈ outside m ∧ D q' = schwSym 1 0 R (sphericalToSpace (φ q')) ∧
        ∀ v w : TangentSpace 𝓘(ℝ, Coords 4) q',
          g q' v w = flatMeasure (tableMeasure (roundG (schwA m) (schwB m))) (φ q')
            (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q' v)
            (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q' w) := by
  sorry

/-- **A space-time with a length-keeping map into Schwarzschild's whole space-time (mass zero
or negative) is Schwarzschild's in a chart around every point of the region.** For mass zero a
point sent to the centre is first shifted off it. -/
theorem IsSchwarzschildMapOn.isSchwarzschildWith {D : M → Coords 4} (hm : m ≤ 0)
    (hD : IsSchwarzschildMapOn m g D s) (hg : IsSpaceTimeOn g s) {q : M} (hq : q ∈ s) :
    IsSchwarzschildWith m g q := by
  sorry

end SchwChart

end GravityInLean.Curved
