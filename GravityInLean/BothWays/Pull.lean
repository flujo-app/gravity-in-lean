/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Join.Carry

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# From a chart back to the curved space: the words

Board item `task:bothways-pull`. Definitions only. `Join/Carry.lean` reads a curved space in a
chart. Here the notions are known in the chart and wanted on the curved space:

* `ReadsAs c g G`: on the domain of the chart `c`, the length measure `g` of the curved space is
  the length measure `G` of coordinate space, for the steps as the chart sees them;
* `pullTransport c cov'`: a connection of coordinate space, taken to the curved space by the
  chart. (A field of arrows of coordinate space is taken to the curved space by `pushField` of
  `Join/Carry.lean`.)

The other files of `BothWays/` show that every notion of `Curved/Basic.lean` comes back along
the chart.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.BothWays

open GravityInLean.Curved GravityInLean.Join

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- **The length measure `g` of the curved space reads as `G` in the chart `c`.** At every point
`q` of the chart's domain, the length of two steps measured with `g` is what `G` gives at the
point `c q` for the two steps as the chart sees them. -/
def ReadsAs (c : OpenPartialHomeomorph M E) (g : LengthMeasure 𝓘(ℝ, E) M)
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) : Prop :=
  ∀ q ∈ c.source, ∀ v w : TangentSpace 𝓘(ℝ, E) q,
    g q v w = flatMeasure G (c q) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q w)

/-- A connection of coordinate space, taken to the curved space by the chart `c`: read the field
in the chart, let the connection act there, and take the result back. Outside the domain of the
chart it has no meaning. -/
noncomputable def pullTransport (c : OpenPartialHomeomorph M E) (cov' : Transport 𝓘(ℝ, E) E) :
    Transport 𝓘(ℝ, E) M :=
  fun σ q ↦ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q)).comp
    ((cov' (carryField c σ) (c q)).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q))

theorem pullTransport_apply (c : OpenPartialHomeomorph M E) (cov' : Transport 𝓘(ℝ, E) E)
    (σ : Arrows 𝓘(ℝ, E) M) (q : M) (v : TangentSpace 𝓘(ℝ, E) q) :
    pullTransport c cov' σ q v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q)
      (cov' (carryField c σ) (c q) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c q v)) := rfl

end GravityInLean.BothWays
