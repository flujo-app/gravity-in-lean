/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Curved.Goal

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Reading a curved space in a chart: the words

Board item `task:join-carry`. Definitions only. A chart `c` of the curved space `M` turns

* a length measure `g` on `M` into a length measure on coordinate space (`carryMeasure`),
* a field of arrows on `M` into a field of arrows on coordinate space (`carryField`), and back
  (`pushField`),
* a connection on `M` into a connection on coordinate space (`carryTransport`).

The other files of `Join/` show that every notion of `Curved/Basic.lean` carries over.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Join

open GravityInLean.Curved

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- The length measure `g` of the curved space, read in the chart `c`: two steps at the point `x`
of coordinate space are taken back to the curved space by the slope of `c.symm`, and measured
there. -/
noncomputable def carryMeasure (c : OpenPartialHomeomorph M E) (g : LengthMeasure 𝓘(ℝ, E) M) :
    E → E →L[ℝ] E →L[ℝ] ℝ :=
  fun x ↦ (g (c.symm x)).bilinearComp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x)

/-- A field of arrows of the curved space, read in the chart `c`: the arrow at `c.symm x`, as the
chart sees it. -/
noncomputable def carryField (c : OpenPartialHomeomorph M E) (X : Arrows 𝓘(ℝ, E) M) :
    Arrows 𝓘(ℝ, E) E :=
  fun x ↦ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x) (X (c.symm x))

/-- A field of arrows on coordinate space, taken to the curved space by the chart `c`. Outside
the domain of the chart it has no meaning. -/
noncomputable def pushField (c : OpenPartialHomeomorph M E) (X : Arrows 𝓘(ℝ, E) E) :
    Arrows 𝓘(ℝ, E) M :=
  fun q ↦ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c q) (X (c q))

/-- A connection of the curved space, read in the chart `c`: take the field to the curved space,
let the connection act there, and read the result in the chart. -/
noncomputable def carryTransport (c : OpenPartialHomeomorph M E) (cov : Transport 𝓘(ℝ, E) M) :
    Transport 𝓘(ℝ, E) E :=
  fun σ x ↦ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x)).comp
    ((cov (pushField c σ) (c.symm x)).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x))

theorem carryMeasure_apply (c : OpenPartialHomeomorph M E) (g : LengthMeasure 𝓘(ℝ, E) M)
    (x v w : E) :
    carryMeasure c g x v w = g (c.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x w) := rfl

theorem carryTransport_apply (c : OpenPartialHomeomorph M E) (cov : Transport 𝓘(ℝ, E) M)
    (σ : Arrows 𝓘(ℝ, E) E) (x : E) (v : E) :
    carryTransport c cov σ x v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (c.symm x)
      (cov (pushField c σ) (c.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm x v)) := rfl

end GravityInLean.Join
