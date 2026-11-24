/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Connection.IsConnection
public import GravityInLean.Connection.NoTwist
public import GravityInLean.Connection.KeepsLengths
public import GravityInLean.Goals.Connection

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Every length measure has a connection

Board item `task:checks-connection-skeleton`. Last file of the proof of
`ConnectionExistsStatement` (`Goals/Connection.lean`), after the textbooks' formula of Koszul
(for example O'Neill, *Semi-Riemannian Geometry*, chapter 3). The route:

* `Koszul.lean`: Koszul's expression `koszulExpr`, made of slopes of `g` and brackets only;
* `Tensorial1.lean`, `Tensorial3.lean`: it depends on its outer fields only through their steps
  at the point;
* `Middle.lean`: in its middle field it obeys the sum rule and the product rule;
* `Sharp.lean`: because no step is at right angles to all steps, a measurement names one step;
* `Candidate.lean`: so Koszul's expression names a connection, `koszulCov g`;
* `IsConnection.lean`, `NoTwist.lean`, `KeepsLengths.lean`: the three conditions of
  `IsConnectionOf`.

This file puts the three conditions together.
-/

@[expose] public section

namespace GravityInLean

open scoped Manifold ContDiff

/-- **The candidate is the connection that belongs to `g`**, on every open region where `g` is a
length measure. -/
theorem Curved.isConnectionOf_koszulCov {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {g : Curved.LengthMeasure I M} {s : Set M} (hg : Curved.IsLengthMeasureOn g s)
    (hs : IsOpen s) : Curved.IsConnectionOf g (Curved.koszulCov g) s where
  isOpen := hs
  isConnection := Curved.isCovariantDerivativeOn_koszulCov hg hs
  noTwist := fun _ hx _ _ hX hY ↦ Curved.koszulCov_noTwist hg hs hx hX hY
  keepsLengths := fun _ hx _ _ hY hZ v ↦ Curved.koszulCov_keepsLengths hg hs hx hY hZ v

/-- **The statement `ConnectionExistsStatement` is true:** a length measure on an open region
has a connection there. -/
theorem connectionExists : Curved.ConnectionExistsStatement :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hs hg ↦ ⟨_, Curved.isConnectionOf_koszulCov hg hs⟩

end GravityInLean
