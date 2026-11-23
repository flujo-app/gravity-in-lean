/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Curved.Basic

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Statements to prove: every length measure has exactly one connection

**Nothing in this file is a proof of the statements it names.** These are the first two
statements of the work on curvature on curved spaces. They are definitions of type `Prop`; a
proof of one of them is a theorem of that type, written in another file.

**Rule for anyone proving these: this file is not to be changed.** A statement that is too hard
is reported, not weakened.

`Basic.lean` says what "the connection that belongs to a length measure" means
(`IsConnectionOf`), but not that there is one, nor that there is only one. The textbooks prove
both from one formula (Koszul's). Lean's standard library does the same for length measures that
give every step a positive length; a space-time has a time direction, so that proof has to be
redone with "no step is at right angles to all steps" in place of "all lengths are positive".

* `ConnectionExistsStatement`: a length measure on an open region has a connection there.
* `ConnectionUniqueStatement`: two connections of the same length measure agree on every field of
  arrows that can be differentiated.

Both are known to hold for every good table of functions on flat coordinate space, where the
textbooks' formula gives the connection (`IsRegularTableOn.isConnectionOf` in `Tables.lean`). So
the first statement is not about nothing.
-/

@[expose] public section

namespace GravityInLean.Curved

open Bundle

open scoped Manifold ContDiff

/-- **Statement: a length measure has a connection.** On an open region where `g` is a length
measure (symmetric, no step at right angles to all steps, smooth), there is a connection that
belongs to `g`. -/
def ConnectionExistsStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (H : Type) [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : LengthMeasure I M) (s : Set M), IsOpen s → IsLengthMeasureOn g s →
    ∃ cov : Transport I M, IsConnectionOf g cov s

/-- **Statement: and only one.** Two connections that belong to the same length measure on an
open region give the same answer for every field of arrows that can be differentiated at the
point in question. (For fields that cannot be differentiated a connection is free to give
anything, so nothing can be said there.) -/
def ConnectionUniqueStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (H : Type) [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : LengthMeasure I M) (s : Set M) (cov cov' : Transport I M),
    IsOpen s → IsLengthMeasureOn g s → IsConnectionOf g cov s → IsConnectionOf g cov' s →
    ∀ x ∈ s, ∀ Y : Arrows I M, MDiffAt (T% Y) x → cov Y x = cov' Y x

end GravityInLean.Curved
