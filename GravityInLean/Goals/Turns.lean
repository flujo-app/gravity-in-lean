/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Curved.KnownAnswers
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Statements to prove: coordinates that fit the turns

**Nothing in this file is a proof of the statements it names.** It fixes, in exact form, what has
to be proved to remove the last shortcut of step 2 (issue 20): that coordinates in which the
three turns move only the two angles always exist. The statements are definitions of type `Prop`.
A proof of one of them is a theorem of that type, written in another file.

**Rule for anyone proving these: this file is not to be changed.** A statement that is too hard
is reported, not weakened.

Two statements:

* `SmoothFlowStatement`: following a smooth field of arrows for a time `t` is a smooth function
  of `t` and of the starting point together. Lean's standard library has the paths, but not that
  they depend smoothly on where they start.
* `TurnsCoordinatesStatement`: the goal of issue 20. Start from any good table of functions and
  three fields of arrows that leave it unchanged, combine the way turns do, and sweep out
  surfaces on which all lengths are positive (`TurnsOn`). Then around every point there are new
  coordinates in which the three fields, after one fixed rotation among themselves, are exactly
  the three standard turns `rotY`, `rotX`, `rotZ`.

Each statement comes with a check that it is not about nothing, and that its conclusion is formed
the right way round: `smoothFlow_const` (a field that is the same everywhere),
`schwarzschild_turnsOn` and `turnsCoordinates_schwarzschild` (Schwarzschild's own coordinates
already fit the turns, with the change of coordinates that does nothing).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean

open Real Filter Topology Set

open scoped Manifold ContDiff

/-! ## Statement 1: paths along a field depend smoothly on where they start -/

/-- **Statement 1.** Let `X` be a smooth field of arrows on an open region `U` of a space of
vectors, and `x₀` a point of `U`. Then there are a time span `ε` and a function `flow` such that,
for starting points `x` within `ε` of `x₀` and times `t` between `-ε` and `ε`:

* `flow t x` is smooth as a function of `t` and `x` together;
* `flow 0 x = x`: at time zero nothing has moved;
* `flow t x` stays in `U`, and moves with the velocity the field gives at the place it has
  reached. -/
def SmoothFlowStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (X : E → E) (U : Set E), IsOpen U → ContDiffOn ℝ ∞ X U → ∀ x₀ ∈ U,
    ∃ (ε : ℝ) (flow : ℝ → E → E), 0 < ε ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ flow p.1 p.2) (Ioo (-ε) ε ×ˢ Metric.ball x₀ ε) ∧
      (∀ x ∈ Metric.ball x₀ ε, flow 0 x = x) ∧
      ∀ x ∈ Metric.ball x₀ ε, ∀ t ∈ Ioo (-ε) ε,
        flow t x ∈ U ∧ HasDerivAt (fun r ↦ flow r x) (X (flow t x)) t

/-- The conclusion of statement 1 holds for a field that is the same everywhere: the path is a
straight line. So the statement is formed the right way round. -/
theorem smoothFlow_const (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (v x₀ : E) :
    ∃ (ε : ℝ) (flow : ℝ → E → E), 0 < ε ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ flow p.1 p.2) (Ioo (-ε) ε ×ˢ Metric.ball x₀ ε) ∧
      (∀ x ∈ Metric.ball x₀ ε, flow 0 x = x) ∧
      ∀ x ∈ Metric.ball x₀ ε, ∀ t ∈ Ioo (-ε) ε,
        flow t x ∈ (Set.univ : Set E) ∧ HasDerivAt (fun r ↦ flow r x) ((fun _ ↦ v) (flow t x)) t := by
  refine ⟨1, fun t x ↦ x + t • v, one_pos, ?_, fun x _ ↦ by simp, fun x _ t _ ↦ ⟨mem_univ _, ?_⟩⟩
  · exact (contDiff_snd.add (contDiff_fst.smul contDiff_const)).contDiffOn
  · simpa using ((hasDerivAt_id t).smul_const v).const_add x

/-! ## The bracket of two fields, in coordinates -/

/-- **The bracket of two fields of arrows given by their parts,** part `k`: how `Y` changes along
`X`, minus how `X` changes along `Y`. `mlieBracket_fieldOf_eq` shows that this is the bracket of
the standard library. -/
noncomputable def bracketOf {n : ℕ} (X Y : Fin n → Coords n → ℝ) (k : Fin n) (x : Coords n) : ℝ :=
  ∑ m, X m x * slope m (Y k) x - ∑ m, Y m x * slope m (X k) x

theorem mlieBracket_fieldOf_eq {n : ℕ} {X Y : Fin n → Coords n → ℝ} {x : Coords n}
    (hX : ∀ k, DifferentiableAt ℝ (X k) x) (hY : ∀ k, DifferentiableAt ℝ (Y k) x) (k : Fin n) :
    VectorField.mlieBracket 𝓘(ℝ, Coords n) (Curved.fieldOf X) (Curved.fieldOf Y) x k
      = bracketOf X Y k x :=
  Curved.mlieBracket_fieldOf hX hY k

/-! ## Statement 2: coordinates that fit the turns -/

/-- The three standard turns of `Symmetry.lean`, in the order in which the bracket of two of them
is the third. -/
noncomputable def stdTurn : Fin 3 → Fin 4 → Coords 4 → ℝ := ![rotY, rotX, rotZ]

/-- **Three fields that turn,** for a table of functions `g` on a region `s`: what issue 20 starts
from. The three fields `ξ 0`, `ξ 1`, `ξ 2`, given by their parts,

* are smooth;
* each leave `g` unchanged (Killing's equation, as in `Symmetry.lean`);
* combine the way turns do: the bracket of two of them is the third;
* sweep out surfaces: at each point they span two directions;
* and on these surfaces all lengths are positive.

Nothing is said about what the coordinates mean. -/
structure TurnsOn (g : Fin 4 → Fin 4 → Coords 4 → ℝ) (ξ : Fin 3 → Fin 4 → Coords 4 → ℝ)
    (s : Set (Coords 4)) : Prop where
  /-- The three fields are smooth. -/
  smooth : ∀ i k, ContDiffOn ℝ ∞ (ξ i k) s
  /-- Each leaves the table unchanged. -/
  unchanged : ∀ i, ∀ x ∈ s, LeavesUnchangedAt g (ξ i) x
  /-- They combine the way turns do. -/
  likeTurns : ∀ x ∈ s, ∀ k, bracketOf (ξ 0) (ξ 1) k x = ξ 2 k x ∧
    bracketOf (ξ 1) (ξ 2) k x = ξ 0 k x ∧ bracketOf (ξ 2) (ξ 0) k x = ξ 1 k x
  /-- They sweep out surfaces. -/
  surfaces : ∀ x ∈ s, Module.finrank ℝ
    (Submodule.span ℝ (Set.range fun i ↦ (fun k ↦ ξ i k x : Coords 4))) = 2
  /-- On these surfaces all lengths are positive. -/
  positive : ∀ x ∈ s, ∀ v ∈ Submodule.span ℝ (Set.range fun i ↦ (fun k ↦ ξ i k x : Coords 4)),
    v ≠ 0 → 0 < ∑ a, ∑ b, g a b x * v a * v b

/-- **Statement 2: coordinates that fit the turns exist.** Take a table of functions `g` that is
good on a region `s` (`IsRegularTableOn`: smooth, symmetric, with an inverse) and three fields
that turn (`TurnsOn`). Then for every point `p` of the region there are

* a change of coordinates `Φ` (new coordinates in, old coordinates out), smooth on an open set
  `W` of new coordinates, which hits `p`, stays inside the region, and loses no direction;
* one fixed rotation `R` of the three fields among themselves;

such that, in the new coordinates, the rotated fields are exactly the three standard turns: the
table of slopes of `Φ` turns `stdTurn i` at `y` into `∑ j, R i j * ξ j` at `Φ y`. The new
coordinates stay away from the poles.

With this, `shape_of_round` and `birkhoff_of_round` apply in the new coordinates, and the "any
coordinates" theorems carry everything back. -/
def TurnsCoordinatesStatement : Prop :=
  ∀ (g ginv : Fin 4 → Fin 4 → Coords 4 → ℝ) (ξ : Fin 3 → Fin 4 → Coords 4 → ℝ)
    (s : Set (Coords 4)), Curved.IsRegularTableOn g ginv s → TurnsOn g ξ s → ∀ p ∈ s,
    ∃ (Φ : Coords 4 → Coords 4) (R : Matrix (Fin 3) (Fin 3) ℝ) (W : Set (Coords 4))
      (y₀ : Coords 4),
      IsOpen W ∧ y₀ ∈ W ∧ Φ y₀ = p ∧ (∀ y ∈ W, Φ y ∈ s) ∧ ContDiffOn ℝ ∞ Φ W ∧
      R * R.transpose = 1 ∧ R.det = 1 ∧
      (∀ y ∈ W, sin (y 2) ≠ 0 ∧ (tab (jac Φ) y).det ≠ 0) ∧
      ∀ y ∈ W, ∀ i α, ∑ μ, jac Φ α μ y * stdTurn i μ y = ∑ j, R i j * ξ j α (Φ y)

end GravityInLean
