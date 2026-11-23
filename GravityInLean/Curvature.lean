/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Algebra.BigOperators.Fin

import Mathlib.Tactic

/-!
# Curvature and free fall, from coordinates: the general definitions

The standard library has no curvature yet, so this file states the classic textbook formulas as
definitions. They work for any number of coordinates, so they cover a space-time as well as a
sphere.

* `slope i f x`: how fast `f` changes when only coordinate `i` moves.
* `christoffel g ginv`: the "connection" that belongs to a way of measuring lengths `g`.
  It says how straight lines look in the chosen coordinates.
* `ricci Γ`: the curvature built from a connection.
* `IsRicciFlatAt g ginv x`: every part of that curvature vanishes at `x`. This is Einstein's
  equation for empty space.
* `IsFreeFallAt Γ γ τ`: the path `γ` falls freely at the moment `τ`. It bends exactly as the
  connection says and has no push of its own.
* `KeepsOwnTimeAt g γ τ`: the path is timed by a clock that travels along it.

What this file does **not** do: connect these formulas to the abstract geometry in the standard
library. They are the definitions every textbook computes with, taken here as the starting point.
-/

@[expose] public section

namespace GravityInLean

/-- A point described by `n` coordinates. -/
abbrev Coords (n : ℕ) := Fin n → ℝ

/-- How fast `f` changes at `x` when only coordinate `i` moves. -/
noncomputable def slope {n : ℕ} (i : Fin n) (f : Coords n → ℝ) (x : Coords n) : ℝ :=
  deriv (fun s => f (Function.update x i s)) (x i)

/-- If `f` only looks at coordinate `i`, its slope along `i` is the ordinary slope. -/
theorem slope_along {n : ℕ} (i : Fin n) (F : ℝ → ℝ) (x : Coords n) :
    slope i (fun y => F (y i)) x = deriv F (x i) := by
  simp [slope]

/-- If `f` only looks at another coordinate `j`, it does not change along `i`. -/
theorem slope_across {n : ℕ} {i j : Fin n} (h : j ≠ i) (F : ℝ → ℝ) (x : Coords n) :
    slope i (fun y => F (y j)) x = 0 := by
  simp [slope, Function.update_of_ne h]

/-- Something that is the same everywhere has no slope. -/
theorem slope_const {n : ℕ} (i : Fin n) (c : ℝ) (x : Coords n) :
    slope i (fun _ => c) x = 0 := by
  simp [slope]

/-- The connection belonging to a length measure `g` with inverse `ginv`
(the Christoffel symbols of the textbooks). -/
noncomputable def christoffel {n : ℕ} (g ginv : Fin n → Fin n → Coords n → ℝ)
    (a b c : Fin n) : Coords n → ℝ := fun x =>
  (1 / 2) * ∑ d, ginv a d x * (slope b (g d c) x + slope c (g d b) x - slope d (g b c) x)

/-- The curvature built from a connection `Γ` (the Ricci tensor of the textbooks). -/
noncomputable def ricci {n : ℕ} (Γ : Fin n → Fin n → Fin n → Coords n → ℝ)
    (b c : Fin n) (x : Coords n) : ℝ :=
  ∑ a, slope a (Γ a b c) x - ∑ a, slope c (Γ a b a) x
    + ∑ a, ∑ d, Γ a a d x * Γ d b c x - ∑ a, ∑ d, Γ a c d x * Γ d b a x

/-- Einstein's equation for empty space at the point `x`: every part of the curvature that
belongs to the length measure `g` vanishes there. -/
def IsRicciFlatAt {n : ℕ} (g ginv : Fin n → Fin n → Coords n → ℝ) (x : Coords n) : Prop :=
  ∀ i j, ricci (christoffel g ginv) i j x = 0

/-! ## Diagonal tables -/

/-- A table with the entries `G i` on the diagonal and zero everywhere else. -/
noncomputable def diag {n : ℕ} (G : Fin n → Coords n → ℝ) (i j : Fin n) (x : Coords n) : ℝ :=
  if i = j then G i x else 0

/-- The slope of an entry of a diagonal table: the slope of the diagonal entry, or zero. -/
theorem slope_diag {n : ℕ} (G : Fin n → Coords n → ℝ) (k i j : Fin n) (x : Coords n) :
    slope k (diag G i j) x = if i = j then slope k (G i) x else 0 := by
  by_cases h : i = j
  · subst h
    simp [slope, diag]
  · simp [slope, diag, h]

/-- When the inverse length measure is diagonal, the sum in the connection has a single term. -/
theorem christoffel_diag {n : ℕ} (g : Fin n → Fin n → Coords n → ℝ) (H : Fin n → Coords n → ℝ)
    (a b c : Fin n) (x : Coords n) :
    christoffel g (diag H) a b c x
      = (1 / 2) * (H a x * (slope b (g a c) x + slope c (g a b) x - slope a (g b c) x)) := by
  simp [christoffel, diag, Finset.sum_ite_eq]

/-! ## Free fall -/

/-- The left-hand side of the equation of free fall for coordinate `a`: how much the path bends
by itself, plus how much the connection says it should bend. -/
noncomputable def freeFallExpr {n : ℕ} (Γ : Fin n → Fin n → Fin n → Coords n → ℝ)
    (γ : ℝ → Coords n) (τ : ℝ) (a : Fin n) : ℝ :=
  deriv (deriv fun s => γ s a) τ
    + ∑ b, ∑ c, Γ a b c (γ τ) * deriv (fun s => γ s b) τ * deriv (fun s => γ s c) τ

/-- Free fall at the moment `τ`: the path `γ` bends exactly as the connection says, with no push
of its own (the geodesic equation of the textbooks). `τ` is the time shown by a clock that
travels along the path. -/
def IsFreeFallAt {n : ℕ} (Γ : Fin n → Fin n → Fin n → Coords n → ℝ) (γ : ℝ → Coords n)
    (τ : ℝ) : Prop :=
  ∀ a, freeFallExpr Γ γ τ a = 0

/-- The path is timed by its own clock: one second of `τ` is one second of the path's own time.
In the length measure `g` that reads "the step per second has length `-1`"; the minus sign marks
a step through time. -/
def KeepsOwnTimeAt {n : ℕ} (g : Fin n → Fin n → Coords n → ℝ) (γ : ℝ → Coords n)
    (τ : ℝ) : Prop :=
  ∑ a, ∑ b, g a b (γ τ) * deriv (fun s => γ s a) τ * deriv (fun s => γ s b) τ = -1

end GravityInLean
