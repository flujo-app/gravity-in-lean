/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.NewCoordinates
public import GravityInLean.Curved.Tables

import Mathlib.Tactic

/-!
# The curvature scalar of a table, and maps of coordinate space that carry one table to another

Two definitions that the proof of uniqueness of the length-keeping map shares.

* `kretschmann g ginv x`: the full curvature of the table `g`, contracted with itself (up to
  sign, the scalar that the textbooks name after Kretschmann). For Schwarzschild's and Kruskal's
  tables it is a fixed multiple of `m² / r⁶`, so it tells the radius.
* `CarriesTableAt g h f x`: near `x` the map `f` of coordinate space is smooth and the length of
  two steps in the table `g` is the length in the table `h` of the steps as `f` carries them.
-/

@[expose] public section

namespace GravityInLean.Curved

open scoped ContDiff Topology

/-- **The curvature scalar of a table:** the full curvature (one table of numbers `riemM` for
each pair of directions) multiplied with itself and summed over the directions with the inverse
table: `Σ g⁻¹(ρ, σ) g⁻¹(μ, τ) · trace (riemM ρ μ · riemM σ τ)`. -/
noncomputable def kretschmann {n : ℕ} (g ginv : Fin n → Fin n → Coords n → ℝ) (x : Coords n) :
    ℝ :=
  ∑ ρ, ∑ μ, ∑ σ, ∑ τ, ginv ρ σ x * ginv μ τ x *
    (riemM (christoffel g ginv) ρ μ x * riemM (christoffel g ginv) σ τ x).trace

/-- **The map `f` carries the table `g` to the table `h` near `x`:** `f` is smooth at `x`, and
at every point `y` near `x` the length of two steps measured with `g` is the length, measured
with `h` at `f y`, of the steps as `f` carries them. -/
def CarriesTableAt {n : ℕ} (g h : Fin n → Fin n → Coords n → ℝ) (f : Coords n → Coords n)
    (x : Coords n) : Prop :=
  ContDiffAt ℝ ∞ f x ∧ ∀ᶠ y in 𝓝 x, ∀ u v : Coords n,
    tableMeasure h (f y) (fderiv ℝ f y u) (fderiv ℝ f y v) = tableMeasure g y u v

end GravityInLean.Curved
