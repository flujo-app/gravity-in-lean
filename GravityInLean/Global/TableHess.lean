/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.Kretschmann

import Mathlib.Tactic

/-!
# The slope and the second slope of a function, measured with a table

Two more definitions that the proof of uniqueness of the length-keeping map shares.

* `gradSq g ginv F x`: the squared length of the slope of the function `F`, measured with the
  table `g` (through its inverse table).
* `hessT g ginv F a b x`: the second slope of `F` that belongs to the table `g` (the Hessian of
  the textbooks, `∂ₐ∂_b F - Γᶜₐ_b ∂_c F`).
-/

@[expose] public section

namespace GravityInLean.Curved

/-- **The squared length of the slope of `F`,** measured with the table whose inverse is
`ginv`: `Σ g⁻¹(a, b) · ∂ₐF · ∂_bF`. -/
noncomputable def gradSq {n : ℕ} (ginv : Fin n → Fin n → Coords n → ℝ) (F : Coords n → ℝ)
    (x : Coords n) : ℝ :=
  ∑ a, ∑ b, ginv a b x * slope a F x * slope b F x

/-- **The second slope of `F` that belongs to the table `g`** (the Hessian): the plain second
slope, corrected by the connection of `g`: `∂ₐ∂_b F - Σ Γᶜₐ_b ∂_c F`. -/
noncomputable def hessT {n : ℕ} (g ginv : Fin n → Fin n → Coords n → ℝ) (F : Coords n → ℝ)
    (a b : Fin n) (x : Coords n) : ℝ :=
  slope a (slope b F) x - ∑ c, christoffel g ginv c a b x * slope c F x

end GravityInLean.Curved
