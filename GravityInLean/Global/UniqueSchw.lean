/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.SchwKept
public import GravityInLean.Global.SphereRigid
public import GravityInLean.Global.SchwChart

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Two length-keeping maps into Schwarzschild's of negative mass differ by a symmetry
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

/-- **A map of coordinate space that keeps Schwarzschild's table of negative mass is a symmetry
of Schwarzschild's whole space-time, near every point:** in ordinary space labels it is
`schwSym ε c R`. -/
theorem KeepsSchwOn.local {m : ℝ} {f : Coords 4 → Coords 4} {W : Set (Coords 4)}
    {x₀ : Coords 4} (hm : m < 0) (h : KeepsSchwOn m f W) (hx₀ : x₀ ∈ W) :
    ∃ (ε c : ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ), (ε = 1 ∨ ε = -1) ∧ R.transpose * R = 1 ∧
      ∀ᶠ x in 𝓝 x₀, sphericalToSpace (f x) = schwSym ε c R (sphericalToSpace x) := by
  sorry

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  [IsManifold 𝓘(ℝ, Coords 4) ∞ M] {m : ℝ} {g : LengthMeasure 𝓘(ℝ, Coords 4) M} {s : Set M}

/-- **Two length-keeping maps into Schwarzschild's whole space-time of negative mass differ by
a symmetry near every point of the region.** -/
theorem IsSchwarzschildMapOn.local_unique {D D' : M → Coords 4} (hm : m < 0)
    (hD : IsSchwarzschildMapOn m g D s) (hD' : IsSchwarzschildMapOn m g D' s)
    (hg : IsSpaceTimeOn g s) {q : M} (hq : q ∈ s) :
    ∃ (ε c : ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ), (ε = 1 ∨ ε = -1) ∧ R.transpose * R = 1 ∧
      ∀ᶠ q' in 𝓝 q, D' q' = schwSym ε c R (D q') := by
  sorry

/-- **A symmetry is fixed by what it does to a length-keeping map near one point.** -/
theorem IsSchwarzschildMapOn.sym_unique {D : M → Coords 4} (hm : m < 0)
    (hD : IsSchwarzschildMapOn m g D s) (hg : IsSpaceTimeOn g s) {q : M} (hq : q ∈ s)
    {ε c ε' c' : ℝ} {R R' : Matrix (Fin 3) (Fin 3) ℝ}
    (h : ∀ᶠ q' in 𝓝 q, schwSym ε c R (D q') = schwSym ε' c' R' (D q')) :
    ε = ε' ∧ c = c' ∧ R = R' := by
  sorry

/-- **Two length-keeping maps into Schwarzschild's whole space-time of negative mass on a
region in one piece differ by one symmetry:** the second part of `GlobalBirkhoffUnique`. -/
theorem unique_schw (hs : IsPreconnected s) (hg : IsSpaceTimeOn g s) (hm : m < 0)
    (D D' : M → Coords 4) (hD : IsSchwarzschildMapOn m g D s)
    (hD' : IsSchwarzschildMapOn m g D' s) :
    ∃ (ε c : ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ), (ε = 1 ∨ ε = -1) ∧ R.transpose * R = 1 ∧
      ∀ q ∈ s, D' q = schwSym ε c R (D q) := by
  sorry

end GravityInLean.Curved
