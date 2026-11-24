/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.Checks

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# The symmetries of Schwarzschild's whole space-time are symmetries

A shift of time (possibly turned round) with a turn or mirror of space keeps the table
`schwSpaceG`; for mass zero so does every Lorentz transformation followed by a shift. So a
length-keeping map followed by such a symmetry is again length-keeping.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

section SchwSym

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  [IsManifold 𝓘(ℝ, Coords 4) ∞ M] {m : ℝ} {g : LengthMeasure 𝓘(ℝ, Coords 4) M} {s : Set M}
  {ε c : ℝ} {R : Matrix (Fin 3) (Fin 3) ℝ}

/-- A symmetry keeps the distance from the centre. -/
theorem schwSym_sumSq (hR : R.transpose * R = 1) (z : Coords 4) :
    schwSym ε c R z 1 ^ 2 + schwSym ε c R z 2 ^ 2 + schwSym ε c R z 3 ^ 2
      = z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 := by
  sorry

/-- A symmetry is smooth. -/
theorem contDiff_schwSym (ε c : ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) :
    ContDiff ℝ ∞ (schwSym ε c R) := by
  sorry

/-- **A symmetry keeps Schwarzschild's lengths,** steps carried by its derivative. -/
theorem schwSym_measure (m : ℝ) (hε : ε = 1 ∨ ε = -1) (hR : R.transpose * R = 1)
    (z u w : Coords 4) :
    tableMeasure (schwSpaceG m) (schwSym ε c R z) (fderiv ℝ (schwSym ε c R) z u)
        (fderiv ℝ (schwSym ε c R) z w) = tableMeasure (schwSpaceG m) z u w := by
  sorry

/-- **A length-keeping map into Schwarzschild's whole space-time, followed by a symmetry, is
again one.** -/
theorem IsSchwarzschildMapOn.sym {D : M → Coords 4} (hD : IsSchwarzschildMapOn m g D s)
    (hε : ε = 1 ∨ ε = -1) (hR : R.transpose * R = 1) :
    IsSchwarzschildMapOn m g (fun q ↦ schwSym ε c R (D q)) s := by
  sorry

/-- **A length-keeping map into flat space-time, followed by a Lorentz transformation and a
shift, is again one.** -/
theorem IsSchwarzschildMapOn.lorentz {D : M → Coords 4} (hD : IsSchwarzschildMapOn 0 g D s)
    {Λ : Matrix (Fin 4) (Fin 4) ℝ} (hΛ : Λ.transpose * lightSign4 * Λ = lightSign4)
    (b : Coords 4) : IsSchwarzschildMapOn 0 g (fun q ↦ Λ.mulVec (D q) + b) s := by
  sorry

end SchwSym

end GravityInLean.Curved
