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
# The mass at a point, said without coordinates

Board item `task:checks-mass-def`. For the statement "one mass for a whole region"
(`Goals/OneMass.lean`) every point of the region needs a mass of its own that does not depend on
any coordinates. The textbooks' formula is `(r / 2) · (1 - |slope of r|²)`, where `r²` is the
size of the spheres. Written with the squared size `σ = r²` and with the squared length `N` of
the slope of `σ` (so `|slope of r|² = N / (4 σ)`), it is `massOf σ N`.

* `massOf`: the formula;
* `MassAt g ξ p m`: at the point `p` the formula gives the mass `m`;
* `massAt_unique`: where no step is at right angles to all steps, a point has at most one mass.
-/

@[expose] public section

namespace GravityInLean.Mass

open GravityInLean.Curved

open Real

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The mass read off the squared size `σ` of a sphere and the squared length `N` of the slope of
the squared size: `(√σ / 2) · (1 - N / (4 σ))`. -/
noncomputable def massOf (σ N : ℝ) : ℝ := √σ / 2 * (1 - N / (4 * σ))

/-- **The mass at the point `p` is `m`.** There is a step `n` at `p` that points the way the
spheres grow (it turns the length measure into the slope of `sizeSq`, as in `UsableDistanceAt`),
and the formula `massOf`, fed with the squared size of the sphere through `p` and the squared
length of `n`, gives `m`. The squared length of `n` may be zero here. -/
def MassAt (g : LengthMeasure I M) (ξ : Fin 3 → Arrows I M) (p : M) (m : ℝ) : Prop :=
  ∃ n : TangentSpace I p,
    (∀ w : TangentSpace I p, g p n w = d% (sizeSq g ξ) p w) ∧ massOf (sizeSq g ξ p) (g p n n) = m

/-- **A point has at most one mass,** if no step at it is at right angles to all steps: the step
that points the way the spheres grow is then fixed by the slope of their size. -/
theorem massAt_unique {g : LengthMeasure I M} {ξ : Fin 3 → Arrows I M} {p : M} {m m' : ℝ}
    (hnd : Nondegenerate fun v w : TangentSpace I p ↦ g p v w)
    (h : MassAt g ξ p m) (h' : MassAt g ξ p m') : m = m' := by
  obtain ⟨n, hn, rfl⟩ := h
  obtain ⟨n', hn', rfl⟩ := h'
  have e : n - n' = 0 := hnd (n - n') fun w ↦ by
    change g p (n - n') w = 0
    rw [map_sub, sub_apply, hn w, hn' w, sub_self]
  rw [sub_eq_zero.mp e]

end GravityInLean.Mass
