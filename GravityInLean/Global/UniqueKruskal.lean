/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.KruskalPlane
public import GravityInLean.Global.SphereRigid
public import GravityInLean.Global.KruskalChart

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Two length-keeping maps into Kruskal's differ by a symmetry near every point
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

/-- **A map of coordinate space that keeps Kruskal's table is a symmetry of Kruskal's whole
space-time, near every point:** after wrapping round the sphere, it is `kruskalSym L R`. -/
theorem KeepsKruskalOn.local {m : ℝ} {f : Coords 4 → Coords 4} {W : Set (Coords 4)}
    {x₀ : Coords 4} (hm : 0 < m) (h : KeepsKruskalOn m f W) (hx₀ : x₀ ∈ W) :
    ∃ (L : Matrix (Fin 2) (Fin 2) ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ),
      L.transpose * lightSign2 * L = lightSign2 ∧ R.transpose * R = 1 ∧
        ∀ᶠ x in 𝓝 x₀, kruskalWrap (f x) = kruskalSym L R (kruskalWrap x) := by
  sorry

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  [IsManifold 𝓘(ℝ, Coords 4) ∞ M] {m : ℝ} {g : LengthMeasure 𝓘(ℝ, Coords 4) M} {s : Set M}

/-- **Two length-keeping maps into Kruskal's differ by a symmetry near every point of the
region.** -/
theorem IsKruskalMapOn.local_unique {D D' : M → Coords 5} (hm : 0 < m)
    (hD : IsKruskalMapOn m g D s) (hD' : IsKruskalMapOn m g D' s) (hg : IsSpaceTimeOn g s)
    {q : M} (hq : q ∈ s) :
    ∃ (L : Matrix (Fin 2) (Fin 2) ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ),
      L.transpose * lightSign2 * L = lightSign2 ∧ R.transpose * R = 1 ∧
        ∀ᶠ q' in 𝓝 q, D' q' = kruskalSym L R (D q') := by
  sorry

/-- **A symmetry is fixed by what it does to a length-keeping map near one point.** -/
theorem IsKruskalMapOn.sym_unique {D : M → Coords 5} (hD : IsKruskalMapOn m g D s)
    (hg : IsSpaceTimeOn g s) {q : M} (hq : q ∈ s)
    {L L' : Matrix (Fin 2) (Fin 2) ℝ} {R R' : Matrix (Fin 3) (Fin 3) ℝ}
    (h : ∀ᶠ q' in 𝓝 q, kruskalSym L R (D q') = kruskalSym L' R' (D q')) : L = L' ∧ R = R' := by
  sorry

/-- **Two length-keeping maps into Kruskal's on a region in one piece differ by one symmetry:**
the first part of `GlobalBirkhoffUnique`. -/
theorem unique_kruskal (hs : IsPreconnected s) (hg : IsSpaceTimeOn g s) (hm : 0 < m)
    (D D' : M → Coords 5) (hD : IsKruskalMapOn m g D s) (hD' : IsKruskalMapOn m g D' s) :
    ∃ (L : Matrix (Fin 2) (Fin 2) ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ),
      L.transpose * lightSign2 * L = lightSign2 ∧ R.transpose * R = 1 ∧
        ∀ q ∈ s, D' q = kruskalSym L R (D q) := by
  sorry

end GravityInLean.Curved
