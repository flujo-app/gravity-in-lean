/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.Tests
public import GravityInLean.BothWays.NoCoordinates

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Tests 7 and 8: de Sitter's space-time

Board item `task:checks-desitter`. Three statements of `Goals/Tests.lean`:

* `Curved.Tests.deSitterIsRoundOn`: de Sitter's space-time looks the same from every side;
* `Curved.Tests.deSitterUsable`: the size of its spheres is a usable distance;
* `Curved.Tests.deSitterNotSchwarzschild`: there is no chart around any of its points in which
  it is Schwarzschild's, for any mass.

With the older `deSitter_isSpaceTimeOn` and `deSitter_not_isEmptyOn`, the first two say that de
Sitter's space-time meets every assumption of Birkhoff's theorem except "empty".

"Looks the same from every side" is proved once for every round table, with any clock and ruler
functions (`Checks.DeSitter.round_isRoundOn`), and then used for de Sitter's.

The third goes across a real change of charts. If de Sitter's length measure were
Schwarzschild's in a chart around a point, it would be empty near that point
(`schwarzschildIsEmpty`: "empty" comes back from the chart to the space). But the curvature of
de Sitter's table is `3 / L²` times the table at every point, and the table is not zero.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean

open Real Set

open scoped Manifold ContDiff

namespace Checks.DeSitter

open GravityInLean.Curved

section Mono

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The connection of a length measure on a region is its connection on every smaller open
region. -/
theorem isConnectionOf_mono {g : LengthMeasure I M} {cov : Transport I M} {s t : Set M}
    (h : IsConnectionOf g cov s) (ht : IsOpen t) (hts : t ⊆ s) : IsConnectionOf g cov t where
  isOpen := ht
  isConnection := h.isConnection.mono hts
  noTwist := fun x hx ↦ h.noTwist x (hts hx)
  keepsLengths := fun x hx ↦ h.keepsLengths x (hts hx)

/-- Space that is empty on a region is empty on every smaller open region. -/
theorem isEmptyOn_mono [FiniteDimensional ℝ E] {g : LengthMeasure I M} {s t : Set M}
    (h : Curved.IsEmptyOn g s) (ht : IsOpen t) (hts : t ⊆ s) : Curved.IsEmptyOn g t := by
  obtain ⟨cov, hcov, hric⟩ := h
  exact ⟨cov, isConnectionOf_mono hcov ht hts, fun x hx ↦ hric x (hts hx)⟩

end Mono

/-- Every round table, whatever its clock and ruler functions, is unchanged by the three turns
of ordinary space, away from the poles. -/
theorem roundG_isRoundAt (A B : ℝ → ℝ) {p : Coords 4} (hs : sin (p 2) ≠ 0) :
    IsRoundAt (roundG A B) p := by
  have e : roundG A B = genG (fun _ r => A r) (fun _ r => B r) zero2 (onlyR sqF) := by
    rw [genG_diagonal, changingG_static]
  rw [e]
  exact genG_isRound _ _ _ _ hs

/-- **Every round table looks the same from every side,** in the sense of `Basic.lean`, on an
open region away from the centre and the poles on which its entries can be differentiated: the
three turns of ordinary space are smooth, leave the length measure unchanged, combine the way
turns do, and sweep out surfaces on which all lengths are positive. Nothing is asked of the
clock and ruler functions beyond that. -/
theorem round_isRoundOn (A B : ℝ → ℝ) {s : Set (Coords 4)} (hs : IsOpen s)
    (hgood : ∀ x ∈ s, x 1 ≠ 0 ∧ sin (x 2) ≠ 0)
    (hg : ∀ x ∈ s, ∀ a b, DifferentiableAt ℝ (roundG A B a b) x) :
    IsRoundOn (flatMeasure (tableMeasure (roundG A B))) turns s where
  isOpen := hs
  smooth := by
    intro i
    fin_cases i
    · exact contMDiffOn_arrows_iff.mpr (contDiffOn_pi.2 fun k x hx ↦
        (smooth_rotY (z := x) (hgood x hx).2 k).contDiffWithinAt)
    · exact contMDiffOn_arrows_iff.mpr (contDiffOn_pi.2 fun k x hx ↦
        (smooth_rotX (z := x) (hgood x hx).2 k).contDiffWithinAt)
    · exact contMDiffOn_arrows_iff.mpr (contDiffOn_pi.2 fun k x _ ↦
        (smooth_rotZ x k).contDiffWithinAt)
  unchanged := by
    intro i x hx
    have hsin := (hgood x hx).2
    have hround := roundG_isRoundAt A B hsin
    fin_cases i
    · exact (leavesUnchangedAt_table_iff (hg x hx) (differentiableAt_rotY hsin)).mpr hround.2.1
    · exact (leavesUnchangedAt_table_iff (hg x hx) (differentiableAt_rotX hsin)).mpr hround.1
    · exact (leavesUnchangedAt_table_iff (hg x hx) (differentiableAt_rotZ x)).mpr hround.2.2
  likeTurns := fun x hx ↦
    ⟨bracket_rotY_rotX (hgood x hx).2, bracket_rotX_rotZ (hgood x hx).2,
      bracket_rotZ_rotY (hgood x hx).2⟩
  surfaces := fun x _ ↦ by
    have h := finrank_span_angles
    rw [← span_turns x] at h
    exact h
  positive := fun x hx v hv hne ↦ by
    have hv' : (v : Coords 4)
        ∈ Submodule.span ℝ (Set.range fun i : Fin 3 ↦ (turns i x : Coords 4)) := hv
    rw [span_turns] at hv'
    exact round_pos_on_angles (hgood x hx).1 (hgood x hx).2 v hv' hne

/-- The sphere entry of de Sitter's table is the square of the distance label. -/
theorem deSitter_sphereEntry (L : ℝ) (x : Coords 4) :
    roundG (dsA L) (dsB L) 2 2 x = x 1 ^ 2 := by
  simp [roundG, diag, roundDiag, sep, gr, gθ, sqF, constOne]

/-- **De Sitter's table is not empty at any point of its region:** one part of its curvature,
the one for the first angle taken twice, is `3 / L²` times the square of the distance label,
which is not zero. -/
theorem deSitter_not_ricciFlatAt {L : ℝ} (hL : 0 < L) {x : Coords 4}
    (hx : x ∈ deSitterRegion L) :
    ¬ IsRicciFlatAt (roundG (dsA L) (dsB L)) (roundGinv (dsA L) (dsB L)) x := by
  intro hflat
  have h1 : ricci (christoffel (roundG (dsA L) (dsB L)) (roundGinv (dsA L) (dsB L))) 2 2 x = 0 :=
    hflat 2 2
  rw [ricci_deSitter hx.1 hx.2.1 hx.2.2, deSitter_sphereEntry] at h1
  exact mul_ne_zero (div_ne_zero three_ne_zero (pow_ne_zero 2 hL.ne'))
    (pow_ne_zero 2 hx.1.ne') h1

/-- **De Sitter's space-time is not empty on any open region around any of its points.** The
older `deSitter_not_isEmptyOn` says so for the whole region only. -/
theorem deSitter_not_isEmptyOn_near {L : ℝ} (hL : 0 < L) {p : Coords 4}
    (hp : p ∈ deSitterRegion L) {u : Set (Coords 4)} (hu : IsOpen u) (hpu : p ∈ u) :
    ¬ Curved.IsEmptyOn (flatMeasure (tableMeasure (roundG (dsA L) (dsB L)))) u := by
  intro hempty
  have ht : IsOpen (u ∩ deSitterRegion L) := hu.inter (isOpen_deSitterRegion L)
  have hreg := BothWays.isRegularTableOn_mono (deSitter_regularTable L) ht inter_subset_right
  have hflat := hreg.isEmptyOn_iff.mp
    (isEmptyOn_mono (I := 𝓘(ℝ, Coords 4)) hempty ht inter_subset_left)
  exact deSitter_not_ricciFlatAt hL hp (hflat p ⟨hpu, hp⟩)

end Checks.DeSitter

namespace Curved.Tests

open Checks.DeSitter

/-- **Test 7, first half.** De Sitter's space-time looks the same from every side on its
region, for every radius `L`. -/
theorem deSitterIsRoundOn : DeSitterIsRoundOn := fun L ↦
  round_isRoundOn (dsA L) (dsB L) (isOpen_deSitterRegion L) (fun _ hx ↦ ⟨hx.1.ne', hx.2.2⟩)
    fun _ hx a b ↦ (deSitter_regularTable L).differentiableAt hx a b

/-- **Test 7, second half.** At every point of de Sitter's region the size of the spheres is a
usable distance. -/
theorem deSitterUsable : DeSitterUsable := fun L _ hx ↦
  round_usable (dsA L) (dsB L) hx.1.ne' (inv_ne_zero (dsA_pos hx.1 hx.2.1).ne') hx.2.2

/-- **Test 8.** Around no point of de Sitter's region is there a chart in which de Sitter's
length measure is Schwarzschild's, for any mass. If there were one, de Sitter's space-time would
be empty near the point, and it is not empty near any point. -/
theorem deSitterNotSchwarzschild : DeSitterNotSchwarzschild := by
  intro L hL p hp hnear
  obtain ⟨u, hu, hpu, hempty⟩ := schwarzschildIsEmpty (Coords 4) _ p hnear
  exact deSitter_not_isEmptyOn_near hL hp hu hpu hempty

end Curved.Tests

end GravityInLean
