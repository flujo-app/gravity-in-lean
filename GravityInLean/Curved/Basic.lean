/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.QuadraticDiscriminant

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Gravity on a curved space, with no coordinates given

Everything else in this project computes with coordinates. This file says what the same notions
mean on a curved space (a manifold of the standard library) where no coordinates are singled out.
It contains definitions only. They are the starting point for the proof of Birkhoff's theorem with
no coordinates at all, and nothing may be built on them before they have been tested on cases with
known answers. Those tests are in `Flat.lean`, `Tables.lean` and `KnownAnswers.lean`.

The words used here, and the textbooks' words for them:

| here | textbooks |
|---|---|
| a step at a point | a tangent vector |
| a field of arrows | a vector field |
| a length measure | a metric (a symmetric two-slot function on steps) |
| one time direction | Lorentzian signature |
| the connection of a length measure | the Levi-Civita connection |
| the full curvature | the Riemann tensor |
| the curvature | the Ricci tensor |
| empty | Ricci-flat: Einstein's equation without matter |
| a move that leaves the length measure unchanged | a Killing field |
| looks the same from every side | spherically symmetric |

**What is defined here.**

* `HasOneTimeDirection`: a two-slot function on steps that counts exactly one direction as time
  (`HasOneTimeDirection.not_orthogonal` shows that it is exactly one).
* `IsLengthMeasureOn`, `IsSpaceTimeOn`: a smooth length measure on a region, and one with a time
  direction.
* `IsConnectionOf`: the connection that belongs to a length measure.
* `curvatureOfFields`, `curvatureAt`, `ricciAt`, `IsEmptyOn`: curvature, and empty space.
* `LeavesUnchangedAt`: a field of arrows along which the length measure does not change.
* `IsRoundOn`: three such fields that combine the way turns do and sweep out surfaces on which all
  lengths are positive.

**Why regions.** Every notion is stated on a region `s` of the curved space, not on all of it.
For the whole space take `s = Set.univ`. Regions are needed because the known answers come in
coordinates that fail somewhere (at the poles, at the centre), and because Birkhoff's theorem is a
statement about the neighbourhood of a point.

**Regions are open.** Curvature at a point looks at the connection near that point, and a bracket
looks at the fields near the point. On a region with an edge these notions would say nothing at
the edge. So `IsConnectionOf` and `IsRoundOn` ask for an open region as part of their meaning.
-/

@[expose] public section

namespace GravityInLean.Curved

open Bundle FiberBundle VectorField

open scoped Manifold ContDiff Topology

/-! ## One time direction -/

section TimeDirection

variable {V : Type*} [Zero V]

/-- **One time direction.** `b` measures steps: `b v v` is the squared length of the step `v`, and
`b v w = 0` says that `v` and `w` are at right angles. There is a step `t` with negative squared
length (a step through time), and every other step at right angles to it has positive squared
length (a step through space). The textbooks call this Lorentzian signature. -/
def HasOneTimeDirection (b : V → V → ℝ) : Prop :=
  ∃ t : V, b t t < 0 ∧ ∀ v : V, b t v = 0 → v ≠ 0 → 0 < b v v

/-- No step is at right angles to every step. Without this, lengths could not be turned back into
steps, and a length measure would have no connection. -/
def Nondegenerate (b : V → V → ℝ) : Prop :=
  ∀ v : V, (∀ w : V, b v w = 0) → v = 0

/-- A symmetric measure with one time direction is nondegenerate. -/
theorem HasOneTimeDirection.nondegenerate {b : V → V → ℝ} (h : HasOneTimeDirection b)
    (hsymm : ∀ v w, b v w = b w v) : Nondegenerate b := by
  obtain ⟨t, _, hpos⟩ := h
  intro v hv
  by_contra hne
  have h1 : b t v = 0 := by rw [hsymm]; exact hv t
  have h2 := hpos v h1 hne
  rw [hv v] at h2
  exact lt_irrefl 0 h2

end TimeDirection

section OnlyOne

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **There is only one time direction.** If a symmetric two-slot function has one time direction
in the sense above, then two steps through time are never at right angles to each other. So the
steps through time do not contain two independent directions that the measure keeps apart: the
definition really says "one", not "at least one". -/
theorem HasOneTimeDirection.not_orthogonal {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
    (h : HasOneTimeDirection fun v w ↦ B v w) (hsymm : ∀ v w, B v w = B w v) {u w : V}
    (hu : B u u < 0) (hw : B w w < 0) : B u w ≠ 0 := by
  obtain ⟨t, ht, hpos⟩ := h
  have hnn : ∀ v, B t v = 0 → 0 ≤ B v v := fun v hv ↦ by
    by_cases h0 : v = 0
    · simp [h0]
    · exact (hpos v hv h0).le
  intro huw
  have hq : B t t ≠ 0 := ht.ne
  -- The parts of `u` and `w` at right angles to the time direction.
  have htu' : B t (u - (B t u / B t t) • t) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul]
    field_simp
    ring
  have htw' : B t (w - (B t w / B t t) • t) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul]
    field_simp
    ring
  set α := B t u / B t t with hα
  set β := B t w / B t t with hβ
  set u' := u - α • t with hu'
  set w' := w - β • t with hw'
  have hsu : B u' t = 0 := by rw [hsymm]; exact htu'
  have hsw : B w' t = 0 := by rw [hsymm]; exact htw'
  -- On these parts all squared lengths are at least zero: the Cauchy-Schwarz inequality.
  have hquad : ∀ l : ℝ, 0 ≤ B w' w' * (l * l) + 2 * B u' w' * l + B u' u' := fun l ↦ by
    have h1 := hnn (u' + l • w') (by simp [map_add, map_smul, htu', htw'])
    have e : B (u' + l • w') (u' + l • w')
        = B w' w' * (l * l) + 2 * B u' w' * l + B u' u' := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hsymm w' u']
      ring
    linarith
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  -- `u` and `w`, split into their parts.
  have eu : u = u' + α • t := by rw [hu']; abel
  have ew : w = w' + β • t := by rw [hw']; abel
  have e1 : B u u = B u' u' + α ^ 2 * B t t := by
    conv_lhs => rw [eu]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hsu,
      htu']
    ring
  have e2 : B w w = B w' w' + β ^ 2 * B t t := by
    conv_lhs => rw [ew]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hsw,
      htw']
    ring
  have e3 : B u w = B u' w' + α * β * B t t := by
    conv_lhs => rw [eu, ew]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hsu,
      htw']
    ring
  have ha0 : 0 ≤ B u' u' := hnn u' htu'
  have hb0 : 0 ≤ B w' w' := hnn w' htw'
  have ha : B u' u' < α ^ 2 * (-B t t) := by linarith
  have hb : B w' w' < β ^ 2 * (-B t t) := by linarith
  have hprod : B u' u' * B w' w' < α ^ 2 * (-B t t) * (β ^ 2 * (-B t t)) :=
    mul_lt_mul'' ha hb ha0 hb0
  have hx : B u' w' = -(α * β * B t t) := by linarith
  rw [hx] at hdisc
  nlinarith

end OnlyOne

/-! ## Length measures on a curved space -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- A field of arrows on the curved space `M`: at every point one step away from that point (a
vector field of the textbooks). -/
abbrev Arrows := Π x : M, TangentSpace I x

/-- A two-slot function on the steps at every point of `M`. With the conditions of
`IsLengthMeasureOn` it is a length measure: `g x v v` is the squared length of the step `v` taken
at `x`. -/
abbrev LengthMeasure := Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ

/-- A rule that says how a field of arrows changes from point to point: `cov σ x v` is the change
of the field `σ` at `x` along the step `v`. With the conditions of the standard library's
`IsCovariantDerivativeOn` it is a connection. -/
abbrev Transport :=
  (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)

variable {I M} [IsManifold I ∞ M]

/-- The length measure depends smoothly on the point, on the region `s`. Said as in the standard
library: `g` is a smooth section of the bundle of two-slot functions on steps. -/
def IsSmoothOn (g : LengthMeasure I M) (s : Set M) : Prop :=
  ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
    (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (g x)) s

/-- **A length measure on the region `s`** (a metric of the textbooks, of any signature): it does
not depend on the order of its two steps, no step is at right angles to all steps, and it depends
smoothly on the point. -/
structure IsLengthMeasureOn (g : LengthMeasure I M) (s : Set M) : Prop where
  /-- The order of the two steps does not matter. -/
  symm : ∀ x ∈ s, ∀ v w : TangentSpace I x, g x v w = g x w v
  /-- No step is at right angles to all steps. -/
  nondegenerate : ∀ x ∈ s, Nondegenerate fun v w : TangentSpace I x ↦ g x v w
  /-- It depends smoothly on the point. -/
  smooth : IsSmoothOn g s

/-- **A space-time on the region `s`:** a length measure that counts exactly one direction as
time, at every point of the region. -/
structure IsSpaceTimeOn (g : LengthMeasure I M) (s : Set M) : Prop where
  /-- The order of the two steps does not matter. -/
  symm : ∀ x ∈ s, ∀ v w : TangentSpace I x, g x v w = g x w v
  /-- One direction is time, the others are space. -/
  oneTime : ∀ x ∈ s, HasOneTimeDirection fun v w : TangentSpace I x ↦ g x v w
  /-- It depends smoothly on the point. -/
  smooth : IsSmoothOn g s

/-- A space-time is in particular a length measure. -/
theorem IsSpaceTimeOn.isLengthMeasureOn {g : LengthMeasure I M} {s : Set M}
    (h : IsSpaceTimeOn g s) : IsLengthMeasureOn g s where
  symm := h.symm
  nondegenerate := fun x hx ↦ (h.oneTime x hx).nondegenerate (h.symm x hx)
  smooth := h.smooth

/-! ## The connection of a length measure -/

/-- **The connection that belongs to the length measure `g`** on the region `s` (the Levi-Civita
connection of the textbooks). Three conditions:

* it is a connection: it obeys the sum rule and the product rule;
* it has no twist: changing `Y` along `X` minus changing `X` along `Y` is the bracket of the two
  fields, nothing more;
* it keeps lengths: the change of `g(Y, Z)` along a step is what the changes of `Y` and of `Z`
  along that step account for.

The textbooks prove that a length measure has exactly one such connection. Both halves are
proved in this project: at most one in `Unique.lean` (`IsConnectionOf.unique`), and one, on any
curved space, in `Connection/Exists.lean` (`connectionExists`; the statement is in
`Goals/Connection.lean`). -/
structure IsConnectionOf (g : LengthMeasure I M) (cov : Transport I M) (s : Set M) : Prop where
  /-- The region is open: curvature at a point looks at the connection near the point. -/
  isOpen : IsOpen s
  /-- It is a connection, in the sense of the standard library. -/
  isConnection : IsCovariantDerivativeOn E cov s
  /-- It has no twist (it is torsion-free). -/
  noTwist : ∀ x ∈ s, ∀ X Y : Arrows I M, MDiffAt (T% X) x → MDiffAt (T% Y) x →
    cov Y x (X x) - cov X x (Y x) = mlieBracket I X Y x
  /-- It keeps lengths (it is compatible with the length measure). -/
  keepsLengths : ∀ x ∈ s, ∀ Y Z : Arrows I M, MDiffAt (T% Y) x → MDiffAt (T% Z) x →
    ∀ v : TangentSpace I x,
      d% (fun y ↦ g y (Y y) (Z y)) x v = g x (cov Y x v) (Z x) + g x (Y x) (cov Z x v)

/-! ## Curvature -/

/-- **The full curvature, for three fields of arrows** (the Riemann tensor of the textbooks,
`R(X, Y) Z`): carry `Z` first along `Y` and then along `X`, do it in the other order, and take the
difference, corrected by the amount by which the two fields `X` and `Y` fail to close a small
loop. -/
noncomputable def curvatureOfFields (cov : Transport I M) (X Y Z : Arrows I M) : Arrows I M :=
  fun x ↦ cov (fun y ↦ cov Z y (Y y)) x (X x) - cov (fun y ↦ cov Z y (X y)) x (Y x)
    - cov Z x (mlieBracket I X Y x)

/-- **The full curvature at a point, for three steps** `u`, `v`, `w` at `x`. Each step is first
extended to a field of arrows near `x`, in the standard library's way: with the same parts in the
chart around `x`.

The textbooks show that any other smooth extension gives the same answer. That is shown for flat
coordinate space in `Flat.lean`, and for the connection of a length measure along any chart of a
curved space in `Join/` (`curvatureOfFields_carry`, `curvatureAt_carry`). -/
noncomputable def curvatureAt (cov : Transport I M) (x : M) (u v w : TangentSpace I x) :
    TangentSpace I x :=
  curvatureOfFields cov (extend E u) (extend E v) (extend E w) x

section Trace

variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]

/-- The trace of a function from a space of steps to itself, read off in a basis: the function is
applied to each basis step, and the part of the result along that same basis step is taken; these
parts are added. For a linear function this is its trace, and does not depend on the basis
(`traceIn_eq_trace` in `Flat.lean`; a change of basis: `traceIn_conj` in `Join/`). -/
noncomputable def traceIn (b : Module.Basis ι ℝ V) (F : V → V) : ℝ :=
  ∑ i, b.repr (F (b i)) i

end Trace

variable [FiniteDimensional ℝ E]

variable (I) in
/-- A basis of the steps at `x`, chosen once and for all. Which basis it is does not matter as
long as the function it is used on is linear: it is only used to take a trace, and the trace of
a linear function does not depend on the basis (`traceIn_eq_trace` in `Flat.lean`). For the
connection of a length measure on a curved space, the curvature is linear in each step and its
trace carries over along a chart: `Join/` (`ricciAt_carry`). -/
noncomputable def stepBasis (x : M) :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
  (Module.finBasis ℝ E).map (tangentSpaceCastModel I x).symm.toLinearEquiv

/-- **The curvature at a point** (the Ricci tensor of the textbooks), for two steps `v`, `w`: the
trace of the full curvature over its first slot. -/
noncomputable def ricciAt (cov : Transport I M) (x : M) (v w : TangentSpace I x) : ℝ :=
  traceIn (stepBasis I x) fun u ↦ curvatureAt cov x u v w

/-- **Space is empty on the region `s`:** Einstein's equation without matter. The length measure
has a connection there, and the curvature of that connection vanishes at every point of the
region. -/
def IsEmptyOn (g : LengthMeasure I M) (s : Set M) : Prop :=
  ∃ cov : Transport I M, IsConnectionOf g cov s ∧
    ∀ x ∈ s, ∀ v w : TangentSpace I x, ricciAt cov x v w = 0

/-! ## Symmetry -/

/-- **Moving along the field of arrows `ξ` leaves the length measure unchanged at `x`** (`ξ` is a
Killing field at `x`). The field can be differentiated at `x`, and for any two fields `X` and `Y`:
the change of `g(X, Y)` along `ξ` is what the changes of `X` and of `Y` along `ξ` account for.
"The change of `X` along `ξ`" is the bracket of the two fields, so no connection is needed to say
this. -/
def LeavesUnchangedAt (g : LengthMeasure I M) (ξ : Arrows I M) (x : M) : Prop :=
  MDiffAt (T% ξ) x ∧ ∀ X Y : Arrows I M, MDiffAt (T% X) x → MDiffAt (T% Y) x →
    d% (fun y ↦ g y (X y) (Y y)) x (ξ x)
      = g x (mlieBracket I ξ X x) (Y x) + g x (X x) (mlieBracket I ξ Y x)

/-- **The space-time looks the same from every side, on the region `s`.** There are three fields
of arrows `ξ 0`, `ξ 1`, `ξ 2` that

* are smooth;
* each leave the length measure unchanged;
* combine the way the turns around three axes at right angles do: the bracket of two of them,
  taken in the order 0, 1, 2 round the circle, is the third (in the other order, minus the
  third);
* together sweep out surfaces, not whole regions: at each point they span two directions;
* and on these surfaces all lengths are positive.

This is the statement "the turns of ordinary space act on the space-time, keeping all lengths,
and move each point over a sphere", said for small turns. No coordinates are mentioned. -/
structure IsRoundOn (g : LengthMeasure I M) (ξ : Fin 3 → Arrows I M) (s : Set M) : Prop where
  /-- The region is open: a bracket looks at the fields near a point. -/
  isOpen : IsOpen s
  /-- The three fields are smooth. -/
  smooth : ∀ i, CMDiff[s] ∞ (T% (ξ i))
  /-- Each leaves the length measure unchanged. -/
  unchanged : ∀ i, ∀ x ∈ s, LeavesUnchangedAt g (ξ i) x
  /-- They combine the way turns do. -/
  likeTurns : ∀ x ∈ s, mlieBracket I (ξ 0) (ξ 1) x = ξ 2 x ∧
    mlieBracket I (ξ 1) (ξ 2) x = ξ 0 x ∧ mlieBracket I (ξ 2) (ξ 0) x = ξ 1 x
  /-- They sweep out surfaces. -/
  surfaces : ∀ x ∈ s, Module.finrank ℝ (Submodule.span ℝ (Set.range fun i ↦ ξ i x)) = 2
  /-- On these surfaces all lengths are positive. -/
  positive : ∀ x ∈ s, ∀ v ∈ Submodule.span ℝ (Set.range fun i ↦ ξ i x), v ≠ 0 → 0 < g x v v

end GravityInLean.Curved
