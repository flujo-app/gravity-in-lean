/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Curved.Basic
public import Mathlib.Analysis.Calculus.VectorField
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# The definitions of `Basic.lean`, worked out on flat space

Flat space is the simplest curved space: a space of plain vectors, with the one chart that does
nothing. A field of arrows on it is an ordinary function, and every notion of `Basic.lean` turns
into a formula of ordinary calculus. This file works those formulas out. It is the first test of
the definitions, and the tool for the tests with known answers in `Tables.lean` and
`KnownAnswers.lean`.

A length measure on flat space need not be flat: it may change from point to point, as on a globe
drawn on a map. So this covers every space-time that fits into one set of coordinates.

**What is proved here.**

* `isCovariantDerivativeOn_flatTransport`: "the plain slope plus a correction `A`" is a
  connection.
* `flat_noTwist`, `flat_keepsLengths`: when it is the connection of a length measure.
* `curvatureOfFields_flat`: its full curvature, for any three fields of arrows. The answer only
  looks at the three arrows at the point, not at how the fields continue. So on flat space the
  full curvature at a point does not depend on how the three steps are extended.
* `curvatureAt_flat`, `ricciAt_flat`: the curvature at a point, in formulas.
* `leavesUnchangedAt_flat_iff`: "moving along a field leaves the length measure unchanged", in
  formulas.
* `isSmoothOn_flat_iff`: smooth in the sense of curved spaces is smooth in the ordinary sense.

**A technical remark.** The standard library treats a step at a point of flat space and a plain
vector as two types that happen to be the same. This file uses that on purpose, and says so to
Lean with `backward.isDefEq.respectTransparency false`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Bundle FiberBundle VectorField

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Fields of arrows on flat space are ordinary functions -/

/-- A field of arrows on flat space, as an ordinary function. -/
def plain (X : Arrows 𝓘(ℝ, E) E) : E → E := X

/-- An ordinary function, as a field of arrows on flat space. -/
def arrows (X : E → E) : Arrows 𝓘(ℝ, E) E := X

@[simp] theorem plain_arrows (X : E → E) : plain (arrows X) = X := rfl

/-- A field of arrows on flat space can be differentiated in the sense of curved spaces exactly
when it can in the ordinary sense. -/
theorem mdiffAt_arrows_iff {X : Arrows 𝓘(ℝ, E) E} {x : E} :
    MDiffAt (T% X) x ↔ DifferentiableAt ℝ (plain X) x := by
  constructor
  · intro h
    have h2 : MDiffAt ((fun p : TangentBundle 𝓘(ℝ, E) E ↦ p.2) ∘ (T% X)) x :=
      ((contMDiff_snd_tangentBundle_modelSpace E 𝓘(ℝ, E) (n := 1)).mdifferentiableAt
        one_ne_zero).comp x h
    exact mdifferentiableAt_iff_differentiableAt.mp h2
  · intro h
    rw [mdifferentiableAt_totalSpace]
    refine ⟨mdifferentiableAt_id, ?_⟩
    convert! h.mdifferentiableAt with y
    simp
    rfl

/-- The bracket of two fields of arrows on flat space is the bracket of ordinary calculus. -/
theorem mlieBracket_flat (X Y : Arrows 𝓘(ℝ, E) E) (x : E) :
    mlieBracket 𝓘(ℝ, E) X Y x
      = fderiv ℝ (plain Y) x (plain X x) - fderiv ℝ (plain X) x (plain Y x) := by
  rw [← mlieBracketWithin_univ, mlieBracketWithin_eq_lieBracketWithin, lieBracketWithin_univ]
  rfl

/-- The standard library's way of extending a step at `x` to a field of arrows gives, on flat
space, the same step at every point. -/
theorem plain_extend (x : E) (u : TangentSpace 𝓘(ℝ, E) x) :
    plain (extend E u) = fun _ ↦ u := by
  funext y
  simp only [plain, extend]
  rw [← Trivialization.symmL_apply (R := ℝ) _ (by simp)]
  simp
  rfl

/-- The slope of a function on flat space, in the sense of curved spaces, is the ordinary one. -/
theorem mvfderiv_flat (f : E → ℝ) (x : E) (v : TangentSpace 𝓘(ℝ, E) x) :
    d% f x v = fderiv ℝ f x v := by
  simp
  rfl

/-! ## A connection on flat space -/

/-- A connection on flat space: the plain slope of the field, plus a correction. `A x z v` is the
correction for the arrow `z` when moving along the step `v` (the Christoffel symbols of the
textbooks, as one object). -/
noncomputable def flatTransport (A : E → E →L[ℝ] E →L[ℝ] E) : Transport 𝓘(ℝ, E) E :=
  fun σ x ↦ fderiv ℝ (plain σ) x + A x (plain σ x)

theorem flatTransport_apply (A : E → E →L[ℝ] E →L[ℝ] E) (σ : Arrows 𝓘(ℝ, E) E) (x : E)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    flatTransport A σ x v = fderiv ℝ (plain σ) x v + A x (plain σ x) v := rfl

/-- "The plain slope plus a correction" is a connection, whatever the correction. -/
theorem isCovariantDerivativeOn_flatTransport (A : E → E →L[ℝ] E →L[ℝ] E) :
    IsCovariantDerivativeOn E (flatTransport A) Set.univ where
  add {σ σ' x} hσ hσ' _ := by
    have h1 := mdiffAt_arrows_iff.mp hσ
    have h2 := mdiffAt_arrows_iff.mp hσ'
    have e : fderiv ℝ (fun y ↦ plain σ y + plain σ' y) x
        = fderiv ℝ (plain σ) x + fderiv ℝ (plain σ') x := fderiv_add h1 h2
    ext v
    change fderiv ℝ (fun y ↦ plain σ y + plain σ' y) x v + A x (plain σ x + plain σ' x) v
      = (fderiv ℝ (plain σ) x v + A x (plain σ x) v)
        + (fderiv ℝ (plain σ') x v + A x (plain σ' x) v)
    rw [e]
    simp only [add_apply, map_add]
    abel
  leibniz {σ g x} hσ hg _ := by
    have h1 := mdiffAt_arrows_iff.mp hσ
    have h2 : DifferentiableAt ℝ g x := mdifferentiableAt_iff_differentiableAt.mp hg
    have e : fderiv ℝ (fun y ↦ g y • plain σ y) x
        = g x • fderiv ℝ (plain σ) x + (fderiv ℝ g x).smulRight (plain σ x) :=
      fderiv_smul h2 h1
    ext v
    rw [mvfderiv_eq_fderiv]
    change fderiv ℝ (fun y ↦ g y • plain σ y) x v + A x (g x • plain σ x) v
      = g x • (fderiv ℝ (plain σ) x v + A x (plain σ x) v) + (fderiv ℝ g x v) • plain σ x
    rw [e]
    simp only [add_apply, map_smul, smul_apply, ContinuousLinearMap.smulRight_apply, smul_add]
    abel

/-- **No twist on flat space.** The connection has no twist at `x` when its correction does not
depend on the order of its two arrows there. -/
theorem flat_noTwist {A : E → E →L[ℝ] E →L[ℝ] E} {x : E} (hA : ∀ u v : E, A x u v = A x v u)
    (X Y : Arrows 𝓘(ℝ, E) E) :
    flatTransport A Y x (X x) - flatTransport A X x (Y x) = mlieBracket 𝓘(ℝ, E) X Y x := by
  rw [mlieBracket_flat]
  change (fderiv ℝ (plain Y) x (plain X x) + A x (plain Y x) (plain X x))
      - (fderiv ℝ (plain X) x (plain Y x) + A x (plain X x) (plain Y x))
    = fderiv ℝ (plain Y) x (plain X x) - fderiv ℝ (plain X) x (plain Y x)
  rw [hA (plain Y x) (plain X x)]
  abel

/-! ## A length measure on flat space -/

section Measure

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The product rule for a two-slot function applied to two fields. -/
theorem fderiv_apply₂ {g : E → E →L[ℝ] E →L[ℝ] F} {Y Z : E → E} {x : E}
    (hg : DifferentiableAt ℝ g x) (hY : DifferentiableAt ℝ Y x) (hZ : DifferentiableAt ℝ Z x)
    (v : E) :
    fderiv ℝ (fun y ↦ g y (Y y) (Z y)) x v
      = fderiv ℝ g x v (Y x) (Z x) + g x (fderiv ℝ Y x v) (Z x) + g x (Y x) (fderiv ℝ Z x v) := by
  have h := ((hg.hasFDerivAt.clm_apply hY.hasFDerivAt).clm_apply hZ.hasFDerivAt).fderiv
  rw [h]
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.flip_apply]
  abel

theorem differentiableAt_apply₂ {g : E → E →L[ℝ] E →L[ℝ] F} {Y Z : E → E} {x : E}
    (hg : DifferentiableAt ℝ g x) (hY : DifferentiableAt ℝ Y x) (hZ : DifferentiableAt ℝ Z x) :
    DifferentiableAt ℝ (fun y ↦ g y (Y y) (Z y)) x :=
  ((hg.hasFDerivAt.clm_apply hY.hasFDerivAt).clm_apply hZ.hasFDerivAt).differentiableAt

end Measure

/-- A two-slot function on plain vectors that changes from point to point, as a length measure on
flat space. -/
def flatMeasure (g : E → E →L[ℝ] E →L[ℝ] ℝ) : LengthMeasure 𝓘(ℝ, E) E := g

/-- **Smooth on flat space.** A length measure on flat space is smooth in the sense of curved
spaces exactly when it is smooth as an ordinary function of the point. -/
theorem isSmoothOn_flat_iff {g : E → E →L[ℝ] E →L[ℝ] ℝ} {s : Set E} :
    IsSmoothOn (flatMeasure g) s ↔ ContDiffOn ℝ ∞ g s := by
  unfold IsSmoothOn
  have key : ∀ x₀ x : E, (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ) x₀
        ⟨x, flatMeasure g x⟩).2 = g x := by
    intro x₀ x
    ext v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, flatMeasure]
    rfl
  constructor
  · intro h x hx
    have h1 := contMDiffWithinAt_section_iff.mp (h x hx)
    simp only [key] at h1
    exact contMDiffWithinAt_iff_contDiffWithinAt.mp h1
  · intro h x hx
    rw [contMDiffWithinAt_section_iff]
    simp only [key]
    exact (h x hx).contMDiffWithinAt

/-- A field of arrows on flat space is smooth in the sense of curved spaces exactly when it is
smooth as an ordinary function. -/
theorem contMDiffOn_arrows_iff {X : Arrows 𝓘(ℝ, E) E} {s : Set E} :
    CMDiff[s] ∞ (T% X) ↔ ContDiffOn ℝ ∞ (plain X) s :=
  contMDiffOn_vectorSpace_iff_contDiffOn

/-- **Keeping lengths on flat space.** The connection keeps the lengths of `g` at `x` when the
slopes of `g` are accounted for by the correction: slot by slot. -/
theorem flat_keepsLengths {g : E → E →L[ℝ] E →L[ℝ] ℝ} {A : E → E →L[ℝ] E →L[ℝ] E} {x : E}
    (hg : DifferentiableAt ℝ g x)
    (h : ∀ v y z : E, fderiv ℝ g x v y z = g x (A x y v) z + g x y (A x z v))
    (Y Z : Arrows 𝓘(ℝ, E) E) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    d% (fun y ↦ flatMeasure g y (Y y) (Z y)) x v
      = flatMeasure g x (flatTransport A Y x v) (Z x)
        + flatMeasure g x (Y x) (flatTransport A Z x v) := by
  have hY' := mdiffAt_arrows_iff.mp hY
  have hZ' := mdiffAt_arrows_iff.mp hZ
  rw [mvfderiv_flat]
  change fderiv ℝ (fun y ↦ g y (plain Y y) (plain Z y)) x v
    = g x (fderiv ℝ (plain Y) x v + A x (plain Y x) v) (plain Z x)
      + g x (plain Y x) (fderiv ℝ (plain Z) x v + A x (plain Z x) v)
  rw [fderiv_apply₂ hg hY' hZ', h v (plain Y x) (plain Z x)]
  simp only [map_add, add_apply]
  abel

/-- **"Unchanged along a field" on flat space.** Moving along `ξ` leaves the length measure `g`
unchanged at `x` exactly when: the slope of `g` along `ξ`, plus `g` with the slope of `ξ` put into
its first slot, plus `g` with the slope of `ξ` put into its second slot, is zero. This is
Killing's equation as the textbooks write it in coordinates. -/
theorem leavesUnchangedAt_flat_iff {g : E → E →L[ℝ] E →L[ℝ] ℝ} {ξ : Arrows 𝓘(ℝ, E) E} {x : E}
    (hg : DifferentiableAt ℝ g x) :
    LeavesUnchangedAt (flatMeasure g) ξ x ↔ ∀ y z : E,
      fderiv ℝ g x (plain ξ x) y z + g x (fderiv ℝ (plain ξ) x y) z
        + g x y (fderiv ℝ (plain ξ) x z) = 0 := by
  constructor
  · intro h y z
    have hy : MDiffAt (T% (arrows fun _ : E ↦ y)) x :=
      mdiffAt_arrows_iff.mpr (differentiableAt_const y)
    have hz : MDiffAt (T% (arrows fun _ : E ↦ z)) x :=
      mdiffAt_arrows_iff.mpr (differentiableAt_const z)
    have h1 := h (arrows fun _ ↦ y) (arrows fun _ ↦ z) hy hz
    rw [mvfderiv_flat, mlieBracket_flat, mlieBracket_flat] at h1
    have e : fderiv ℝ (fun p ↦ g p y z) x (plain ξ x) = fderiv ℝ g x (plain ξ x) y z := by
      have := fderiv_apply₂ hg (differentiableAt_const y) (differentiableAt_const z)
        (plain ξ x)
      simpa using this
    change fderiv ℝ (fun p ↦ g p y z) x (plain ξ x)
      = g x (fderiv ℝ (fun _ : E ↦ y) x (plain ξ x) - fderiv ℝ (plain ξ) x y) z
        + g x y (fderiv ℝ (fun _ : E ↦ z) x (plain ξ x) - fderiv ℝ (plain ξ) x z) at h1
    rw [e] at h1
    simp only [fderiv_fun_const, Pi.zero_apply, zero_apply, zero_sub, map_neg, neg_apply]
      at h1
    linarith
  · intro h X Y hX hY
    have hX' := mdiffAt_arrows_iff.mp hX
    have hY' := mdiffAt_arrows_iff.mp hY
    rw [mvfderiv_flat, mlieBracket_flat, mlieBracket_flat]
    change fderiv ℝ (fun y ↦ g y (plain X y) (plain Y y)) x (plain ξ x)
      = g x (fderiv ℝ (plain X) x (plain ξ x) - fderiv ℝ (plain ξ) x (plain X x)) (plain Y x)
        + g x (plain X x) (fderiv ℝ (plain Y) x (plain ξ x) - fderiv ℝ (plain ξ) x (plain Y x))
    rw [fderiv_apply₂ hg hX' hY']
    have h1 := h (plain X x) (plain Y x)
    simp only [map_sub, sub_apply]
    linarith

/-! ## Curvature on flat space -/

section Curvature

variable {A : E → E →L[ℝ] E →L[ℝ] E} {x : E}

/-- **The full curvature on flat space, for any three fields of arrows.** The right-hand side only
looks at the three arrows `X x`, `Y x`, `Z x` at the point, not at how the fields continue. So on
flat space the full curvature is a function of three steps at a point, as the textbooks say it
must be. -/
theorem curvatureOfFields_flat (hA : DifferentiableAt ℝ A x) {X Y Z : Arrows 𝓘(ℝ, E) E}
    (hX : DifferentiableAt ℝ (plain X) x) (hY : DifferentiableAt ℝ (plain Y) x)
    (hZ : ContDiffAt ℝ 2 (plain Z) x) :
    curvatureOfFields (flatTransport A) X Y Z x
      = fderiv ℝ A x (plain X x) (plain Z x) (plain Y x)
        - fderiv ℝ A x (plain Y x) (plain Z x) (plain X x)
        + A x (A x (plain Z x) (plain Y x)) (plain X x)
        - A x (A x (plain Z x) (plain X x)) (plain Y x) := by
  -- `Z` can be differentiated, and so can its slope; the order of two slopes does not matter.
  have hZ1 : DifferentiableAt ℝ (plain Z) x := hZ.differentiableAt (by simp)
  have hZ2 : DifferentiableAt ℝ (fderiv ℝ (plain Z)) x :=
    (hZ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hsymm : ∀ u v : E,
      fderiv ℝ (fderiv ℝ (plain Z)) x u v = fderiv ℝ (fderiv ℝ (plain Z)) x v u :=
    fun u v ↦ hZ.isSymmSndFDerivAt (by simp) u v
  -- The slope of "`Z` carried along `W`".
  have key : ∀ W : E → E, DifferentiableAt ℝ W x → ∀ v : E,
      fderiv ℝ (fun y ↦ fderiv ℝ (plain Z) y (W y) + A y (plain Z y) (W y)) x v
        = fderiv ℝ (fderiv ℝ (plain Z)) x v (W x) + fderiv ℝ (plain Z) x (fderiv ℝ W x v)
          + (fderiv ℝ A x v (plain Z x) (W x) + A x (fderiv ℝ (plain Z) x v) (W x)
            + A x (plain Z x) (fderiv ℝ W x v)) := by
    intro W hW v
    have d1 : HasFDerivAt (fun y ↦ fderiv ℝ (plain Z) y (W y))
        ((fderiv ℝ (plain Z) x).comp (fderiv ℝ W x)
          + (fderiv ℝ (fderiv ℝ (plain Z)) x).flip (W x)) x :=
      hZ2.hasFDerivAt.clm_apply hW.hasFDerivAt
    have d2 : DifferentiableAt ℝ (fun y ↦ A y (plain Z y) (W y)) x :=
      differentiableAt_apply₂ hA hZ1 hW
    have e : fderiv ℝ (fun y ↦ fderiv ℝ (plain Z) y (W y) + A y (plain Z y) (W y)) x
        = fderiv ℝ (fun y ↦ fderiv ℝ (plain Z) y (W y)) x
          + fderiv ℝ (fun y ↦ A y (plain Z y) (W y)) x :=
      fderiv_add d1.differentiableAt d2
    rw [e, add_apply, d1.fderiv, fderiv_apply₂ hA hZ1 hW]
    simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.flip_apply]
    abel
  unfold curvatureOfFields
  rw [mlieBracket_flat]
  change (fderiv ℝ (fun y ↦ fderiv ℝ (plain Z) y (plain Y y) + A y (plain Z y) (plain Y y)) x
          (plain X x)
        + A x (fderiv ℝ (plain Z) x (plain Y x) + A x (plain Z x) (plain Y x)) (plain X x))
      - (fderiv ℝ (fun y ↦ fderiv ℝ (plain Z) y (plain X y) + A y (plain Z y) (plain X y)) x
          (plain Y x)
        + A x (fderiv ℝ (plain Z) x (plain X x) + A x (plain Z x) (plain X x)) (plain Y x))
      - (fderiv ℝ (plain Z) x
            (fderiv ℝ (plain Y) x (plain X x) - fderiv ℝ (plain X) x (plain Y x))
        + A x (plain Z x)
            (fderiv ℝ (plain Y) x (plain X x) - fderiv ℝ (plain X) x (plain Y x)))
    = _
  rw [key (plain Y) hY, key (plain X) hX, hsymm (plain X x) (plain Y x)]
  simp only [map_add, map_sub, add_apply]
  abel

/-- **The full curvature at a point of flat space,** for three steps. -/
theorem curvatureAt_flat (hA : DifferentiableAt ℝ A x) (u v w : TangentSpace 𝓘(ℝ, E) x) :
    curvatureAt (flatTransport A) x u v w
      = fderiv ℝ A x u w v - fderiv ℝ A x v w u + A x (A x w v) u - A x (A x w u) v := by
  have h := curvatureOfFields_flat hA (X := extend E u) (Y := extend E v) (Z := extend E w)
    (by rw [plain_extend]; exact differentiableAt_const _)
    (by rw [plain_extend]; exact differentiableAt_const _)
    (by rw [plain_extend]; exact contDiffAt_const)
  simp only [plain_extend] at h
  exact h

/-- On flat space, the full curvature of three fields of arrows at a point is the full curvature
of their three arrows at that point: it does not matter how the steps are extended. -/
theorem curvatureOfFields_flat_eq_curvatureAt (hA : DifferentiableAt ℝ A x)
    {X Y Z : Arrows 𝓘(ℝ, E) E} (hX : DifferentiableAt ℝ (plain X) x)
    (hY : DifferentiableAt ℝ (plain Y) x) (hZ : ContDiffAt ℝ 2 (plain Z) x) :
    curvatureOfFields (flatTransport A) X Y Z x
      = curvatureAt (flatTransport A) x (X x) (Y x) (Z x) := by
  rw [curvatureOfFields_flat hA hX hY hZ, curvatureAt_flat hA]
  rfl

end Curvature

/-! ## The trace -/

section TraceLemmas

variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]

/-- For a linear function, the trace read off in a basis is the trace, whatever the basis. -/
theorem traceIn_eq_trace (b : Module.Basis ι ℝ V) (L : V →ₗ[ℝ] V) :
    traceIn b L = LinearMap.trace ℝ V L := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℝ b L]
  simp [traceIn, Matrix.trace, LinearMap.toMatrix_apply]

end TraceLemmas

section Ricci

variable {A : E → E →L[ℝ] E →L[ℝ] E} {x : E}

/-- The full curvature at a point of flat space, as a linear function of its first step. -/
noncomputable def curvatureMap (A : E → E →L[ℝ] E →L[ℝ] E) (x v w : E) : E →L[ℝ] E :=
  ((fderiv ℝ A x).flip w).flip v - fderiv ℝ A x v w + A x (A x w v) - ((A x).flip v).comp (A x w)

theorem curvatureMap_apply (A : E → E →L[ℝ] E →L[ℝ] E) (x v w u : E) :
    curvatureMap A x v w u
      = fderiv ℝ A x u w v - fderiv ℝ A x v w u + A x (A x w v) u - A x (A x w u) v := by
  simp [curvatureMap]

theorem curvatureMap_add_left (A : E → E →L[ℝ] E →L[ℝ] E) (x v v' w : E) :
    curvatureMap A x (v + v') w = curvatureMap A x v w + curvatureMap A x v' w := by
  ext u
  simp only [curvatureMap_apply, add_apply, map_add]
  abel

theorem curvatureMap_smul_left (A : E → E →L[ℝ] E →L[ℝ] E) (x : E) (c : ℝ) (v w : E) :
    curvatureMap A x (c • v) w = c • curvatureMap A x v w := by
  ext u
  simp only [curvatureMap_apply, smul_apply, map_smul, smul_sub, smul_add]

theorem curvatureMap_add_right (A : E → E →L[ℝ] E →L[ℝ] E) (x v w w' : E) :
    curvatureMap A x v (w + w') = curvatureMap A x v w + curvatureMap A x v w' := by
  ext u
  simp only [curvatureMap_apply, add_apply, map_add]
  abel

theorem curvatureMap_smul_right (A : E → E →L[ℝ] E →L[ℝ] E) (x : E) (c : ℝ) (v w : E) :
    curvatureMap A x v (c • w) = c • curvatureMap A x v w := by
  ext u
  simp only [curvatureMap_apply, smul_apply, map_smul, smul_sub, smul_add]

variable [FiniteDimensional ℝ E]

/-- **The curvature at a point of flat space** is the trace of the full curvature over its first
step. -/
theorem ricciAt_flat (hA : DifferentiableAt ℝ A x) (v w : TangentSpace 𝓘(ℝ, E) x) :
    ricciAt (flatTransport A) x v w
      = LinearMap.trace ℝ E (curvatureMap A x v w : E →ₗ[ℝ] E) := by
  unfold ricciAt
  have e : (fun u : TangentSpace 𝓘(ℝ, E) x ↦ curvatureAt (flatTransport A) x u v w)
      = fun u ↦ curvatureMap A x v w u := by
    funext u
    rw [curvatureAt_flat hA, curvatureMap_apply]
  rw [e]
  exact traceIn_eq_trace (stepBasis 𝓘(ℝ, E) x) (curvatureMap A x v w : E →ₗ[ℝ] E)

end Ricci

/-! ## Checking on the basic steps -/

section Basis

variable {ι : Type*} (b : Module.Basis ι ℝ E)

/-- A two-slot identity that is linear in each slot only has to be checked on the basic steps. -/
theorem eq_of_basis₂ (F : E →L[ℝ] E →L[ℝ] ℝ) (R : E → E → ℝ)
    (hR₁ : ∀ z, IsLinearMap ℝ fun y ↦ R y z) (hR₂ : ∀ y, IsLinearMap ℝ fun z ↦ R y z)
    (h : ∀ i j, F (b i) (b j) = R (b i) (b j)) (y z : E) : F y z = R y z := by
  have step1 : ∀ j, ∀ y, F y (b j) = R y (b j) := by
    intro j y
    have e : (F.flip (b j) : E →ₗ[ℝ] ℝ) = (hR₁ (b j)).mk' _ :=
      b.ext fun i ↦ h i j
    exact congrArg (fun L : E →ₗ[ℝ] ℝ ↦ L y) e
  have e : (F y : E →ₗ[ℝ] ℝ) = (hR₂ y).mk' _ := b.ext fun j ↦ step1 j y
  exact congrArg (fun L : E →ₗ[ℝ] ℝ ↦ L z) e

/-- A three-slot identity that is linear in each slot only has to be checked on the basic
steps. -/
theorem eq_of_basis₃ (F : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (R : E → E → E → ℝ)
    (hR₁ : ∀ y z, IsLinearMap ℝ fun v ↦ R v y z) (hR₂ : ∀ v z, IsLinearMap ℝ fun y ↦ R v y z)
    (hR₃ : ∀ v y, IsLinearMap ℝ fun z ↦ R v y z)
    (h : ∀ i j k, F (b i) (b j) (b k) = R (b i) (b j) (b k)) (v y z : E) :
    F v y z = R v y z := by
  have step1 : ∀ j k, ∀ v, F v (b j) (b k) = R v (b j) (b k) := by
    intro j k v
    have e : ((F.flip (b j)).flip (b k) : E →ₗ[ℝ] ℝ) = (hR₁ (b j) (b k)).mk' _ :=
      b.ext fun i ↦ h i j k
    exact congrArg (fun L : E →ₗ[ℝ] ℝ ↦ L v) e
  exact eq_of_basis₂ b (F v) (R v) (hR₂ v) (hR₃ v) (fun j k ↦ step1 j k v) y z

end Basis

end GravityInLean.Curved
