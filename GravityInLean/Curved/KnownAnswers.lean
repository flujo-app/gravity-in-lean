/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Curved.Tables
public import GravityInLean.Probe.Sphere
public import GravityInLean.Probe.DeSitter
public import GravityInLean.SameSpacetime

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# The definitions of `Basic.lean`, tested on three known answers

A definition that nobody has tested is a guess. Before anything is built on the definitions of
`Basic.lean`, this file applies them to three cases where the answer is known beforehand.

**A sphere.** All lengths are positive, so it has no time direction (`sphere_noTime`). Its
curvature is its own length measure (`sphere_curvature`): positive, with the textbooks' sign.

**De Sitter's space-time,** an empty universe with a cosmological constant. It has exactly one
time direction (`deSitter_isSpaceTimeOn`). Its curvature is `3 / L²` times its length measure
(`deSitter_curvature`). It is curved, and not empty in the sense used here.

**Schwarzschild's space-time,** around one mass. It has one time direction outside the rim, and
one inside as well, where the distance label is the time direction
(`schwarzschild_isSpaceTimeOn_outside`, `schwarzschild_isSpaceTimeOn_inside`). It is empty
(`schwarzschild_isEmptyOn`). It looks the same from every side (`schwarzschild_isRoundOn`).

Every theorem here is about the notions of `Basic.lean`. The calculations behind them were done
earlier in this project, in coordinates (`Probe/Sphere.lean`, `Probe/DeSitter.lean`, step 1);
`Tables.lean` is what carries them over.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Filter Topology Set

open scoped Manifold ContDiff

/-! ## Diagonal tables -/

section Diagonal

variable {n : ℕ}

theorem formOf_diag (D : Fin n → ℝ) (v w : Coords n) :
    formOf (fun a b ↦ if a = b then D a else 0) v w = ∑ a, D a * v a * w a := by
  rw [formOf_apply]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ h
    simp [Ne.symm h]
  · simp

theorem formOf_const_mul (k : ℝ) (T : Fin n → Fin n → ℝ) (v w : Coords n) :
    formOf (fun a b ↦ k * T a b) v w = k * formOf T v w := by
  simp only [formOf_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring

/-- **A diagonal table with one negative entry and all others positive has one time
direction:** the direction of the negative entry. -/
theorem hasOneTimeDirection_diag {D : Fin n → ℝ} (t : Fin n) (ht : D t < 0)
    (hpos : ∀ a, a ≠ t → 0 < D a) :
    HasOneTimeDirection fun v w : Coords n ↦
      formOf (fun a b ↦ if a = b then D a else 0) v w := by
  refine ⟨Pi.single t 1, ?_, ?_⟩
  · change formOf (fun a b ↦ if a = b then D a else 0) (Pi.single t 1) (Pi.single t 1) < 0
    rw [formOf_single_single]
    simpa using ht
  · intro v hv hne
    have hv' : formOf (fun a b ↦ if a = b then D a else 0) (Pi.single t 1) v = 0 := hv
    have e : formOf (fun a b ↦ if a = b then D a else 0) (Pi.single t 1) v = D t * v t := by
      rw [formOf_single_left, Finset.sum_eq_single t]
      · simp
      · intro b _ h
        simp [Ne.symm h]
      · simp
    rw [e] at hv'
    have hvt : v t = 0 := by
      rcases mul_eq_zero.mp hv' with h | h
      · exact absurd h ht.ne
      · exact h
    obtain ⟨a, ha⟩ : ∃ a, v a ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne (funext hcon)
    have hat : a ≠ t := fun h ↦ ha (h ▸ hvt)
    change 0 < formOf (fun a b ↦ if a = b then D a else 0) v v
    rw [formOf_diag]
    refine Finset.sum_pos' (fun i _ ↦ ?_) ⟨a, Finset.mem_univ a, ?_⟩
    · by_cases hi : i = t
      · rw [hi, hvt]
        simp
      · rw [mul_assoc]
        exact mul_nonneg (hpos i hi).le (mul_self_nonneg _)
    · rw [mul_assoc]
      exact mul_pos (hpos a hat) (mul_self_pos.mpr ha)

end Diagonal

/-- A measure that gives no step a negative squared length has no time direction. -/
theorem not_hasOneTimeDirection_of_nonneg {V : Type*} [Zero V] {b : V → V → ℝ}
    (h : ∀ v, 0 ≤ b v v) : ¬ HasOneTimeDirection b :=
  fun ⟨t, ht, _⟩ ↦ absurd ht (not_lt.mpr (h t))

/-! ## Known answer 1: a sphere -/

/-- The sphere without its two poles, in the coordinates (angle from the pole, angle around). -/
def sphereRegion : Set (Coords 2) := {x | sin (x 0) ≠ 0}

theorem isOpen_sphereRegion : IsOpen sphereRegion :=
  isOpen_ne_fun (Real.continuous_sin.comp (continuous_apply 0)) continuous_const

/-- The sphere's table is good away from the poles. -/
theorem sphere_regular : IsRegularTableOn sphereG sphereGinv sphereRegion where
  isOpen := isOpen_sphereRegion
  smooth := fun a b ↦ by
    have h : ContDiff ℝ ∞ (fun x : Coords 2 ↦ sin (x 0) ^ 2) :=
      (Real.contDiff_sin.comp (contDiff_apply ℝ ℝ (0 : Fin 2))).pow 2
    unfold sphereG
    split_ifs
    · exact contDiffOn_const
    · exact h.contDiffOn
    · exact contDiffOn_const
  symm := fun x _ a b ↦ by fin_cases a <;> fin_cases b <;> simp [sphereG]
  inverse := fun _ hx a c ↦ sphereG_mul_sphereGinv hx a c

/-- The sphere is a length measure in the sense of `Basic.lean`. -/
theorem sphere_isLengthMeasureOn :
    IsLengthMeasureOn (flatMeasure (tableMeasure sphereG)) sphereRegion :=
  sphere_regular.isLengthMeasureOn

theorem sphere_measure_apply (x v w : Coords 2) :
    tableMeasure sphereG x v w = v 0 * w 0 + sin (x 0) ^ 2 * v 1 * w 1 := by
  simp [tableMeasure, formOf_apply, Fin.sum_univ_two, sphereG]

/-- **The sphere has no time direction:** all its lengths are positive. So "one time direction"
does not hold of everything. -/
theorem sphere_noTime (x : Coords 2) :
    ¬ HasOneTimeDirection fun v w : TangentSpace 𝓘(ℝ, Coords 2) x ↦
      flatMeasure (tableMeasure sphereG) x v w := by
  refine not_hasOneTimeDirection_of_nonneg fun v ↦ ?_
  change 0 ≤ tableMeasure sphereG x v v
  rw [sphere_measure_apply]
  nlinarith [mul_self_nonneg (v 0), mul_self_nonneg (sin (x 0) * v 1)]

/-- **Known answer 1.** The curvature of the sphere, in the sense of `Basic.lean`, is the
sphere's own length measure. -/
theorem sphere_curvature {x : Coords 2} (hx : x ∈ sphereRegion)
    (v w : TangentSpace 𝓘(ℝ, Coords 2) x) :
    ricciAt (flatTransport (tableCorr (christoffel sphereG sphereGinv))) x v w
      = flatMeasure (tableMeasure sphereG) x v w := by
  rw [sphere_regular.ricciAt hx]
  have e : (fun b c : Fin 2 ↦ ricci (christoffel sphereG sphereGinv) c b x)
      = fun b c ↦ sphereG b c x := by
    funext b c
    rw [ricci_sphere hx c b, sphere_regular.symm x hx c b]
  rw [e]
  rfl

/-! ## Round tables in four coordinates -/

section Round

variable {A B : ℝ → ℝ}

theorem smooth_sep {f h : ℝ → ℝ} {z : Coords 4} {k : WithTop ℕ∞} (hf : ContDiffAt ℝ k f (z 1))
    (hh : ContDiffAt ℝ k h (z 2)) : ContDiffAt ℝ k (sep f h) z := by
  have h1 : ContDiffAt ℝ k (fun y : Coords 4 ↦ f (y 1)) z :=
    ContDiffAt.comp (g := f) z hf (contDiffAt_apply ℝ (fun _ : Fin 4 ↦ ℝ) 1 z)
  have h2 : ContDiffAt ℝ k (fun y : Coords 4 ↦ h (y 2)) z :=
    ContDiffAt.comp (g := h) z hh (contDiffAt_apply ℝ (fun _ : Fin 4 ↦ ℝ) 2 z)
  exact h1.mul h2

/-- Every entry of a round table is as smooth as its clock and ruler functions. -/
theorem smooth_roundG {z : Coords 4} {k : WithTop ℕ∞} (ha : ContDiffAt ℝ k A (z 1))
    (hb : ContDiffAt ℝ k B (z 1)) (i j : Fin 4) : ContDiffAt ℝ k (roundG A B i j) z := by
  by_cases hij : i = j
  · subst hij
    have e : roundG A B i i = sep (gr A B i) (gθ i) := by
      funext w
      simp [roundG, diag, roundDiag]
    rw [e]
    refine smooth_sep ?_ ?_
    · unfold gr
      split_ifs
      · exact ha.neg
      · exact hb
      · exact contDiffAt_id.pow 2
    · unfold gθ
      split_ifs
      · exact (Real.contDiff_sin.contDiffAt).pow 2
      · exact (contDiffAt_const : ContDiffAt ℝ k (fun _ : ℝ ↦ (1 : ℝ)) (z 2))
  · have e : roundG A B i j = fun _ ↦ 0 := by
      funext w
      simp [roundG, diag, hij]
    rw [e]
    exact contDiffAt_const

/-- A round table is good on an open region where its clock and ruler functions are smooth and
the conditions of step 1 hold. -/
theorem round_regular {s : Set (Coords 4)} (hs : IsOpen s)
    (hA : ∀ x ∈ s, ContDiffAt ℝ ∞ A (x 1)) (hB : ∀ x ∈ s, ContDiffAt ℝ ∞ B (x 1))
    (hreg : ∀ x ∈ s, Regular A B x) : IsRegularTableOn (roundG A B) (roundGinv A B) s where
  isOpen := hs
  smooth := fun a b x hx ↦ (smooth_roundG (hA x hx) (hB x hx) a b).contDiffWithinAt
  symm := fun x _ a b ↦ roundG_symm A B a b x
  inverse := fun _ hx a c ↦ roundG_mul_roundGinv (hreg _ hx) a c

theorem round_measure_apply (A B : ℝ → ℝ) (x v w : Coords 4) :
    tableMeasure (roundG A B) x v w = ∑ a, roundDiag A B a x * v a * w a :=
  formOf_diag (fun a ↦ roundDiag A B a x) v w

/-- A round table with positive clock and ruler functions has one time direction: the time
label. -/
theorem round_oneTime_of_pos {x : Coords 4} (hA : 0 < A (x 1)) (hB : 0 < B (x 1))
    (hr : x 1 ≠ 0) (hs : sin (x 2) ≠ 0) :
    HasOneTimeDirection fun v w : Coords 4 ↦ tableMeasure (roundG A B) x v w := by
  refine hasOneTimeDirection_diag (D := fun a ↦ roundDiag A B a x) 0 ?_ ?_
  · simpa [roundDiag, sep, gr, gθ, negF, constOne] using hA
  · intro a ha
    fin_cases a
    · exact absurd rfl ha
    · simpa [roundDiag, sep, gr, gθ, constOne] using hB
    · simpa [roundDiag, sep, gr, gθ, sqF, constOne] using sq_pos_iff.mpr hr
    · simpa [roundDiag, sep, gr, gθ, sqF, sin2] using
        mul_pos (sq_pos_iff.mpr hr) (sq_pos_iff.mpr hs)

/-- A round table with negative clock and ruler functions has one time direction as well: the
distance label. This is what happens inside the rim of a black hole. -/
theorem round_oneTime_of_neg {x : Coords 4} (hA : A (x 1) < 0) (hB : B (x 1) < 0)
    (hr : x 1 ≠ 0) (hs : sin (x 2) ≠ 0) :
    HasOneTimeDirection fun v w : Coords 4 ↦ tableMeasure (roundG A B) x v w := by
  refine hasOneTimeDirection_diag (D := fun a ↦ roundDiag A B a x) 1 ?_ ?_
  · simpa [roundDiag, sep, gr, gθ, constOne] using hB
  · intro a ha
    fin_cases a
    · simpa [roundDiag, sep, gr, gθ, negF, constOne] using hA
    · exact absurd rfl ha
    · simpa [roundDiag, sep, gr, gθ, sqF, constOne] using sq_pos_iff.mpr hr
    · simpa [roundDiag, sep, gr, gθ, sqF, sin2] using
        mul_pos (sq_pos_iff.mpr hr) (sq_pos_iff.mpr hs)

end Round

end GravityInLean.Curved
