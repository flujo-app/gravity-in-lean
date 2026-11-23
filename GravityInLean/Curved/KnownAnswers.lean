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
# The definitions of `Basic.lean`, tested on known answers

A definition that nobody has tested is a guess. Before anything is built on the definitions of
`Basic.lean`, this file applies them to cases where the answer is known beforehand.

**Flat space-time.** One time direction, and empty (`flat_isSpaceTimeOn`, `flat_isEmptyOn`).

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

/-! ## Known answer 0: flat space-time -/

section Flat

/-- The table of flat space-time (Minkowski's): `-1` for time, `1` for each of the three space
directions, the same at every point. It is its own inverse. -/
noncomputable def flatG (a b : Fin 4) : Coords 4 → ℝ := fun _ ↦
  if a = b then (if a = 0 then -1 else 1) else 0

/-- Flat space-time has no connection beyond the plain slope: all its Christoffel symbols are
zero. -/
theorem christoffel_flatG (a b c : Fin 4) (x : Coords 4) : christoffel flatG flatG a b c x = 0 := by
  have h : ∀ (i j k : Fin 4), slope k (flatG i j) x = 0 := fun i j k ↦ slope_const _ _ _
  simp [christoffel, h]

theorem flatG_regular : IsRegularTableOn flatG flatG Set.univ where
  isOpen := isOpen_univ
  smooth := fun _ _ ↦ contDiffOn_const
  symm := fun x _ a b ↦ by fin_cases a <;> fin_cases b <;> simp [flatG]
  inverse := fun x _ a c ↦ by
    fin_cases a <;> fin_cases c <;> simp [flatG]

/-- **Flat space-time is a space-time in the sense of `Basic.lean`,** everywhere. -/
theorem flat_isSpaceTimeOn :
    IsSpaceTimeOn (flatMeasure (tableMeasure flatG)) (Set.univ : Set (Coords 4)) where
  symm := fun _ hx v w ↦ flatG_regular.measure_symm hx v w
  oneTime := fun _ _ ↦
    hasOneTimeDirection_diag (D := fun a : Fin 4 ↦ if a = 0 then (-1 : ℝ) else 1) 0 (by simp)
      (fun a ha ↦ by simp [ha])
  smooth := flatG_regular.isSmoothOn

/-- **Known answer 0.** Flat space-time is empty in the sense of `Basic.lean`, everywhere. -/
theorem flat_isEmptyOn :
    IsEmptyOn (flatMeasure (tableMeasure flatG)) (Set.univ : Set (Coords 4)) :=
  flatG_regular.isEmptyOn fun x _ i j ↦ by
    have h : christoffel flatG flatG = fun _ _ _ _ ↦ 0 := by
      funext a b c y
      exact christoffel_flatG a b c y
    rw [h]
    simp [ricci, slope_const]

end Flat

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
      (Real.contDiff_sin.comp (contDiff_apply ℝ (fun _ : Fin 2 ↦ ℝ) 0)).pow 2
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

/-! ## Known answer 2: de Sitter's space-time -/

section DeSitter

/-- The part of de Sitter's space-time that its coordinates cover: inside the distance `L`, away
from the centre and the poles. -/
def deSitterRegion (L : ℝ) : Set (Coords 4) := {x | 0 < x 1 ∧ x 1 < L ∧ sin (x 2) ≠ 0}

theorem isOpen_deSitterRegion (L : ℝ) : IsOpen (deSitterRegion L) :=
  (isOpen_lt continuous_const (continuous_apply 1)).inter
    ((isOpen_lt (continuous_apply 1) continuous_const).inter
      (isOpen_ne_fun (Real.continuous_sin.comp (continuous_apply 2)) continuous_const))

theorem dsA_pos {L r : ℝ} (hr : 0 < r) (hL : r < L) : 0 < dsA L r := by
  have hL0 : 0 < L := hr.trans hL
  unfold dsA
  rw [sub_pos, div_lt_one (pow_pos hL0 2)]
  exact pow_lt_pow_left₀ hL hr.le two_ne_zero

theorem smooth_dsA (L r : ℝ) {k : WithTop ℕ∞} : ContDiffAt ℝ k (dsA L) r :=
  contDiffAt_const.sub ((contDiffAt_id.pow 2).div_const _)

theorem smooth_dsB {L r : ℝ} (hh : dsA L r ≠ 0) {k : WithTop ℕ∞} : ContDiffAt ℝ k (dsB L) r :=
  (smooth_dsA L r).inv hh

/-- De Sitter's table is good on its region. -/
theorem deSitter_regularTable (L : ℝ) :
    IsRegularTableOn (roundG (dsA L) (dsB L)) (roundGinv (dsA L) (dsB L)) (deSitterRegion L) :=
  round_regular (isOpen_deSitterRegion L) (fun x _ ↦ smooth_dsA L (x 1))
    (fun _ hx ↦ smooth_dsB (dsA_pos hx.1 hx.2.1).ne')
    (fun _ hx ↦ deSitter_regular hx.1 hx.2.1 hx.2.2)

/-- **De Sitter's space-time is a space-time in the sense of `Basic.lean`:** it has exactly one
time direction, at every point of its region. -/
theorem deSitter_isSpaceTimeOn (L : ℝ) :
    IsSpaceTimeOn (flatMeasure (tableMeasure (roundG (dsA L) (dsB L)))) (deSitterRegion L) where
  symm := fun _ hx v w ↦ (deSitter_regularTable L).measure_symm hx v w
  oneTime := fun _ hx ↦
    round_oneTime_of_pos (dsA_pos hx.1 hx.2.1) (inv_pos.mpr (dsA_pos hx.1 hx.2.1)) hx.1.ne'
      hx.2.2
  smooth := (deSitter_regularTable L).isSmoothOn

/-- **Known answer 2.** The curvature of de Sitter's space-time, in the sense of `Basic.lean`, is
`3 / L²` times its length measure. So it is curved, and it is not empty. -/
theorem deSitter_curvature {L : ℝ} {x : Coords 4} (hx : x ∈ deSitterRegion L)
    (v w : TangentSpace 𝓘(ℝ, Coords 4) x) :
    ricciAt (flatTransport (tableCorr (christoffel (roundG (dsA L) (dsB L))
        (roundGinv (dsA L) (dsB L))))) x v w
      = 3 / L ^ 2 * flatMeasure (tableMeasure (roundG (dsA L) (dsB L))) x v w := by
  rw [(deSitter_regularTable L).ricciAt hx]
  have e : (fun b c : Fin 4 ↦ ricci (christoffel (roundG (dsA L) (dsB L))
        (roundGinv (dsA L) (dsB L))) c b x)
      = fun b c ↦ 3 / L ^ 2 * roundG (dsA L) (dsB L) b c x := by
    funext b c
    rw [ricci_deSitter hx.1 hx.2.1 hx.2.2 c b, roundG_symm (dsA L) (dsB L) c b x]
  rw [e, formOf_const_mul]
  rfl

end DeSitter

/-! ## Known answer 3: Schwarzschild's space-time -/

section Schwarzschild

/-- Outside the rim of the black hole, away from the poles. -/
def outside (M : ℝ) : Set (Coords 4) := {x | 0 < x 1 ∧ 2 * M < x 1 ∧ sin (x 2) ≠ 0}

/-- Inside the rim of the black hole, away from the centre and the poles. -/
def inside (M : ℝ) : Set (Coords 4) := {x | 0 < x 1 ∧ x 1 < 2 * M ∧ sin (x 2) ≠ 0}

theorem isOpen_outside (M : ℝ) : IsOpen (outside M) :=
  (isOpen_lt continuous_const (continuous_apply 1)).inter
    ((isOpen_lt continuous_const (continuous_apply 1)).inter
      (isOpen_ne_fun (Real.continuous_sin.comp (continuous_apply 2)) continuous_const))

theorem isOpen_inside (M : ℝ) : IsOpen (inside M) :=
  (isOpen_lt continuous_const (continuous_apply 1)).inter
    ((isOpen_lt (continuous_apply 1) continuous_const).inter
      (isOpen_ne_fun (Real.continuous_sin.comp (continuous_apply 2)) continuous_const))

theorem schwA_pos_outside {M r : ℝ} (hr : 0 < r) (hrim : 2 * M < r) : 0 < schwA M r := by
  unfold schwA
  rw [sub_pos, div_lt_one hr]
  exact hrim

theorem schwA_neg_inside {M r : ℝ} (hr : 0 < r) (hrim : r < 2 * M) : schwA M r < 0 := by
  unfold schwA
  rw [sub_neg, one_lt_div hr]
  exact hrim

theorem smooth_schwA (M : ℝ) {r : ℝ} (hr : r ≠ 0) {k : WithTop ℕ∞} :
    ContDiffAt ℝ k (schwA M) r :=
  contDiffAt_const.sub (contDiffAt_const.div contDiffAt_id hr)

theorem smooth_schwB (M : ℝ) {r : ℝ} (hr : r ≠ 0) (hh : schwA M r ≠ 0) {k : WithTop ℕ∞} :
    ContDiffAt ℝ k (schwB M) r :=
  (smooth_schwA M hr).inv hh

/-- The conditions of step 1 also hold inside the rim. -/
theorem schwarzschild_regular_inside (M : ℝ) {x : Coords 4} (hr : 0 < x 1)
    (hrim : x 1 < 2 * M) (hs : sin (x 2) ≠ 0) : Regular (schwA M) (schwB M) x := by
  have hr0 : x 1 ≠ 0 := hr.ne'
  have hneg : schwA M (x 1) < 0 := schwA_neg_inside hr hrim
  exact
    { r_ne := hr0
      sin_ne := hs
      A_ne := hneg.ne
      B_ne := inv_ne_zero hneg.ne
      diffA := (hasDerivAt_schwA M hr0).differentiableAt
      diffA' := (hasDerivAt_deriv_schwA M hr0).differentiableAt
      diffB := (hasDerivAt_schwB M hr0 hneg.ne).differentiableAt }

/-- Schwarzschild's table is good outside the rim. -/
theorem schwarzschild_regularTable_outside (M : ℝ) :
    IsRegularTableOn (roundG (schwA M) (schwB M)) (roundGinv (schwA M) (schwB M)) (outside M) :=
  round_regular (isOpen_outside M) (fun _ hx ↦ smooth_schwA M hx.1.ne')
    (fun _ hx ↦ smooth_schwB M hx.1.ne' (schwA_pos_outside hx.1 hx.2.1).ne')
    (fun _ hx ↦ schwarzschild_regular M hx.1 hx.2.1 hx.2.2)

/-- Schwarzschild's table is good inside the rim as well. -/
theorem schwarzschild_regularTable_inside (M : ℝ) :
    IsRegularTableOn (roundG (schwA M) (schwB M)) (roundGinv (schwA M) (schwB M)) (inside M) :=
  round_regular (isOpen_inside M) (fun _ hx ↦ smooth_schwA M hx.1.ne')
    (fun _ hx ↦ smooth_schwB M hx.1.ne' (schwA_neg_inside hx.1 hx.2.1).ne)
    (fun _ hx ↦ schwarzschild_regular_inside M hx.1 hx.2.1 hx.2.2)

/-- **Schwarzschild's space-time is a space-time in the sense of `Basic.lean`, outside the rim:**
one time direction, the time label. -/
theorem schwarzschild_isSpaceTimeOn_outside (M : ℝ) :
    IsSpaceTimeOn (flatMeasure (tableMeasure (roundG (schwA M) (schwB M)))) (outside M) where
  symm := fun _ hx v w ↦ (schwarzschild_regularTable_outside M).measure_symm hx v w
  oneTime := fun _ hx ↦
    round_oneTime_of_pos (schwA_pos_outside hx.1 hx.2.1)
      (inv_pos.mpr (schwA_pos_outside hx.1 hx.2.1)) hx.1.ne' hx.2.2
  smooth := (schwarzschild_regularTable_outside M).isSmoothOn

/-- **And inside the rim:** still exactly one time direction, but now it is the distance label.
Falling inward is as unavoidable there as growing older is outside. -/
theorem schwarzschild_isSpaceTimeOn_inside (M : ℝ) :
    IsSpaceTimeOn (flatMeasure (tableMeasure (roundG (schwA M) (schwB M)))) (inside M) where
  symm := fun _ hx v w ↦ (schwarzschild_regularTable_inside M).measure_symm hx v w
  oneTime := fun _ hx ↦
    round_oneTime_of_neg (schwA_neg_inside hx.1 hx.2.1)
      (inv_lt_zero.mpr (schwA_neg_inside hx.1 hx.2.1)) hx.1.ne' hx.2.2
  smooth := (schwarzschild_regularTable_inside M).isSmoothOn

/-- **Known answer 3.** Schwarzschild's space-time is empty in the sense of `Basic.lean`, outside
the rim. -/
theorem schwarzschild_isEmptyOn (M : ℝ) :
    IsEmptyOn (flatMeasure (tableMeasure (roundG (schwA M) (schwB M)))) (outside M) :=
  (schwarzschild_regularTable_outside M).isEmptyOn fun _ hx ↦
    schwarzschild_ricciFlat M hx.1 hx.2.1 hx.2.2

/-! ### It looks the same from every side -/

section Round

theorem smooth_sepA {f h : ℝ → ℝ} {z : Coords 4} {k : WithTop ℕ∞} (hf : ContDiffAt ℝ k f (z 2))
    (hh : ContDiffAt ℝ k h (z 3)) : ContDiffAt ℝ k (sepA f h) z := by
  have h1 : ContDiffAt ℝ k (fun y : Coords 4 ↦ f (y 2)) z :=
    ContDiffAt.comp (g := f) z hf (contDiffAt_apply ℝ (fun _ : Fin 4 ↦ ℝ) 2 z)
  have h2 : ContDiffAt ℝ k (fun y : Coords 4 ↦ h (y 3)) z :=
    ContDiffAt.comp (g := h) z hh (contDiffAt_apply ℝ (fun _ : Fin 4 ↦ ℝ) 3 z)
  exact h1.mul h2

theorem smooth_negCot {θ : ℝ} (hs : sin θ ≠ 0) {k : WithTop ℕ∞} : ContDiffAt ℝ k negCot θ :=
  (Real.contDiff_cos.contDiffAt.div Real.contDiff_sin.contDiffAt hs).neg

theorem smooth_negSin (φ : ℝ) {k : WithTop ℕ∞} : ContDiffAt ℝ k negSin φ :=
  Real.contDiff_sin.contDiffAt.neg

theorem smooth_constOne (θ : ℝ) {k : WithTop ℕ∞} : ContDiffAt ℝ k constOne θ :=
  (contDiffAt_const : ContDiffAt ℝ k (fun _ : ℝ ↦ (1 : ℝ)) θ)

theorem smooth_rotX {z : Coords 4} (hs : sin (z 2) ≠ 0) (i : Fin 4) {k : WithTop ℕ∞} :
    ContDiffAt ℝ k (rotX i) z := by
  unfold rotX
  split_ifs
  · exact smooth_sepA (smooth_constOne _) (smooth_negSin _)
  · exact smooth_sepA (smooth_negCot hs) Real.contDiff_cos.contDiffAt
  · exact contDiffAt_const

theorem smooth_rotY {z : Coords 4} (hs : sin (z 2) ≠ 0) (i : Fin 4) {k : WithTop ℕ∞} :
    ContDiffAt ℝ k (rotY i) z := by
  unfold rotY
  split_ifs
  · exact smooth_sepA (smooth_constOne _) Real.contDiff_cos.contDiffAt
  · exact smooth_sepA (smooth_negCot hs) Real.contDiff_sin.contDiffAt
  · exact contDiffAt_const

theorem smooth_rotZ (z : Coords 4) (i : Fin 4) {k : WithTop ℕ∞} : ContDiffAt ℝ k (rotZ i) z := by
  unfold rotZ
  split_ifs <;> exact contDiffAt_const

theorem slope_rotZ (m k : Fin 4) (x : Coords 4) : slope m (rotZ k) x = 0 := by
  unfold rotZ
  split_ifs <;> exact slope_const _ _ _

/-- A fact about the pole angle that the bracket of two turns needs. -/
theorem negCot_identity {θ : ℝ} (hs : sin θ ≠ 0) : deriv negCot θ - negCot θ ^ 2 = 1 := by
  rw [deriv_negCot hs, negCot]
  field_simp
  linear_combination -Real.sin_sq_add_cos_sq θ

/-- **The three turns combine the way turns do, 1.** -/
theorem bracket_rotY_rotX {x : Coords 4} (hs : sin (x 2) ≠ 0) :
    VectorField.mlieBracket 𝓘(ℝ, Coords 4) (fieldOf rotY) (fieldOf rotX) x = fieldOf rotZ x := by
  have hY := differentiableAt_rotY hs
  have hX := differentiableAt_rotX hs
  have c0 : VectorField.mlieBracket 𝓘(ℝ, Coords 4) (fieldOf rotY) (fieldOf rotX) x 0
      = rotZ 0 x := by
    rw [mlieBracket_fieldOf hY hX 0]
    simp [rotX, rotY, rotZ, slope_const]
  have c1 : VectorField.mlieBracket 𝓘(ℝ, Coords 4) (fieldOf rotY) (fieldOf rotX) x 1
      = rotZ 1 x := by
    rw [mlieBracket_fieldOf hY hX 1]
    simp [rotX, rotY, rotZ, slope_const]
  have c2 : VectorField.mlieBracket 𝓘(ℝ, Coords 4) (fieldOf rotY) (fieldOf rotX) x 2
      = rotZ 2 x := by
    rw [mlieBracket_fieldOf hY hX 2]
    simp only [Fin.sum_univ_four, slope_rotX_two, slope_rotY_two]
    simp [rotX, rotY, rotZ, sepA, constOne, negSin]
    ring
  have c3 : VectorField.mlieBracket 𝓘(ℝ, Coords 4) (fieldOf rotY) (fieldOf rotX) x 3
      = rotZ 3 x := by
    rw [mlieBracket_fieldOf hY hX 3]
    simp only [Fin.sum_univ_four, slope_rotX_three, slope_rotY_three]
    simp [rotX, rotY, rotZ, sepA, constOne, negSin]
    linear_combination (deriv negCot (x 2) - negCot (x 2) ^ 2)
      * Real.sin_sq_add_cos_sq (x 3) + negCot_identity hs
  have key : ∀ k, VectorField.mlieBracket 𝓘(ℝ, Coords 4) (fieldOf rotY) (fieldOf rotX) x k
      = rotZ k x := by
    intro k
    fin_cases k
    exacts [c0, c1, c2, c3]
  exact funext key

/-- **The three turns combine the way turns do, 2.** -/
theorem bracket_rotX_rotZ {x : Coords 4} (hs : sin (x 2) ≠ 0) :
    VectorField.mlieBracket 𝓘(ℝ, Coords 4) (fieldOf rotX) (fieldOf rotZ) x = fieldOf rotY x := by
  have hX := differentiableAt_rotX hs
  have hZ := differentiableAt_rotZ x
  have c0 : VectorField.mlieBracket 𝓘(ℝ, Coords 4) (fieldOf rotX) (fieldOf rotZ) x 0
      = rotY 0 x := by
    rw [mlieBracket_fieldOf hX hZ 0]
    simp [rotX, rotY, rotZ, slope_const]
  have c1 : VectorField.mlieBracket 𝓘(ℝ, Coords 4) (fieldOf rotX) (fieldOf rotZ) x 1
      = rotY 1 x := by
    rw [mlieBracket_fieldOf hX hZ 1]
    simp [rotX, rotY, rotZ, slope_const]
  have c2 : VectorField.mlieBracket 𝓘(ℝ, Coords 4) (fieldOf rotX) (fieldOf rotZ) x 2
      = rotY 2 x := by
    rw [mlieBracket_fieldOf hX hZ 2]
    simp only [Fin.sum_univ_four, slope_rotZ, slope_rotX_two]
    simp [rotY, rotZ, sepA, constOne]
  have c3 : VectorField.mlieBracket 𝓘(ℝ, Coords 4) (fieldOf rotX) (fieldOf rotZ) x 3
      = rotY 3 x := by
    rw [mlieBracket_fieldOf hX hZ 3]
    simp only [Fin.sum_univ_four, slope_rotZ, slope_rotX_three]
    simp [rotY, rotZ, sepA]
  have key : ∀ k, VectorField.mlieBracket 𝓘(ℝ, Coords 4) (fieldOf rotX) (fieldOf rotZ) x k
      = rotY k x := by
    intro k
    fin_cases k
    exacts [c0, c1, c2, c3]
  exact funext key

/-- **The three turns combine the way turns do, 3.** -/
theorem bracket_rotZ_rotY {x : Coords 4} (hs : sin (x 2) ≠ 0) :
    VectorField.mlieBracket 𝓘(ℝ, Coords 4) (fieldOf rotZ) (fieldOf rotY) x = fieldOf rotX x := by
  have hY := differentiableAt_rotY hs
  have hZ := differentiableAt_rotZ x
  have c0 : VectorField.mlieBracket 𝓘(ℝ, Coords 4) (fieldOf rotZ) (fieldOf rotY) x 0
      = rotX 0 x := by
    rw [mlieBracket_fieldOf hZ hY 0]
    simp [rotX, rotY, rotZ, slope_const]
  have c1 : VectorField.mlieBracket 𝓘(ℝ, Coords 4) (fieldOf rotZ) (fieldOf rotY) x 1
      = rotX 1 x := by
    rw [mlieBracket_fieldOf hZ hY 1]
    simp [rotX, rotY, rotZ, slope_const]
  have c2 : VectorField.mlieBracket 𝓘(ℝ, Coords 4) (fieldOf rotZ) (fieldOf rotY) x 2
      = rotX 2 x := by
    rw [mlieBracket_fieldOf hZ hY 2]
    simp only [Fin.sum_univ_four, slope_rotZ, slope_rotY_two]
    simp [rotX, rotZ, sepA, constOne, negSin]
  have c3 : VectorField.mlieBracket 𝓘(ℝ, Coords 4) (fieldOf rotZ) (fieldOf rotY) x 3
      = rotX 3 x := by
    rw [mlieBracket_fieldOf hZ hY 3]
    simp only [Fin.sum_univ_four, slope_rotZ, slope_rotY_three]
    simp [rotX, rotZ, sepA]
  have key : ∀ k, VectorField.mlieBracket 𝓘(ℝ, Coords 4) (fieldOf rotZ) (fieldOf rotY) x k
      = rotX k x := by
    intro k
    fin_cases k
    exacts [c0, c1, c2, c3]
  exact funext key

/-- The three turns of ordinary space, as fields of arrows on coordinate space, in the order in
which the bracket of two of them is the third. -/
noncomputable def turns : Fin 3 → Arrows 𝓘(ℝ, Coords 4) (Coords 4) :=
  ![fieldOf rotY, fieldOf rotX, fieldOf rotZ]

theorem rotY_eq (x : Coords 4) : (fun k ↦ rotY k x)
    = cos (x 3) • (Pi.single 2 1 : Coords 4) + (negCot (x 2) * sin (x 3)) • Pi.single 3 1 := by
  funext k
  fin_cases k <;> simp [rotY, sepA, constOne]

theorem rotX_eq (x : Coords 4) : (fun k ↦ rotX k x)
    = (-sin (x 3)) • (Pi.single 2 1 : Coords 4) + (negCot (x 2) * cos (x 3)) • Pi.single 3 1 := by
  funext k
  fin_cases k <;> simp [rotX, sepA, constOne, negSin]

theorem rotZ_eq (x : Coords 4) : (fun k ↦ rotZ k x) = (Pi.single 3 1 : Coords 4) := by
  funext k
  fin_cases k <;> simp [rotZ]

theorem single_two_eq (x : Coords 4) : (Pi.single 2 1 : Coords 4)
    = cos (x 3) • (fun k ↦ rotY k x) - sin (x 3) • fun k ↦ rotX k x := by
  funext k
  fin_cases k
  · simp [rotX, rotY]
  · simp [rotX, rotY]
  · simp [rotX, rotY, sepA, constOne, negSin]
    linear_combination -(Real.cos_sq_add_sin_sq (x 3))
  · simp [rotX, rotY, sepA]
    ring

/-- At every point, the three turns span the two angle directions. -/
theorem span_turns (x : Coords 4) :
    Submodule.span ℝ (Set.range fun i : Fin 3 ↦ (turns i x : Coords 4))
      = Submodule.span ℝ (Set.range ![(Pi.single 2 1 : Coords 4), Pi.single 3 1]) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · change (fun k ↦ rotY k x) ∈ _
      rw [rotY_eq]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
    · change (fun k ↦ rotX k x) ∈ _
      rw [rotX_eq]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
    · change (fun k ↦ rotZ k x) ∈ _
      rw [rotZ_eq]
      exact Submodule.subset_span ⟨1, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · change (Pi.single 2 1 : Coords 4) ∈ _
      rw [single_two_eq x]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
    · change (Pi.single 3 1 : Coords 4) ∈ _
      rw [← rotZ_eq x]
      exact Submodule.subset_span ⟨2, rfl⟩

theorem finrank_span_angles : Module.finrank ℝ
    (Submodule.span ℝ (Set.range ![(Pi.single 2 1 : Coords 4), Pi.single 3 1])) = 2 := by
  have hli : LinearIndependent ℝ ![(Pi.single 2 1 : Coords 4), Pi.single 3 1] := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    exact ⟨by simpa using congrFun h 2, by simpa using congrFun h 3⟩
  rw [finrank_span_eq_card hli]
  simp

/-- On the two angle directions, a round table gives every step a positive squared length. -/
theorem round_pos_on_angles {A B : ℝ → ℝ} {x : Coords 4} (hr : x 1 ≠ 0) (hs : sin (x 2) ≠ 0)
    (v : Coords 4)
    (hv : v ∈ Submodule.span ℝ (Set.range ![(Pi.single 2 1 : Coords 4), Pi.single 3 1]))
    (hne : v ≠ 0) : 0 < tableMeasure (roundG A B) x v v := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
  have hc : c 0 ≠ 0 ∨ c 1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hne
    simp [Fin.sum_univ_two, hcon.1, hcon.2]
  have e : tableMeasure (roundG A B) x
        (∑ i, c i • ![(Pi.single 2 1 : Coords 4), Pi.single 3 1] i)
        (∑ i, c i • ![(Pi.single 2 1 : Coords 4), Pi.single 3 1] i)
      = x 1 ^ 2 * c 0 ^ 2 + x 1 ^ 2 * sin (x 2) ^ 2 * c 1 ^ 2 := by
    rw [round_measure_apply]
    simp [Fin.sum_univ_two, Fin.sum_univ_four, roundDiag, sep, gr, gθ, sqF, sin2, constOne]
    ring
  rw [e]
  have h1 : 0 < x 1 ^ 2 := sq_pos_iff.mpr hr
  have h2 : 0 < sin (x 2) ^ 2 := sq_pos_iff.mpr hs
  rcases hc with h | h
  · have h3 : 0 < c 0 ^ 2 := sq_pos_iff.mpr h
    nlinarith [mul_pos h1 h3, mul_nonneg (mul_pos h1 h2).le (sq_nonneg (c 1))]
  · have h3 : 0 < c 1 ^ 2 := sq_pos_iff.mpr h
    nlinarith [mul_pos (mul_pos h1 h2) h3, mul_nonneg h1.le (sq_nonneg (c 0))]

/-- **Known answer 3, second half.** Schwarzschild's space-time looks the same from every side,
in the sense of `Basic.lean`: the three turns of ordinary space are smooth, leave the length
measure unchanged, combine the way turns do, and sweep out surfaces on which all lengths are
positive. -/
theorem schwarzschild_isRoundOn (M : ℝ) :
    IsRoundOn (flatMeasure (tableMeasure (roundG (schwA M) (schwB M)))) turns (outside M) where
  smooth := by
    intro i
    fin_cases i
    · exact contMDiffOn_arrows_iff.mpr (contDiffOn_pi.2 fun k x hx ↦
        (smooth_rotY (z := x) hx.2.2 k).contDiffWithinAt)
    · exact contMDiffOn_arrows_iff.mpr (contDiffOn_pi.2 fun k x hx ↦
        (smooth_rotX (z := x) hx.2.2 k).contDiffWithinAt)
    · exact contMDiffOn_arrows_iff.mpr (contDiffOn_pi.2 fun k x _ ↦
        (smooth_rotZ x k).contDiffWithinAt)
  unchanged := by
    intro i x hx
    have hg := fun a b ↦ (schwarzschild_regularTable_outside M).differentiableAt hx a b
    have hround := schwarzschild_isRound M hx.2.2
    fin_cases i
    · exact (leavesUnchangedAt_table_iff hg (differentiableAt_rotY hx.2.2)).mpr hround.2.1
    · exact (leavesUnchangedAt_table_iff hg (differentiableAt_rotX hx.2.2)).mpr hround.1
    · exact (leavesUnchangedAt_table_iff hg (differentiableAt_rotZ x)).mpr hround.2.2
  likeTurns := fun _ hx ↦
    ⟨bracket_rotY_rotX hx.2.2, bracket_rotX_rotZ hx.2.2, bracket_rotZ_rotY hx.2.2⟩
  surfaces := fun x _ ↦ by
    have h := finrank_span_angles
    rw [← span_turns x] at h
    exact h
  positive := fun x hx v hv hne ↦ by
    have hv' : (v : Coords 4)
        ∈ Submodule.span ℝ (Set.range fun i : Fin 3 ↦ (turns i x : Coords 4)) := hv
    rw [span_turns] at hv'
    exact round_pos_on_angles hx.1.ne' hx.2.2 v hv' hne

end Round

end Schwarzschild

end GravityInLean.Curved
