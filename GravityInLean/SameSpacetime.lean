/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Eddington
public import GravityInLean.FreeFall
public import GravityInLean.SamePath
public import GravityInLean.SameSymmetry
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

import Mathlib.Tactic

/-!
# One space-time, written in two ways

`NewCoordinates.lean` proves that the curvature formula does not depend on the coordinates. A
theorem with assumptions needs a check that the assumptions can be met, and a theorem this
general deserves a test on a case where the answer is known by another route. This file gives
both, with the space-time around a mass.

Schwarzschild's way of writing it and Eddington's and Finkelstein's way differ by a change of the
time label only: Eddington's time is Schwarzschild's time plus a function of the distance, the
"tortoise" distance `r + 2M · ln(r - 2M)` of the textbooks.

**What is proved here.**

* `schwarzschild_ricciFlat_inNewCoords`: Schwarzschild's space-time is empty in any coordinates
  whatsoever (three times smoothly differentiable, and such that the re-written length measure
  has an inverse).
* `inNewCoords_toSchw`: Schwarzschild's length measure, re-written with Eddington's time label, is
  exactly the length measure of `Eddington.lean`, cross term and all.
* `eddington_ricciFlat_from_schwarzschild`: so Eddington's and Finkelstein's space-time is empty
  outside the rim, because Schwarzschild's is and emptiness does not depend on the coordinates.

`Eddington.lean` proves the same emptiness by computing the curvature directly. The two routes
share nothing but the definitions, and they agree.

* `birkhoff_general_inNewCoords`: Birkhoff's theorem, said in the language of this file: an empty
  round space-time is Schwarzschild's length measure in other coordinates, entry by entry.
* `eddington_orbit_freeFall`: the free-falling round orbit of step 1, written with Eddington's
  time label, falls freely in Eddington's coordinates too. No connection is computed for this:
  free fall does not depend on the coordinates (`SamePath.lean`).
* `eddington_isRound_from_schwarzschild`: Eddington's space-time looks the same from every side,
  because Schwarzschild's does and "unchanged by a turn" does not depend on the coordinates
  (`SameSymmetry.lean`). `genG_isRound` reaches the same conclusion by direct computation.
-/

@[expose] public section

namespace GravityInLean

open Real Filter Topology Set

/-! ## Smoothness of the pieces -/

/-- A function of the form `f(r) · h(θ)` is as smooth as its two factors. -/
theorem contDiffAt_sep {f h : ℝ → ℝ} {z : Coords 4} (hf : ContDiffAt ℝ 2 f (z 1))
    (hh : ContDiffAt ℝ 2 h (z 2)) : ContDiffAt ℝ 2 (sep f h) z := by
  have h1 : ContDiffAt ℝ 2 (fun y : Coords 4 => f (y 1)) z :=
    ContDiffAt.comp (g := f) z hf (contDiffAt_apply ℝ (fun _ : Fin 4 => ℝ) 1 z)
  have h2 : ContDiffAt ℝ 2 (fun y : Coords 4 => h (y 2)) z :=
    ContDiffAt.comp (g := h) z hh (contDiffAt_apply ℝ (fun _ : Fin 4 => ℝ) 2 z)
  exact h1.mul h2

theorem contDiffAt_roundDiag {a b : ℝ → ℝ} {z : Coords 4} (ha : ContDiffAt ℝ 2 a (z 1))
    (hb : ContDiffAt ℝ 2 b (z 1)) (i : Fin 4) : ContDiffAt ℝ 2 (roundDiag a b i) z := by
  have hgr : ContDiffAt ℝ 2 (gr a b i) (z 1) := by
    unfold gr
    split_ifs
    · exact ha.neg
    · exact hb
    · exact contDiffAt_id.pow 2
  have hgθ : ContDiffAt ℝ 2 (gθ i) (z 2) := by
    unfold gθ
    split_ifs
    · exact (Real.contDiff_sin.contDiffAt).pow 2
    · exact (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : ℝ => (1 : ℝ)) (z 2))
  exact contDiffAt_sep hgr hgθ

/-- Every entry of a round, unchanging length measure is twice smoothly differentiable where its
clock and ruler functions are. -/
theorem contDiffAt_roundG {a b : ℝ → ℝ} {z : Coords 4} (ha : ContDiffAt ℝ 2 a (z 1))
    (hb : ContDiffAt ℝ 2 b (z 1)) (i j : Fin 4) : ContDiffAt ℝ 2 (roundG a b i j) z := by
  by_cases hij : i = j
  · subst hij
    have e : roundG a b i i = roundDiag a b i := by
      funext w
      simp [roundG, diag]
    rw [e]
    exact contDiffAt_roundDiag ha hb i
  · have e : roundG a b i j = fun _ => 0 := by
      funext w
      simp [roundG, diag, hij]
    rw [e]
    exact contDiffAt_const

theorem roundG_symm (a b : ℝ → ℝ) (i j : Fin 4) (z : Coords 4) :
    roundG a b i j z = roundG a b j i z := by
  by_cases hij : i = j
  · subst hij
    rfl
  · simp [roundG, diag, hij, Ne.symm hij]

theorem contDiffAt_schwB (M : ℝ) {r : ℝ} (hr : r ≠ 0) (hh : 1 - 2 * M / r ≠ 0) :
    ContDiffAt ℝ 2 (schwB M) r :=
  (contDiffAt_schwA M hr).inv hh

/-- Near a point outside the rim and away from the poles, every point is outside the rim and away
from the poles. -/
theorem eventually_outside {M : ℝ} {p : Coords 4} (hr : 0 < p 1) (hrim : 2 * M < p 1)
    (hs : sin (p 2) ≠ 0) : ∀ᶠ z in 𝓝 p, 0 < z 1 ∧ 2 * M < z 1 ∧ sin (z 2) ≠ 0 := by
  have c1 : ContinuousAt (fun z : Coords 4 => z 1) p := (continuous_apply 1).continuousAt
  have c2 : ContinuousAt (fun z : Coords 4 => sin (z 2)) p :=
    (Real.continuous_sin.comp (continuous_apply 2)).continuousAt
  exact (c1.eventually (lt_mem_nhds hr)).and
    ((c1.eventually (lt_mem_nhds hrim)).and (c2.eventually_ne hs))

/-! ## Schwarzschild's space-time in any coordinates -/

/-- **Schwarzschild's space-time is empty in any coordinates.** Take any change of coordinates
`Φ` that is three times smoothly differentiable near `x` and lands outside the rim, away from the
poles. If the re-written length measure has an inverse `ginv'` near `x`, it makes space empty at
`x`. -/
theorem schwarzschild_ricciFlat_inNewCoords (M : ℝ) {Φ : Coords 4 → Coords 4}
    {ginv' : Fin 4 → Fin 4 → Coords 4 → ℝ} {x : Coords 4}
    (hΦ : ∀ α, ContDiffAt ℝ 3 (fun z => Φ z α) x) (hr : 0 < Φ x 1) (hrim : 2 * M < Φ x 1)
    (hs : sin (Φ x 2) ≠ 0)
    (hinv' : ∀ᶠ y in 𝓝 x, ∀ μ κ,
      ∑ ν, inNewCoords Φ (roundG (schwA M) (schwB M)) μ ν y * ginv' ν κ y
        = if μ = κ then 1 else 0) :
    IsRicciFlatAt (inNewCoords Φ (roundG (schwA M) (schwB M))) ginv' x := by
  have hr0 : Φ x 1 ≠ 0 := hr.ne'
  have hpos : 0 < 1 - 2 * M / Φ x 1 := by
    rw [sub_pos, div_lt_one hr]
    exact hrim
  have hA := contDiffAt_schwA M hr0
  have hB := contDiffAt_schwB M hr0 hpos.ne'
  refine (isRicciFlatAt_inNewCoords hΦ (fun α β => contDiffAt_roundG hA hB α β)
    (Eventually.of_forall fun z α β => roundG_symm _ _ α β z)
    ((eventually_outside hr hrim hs).mono fun z hz α γ =>
      roundG_mul_roundGinv (schwarzschild_regular M hz.1 hz.2.1 hz.2.2) α γ)
    hinv').mpr ?_
  exact schwarzschild_ricciFlat M hr hrim hs

/-! ## From Eddington's labels to Schwarzschild's -/

/-- The amount by which Eddington's time label runs ahead of Schwarzschild's at the distance `r`:
the "tortoise" distance of the textbooks. -/
noncomputable def tortoise (M r : ℝ) : ℝ := r + 2 * M * Real.log (r - 2 * M)

/-- The tortoise distance grows at the rate of Schwarzschild's ruler function. -/
theorem hasDerivAt_tortoise (M : ℝ) {r : ℝ} (hr : 0 < r) (hrim : 2 * M < r) :
    HasDerivAt (tortoise M) (schwB M r) r := by
  have hne : r - 2 * M ≠ 0 := (sub_pos.mpr hrim).ne'
  have hr0 := hr.ne'
  have h1 : HasDerivAt (fun y : ℝ => y - 2 * M) 1 r := by
    simpa using hasDerivAt_id' r
  have h : HasDerivAt (fun y : ℝ => y + 2 * M * Real.log (y - 2 * M))
      (1 + 2 * M * (1 / (r - 2 * M))) r :=
    (hasDerivAt_id' r).add ((h1.log hne).const_mul (2 * M))
  refine h.congr_deriv ?_
  unfold schwB
  have hh : 1 - 2 * M / r ≠ 0 := by
    have : 0 < 1 - 2 * M / r := by
      rw [sub_pos, div_lt_one hr]
      exact hrim
    exact this.ne'
  field_simp
  ring

theorem contDiffAt_tortoise (M : ℝ) {r : ℝ} (hrim : 2 * M < r) :
    ContDiffAt ℝ 3 (tortoise M) r := by
  have hne : r - 2 * M ≠ 0 := (sub_pos.mpr hrim).ne'
  have h1 : ContDiffAt ℝ 3 (fun y : ℝ => y - 2 * M) r := contDiffAt_id.sub contDiffAt_const
  exact contDiffAt_id.add (contDiffAt_const.mul (h1.log hne))

/-- From Eddington's labels to Schwarzschild's: the time label changes by the tortoise distance,
nothing else changes. -/
noncomputable def toSchw (M : ℝ) (x : Coords 4) : Coords 4 :=
  ![x 0 - tortoise M (x 1), x 1, x 2, x 3]

theorem contDiffAt_toSchw (M : ℝ) {x : Coords 4} (hrim : 2 * M < x 1) (α : Fin 4) :
    ContDiffAt ℝ 3 (fun z => toSchw M z α) x := by
  have p : ∀ k : Fin 4, ContDiffAt ℝ 3 (fun z : Coords 4 => z k) x :=
    fun k => contDiffAt_apply ℝ (fun _ : Fin 4 => ℝ) k x
  have h0 : ContDiffAt ℝ 3 (fun z : Coords 4 => z 0 - tortoise M (z 1)) x :=
    (p 0).sub (ContDiffAt.comp (g := tortoise M) x (contDiffAt_tortoise M hrim) (p 1))
  fin_cases α
  · exact h0
  · exact p 1
  · exact p 2
  · exact p 3

/-- The table of slopes of this change of labels: the identity, except for one entry. -/
theorem jac_toSchw (M : ℝ) {x : Coords 4} (hr : 0 < x 1) (hrim : 2 * M < x 1) (α μ : Fin 4) :
    jac (toSchw M) α μ x
      = if α = 0 ∧ μ = 1 then -schwB M (x 1) else if α = μ then 1 else 0 := by
  have hT := (hasDerivAt_tortoise M hr hrim).deriv
  fin_cases α <;> fin_cases μ <;> simp [jac, slope, toSchw, hT]

/-- **Schwarzschild's length measure, re-written with Eddington's time label, is Eddington's and
Finkelstein's length measure**, cross term and all. -/
theorem inNewCoords_toSchw (M : ℝ) {x : Coords 4} (hr : 0 < x 1) (hrim : 2 * M < x 1)
    (μ ν : Fin 4) :
    inNewCoords (toSchw M) (roundG (schwA M) (schwB M)) μ ν x
      = genG (onlyR (schwA M)) zero2 one2 (onlyR sqF) μ ν x := by
  have hAB := schwA_mul_schwB M hr hrim
  simp only [inNewCoords, Fin.sum_univ_four, jac_toSchw M hr hrim]
  fin_cases μ <;> fin_cases ν <;>
    simp [roundG, diag, roundDiag, sep, gr, gθ, negF, sqF, sin2, constOne, toSchw, genG, sep2,
      gTR, gΘ, negA, onlyR, zero2, one2]
  · linear_combination hAB
  · linear_combination hAB
  · linear_combination -schwB M (x 1) * hAB

/-- **Eddington's and Finkelstein's space-time is empty outside the rim, because Schwarzschild's
is.** The proof computes no curvature. It uses three facts: Schwarzschild's space-time is empty
(step 1), Eddington's length measure is Schwarzschild's in other coordinates
(`inNewCoords_toSchw`), and emptiness does not depend on the coordinates
(`isRicciFlatAt_inNewCoords`). `eddington_isEmptyOn` reaches the same conclusion by computing the
curvature directly. -/
theorem eddington_ricciFlat_from_schwarzschild (M : ℝ) {x : Coords 4} (hr : 0 < x 1)
    (hrim : 2 * M < x 1) (hs : sin (x 2) ≠ 0) :
    IsRicciFlatAt (genG (onlyR (schwA M)) zero2 one2 (onlyR sqF))
      (genGinv (onlyR (schwA M)) zero2 one2 (onlyR sqF)) x := by
  have hnear := eventually_outside hr hrim hs
  -- Near `x`, Eddington's length measure is Schwarzschild's in other coordinates.
  have heq : ∀ μ ν, inNewCoords (toSchw M) (roundG (schwA M) (schwB M)) μ ν
      =ᶠ[𝓝 x] genG (onlyR (schwA M)) zero2 one2 (onlyR sqF) μ ν :=
    fun μ ν => hnear.mono fun y hy => inNewCoords_toSchw M hy.1 hy.2.1 μ ν
  have hset := eddington_setting M isOpen_Ioi isPreconnected_Ioi
    (fun ρ (hρ : ρ ∈ Ioi (0 : ℝ)) => hρ)
  have hinv' : ∀ᶠ y in 𝓝 x, ∀ μ κ,
      ∑ ν, inNewCoords (toSchw M) (roundG (schwA M) (schwB M)) μ ν y
          * genGinv (onlyR (schwA M)) zero2 one2 (onlyR sqF) ν κ y
        = if μ = κ then 1 else 0 :=
    hnear.mono fun y hy μ κ => by
      simp only [inNewCoords_toSchw M hy.1 hy.2.1]
      exact genG_mul_genGinv (hset.spaceTime _ (mem_univ _) _ hy.1).ne'
        (hset.S_pos _ (mem_univ _) _ hy.1).ne' hy.2.2 μ κ
  have h := schwarzschild_ricciFlat_inNewCoords M (Φ := toSchw M) (contDiffAt_toSchw M hrim) hr
    hrim hs hinv'
  exact (isRicciFlatAt_congr heq (fun _ _ => EventuallyEq.rfl)).mp h

/-! ## Re-writing does not change lengths -/

/-- **Re-writing a length measure does not change the length of any step.** A step `v` taken at
`x` in the new coordinates is, in the old coordinates, the step with the parts
`∑ μ, jac Φ α μ x * v μ`. Its length is the same in both. This is what `inNewCoords` means. -/
theorem stepLength_inNewCoords (Φ : Coords 4 → Coords 4) (g : Fin 4 → Fin 4 → Coords 4 → ℝ)
    (x v : Coords 4) :
    stepLength (inNewCoords Φ g) x v
      = stepLength g (Φ x) (fun α => ∑ μ, jac Φ α μ x * v μ) :=
  length_inNewCoords Φ g x v

/-- "The same step in new labels" of `BirkhoffGeneral.lean` is the step re-written with the table
of slopes of the change of labels. -/
theorem relabelStep_eq_jac (T R : ℝ → ℝ → ℝ) (x v : Coords 4) (α : Fin 4) :
    relabelStep T R x v α = ∑ μ, jac (relabel T R) α μ x * v μ := by
  fin_cases α <;> simp [relabelStep, relabel, jac, slope, dt, dr, Fin.sum_univ_four]

/-- A symmetric table of numbers can be read off from the lengths it gives to three steps: one
along `i`, one along `j`, and their sum. -/
theorem entry_of_stepLengths {n : ℕ} {p : Fin n → Fin n → ℝ} (hp : ∀ a b, p a b = p b a)
    (i j : Fin n) :
    2 * p i j
      = (∑ a, ∑ b, p a b * (Pi.single i 1 + Pi.single j 1 : Fin n → ℝ) a
            * (Pi.single i 1 + Pi.single j 1 : Fin n → ℝ) b)
        - (∑ a, ∑ b, p a b * (Pi.single i 1 : Fin n → ℝ) a * (Pi.single i 1 : Fin n → ℝ) b)
        - ∑ a, ∑ b, p a b * (Pi.single j 1 : Fin n → ℝ) a * (Pi.single j 1 : Fin n → ℝ) b := by
  have key : ∀ k l : Fin n,
      ∑ a, ∑ b, p a b * (Pi.single k 1 : Fin n → ℝ) a * (Pi.single l 1 : Fin n → ℝ) b
        = p k l := by
    intro k l
    simp [Pi.single_apply]
  simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib, key]
  rw [hp j i]
  ring

/-- Two symmetric length measures that give every step the same length are the same, entry by
entry. -/
theorem eq_of_stepLength_eq {P Q : Fin 4 → Fin 4 → Coords 4 → ℝ} {x : Coords 4}
    (hP : ∀ i j, P i j x = P j i x) (hQ : ∀ i j, Q i j x = Q j i x)
    (h : ∀ v, stepLength P x v = stepLength Q x v) (i j : Fin 4) : P i j x = Q i j x := by
  have eP := entry_of_stepLengths (p := fun a b => P a b x) hP i j
  have eQ := entry_of_stepLengths (p := fun a b => Q a b x) hQ i j
  have h1 := h (Pi.single i 1 + Pi.single j 1)
  have h2 := h (Pi.single i 1)
  have h3 := h (Pi.single j 1)
  simp only [stepLength] at h1 h2 h3
  beta_reduce at eP eQ
  linarith

/-- Birkhoff's theorem, said with lengths: in an empty space-time of the general round shape,
where the size of the spheres is a usable distance, every step has the length that Schwarzschild's
length measure, written in other coordinates, gives it. -/
theorem birkhoff_general_stepLength {A B C S : ℝ → ℝ → ℝ} {J I : Set ℝ}
    (h : SettingG A B C S J I) (hE : IsEmptyOnG A B C S J I)
    (hn : ∀ t ∈ J, ∀ ρ ∈ I, sizeSlopeSq A B C S t ρ ≠ 0) :
    ∃ M : ℝ, ∃ T : ℝ → ℝ → ℝ, ∀ x : Coords 4, x 0 ∈ J → x 1 ∈ I → ∀ v : Coords 4,
      stepLength (genG A B C S) x v
        = stepLength (inNewCoords (relabel T (radius S)) (roundG (schwA M) (schwB M))) x v := by
  obtain ⟨M, T, hT⟩ := birkhoff_general h hE hn
  refine ⟨M, T, fun x ht hρ v => ?_⟩
  rw [stepLength_inNewCoords, (hT x ht hρ).2.2.2.2 v]
  congr 1
  funext α
  exact relabelStep_eq_jac T (radius S) x v α

/-- **Birkhoff's theorem, in the language of this file.** An empty space-time of the general
round shape, where the size of the spheres is a usable distance, *is* Schwarzschild's length
measure written in other coordinates, entry by entry. Together with
`schwarzschild_ricciFlat_inNewCoords` this closes the circle: empty round space-times are
Schwarzschild's in other coordinates, and Schwarzschild's in other coordinates is empty. -/
theorem birkhoff_general_inNewCoords {A B C S : ℝ → ℝ → ℝ} {J I : Set ℝ}
    (h : SettingG A B C S J I) (hE : IsEmptyOnG A B C S J I)
    (hn : ∀ t ∈ J, ∀ ρ ∈ I, sizeSlopeSq A B C S t ρ ≠ 0) :
    ∃ M : ℝ, ∃ T : ℝ → ℝ → ℝ, ∀ x : Coords 4, x 0 ∈ J → x 1 ∈ I → ∀ μ ν : Fin 4,
      genG A B C S μ ν x
        = inNewCoords (relabel T (radius S)) (roundG (schwA M) (schwB M)) μ ν x := by
  obtain ⟨M, T, hT⟩ := birkhoff_general_stepLength h hE hn
  exact ⟨M, T, fun x ht hρ μ ν => eq_of_stepLength_eq (fun i j => genG_symm A B C S i j x)
    (fun i j => inNewCoords_symm (fun α β => roundG_symm _ _ α β _) i j) (hT x ht hρ) μ ν⟩

/-! ## A free-falling orbit, written in two ways -/

/-- The round orbit of step 1, written with Eddington's time label. -/
noncomputable def eddOrbit (M r tdot φdot τ : ℝ) : Coords 4 :=
  ![tdot * τ + tortoise M r, r, π / 2, φdot * τ]

/-- Changing the time label back gives the round orbit of step 1. -/
theorem toSchw_eddOrbit (M r tdot φdot τ : ℝ) :
    toSchw M (eddOrbit M r tdot φdot τ) = roundOrbit r tdot φdot τ := by
  funext i
  fin_cases i <;> simp [toSchw, eddOrbit, roundOrbit]

/-- **The round orbit falls freely in Eddington's coordinates as well.** At every distance outside
`r = 3M` there is a round orbit that falls freely and is timed by its own clock, when both are
computed from Eddington's and Finkelstein's length measure. No connection is computed for this:
it follows from step 1 (`roundOrbit_freeFall_exists`), because free fall and a path's own time do
not depend on the coordinates. -/
theorem eddington_orbit_freeFall {M r : ℝ} (hM : 0 < M) (hr : 3 * M < r) :
    ∃ tdot φdot : ℝ, 0 < tdot ∧
      (∀ τ, IsFreeFallAt
        (christoffel (genG (onlyR (schwA M)) zero2 one2 (onlyR sqF))
          (genGinv (onlyR (schwA M)) zero2 one2 (onlyR sqF)))
        (eddOrbit M r tdot φdot) τ) ∧
      (∀ τ, KeepsOwnTimeAt (genG (onlyR (schwA M)) zero2 one2 (onlyR sqF))
        (eddOrbit M r tdot φdot) τ) := by
  obtain ⟨tdot, φdot, ht, hfree, hown⟩ := roundOrbit_freeFall_exists hM hr
  have hr0 : 0 < r := by linarith
  have hrim : 2 * M < r := by linarith
  have hset := eddington_setting M isOpen_Ioi isPreconnected_Ioi
    (fun ρ (hρ : ρ ∈ Ioi (0 : ℝ)) => hρ)
  -- The orbit, with its time label changed back, is the orbit of step 1.
  have hpath : (fun s => toSchw M (eddOrbit M r tdot φdot s)) = roundOrbit r tdot φdot :=
    funext fun s => toSchw_eddOrbit M r tdot φdot s
  have hγ : ∀ μ, ContDiff ℝ 2 (fun s => eddOrbit M r tdot φdot s μ) := by
    intro μ
    fin_cases μ
    · exact ((contDiff_const.mul contDiff_id).add contDiff_const :
        ContDiff ℝ 2 (fun s : ℝ => tdot * s + tortoise M r))
    · exact (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => r))
    · exact (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => π / 2))
    · exact (contDiff_const.mul contDiff_id : ContDiff ℝ 2 (fun s : ℝ => φdot * s))
  have hboth : ∀ τ,
      IsFreeFallAt
        (christoffel (genG (onlyR (schwA M)) zero2 one2 (onlyR sqF))
          (genGinv (onlyR (schwA M)) zero2 one2 (onlyR sqF)))
        (eddOrbit M r tdot φdot) τ ∧
      KeepsOwnTimeAt (genG (onlyR (schwA M)) zero2 one2 (onlyR sqF))
        (eddOrbit M r tdot φdot) τ := by
    intro τ
    -- Where the orbit is, in both sets of coordinates.
    have hx1 : eddOrbit M r tdot φdot τ 1 = r := by simp [eddOrbit]
    have hx2 : eddOrbit M r tdot φdot τ 2 = π / 2 := by simp [eddOrbit]
    have hxr : 0 < eddOrbit M r tdot φdot τ 1 := by rw [hx1]; exact hr0
    have hxrim : 2 * M < eddOrbit M r tdot φdot τ 1 := by rw [hx1]; exact hrim
    have hxs : sin (eddOrbit M r tdot φdot τ 2) ≠ 0 := by rw [hx2]; simp
    have hp1 : toSchw M (eddOrbit M r tdot φdot τ) 1 = r := by simp [toSchw, eddOrbit]
    have hp2 : toSchw M (eddOrbit M r tdot φdot τ) 2 = π / 2 := by simp [toSchw, eddOrbit]
    have hpr : 0 < toSchw M (eddOrbit M r tdot φdot τ) 1 := by rw [hp1]; exact hr0
    have hprim : 2 * M < toSchw M (eddOrbit M r tdot φdot τ) 1 := by rw [hp1]; exact hrim
    have hps : sin (toSchw M (eddOrbit M r tdot φdot τ) 2) ≠ 0 := by rw [hp2]; simp
    have hpos : 0 < 1 - 2 * M / toSchw M (eddOrbit M r tdot φdot τ) 1 := by
      rw [sub_pos, div_lt_one hpr]
      exact hprim
    have hA := contDiffAt_schwA M hpr.ne'
    have hB := contDiffAt_schwB M hpr.ne' hpos.ne'
    -- Near the orbit, Eddington's length measure is Schwarzschild's in other coordinates.
    have hnear := eventually_outside hxr hxrim hxs
    have heq : ∀ μ ν, inNewCoords (toSchw M) (roundG (schwA M) (schwB M)) μ ν
        =ᶠ[𝓝 (eddOrbit M r tdot φdot τ)] genG (onlyR (schwA M)) zero2 one2 (onlyR sqF) μ ν :=
      fun μ ν => hnear.mono fun y hy => inNewCoords_toSchw M hy.1 hy.2.1 μ ν
    have hval : ∀ μ ν, inNewCoords (toSchw M) (roundG (schwA M) (schwB M)) μ ν
          (eddOrbit M r tdot φdot τ)
        = genG (onlyR (schwA M)) zero2 one2 (onlyR sqF) μ ν (eddOrbit M r tdot φdot τ) :=
      fun μ ν => (heq μ ν).eq_of_nhds
    have hΦ3 : ∀ α, ContDiffAt ℝ 3 (fun z => toSchw M z α) (eddOrbit M r tdot φdot τ) :=
      fun α => contDiffAt_toSchw M hxrim α
    constructor
    · -- Free fall.
      have hmain := isFreeFallAt_inNewCoords (Φ := toSchw M) (g := roundG (schwA M) (schwB M))
        (ginv := roundGinv (schwA M) (schwB M))
        (ginv' := genGinv (onlyR (schwA M)) zero2 one2 (onlyR sqF))
        (γ := eddOrbit M r tdot φdot) (τ := τ)
        (fun α => (hΦ3 α).of_le (by norm_num)) (fun μ => (hγ μ).contDiffAt)
        (fun α β => (contDiffAt_roundG hA hB α β).differentiableAt (by simp))
        (fun α β => roundG_symm _ _ α β _)
        (fun α δ => roundG_mul_roundGinv (schwarzschild_regular M hpr hprim hps) α δ)
        (fun μ κ => by
          simp only [hval]
          exact genG_mul_genGinv (hset.spaceTime _ (mem_univ _) _ hxr).ne'
            (hset.S_pos _ (mem_univ _) _ hxr).ne' hxs μ κ)
      have h1 : IsFreeFallAt
          (christoffel (inNewCoords (toSchw M) (roundG (schwA M) (schwB M)))
            (genGinv (onlyR (schwA M)) zero2 one2 (onlyR sqF)))
          (eddOrbit M r tdot φdot) τ :=
        hmain.mpr (by rw [hpath]; exact hfree τ)
      have hΓ : ∀ a b c,
          christoffel (inNewCoords (toSchw M) (roundG (schwA M) (schwB M)))
              (genGinv (onlyR (schwA M)) zero2 one2 (onlyR sqF)) a b c
              (eddOrbit M r tdot φdot τ)
            = christoffel (genG (onlyR (schwA M)) zero2 one2 (onlyR sqF))
              (genGinv (onlyR (schwA M)) zero2 one2 (onlyR sqF)) a b c
              (eddOrbit M r tdot φdot τ) :=
        fun a b c => (christoffel_congr heq (fun _ _ => EventuallyEq.rfl) a b c).eq_of_nhds
      intro a
      have h2 := h1 a
      simp only [freeFallExpr, hΓ] at h2 ⊢
      exact h2
    · -- Own time.
      have h1 : KeepsOwnTimeAt (inNewCoords (toSchw M) (roundG (schwA M) (schwB M)))
          (eddOrbit M r tdot φdot) τ :=
        (keepsOwnTimeAt_inNewCoords (Φ := toSchw M) (g := roundG (schwA M) (schwB M))
          (fun α => (hΦ3 α).differentiableAt (by simp))
          (fun μ => (hγ μ).contDiffAt.differentiableAt (by simp))).mpr
          (by rw [hpath]; exact hown τ)
      simp only [KeepsOwnTimeAt, hval] at h1 ⊢
      exact h1
  exact ⟨tdot, φdot, ht, fun τ => (hboth τ).1, fun τ => (hboth τ).2⟩

/-! ## Round, written in two ways -/

/-- A function of the form `f(θ) · h(φ)` can be differentiated where both factors can. -/
theorem differentiableAt_sepA {f h : ℝ → ℝ} {x : Coords 4} (hf : DifferentiableAt ℝ f (x 2))
    (hh : DifferentiableAt ℝ h (x 3)) : DifferentiableAt ℝ (sepA f h) x := by
  have p2 : DifferentiableAt ℝ (fun z : Coords 4 => z 2) x := differentiableAt_apply 2 x
  have p3 : DifferentiableAt ℝ (fun z : Coords 4 => z 3) x := differentiableAt_apply 3 x
  have h1 : DifferentiableAt ℝ (fun z : Coords 4 => f (z 2) * h (z 3)) x :=
    (DifferentiableAt.comp x hf p2).mul (DifferentiableAt.comp x hh p3)
  exact h1

theorem differentiableAt_negCot {θ : ℝ} (hs : sin θ ≠ 0) : DifferentiableAt ℝ negCot θ := by
  have h : HasDerivAt negCot (-((-sin θ * sin θ - cos θ * cos θ) / sin θ ^ 2)) θ :=
    ((Real.hasDerivAt_cos θ).div (Real.hasDerivAt_sin θ) hs).neg
  exact h.differentiableAt

theorem differentiableAt_negSin (φ : ℝ) : DifferentiableAt ℝ negSin φ := by
  have h : DifferentiableAt ℝ (fun y => -sin y) φ := Real.differentiableAt_sin.neg
  exact h

theorem differentiableAt_constOne (θ : ℝ) : DifferentiableAt ℝ constOne θ := by
  have h : DifferentiableAt ℝ (fun _ : ℝ => (1 : ℝ)) θ := differentiableAt_const _
  exact h

/-- The three turns can be differentiated away from the poles. -/
theorem differentiableAt_rotX {x : Coords 4} (hs : sin (x 2) ≠ 0) (k : Fin 4) :
    DifferentiableAt ℝ (rotX k) x := by
  unfold rotX
  split_ifs
  · exact differentiableAt_sepA (differentiableAt_constOne _) (differentiableAt_negSin _)
  · exact differentiableAt_sepA (differentiableAt_negCot hs) Real.differentiableAt_cos
  · exact differentiableAt_const _

theorem differentiableAt_rotY {x : Coords 4} (hs : sin (x 2) ≠ 0) (k : Fin 4) :
    DifferentiableAt ℝ (rotY k) x := by
  unfold rotY
  split_ifs
  · exact differentiableAt_sepA (differentiableAt_constOne _) Real.differentiableAt_cos
  · exact differentiableAt_sepA (differentiableAt_negCot hs) Real.differentiableAt_sin
  · exact differentiableAt_const _

theorem differentiableAt_rotZ (x : Coords 4) (k : Fin 4) : DifferentiableAt ℝ (rotZ k) x := by
  unfold rotZ
  split_ifs <;> exact differentiableAt_const _

/-- A field of arrows that has no part along the distance, and only looks at the two angles, is
the same field with Eddington's time label as with Schwarzschild's. -/
theorem toSchw_keeps_field (M : ℝ) {ξ : Fin 4 → Coords 4 → ℝ} (h1 : ∀ z, ξ 1 z = 0)
    (hang : ∀ k z, ξ k (toSchw M z) = ξ k z) {y : Coords 4} (hr : 0 < y 1)
    (hrim : 2 * M < y 1) (α : Fin 4) :
    ∑ μ, jac (toSchw M) α μ y * ξ μ y = ξ α (toSchw M y) := by
  rw [hang]
  simp only [Fin.sum_univ_four, jac_toSchw M hr hrim]
  fin_cases α <;> simp [h1]

/-- Schwarzschild's space-time looks the same from every side. -/
theorem schwarzschild_isRound (M : ℝ) {p : Coords 4} (hs : sin (p 2) ≠ 0) :
    IsRoundAt (roundG (schwA M) (schwB M)) p := by
  have e : roundG (schwA M) (schwB M)
      = genG (fun _ r => schwA M r) (fun _ r => schwB M r) zero2 (onlyR sqF) := by
    rw [genG_diagonal, changingG_static]
  rw [e]
  exact genG_isRound _ _ _ _ hs

/-- **Eddington's space-time looks the same from every side, because Schwarzschild's does.** No
slope of Eddington's length measure is computed for this. It uses three facts: Schwarzschild's
space-time is round, Eddington's length measure is Schwarzschild's in other coordinates, and
"unchanged by a turn" does not depend on the coordinates (`leavesUnchangedAt_inNewCoords`).
`genG_isRound` reaches the same conclusion by computing directly. -/
theorem eddington_isRound_from_schwarzschild (M : ℝ) {x : Coords 4} (hr : 0 < x 1)
    (hrim : 2 * M < x 1) (hs : sin (x 2) ≠ 0) :
    IsRoundAt (genG (onlyR (schwA M)) zero2 one2 (onlyR sqF)) x := by
  have hnear := eventually_outside hr hrim hs
  have heq : ∀ μ ν, inNewCoords (toSchw M) (roundG (schwA M) (schwB M)) μ ν
      =ᶠ[𝓝 x] genG (onlyR (schwA M)) zero2 one2 (onlyR sqF) μ ν :=
    fun μ ν => hnear.mono fun y hy => inNewCoords_toSchw M hy.1 hy.2.1 μ ν
  -- Where the point is, with Schwarzschild's labels.
  have hp1 : toSchw M x 1 = x 1 := by simp [toSchw]
  have hp2 : toSchw M x 2 = x 2 := by simp [toSchw]
  have hpr : 0 < toSchw M x 1 := by rw [hp1]; exact hr
  have hprim : 2 * M < toSchw M x 1 := by rw [hp1]; exact hrim
  have hps : sin (toSchw M x 2) ≠ 0 := by rw [hp2]; exact hs
  have hpos : 0 < 1 - 2 * M / toSchw M x 1 := by
    rw [sub_pos, div_lt_one hpr]
    exact hprim
  have hA := contDiffAt_schwA M hpr.ne'
  have hB := contDiffAt_schwB M hpr.ne' hpos.ne'
  have hg : ∀ α β, DifferentiableAt ℝ (roundG (schwA M) (schwB M) α β) (toSchw M x) :=
    fun α β => (contDiffAt_roundG hA hB α β).differentiableAt (by simp)
  have hΦ : ∀ α, ContDiffAt ℝ 2 (fun z => toSchw M z α) x :=
    fun α => (contDiffAt_toSchw M hrim α).of_le (by norm_num)
  -- The change of labels loses no direction.
  have hset := eddington_setting M isOpen_Ioi isPreconnected_Ioi
    (fun ρ (hρ : ρ ∈ Ioi (0 : ℝ)) => hρ)
  have hdet : (tab (jac (toSchw M)) x).det ≠ 0 := by
    obtain ⟨K, hK⟩ := exists_inverse_jac (Φ := toSchw M) (g := roundG (schwA M) (schwB M))
      (ginv' := genGinv (onlyR (schwA M)) zero2 one2 (onlyR sqF)) (x := x) (fun μ κ => by
        simp only [inNewCoords_toSchw M hr hrim]
        exact genG_mul_genGinv (hset.spaceTime _ (mem_univ _) _ hr).ne'
          (hset.S_pos _ (mem_univ _) _ hr).ne' hs μ κ)
    exact Matrix.det_ne_zero_of_right_inverse hK
  have hround := schwarzschild_isRound M hps
  -- One field at a time.
  have transfer : ∀ ξ : Fin 4 → Coords 4 → ℝ, (∀ z, ξ 1 z = 0) →
      (∀ k z, ξ k (toSchw M z) = ξ k z) → (∀ k, DifferentiableAt ℝ (ξ k) x) →
      (∀ k, DifferentiableAt ℝ (ξ k) (toSchw M x)) →
      LeavesUnchangedAt (roundG (schwA M) (schwB M)) ξ (toSchw M x) →
      LeavesUnchangedAt (genG (onlyR (schwA M)) zero2 one2 (onlyR sqF)) ξ x := by
    intro ξ h1 hang hd hd' hL
    have hrel : ∀ᶠ y in 𝓝 x, ∀ α, ∑ μ, jac (toSchw M) α μ y * ξ μ y = ξ α (toSchw M y) :=
      hnear.mono fun y hy α => toSchw_keeps_field M h1 hang hy.1 hy.2.1 α
    have h2 := (leavesUnchangedAt_inNewCoords hΦ hg hd' hd hrel hdet).mpr hL
    intro i j
    rw [← lieD_congr heq ξ i j]
    exact h2 i j
  refine ⟨transfer rotX (fun z => by simp [rotX])
      (fun k z => by fin_cases k <;> simp [rotX, sepA, toSchw])
      (differentiableAt_rotX hs) (differentiableAt_rotX hps) hround.1,
    transfer rotY (fun z => by simp [rotY])
      (fun k z => by fin_cases k <;> simp [rotY, sepA, toSchw])
      (differentiableAt_rotY hs) (differentiableAt_rotY hps) hround.2.1,
    transfer rotZ (fun z => by simp [rotZ])
      (fun k z => by fin_cases k <;> simp [rotZ])
      (differentiableAt_rotZ x) (differentiableAt_rotZ _) hround.2.2⟩

end GravityInLean
