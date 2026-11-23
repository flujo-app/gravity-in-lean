/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.BirkhoffFromSymmetry

import Mathlib.Tactic

/-!
# An example with a cross term: Eddington's and Finkelstein's coordinates

Every theorem with assumptions needs a check that the assumptions can be met. For the general
theorems of step 2 this file gives one explicitly, and it is one the earlier shape could not
describe.

In 1924 Eddington, and in 1958 Finkelstein, wrote the space-time around a mass with a different
time label `v`:

`-(1 - 2M/ρ) dv² + 2 dv dρ + ρ² (dθ² + sin²θ dφ²)`.

It has a cross term, and no ruler function at all. In the language of `GeneralShape.lean`:
`A = 1 - 2M/ρ`, `B = 0`, `C = 1`, `S = ρ²`. Unlike Schwarzschild's own form it stays regular at the
rim `ρ = 2M`: nothing in it blows up there.

**What is proved here.**

* `eddington_isEmptyOn`: this space-time is empty at every distance `ρ > 0`, the rim and the
  inside included. Computed from the general definitions.
* `eddington_mass`: the mass read off from the size of the spheres is `M`, everywhere.
* `eddington_roundEmpty`: it meets all assumptions of `birkhoff_of_round`.
* `eddington_outside`, `eddington_inside`: so, by the general theorem, outside the rim and inside
  the rim it is Schwarzschild's space-time with the same mass `M`, after a new time label. The rim
  itself is where the theorem does not apply: there the size of the spheres is not a usable
  distance (`sizeSlopeSq = 0`).
-/

@[expose] public section

namespace GravityInLean

open Real Filter Topology Set

/-! ## Functions of the distance alone, and constants -/

/-- The constant function 1 of time and distance. -/
noncomputable def one2 (_t _ρ : ℝ) : ℝ := 1

theorem dt_one2_fun : dt one2 = zero2 := by
  funext t r
  simp [dt, one2, zero2]

theorem dr_one2_fun : dr one2 = zero2 := by
  funext t r
  simp [dr, one2, zero2]

theorem twiceSmooth_onlyR {f : ℝ → ℝ} {ρ : ℝ} (hf : ContDiffAt ℝ 2 f ρ) (t : ℝ) :
    TwiceSmooth (onlyR f) t ρ :=
  ContDiffAt.comp (g := f) (t, ρ) hf contDiffAt_snd

theorem twiceSmooth_zero2 (t ρ : ℝ) : TwiceSmooth zero2 t ρ :=
  (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : ℝ × ℝ => (0 : ℝ)) (t, ρ))

theorem twiceSmooth_one2 (t ρ : ℝ) : TwiceSmooth one2 t ρ :=
  (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : ℝ × ℝ => (1 : ℝ)) (t, ρ))

theorem contDiffAt_schwA (M : ℝ) {r : ℝ} (hr : r ≠ 0) : ContDiffAt ℝ 2 (schwA M) r :=
  contDiffAt_const.sub (contDiffAt_const.div contDiffAt_id hr)

theorem contDiffAt_sqF (r : ℝ) : ContDiffAt ℝ 2 sqF r :=
  contDiffAt_id.pow 2

theorem deriv_deriv_sqF (r : ℝ) : deriv (deriv sqF) r = 2 := by
  have h : deriv sqF = fun y => 2 * y := funext deriv_sqF
  rw [h]
  simp

/-! ## The example -/

/-- Eddington's and Finkelstein's space-time meets the setting of the general theorem on every
stretch of positive distances, across the rim as well. -/
theorem eddington_setting (M : ℝ) {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    (hpos : ∀ ρ ∈ I, 0 < ρ) : SettingG (onlyR (schwA M)) zero2 one2 (onlyR sqF) univ I where
  openJ := isOpen_univ
  onePieceJ := isPreconnected_univ
  openI := hI
  onePieceI := hIc
  smoothA := fun t _ ρ hρ => twiceSmooth_onlyR (contDiffAt_schwA M (hpos ρ hρ).ne') t
  smoothB := fun t _ ρ _ => twiceSmooth_zero2 t ρ
  smoothC := fun t _ ρ _ => twiceSmooth_one2 t ρ
  smoothS := fun t _ ρ _ => twiceSmooth_onlyR (contDiffAt_sqF ρ) t
  spaceTime := fun t _ ρ _ => by simp [det2, zero2, one2]
  S_pos := fun t _ ρ hρ => by
    change 0 < ρ ^ 2
    exact pow_pos (hpos ρ hρ) 2

/-- With a cross term 1 and no ruler function, the time-distance part is never degenerate. -/
theorem eddington_det2 (M t ρ : ℝ) : det2 (onlyR (schwA M)) zero2 one2 t ρ = 1 := by
  simp [det2, zero2, one2]

/-- The four formulas vanish for Eddington's and Finkelstein's space-time, at every distance
other than the centre. -/
theorem eddington_isEmptyG (M t : ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    IsEmptyG (onlyR (schwA M)) zero2 one2 (onlyR sqF) t ρ := by
  have d1 : deriv (schwA M) ρ = 2 * M / ρ ^ 2 := (hasDerivAt_schwA M hρ).deriv
  have d2 : deriv (deriv (schwA M)) ρ = -4 * M / ρ ^ 3 := (hasDerivAt_deriv_schwA M hρ).deriv
  have d3 : deriv sqF ρ = 2 * ρ := deriv_sqF ρ
  have d4 : deriv (deriv sqF) ρ = 2 := deriv_deriv_sqF ρ
  simp only [IsEmptyG, ricciTTg, ricciTRg, ricciRRg, ricciAngG, hessTT, hessTR, hessRR, curv2,
    half, n000, n001, n011, n100, n101, n111, eddington_det2, dt_onlyR_fun, dr_onlyR_fun,
    dt_zero2_fun, dr_zero2_fun, dt_one2_fun, dr_one2_fun, onlyR, zero2, one2, d1, d2, d3, d4]
  unfold schwA sqF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- **Eddington's and Finkelstein's space-time is empty**, at every positive distance, the rim
and the inside of the black hole included. -/
theorem eddington_isEmptyOn (M : ℝ) {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    (hpos : ∀ ρ ∈ I, 0 < ρ) : IsEmptyOnG (onlyR (schwA M)) zero2 one2 (onlyR sqF) univ I :=
  fun x _ hρ hs =>
    (gen_ricciFlat_iff ((eddington_setting M hI hIc hpos).regular (mem_univ _) hρ hs)).mpr
      (eddington_isEmptyG M (x 0) (hpos _ hρ).ne')

/-- The size of the spheres is a usable distance exactly away from the rim. -/
theorem eddington_sizeSlopeSq (M t ρ : ℝ) :
    sizeSlopeSq (onlyR (schwA M)) zero2 one2 (onlyR sqF) t ρ = schwA M ρ * (4 * ρ ^ 2) := by
  simp only [sizeSlopeSq, dt_onlyR_fun, dr_onlyR_fun, onlyR, zero2, one2, deriv_sqF]
  ring

/-- **The mass read off from the spheres is `M`**, at every time and every positive distance. -/
theorem eddington_mass (M t : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    massFn (onlyR (schwA M)) zero2 one2 (onlyR sqF) t ρ = M := by
  have hρ0 := hρ.ne'
  have hsq : √(ρ ^ 2) = ρ := Real.sqrt_sq hρ.le
  simp only [massFn, radiusSlopeSq, eddington_sizeSlopeSq, eddington_det2, onlyR]
  unfold schwA sqF
  rw [hsq]
  field_simp
  ring

/-- It meets all assumptions of `birkhoff_of_round`. -/
theorem eddington_roundEmpty (M : ℝ) {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    (hpos : ∀ ρ ∈ I, 0 < ρ) :
    RoundEmpty (genG (onlyR (schwA M)) zero2 one2 (onlyR sqF))
      (genGinv (onlyR (schwA M)) zero2 one2 (onlyR sqF)) univ I :=
  roundEmpty_genG (eddington_setting M hI hIc hpos) (eddington_isEmptyOn M hI hIc hpos)

/-- **Outside the rim it is Schwarzschild's space-time, with the same mass.** There is a new time
label `T` such that, with the labels `T` and `ρ`, the length of every step in Eddington's and
Finkelstein's space-time is Schwarzschild's length of the same step. -/
theorem eddington_outside {M : ℝ} (hM : 0 < M) :
    ∃ T : ℝ → ℝ → ℝ, ∀ x : Coords 4, 2 * M < x 1 →
      DifferentiableAt ℝ (Function.uncurry T) (x 0, x 1) ∧
      dt T (x 0) (x 1) * dr (radius (onlyR sqF)) (x 0) (x 1)
        - dr T (x 0) (x 1) * dt (radius (onlyR sqF)) (x 0) (x 1) ≠ 0 ∧
      ∀ v : Coords 4, stepLength (genG (onlyR (schwA M)) zero2 one2 (onlyR sqF)) x v
        = stepLength (roundG (schwA M) (schwB M)) (relabel T (radius (onlyR sqF)) x)
            (relabelStep T (radius (onlyR sqF)) x v) := by
  have hpos : ∀ ρ ∈ Ioi (2 * M), 0 < ρ := fun ρ hρ => by
    have : 2 * M < ρ := hρ
    linarith
  have hset := eddington_setting M isOpen_Ioi isPreconnected_Ioi hpos
  have hE := eddington_isEmptyOn M isOpen_Ioi isPreconnected_Ioi hpos
  obtain ⟨M', T, hT⟩ := birkhoff_general hset hE (fun t _ ρ hρ => by
    have h2 : 2 * M < ρ := hρ
    have hρ0 : 0 < ρ := by linarith
    have hA : 0 < schwA M ρ := by
      unfold schwA
      rw [sub_pos, div_lt_one hρ0]
      exact h2
    rw [eddington_sizeSlopeSq]
    exact (mul_pos hA (by positivity)).ne')
  have hmem : (3 * M : ℝ) ∈ Ioi (2 * M) := by
    change 2 * M < 3 * M
    linarith
  have hM' : M' = M := by
    have h := (hT (onEquator 0 (3 * M)) (mem_univ _) hmem).1
    have e : massFn (onlyR (schwA M)) zero2 one2 (onlyR sqF) (onEquator 0 (3 * M) 0)
        (onEquator 0 (3 * M) 1) = M := eddington_mass M _ (by change 0 < 3 * M; linarith)
    rw [← h, e]
  subst hM'
  exact ⟨T, fun x hx => ⟨(hT x (mem_univ _) hx).2.1, (hT x (mem_univ _) hx).2.2.2.1,
    (hT x (mem_univ _) hx).2.2.2.2⟩⟩

/-- **Inside the rim as well.** Between the centre and the rim, the same holds: it is
Schwarzschild's space-time with the mass `M`, in the form Schwarzschild's functions take inside a
black hole (where the "time" label counts a distance and the "distance" label counts time). -/
theorem eddington_inside {M : ℝ} (hM : 0 < M) :
    ∃ T : ℝ → ℝ → ℝ, ∀ x : Coords 4, 0 < x 1 → x 1 < 2 * M →
      DifferentiableAt ℝ (Function.uncurry T) (x 0, x 1) ∧
      dt T (x 0) (x 1) * dr (radius (onlyR sqF)) (x 0) (x 1)
        - dr T (x 0) (x 1) * dt (radius (onlyR sqF)) (x 0) (x 1) ≠ 0 ∧
      ∀ v : Coords 4, stepLength (genG (onlyR (schwA M)) zero2 one2 (onlyR sqF)) x v
        = stepLength (roundG (schwA M) (schwB M)) (relabel T (radius (onlyR sqF)) x)
            (relabelStep T (radius (onlyR sqF)) x v) := by
  have hpos : ∀ ρ ∈ Ioo 0 (2 * M), 0 < ρ := fun ρ hρ => hρ.1
  have hset := eddington_setting M isOpen_Ioo isPreconnected_Ioo hpos
  have hE := eddington_isEmptyOn M isOpen_Ioo isPreconnected_Ioo hpos
  obtain ⟨M', T, hT⟩ := birkhoff_general hset hE (fun t _ ρ hρ => by
    have hρ0 : 0 < ρ := hρ.1
    have hA : schwA M ρ < 0 := by
      unfold schwA
      rw [sub_neg, one_lt_div hρ0]
      exact hρ.2
    rw [eddington_sizeSlopeSq]
    exact mul_ne_zero hA.ne (by positivity))
  have hmem : (M : ℝ) ∈ Ioo 0 (2 * M) := ⟨hM, by linarith⟩
  have hM' : M' = M := by
    have h := (hT (onEquator 0 M) (mem_univ _) hmem).1
    have e : massFn (onlyR (schwA M)) zero2 one2 (onlyR sqF) (onEquator 0 M 0)
        (onEquator 0 M 1) = M := eddington_mass M _ hM
    rw [← h, e]
  subst hM'
  exact ⟨T, fun x hx0 hx => ⟨(hT x (mem_univ _) ⟨hx0, hx⟩).2.1,
    (hT x (mem_univ _) ⟨hx0, hx⟩).2.2.2.1, (hT x (mem_univ _) ⟨hx0, hx⟩).2.2.2.2⟩⟩

end GravityInLean
