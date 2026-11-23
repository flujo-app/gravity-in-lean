/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.RoundChanging
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Real.Sqrt

import Mathlib.Tactic

/-!
# Step 2: it is the only one (Birkhoff's theorem, in coordinates)

Step 1 showed that Schwarzschild's space-time is empty. This file shows the converse: a round
space-time that is empty is Schwarzschild's, even if it is allowed to change in time. In
particular, a round star that pulsates makes no gravity waves outside itself.

**The setting** (`Setting`). A stretch of times `J` and a stretch of distances `I`, both open and in
one piece, all distances positive. On that region the length measure is

`-A(t, r) dt² + B(t, r) dr² + r² dθ² + r² sin²θ dφ²`

with a clock function `A` and a ruler function `B` that are twice smoothly differentiable and not
zero. "Empty" (`IsEmptyOn`) means: Einstein's equation for empty space, all sixteen parts of it,
holds at every point of the region away from the poles.

**What is proved here.**

* `birkhoff`: the space-time is empty on the region exactly when there are a mass `M` and a
  function of time `k` with `B = 1 / (1 - 2M/r)` and `A = k(t) · (1 - 2M/r)` everywhere in it.
* `birkhoff_nothingChanges`: so the ruler function never changes, and clocks at two distances
  keep the same ratio of rates at every time. Nothing that can be measured changes.
* `birkhoff_resetClocks`: when clock and ruler functions are positive, the region lies outside
  the rim (`r > 2M`), and after re-setting the far clocks (a new time `T` with `dT = √k dt`) the
  length of every step is Schwarzschild's length of the same step. The factor `k(t)` is only a
  choice of how the clocks were labelled.
* `static_unique`: the core step in the unchanging case, at one moment of time.
* `schwarzschild_setting`, `schwarzschild_isEmptyOn`, `relabelled_isEmptyOn`: the assumptions can
  be met, by Schwarzschild's space-time itself and by one whose clock labels really do change.

**What is still assumed.** The starting shape: that a round space-time can be written with just a
clock function and a ruler function in these coordinates. The textbooks get there from the
symmetry by a change of coordinates; that step is not done here. The definitions of curvature are
the classic coordinate formulas, and the poles are left out, as in step 1. The mass `M` is not
required to be positive: a negative mass also solves the equations, as it does in the textbooks.
-/

@[expose] public section

namespace GravityInLean

open Real Filter Topology Set

/-! ## The setting -/

/-- The setting of Birkhoff's theorem: a stretch of times `J` and a stretch of distances `I`, both
open and in one piece, all distances positive; on that region the clock function `A` and the
ruler function `B` are twice smoothly differentiable and not zero. -/
structure Setting (A B : ℝ → ℝ → ℝ) (J I : Set ℝ) : Prop where
  openJ : IsOpen J
  onePieceJ : IsPreconnected J
  openI : IsOpen I
  onePieceI : IsPreconnected I
  pos : ∀ r ∈ I, 0 < r
  smoothA : ∀ t ∈ J, ∀ r ∈ I, TwiceSmooth A t r
  smoothB : ∀ t ∈ J, ∀ r ∈ I, TwiceSmooth B t r
  A_ne : ∀ t ∈ J, ∀ r ∈ I, A t r ≠ 0
  B_ne : ∀ t ∈ J, ∀ r ∈ I, B t r ≠ 0

/-- Space-time is empty on the region: Einstein's equation for empty space, all sixteen parts of
it, holds at every point whose time is in `J` and whose distance is in `I`, away from the poles. -/
def IsEmptyOn (A B : ℝ → ℝ → ℝ) (J I : Set ℝ) : Prop :=
  ∀ x : Coords 4, x 0 ∈ J → x 1 ∈ I → sin (x 2) ≠ 0 →
    IsRicciFlatAt (changingG A B) (changingGinv A B) x

variable {A B : ℝ → ℝ → ℝ} {J I : Set ℝ}

theorem Setting.regular (h : Setting A B J I) {x : Coords 4} (ht : x 0 ∈ J) (hr : x 1 ∈ I)
    (hs : sin (x 2) ≠ 0) : Regular2 A B x where
  r_ne := (h.pos _ hr).ne'
  sin_ne := hs
  A_ne := h.A_ne _ ht _ hr
  B_ne := h.B_ne _ ht _ hr
  smoothA := h.smoothA _ ht _ hr
  smoothB := h.smoothB _ ht _ hr

/-- On the region, "empty" means: the four formulas of `RoundChanging.lean` vanish at every time
and distance. The angles do not matter. -/
theorem isEmptyOn_iff (h : Setting A B J I) :
    IsEmptyOn A B J I ↔ ∀ t ∈ J, ∀ r ∈ I, IsEmptyAt A B t r := by
  constructor
  · intro hE t ht r hr
    have hs : sin (onEquator t r 2) ≠ 0 := by simp [onEquator]
    exact (changing_ricciFlat_iff (h.regular (x := onEquator t r) ht hr hs)).mp (hE _ ht hr hs)
  · intro hE x ht hr hs
    exact (changing_ricciFlat_iff (h.regular ht hr hs)).mpr (hE _ ht _ hr)

/-! ## The unchanging case, at one moment -/

/-- **The core step.** On an open stretch of distances in one piece, if the clock and ruler
functions `a` and `b` are not zero, have slopes, and space is empty at every distance (the three
formulas of Piece B vanish), then the product `a · b` is the same at every distance, and `b` is
Schwarzschild's ruler function for some mass `M`. -/
theorem static_unique {a b : ℝ → ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    (hpos : ∀ r ∈ I, 0 < r) (ha : ∀ r ∈ I, a r ≠ 0) (hb : ∀ r ∈ I, b r ≠ 0)
    (hda : ∀ r ∈ I, DifferentiableAt ℝ a r) (hdb : ∀ r ∈ I, DifferentiableAt ℝ b r)
    (hE : ∀ r ∈ I, IsEmptySpaceAt a b r) {r₀ : ℝ} (hr₀ : r₀ ∈ I) :
    ∃ M : ℝ, ∀ r ∈ I, a r * b r = a r₀ * b r₀ ∧ b r = schwB M r := by
  -- The time part and the distance part together say: `a' b + a b' = 0`.
  have key : ∀ r ∈ I, deriv a r * b r + a r * deriv b r = 0 := by
    intro r hr
    obtain ⟨h1, h2, -⟩ := hE r hr
    have hr0 := (hpos r hr).ne'
    have ha0 := ha r hr
    have hb0 := hb r hr
    have e : deriv a r * b r + a r * deriv b r
        = r * b r ^ 2 * ricciTT (a r) (deriv a r) (deriv (deriv a) r) (b r) (deriv b r) r
          + r * a r * b r * ricciRR (a r) (deriv a r) (deriv (deriv a) r) (b r) (deriv b r) r := by
      unfold ricciTT ricciRR
      field_simp
      ring
    linear_combination e + r * b r ^ 2 * h1 + r * a r * b r * h2
  -- So the product `a b` has slope zero.
  have hprod : ∀ r ∈ I, HasDerivAt (fun s => a s * b s) 0 r := by
    intro r hr
    exact ((hda r hr).hasDerivAt.mul (hdb r hr).hasDerivAt).congr_deriv (key r hr)
  -- The part around the mass then says: `r - r / b` has slope zero.
  have hw : ∀ r ∈ I, HasDerivAt (fun s => s - s / b s) 0 r := by
    intro r hr
    obtain ⟨-, -, h3⟩ := hE r hr
    have hr0 := (hpos r hr).ne'
    have ha0 := ha r hr
    have hb0 := hb r hr
    have e : 1 - (1 * b r - r * deriv b r) / b r ^ 2
        = ricciAng (a r) (deriv a r) (b r) (deriv b r) r
          + r / (2 * a r * b r ^ 2) * (deriv a r * b r + a r * deriv b r) := by
      unfold ricciAng
      field_simp
      ring
    refine ((hasDerivAt_id' r).sub ((hasDerivAt_id' r).div (hdb r hr).hasDerivAt hb0)).congr_deriv
      ?_
    linear_combination e + h3 + r / (2 * a r * b r ^ 2) * key r hr
  -- Name the constant value of `r - r / b` as `2M`.
  refine ⟨(r₀ - r₀ / b r₀) / 2, fun r hr => ⟨const_of_hasDerivAt_zero hI hIc hprod hr hr₀, ?_⟩⟩
  have hw' : r - r / b r = r₀ - r₀ / b r₀ := const_of_hasDerivAt_zero hI hIc hw hr hr₀
  have hr0 := (hpos r hr).ne'
  have hb0 := hb r hr
  have e : 1 - 2 * ((r₀ - r₀ / b r₀) / 2) / r = (b r)⁻¹ := by
    rw [← hw']
    field_simp
    ring
  rw [schwB, e, inv_inv]

/-! ## Birkhoff's theorem -/

/-- **Birkhoff's theorem, one direction.** An empty round space-time is Schwarzschild's, up to a
factor `k(t)` in the clock function. -/
theorem birkhoff_forward (h : Setting A B J I) (hE : IsEmptyOn A B J I) :
    ∃ M : ℝ, ∃ k : ℝ → ℝ, ∀ t ∈ J, ∀ r ∈ I, B t r = schwB M r ∧ A t r = k t * schwA M r := by
  have h4 := (isEmptyOn_iff h).mp hE
  -- The mixed time-distance part says: the ruler function does not change in time.
  have hBt : ∀ t ∈ J, ∀ r ∈ I, dt B t r = 0 := by
    intro t ht r hr
    have h3 := (h4 t ht r hr).2.2.1
    unfold ricciTRc at h3
    rcases div_eq_zero_iff.mp h3 with h3 | h3
    · exact h3
    · exact absurd h3 (mul_ne_zero (h.pos r hr).ne' (h.B_ne t ht r hr))
  have hBconst : ∀ r ∈ I, ∀ t ∈ J, ∀ t' ∈ J, B t r = B t' r := by
    intro r hr t ht t' ht'
    refine const_of_hasDerivAt_zero (f := fun s => B s r) h.openJ h.onePieceJ ?_ ht ht'
    intro s hs
    exact (h.smoothB s hs r hr).slopeT.congr_deriv (hBt s hs r hr)
  have hBtt : ∀ t ∈ J, ∀ r ∈ I, dt (dt B) t r = 0 := by
    intro t ht r hr
    refine deriv_eq_zero_of_eventually_const (c := 0) ?_
    filter_upwards [h.openJ.mem_nhds ht] with s hs
    exact hBt s hs r hr
  -- So at each moment the three formulas of the unchanging case vanish.
  have hstatic : ∀ t ∈ J, ∀ r ∈ I, IsEmptySpaceAt (A t) (B t) r := by
    intro t ht r hr
    obtain ⟨h1, h2, -, h3⟩ := h4 t ht r hr
    unfold ricciTTc at h1
    unfold ricciRRc at h2
    unfold ricciAngc at h3
    rw [hBt t ht r hr, hBtt t ht r hr] at h1 h2
    change ricciTT (A t r) (dr A t r) (dr (dr A) t r) (B t r) (dr B t r) r = 0 ∧
      ricciRR (A t r) (dr A t r) (dr (dr A) t r) (B t r) (dr B t r) r = 0 ∧
      ricciAng (A t r) (dr A t r) (B t r) (dr B t r) r = 0
    refine ⟨?_, ?_, h3⟩
    · linear_combination h1
    · linear_combination h2
  rcases J.eq_empty_or_nonempty with hJ | ⟨t₀, ht₀⟩
  · exact ⟨0, fun _ => 0, fun t ht => by simp [hJ] at ht⟩
  rcases I.eq_empty_or_nonempty with hI | ⟨r₀, hr₀⟩
  · exact ⟨0, fun _ => 0, fun t _ r hr => by simp [hI] at hr⟩
  have stat : ∀ t ∈ J, ∃ M : ℝ, ∀ r ∈ I, A t r * B t r = A t r₀ * B t r₀ ∧ B t r = schwB M r :=
    fun t ht => static_unique h.openI h.onePieceI h.pos (fun r hr => h.A_ne t ht r hr)
      (fun r hr => h.B_ne t ht r hr) (fun r hr => (h.smoothA t ht r hr).slopeR.differentiableAt)
      (fun r hr => (h.smoothB t ht r hr).slopeR.differentiableAt) (hstatic t ht) hr₀
  -- The mass comes from one moment; it is the same at all others because `B` does not change.
  obtain ⟨M, hM⟩ := stat t₀ ht₀
  refine ⟨M, fun t => A t r₀ * B t r₀, fun t ht r hr => ?_⟩
  have hB : B t r = schwB M r := (hBconst r hr t ht t₀ ht₀).trans (hM r hr).2
  obtain ⟨M', hM'⟩ := stat t ht
  have hinv : schwA M r = (B t r)⁻¹ := by rw [hB, schwB, inv_inv, schwA]
  refine ⟨hB, ?_⟩
  change A t r = A t r₀ * B t r₀ * schwA M r
  rw [hinv, ← (hM' r hr).1, mul_assoc, mul_inv_cancel₀ (h.B_ne t ht r hr), mul_one]

/-- Schwarzschild's three formulas still vanish when the clock function is multiplied by a
constant `k`. Inside the rim as well as outside, as long as the formulas make sense. -/
theorem scaled_isEmpty (M k : ℝ) {r : ℝ} (hr0 : r ≠ 0) (hh : 1 - 2 * M / r ≠ 0) (hk : k ≠ 0) :
    ricciTT (k * schwA M r) (k * (2 * M / r ^ 2)) (k * (-4 * M / r ^ 3)) (schwB M r)
        (-(2 * M / r ^ 2) / (1 - 2 * M / r) ^ 2) r = 0 ∧
      ricciRR (k * schwA M r) (k * (2 * M / r ^ 2)) (k * (-4 * M / r ^ 3)) (schwB M r)
        (-(2 * M / r ^ 2) / (1 - 2 * M / r) ^ 2) r = 0 ∧
      ricciAng (k * schwA M r) (k * (2 * M / r ^ 2)) (schwB M r)
        (-(2 * M / r ^ 2) / (1 - 2 * M / r) ^ 2) r = 0 := by
  have hne : r - 2 * M ≠ 0 := by
    intro h0
    apply hh
    field_simp
    linarith
  refine ⟨?_, ?_, ?_⟩
  · simp only [ricciTT, schwA, schwB]
    field_simp
    ring
  · simp only [ricciRR, schwA, schwB]
    field_simp
    ring
  · simp only [ricciAng, schwA, schwB]
    field_simp
    ring

/-- **Birkhoff's theorem, the other direction.** Every space-time of that form is empty. -/
theorem birkhoff_converse (h : Setting A B J I)
    (hform : ∃ M : ℝ, ∃ k : ℝ → ℝ, ∀ t ∈ J, ∀ r ∈ I,
      B t r = schwB M r ∧ A t r = k t * schwA M r) :
    IsEmptyOn A B J I := by
  obtain ⟨M, k, hk⟩ := hform
  rw [isEmptyOn_iff h]
  intro t ht r hr
  have hr0 := (h.pos r hr).ne'
  have hB0 := h.B_ne t ht r hr
  have hA0 := h.A_ne t ht r hr
  have hh : 1 - 2 * M / r ≠ 0 := by
    intro h0
    apply hB0
    rw [(hk t ht r hr).1, schwB, h0, inv_zero]
  have hk0 : k t ≠ 0 := by
    intro h0
    apply hA0
    rw [(hk t ht r hr).2, h0, zero_mul]
  -- Along time, the ruler function is constant.
  have hBt : ∀ s ∈ J, dt B s r = 0 := fun s hs =>
    deriv_eq_zero_of_eventually_const (c := schwB M r) (by
      filter_upwards [h.openJ.mem_nhds hs] with u hu
      exact (hk u hu r hr).1)
  have hBtt : dt (dt B) t r = 0 :=
    deriv_eq_zero_of_eventually_const (c := 0) (by
      filter_upwards [h.openJ.mem_nhds ht] with u hu
      exact hBt u hu)
  -- Along the distance, at the time `t`, the slopes are Schwarzschild's.
  have hAr : ∀ s ∈ I, dr A t s = k t * deriv (schwA M) s := by
    intro s hs
    have hs0 := (h.pos s hs).ne'
    have hev : (fun u => A t u) =ᶠ[𝓝 s] fun u => k t * schwA M u := by
      filter_upwards [h.openI.mem_nhds hs] with u hu
      exact (hk t ht u hu).2
    rw [dr, hev.deriv_eq, ((hasDerivAt_schwA M hs0).const_mul (k t)).deriv,
      (hasDerivAt_schwA M hs0).deriv]
  have hA1 : dr A t r = k t * (2 * M / r ^ 2) := by
    rw [hAr r hr, (hasDerivAt_schwA M hr0).deriv]
  have hA2 : dr (dr A) t r = k t * (-4 * M / r ^ 3) := by
    have hev : (fun u => dr A t u) =ᶠ[𝓝 r] fun u => k t * deriv (schwA M) u := by
      filter_upwards [h.openI.mem_nhds hr] with u hu
      exact hAr u hu
    rw [dr, hev.deriv_eq]
    exact ((hasDerivAt_deriv_schwA M hr0).const_mul (k t)).deriv
  have hB1 : dr B t r = -(2 * M / r ^ 2) / (1 - 2 * M / r) ^ 2 := by
    have hev : (fun u => B t u) =ᶠ[𝓝 r] fun u => schwB M u := by
      filter_upwards [h.openI.mem_nhds hr] with u hu
      exact (hk t ht u hu).1
    rw [dr, hev.deriv_eq]
    exact (hasDerivAt_schwB M hr0 hh).deriv
  obtain ⟨e1, e2, e3⟩ := scaled_isEmpty M (k t) hr0 hh hk0
  have hBv := (hk t ht r hr).1
  have hAv := (hk t ht r hr).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold ricciTTc
    rw [hBt t ht, hBtt, hBv, hAv, hA1, hA2, hB1]
    linear_combination e1
  · unfold ricciRRc
    rw [hBt t ht, hBtt, hBv, hAv, hA1, hA2, hB1]
    linear_combination e2
  · unfold ricciTRc
    rw [hBt t ht, zero_div]
  · unfold ricciAngc
    rw [hBv, hAv, hA1, hB1]
    exact e3

/-- **Step 2: Birkhoff's theorem, in coordinates.** A round space-time, allowed to change in time,
is empty on the region exactly when it is Schwarzschild's there: there are a mass `M` and a
function of time `k` with `B = 1 / (1 - 2M/r)` and `A = k(t) · (1 - 2M/r)`. -/
theorem birkhoff (h : Setting A B J I) :
    IsEmptyOn A B J I ↔ ∃ M : ℝ, ∃ k : ℝ → ℝ, ∀ t ∈ J, ∀ r ∈ I,
      B t r = schwB M r ∧ A t r = k t * schwA M r :=
  ⟨birkhoff_forward h, birkhoff_converse h⟩

/-! ## What it means -/

/-- **Nothing changes.** In an empty round space-time the ruler function is the same at every
time, and clocks at two distances keep the same ratio of rates at every time. So a round star
that pulsates sends out no gravity waves: outside it, nothing measurable changes. -/
theorem birkhoff_nothingChanges (h : Setting A B J I) (hE : IsEmptyOn A B J I) :
    ∀ t ∈ J, ∀ t' ∈ J, ∀ r ∈ I, ∀ r' ∈ I,
      B t r = B t' r ∧ A t r * A t' r' = A t' r * A t r' := by
  obtain ⟨M, k, hk⟩ := birkhoff_forward h hE
  intro t ht t' ht' r hr r' hr'
  refine ⟨(hk t ht r hr).1.trans (hk t' ht' r hr).1.symm, ?_⟩
  rw [(hk t ht r hr).2, (hk t' ht' r' hr').2, (hk t' ht' r hr).2, (hk t ht r' hr').2]
  ring

/-- The length of a step `v` taken at the point `x`, as the length measure `g` measures it. -/
noncomputable def stepLength (g : Fin 4 → Fin 4 → Coords 4 → ℝ) (x v : Coords 4) : ℝ :=
  ∑ i, ∑ j, g i j x * v i * v j

/-- The same point, with its time reading `t` replaced by `T(t)`. -/
noncomputable def resetTime (T : ℝ → ℝ) (x : Coords 4) : Coords 4 :=
  Function.update x 0 (T (x 0))

/-- The same step, with its time part stretched by the slope of `T`: how a step looks in the new
time. -/
noncomputable def resetStep (T : ℝ → ℝ) (x v : Coords 4) : Coords 4 :=
  Function.update v 0 (deriv T (x 0) * v 0)

theorem stepLength_changing (A B : ℝ → ℝ → ℝ) (x v : Coords 4) :
    stepLength (changingG A B) x v = -A (x 0) (x 1) * v 0 ^ 2 + B (x 0) (x 1) * v 1 ^ 2
      + x 1 ^ 2 * v 2 ^ 2 + x 1 ^ 2 * sin (x 2) ^ 2 * v 3 ^ 2 := by
  simp [stepLength, Fin.sum_univ_four, changingG, diag, changingDiag, sep2, gtr, gθ, negA, onlyR,
    sqF, sin2, constOne]
  ring

theorem stepLength_round (a b : ℝ → ℝ) (y w : Coords 4) :
    stepLength (roundG a b) y w = -a (y 1) * w 0 ^ 2 + b (y 1) * w 1 ^ 2
      + y 1 ^ 2 * w 2 ^ 2 + y 1 ^ 2 * sin (y 2) ^ 2 * w 3 ^ 2 := by
  simp [stepLength, Fin.sum_univ_four, roundG, diag, roundDiag, sep, gr, gθ, negF, sqF, sin2,
    constOne]
  ring

/-- **Re-setting the clocks.** If clock and ruler functions are positive, an empty round
space-time lies outside the rim (`r > 2M`), and there is a new time `T`, running forwards, such
that the length of every step equals Schwarzschild's length of the same step read in the new time.
So the factor `k(t)` of `birkhoff` is only a choice of clock labels. -/
theorem birkhoff_resetClocks (h : Setting A B J I) (hApos : ∀ t ∈ J, ∀ r ∈ I, 0 < A t r)
    (hBpos : ∀ t ∈ J, ∀ r ∈ I, 0 < B t r) (hE : IsEmptyOn A B J I) :
    ∃ M : ℝ, ∃ T : ℝ → ℝ, (∀ r ∈ I, 2 * M < r) ∧
      ∀ x : Coords 4, x 0 ∈ J → x 1 ∈ I →
        0 < deriv T (x 0) ∧ HasDerivAt T (deriv T (x 0)) (x 0) ∧
        ∀ v : Coords 4, stepLength (changingG A B) x v
          = stepLength (roundG (schwA M) (schwB M)) (resetTime T x) (resetStep T x v) := by
  obtain ⟨M, k, hk⟩ := birkhoff_forward h hE
  rcases J.eq_empty_or_nonempty with hJ | ⟨t₀, ht₀⟩
  · refine ⟨0, id, fun r hr => ?_, fun x hx => by simp [hJ] at hx⟩
    have := h.pos r hr
    linarith
  rcases I.eq_empty_or_nonempty with hI | ⟨r₀, hr₀⟩
  · exact ⟨0, id, fun r hr => by simp [hI] at hr, fun x _ hx => by simp [hI] at hx⟩
  -- Outside the rim.
  have hrim : ∀ r ∈ I, 0 < 1 - 2 * M / r := by
    intro r hr
    have := hBpos t₀ ht₀ r hr
    rw [(hk t₀ ht₀ r hr).1, schwB] at this
    exact inv_pos.mp this
  have hAs : ∀ r ∈ I, 0 < schwA M r := hrim
  -- The clock factor is positive, and continuous in time.
  have hkpos : ∀ t ∈ J, 0 < k t := by
    intro t ht
    have := hApos t ht r₀ hr₀
    rw [(hk t ht r₀ hr₀).2] at this
    exact (pos_iff_pos_of_mul_pos this).mpr (hAs r₀ hr₀)
  have hkcont : ContinuousOn k J := by
    have hc : ContinuousOn (fun t => A t r₀ / schwA M r₀) J := fun t ht =>
      ((h.smoothA t ht r₀ hr₀).slopeT.continuousAt.div_const _).continuousWithinAt
    refine hc.congr fun t ht => ?_
    change k t = A t r₀ / schwA M r₀
    rw [(hk t ht r₀ hr₀).2, mul_div_cancel_right₀ _ (hAs r₀ hr₀).ne']
  have hgcont : ContinuousOn (fun s => √(k s)) J := Real.continuous_sqrt.comp_continuousOn hkcont
  -- The new time: `T(t) = ∫ √k` from `t₀` to `t`.
  have hT : ∀ t ∈ J, HasDerivAt (fun u => ∫ s in t₀..u, √(k s)) (√(k t)) t := by
    intro t ht
    apply intervalIntegral.integral_hasDerivAt_right
    · exact (hgcont.mono (h.onePieceJ.ordConnected.uIcc_subset ht₀ ht)).intervalIntegrable
    · exact hgcont.stronglyMeasurableAtFilter h.openJ t ht
    · exact hgcont.continuousAt (h.openJ.mem_nhds ht)
  refine ⟨M, fun u => ∫ s in t₀..u, √(k s), fun r hr => ?_, fun x ht hr => ?_⟩
  · have := hrim r hr
    rw [sub_pos, div_lt_one (h.pos r hr)] at this
    exact this
  · have hTd := hT (x 0) ht
    have hd := hTd.deriv
    refine ⟨by rw [hd]; exact Real.sqrt_pos.mpr (hkpos _ ht), hTd.differentiableAt.hasDerivAt,
      fun v => ?_⟩
    have e1 : resetTime (fun u => ∫ s in t₀..u, √(k s)) x 1 = x 1 := by simp [resetTime]
    have e2 : resetTime (fun u => ∫ s in t₀..u, √(k s)) x 2 = x 2 := by simp [resetTime]
    have f0 : resetStep (fun u => ∫ s in t₀..u, √(k s)) x v 0
        = deriv (fun u => ∫ s in t₀..u, √(k s)) (x 0) * v 0 := by simp [resetStep]
    have f1 : resetStep (fun u => ∫ s in t₀..u, √(k s)) x v 1 = v 1 := by simp [resetStep]
    have f2 : resetStep (fun u => ∫ s in t₀..u, √(k s)) x v 2 = v 2 := by simp [resetStep]
    have f3 : resetStep (fun u => ∫ s in t₀..u, √(k s)) x v 3 = v 3 := by simp [resetStep]
    rw [stepLength_changing, stepLength_round, e1, e2, f0, f1, f2, f3, hd, (hk _ ht _ hr).1,
      (hk _ ht _ hr).2, mul_pow, Real.sq_sqrt (hkpos _ ht).le]
    ring

/-! ## The assumptions can be met -/

/-- Schwarzschild's space-time, seen as one that might change in time, meets every assumption of
the setting outside the rim. -/
theorem schwarzschild_setting {M : ℝ} (hM : 0 < M) :
    Setting (fun _ r => schwA M r) (fun _ r => schwB M r) univ (Ioi (2 * M)) where
  openJ := isOpen_univ
  onePieceJ := isPreconnected_univ
  openI := isOpen_Ioi
  onePieceI := isPreconnected_Ioi
  pos := fun r hr => by
    have : 2 * M < r := hr
    linarith
  smoothA := fun t _ r hr => by
    have hr0 : r ≠ 0 := by
      have : 2 * M < r := hr
      linarith
    change ContDiffAt ℝ 2 (fun p : ℝ × ℝ => 1 - 2 * M / p.2) (t, r)
    exact contDiffAt_const.sub (contDiffAt_const.div contDiffAt_snd hr0)
  smoothB := fun t _ r hr => by
    have hr' : 0 < r := by
      have : 2 * M < r := hr
      linarith
    have hpos : 0 < 1 - 2 * M / r := by
      rw [sub_pos, div_lt_one hr']
      exact hr
    change ContDiffAt ℝ 2 (fun p : ℝ × ℝ => (1 - 2 * M / p.2)⁻¹) (t, r)
    exact (contDiffAt_const.sub (contDiffAt_const.div contDiffAt_snd hr'.ne')).inv hpos.ne'
  A_ne := fun t _ r hr => by
    have hr' : 0 < r := by
      have : 2 * M < r := hr
      linarith
    have hpos : 0 < 1 - 2 * M / r := by
      rw [sub_pos, div_lt_one hr']
      exact hr
    exact hpos.ne'
  B_ne := fun t _ r hr => by
    have hr' : 0 < r := by
      have : 2 * M < r := hr
      linarith
    have hpos : 0 < 1 - 2 * M / r := by
      rw [sub_pos, div_lt_one hr']
      exact hr
    exact inv_ne_zero hpos.ne'

/-- And it is empty there, now in the sense of this file. -/
theorem schwarzschild_isEmptyOn {M : ℝ} (hM : 0 < M) :
    IsEmptyOn (fun _ r => schwA M r) (fun _ r => schwB M r) univ (Ioi (2 * M)) :=
  (birkhoff (schwarzschild_setting hM)).mpr
    ⟨M, fun _ => 1, fun _ _ _ _ => ⟨rfl, (one_mul _).symm⟩⟩

/-- A space-time whose clock labels really do change in time, `A = (1 + t²)(1 - 2M/r)`, is also
empty. So the factor `k(t)` in `birkhoff` cannot be left out of the statement. -/
theorem relabelled_isEmptyOn {M : ℝ} (hM : 0 < M) :
    IsEmptyOn (fun t r => (1 + t ^ 2) * schwA M r) (fun _ r => schwB M r) univ
      (Ioi (2 * M)) := by
  have hS := schwarzschild_setting hM
  have h : Setting (fun t r => (1 + t ^ 2) * schwA M r) (fun _ r => schwB M r) univ
      (Ioi (2 * M)) :=
    { hS with
      smoothA := fun t ht r hr => by
        change ContDiffAt ℝ 2 (fun p : ℝ × ℝ => (1 + p.1 ^ 2) * schwA M p.2) (t, r)
        exact (contDiffAt_const.add (contDiffAt_fst.pow 2)).mul (hS.smoothA t ht r hr)
      A_ne := fun t ht r hr => mul_ne_zero (by positivity) (hS.A_ne t ht r hr) }
  exact (birkhoff h).mpr ⟨M, fun t => 1 + t ^ 2, fun _ _ _ _ => ⟨rfl, rfl⟩⟩

end GravityInLean
