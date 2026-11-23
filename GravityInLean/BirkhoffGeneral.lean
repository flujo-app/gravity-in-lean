/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.GeneralCurvature
public import GravityInLean.Potential
public import GravityInLean.Birkhoff

import Mathlib.Tactic

/-!
# Step 2, from the general round shape: Birkhoff's theorem without a choice of coordinates

`Birkhoff.lean` proved the theorem for a length measure already written with a clock function and
a ruler function. Writing it that way is a choice of coordinates. This file removes that choice.
It starts from the general round shape of `GeneralShape.lean`,

`-A dt² + 2C dt dρ + B dρ² + S (dθ² + sin²θ dφ²)`,

with four free functions of the time `t` and the distance label `ρ`, and proves that an empty
space-time of this shape is Schwarzschild's, after new labels for time and distance.

**What is proved here.**

* `massFn_const`: in an empty round space-time the number `M = (√S / 2) · (1 - |∇√S|²)` is the
  same everywhere. It can be read off at any place from how fast the spheres grow there.
* `birkhoff_general`: where the size of the spheres is a usable distance (`sizeSlopeSq ≠ 0`),
  there is a new time `T(t, ρ)` such that, with the new labels `T` and `r = √S`, the length of
  every step is Schwarzschild's length of the same step. The new labels are differentiable and
  really are coordinates (their Jacobian is not zero).
* `relabel_path`: the meaning of "the same step in new labels": it is the speed of a path, read
  in the new labels (the chain rule).
* `eddington_isEmptyOn`, `eddington_isSchwarzschild`: the assumptions can be met by a space-time
  with a cross term: Eddington's and Finkelstein's way of writing a black hole, which stays
  regular at the rim.

**What is still assumed.** That the length measure has the general round shape; `Symmetry.lean`
shows that this is all that "looks the same from every side" allows. The places where the sphere
size is not a usable distance (the rim itself) are left out of `birkhoff_general`, though not of
`massFn_const`. The definitions of curvature are the classic coordinate formulas, and the poles
are left out, as before.
-/

@[expose] public section

namespace GravityInLean

open Real Filter Topology Set

variable {A B C S : ℝ → ℝ → ℝ} {J I : Set ℝ}

/-! ## The setting -/

/-- The setting of the general theorem: a stretch of times `J` and a stretch of distance labels
`I`, both open and in one piece; on that region the four functions are twice smoothly
differentiable, the time-distance part has one time and one space direction, and the spheres have
a positive size. -/
structure SettingG (A B C S : ℝ → ℝ → ℝ) (J I : Set ℝ) : Prop where
  openJ : IsOpen J
  onePieceJ : IsPreconnected J
  openI : IsOpen I
  onePieceI : IsPreconnected I
  smoothA : ∀ t ∈ J, ∀ ρ ∈ I, TwiceSmooth A t ρ
  smoothB : ∀ t ∈ J, ∀ ρ ∈ I, TwiceSmooth B t ρ
  smoothC : ∀ t ∈ J, ∀ ρ ∈ I, TwiceSmooth C t ρ
  smoothS : ∀ t ∈ J, ∀ ρ ∈ I, TwiceSmooth S t ρ
  spaceTime : ∀ t ∈ J, ∀ ρ ∈ I, 0 < det2 A B C t ρ
  S_pos : ∀ t ∈ J, ∀ ρ ∈ I, 0 < S t ρ

/-- Space-time is empty on the region: Einstein's equation for empty space, all sixteen parts of
it, holds at every point whose time is in `J` and whose distance label is in `I`, away from the
poles. -/
def IsEmptyOnG (A B C S : ℝ → ℝ → ℝ) (J I : Set ℝ) : Prop :=
  ∀ x : Coords 4, x 0 ∈ J → x 1 ∈ I → sin (x 2) ≠ 0 →
    IsRicciFlatAt (genG A B C S) (genGinv A B C S) x

theorem SettingG.regular (h : SettingG A B C S J I) {x : Coords 4} (ht : x 0 ∈ J)
    (hρ : x 1 ∈ I) (hs : sin (x 2) ≠ 0) : RegularG A B C S x where
  sin_ne := hs
  det_ne := (h.spaceTime _ ht _ hρ).ne'
  S_ne := (h.S_pos _ ht _ hρ).ne'
  smoothA := h.smoothA _ ht _ hρ
  smoothB := h.smoothB _ ht _ hρ
  smoothC := h.smoothC _ ht _ hρ
  smoothS := h.smoothS _ ht _ hρ

/-- In an empty round space-time the three size equations hold at every time and distance. -/
theorem SettingG.sizeEquations (h : SettingG A B C S J I) (hE : IsEmptyOnG A B C S J I) {t ρ : ℝ}
    (ht : t ∈ J) (hρ : ρ ∈ I) : SizeEquations A B C S t ρ := by
  have hs : sin (onEquator t ρ 2) ≠ 0 := by simp [onEquator]
  have hreg := h.regular (x := onEquator t ρ) ht hρ hs
  exact GravityInLean.sizeEquations (h.spaceTime t ht ρ hρ).ne' (h.S_pos t ht ρ hρ).ne'
    ((gen_ricciFlat_iff hreg).mp (hE _ ht hρ hs))

/-! ## More slopes -/

section Slopes

variable {t ρ : ℝ}

/-- `C S_t + A S_ρ`. -/
noncomputable def pT (A C S : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ := C t ρ * dt S t ρ + A t ρ * dr S t ρ

theorem hasDerivAt_pT_r (hA : TwiceSmooth A t ρ) (hC : TwiceSmooth C t ρ)
    (hS : TwiceSmooth S t ρ) :
    HasDerivAt (fun s => pT A C S t s)
      (dr C t ρ * dt S t ρ + C t ρ * dr (dt S) t ρ
        + (dr A t ρ * dr S t ρ + A t ρ * dr (dr S) t ρ)) ρ :=
  (hC.slopeR.mul hS.slopeTR).add (hA.slopeR.mul hS.slopeRR)

theorem hasDerivAt_sizeSlopeSq_t (hA : TwiceSmooth A t ρ) (hB : TwiceSmooth B t ρ)
    (hC : TwiceSmooth C t ρ) (hS : TwiceSmooth S t ρ) :
    HasDerivAt (fun s => sizeSlopeSq A B C S s ρ)
      (dt A t ρ * (dr S t ρ * dr S t ρ)
        + A t ρ * (dt (dr S) t ρ * dr S t ρ + dr S t ρ * dt (dr S) t ρ)
        + (2 * dt C t ρ * (dt S t ρ * dr S t ρ)
          + 2 * C t ρ * (dt (dt S) t ρ * dr S t ρ + dt S t ρ * dt (dr S) t ρ))
        - (dt B t ρ * (dt S t ρ * dt S t ρ)
          + B t ρ * (dt (dt S) t ρ * dt S t ρ + dt S t ρ * dt (dt S) t ρ))) t :=
  ((hA.slopeT.mul (hS.slopeRT.mul hS.slopeRT)).add
    ((hC.slopeT.const_mul 2).mul (hS.slopeTT.mul hS.slopeRT))).sub
    (hB.slopeT.mul (hS.slopeTT.mul hS.slopeTT))

theorem hasDerivAt_sizeSlopeSq_r (hA : TwiceSmooth A t ρ) (hB : TwiceSmooth B t ρ)
    (hC : TwiceSmooth C t ρ) (hS : TwiceSmooth S t ρ) :
    HasDerivAt (fun s => sizeSlopeSq A B C S t s)
      (dr A t ρ * (dr S t ρ * dr S t ρ)
        + A t ρ * (dr (dr S) t ρ * dr S t ρ + dr S t ρ * dr (dr S) t ρ)
        + (2 * dr C t ρ * (dt S t ρ * dr S t ρ)
          + 2 * C t ρ * (dr (dt S) t ρ * dr S t ρ + dt S t ρ * dr (dr S) t ρ))
        - (dr B t ρ * (dt S t ρ * dt S t ρ)
          + B t ρ * (dr (dt S) t ρ * dt S t ρ + dt S t ρ * dr (dt S) t ρ))) ρ :=
  ((hA.slopeR.mul (hS.slopeRR.mul hS.slopeRR)).add
    ((hC.slopeR.const_mul 2).mul (hS.slopeTR.mul hS.slopeRR))).sub
    (hB.slopeR.mul (hS.slopeTR.mul hS.slopeTR))

end Slopes

/-! ## The mass -/

/-- The mass inside the sphere at `(t, ρ)`, read off from the size of the sphere and from how fast
the spheres grow there: `(√S / 2) · (1 - |∇√S|²)`. For Schwarzschild's space-time it is `M`. -/
noncomputable def massFn (A B C S : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ :=
  √(S t ρ) / 2 * (1 - radiusSlopeSq A B C S t ρ)

/-- Where the size equations hold, the mass does not change in time. -/
theorem hasDerivAt_massFn_t {t ρ : ℝ} (hA : TwiceSmooth A t ρ) (hB : TwiceSmooth B t ρ)
    (hC : TwiceSmooth C t ρ) (hS : TwiceSmooth S t ρ) (hD : det2 A B C t ρ ≠ 0)
    (hS0 : 0 < S t ρ) (hE : SizeEquations A B C S t ρ) :
    HasDerivAt (fun s => massFn A B C S s ρ) 0 t := by
  obtain ⟨e1, e2, -⟩ := hE
  have hS' := hS0.ne'
  have hden : HasDerivAt (fun s => 4 * (S s ρ * det2 A B C s ρ))
      (4 * (dt S t ρ * det2 A B C t ρ + S t ρ * (dt A t ρ * B t ρ + A t ρ * dt B t ρ
        + (dt C t ρ * C t ρ + C t ρ * dt C t ρ)))) t :=
    (hS.slopeT.mul (hasDerivAt_det2_t hA hB hC)).const_mul 4
  have h0 : 4 * (S t ρ * det2 A B C t ρ) ≠ 0 := mul_ne_zero four_ne_zero (mul_ne_zero hS' hD)
  have hN := (hasDerivAt_sizeSlopeSq_t hA hB hC hS).fun_div hden h0
  have dN : dt (radiusSlopeSq A B C S) t ρ = _ := hN.deriv
  have core : dt S t ρ * (1 - radiusSlopeSq A B C S t ρ)
      - 2 * S t ρ * dt (radiusSlopeSq A B C S) t ρ
      = m0 B C S t ρ / det2 A B C t ρ * (hessTT A B C S t ρ
          - (-(A t ρ) * (1 - radiusSlopeSq A B C S t ρ) + dt S t ρ ^ 2 / (2 * S t ρ)))
        + m1 A C S t ρ / det2 A B C t ρ * (hessTR A B C S t ρ
          - (C t ρ * (1 - radiusSlopeSq A B C S t ρ) + dt S t ρ * dr S t ρ / (2 * S t ρ))) := by
    rw [dN]
    simp only [hS.swap, hessTT, hessTR, radiusSlopeSq, sizeSlopeSq, half, n000, n100, n001, n101,
      m0, m1]
    field_simp
    simp only [det2]
    ring
  have core0 : dt S t ρ * (1 - radiusSlopeSq A B C S t ρ)
      - 2 * S t ρ * dt (radiusSlopeSq A B C S) t ρ = 0 := by
    rw [core, e1, e2]
    ring
  have hw : HasDerivAt (fun s => √(S s ρ)) (√(S t ρ) * (dt S t ρ / (2 * S t ρ))) t :=
    hasDerivAt_sqrt_of_pos hS.slopeT hS0
  have hNd : HasDerivAt (fun s => radiusSlopeSq A B C S s ρ)
      (dt (radiusSlopeSq A B C S) t ρ) t := hN.differentiableAt.hasDerivAt
  have hm : HasDerivAt (fun s => √(S s ρ) / 2 * (1 - radiusSlopeSq A B C S s ρ))
      (√(S t ρ) * (dt S t ρ / (2 * S t ρ)) / 2 * (1 - radiusSlopeSq A B C S t ρ)
        + √(S t ρ) / 2 * -dt (radiusSlopeSq A B C S) t ρ) t :=
    (hw.div_const 2).mul (hNd.const_sub 1)
  refine hm.congr_deriv ?_
  have e : √(S t ρ) * (dt S t ρ / (2 * S t ρ)) / 2 * (1 - radiusSlopeSq A B C S t ρ)
      + √(S t ρ) / 2 * -dt (radiusSlopeSq A B C S) t ρ
      = √(S t ρ) / (4 * S t ρ) * (dt S t ρ * (1 - radiusSlopeSq A B C S t ρ)
        - 2 * S t ρ * dt (radiusSlopeSq A B C S) t ρ) := by
    field_simp
    ring
  rw [e, core0, mul_zero]

/-- Where the size equations hold, the mass does not change with distance. -/
theorem hasDerivAt_massFn_r {t ρ : ℝ} (hA : TwiceSmooth A t ρ) (hB : TwiceSmooth B t ρ)
    (hC : TwiceSmooth C t ρ) (hS : TwiceSmooth S t ρ) (hD : det2 A B C t ρ ≠ 0)
    (hS0 : 0 < S t ρ) (hE : SizeEquations A B C S t ρ) :
    HasDerivAt (fun s => massFn A B C S t s) 0 ρ := by
  obtain ⟨-, e2, e3⟩ := hE
  have hS' := hS0.ne'
  have hden : HasDerivAt (fun s => 4 * (S t s * det2 A B C t s))
      (4 * (dr S t ρ * det2 A B C t ρ + S t ρ * (dr A t ρ * B t ρ + A t ρ * dr B t ρ
        + (dr C t ρ * C t ρ + C t ρ * dr C t ρ)))) ρ :=
    (hS.slopeR.mul (hasDerivAt_det2_r hA hB hC)).const_mul 4
  have h0 : 4 * (S t ρ * det2 A B C t ρ) ≠ 0 := mul_ne_zero four_ne_zero (mul_ne_zero hS' hD)
  have hN := (hasDerivAt_sizeSlopeSq_r hA hB hC hS).fun_div hden h0
  have dN : dr (radiusSlopeSq A B C S) t ρ = _ := hN.deriv
  have core : dr S t ρ * (1 - radiusSlopeSq A B C S t ρ)
      - 2 * S t ρ * dr (radiusSlopeSq A B C S) t ρ
      = m0 B C S t ρ / det2 A B C t ρ * (hessTR A B C S t ρ
          - (C t ρ * (1 - radiusSlopeSq A B C S t ρ) + dt S t ρ * dr S t ρ / (2 * S t ρ)))
        + m1 A C S t ρ / det2 A B C t ρ * (hessRR A B C S t ρ
          - (B t ρ * (1 - radiusSlopeSq A B C S t ρ) + dr S t ρ ^ 2 / (2 * S t ρ))) := by
    rw [dN]
    simp only [hessTR, hessRR, radiusSlopeSq, sizeSlopeSq, half, n001, n101, n011, n111, m0, m1]
    field_simp
    simp only [det2]
    ring
  have core0 : dr S t ρ * (1 - radiusSlopeSq A B C S t ρ)
      - 2 * S t ρ * dr (radiusSlopeSq A B C S) t ρ = 0 := by
    rw [core, e2, e3]
    ring
  have hw : HasDerivAt (fun s => √(S t s)) (√(S t ρ) * (dr S t ρ / (2 * S t ρ))) ρ :=
    hasDerivAt_sqrt_of_pos hS.slopeR hS0
  have hNd : HasDerivAt (fun s => radiusSlopeSq A B C S t s)
      (dr (radiusSlopeSq A B C S) t ρ) ρ := hN.differentiableAt.hasDerivAt
  have hm : HasDerivAt (fun s => √(S t s) / 2 * (1 - radiusSlopeSq A B C S t s))
      (√(S t ρ) * (dr S t ρ / (2 * S t ρ)) / 2 * (1 - radiusSlopeSq A B C S t ρ)
        + √(S t ρ) / 2 * -dr (radiusSlopeSq A B C S) t ρ) ρ :=
    (hw.div_const 2).mul (hNd.const_sub 1)
  refine hm.congr_deriv ?_
  have e : √(S t ρ) * (dr S t ρ / (2 * S t ρ)) / 2 * (1 - radiusSlopeSq A B C S t ρ)
      + √(S t ρ) / 2 * -dr (radiusSlopeSq A B C S) t ρ
      = √(S t ρ) / (4 * S t ρ) * (dr S t ρ * (1 - radiusSlopeSq A B C S t ρ)
        - 2 * S t ρ * dr (radiusSlopeSq A B C S) t ρ) := by
    field_simp
    ring
  rw [e, core0, mul_zero]

/-- Where the size equations hold on a whole region, the mass has the same value everywhere in
it. -/
theorem massFn_const_of_sizeEquations (h : SettingG A B C S J I)
    (hsize : ∀ t ∈ J, ∀ ρ ∈ I, SizeEquations A B C S t ρ) :
    ∀ t ∈ J, ∀ t' ∈ J, ∀ ρ ∈ I, ∀ ρ' ∈ I, massFn A B C S t ρ = massFn A B C S t' ρ' := by
  intro t ht t' ht' ρ hρ ρ' hρ'
  have h1 : massFn A B C S t ρ = massFn A B C S t' ρ :=
    const_of_hasDerivAt_zero (f := fun s => massFn A B C S s ρ) h.openJ h.onePieceJ
      (fun s hs => hasDerivAt_massFn_t (h.smoothA s hs ρ hρ) (h.smoothB s hs ρ hρ)
        (h.smoothC s hs ρ hρ) (h.smoothS s hs ρ hρ) (h.spaceTime s hs ρ hρ).ne'
        (h.S_pos s hs ρ hρ) (hsize s hs ρ hρ)) ht ht'
  have h2 : massFn A B C S t' ρ = massFn A B C S t' ρ' :=
    const_of_hasDerivAt_zero (f := fun s => massFn A B C S t' s) h.openI h.onePieceI
      (fun s hs => hasDerivAt_massFn_r (h.smoothA t' ht' s hs) (h.smoothB t' ht' s hs)
        (h.smoothC t' ht' s hs) (h.smoothS t' ht' s hs) (h.spaceTime t' ht' s hs).ne'
        (h.S_pos t' ht' s hs) (hsize t' ht' s hs)) hρ hρ'
  exact h1.trans h2

/-- **The mass is the same everywhere.** In an empty round space-time the number
`(√S / 2) · (1 - |∇√S|²)` has the same value at every time and every distance. -/
theorem massFn_const (h : SettingG A B C S J I) (hE : IsEmptyOnG A B C S J I) :
    ∀ t ∈ J, ∀ t' ∈ J, ∀ ρ ∈ I, ∀ ρ' ∈ I, massFn A B C S t ρ = massFn A B C S t' ρ' :=
  massFn_const_of_sizeEquations h fun _ ht _ hρ => h.sizeEquations hE ht hρ

/-! ## The new time -/

/-- The slope the new time has to have along the old time. -/
noncomputable def newTimeT (A B C S : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ :=
  √(S t ρ * det2 A B C t ρ) * (2 * pT A C S t ρ / sizeSlopeSq A B C S t ρ)

/-- The slope the new time has to have along the old distance label. -/
noncomputable def newTimeR (A B C S : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ :=
  √(S t ρ * det2 A B C t ρ) * (2 * m0 B C S t ρ / sizeSlopeSq A B C S t ρ)

/-- **The two slopes fit together.** Where the size equations hold, the slope of `newTimeT` along
distance equals the slope of `newTimeR` along time. So a new time with these two slopes exists. -/
theorem newTime_closed {t ρ : ℝ} (hA : TwiceSmooth A t ρ) (hB : TwiceSmooth B t ρ)
    (hC : TwiceSmooth C t ρ) (hS : TwiceSmooth S t ρ) (hD : 0 < det2 A B C t ρ)
    (hS0 : 0 < S t ρ) (hn : sizeSlopeSq A B C S t ρ ≠ 0) (hE : SizeEquations A B C S t ρ) :
    dr (newTimeT A B C S) t ρ = dt (newTimeR A B C S) t ρ := by
  obtain ⟨e1, e2, e3⟩ := hE
  have hSne := hS0.ne'
  have hDne := hD.ne'
  have hX0 : 0 < S t ρ * det2 A B C t ρ := mul_pos hS0 hD
  have hXne := hX0.ne'
  have hXt : HasDerivAt (fun s => S s ρ * det2 A B C s ρ)
      (dt S t ρ * det2 A B C t ρ + S t ρ * (dt A t ρ * B t ρ + A t ρ * dt B t ρ
        + (dt C t ρ * C t ρ + C t ρ * dt C t ρ))) t :=
    hS.slopeT.mul (hasDerivAt_det2_t hA hB hC)
  have hXr : HasDerivAt (fun s => S t s * det2 A B C t s)
      (dr S t ρ * det2 A B C t ρ + S t ρ * (dr A t ρ * B t ρ + A t ρ * dr B t ρ
        + (dr C t ρ * C t ρ + C t ρ * dr C t ρ))) ρ :=
    hS.slopeR.mul (hasDerivAt_det2_r hA hB hC)
  have dP : dr (newTimeT A B C S) t ρ = _ :=
    ((hasDerivAt_sqrt_of_pos hXr hX0).mul
      (((hasDerivAt_pT_r hA hC hS).const_mul 2).fun_div
        (hasDerivAt_sizeSlopeSq_r hA hB hC hS) hn)).deriv
  have dQ : dt (newTimeR A B C S) t ρ = _ :=
    ((hasDerivAt_sqrt_of_pos hXt hX0).mul
      (((hasDerivAt_m0_t hB hC hS).const_mul 2).fun_div
        (hasDerivAt_sizeSlopeSq_t hA hB hC hS) hn)).deriv
  rw [dP, dQ]
  linear_combination (norm := skip)
    (√(S t ρ * det2 A B C t ρ) * 2
        * (-(B t ρ * sizeSlopeSq A B C S t ρ + 2 * m0 B C S t ρ ^ 2)
          / sizeSlopeSq A B C S t ρ ^ 2)) * e1
      + (√(S t ρ * det2 A B C t ρ) * 2
        * ((2 * C t ρ * sizeSlopeSq A B C S t ρ + 4 * pT A C S t ρ * m0 B C S t ρ)
          / sizeSlopeSq A B C S t ρ ^ 2)) * e2
      + (√(S t ρ * det2 A B C t ρ) * 2
        * ((A t ρ * sizeSlopeSq A B C S t ρ - 2 * pT A C S t ρ ^ 2)
          / sizeSlopeSq A B C S t ρ ^ 2)) * e3
  simp only [hS.swap, hessTT, hessTR, hessRR, radiusSlopeSq, half, n000, n100, n001, n101, n011,
    n111, m0, pT]
  field_simp
  simp only [det2, sizeSlopeSq]
  ring

/-- The first slope of the new time can be differentiated, as a function of time and distance
together. -/
theorem differentiableAt_newTimeT {t ρ : ℝ} (hA : TwiceSmooth A t ρ) (hB : TwiceSmooth B t ρ)
    (hC : TwiceSmooth C t ρ) (hS : TwiceSmooth S t ρ) (hD : 0 < det2 A B C t ρ)
    (hS0 : 0 < S t ρ) (hn : sizeSlopeSq A B C S t ρ ≠ 0) :
    DifferentiableAt ℝ (Function.uncurry (newTimeT A B C S)) (t, ρ) := by
  have dA : DifferentiableAt ℝ (fun q : ℝ × ℝ => A q.1 q.2) (t, ρ) := hA.differentiableAt
  have dB : DifferentiableAt ℝ (fun q : ℝ × ℝ => B q.1 q.2) (t, ρ) := hB.differentiableAt
  have dC : DifferentiableAt ℝ (fun q : ℝ × ℝ => C q.1 q.2) (t, ρ) := hC.differentiableAt
  have dS : DifferentiableAt ℝ (fun q : ℝ × ℝ => S q.1 q.2) (t, ρ) := hS.differentiableAt
  have dSt : DifferentiableAt ℝ (fun q : ℝ × ℝ => dt S q.1 q.2) (t, ρ) := hS.differentiableAt_dt
  have dSr : DifferentiableAt ℝ (fun q : ℝ × ℝ => dr S q.1 q.2) (t, ρ) := hS.differentiableAt_dr
  have ddet : DifferentiableAt ℝ (fun q : ℝ × ℝ => det2 A B C q.1 q.2) (t, ρ) :=
    (dA.mul dB).add (dC.mul dC)
  have dn : DifferentiableAt ℝ (fun q : ℝ × ℝ => sizeSlopeSq A B C S q.1 q.2) (t, ρ) :=
    ((dA.mul (dSr.mul dSr)).add ((dC.const_mul 2).mul (dSt.mul dSr))).sub (dB.mul (dSt.mul dSt))
  have dp : DifferentiableAt ℝ (fun q : ℝ × ℝ => pT A C S q.1 q.2) (t, ρ) :=
    (dC.mul dSt).add (dA.mul dSr)
  have dσ : DifferentiableAt ℝ (fun q : ℝ × ℝ => √(S q.1 q.2 * det2 A B C q.1 q.2)) (t, ρ) :=
    (dS.mul ddet).sqrt (mul_pos hS0 hD).ne'
  have dquot : DifferentiableAt ℝ
      (fun q : ℝ × ℝ => 2 * pT A C S q.1 q.2 / sizeSlopeSq A B C S q.1 q.2) (t, ρ) :=
    (dp.const_mul 2).mul (dn.inv hn)
  exact dσ.mul dquot

/-- The second slope of the new time can be differentiated as well. -/
theorem differentiableAt_newTimeR {t ρ : ℝ} (hA : TwiceSmooth A t ρ) (hB : TwiceSmooth B t ρ)
    (hC : TwiceSmooth C t ρ) (hS : TwiceSmooth S t ρ) (hD : 0 < det2 A B C t ρ)
    (hS0 : 0 < S t ρ) (hn : sizeSlopeSq A B C S t ρ ≠ 0) :
    DifferentiableAt ℝ (Function.uncurry (newTimeR A B C S)) (t, ρ) := by
  have dA : DifferentiableAt ℝ (fun q : ℝ × ℝ => A q.1 q.2) (t, ρ) := hA.differentiableAt
  have dB : DifferentiableAt ℝ (fun q : ℝ × ℝ => B q.1 q.2) (t, ρ) := hB.differentiableAt
  have dC : DifferentiableAt ℝ (fun q : ℝ × ℝ => C q.1 q.2) (t, ρ) := hC.differentiableAt
  have dS : DifferentiableAt ℝ (fun q : ℝ × ℝ => S q.1 q.2) (t, ρ) := hS.differentiableAt
  have dSt : DifferentiableAt ℝ (fun q : ℝ × ℝ => dt S q.1 q.2) (t, ρ) := hS.differentiableAt_dt
  have dSr : DifferentiableAt ℝ (fun q : ℝ × ℝ => dr S q.1 q.2) (t, ρ) := hS.differentiableAt_dr
  have ddet : DifferentiableAt ℝ (fun q : ℝ × ℝ => det2 A B C q.1 q.2) (t, ρ) :=
    (dA.mul dB).add (dC.mul dC)
  have dn : DifferentiableAt ℝ (fun q : ℝ × ℝ => sizeSlopeSq A B C S q.1 q.2) (t, ρ) :=
    ((dA.mul (dSr.mul dSr)).add ((dC.const_mul 2).mul (dSt.mul dSr))).sub (dB.mul (dSt.mul dSt))
  have dq : DifferentiableAt ℝ (fun q : ℝ × ℝ => m0 B C S q.1 q.2) (t, ρ) :=
    (dB.mul dSt).sub (dC.mul dSr)
  have dσ : DifferentiableAt ℝ (fun q : ℝ × ℝ => √(S q.1 q.2 * det2 A B C q.1 q.2)) (t, ρ) :=
    (dS.mul ddet).sqrt (mul_pos hS0 hD).ne'
  have dquot : DifferentiableAt ℝ
      (fun q : ℝ × ℝ => 2 * m0 B C S q.1 q.2 / sizeSlopeSq A B C S q.1 q.2) (t, ρ) :=
    (dq.const_mul 2).mul (dn.inv hn)
  exact dσ.mul dquot

/-! ## New labels for time and distance -/

/-- The radius of the sphere at `(t, ρ)`: the square root of its size. -/
noncomputable def radius (S : ℝ → ℝ → ℝ) (t ρ : ℝ) : ℝ := √(S t ρ)

/-- The same point with new labels `T(t, ρ)` and `R(t, ρ)` for time and distance. The two angles
stay as they are. -/
noncomputable def relabel (T R : ℝ → ℝ → ℝ) (x : Coords 4) : Coords 4 :=
  ![T (x 0) (x 1), R (x 0) (x 1), x 2, x 3]

/-- The same step, read in the new labels: its time and distance parts are mixed by the slopes of
the new labels (the chain rule). -/
noncomputable def relabelStep (T R : ℝ → ℝ → ℝ) (x v : Coords 4) : Coords 4 :=
  ![dt T (x 0) (x 1) * v 0 + dr T (x 0) (x 1) * v 1,
    dt R (x 0) (x 1) * v 0 + dr R (x 0) (x 1) * v 1, v 2, v 3]

/-- **What "the same step in new labels" means.** If a path `γ` passes through the point `γ τ`
with speed `v`, then the path read in the new labels passes through `relabel T R (γ τ)` with speed
`relabelStep T R (γ τ) v`. -/
theorem relabel_path {T R : ℝ → ℝ → ℝ} {γ : ℝ → Coords 4} {v : Coords 4} {τ : ℝ}
    (hT : DifferentiableAt ℝ (Function.uncurry T) (γ τ 0, γ τ 1))
    (hR : DifferentiableAt ℝ (Function.uncurry R) (γ τ 0, γ τ 1))
    (hγ : ∀ i, HasDerivAt (fun s => γ s i) (v i) τ) (i : Fin 4) :
    HasDerivAt (fun s => relabel T R (γ s) i) (relabelStep T R (γ τ) v i) τ := by
  fin_cases i
  · exact hasDerivAt_comp_path hT (hγ 0) (hγ 1)
  · exact hasDerivAt_comp_path hR (hγ 0) (hγ 1)
  · exact hγ 2
  · exact hγ 3

/-- The length of a step in the general round shape, written out. -/
theorem stepLength_gen (A B C S : ℝ → ℝ → ℝ) (x v : Coords 4) :
    stepLength (genG A B C S) x v
      = -A (x 0) (x 1) * v 0 ^ 2 + 2 * C (x 0) (x 1) * v 0 * v 1 + B (x 0) (x 1) * v 1 ^ 2
        + S (x 0) (x 1) * v 2 ^ 2 + S (x 0) (x 1) * sin (x 2) ^ 2 * v 3 ^ 2 := by
  simp [stepLength, Fin.sum_univ_four, genG, sep2, gTR, gΘ, negA, zero2, sin2, constOne]
  ring

/-- The heart of the change of labels, for the time-distance part: with the new time slopes and
the slopes of the radius, the old length of a step is Schwarzschild's length of it. -/
theorem timeDistance_relabelled {t ρ : ℝ} (hD : 0 < det2 A B C t ρ) (hS0 : 0 < S t ρ)
    (hn : sizeSlopeSq A B C S t ρ ≠ 0) (v0 v1 : ℝ) :
    -A t ρ * v0 ^ 2 + 2 * C t ρ * v0 * v1 + B t ρ * v1 ^ 2
      = -radiusSlopeSq A B C S t ρ
          * (newTimeT A B C S t ρ * v0 + newTimeR A B C S t ρ * v1) ^ 2
        + (radiusSlopeSq A B C S t ρ)⁻¹
          * (dt S t ρ / (2 * √(S t ρ)) * v0 + dr S t ρ / (2 * √(S t ρ)) * v1) ^ 2 := by
  have hSne := hS0.ne'
  have hDne := hD.ne'
  have hw0 : √(S t ρ) ≠ 0 := (Real.sqrt_pos.mpr hS0).ne'
  have hw2 : √(S t ρ) ^ 2 = S t ρ := Real.sq_sqrt hS0.le
  have hσ2 : √(S t ρ * det2 A B C t ρ) ^ 2 = S t ρ * det2 A B C t ρ :=
    Real.sq_sqrt (mul_pos hS0 hD).le
  have e1 : (newTimeT A B C S t ρ * v0 + newTimeR A B C S t ρ * v1) ^ 2
      = S t ρ * det2 A B C t ρ * (2 * pT A C S t ρ / sizeSlopeSq A B C S t ρ * v0
        + 2 * m0 B C S t ρ / sizeSlopeSq A B C S t ρ * v1) ^ 2 := by
    rw [← hσ2]
    simp only [newTimeT, newTimeR]
    ring
  have e2 : (dt S t ρ / (2 * √(S t ρ)) * v0 + dr S t ρ / (2 * √(S t ρ)) * v1) ^ 2
      = (dt S t ρ * v0 + dr S t ρ * v1) ^ 2 / (4 * S t ρ) := by
    have e2w : (dt S t ρ / (2 * √(S t ρ)) * v0 + dr S t ρ / (2 * √(S t ρ)) * v1) ^ 2
        = (dt S t ρ * v0 + dr S t ρ * v1) ^ 2 / (4 * √(S t ρ) ^ 2) := by
      ring
    rw [e2w, hw2]
  rw [e1, e2]
  simp only [radiusSlopeSq, pT, m0]
  field_simp
  simp only [det2, sizeSlopeSq]
  ring

/-! ## Birkhoff's theorem from the general round shape -/

/-- The general theorem, stated with the three size equations in place of "empty". The theorem
`birkhoff_general` below is this one with the size equations supplied by `sizeEquations`. -/
theorem birkhoff_general_of_sizeEquations (h : SettingG A B C S J I)
    (hsize : ∀ t ∈ J, ∀ ρ ∈ I, SizeEquations A B C S t ρ)
    (hn : ∀ t ∈ J, ∀ ρ ∈ I, sizeSlopeSq A B C S t ρ ≠ 0) :
    ∃ M : ℝ, ∃ T : ℝ → ℝ → ℝ, ∀ x : Coords 4, x 0 ∈ J → x 1 ∈ I →
      massFn A B C S (x 0) (x 1) = M ∧
      DifferentiableAt ℝ (Function.uncurry T) (x 0, x 1) ∧
      DifferentiableAt ℝ (Function.uncurry (radius S)) (x 0, x 1) ∧
      dt T (x 0) (x 1) * dr (radius S) (x 0) (x 1)
        - dr T (x 0) (x 1) * dt (radius S) (x 0) (x 1) ≠ 0 ∧
      ∀ v : Coords 4, stepLength (genG A B C S) x v
        = stepLength (roundG (schwA M) (schwB M)) (relabel T (radius S) x)
            (relabelStep T (radius S) x v) := by
  rcases J.eq_empty_or_nonempty with hJ | ⟨t₀, ht₀⟩
  · exact ⟨0, fun _ _ => 0, fun x hx => by simp [hJ] at hx⟩
  rcases I.eq_empty_or_nonempty with hI | ⟨ρ₀, hρ₀⟩
  · exact ⟨0, fun _ _ => 0, fun x _ hx => by simp [hI] at hx⟩
  obtain ⟨T, hT⟩ := exists_potential (P := newTimeT A B C S) (Q := newTimeR A B C S) h.openJ
    h.onePieceJ h.openI h.onePieceI
    (fun t ht ρ hρ => differentiableAt_newTimeT (h.smoothA t ht ρ hρ) (h.smoothB t ht ρ hρ)
      (h.smoothC t ht ρ hρ) (h.smoothS t ht ρ hρ) (h.spaceTime t ht ρ hρ) (h.S_pos t ht ρ hρ)
      (hn t ht ρ hρ))
    (fun t ht ρ hρ => differentiableAt_newTimeR (h.smoothA t ht ρ hρ) (h.smoothB t ht ρ hρ)
      (h.smoothC t ht ρ hρ) (h.smoothS t ht ρ hρ) (h.spaceTime t ht ρ hρ) (h.S_pos t ht ρ hρ)
      (hn t ht ρ hρ))
    (fun t ht ρ hρ => newTime_closed (h.smoothA t ht ρ hρ) (h.smoothB t ht ρ hρ)
      (h.smoothC t ht ρ hρ) (h.smoothS t ht ρ hρ) (h.spaceTime t ht ρ hρ) (h.S_pos t ht ρ hρ)
      (hn t ht ρ hρ) (hsize t ht ρ hρ))
  refine ⟨massFn A B C S t₀ ρ₀, T, fun x ht hρ => ?_⟩
  obtain ⟨hTd, hTt, hTr⟩ := hT (x 0) ht (x 1) hρ
  have hM : massFn A B C S (x 0) (x 1) = massFn A B C S t₀ ρ₀ :=
    massFn_const_of_sizeEquations h hsize _ ht _ ht₀ _ hρ _ hρ₀
  have hS0 := h.S_pos _ ht _ hρ
  have hD := h.spaceTime _ ht _ hρ
  have hn0 := hn _ ht _ hρ
  have hSne := hS0.ne'
  have hDne := hD.ne'
  have hw0 : √(S (x 0) (x 1)) ≠ 0 := (Real.sqrt_pos.mpr hS0).ne'
  have hw2 : √(S (x 0) (x 1)) ^ 2 = S (x 0) (x 1) := Real.sq_sqrt hS0.le
  have hσ0 : √(S (x 0) (x 1) * det2 A B C (x 0) (x 1)) ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos hS0 hD)).ne'
  have hRt : dt (radius S) (x 0) (x 1) = dt S (x 0) (x 1) / (2 * √(S (x 0) (x 1))) :=
    ((h.smoothS _ ht _ hρ).slopeT.sqrt hSne).deriv
  have hRr : dr (radius S) (x 0) (x 1) = dr S (x 0) (x 1) / (2 * √(S (x 0) (x 1))) :=
    ((h.smoothS _ ht _ hρ).slopeR.sqrt hSne).deriv
  have hRd : DifferentiableAt ℝ (Function.uncurry (radius S)) (x 0, x 1) :=
    (h.smoothS _ ht _ hρ).differentiableAt.sqrt hSne
  refine ⟨hM, hTd, hRd, ?_, fun v => ?_⟩
  · -- The Jacobian is `√(S · det) / √S`.
    have hj : newTimeT A B C S (x 0) (x 1) * (dr S (x 0) (x 1) / (2 * √(S (x 0) (x 1))))
        - newTimeR A B C S (x 0) (x 1) * (dt S (x 0) (x 1) / (2 * √(S (x 0) (x 1))))
        = √(S (x 0) (x 1) * det2 A B C (x 0) (x 1)) / √(S (x 0) (x 1)) := by
      simp only [newTimeT, newTimeR]
      field_simp
      simp only [sizeSlopeSq, pT, m0]
      ring
    rw [hTt, hTr, hRt, hRr, hj]
    exact div_ne_zero hσ0 hw0
  · -- The length of a step.
    have hAs : schwA (massFn A B C S t₀ ρ₀) (√(S (x 0) (x 1)))
        = radiusSlopeSq A B C S (x 0) (x 1) := by
      rw [← hM]
      unfold schwA massFn
      field_simp
      ring
    have hBs : schwB (massFn A B C S t₀ ρ₀) (√(S (x 0) (x 1)))
        = (radiusSlopeSq A B C S (x 0) (x 1))⁻¹ := by
      rw [← hAs]
      rfl
    have key := timeDistance_relabelled hD hS0 hn0 (v 0) (v 1)
    have e : stepLength (roundG (schwA (massFn A B C S t₀ ρ₀)) (schwB (massFn A B C S t₀ ρ₀)))
          (relabel T (radius S) x) (relabelStep T (radius S) x v)
        = -radiusSlopeSq A B C S (x 0) (x 1)
            * (newTimeT A B C S (x 0) (x 1) * v 0 + newTimeR A B C S (x 0) (x 1) * v 1) ^ 2
          + (radiusSlopeSq A B C S (x 0) (x 1))⁻¹
            * (dt S (x 0) (x 1) / (2 * √(S (x 0) (x 1))) * v 0
              + dr S (x 0) (x 1) / (2 * √(S (x 0) (x 1))) * v 1) ^ 2
          + S (x 0) (x 1) * v 2 ^ 2 + S (x 0) (x 1) * sin (x 2) ^ 2 * v 3 ^ 2 := by
      rw [stepLength_round]
      have r1 : relabel T (radius S) x 1 = √(S (x 0) (x 1)) := rfl
      have r2 : relabel T (radius S) x 2 = x 2 := rfl
      have s0 : relabelStep T (radius S) x v 0
          = dt T (x 0) (x 1) * v 0 + dr T (x 0) (x 1) * v 1 := rfl
      have s1 : relabelStep T (radius S) x v 1
          = dt (radius S) (x 0) (x 1) * v 0 + dr (radius S) (x 0) (x 1) * v 1 := rfl
      have s2 : relabelStep T (radius S) x v 2 = v 2 := rfl
      have s3 : relabelStep T (radius S) x v 3 = v 3 := rfl
      rw [r1, r2, s0, s1, s2, s3, hTt, hTr, hRt, hRr, hAs, hBs, hw2]
    rw [stepLength_gen, e]
    linear_combination key

/-- **Birkhoff's theorem, from the general round shape.** Take an empty space-time of the general
round shape, on a region where the size of the spheres is a usable distance. Then there are a
mass `M` and a new time `T(t, ρ)` such that, with the new labels `T` for time and `r = √S` for
distance:

* the mass function equals `M` everywhere;
* both new labels are differentiable, and they really are coordinates near every point (their
  Jacobian is not zero);
* the length of every step equals Schwarzschild's length of the same step.

So every round empty space-time is a piece of Schwarzschild's, written in other coordinates. -/
theorem birkhoff_general (h : SettingG A B C S J I) (hE : IsEmptyOnG A B C S J I)
    (hn : ∀ t ∈ J, ∀ ρ ∈ I, sizeSlopeSq A B C S t ρ ≠ 0) :
    ∃ M : ℝ, ∃ T : ℝ → ℝ → ℝ, ∀ x : Coords 4, x 0 ∈ J → x 1 ∈ I →
      massFn A B C S (x 0) (x 1) = M ∧
      DifferentiableAt ℝ (Function.uncurry T) (x 0, x 1) ∧
      DifferentiableAt ℝ (Function.uncurry (radius S)) (x 0, x 1) ∧
      dt T (x 0) (x 1) * dr (radius S) (x 0) (x 1)
        - dr T (x 0) (x 1) * dt (radius S) (x 0) (x 1) ≠ 0 ∧
      ∀ v : Coords 4, stepLength (genG A B C S) x v
        = stepLength (roundG (schwA M) (schwB M)) (relabel T (radius S) x)
            (relabelStep T (radius S) x v) :=
  birkhoff_general_of_sizeEquations h (fun _ ht _ hρ => h.sizeEquations hE ht hρ) hn

end GravityInLean
