/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.BirkhoffGeneral
public import GravityInLean.Symmetry
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

import Mathlib.Tactic

/-!
# Step 2, in full: Birkhoff's theorem from symmetry

This file joins `Symmetry.lean` and `BirkhoffGeneral.lean` into one statement with no particular
shape of the length measure assumed:

**a space-time that looks the same from every side and is empty is Schwarzschild's.**

* `RoundEmpty g ginv J I`: the assumptions, for an arbitrary table `g` of sixteen functions of the
  four coordinates and its inverse `ginv`. The length measure is symmetric, twice smoothly
  differentiable, unchanged by the three turns, of the space-time kind, and makes space empty.
* `birkhoff_of_round`: then, wherever the size of the spheres is a usable distance, there are a
  mass `M` and new labels for time and distance in which the length of every step is
  Schwarzschild's length of the same step.
* `roundEmpty_genG`: the assumptions can be met: every empty space-time of the general round shape
  meets them. `Eddington.lean` gives one explicitly.

On the way: the definitions of connection and curvature only look at what happens near a point
(`slope_congr`, `christoffel_congr`, `ricci_congr`), and a table of numbers has at most one
inverse (`inverse_unique`).

**What is still assumed.** Coordinates `(t, ρ, θ, φ)` in which the three turns move only the two
angles, in the usual way; the classic coordinate formulas for curvature; and the poles and the
rim are left out. Nothing else.
-/

@[expose] public section

namespace GravityInLean

open Real Filter Topology Set

/-! ## The definitions only look near a point -/

/-- Two functions that agree near `x` have the same slopes at `x`. -/
theorem slope_congr {n : ℕ} {f f' : Coords n → ℝ} {x : Coords n} (h : f =ᶠ[𝓝 x] f')
    (i : Fin n) : slope i f x = slope i f' x := by
  have hc : Tendsto (Function.update x i) (𝓝 (x i)) (𝓝 x) := by
    have h1 := (hasDerivAt_update x i (x i)).continuousAt.tendsto
    rwa [Function.update_eq_self] at h1
  exact Filter.EventuallyEq.deriv_eq (hc.eventually h)

/-- Two length measures that agree near `x`, with inverses that agree near `x`, have connections
that agree near `x`. -/
theorem christoffel_congr {n : ℕ} {g g' ginv ginv' : Fin n → Fin n → Coords n → ℝ}
    {x : Coords n} (hg : ∀ i j, g i j =ᶠ[𝓝 x] g' i j)
    (hinv : ∀ i j, ginv i j =ᶠ[𝓝 x] ginv' i j) (a b c : Fin n) :
    christoffel g ginv a b c =ᶠ[𝓝 x] christoffel g' ginv' a b c := by
  have hg' : ∀ᶠ y in 𝓝 x, ∀ i j, g i j =ᶠ[𝓝 y] g' i j :=
    eventually_all.2 fun i => eventually_all.2 fun j => (hg i j).eventuallyEq_nhds
  have hinv' : ∀ᶠ y in 𝓝 x, ∀ i j, ginv i j y = ginv' i j y :=
    eventually_all.2 fun i => eventually_all.2 fun j => hinv i j
  filter_upwards [hg', hinv'] with y hy1 hy2
  simp only [christoffel]
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [hy2 a d, slope_congr (hy1 d c) b, slope_congr (hy1 d b) c, slope_congr (hy1 b c) d]

/-- Two connections that agree near `x` have the same curvature at `x`. -/
theorem ricci_congr {n : ℕ} {Γ Γ' : Fin n → Fin n → Fin n → Coords n → ℝ} {x : Coords n}
    (h : ∀ a b c, Γ a b c =ᶠ[𝓝 x] Γ' a b c) (b c : Fin n) :
    ricci Γ b c x = ricci Γ' b c x := by
  have hs : ∀ a b c i, slope i (Γ a b c) x = slope i (Γ' a b c) x :=
    fun a b c i => slope_congr (h a b c) i
  have hv : ∀ a b c, Γ a b c x = Γ' a b c x := fun a b c => (h a b c).eq_of_nhds
  simp only [ricci, hs, hv]

/-- "Empty at `x`" only depends on the length measure near `x`. -/
theorem isRicciFlatAt_congr {n : ℕ} {g g' ginv ginv' : Fin n → Fin n → Coords n → ℝ}
    {x : Coords n} (hg : ∀ i j, g i j =ᶠ[𝓝 x] g' i j)
    (hinv : ∀ i j, ginv i j =ᶠ[𝓝 x] ginv' i j) :
    IsRicciFlatAt g ginv x ↔ IsRicciFlatAt g' ginv' x := by
  have e : ∀ i j, ricci (christoffel g ginv) i j x = ricci (christoffel g' ginv') i j x :=
    fun i j => ricci_congr (fun a b c => christoffel_congr hg hinv a b c) i j
  simp only [IsRicciFlatAt, e]

/-- A square table of numbers has at most one inverse. -/
theorem inverse_unique {n : ℕ} {m a b : Fin n → Fin n → ℝ}
    (ha : ∀ i k, ∑ j, m i j * a j k = if i = k then 1 else 0)
    (hb : ∀ i k, ∑ j, m i j * b j k = if i = k then 1 else 0) : a = b := by
  have e1 : Matrix.of m * Matrix.of a = 1 := by
    ext i k
    simp [Matrix.mul_apply, Matrix.one_apply, ha]
  have e2 : Matrix.of m * Matrix.of b = 1 := by
    ext i k
    simp [Matrix.mul_apply, Matrix.one_apply, hb]
  exact Matrix.of.injective ((Matrix.inv_eq_right_inv e1).symm.trans (Matrix.inv_eq_right_inv e2))

/-! ## The region and the equator -/

/-- The region is open when the stretches of time and distance are. -/
theorem isOpen_inRegion {J I : Set ℝ} (hJ : IsOpen J) (hI : IsOpen I) :
    IsOpen {x : Coords 4 | InRegion J I x} := by
  have h0 : IsOpen {x : Coords 4 | x 0 ∈ J} := hJ.preimage (continuous_apply 0)
  have h1 : IsOpen {x : Coords 4 | x 1 ∈ I} := hI.preimage (continuous_apply 1)
  have h2 : IsOpen {x : Coords 4 | 0 < x 2} := isOpen_lt continuous_const (continuous_apply 2)
  have h3 : IsOpen {x : Coords 4 | x 2 < π} := isOpen_lt (continuous_apply 2) continuous_const
  exact h0.inter (h1.inter (h2.inter h3))

theorem onEquator_inRegion {J I : Set ℝ} {t ρ : ℝ} (ht : t ∈ J) (hρ : ρ ∈ I) :
    InRegion J I (onEquator t ρ) := by
  refine ⟨ht, hρ, ?_, ?_⟩
  · simp [onEquator, Real.pi_pos]
  · simp [onEquator, Real.pi_pos]

theorem update_onEquator_zero (t ρ s : ℝ) :
    Function.update (onEquator t ρ) 0 s = onEquator s ρ := by
  funext k
  fin_cases k <;> simp [onEquator]

theorem update_onEquator_one (t ρ s : ℝ) :
    Function.update (onEquator t ρ) 1 s = onEquator t s := by
  funext k
  fin_cases k <;> simp [onEquator]

theorem slope_zero_onEquator (f : Coords 4 → ℝ) (t ρ : ℝ) :
    slope 0 f (onEquator t ρ) = dt (fun t ρ => f (onEquator t ρ)) t ρ := by
  simp only [slope, dt, update_onEquator_zero]
  rfl

theorem slope_one_onEquator (f : Coords 4 → ℝ) (t ρ : ℝ) :
    slope 1 f (onEquator t ρ) = dr (fun t ρ => f (onEquator t ρ)) t ρ := by
  simp only [slope, dr, update_onEquator_one]
  rfl

theorem contDiffAt_onEquator (t ρ : ℝ) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ => onEquator q.1 q.2) (t, ρ) := by
  refine contDiffAt_pi.2 fun i => ?_
  fin_cases i
  · exact contDiffAt_fst
  · exact contDiffAt_snd
  · exact contDiffAt_const
  · exact contDiffAt_const

/-- A function that is twice smoothly differentiable at a point of the equator is twice smoothly
differentiable there as a function of time and distance. -/
theorem twiceSmooth_of_equator {f : Coords 4 → ℝ} {t ρ : ℝ}
    (hf : ContDiffAt ℝ 2 f (onEquator t ρ)) : TwiceSmooth (fun t ρ => f (onEquator t ρ)) t ρ :=
  hf.comp (t, ρ) (contDiffAt_onEquator t ρ)

/-! ## The theorem -/

/-- **A round, empty space-time**, on a region, in coordinates in which the turns move only the
two angles. The length measure `g` is any table of sixteen functions of the four coordinates, and
`ginv` is its inverse. -/
structure RoundEmpty (g ginv : Fin 4 → Fin 4 → Coords 4 → ℝ) (J I : Set ℝ) : Prop where
  /-- The stretch of times is open. -/
  openJ : IsOpen J
  /-- The stretch of times is in one piece. -/
  onePieceJ : IsPreconnected J
  /-- The stretch of distance labels is open. -/
  openI : IsOpen I
  /-- The stretch of distance labels is in one piece. -/
  onePieceI : IsPreconnected I
  /-- Every entry is twice smoothly differentiable. -/
  smooth : ∀ x, InRegion J I x → ∀ i j, ContDiffAt ℝ 2 (g i j) x
  /-- The table is symmetric, as every length measure is. -/
  symm : ∀ x, InRegion J I x → ∀ i j, g i j x = g j i x
  /-- It looks the same from every side. -/
  round : ∀ x, InRegion J I x → IsRoundAt g x
  /-- It is of the space-time kind: the spheres have a positive size, and the rest has one time
  direction and one space direction. -/
  spaceTime : ∀ x, InRegion J I x → 0 < g 2 2 x ∧ g 0 0 x * g 1 1 x - g 0 1 x * g 0 1 x < 0
  /-- `ginv` is the inverse of `g`. -/
  inverse : ∀ x, InRegion J I x → ∀ i k, ∑ j, g i j x * ginv j k x = if i = k then 1 else 0
  /-- Space is empty: Einstein's equation for empty space, all sixteen parts of it. -/
  empty : ∀ x, InRegion J I x → IsRicciFlatAt g ginv x

/-- The slope of the size of the spheres, squared and measured by the rest of the length measure.
It is zero exactly where the size of the spheres changes in no direction, or only along the path
of a light ray. The rim of a black hole is such a place. -/
noncomputable def sizeSlopeOf (g : Fin 4 → Fin 4 → Coords 4 → ℝ) (x : Coords 4) : ℝ :=
  -g 0 0 x * (slope 1 (g 2 2) x * slope 1 (g 2 2) x)
    + 2 * g 0 1 x * (slope 0 (g 2 2) x * slope 1 (g 2 2) x)
    - g 1 1 x * (slope 0 (g 2 2) x * slope 0 (g 2 2) x)

/-- The four functions read off from a round, empty space-time meet the setting of the general
theorem. -/
theorem RoundEmpty.settingG {g ginv : Fin 4 → Fin 4 → Coords 4 → ℝ} {J I : Set ℝ}
    (h : RoundEmpty g ginv J I) :
    SettingG (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) J I where
  openJ := h.openJ
  onePieceJ := h.onePieceJ
  openI := h.openI
  onePieceI := h.onePieceI
  smoothA := fun _ ht _ hρ =>
    (twiceSmooth_of_equator (h.smooth _ (onEquator_inRegion ht hρ) 0 0)).neg
  smoothB := fun _ ht _ hρ => twiceSmooth_of_equator (h.smooth _ (onEquator_inRegion ht hρ) 1 1)
  smoothC := fun _ ht _ hρ => twiceSmooth_of_equator (h.smooth _ (onEquator_inRegion ht hρ) 0 1)
  smoothS := fun _ ht _ hρ => twiceSmooth_of_equator (h.smooth _ (onEquator_inRegion ht hρ) 2 2)
  spaceTime := fun t ht ρ hρ => by
    have hk := (h.spaceTime _ (onEquator_inRegion ht hρ)).2
    change 0 < -g 0 0 (onEquator t ρ) * g 1 1 (onEquator t ρ)
      + g 0 1 (onEquator t ρ) * g 0 1 (onEquator t ρ)
    linarith
  S_pos := fun _ ht _ hρ => (h.spaceTime _ (onEquator_inRegion ht hρ)).1

/-- **Birkhoff's theorem, from symmetry.** Take a space-time that looks the same from every side
and is empty, with no particular shape assumed. On a region where the size of the spheres is a
usable distance, there are a mass `M` and a new time `T` such that, with the new labels `T` for
time and "radius of the sphere" for distance:

* both new labels are differentiable, and they really are coordinates near every point;
* the length of every step equals Schwarzschild's length of the same step.

So a round, empty space-time is Schwarzschild's, whatever coordinates it was first written in,
and whether or not it seemed to change in time. -/
theorem birkhoff_of_round {g ginv : Fin 4 → Fin 4 → Coords 4 → ℝ} {J I : Set ℝ}
    (h : RoundEmpty g ginv J I) (husable : ∀ x, InRegion J I x → sizeSlopeOf g x ≠ 0) :
    ∃ M : ℝ, ∃ T : ℝ → ℝ → ℝ, ∀ x, InRegion J I x →
      DifferentiableAt ℝ (Function.uncurry T) (x 0, x 1) ∧
      DifferentiableAt ℝ (Function.uncurry (radius (sizeOf g))) (x 0, x 1) ∧
      dt T (x 0) (x 1) * dr (radius (sizeOf g)) (x 0) (x 1)
        - dr T (x 0) (x 1) * dt (radius (sizeOf g)) (x 0) (x 1) ≠ 0 ∧
      ∀ v : Coords 4, stepLength g x v
        = stepLength (roundG (schwA M) (schwB M)) (relabel T (radius (sizeOf g)) x)
            (relabelStep T (radius (sizeOf g)) x v) := by
  -- Symmetry gives the shape.
  have hshape := shape_of_round h.symm
    (fun x hx i j => (h.smooth x hx i j).differentiableAt (by simp)) h.round
  have hset := h.settingG
  -- Empty, in the sense of the general round shape, at every point of the equator.
  have hsize : ∀ t ∈ J, ∀ ρ ∈ I,
      SizeEquations (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) t ρ := by
    intro t ht ρ hρ
    have hx : InRegion J I (onEquator t ρ) := onEquator_inRegion ht hρ
    have hnear : ∀ᶠ y in 𝓝 (onEquator t ρ), InRegion J I y :=
      (isOpen_inRegion h.openJ h.openI).mem_nhds hx
    have hg : ∀ i j, g i j
        =ᶠ[𝓝 (onEquator t ρ)] genG (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) i j :=
      fun i j => hnear.mono fun y hy => hshape y hy i j
    have hgi : ∀ i j, ginv i j
        =ᶠ[𝓝 (onEquator t ρ)] genGinv (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) i j := by
      intro i j
      refine hnear.mono fun y hy => ?_
      have hu := inverse_unique (m := fun i j => g i j y) (a := fun i j => ginv i j y)
        (b := fun i j => genGinv (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) i j y)
        (h.inverse y hy) (fun i k => by
          simp only [hshape y hy]
          exact genG_mul_genGinv (hset.spaceTime _ hy.1 _ hy.2.1).ne'
            (hset.S_pos _ hy.1 _ hy.2.1).ne' hy.sin_ne i k)
      exact congrFun (congrFun hu i) j
    have hflat := (isRicciFlatAt_congr hg hgi).mp (h.empty _ hx)
    have hreg := hset.regular (x := onEquator t ρ) ht hρ hx.sin_ne
    exact sizeEquations (hset.spaceTime t ht ρ hρ).ne' (hset.S_pos t ht ρ hρ).ne'
      ((gen_ricciFlat_iff hreg).mp hflat)
  -- The size of the spheres is a usable distance.
  have hn : ∀ t ∈ J, ∀ ρ ∈ I,
      sizeSlopeSq (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) t ρ ≠ 0 := by
    intro t ht ρ hρ
    have hu := husable _ (onEquator_inRegion (J := J) (I := I) ht hρ)
    have e : sizeSlopeSq (clockOf g) (rulerOf g) (crossOf g) (sizeOf g) t ρ
        = sizeSlopeOf g (onEquator t ρ) := by
      simp only [sizeSlopeSq, sizeSlopeOf, slope_zero_onEquator, slope_one_onEquator]
      rfl
    rwa [e]
  obtain ⟨M, T, hT⟩ := birkhoff_general_of_sizeEquations hset hsize hn
  refine ⟨M, T, fun x hx => ?_⟩
  obtain ⟨-, h1, h2, h3, h4⟩ := hT x hx.1 hx.2.1
  refine ⟨h1, h2, h3, fun v => ?_⟩
  rw [← h4 v]
  simp only [stepLength, hshape x hx]

/-! ## The assumptions can be met -/

variable {A B C S : ℝ → ℝ → ℝ} {J I : Set ℝ}

/-- The general round shape is symmetric. -/
theorem genG_symm (A B C S : ℝ → ℝ → ℝ) (i j : Fin 4) (x : Coords 4) :
    genG A B C S i j x = genG A B C S j i x := by
  fin_cases i <;> fin_cases j <;> simp [genG, sep2, gTR, gΘ]

/-- A function of the form `F(t, ρ) · h(θ)` is twice smoothly differentiable where both factors
are. -/
theorem contDiffAt_sep2 {F : ℝ → ℝ → ℝ} {h : ℝ → ℝ} {x : Coords 4}
    (hF : TwiceSmooth F (x 0) (x 1)) (hh : ContDiffAt ℝ 2 h (x 2)) :
    ContDiffAt ℝ 2 (sep2 F h) x := by
  have hpair : ContDiffAt ℝ 2 (fun y : Coords 4 => (y 0, y 1)) x :=
    (contDiffAt_apply ℝ (fun _ : Fin 4 => ℝ) 0 x).prodMk
      (contDiffAt_apply ℝ (fun _ : Fin 4 => ℝ) 1 x)
  have hFc : ContDiffAt ℝ 2 (Function.uncurry F) (x 0, x 1) := hF
  have h1 : ContDiffAt ℝ 2 (fun y : Coords 4 => F (y 0) (y 1)) x :=
    ContDiffAt.comp (g := Function.uncurry F) x hFc hpair
  have h2 : ContDiffAt ℝ 2 (fun y : Coords 4 => h (y 2)) x :=
    ContDiffAt.comp (g := h) x hh (contDiffAt_apply ℝ (fun _ : Fin 4 => ℝ) 2 x)
  exact h1.mul h2

/-- Every entry of the general round shape is twice smoothly differentiable where the four
functions are. -/
theorem contDiffAt_genG {x : Coords 4} (hA : TwiceSmooth A (x 0) (x 1))
    (hB : TwiceSmooth B (x 0) (x 1)) (hC : TwiceSmooth C (x 0) (x 1))
    (hS : TwiceSmooth S (x 0) (x 1)) (i j : Fin 4) : ContDiffAt ℝ 2 (genG A B C S i j) x := by
  have hF : TwiceSmooth (gTR A B C S i j) (x 0) (x 1) := by
    unfold gTR
    split_ifs
    · exact hA.neg
    · exact hC
    · exact hB
    · exact hS
    · exact (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : ℝ × ℝ => (0 : ℝ)) (x 0, x 1))
  have hh : ContDiffAt ℝ 2 (gΘ i j) (x 2) := by
    unfold gΘ
    split_ifs
    · exact (Real.contDiff_sin.contDiffAt).pow 2
    · exact (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : ℝ => (1 : ℝ)) (x 2))
  exact contDiffAt_sep2 hF hh

/-- For the general round shape, `sizeSlopeOf` is the `sizeSlopeSq` of `GeneralCurvature.lean`. -/
theorem sizeSlopeOf_genG (A B C S : ℝ → ℝ → ℝ) (x : Coords 4) :
    sizeSlopeOf (genG A B C S) x = sizeSlopeSq A B C S (x 0) (x 1) := by
  simp [sizeSlopeOf, sizeSlopeSq, genG, slope_sep2_t, slope_sep2_r, sep2, gTR, gΘ, negA, constOne]

/-- **The assumptions can be met.** Every empty space-time of the general round shape is a round,
empty space-time in the sense of this file. -/
theorem roundEmpty_genG (h : SettingG A B C S J I) (hE : IsEmptyOnG A B C S J I) :
    RoundEmpty (genG A B C S) (genGinv A B C S) J I where
  openJ := h.openJ
  onePieceJ := h.onePieceJ
  openI := h.openI
  onePieceI := h.onePieceI
  smooth := fun _ hx i j => contDiffAt_genG (h.smoothA _ hx.1 _ hx.2.1) (h.smoothB _ hx.1 _ hx.2.1)
    (h.smoothC _ hx.1 _ hx.2.1) (h.smoothS _ hx.1 _ hx.2.1) i j
  symm := fun x _ i j => genG_symm A B C S i j x
  round := fun _ hx => genG_isRound A B C S hx.sin_ne
  spaceTime := fun x hx => by
    have hd : 0 < A (x 0) (x 1) * B (x 0) (x 1) + C (x 0) (x 1) * C (x 0) (x 1) :=
      h.spaceTime _ hx.1 _ hx.2.1
    have hs := h.S_pos _ hx.1 _ hx.2.1
    have e0 : genG A B C S 0 0 x = -A (x 0) (x 1) := by
      simp [genG, sep2, gTR, gΘ, negA, constOne]
    have e1 : genG A B C S 1 1 x = B (x 0) (x 1) := by simp [genG, sep2, gTR, gΘ, constOne]
    have e2 : genG A B C S 0 1 x = C (x 0) (x 1) := by simp [genG, sep2, gTR, gΘ, constOne]
    have e3 : genG A B C S 2 2 x = S (x 0) (x 1) := by simp [genG, sep2, gTR, gΘ, constOne]
    rw [e0, e1, e2, e3]
    exact ⟨hs, by linarith⟩
  inverse := fun _ hx i k => genG_mul_genGinv (h.spaceTime _ hx.1 _ hx.2.1).ne'
    (h.S_pos _ hx.1 _ hx.2.1).ne' hx.sin_ne i k
  empty := fun x hx => hE x hx.1 hx.2.1 hx.sin_ne

end GravityInLean
