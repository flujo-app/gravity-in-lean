/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Rim.NullEquations
public import GravityInLean.Rim.Product
public import GravityInLean.Join.NewTime

import Mathlib.Tactic

/-!
# In labels along the paths of light, an empty round shape of positive mass is Kruskal's

Board item `task:rim-null-kruskal`. Steps 10 to 12 of the route, on a whole box. The round shape
`genG zero2 zero2 F S` (time-distance part `2 F da db`) is empty and its mass function is
`m > 0` on the box. Then there are new labels `T`, `X` on the whole box in which it is Kruskal's.

On paper: `Ω = kruskalΩ m S` is smooth, `Ω · Ω_ab = Ω_a · Ω_b` and `Ω_ab ≠ 0`
(`NullEquations.lean`: `2 F = (32 m³ / r) exp (-r / 2m) Ω_ab` and `F ≠ 0`). So
`Ω(a, b) · E₀ = Ω_b(a, b₀) · Ω_a(a₀, b)` with `E₀ = Ω_ab(a₀, b₀)` (`product_form`). Put
`U(a) = -Ω_b(a, b₀) / E₀` and `V(b) = Ω_a(a₀, b)`: then `Ω = -U V` and `Ω_ab = -U' V'`. With
`T = (U + V) / 2` and `X = (V - U) / 2`: `X² - T² = -U V = kruskalF m r > -1`, so Kruskal's
radius at `(T, X)` is `r` (`kruskalR_kruskalF`); `T_a² = X_a²`, `T_b² = X_b²`, and
`X_a X_b - T_a T_b = -U' V' / 2 = Ω_ab / 2`.
-/

@[expose] public section

namespace GravityInLean

open Set

open scoped ContDiff

namespace Rim

open Curved

/-- The first of Kruskal's two labels, built from a function `Ω` of two labels along the paths of
light and a base point `(a₀, b₀)`: half of `Ω_a(a₀, b) - Ω_b(a, b₀) / Ω_ab(a₀, b₀)`. -/
noncomputable def lightT (Ω : ℝ → ℝ → ℝ) (a₀ b₀ a b : ℝ) : ℝ :=
  (dt Ω a₀ b - dr Ω a b₀ / dt (dr Ω) a₀ b₀) / 2

/-- The second of Kruskal's two labels: half of `Ω_a(a₀, b) + Ω_b(a, b₀) / Ω_ab(a₀, b₀)`. -/
noncomputable def lightX (Ω : ℝ → ℝ → ℝ) (a₀ b₀ a b : ℝ) : ℝ :=
  (dt Ω a₀ b + dr Ω a b₀ / dt (dr Ω) a₀ b₀) / 2

/-- **A product gives Kruskal's two labels.** Let `Ω` be smooth on a box, with
`Ω(a, b) · Ω_ab(a₀, b₀) = Ω_b(a, b₀) · Ω_a(a₀, b)` on the box and `Ω_ab(a₀, b₀) ≠ 0`. Then the
two labels `T = lightT Ω a₀ b₀` and `X = lightX Ω a₀ b₀` are smooth on the box, `X² - T² = Ω`,
each of them changes along `a` and along `b` at the same rate up to sign, and
`X_a X_b - T_a T_b` is half the mixed slope of `Ω`. -/
theorem light_labels {Ω : ℝ → ℝ → ℝ} {J I : Set ℝ} (hJ : IsOpen J) (hI : IsOpen I)
    (hΩ : ContDiffOn ℝ ∞ (Function.uncurry Ω) (J ×ˢ I)) {a₀ b₀ : ℝ} (ha₀ : a₀ ∈ J)
    (hb₀ : b₀ ∈ I) (hE₀ : dt (dr Ω) a₀ b₀ ≠ 0)
    (hP : ∀ a ∈ J, ∀ b ∈ I, Ω a b * dt (dr Ω) a₀ b₀ = dr Ω a b₀ * dt Ω a₀ b) :
    ContDiffOn ℝ ∞ (Function.uncurry (lightT Ω a₀ b₀)) (J ×ˢ I) ∧
      ContDiffOn ℝ ∞ (Function.uncurry (lightX Ω a₀ b₀)) (J ×ˢ I) ∧
      ∀ a ∈ J, ∀ b ∈ I,
        lightX Ω a₀ b₀ a b ^ 2 - lightT Ω a₀ b₀ a b ^ 2 = Ω a b ∧
        dt (lightT Ω a₀ b₀) a b ^ 2 - dt (lightX Ω a₀ b₀) a b ^ 2 = 0 ∧
        dr (lightX Ω a₀ b₀) a b ^ 2 - dr (lightT Ω a₀ b₀) a b ^ 2 = 0 ∧
        dt (lightX Ω a₀ b₀) a b * dr (lightX Ω a₀ b₀) a b
            - dt (lightT Ω a₀ b₀) a b * dr (lightT Ω a₀ b₀) a b
          = dt (dr Ω) a b / 2 := by
  have hJI : IsOpen (J ×ˢ I) := hJ.prod hI
  have h2 : ∀ a ∈ J, ∀ b ∈ I, TwiceSmooth Ω a b := fun a ha b hb ↦
    (hΩ.contDiffAt (hJI.mem_nhds (Set.mk_mem_prod ha hb))).of_le (by norm_num)
  -- The slope in `a` of the product identity.
  have hP1 : ∀ a ∈ J, ∀ b ∈ I,
      dt Ω a b * dt (dr Ω) a₀ b₀ = dt (dr Ω) a b₀ * dt Ω a₀ b := by
    intro a ha b hb
    have l : HasDerivAt (fun s ↦ Ω s b * dt (dr Ω) a₀ b₀) (dt Ω a b * dt (dr Ω) a₀ b₀) a :=
      (h2 a ha b hb).slopeT.mul_const _
    have r : HasDerivAt (fun s ↦ dr Ω s b₀ * dt Ω a₀ b) (dt (dr Ω) a b₀ * dt Ω a₀ b) a :=
      (h2 a ha b₀ hb₀).slopeRT.mul_const _
    have ev : (fun s ↦ Ω s b * dt (dr Ω) a₀ b₀) =ᶠ[nhds a] fun s ↦ dr Ω s b₀ * dt Ω a₀ b := by
      filter_upwards [hJ.mem_nhds ha] with s hs using hP s hs b hb
    exact l.unique (r.congr_of_eventuallyEq ev)
  -- The slope in `b` of that: the mixed slope is a product too.
  have hP2 : ∀ a ∈ J, ∀ b ∈ I,
      dt (dr Ω) a b * dt (dr Ω) a₀ b₀ = dt (dr Ω) a b₀ * dt (dr Ω) a₀ b := by
    intro a ha b hb
    have l : HasDerivAt (fun s ↦ dt Ω a s * dt (dr Ω) a₀ b₀)
        (dr (dt Ω) a b * dt (dr Ω) a₀ b₀) b := (h2 a ha b hb).slopeTR.mul_const _
    have r : HasDerivAt (fun s ↦ dt (dr Ω) a b₀ * dt Ω a₀ s)
        (dt (dr Ω) a b₀ * dr (dt Ω) a₀ b) b := (h2 a₀ ha₀ b hb).slopeTR.const_mul _
    have ev : (fun s ↦ dt Ω a s * dt (dr Ω) a₀ b₀)
        =ᶠ[nhds b] fun s ↦ dt (dr Ω) a b₀ * dt Ω a₀ s := by
      filter_upwards [hI.mem_nhds hb] with s hs using hP1 a ha s hs
    have e := l.unique (r.congr_of_eventuallyEq ev)
    rw [← (h2 a ha b hb).swap, ← (h2 a₀ ha₀ b hb).swap] at e
    exact e
  -- The two pieces of the labels are smooth on the box.
  have hV : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ ↦ dt Ω a₀ q.2) (J ×ˢ I) :=
    (Join.contDiffOn_dt hJI hΩ).comp (contDiffOn_const.prodMk contDiffOn_snd)
      (fun q hq ↦ Set.mk_mem_prod ha₀ hq.2)
  have hQ : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ ↦ dr Ω q.1 b₀) (J ×ˢ I) :=
    (Join.contDiffOn_dr hJI hΩ).comp (contDiffOn_fst.prodMk contDiffOn_const)
      (fun q hq ↦ Set.mk_mem_prod hq.1 hb₀)
  refine ⟨(hV.sub (hQ.div_const _)).div_const 2, (hV.add (hQ.div_const _)).div_const 2,
    fun a ha b hb ↦ ?_⟩
  -- The slopes of the two labels at `(a, b)`.
  have hRT : HasDerivAt (fun s ↦ dr Ω s b₀) (dt (dr Ω) a b₀) a := (h2 a ha b₀ hb₀).slopeRT
  have hTR : HasDerivAt (fun s ↦ dt Ω a₀ s) (dr (dt Ω) a₀ b) b := (h2 a₀ ha₀ b hb).slopeTR
  have eTa : dt (lightT Ω a₀ b₀) a b = -(dt (dr Ω) a b₀ / dt (dr Ω) a₀ b₀) / 2 :=
    (((hRT.div_const (dt (dr Ω) a₀ b₀)).const_sub (dt Ω a₀ b)).div_const 2).deriv
  have eXa : dt (lightX Ω a₀ b₀) a b = dt (dr Ω) a b₀ / dt (dr Ω) a₀ b₀ / 2 :=
    (((hRT.div_const (dt (dr Ω) a₀ b₀)).const_add (dt Ω a₀ b)).div_const 2).deriv
  have eTb : dr (lightT Ω a₀ b₀) a b = dt (dr Ω) a₀ b / 2 := by
    rw [(h2 a₀ ha₀ b hb).swap]
    exact ((hTR.sub_const (dr Ω a b₀ / dt (dr Ω) a₀ b₀)).div_const 2).deriv
  have eXb : dr (lightX Ω a₀ b₀) a b = dt (dr Ω) a₀ b / 2 := by
    rw [(h2 a₀ ha₀ b hb).swap]
    exact ((hTR.add_const (dr Ω a b₀ / dt (dr Ω) a₀ b₀)).div_const 2).deriv
  have eΩ : Ω a b = dr Ω a b₀ * dt Ω a₀ b / dt (dr Ω) a₀ b₀ := by
    rw [eq_div_iff hE₀]
    exact hP a ha b hb
  have eE : dt (dr Ω) a b = dt (dr Ω) a b₀ * dt (dr Ω) a₀ b / dt (dr Ω) a₀ b₀ := by
    rw [eq_div_iff hE₀]
    exact hP2 a ha b hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eΩ, lightX, lightT]
    ring
  · rw [eTa, eXa]
    ring
  · rw [eTb, eXb]
    ring
  · rw [eTa, eXa, eTb, eXb, eE]
    ring

/-- **Kruskal's labels from labels along the paths of light,** on a whole box. -/
theorem kruskal_core_null {F S : ℝ → ℝ → ℝ} {J I : Set ℝ}
    (hset : SettingG zero2 zero2 F S J I) (hE : IsEmptyOnG zero2 zero2 F S J I)
    (hF : ContDiffOn ℝ ∞ (Function.uncurry F) (J ×ˢ I))
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (J ×ˢ I)) {m : ℝ} (hm : 0 < m)
    (hmass : ∀ a ∈ J, ∀ b ∈ I, massFn zero2 zero2 F S a b = m)
    {a₀ b₀ : ℝ} (ha₀ : a₀ ∈ J) (hb₀ : b₀ ∈ I) :
    ∃ T X : ℝ → ℝ → ℝ, ContDiffOn ℝ ∞ (Function.uncurry T) (J ×ˢ I) ∧
      ContDiffOn ℝ ∞ (Function.uncurry X) (J ×ˢ I) ∧
      ∀ a ∈ J, ∀ b ∈ I, -1 < X a b ^ 2 - T a b ^ 2 ∧
        kruskalS m (T a b) (X a b) = S a b ∧
        dt T a b ^ 2 - dt X a b ^ 2 = 0 ∧
        F a b = kruskalA m (T a b) (X a b) * (dt X a b * dr X a b - dt T a b * dr T a b) ∧
        dr X a b ^ 2 - dr T a b ^ 2 = 0 := by
  have hΩ : ContDiffOn ℝ ∞ (Function.uncurry (kruskalΩ m S)) (J ×ˢ I) :=
    contDiffOn_kruskalΩ m hS hset.S_pos
  have hmixed := kruskalΩ_mixed hset hE hF hS hm hmass
  -- The factor of the table is not zero, so neither is the mixed slope of `Ω`.
  have hFne : ∀ a ∈ J, ∀ b ∈ I, F a b ≠ 0 := by
    intro a ha b hb h0
    have hp := hset.spaceTime a ha b hb
    have e : det2 zero2 zero2 F a b = F a b * F a b := by
      rw [det2, zero2]
      ring
    rw [e, h0, mul_zero] at hp
    exact lt_irrefl _ hp
  have hEne : ∀ a ∈ J, ∀ b ∈ I, dt (dr (kruskalΩ m S)) a b ≠ 0 := by
    intro a ha b hb h0
    have h := hmixed a ha b hb
    rw [h0, mul_zero] at h
    exact hFne a ha b hb (by linarith)
  -- So `Ω` is a product, and the product gives the two labels.
  have hprod := product_form hset.openJ hset.onePieceJ hset.openI hset.onePieceI hΩ
    (kruskalΩ_product hset hE hF hS hm hmass) hEne
  obtain ⟨hT, hX, hTX⟩ := light_labels hset.openJ hset.openI hΩ ha₀ hb₀ (hEne a₀ ha₀ b₀ hb₀)
    (fun a ha b hb ↦ hprod a ha b hb a₀ ha₀ b₀ hb₀)
  refine ⟨lightT (kruskalΩ m S) a₀ b₀, lightX (kruskalΩ m S) a₀ b₀, hT, hX, fun a ha b hb ↦ ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hTX a ha b hb
  have hr : 0 < √(S a b) := Real.sqrt_pos.mpr (hset.S_pos a ha b hb)
  -- `X² - T²` is Kruskal's function of the radius `√S`, so Kruskal's radius there is `√S`.
  have hu : lightX (kruskalΩ m S) a₀ b₀ a b ^ 2 - lightT (kruskalΩ m S) a₀ b₀ a b ^ 2
      = kruskalF m (√(S a b)) := h1
  have hR : kruskalR m
      (lightX (kruskalΩ m S) a₀ b₀ a b ^ 2 - lightT (kruskalΩ m S) a₀ b₀ a b ^ 2)
        = √(S a b) := by
    rw [hu]
    exact kruskalR_kruskalF hm hr
  refine ⟨?_, ?_, h2, ?_, h3⟩
  · rw [hu]
    exact neg_one_lt_kruskalF hm hr
  · rw [kruskalS, hR, Real.sq_sqrt (hset.S_pos a ha b hb).le]
  · rw [kruskalA, hR, h4]
    linear_combination (-1 / 2 : ℝ) * hmixed a ha b hb

end Rim

end GravityInLean
