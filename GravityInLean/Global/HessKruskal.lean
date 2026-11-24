/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.TableHess
public import GravityInLean.GeneralShape
public import GravityInLean.Rim.Empty

import Mathlib.Tactic

/-!
# The slope and the second slope of the radius of Kruskal's table

Board item `task:global-hess-kruskal`. The computing half of the step "the spheres are kept" in
the proof that a length-keeping map into Kruskal's is unique up to a symmetry.

The radius of Kruskal's table is the function `kruskalRad m`, `r = kruskalR m (X² - T²)` of the
four labels. Measured with Kruskal's table, for a positive mass and at every point of Kruskal's
region (the rim included):

* `gradSq_kruskalRad`: the squared length of its slope is `1 - 2m / r`;
* `hessT_kruskalRad`: its second slope (the Hessian of the textbooks) is `(m / r²) · g` on the
  plane of `T` and `X`, `((r - 2m) / r²) · g` on the sphere, and zero between the two. The two
  numbers differ except where `r = 3m`, so the second slope of the radius tells the plane of
  `T` and `X` from the sphere. The three blocks are also stated one by one:
  `hessT_kruskalRad_plane`, `hessT_kruskalRad_sphere`, `hessT_kruskalRad_mixed`.

How it is done. For a table of the general round shape with the same function `A` in front of
`-dT²` and of `dX²` and no cross term, and for a function `F` of `T` and `X` alone, the slope
length and every entry of the second slope are written out (`gradSq_conf`, `hessT_conf_tt` and
the lemmas after it), from the connection `genΓ` of `GeneralShape.lean`. For Kruskal's table
all slopes are known in closed form (`Rim/Empty.lean`); the radius has the slope
`A / 8m` along `u = X² - T²`. Three identities in `u` then finish (`kruskalAu_add_mul`,
`kruskalAu_mul`, `kruskalSu1_mul`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set Filter Topology

/-! ## The four labels: which is below two, which is not -/

/-- A label of the plane of `T` and `X` is the label `0` or the label `1`. -/
theorem fin4_lt_two : ∀ a : Fin 4, a.val < 2 → a = 0 ∨ a = 1 := by decide

/-- A label of the sphere is the label `2` or the label `3`. -/
theorem fin4_ge_two : ∀ a : Fin 4, 2 ≤ a.val → a = 2 ∨ a = 3 := by decide

/-! ## The general round table, entry by entry -/

section Entries

variable (A B C S : ℝ → ℝ → ℝ) (x : Coords 4)

/-- The entry "time, time" of the general round table is `-A`. -/
theorem genG_tt : genG A B C S 0 0 x = -A (x 0) (x 1) := by
  simp [genG, sep2, gTR, gΘ, negA, constOne]

/-- The entry "distance, distance" of the general round table is `B`. -/
theorem genG_xx : genG A B C S 1 1 x = B (x 0) (x 1) := by
  simp [genG, sep2, gTR, gΘ, constOne]

/-- The entry "pole angle, pole angle" of the general round table is `S`. -/
theorem genG_θθ : genG A B C S 2 2 x = S (x 0) (x 1) := by
  simp [genG, sep2, gTR, gΘ, constOne]

/-- The entry "angle around the axis, twice" of the general round table is `S sin² θ`. -/
theorem genG_φφ : genG A B C S 3 3 x = S (x 0) (x 1) * sin (x 2) ^ 2 := by
  simp [genG, sep2, gTR, gΘ, sin2]

/-- Without a cross term, the general round table has no entry off the diagonal. -/
theorem genG_off : ∀ a b : Fin 4, a ≠ b → genG A B zero2 S a b x = 0 := by
  intro a b
  fin_cases a <;> fin_cases b <;> simp [genG, sep2, gTR, gΘ, zero2]

end Entries

/-! ## Functions of `T` and `X` alone: their slopes -/

section Slopes

variable (F : ℝ → ℝ → ℝ) (x : Coords 4)

/-- The slope along `T` of a function of `T` and `X` alone is again such a function. -/
theorem slope_t_sep2_one : slope 0 (sep2 F constOne) = sep2 (dt F) constOne :=
  funext fun y ↦ slope_sep2_t F constOne y

/-- The slope along `X` of a function of `T` and `X` alone is again such a function. -/
theorem slope_r_sep2_one : slope 1 (sep2 F constOne) = sep2 (dr F) constOne :=
  funext fun y ↦ slope_sep2_r F constOne y

/-- A function of `T` and `X` alone has no slope along the pole angle. -/
theorem slope_θ_sep2_one : slope 2 (sep2 F constOne) = fun _ ↦ 0 := by
  funext y
  rw [slope_sep2_θ, deriv_constOne, mul_zero]

/-- A function of `T` and `X` alone has no slope around the axis. -/
theorem slope_φ_sep2_one : slope 3 (sep2 F constOne) = fun _ ↦ 0 :=
  funext fun y ↦ slope_sep2_φ F constOne y

/-- The slope along `T`, at a point. -/
theorem slope_t_sep2_one_apply : slope 0 (sep2 F constOne) x = dt F (x 0) (x 1) :=
  (slope_sep2_t F constOne x).trans (mul_one _)

/-- The slope along `X`, at a point. -/
theorem slope_r_sep2_one_apply : slope 1 (sep2 F constOne) x = dr F (x 0) (x 1) :=
  (slope_sep2_r F constOne x).trans (mul_one _)

/-- The second slope, twice along `T`. -/
theorem slope_tt_sep2_one :
    slope 0 (slope 0 (sep2 F constOne)) x = dt (dt F) (x 0) (x 1) := by
  rw [slope_t_sep2_one]
  exact slope_t_sep2_one_apply (dt F) x

/-- The second slope, first along `X`, then along `T`. -/
theorem slope_tx_sep2_one :
    slope 0 (slope 1 (sep2 F constOne)) x = dt (dr F) (x 0) (x 1) := by
  rw [slope_r_sep2_one]
  exact slope_t_sep2_one_apply (dr F) x

/-- The second slope, first along `T`, then along `X`. -/
theorem slope_xt_sep2_one :
    slope 1 (slope 0 (sep2 F constOne)) x = dr (dt F) (x 0) (x 1) := by
  rw [slope_t_sep2_one]
  exact slope_r_sep2_one_apply (dt F) x

/-- The second slope, twice along `X`. -/
theorem slope_xx_sep2_one :
    slope 1 (slope 1 (sep2 F constOne)) x = dr (dr F) (x 0) (x 1) := by
  rw [slope_r_sep2_one]
  exact slope_r_sep2_one_apply (dr F) x

/-- A second slope of a function of `T` and `X` alone vanishes as soon as one of the two
directions is an angle. -/
theorem slope_slope_sep2_one_angle (a b : Fin 4) (h : 2 ≤ a.val ∨ 2 ≤ b.val) :
    slope a (slope b (sep2 F constOne)) x = 0 := by
  by_cases hb : 2 ≤ b.val
  · rcases fin4_ge_two b hb with rfl | rfl
    · rw [slope_θ_sep2_one]
      exact slope_const a 0 x
    · rw [slope_φ_sep2_one]
      exact slope_const a 0 x
  · have hb' := fin4_lt_two b (by omega)
    have ha' := fin4_ge_two a (by omega)
    rcases hb' with rfl | rfl <;> rcases ha' with rfl | rfl
    · rw [slope_t_sep2_one, slope_sep2_θ, deriv_constOne, mul_zero]
    · rw [slope_t_sep2_one]
      exact slope_sep2_φ _ _ x
    · rw [slope_r_sep2_one, slope_sep2_θ, deriv_constOne, mul_zero]
    · rw [slope_r_sep2_one]
      exact slope_sep2_φ _ _ x

end Slopes

/-! ## The slope length and the second slope, for a table with one factor `A` and no cross term -/

section Conf

variable (A B C S F : ℝ → ℝ → ℝ) (x : Coords 4)

/-- **The second slope of a function of `T` and `X` alone, for the general round table:** the
plain second slope, less the two entries of the connection that point along `T` and along `X`,
each times the slope of the function in that direction. -/
theorem hessT_gen_sep2 (a b : Fin 4) :
    hessT (genG A B C S) (genGinv A B C S) (sep2 F constOne) a b x
      = slope a (slope b (sep2 F constOne)) x
        - (genΓ A B C S 0 a b x * dt F (x 0) (x 1) + genΓ A B C S 1 a b x * dr F (x 0) (x 1)) := by
  have h0 := slope_t_sep2_one_apply F x
  have h1 := slope_r_sep2_one_apply F x
  have h2 : slope 2 (sep2 F constOne) x = 0 := congrFun (slope_θ_sep2_one F) x
  have h3 : slope 3 (sep2 F constOne) x = 0 := congrFun (slope_φ_sep2_one F) x
  simp only [hessT, Fin.sum_univ_four, christoffel_gen, h0, h1, h2, h3]
  ring

/-- **The squared length of the slope** of a function `F` of `T` and `X` alone, for a table with
the same factor `A` in front of `-dT²` and of `dX²` and no cross term:
`(-(∂_T F)² + (∂_X F)²) / A`. -/
theorem gradSq_conf :
    gradSq (genGinv A A zero2 S) (sep2 F constOne) x
      = -A (x 0) (x 1) / (A (x 0) (x 1) * A (x 0) (x 1)) * dt F (x 0) (x 1) * dt F (x 0) (x 1)
        + A (x 0) (x 1) / (A (x 0) (x 1) * A (x 0) (x 1)) * dr F (x 0) (x 1)
          * dr F (x 0) (x 1) := by
  have h0 := slope_t_sep2_one_apply F x
  have h1 := slope_r_sep2_one_apply F x
  have h2 : slope 2 (sep2 F constOne) x = 0 := congrFun (slope_θ_sep2_one F) x
  have h3 : slope 3 (sep2 F constOne) x = 0 := congrFun (slope_φ_sep2_one F) x
  have g00 : genGinv A A zero2 S 0 0 x = -A (x 0) (x 1) / (A (x 0) (x 1) * A (x 0) (x 1)) := by
    simp [genGinv, ginvTR, ginvΘ, det2, zero2, constOne]
  have g01 : genGinv A A zero2 S 0 1 x = 0 := by
    simp [genGinv, ginvTR, ginvΘ, zero2, constOne]
  have g10 : genGinv A A zero2 S 1 0 x = 0 := by
    simp [genGinv, ginvTR, ginvΘ, zero2, constOne]
  have g11 : genGinv A A zero2 S 1 1 x = A (x 0) (x 1) / (A (x 0) (x 1) * A (x 0) (x 1)) := by
    simp [genGinv, ginvTR, ginvΘ, det2, zero2, constOne]
  simp only [gradSq, Fin.sum_univ_four, h0, h1, h2, h3, g00, g01, g10, g11]
  ring

/-- The second slope, entry "`T`, `T`". -/
theorem hessT_conf_tt :
    hessT (genG A A zero2 S) (genGinv A A zero2 S) (sep2 F constOne) 0 0 x
      = dt (dt F) (x 0) (x 1)
        - (A (x 0) (x 1) * dt A (x 0) (x 1) / (2 * (A (x 0) (x 1) * A (x 0) (x 1)))
            * dt F (x 0) (x 1)
          + A (x 0) (x 1) * dr A (x 0) (x 1) / (2 * (A (x 0) (x 1) * A (x 0) (x 1)))
            * dr F (x 0) (x 1)) := by
  have e0 : genΓ A A zero2 S 0 0 0 x
      = A (x 0) (x 1) * dt A (x 0) (x 1) / (2 * (A (x 0) (x 1) * A (x 0) (x 1))) := by
    simp [genΓ_apply, trPartG, θPartG, half, n000, det2, zero2, constOne, dt_zero2, dr_zero2]
  have e1 : genΓ A A zero2 S 1 0 0 x
      = A (x 0) (x 1) * dr A (x 0) (x 1) / (2 * (A (x 0) (x 1) * A (x 0) (x 1))) := by
    simp [genΓ_apply, trPartG, θPartG, half, n100, det2, zero2, constOne, dt_zero2, dr_zero2]
  rw [hessT_gen_sep2, slope_tt_sep2_one, e0, e1]

/-- The second slope, entry "`T`, `X`". -/
theorem hessT_conf_tx :
    hessT (genG A A zero2 S) (genGinv A A zero2 S) (sep2 F constOne) 0 1 x
      = dt (dr F) (x 0) (x 1)
        - (A (x 0) (x 1) * dr A (x 0) (x 1) / (2 * (A (x 0) (x 1) * A (x 0) (x 1)))
            * dt F (x 0) (x 1)
          + A (x 0) (x 1) * dt A (x 0) (x 1) / (2 * (A (x 0) (x 1) * A (x 0) (x 1)))
            * dr F (x 0) (x 1)) := by
  have e0 : genΓ A A zero2 S 0 0 1 x
      = A (x 0) (x 1) * dr A (x 0) (x 1) / (2 * (A (x 0) (x 1) * A (x 0) (x 1))) := by
    simp [genΓ_apply, trPartG, θPartG, half, n001, det2, zero2, constOne, dt_zero2, dr_zero2]
  have e1 : genΓ A A zero2 S 1 0 1 x
      = A (x 0) (x 1) * dt A (x 0) (x 1) / (2 * (A (x 0) (x 1) * A (x 0) (x 1))) := by
    simp [genΓ_apply, trPartG, θPartG, half, n101, det2, zero2, constOne, dt_zero2, dr_zero2]
  rw [hessT_gen_sep2, slope_tx_sep2_one, e0, e1]

/-- The second slope, entry "`X`, `T`". -/
theorem hessT_conf_xt :
    hessT (genG A A zero2 S) (genGinv A A zero2 S) (sep2 F constOne) 1 0 x
      = dr (dt F) (x 0) (x 1)
        - (A (x 0) (x 1) * dr A (x 0) (x 1) / (2 * (A (x 0) (x 1) * A (x 0) (x 1)))
            * dt F (x 0) (x 1)
          + A (x 0) (x 1) * dt A (x 0) (x 1) / (2 * (A (x 0) (x 1) * A (x 0) (x 1)))
            * dr F (x 0) (x 1)) := by
  have e0 : genΓ A A zero2 S 0 1 0 x
      = A (x 0) (x 1) * dr A (x 0) (x 1) / (2 * (A (x 0) (x 1) * A (x 0) (x 1))) := by
    simp [genΓ_apply, trPartG, θPartG, half, n001, det2, zero2, constOne, dt_zero2, dr_zero2]
  have e1 : genΓ A A zero2 S 1 1 0 x
      = A (x 0) (x 1) * dt A (x 0) (x 1) / (2 * (A (x 0) (x 1) * A (x 0) (x 1))) := by
    simp [genΓ_apply, trPartG, θPartG, half, n101, det2, zero2, constOne, dt_zero2, dr_zero2]
  rw [hessT_gen_sep2, slope_xt_sep2_one, e0, e1]

/-- The second slope, entry "`X`, `X`". -/
theorem hessT_conf_xx :
    hessT (genG A A zero2 S) (genGinv A A zero2 S) (sep2 F constOne) 1 1 x
      = dr (dr F) (x 0) (x 1)
        - (A (x 0) (x 1) * dt A (x 0) (x 1) / (2 * (A (x 0) (x 1) * A (x 0) (x 1)))
            * dt F (x 0) (x 1)
          + A (x 0) (x 1) * dr A (x 0) (x 1) / (2 * (A (x 0) (x 1) * A (x 0) (x 1)))
            * dr F (x 0) (x 1)) := by
  have e0 : genΓ A A zero2 S 0 1 1 x
      = A (x 0) (x 1) * dt A (x 0) (x 1) / (2 * (A (x 0) (x 1) * A (x 0) (x 1))) := by
    simp [genΓ_apply, trPartG, θPartG, half, n011, det2, zero2, constOne, dt_zero2, dr_zero2]
  have e1 : genΓ A A zero2 S 1 1 1 x
      = A (x 0) (x 1) * dr A (x 0) (x 1) / (2 * (A (x 0) (x 1) * A (x 0) (x 1))) := by
    simp [genΓ_apply, trPartG, θPartG, half, n111, det2, zero2, constOne, dt_zero2, dr_zero2]
  rw [hessT_gen_sep2, slope_xx_sep2_one, e0, e1]

/-- The second slope, entry "pole angle, pole angle". -/
theorem hessT_conf_θθ :
    hessT (genG A A zero2 S) (genGinv A A zero2 S) (sep2 F constOne) 2 2 x
      = -(A (x 0) (x 1) * dt S (x 0) (x 1) / (2 * (A (x 0) (x 1) * A (x 0) (x 1)))
            * dt F (x 0) (x 1)
          + -(A (x 0) (x 1) * dr S (x 0) (x 1)) / (2 * (A (x 0) (x 1) * A (x 0) (x 1)))
            * dr F (x 0) (x 1)) := by
  have e0 : genΓ A A zero2 S 0 2 2 x
      = A (x 0) (x 1) * dt S (x 0) (x 1) / (2 * (A (x 0) (x 1) * A (x 0) (x 1))) := by
    simp [genΓ_apply, trPartG, θPartG, half, m0, det2, zero2, constOne]
  have e1 : genΓ A A zero2 S 1 2 2 x
      = -(A (x 0) (x 1) * dr S (x 0) (x 1)) / (2 * (A (x 0) (x 1) * A (x 0) (x 1))) := by
    simp [genΓ_apply, trPartG, θPartG, half, m1, det2, zero2, constOne]
  rw [hessT_gen_sep2, slope_slope_sep2_one_angle F x 2 2 (Or.inl (by decide)), e0, e1, zero_sub]

/-- The second slope, entry "angle around the axis, twice". -/
theorem hessT_conf_φφ :
    hessT (genG A A zero2 S) (genGinv A A zero2 S) (sep2 F constOne) 3 3 x
      = -(A (x 0) (x 1) * dt S (x 0) (x 1) / (2 * (A (x 0) (x 1) * A (x 0) (x 1)))
            * sin (x 2) ^ 2 * dt F (x 0) (x 1)
          + -(A (x 0) (x 1) * dr S (x 0) (x 1)) / (2 * (A (x 0) (x 1) * A (x 0) (x 1)))
            * sin (x 2) ^ 2 * dr F (x 0) (x 1)) := by
  have e0 : genΓ A A zero2 S 0 3 3 x
      = A (x 0) (x 1) * dt S (x 0) (x 1) / (2 * (A (x 0) (x 1) * A (x 0) (x 1)))
        * sin (x 2) ^ 2 := by
    simp [genΓ_apply, trPartG, θPartG, half, m0, det2, zero2, sin2]
  have e1 : genΓ A A zero2 S 1 3 3 x
      = -(A (x 0) (x 1) * dr S (x 0) (x 1)) / (2 * (A (x 0) (x 1) * A (x 0) (x 1)))
        * sin (x 2) ^ 2 := by
    simp [genΓ_apply, trPartG, θPartG, half, m1, det2, zero2, sin2]
  rw [hessT_gen_sep2, slope_slope_sep2_one_angle F x 3 3 (Or.inl (by decide)), e0, e1, zero_sub]

/-- The second slope has no entry between two different directions of which one is an angle. -/
theorem hessT_conf_zero (a b : Fin 4) (hab : a ≠ b) (h : 2 ≤ a.val ∨ 2 ≤ b.val) :
    hessT (genG A A zero2 S) (genGinv A A zero2 S) (sep2 F constOne) a b x = 0 := by
  have hΓ : ∀ c a b : Fin 4, c.val < 2 → a ≠ b → (2 ≤ a.val ∨ 2 ≤ b.val) →
      trPartG A A zero2 S c a b = zero2 := by
    intro c a b
    fin_cases c <;> fin_cases a <;> fin_cases b <;> simp [trPartG]
  rw [hessT_gen_sep2, slope_slope_sep2_one_angle F x a b h, genΓ_apply, genΓ_apply,
    hΓ 0 a b (by decide) hab h, hΓ 1 a b (by decide) hab h]
  simp [zero2]

end Conf

/-! ## One more mixed slope of a function of `X² - T²` -/

/-- The mixed second slope of `f (X² - T²)`: first in `X`, then in `T`. -/
theorem dt_dr_sqDiff {f f1 f2 : ℝ → ℝ} {T X : ℝ} (h1 : ∀ u, -1 < u → HasDerivAt f (f1 u) u)
    (h2 : ∀ u, -1 < u → HasDerivAt f1 (f2 u) u) (h : -1 < X ^ 2 - T ^ 2) :
    dt (dr (sqDiff f)) T X = -4 * T * X * f2 (X ^ 2 - T ^ 2) := by
  have hev : (fun s => dr (sqDiff f) s X) =ᶠ[𝓝 T] fun s => 2 * X * f1 (X ^ 2 - s ^ 2) := by
    filter_upwards [eventually_sqDiff_T h] with s hs
    exact dr_sqDiff h1 hs
  have hd : HasDerivAt (fun s : ℝ => 2 * X * f1 (X ^ 2 - s ^ 2))
      (-4 * T * X * f2 (X ^ 2 - T ^ 2)) T :=
    ((hasDerivAt_sqDiff_T (h2 _ h)).const_mul (2 * X)).congr_deriv (by ring)
  exact hev.deriv_eq.trans hd.deriv

/-! ## Kruskal's radius and its slopes -/

/-- **The radius of Kruskal's table,** as a function of the four labels:
`r = kruskalR m (X² - T²)`. -/
noncomputable def kruskalRad (m : ℝ) (x : Coords 4) : ℝ := kruskalR m (x 1 ^ 2 - x 0 ^ 2)

/-- The slope of the radius in `u = X² - T²`: Kruskal's factor over `8m`. -/
noncomputable def kruskalRu1 (m u : ℝ) : ℝ := kruskalAu m u / (8 * m)

/-- The second slope of the radius in `u = X² - T²`. -/
noncomputable def kruskalRu2 (m u : ℝ) : ℝ := kruskalAu1 m u / (8 * m)

/-- The radius is a function of `T` and `X` alone. -/
theorem kruskalRad_eq (m : ℝ) : kruskalRad m = sep2 (sqDiff (kruskalR m)) constOne := by
  funext x
  simp [kruskalRad, sep2, sqDiff, constOne]

section KruskalFacts

variable {m u : ℝ}

/-- The slope of the radius in `u` is Kruskal's factor over `8m`. -/
theorem hasDerivAt_kruskalRu (hm : 0 < m) (hu : -1 < u) :
    HasDerivAt (kruskalR m) (kruskalRu1 m u) u := by
  have hr : kruskalR m u ≠ 0 := (kruskalR_pos hm hu).ne'
  have hm' : m ≠ 0 := hm.ne'
  refine (hasDerivAt_kruskalR_w hm hu).congr_deriv ?_
  rw [kruskalRu1, kruskalAu]
  field_simp
  ring

/-- The second slope of the radius in `u`. -/
theorem hasDerivAt_kruskalRu1 (hm : 0 < m) (hu : -1 < u) :
    HasDerivAt (kruskalRu1 m) (kruskalRu2 m u) u :=
  (hasDerivAt_kruskalAu hm hu).div_const (8 * m)

/-- The equation that ties the radius to `u = X² - T²`, written with `w = exp (-r / 2m)`. -/
theorem kruskalW_rel (hm : 0 < m) (hu : -1 < u) :
    u = (kruskalR m u / (2 * m) - 1) * (kruskalW m u)⁻¹ := by
  have hF : kruskalF m (kruskalR m u) = u := kruskalF_kruskalR hm hu
  rw [kruskalF, exp_eq_inv_kruskalW] at hF
  exact hF.symm

/-- Kruskal's factor `A` and its slope along `u`: `A + u A' = (4m² / r²) A`. -/
theorem kruskalAu_add_mul (hm : 0 < m) (hu : -1 < u) :
    kruskalAu m u + u * kruskalAu1 m u = 4 * m ^ 2 / kruskalR m u ^ 2 * kruskalAu m u := by
  have hm' : m ≠ 0 := hm.ne'
  have hr : kruskalR m u ≠ 0 := (kruskalR_pos hm hu).ne'
  have hw : kruskalW m u ≠ 0 := (kruskalW_pos m u).ne'
  have hrel := kruskalW_rel hm hu
  simp only [kruskalAu, kruskalAu1]
  generalize kruskalW m u = w at hw hrel ⊢
  generalize kruskalR m u = r at hr hrel ⊢
  rw [hrel]
  field_simp
  ring

/-- Kruskal's factor times `u`: `u A = 16 m² (1 - 2m / r)`. -/
theorem kruskalAu_mul (hm : 0 < m) (hu : -1 < u) :
    u * kruskalAu m u = 16 * m ^ 2 * (1 - 2 * m / kruskalR m u) := by
  have hm' : m ≠ 0 := hm.ne'
  have hr : kruskalR m u ≠ 0 := (kruskalR_pos hm hu).ne'
  have hw : kruskalW m u ≠ 0 := (kruskalW_pos m u).ne'
  have hrel := kruskalW_rel hm hu
  simp only [kruskalAu]
  generalize kruskalW m u = w at hw hrel ⊢
  generalize kruskalR m u = r at hr hrel ⊢
  rw [hrel]
  field_simp
  ring

/-- The slope of the size of the spheres times `u`: `u S' = 4m (r - 2m)`. -/
theorem kruskalSu1_mul (hm : 0 < m) (hu : -1 < u) :
    u * kruskalSu1 m u = 4 * m * (kruskalR m u - 2 * m) := by
  have hm' : m ≠ 0 := hm.ne'
  have hw : kruskalW m u ≠ 0 := (kruskalW_pos m u).ne'
  have hrel := kruskalW_rel hm hu
  simp only [kruskalSu1]
  generalize kruskalW m u = w at hw hrel ⊢
  generalize kruskalR m u = r at hrel ⊢
  rw [hrel]
  field_simp
  ring

end KruskalFacts

section KruskalSlopes

variable {m T X : ℝ}

/-- The slope of the radius along `T`. -/
theorem kruskal_dtR (hm : 0 < m) (h : -1 < X ^ 2 - T ^ 2) :
    dt (sqDiff (kruskalR m)) T X = -2 * T * kruskalRu1 m (X ^ 2 - T ^ 2) :=
  dt_sqDiff (fun _ hu ↦ hasDerivAt_kruskalRu hm hu) h

/-- The slope of the radius along `X`. -/
theorem kruskal_drR (hm : 0 < m) (h : -1 < X ^ 2 - T ^ 2) :
    dr (sqDiff (kruskalR m)) T X = 2 * X * kruskalRu1 m (X ^ 2 - T ^ 2) :=
  dr_sqDiff (fun _ hu ↦ hasDerivAt_kruskalRu hm hu) h

/-- The second slope of the radius, twice along `T`. -/
theorem kruskal_dtdtR (hm : 0 < m) (h : -1 < X ^ 2 - T ^ 2) :
    dt (dt (sqDiff (kruskalR m))) T X
      = -2 * kruskalRu1 m (X ^ 2 - T ^ 2) + 4 * T ^ 2 * kruskalRu2 m (X ^ 2 - T ^ 2) :=
  dt_dt_sqDiff (fun _ hu ↦ hasDerivAt_kruskalRu hm hu)
    (fun _ hu ↦ hasDerivAt_kruskalRu1 hm hu) h

/-- The second slope of the radius, first along `T`, then along `X`. -/
theorem kruskal_drdtR (hm : 0 < m) (h : -1 < X ^ 2 - T ^ 2) :
    dr (dt (sqDiff (kruskalR m))) T X = -4 * T * X * kruskalRu2 m (X ^ 2 - T ^ 2) :=
  dr_dt_sqDiff (fun _ hu ↦ hasDerivAt_kruskalRu hm hu)
    (fun _ hu ↦ hasDerivAt_kruskalRu1 hm hu) h

/-- The second slope of the radius, first along `X`, then along `T`. -/
theorem kruskal_dtdrR (hm : 0 < m) (h : -1 < X ^ 2 - T ^ 2) :
    dt (dr (sqDiff (kruskalR m))) T X = -4 * T * X * kruskalRu2 m (X ^ 2 - T ^ 2) :=
  dt_dr_sqDiff (fun _ hu ↦ hasDerivAt_kruskalRu hm hu)
    (fun _ hu ↦ hasDerivAt_kruskalRu1 hm hu) h

/-- The second slope of the radius, twice along `X`. -/
theorem kruskal_drdrR (hm : 0 < m) (h : -1 < X ^ 2 - T ^ 2) :
    dr (dr (sqDiff (kruskalR m))) T X
      = 2 * kruskalRu1 m (X ^ 2 - T ^ 2) + 4 * X ^ 2 * kruskalRu2 m (X ^ 2 - T ^ 2) :=
  dr_dr_sqDiff (fun _ hu ↦ hasDerivAt_kruskalRu hm hu)
    (fun _ hu ↦ hasDerivAt_kruskalRu1 hm hu) h

/-- The slope of Kruskal's factor along `T`. -/
theorem kruskal_dtA (hm : 0 < m) (h : -1 < X ^ 2 - T ^ 2) :
    dt (kruskalA m) T X = -2 * T * kruskalAu1 m (X ^ 2 - T ^ 2) :=
  dt_sqDiff (f := kruskalAu m) (fun _ hu ↦ hasDerivAt_kruskalAu hm hu) h

/-- The slope of Kruskal's factor along `X`. -/
theorem kruskal_drA (hm : 0 < m) (h : -1 < X ^ 2 - T ^ 2) :
    dr (kruskalA m) T X = 2 * X * kruskalAu1 m (X ^ 2 - T ^ 2) :=
  dr_sqDiff (f := kruskalAu m) (fun _ hu ↦ hasDerivAt_kruskalAu hm hu) h

/-- The slope of the size of the spheres along `T`. -/
theorem kruskal_dtS (hm : 0 < m) (h : -1 < X ^ 2 - T ^ 2) :
    dt (kruskalS m) T X = -2 * T * kruskalSu1 m (X ^ 2 - T ^ 2) :=
  dt_sqDiff (f := kruskalSu m) (fun _ hu ↦ hasDerivAt_kruskalSu hm hu) h

/-- The slope of the size of the spheres along `X`. -/
theorem kruskal_drS (hm : 0 < m) (h : -1 < X ^ 2 - T ^ 2) :
    dr (kruskalS m) T X = 2 * X * kruskalSu1 m (X ^ 2 - T ^ 2) :=
  dr_sqDiff (f := kruskalSu m) (fun _ hu ↦ hasDerivAt_kruskalSu hm hu) h

end KruskalSlopes

/-! ## The slope length and the second slope of Kruskal's radius -/

section KruskalHess

variable {m : ℝ} {x : Coords 4}

/-- **The squared length of the slope of Kruskal's radius is `1 - 2m / r`,** at every point of
Kruskal's region, the rim included (where it is zero). -/
theorem gradSq_kruskalRad (hm : 0 < m) (hx : x ∈ kruskalRegion) :
    gradSq (genGinv (kruskalA m) (kruskalA m) zero2 (kruskalS m)) (kruskalRad m) x
      = 1 - 2 * m / kruskalRad m x := by
  have h : -1 < x 1 ^ 2 - x 0 ^ 2 := hx.1
  have hm' : m ≠ 0 := hm.ne'
  have hr : kruskalR m (x 1 ^ 2 - x 0 ^ 2) ≠ 0 := (kruskalR_pos hm h).ne'
  have ha : kruskalAu m (x 1 ^ 2 - x 0 ^ 2) ≠ 0 := (kruskalA_pos hm h).ne'
  have key := kruskalAu_mul hm h
  have hrad : kruskalRad m x = kruskalR m (x 1 ^ 2 - x 0 ^ 2) := rfl
  rw [hrad, kruskalRad_eq, gradSq_conf, kruskal_dtR hm h, kruskal_drR hm h,
    show kruskalA m (x 0) (x 1) = kruskalAu m (x 1 ^ 2 - x 0 ^ 2) from rfl]
  unfold kruskalRu1
  generalize kruskalAu m (x 1 ^ 2 - x 0 ^ 2) = a at ha key ⊢
  refine Eq.trans (b := (x 1 ^ 2 - x 0 ^ 2) * a / (16 * m ^ 2)) ?_ ?_
  · field_simp
    ring
  · rw [key]
    field_simp

/-- The second slope of Kruskal's radius, entry "`T`, `T`": `(m / r²) · g`. -/
theorem hessT_kruskalRad_tt (hm : 0 < m) (hx : x ∈ kruskalRegion) :
    hessT (kruskalG m) (genGinv (kruskalA m) (kruskalA m) zero2 (kruskalS m)) (kruskalRad m)
        0 0 x = m / kruskalRad m x ^ 2 * kruskalG m 0 0 x := by
  have h : -1 < x 1 ^ 2 - x 0 ^ 2 := hx.1
  have hm' : m ≠ 0 := hm.ne'
  have hr : kruskalR m (x 1 ^ 2 - x 0 ^ 2) ≠ 0 := (kruskalR_pos hm h).ne'
  have ha : kruskalAu m (x 1 ^ 2 - x 0 ^ 2) ≠ 0 := (kruskalA_pos hm h).ne'
  have key := kruskalAu_add_mul hm h
  have hK : kruskalG m 0 0 x = -kruskalAu m (x 1 ^ 2 - x 0 ^ 2) :=
    genG_tt (kruskalA m) (kruskalA m) zero2 (kruskalS m) x
  have hrad : kruskalRad m x = kruskalR m (x 1 ^ 2 - x 0 ^ 2) := rfl
  rw [hK, hrad, kruskalRad_eq,
    show kruskalG m = genG (kruskalA m) (kruskalA m) zero2 (kruskalS m) from rfl,
    hessT_conf_tt, kruskal_dtdtR hm h, kruskal_dtR hm h, kruskal_drR hm h, kruskal_dtA hm h,
    kruskal_drA hm h, show kruskalA m (x 0) (x 1) = kruskalAu m (x 1 ^ 2 - x 0 ^ 2) from rfl]
  unfold kruskalRu1 kruskalRu2
  generalize kruskalAu m (x 1 ^ 2 - x 0 ^ 2) = a at ha key ⊢
  generalize kruskalAu1 m (x 1 ^ 2 - x 0 ^ 2) = a1 at key ⊢
  refine Eq.trans (b := -(a + (x 1 ^ 2 - x 0 ^ 2) * a1) / (4 * m)) ?_ ?_
  · field_simp
    ring
  · rw [key]
    field_simp

/-- The second slope of Kruskal's radius, entry "`X`, `X`": `(m / r²) · g`. -/
theorem hessT_kruskalRad_xx (hm : 0 < m) (hx : x ∈ kruskalRegion) :
    hessT (kruskalG m) (genGinv (kruskalA m) (kruskalA m) zero2 (kruskalS m)) (kruskalRad m)
        1 1 x = m / kruskalRad m x ^ 2 * kruskalG m 1 1 x := by
  have h : -1 < x 1 ^ 2 - x 0 ^ 2 := hx.1
  have hm' : m ≠ 0 := hm.ne'
  have hr : kruskalR m (x 1 ^ 2 - x 0 ^ 2) ≠ 0 := (kruskalR_pos hm h).ne'
  have ha : kruskalAu m (x 1 ^ 2 - x 0 ^ 2) ≠ 0 := (kruskalA_pos hm h).ne'
  have key := kruskalAu_add_mul hm h
  have hK : kruskalG m 1 1 x = kruskalAu m (x 1 ^ 2 - x 0 ^ 2) :=
    genG_xx (kruskalA m) (kruskalA m) zero2 (kruskalS m) x
  have hrad : kruskalRad m x = kruskalR m (x 1 ^ 2 - x 0 ^ 2) := rfl
  rw [hK, hrad, kruskalRad_eq,
    show kruskalG m = genG (kruskalA m) (kruskalA m) zero2 (kruskalS m) from rfl,
    hessT_conf_xx, kruskal_drdrR hm h, kruskal_dtR hm h, kruskal_drR hm h, kruskal_dtA hm h,
    kruskal_drA hm h, show kruskalA m (x 0) (x 1) = kruskalAu m (x 1 ^ 2 - x 0 ^ 2) from rfl]
  unfold kruskalRu1 kruskalRu2
  generalize kruskalAu m (x 1 ^ 2 - x 0 ^ 2) = a at ha key ⊢
  generalize kruskalAu1 m (x 1 ^ 2 - x 0 ^ 2) = a1 at key ⊢
  refine Eq.trans (b := (a + (x 1 ^ 2 - x 0 ^ 2) * a1) / (4 * m)) ?_ ?_
  · field_simp
    ring
  · rw [key]
    field_simp

/-- The second slope of Kruskal's radius, entry "`T`, `X`": zero, as `g` there. -/
theorem hessT_kruskalRad_tx (hm : 0 < m) (hx : x ∈ kruskalRegion) :
    hessT (kruskalG m) (genGinv (kruskalA m) (kruskalA m) zero2 (kruskalS m)) (kruskalRad m)
        0 1 x = m / kruskalRad m x ^ 2 * kruskalG m 0 1 x := by
  have h : -1 < x 1 ^ 2 - x 0 ^ 2 := hx.1
  have hm' : m ≠ 0 := hm.ne'
  have ha : kruskalAu m (x 1 ^ 2 - x 0 ^ 2) ≠ 0 := (kruskalA_pos hm h).ne'
  have hK : kruskalG m 0 1 x = 0 :=
    genG_off (kruskalA m) (kruskalA m) (kruskalS m) x 0 1 (by decide)
  rw [hK, mul_zero, kruskalRad_eq,
    show kruskalG m = genG (kruskalA m) (kruskalA m) zero2 (kruskalS m) from rfl,
    hessT_conf_tx, kruskal_dtdrR hm h, kruskal_dtR hm h, kruskal_drR hm h, kruskal_dtA hm h,
    kruskal_drA hm h, show kruskalA m (x 0) (x 1) = kruskalAu m (x 1 ^ 2 - x 0 ^ 2) from rfl]
  unfold kruskalRu1 kruskalRu2
  generalize kruskalAu m (x 1 ^ 2 - x 0 ^ 2) = a at ha ⊢
  field_simp
  ring

/-- The second slope of Kruskal's radius, entry "`X`, `T`": zero, as `g` there. -/
theorem hessT_kruskalRad_xt (hm : 0 < m) (hx : x ∈ kruskalRegion) :
    hessT (kruskalG m) (genGinv (kruskalA m) (kruskalA m) zero2 (kruskalS m)) (kruskalRad m)
        1 0 x = m / kruskalRad m x ^ 2 * kruskalG m 1 0 x := by
  have h : -1 < x 1 ^ 2 - x 0 ^ 2 := hx.1
  have hm' : m ≠ 0 := hm.ne'
  have ha : kruskalAu m (x 1 ^ 2 - x 0 ^ 2) ≠ 0 := (kruskalA_pos hm h).ne'
  have hK : kruskalG m 1 0 x = 0 :=
    genG_off (kruskalA m) (kruskalA m) (kruskalS m) x 1 0 (by decide)
  rw [hK, mul_zero, kruskalRad_eq,
    show kruskalG m = genG (kruskalA m) (kruskalA m) zero2 (kruskalS m) from rfl,
    hessT_conf_xt, kruskal_drdtR hm h, kruskal_dtR hm h, kruskal_drR hm h, kruskal_dtA hm h,
    kruskal_drA hm h, show kruskalA m (x 0) (x 1) = kruskalAu m (x 1 ^ 2 - x 0 ^ 2) from rfl]
  unfold kruskalRu1 kruskalRu2
  generalize kruskalAu m (x 1 ^ 2 - x 0 ^ 2) = a at ha ⊢
  field_simp
  ring

/-- The second slope of Kruskal's radius, entry "pole angle, pole angle":
`((r - 2m) / r²) · g`. -/
theorem hessT_kruskalRad_θθ (hm : 0 < m) (hx : x ∈ kruskalRegion) :
    hessT (kruskalG m) (genGinv (kruskalA m) (kruskalA m) zero2 (kruskalS m)) (kruskalRad m)
        2 2 x = (kruskalRad m x - 2 * m) / kruskalRad m x ^ 2 * kruskalG m 2 2 x := by
  have h : -1 < x 1 ^ 2 - x 0 ^ 2 := hx.1
  have hm' : m ≠ 0 := hm.ne'
  have hr : kruskalR m (x 1 ^ 2 - x 0 ^ 2) ≠ 0 := (kruskalR_pos hm h).ne'
  have ha : kruskalAu m (x 1 ^ 2 - x 0 ^ 2) ≠ 0 := (kruskalA_pos hm h).ne'
  have key := kruskalSu1_mul hm h
  have hK : kruskalG m 2 2 x = kruskalR m (x 1 ^ 2 - x 0 ^ 2) ^ 2 :=
    genG_θθ (kruskalA m) (kruskalA m) zero2 (kruskalS m) x
  have hrad : kruskalRad m x = kruskalR m (x 1 ^ 2 - x 0 ^ 2) := rfl
  rw [hK, hrad, kruskalRad_eq,
    show kruskalG m = genG (kruskalA m) (kruskalA m) zero2 (kruskalS m) from rfl,
    hessT_conf_θθ, kruskal_dtR hm h, kruskal_drR hm h, kruskal_dtS hm h, kruskal_drS hm h,
    show kruskalA m (x 0) (x 1) = kruskalAu m (x 1 ^ 2 - x 0 ^ 2) from rfl]
  unfold kruskalRu1
  generalize kruskalAu m (x 1 ^ 2 - x 0 ^ 2) = a at ha ⊢
  generalize kruskalSu1 m (x 1 ^ 2 - x 0 ^ 2) = s1 at key ⊢
  refine Eq.trans (b := (x 1 ^ 2 - x 0 ^ 2) * s1 / (4 * m)) ?_ ?_
  · field_simp
    ring
  · rw [key]
    field_simp

/-- The second slope of Kruskal's radius, entry "angle around the axis, twice":
`((r - 2m) / r²) · g`. -/
theorem hessT_kruskalRad_φφ (hm : 0 < m) (hx : x ∈ kruskalRegion) :
    hessT (kruskalG m) (genGinv (kruskalA m) (kruskalA m) zero2 (kruskalS m)) (kruskalRad m)
        3 3 x = (kruskalRad m x - 2 * m) / kruskalRad m x ^ 2 * kruskalG m 3 3 x := by
  have h : -1 < x 1 ^ 2 - x 0 ^ 2 := hx.1
  have hm' : m ≠ 0 := hm.ne'
  have hr : kruskalR m (x 1 ^ 2 - x 0 ^ 2) ≠ 0 := (kruskalR_pos hm h).ne'
  have ha : kruskalAu m (x 1 ^ 2 - x 0 ^ 2) ≠ 0 := (kruskalA_pos hm h).ne'
  have key := kruskalSu1_mul hm h
  have hK : kruskalG m 3 3 x = kruskalR m (x 1 ^ 2 - x 0 ^ 2) ^ 2 * sin (x 2) ^ 2 :=
    genG_φφ (kruskalA m) (kruskalA m) zero2 (kruskalS m) x
  have hrad : kruskalRad m x = kruskalR m (x 1 ^ 2 - x 0 ^ 2) := rfl
  rw [hK, hrad, kruskalRad_eq,
    show kruskalG m = genG (kruskalA m) (kruskalA m) zero2 (kruskalS m) from rfl,
    hessT_conf_φφ, kruskal_dtR hm h, kruskal_drR hm h, kruskal_dtS hm h, kruskal_drS hm h,
    show kruskalA m (x 0) (x 1) = kruskalAu m (x 1 ^ 2 - x 0 ^ 2) from rfl]
  unfold kruskalRu1
  generalize kruskalAu m (x 1 ^ 2 - x 0 ^ 2) = a at ha ⊢
  generalize kruskalSu1 m (x 1 ^ 2 - x 0 ^ 2) = s1 at key ⊢
  refine Eq.trans (b := (x 1 ^ 2 - x 0 ^ 2) * s1 / (4 * m) * sin (x 2) ^ 2) ?_ ?_
  · field_simp
    ring
  · rw [key]
    field_simp

/-- The second slope of Kruskal's radius has no entry between two different directions of
which one is an angle. -/
theorem hessT_kruskalRad_zero (m : ℝ) (x : Coords 4) (a b : Fin 4) (hab : a ≠ b)
    (h : 2 ≤ a.val ∨ 2 ≤ b.val) :
    hessT (kruskalG m) (genGinv (kruskalA m) (kruskalA m) zero2 (kruskalS m)) (kruskalRad m)
        a b x = 0 := by
  rw [kruskalRad_eq]
  exact hessT_conf_zero (kruskalA m) (kruskalS m) (sqDiff (kruskalR m)) x a b hab h

/-- **On the plane of `T` and `X`, the second slope of Kruskal's radius is `(m / r²) · g`.** -/
theorem hessT_kruskalRad_plane (hm : 0 < m) (hx : x ∈ kruskalRegion) (a b : Fin 4)
    (ha : a.val < 2) (hb : b.val < 2) :
    hessT (kruskalG m) (genGinv (kruskalA m) (kruskalA m) zero2 (kruskalS m)) (kruskalRad m)
        a b x = m / kruskalRad m x ^ 2 * kruskalG m a b x := by
  rcases fin4_lt_two a ha with rfl | rfl <;> rcases fin4_lt_two b hb with rfl | rfl
  · exact hessT_kruskalRad_tt hm hx
  · exact hessT_kruskalRad_tx hm hx
  · exact hessT_kruskalRad_xt hm hx
  · exact hessT_kruskalRad_xx hm hx

/-- **On the sphere, the second slope of Kruskal's radius is `((r - 2m) / r²) · g`.** -/
theorem hessT_kruskalRad_sphere (hm : 0 < m) (hx : x ∈ kruskalRegion) (a b : Fin 4)
    (ha : 2 ≤ a.val) (hb : 2 ≤ b.val) :
    hessT (kruskalG m) (genGinv (kruskalA m) (kruskalA m) zero2 (kruskalS m)) (kruskalRad m)
        a b x = (kruskalRad m x - 2 * m) / kruskalRad m x ^ 2 * kruskalG m a b x := by
  rcases fin4_ge_two a ha with rfl | rfl <;> rcases fin4_ge_two b hb with rfl | rfl
  · exact hessT_kruskalRad_θθ hm hx
  · rw [hessT_kruskalRad_zero m x 2 3 (by decide) (Or.inl (by decide)),
      show kruskalG m 2 3 x = 0 from
        genG_off (kruskalA m) (kruskalA m) (kruskalS m) x 2 3 (by decide), mul_zero]
  · rw [hessT_kruskalRad_zero m x 3 2 (by decide) (Or.inl (by decide)),
      show kruskalG m 3 2 x = 0 from
        genG_off (kruskalA m) (kruskalA m) (kruskalS m) x 3 2 (by decide), mul_zero]
  · exact hessT_kruskalRad_φφ hm hx

/-- **Between the plane of `T` and `X` and the sphere, the second slope of Kruskal's radius is
zero.** -/
theorem hessT_kruskalRad_mixed (m : ℝ) (x : Coords 4) (a b : Fin 4)
    (h : (a.val < 2 ∧ 2 ≤ b.val) ∨ (2 ≤ a.val ∧ b.val < 2)) :
    hessT (kruskalG m) (genGinv (kruskalA m) (kruskalA m) zero2 (kruskalS m)) (kruskalRad m)
        a b x = 0 := by
  refine hessT_kruskalRad_zero m x a b ?_ (by omega)
  rintro rfl
  omega

/-- **The second slope of Kruskal's radius,** at every point of Kruskal's region, the rim
included: `(m / r²) · g` on the plane of `T` and `X`, `((r - 2m) / r²) · g` on the sphere, and
zero between the two. -/
theorem hessT_kruskalRad (hm : 0 < m) (hx : x ∈ kruskalRegion) (a b : Fin 4) :
    hessT (kruskalG m) (genGinv (kruskalA m) (kruskalA m) zero2 (kruskalS m)) (kruskalRad m)
        a b x
      = (if a.val < 2 ∧ b.val < 2 then m / kruskalRad m x ^ 2
          else if 2 ≤ a.val ∧ 2 ≤ b.val then (kruskalRad m x - 2 * m) / kruskalRad m x ^ 2
          else 0) * kruskalG m a b x := by
  by_cases h1 : a.val < 2 ∧ b.val < 2
  · rw [if_pos h1]
    exact hessT_kruskalRad_plane hm hx a b h1.1 h1.2
  · by_cases h2 : 2 ≤ a.val ∧ 2 ≤ b.val
    · rw [if_neg h1, if_pos h2]
      exact hessT_kruskalRad_sphere hm hx a b h2.1 h2.2
    · rw [if_neg h1, if_neg h2, zero_mul]
      exact hessT_kruskalRad_mixed m x a b (by omega)

end KruskalHess

end GravityInLean.Curved
