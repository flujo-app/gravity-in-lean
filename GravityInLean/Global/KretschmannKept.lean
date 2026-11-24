/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.Kretschmann
public import GravityInLean.Join.NewTable

import Mathlib.Tactic

/-!
# A map that carries one table to another carries the curvature scalar

Step 8 of the route to `GlobalBirkhoffUnique`, the general half. If a map `f` of coordinate space
carries the table `g` to the table `h` near a point `x` (`CarriesTableAt`), then the curvature
scalar of `h` at `f x` is the curvature scalar of `g` at `x` (`kretschmann_eq_of_carries`).

The reason, in steps:

* near `x`, the table `h` written in the coordinates that `f` gives is the table `g`
  (`CarriesTableAt.eventually_inNewCoords`), so the two have the same connection near `x`
  (`christoffel_congr`) and the same full curvature at `x` (`riemM_congr`);
* the full curvature of `h` in the new coordinates is the full curvature of `h`, re-written
  (`riemann_inNewCoords`), and the inverse table is re-written the opposite way;
* in the curvature scalar the two re-writings cancel (`kretschmann_algebra`,
  `trace_conj_mul`).

Only coordinates are used here; no curved spaces.
-/

@[expose] public section

namespace GravityInLean.Curved

open Filter Topology Matrix

open scoped ContDiff

variable {n : ℕ}

/-! ## The algebra: the re-writings cancel -/

/-- One pair of directions: summing a table `Q`, re-written in both of its directions by `J`,
against `Gi` is summing `Q` itself against `J · Gi · Jᵀ`. -/
theorem contract_pair (J Gi : Matrix (Fin n) (Fin n) ℝ) (Q : Fin n → Fin n → ℝ) :
    ∑ ρ, ∑ σ, Gi ρ σ * ∑ δ, ∑ δ', J δ ρ * J δ' σ * Q δ δ'
      = ∑ δ, ∑ δ', (J * Gi * Jᵀ) δ δ' * Q δ δ' := by
  simp only [Finset.mul_sum]
  refine (sum4_swap _).trans ?_
  refine Finset.sum_congr rfl fun δ _ ↦ Finset.sum_congr rfl fun δ' _ ↦ ?_
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  refine Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun σ _ ↦ Finset.sum_congr rfl fun ρ _ ↦ by ring

/-- Two pairs of directions: the same for a table `T` with four directions. -/
theorem contract_two (J Gi : Matrix (Fin n) (Fin n) ℝ) (T : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ∑ ρ, ∑ μ, ∑ σ, ∑ τ, Gi ρ σ * Gi μ τ
        * ∑ δ, ∑ δ', J δ ρ * J δ' σ * ∑ β, ∑ β', J β μ * J β' τ * T δ β δ' β'
      = ∑ δ, ∑ β, ∑ δ', ∑ β', (J * Gi * Jᵀ) δ δ' * (J * Gi * Jᵀ) β β' * T δ β δ' β' := by
  calc ∑ ρ, ∑ μ, ∑ σ, ∑ τ, Gi ρ σ * Gi μ τ
        * ∑ δ, ∑ δ', J δ ρ * J δ' σ * ∑ β, ∑ β', J β μ * J β' τ * T δ β δ' β'
      = ∑ μ, ∑ τ, Gi μ τ * ∑ ρ, ∑ σ, Gi ρ σ
          * ∑ δ, ∑ δ', J δ ρ * J δ' σ * ∑ β, ∑ β', J β μ * J β' τ * T δ β δ' β' := by
        refine Finset.sum_comm.trans ?_
        refine Finset.sum_congr rfl fun μ _ ↦ ?_
        refine (sum3_rotate _).trans ?_
        refine Finset.sum_congr rfl fun τ _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ρ _ ↦ ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun σ _ ↦ by ring
    _ = ∑ μ, ∑ τ, Gi μ τ * ∑ δ, ∑ δ', (J * Gi * Jᵀ) δ δ'
          * ∑ β, ∑ β', J β μ * J β' τ * T δ β δ' β' := by
        refine Finset.sum_congr rfl fun μ _ ↦ Finset.sum_congr rfl fun τ _ ↦ ?_
        congr 1
        exact contract_pair J Gi fun δ δ' ↦ ∑ β, ∑ β', J β μ * J β' τ * T δ β δ' β'
    _ = ∑ δ, ∑ δ', (J * Gi * Jᵀ) δ δ' * ∑ μ, ∑ τ, Gi μ τ
          * ∑ β, ∑ β', J β μ * J β' τ * T δ β δ' β' := by
        simp only [Finset.mul_sum]
        refine (sum4_swap _).trans ?_
        exact Finset.sum_congr rfl fun δ _ ↦ Finset.sum_congr rfl fun δ' _ ↦
          Finset.sum_congr rfl fun μ _ ↦ Finset.sum_congr rfl fun τ _ ↦
          Finset.sum_congr rfl fun β _ ↦ Finset.sum_congr rfl fun β' _ ↦ by ring
    _ = ∑ δ, ∑ δ', (J * Gi * Jᵀ) δ δ' * ∑ β, ∑ β', (J * Gi * Jᵀ) β β' * T δ β δ' β' := by
        refine Finset.sum_congr rfl fun δ _ ↦ Finset.sum_congr rfl fun δ' _ ↦ ?_
        congr 1
        exact contract_pair J Gi fun β β' ↦ T δ β δ' β'
    _ = ∑ δ, ∑ β, ∑ δ', ∑ β', (J * Gi * Jᵀ) δ δ' * (J * Gi * Jᵀ) β β' * T δ β δ' β' := by
        refine Finset.sum_congr rfl fun δ _ ↦ ?_
        simp only [Finset.mul_sum]
        refine Finset.sum_comm.trans ?_
        exact Finset.sum_congr rfl fun β _ ↦ Finset.sum_congr rfl fun δ' _ ↦
          Finset.sum_congr rfl fun β' _ ↦ by ring

/-- A family of tables `R`, one for each pair of directions, with both directions re-written by
the table of slopes `J`. -/
noncomputable def pullTwo (J : Matrix (Fin n) (Fin n) ℝ)
    (R : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ) (ρ μ : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ δ, ∑ β, (J δ ρ * J β μ) • R δ β

/-- The product of two re-written tables, summed over its diagonal, written out. -/
theorem trace_pullTwo_mul (J : Matrix (Fin n) (Fin n) ℝ)
    (R : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ) (ρ μ σ τ : Fin n) :
    (pullTwo J R ρ μ * pullTwo J R σ τ).trace
      = ∑ δ, ∑ δ', J δ ρ * J δ' σ * ∑ β, ∑ β', J β μ * J β' τ * (R δ β * R δ' β').trace := by
  rw [pullTwo, pullTwo, Finset.sum_mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun δ _ ↦ ?_
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl fun δ' _ ↦ ?_
  rw [Finset.sum_mul_sum, Matrix.trace_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ ↦ ?_
  rw [Matrix.trace_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β' _ ↦ ?_
  rw [smul_mul_smul_comm, Matrix.trace_smul, smul_eq_mul]
  ring

/-- **The re-writings cancel.** The curvature scalar built from the re-written tables and `Gi`
is the curvature scalar built from the tables themselves and `J · Gi · Jᵀ`. -/
theorem kretschmann_algebra (J Gi : Matrix (Fin n) (Fin n) ℝ)
    (R : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ) :
    ∑ ρ, ∑ μ, ∑ σ, ∑ τ, Gi ρ σ * Gi μ τ * (pullTwo J R ρ μ * pullTwo J R σ τ).trace
      = ∑ δ, ∑ β, ∑ δ', ∑ β', (J * Gi * Jᵀ) δ δ' * (J * Gi * Jᵀ) β β'
          * (R δ β * R δ' β').trace := by
  simp only [trace_pullTwo_mul]
  exact contract_two J Gi fun δ β δ' β' ↦ (R δ β * R δ' β').trace

/-- Two tables, each put between `K` and `J` with `J · K = 1`, have the same product summed
over its diagonal as the two tables themselves. -/
theorem trace_conj_mul {J K A B : Matrix (Fin n) (Fin n) ℝ} (hJK : J * K = 1) :
    (K * A * J * (K * B * J)).trace = (A * B).trace := by
  have e : K * A * J * (K * B * J) = K * (A * B * J) := by
    calc K * A * J * (K * B * J) = K * A * (J * K) * B * J := by simp only [Matrix.mul_assoc]
      _ = K * (A * B * J) := by
          rw [hJK, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm K, Matrix.mul_assoc, hJK, Matrix.mul_one]

/-! ## Tables that agree near a point -/

/-- Two tables that agree near `x` have the same connection at `x`, for the same inverse
table. -/
theorem christoffel_congr {g g' ginv : Fin n → Fin n → Coords n → ℝ} {x : Coords n}
    (hgg : ∀ᶠ y in 𝓝 x, ∀ μ ν, g' μ ν y = g μ ν y) (a b c : Fin n) :
    christoffel g' ginv a b c x = christoffel g ginv a b c x := by
  have hs : ∀ μ ν i, slope i (g' μ ν) x = slope i (g μ ν) x := fun μ ν i ↦
    slope_congr (hgg.mono fun y hy ↦ hy μ ν) i
  simp only [christoffel, hs]

/-- Two connections that agree near `x` have the same full curvature at `x`. -/
theorem riemM_congr {Γ Γ' : Fin n → Fin n → Fin n → Coords n → ℝ} {x : Coords n}
    (hΓ : ∀ᶠ y in 𝓝 x, ∀ a b c, Γ' a b c y = Γ a b c y) (ρ μ : Fin n) :
    riemM Γ' ρ μ x = riemM Γ ρ μ x := by
  have hev : ∀ a b c, Γ' a b c =ᶠ[𝓝 x] Γ a b c := fun a b c ↦ hΓ.mono fun y hy ↦ hy a b c
  have hd : ∀ τ κ, dtab τ (dirT Γ' κ) x = dtab τ (dirT Γ κ) x := fun τ κ ↦ by
    ext a c
    change slope τ (Γ' a κ c) x = slope τ (Γ a κ c) x
    exact slope_congr (hev a κ c) τ
  have ht : ∀ κ, tab (dirT Γ' κ) x = tab (dirT Γ κ) x := fun κ ↦ by
    ext a c
    change Γ' a κ c x = Γ a κ c x
    exact (hev a κ c).eq_of_nhds
  simp only [riemM, hd, ht]

/-- **A map that carries `g` to `h` near `x` makes `h`, written in the coordinates the map
gives, equal to `g` near `x`.** -/
theorem CarriesTableAt.eventually_inNewCoords {g h : Fin n → Fin n → Coords n → ℝ}
    {f : Coords n → Coords n} {x : Coords n} (hf : CarriesTableAt g h f x) :
    ∀ᶠ y in 𝓝 x, ∀ μ ν, inNewCoords f h μ ν y = g μ ν y := by
  have hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    ((hf.1.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)).eventually (by simp)).mono fun y hy ↦
      hy.differentiableAt (by simp)
  filter_upwards [hd, hf.2] with y hy hc μ ν
  calc inNewCoords f h μ ν y
      = tableMeasure (inNewCoords f h) y (Pi.single μ 1) (Pi.single ν 1) :=
        (formOf_single_single (fun a b ↦ inNewCoords f h a b y) μ ν).symm
    _ = tableMeasure h (f y) (fderiv ℝ f y (Pi.single μ 1)) (fderiv ℝ f y (Pi.single ν 1)) :=
        Join.tableMeasure_inNewCoords h hy _ _
    _ = tableMeasure g y (Pi.single μ 1) (Pi.single ν 1) := hc _ _
    _ = g μ ν y := formOf_single_single (fun a b ↦ g a b y) μ ν

/-! ## The curvature scalar is carried -/

/-- **A map that carries one table to another carries the curvature scalar.** If `f` carries the
good table `g` to the good table `h` near `x`, the curvature scalar of `h` at `f x` is the
curvature scalar of `g` at `x`. -/
theorem kretschmann_eq_of_carries {g ginv h hinv : Fin n → Fin n → Coords n → ℝ}
    {s t : Set (Coords n)} (hg : IsRegularTableOn g ginv s) (hh : IsRegularTableOn h hinv t)
    {f : Coords n → Coords n} {x : Coords n} (hx : x ∈ s) (hfx : f x ∈ t)
    (hf : CarriesTableAt g h f x) : kretschmann h hinv (f x) = kretschmann g ginv x := by
  -- Near `x`, the table `h` in the coordinates of `f` is `g`.
  have hgg := hf.eventually_inNewCoords
  have hfc : ContinuousAt f x := hf.1.continuousAt
  have hf3 : ∀ α, ContDiffAt ℝ 3 (fun z ↦ f z α) x := fun α ↦
    (contDiffAt_pi.1 (hf.1.of_le (by norm_num : (3 : WithTop ℕ∞) ≤ ∞))) α
  have hf2ev : ∀ᶠ y in 𝓝 x, ∀ α, ContDiffAt ℝ 2 (fun z ↦ f z α) y :=
    eventually_all.2 fun α ↦
      ((hf3 α).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).eventually (by simp)
  have hsev : ∀ᶠ y in 𝓝 x, y ∈ s := hg.isOpen.mem_nhds hx
  have htev : ∀ᶠ y in 𝓝 x, f y ∈ t := hfc.eventually (hh.isOpen.mem_nhds hfx)
  -- The law for connections holds near `x`.
  have hlaw : ∀ᶠ y in 𝓝 x, ∀ ε μ ν,
      ∑ κ, jac f ε κ y * christoffel (inNewCoords f h) ginv κ μ ν y
        = slope μ (jac f ε ν) y
          + ∑ β, ∑ γ, jac f β μ y * christoffel h hinv ε β γ (f y) * jac f γ ν y := by
    filter_upwards [hf2ev, hsev, htev, hgg] with y h1 h2 h3 h4 ε μ ν
    refine christoffel_inNewCoords_at h1 (fun α β ↦ hh.differentiableAt h3 α β)
      (hh.symm _ h3) (hh.inverse _ h3) (fun μ κ ↦ ?_) ε μ ν
    exact (Finset.sum_congr rfl fun ν _ ↦ by rw [h4 μ ν]).trans (hg.inverse y h2 μ κ)
  -- The connection of `h` in the new coordinates is the connection of `g` near `x`.
  have hΓev : ∀ᶠ y in 𝓝 x, ∀ a b c,
      christoffel (inNewCoords f h) ginv a b c y = christoffel g ginv a b c y :=
    hgg.eventually_nhds.mono fun y hy a b c ↦ christoffel_congr hy a b c
  have hΓ' : ∀ a b c, DifferentiableAt ℝ (christoffel (inNewCoords f h) ginv a b c) x :=
    fun a b c ↦ (hg.differentiableAt_christoffel hx a b c).congr_of_eventuallyEq
      (hΓev.mono fun y hy ↦ hy a b c)
  -- The full curvature of `g` at `x` is the full curvature of `h` at `f x`, re-written.
  have hR : ∀ ρ μ, tab (jac f) x * riemM (christoffel g ginv) ρ μ x
      = pullTwo (tab (jac f) x) (fun δ β ↦ riemM (christoffel h hinv) δ β (f x)) ρ μ
        * tab (jac f) x := fun ρ μ ↦ by
    rw [← riemM_congr hΓev ρ μ]
    exact riemann_inNewCoords hf3 hΓ' (fun a b c ↦ hh.differentiableAt_christoffel hfx a b c)
      hlaw ρ μ
  -- The tables at the point, and their inverses.
  have hG : tab g x = (tab (jac f) x)ᵀ * tab h (f x) * tab (jac f) x := by
    rw [← tab_inNewCoords]
    ext μ ν
    exact (hgg.self_of_nhds μ ν).symm
  have hGGi : tab g x * tab ginv x = 1 := by
    ext a c
    simp only [tab, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    exact hg.inverse x hx a c
  have hHHi : tab h (f x) * tab hinv (f x) = 1 := by
    ext a c
    simp only [tab, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    exact hh.inverse (f x) hfx a c
  -- The inverse of `h` is the inverse of `g`, re-written the opposite way.
  have hHi : tab (jac f) x * tab ginv x * (tab (jac f) x)ᵀ = tab hinv (f x) := by
    have h0 : (tab (jac f) x)ᵀ * tab h (f x) * tab (jac f) x * tab ginv x = 1 := by
      rw [← hG]
      exact hGGi
    have h1 : (tab (jac f) x)ᵀ * (tab h (f x) * tab (jac f) x * tab ginv x) = 1 := by
      rw [← h0]
      simp only [Matrix.mul_assoc]
    have h2 : tab h (f x) * tab (jac f) x * tab ginv x * (tab (jac f) x)ᵀ = 1 :=
      mul_eq_one_comm.mp h1
    have h3 : tab h (f x) * (tab (jac f) x * tab ginv x * (tab (jac f) x)ᵀ) = 1 := by
      rw [← h2]
      simp only [Matrix.mul_assoc]
    exact (Matrix.inv_eq_right_inv h3).symm.trans (Matrix.inv_eq_right_inv hHHi)
  -- The table of slopes of `f` has an inverse.
  obtain ⟨K, hK⟩ := exists_inverse_jac (Φ := f) (g := h) (ginv' := ginv) (x := x) fun μ κ ↦
    (Finset.sum_congr rfl fun ν _ ↦ by rw [hgg.self_of_nhds μ ν]).trans (hg.inverse x hx μ κ)
  have hKJ : K * tab (jac f) x = 1 := mul_eq_one_comm.mp hK
  have hRg : ∀ ρ μ, riemM (christoffel g ginv) ρ μ x
      = K * pullTwo (tab (jac f) x) (fun δ β ↦ riemM (christoffel h hinv) δ β (f x)) ρ μ
        * tab (jac f) x := fun ρ μ ↦ by
    rw [Matrix.mul_assoc, ← hR ρ μ, ← Matrix.mul_assoc, hKJ, Matrix.one_mul]
  -- The algebra: the re-writings cancel.
  have alg := kretschmann_algebra (tab (jac f) x) (tab ginv x)
    (fun δ β ↦ riemM (christoffel h hinv) δ β (f x))
  rw [hHi] at alg
  calc kretschmann h hinv (f x)
      = ∑ δ, ∑ β, ∑ δ', ∑ β', tab hinv (f x) δ δ' * tab hinv (f x) β β'
          * (riemM (christoffel h hinv) δ β (f x)
            * riemM (christoffel h hinv) δ' β' (f x)).trace := rfl
    _ = ∑ ρ, ∑ μ, ∑ σ, ∑ τ, tab ginv x ρ σ * tab ginv x μ τ
          * (pullTwo (tab (jac f) x) (fun δ β ↦ riemM (christoffel h hinv) δ β (f x)) ρ μ
            * pullTwo (tab (jac f) x) (fun δ β ↦ riemM (christoffel h hinv) δ β (f x))
              σ τ).trace := alg.symm
    _ = kretschmann g ginv x := by
        refine Finset.sum_congr rfl fun ρ _ ↦ Finset.sum_congr rfl fun μ _ ↦
          Finset.sum_congr rfl fun σ _ ↦ Finset.sum_congr rfl fun τ _ ↦ ?_
        rw [hRg ρ μ, hRg σ τ, trace_conj_mul hK]
        rfl

end GravityInLean.Curved
