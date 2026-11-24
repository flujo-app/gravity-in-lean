/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.GlobalComplete

import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Checks of the definitions for G2: paths of free fall, and Kruskal's foldings

The definitions of `Goals/GlobalComplete.lean` are tested here on cases with known answers,
before anyone tries to prove the statements built on them.

**Paths of free fall, on coordinate space** (whose only chart is the one that does nothing):

* `isFreeFallPath_self_iff`: there, a path of free fall is a smooth curve on an open interval
  that obeys the coordinate equation `IsFreeFallAt` of `Curvature.lean` with the connection of
  the length measure's own table.
* `line_isFreeFallPath`: in flat space-time, straight lines run at a steady rate are paths of
  free fall, on every open interval.
* `bent_not_isFreeFallPath`: a curve that speeds up (`τ ↦ (τ, τ², 0, 0)`) is not, on any
  interval that is not empty.
* `kink_falls`, `kink_not_isFreeFallPath`: a curve with a kink, `τ ↦ (|τ|, 0, 0, 0)`, passes the
  equation at every time, because Lean gives the kink a slope of zero; only the smoothness clause
  rules it out. So that clause is needed, and it does its job.
* `inRay_isFreeFallPath`: a ray of light falling straight into Schwarzschild's mass, written in
  Schwarzschild's own table outside the rim, is a path of free fall (the equation is not trivial
  here: time and distance bend each other through the connection).
* `inRaySlow_not_isFreeFallPath`: the same ray run at a clock that is not the path's own (its
  parameter squared) is not: the equation fixes the clock along the path.
* `inRayIn_isFreeFallPath`, `inRayIn_sizeSq`: a path of free fall in Schwarzschild's table inside
  the rim (a ray of light) stops at a finite time with the spheres shrinking to zero, as the
  second case of the completeness condition allows (that such a path cannot be continued in
  Kruskal's whole space-time is part of `GlobalCompleteConverse`).
* `line_isInextendible`, `line_short_not_isInextendible`: a straight line on all times cannot be
  continued; on the times between 0 and 1 it can.
* `minkowski_path_eq_line`, `minkowski_freeFallComplete`: in flat space-time every path of free
  fall is a piece of a straight line, so every one that cannot be continued runs for all times,
  and flat space-time meets the completeness condition (for any three fields). So the condition
  can be met, and it does not ask for paths that are not there.

**Orientation, on coordinate space:** `coords_isOrientable`, `minkowski_isTimeOrientable`.

**Kruskal's whole space-time and its foldings:**

* `kruskalChart_isKruskalMapOn`: every wrap chart keeps lengths: it is a length-keeping map from
  Kruskal's table into Kruskal's whole space-time.
* `kruskalChart_covers`: the wrap charts reach every point of Kruskal's whole space-time, the
  poles of the sphere included; so `IsKruskalOnto` asks for smoothness and lengths everywhere.
* `kruskalFold_mem`, `kruskalFold_measure`, `kruskalFold_fold`, `kruskalFold_ne`: each of the four
  folds sends Kruskal's whole space-time to itself, keeps its lengths, undoes itself, and moves
  every point. So dividing by a fold is dividing by a free action of a group of two symmetries.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set Filter Topology

open scoped Manifold ContDiff

/-! ## Paths of free fall on coordinate space -/

section Self

variable {n : ℕ}

/-- The table of a length measure on coordinate space, read in the plain coordinates. -/
noncomputable def selfTable (g : LengthMeasure 𝓘(ℝ, Coords n) (Coords n)) :
    Fin n → Fin n → Coords n → ℝ :=
  fun a b y ↦ g y (Pi.single a 1) (Pi.single b 1)

/-- Its inverse table: the inverse matrix at each point. -/
noncomputable def selfTableInv (g : LengthMeasure 𝓘(ℝ, Coords n) (Coords n)) :
    Fin n → Fin n → Coords n → ℝ :=
  fun a b y ↦ (Matrix.of fun i j ↦ selfTable g i j y)⁻¹ a b

/-- On coordinate space the chart at every point does nothing, so the chart's table is the plain
table. -/
theorem chartTable_self (g : LengthMeasure 𝓘(ℝ, Coords n) (Coords n)) (x : Coords n) :
    chartTable g (chartAt (Coords n) x) = selfTable g := by
  rw [chartAt_self_eq]
  funext a b y
  have h : ∀ v : Coords n, mfderiv 𝓘(ℝ, Coords n) 𝓘(ℝ, Coords n)
      (OpenPartialHomeomorph.refl (Coords n)).symm y v = v := by
    intro v
    have e : mfderiv 𝓘(ℝ, Coords n) 𝓘(ℝ, Coords n) (OpenPartialHomeomorph.refl (Coords n)).symm y
        = mfderiv 𝓘(ℝ, Coords n) 𝓘(ℝ, Coords n) (id : Coords n → Coords n) y := rfl
    rw [e, mfderiv_id]
    rfl
  simp only [chartTable, selfTable, h]
  rfl

theorem chartTableInv_self (g : LengthMeasure 𝓘(ℝ, Coords n) (Coords n)) (x : Coords n) :
    chartTableInv g (chartAt (Coords n) x) = selfTableInv g := by
  funext a b y
  simp only [chartTableInv, selfTableInv, chartTable_self]

theorem fallsFreelyIn_self (g : LengthMeasure 𝓘(ℝ, Coords n) (Coords n)) (γ : ℝ → Coords n)
    (τ : ℝ) (x : Coords n) :
    FallsFreelyIn g (chartAt (Coords n) x) γ τ
      ↔ IsFreeFallAt (christoffel (selfTable g) (selfTableInv g)) γ τ := by
  unfold FallsFreelyIn
  rw [chartTable_self, chartTableInv_self, chartAt_self_eq]
  rfl

/-- **On coordinate space, a path of free fall is a smooth curve on an open interval that obeys
the coordinate equation of free fall** with the connection of the plain table. -/
theorem isFreeFallPath_self_iff (g : LengthMeasure 𝓘(ℝ, Coords n) (Coords n))
    (γ : ℝ → Coords n) (J : Set ℝ) :
    IsFreeFallPath g γ J ↔ IsOpen J ∧ J.OrdConnected ∧ ContDiffOn ℝ ∞ γ J ∧
      ∀ τ ∈ J, IsFreeFallAt (christoffel (selfTable g) (selfTableInv g)) γ τ := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, contMDiffOn_iff_contDiffOn.mp h3,
      fun τ hτ ↦ (fallsFreelyIn_self g γ τ _).mp (h4 τ hτ)⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, contMDiffOn_iff_contDiffOn.mpr h3,
      fun τ hτ ↦ (fallsFreelyIn_self g γ τ _).mpr (h4 τ hτ)⟩

/-- The plain table of the length measure that a table of functions describes is that table. -/
theorem selfTable_table (G : Fin n → Fin n → Coords n → ℝ) :
    selfTable (flatMeasure (tableMeasure G)) = G := by
  funext a b y
  exact formOf_single_single (fun a b ↦ G a b y) a b

/-- Where a table has a known inverse, the inverse matrix is that inverse. -/
theorem selfTableInv_table_at {G Ginv : Fin n → Fin n → Coords n → ℝ} {x : Coords n}
    (h : ∀ i k, ∑ j, G i j x * Ginv j k x = if i = k then 1 else 0) (a b : Fin n) :
    selfTableInv (flatMeasure (tableMeasure G)) a b x = Ginv a b x := by
  have hm : (Matrix.of fun i j ↦ G i j x) * (Matrix.of fun i j ↦ Ginv i j x) = 1 := by
    ext i k
    simp only [Matrix.mul_apply, Matrix.of_apply, h, Matrix.one_apply]
  simp only [selfTableInv, selfTable_table]
  rw [Matrix.inv_eq_right_inv hm]
  rfl

/-- The equation of free fall at `τ` only looks at the connection at the point `γ τ`. -/
theorem isFreeFallAt_congr {Γ Γ' : Fin n → Fin n → Fin n → Coords n → ℝ} {γ : ℝ → Coords n}
    {τ : ℝ} (h : ∀ a b c, Γ a b c (γ τ) = Γ' a b c (γ τ)) :
    IsFreeFallAt Γ γ τ ↔ IsFreeFallAt Γ' γ τ := by
  simp only [IsFreeFallAt, freeFallExpr, h]

/-- The connection at a point only looks at the inverse table at that point. -/
theorem christoffel_congr_inv {g ginv ginv' : Fin n → Fin n → Coords n → ℝ} {x : Coords n}
    (h : ∀ a b, ginv a b x = ginv' a b x) (a b c : Fin n) :
    christoffel g ginv a b c x = christoffel g ginv' a b c x := by
  simp only [christoffel, h]

end Self

/-! ## Flat space-time -/

section Minkowski

/-- Flat space-time (Minkowski's) on coordinate space. -/
noncomputable abbrev minkowski : LengthMeasure 𝓘(ℝ, Coords 4) (Coords 4) :=
  flatMeasure (tableMeasure flatG)

theorem christoffel_flatG_any (ginv : Fin 4 → Fin 4 → Coords 4 → ℝ) (a b c : Fin 4)
    (x : Coords 4) : christoffel flatG ginv a b c x = 0 := by
  have h : ∀ (i j k : Fin 4), slope k (flatG i j) x = 0 := fun i j k ↦ slope_const _ _ _
  simp [christoffel, h]

/-- In flat space-time, the equation of free fall says that the second slope of every
coordinate is zero. -/
theorem minkowski_isFreeFallAt_iff (γ : ℝ → Coords 4) (τ : ℝ) :
    IsFreeFallAt (christoffel (selfTable minkowski) (selfTableInv minkowski)) γ τ
      ↔ ∀ a, deriv (deriv fun s ↦ γ s a) τ = 0 := by
  simp [IsFreeFallAt, freeFallExpr, selfTable_table, christoffel_flatG_any]

/-- A straight line run at a steady rate: through `p` with velocity `v`. -/
def line (p v : Coords 4) (τ : ℝ) : Coords 4 := p + τ • v

theorem deriv_line (p v : Coords 4) (a : Fin 4) : deriv (fun s ↦ line p v s a) = fun _ ↦ v a := by
  funext s
  have h : HasDerivAt (fun s ↦ p a + s * v a) (1 * v a) s :=
    ((hasDerivAt_id s).mul_const (v a)).const_add (p a)
  have e : (fun s ↦ line p v s a) = fun s ↦ p a + s * v a := by
    funext s
    simp [line]
  rw [e, h.deriv, one_mul]

/-- **Straight lines are paths of free fall** in flat space-time, on every open interval. -/
theorem line_isFreeFallPath (p v : Coords 4) {J : Set ℝ} (hJ : IsOpen J) (hJ' : J.OrdConnected) :
    IsFreeFallPath minkowski (line p v) J := by
  rw [isFreeFallPath_self_iff]
  refine ⟨hJ, hJ', ?_, fun τ _ ↦ (minkowski_isFreeFallAt_iff _ τ).mpr fun a ↦ ?_⟩
  · exact (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn
  · rw [deriv_line]
    simp

/-- A curve that speeds up along the first space direction. -/
def bent (τ : ℝ) : Coords 4 := ![τ, τ ^ 2, 0, 0]

theorem bent_not_falls (τ : ℝ) :
    ¬ IsFreeFallAt (christoffel (selfTable minkowski) (selfTableInv minkowski)) bent τ := by
  rw [minkowski_isFreeFallAt_iff]
  intro h
  have h1 := h 1
  have e : (fun s ↦ bent s 1) = fun s ↦ s ^ 2 := by
    funext s
    simp [bent]
  have e2 : deriv (fun s : ℝ ↦ s ^ 2) = fun s ↦ 2 * s := by
    funext s
    simp
  rw [e, e2] at h1
  simp at h1

/-- **A bent line is not a path of free fall,** on any interval that is not empty. -/
theorem bent_not_isFreeFallPath {J : Set ℝ} (hJ : J.Nonempty) :
    ¬ IsFreeFallPath minkowski bent J := by
  intro h
  obtain ⟨τ, hτ⟩ := hJ
  exact bent_not_falls τ (((isFreeFallPath_self_iff _ _ _).mp h).2.2.2 τ hτ)

/-- A curve with a kink at the time `0`: time runs backwards before, forwards after. -/
def kink (τ : ℝ) : Coords 4 := ![|τ|, 0, 0, 0]

theorem deriv_sign_zero : deriv (fun s : ℝ ↦ (SignType.sign s : ℝ)) 0 = 0 := by
  apply deriv_zero_of_not_differentiableAt
  intro hd
  have h1 : Tendsto (fun s : ℝ ↦ (SignType.sign s : ℝ)) (𝓝[>] 0) (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp [sign_pos (show (0 : ℝ) < s from hs)]
  have h0 : Tendsto (fun s : ℝ ↦ (SignType.sign s : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have := hd.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have := tendsto_nhds_unique h1 h0
  norm_num at this

theorem deriv_deriv_abs (τ : ℝ) : deriv (deriv fun s : ℝ ↦ |s|) τ = 0 := by
  have e : (deriv fun s : ℝ ↦ |s|) = fun s ↦ (SignType.sign s : ℝ) := funext deriv_abs
  rw [e]
  rcases lt_trichotomy τ 0 with h | h | h
  · have hev : (fun s : ℝ ↦ (SignType.sign s : ℝ)) =ᶠ[𝓝 τ] fun _ ↦ -1 := by
      filter_upwards [Iio_mem_nhds h] with s hs
      simp [sign_neg (show s < 0 from hs)]
    rw [hev.deriv_eq]
    simp
  · subst h
    exact deriv_sign_zero
  · have hev : (fun s : ℝ ↦ (SignType.sign s : ℝ)) =ᶠ[𝓝 τ] fun _ ↦ 1 := by
      filter_upwards [Ioi_mem_nhds h] with s hs
      simp [sign_pos (show 0 < s from hs)]
    rw [hev.deriv_eq]
    simp

/-- **The kink passes the equation of free fall at every time,** with the slopes Lean makes up
where there is none. -/
theorem kink_falls (τ : ℝ) :
    IsFreeFallAt (christoffel (selfTable minkowski) (selfTableInv minkowski)) kink τ := by
  rw [minkowski_isFreeFallAt_iff]
  have h0 : deriv (deriv fun s ↦ kink s 0) τ = 0 := by
    have e : (fun s ↦ kink s 0) = fun s ↦ |s| := by
      funext s
      simp [kink]
    rw [e]
    exact deriv_deriv_abs τ
  have h1 : deriv (deriv fun s ↦ kink s 1) τ = 0 := by simp [kink]
  have h2 : deriv (deriv fun s ↦ kink s 2) τ = 0 := by simp [kink]
  have h3 : deriv (deriv fun s ↦ kink s 3) τ = 0 := by simp [kink]
  intro a
  fin_cases a
  exacts [h0, h1, h2, h3]

/-- **But the kink is not a path of free fall:** it is not smooth at the time `0`. -/
theorem kink_not_isFreeFallPath : ¬ IsFreeFallPath minkowski kink (Ioo (-1) 1) := by
  intro h
  have hs := ((isFreeFallPath_self_iff _ _ _).mp h).2.2.1
  have h0 : ContDiffOn ℝ ∞ (fun s ↦ kink s 0) (Ioo (-1) 1) := contDiffOn_pi.mp hs 0
  have e : (fun s ↦ kink s 0) = fun s ↦ |s| := by
    funext s
    simp [kink]
  rw [e] at h0
  have hd : DifferentiableAt ℝ (fun s : ℝ ↦ |s|) 0 :=
    (h0.differentiableOn (by simp)).differentiableAt (Ioo_mem_nhds (by norm_num) (by norm_num))
  exact not_differentiableAt_abs_zero hd

/-- **A straight line on all times cannot be continued.** -/
theorem line_isInextendible (p v : Coords 4) :
    IsInextendibleFreeFall minkowski (line p v) univ :=
  ⟨line_isFreeFallPath p v isOpen_univ ordConnected_univ,
    fun _ _ _ hJ _ ↦ univ_subset_iff.mp hJ⟩

/-- **A straight line on the times between `0` and `1` can be continued.** -/
theorem line_short_not_isInextendible (p v : Coords 4) :
    ¬ IsInextendibleFreeFall minkowski (line p v) (Ioo 0 1) := by
  rintro ⟨_, h⟩
  have e := h (line p v) univ (line_isFreeFallPath p v isOpen_univ ordConnected_univ)
    (subset_univ _) (fun _ _ ↦ rfl)
  have h2 : (2 : ℝ) ∈ Ioo (0 : ℝ) 1 := e ▸ mem_univ 2
  norm_num at h2

/-- **In flat space-time every path of free fall is a piece of a straight line.** -/
theorem minkowski_path_eq_line {γ : ℝ → Coords 4} {J : Set ℝ}
    (h : IsFreeFallPath minkowski γ J) : ∃ p v : Coords 4, EqOn (line p v) γ J := by
  obtain ⟨hJ, hJ', hs, hf⟩ := (isFreeFallPath_self_iff _ _ _).mp h
  have hpre : IsPreconnected J := hJ'.isPreconnected
  have key : ∀ a : Fin 4, ∃ c d : ℝ, ∀ s ∈ J, γ s a = s * c + d := by
    intro a
    have ha : ContDiffOn ℝ ∞ (fun s ↦ γ s a) J := contDiffOn_pi.mp hs a
    obtain ⟨hd, hd'⟩ := (contDiffOn_infty_iff_deriv_of_isOpen hJ).mp ha
    have hdd : DifferentiableOn ℝ (deriv fun s ↦ γ s a) J := hd'.differentiableOn (by simp)
    have h2 : J.EqOn (deriv (deriv fun s ↦ γ s a)) 0 := fun τ hτ ↦
      (minkowski_isFreeFallAt_iff γ τ).mp (hf τ hτ) a
    obtain ⟨c, hc⟩ := hJ.exists_is_const_of_deriv_eq_zero hpre hdd h2
    have hlin : DifferentiableOn ℝ (fun s : ℝ ↦ s * c) J :=
      DifferentiableOn.mul_const differentiableOn_id c
    have heq : J.EqOn (deriv fun s ↦ γ s a) (deriv fun s : ℝ ↦ s * c) := fun τ hτ ↦ by
      rw [hc τ hτ]
      simp
    obtain ⟨d, hd2⟩ := hJ.exists_eq_add_of_deriv_eq hpre hd hlin heq
    exact ⟨c, d, fun s hs ↦ hd2 hs⟩
  choose c d hcd using key
  refine ⟨d, c, fun s hs ↦ ?_⟩
  funext a
  simp only [line, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hcd a s hs]
  ring

/-- In flat space-time a path of free fall that cannot be continued runs for all times. -/
theorem minkowski_inextendible_univ {γ : ℝ → Coords 4} {J : Set ℝ}
    (h : IsInextendibleFreeFall minkowski γ J) : J = univ := by
  obtain ⟨p, v, hpv⟩ := minkowski_path_eq_line h.1
  exact (h.2 (line p v) univ (line_isFreeFallPath p v isOpen_univ ordConnected_univ)
    (subset_univ J) hpv).symm

/-- **Flat space-time meets the completeness condition,** whatever the three fields are. -/
theorem minkowski_freeFallComplete (ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) (Coords 4)) :
    FreeFallComplete minkowski ξ := by
  intro γ J h
  have hJ := minkowski_inextendible_univ h
  subst hJ
  exact ⟨fun b hb ↦ (not_bddAbove_univ hb.bddAbove).elim,
    fun a ha ↦ (not_bddBelow_univ ha.bddBelow).elim⟩

/-! ## Orientation on coordinate space -/

/-- **Coordinate space is orientable.** -/
theorem coords_isOrientable (n : ℕ) : IsOrientable n (Coords n) := by
  have hmem : OpenPartialHomeomorph.refl (Coords n)
      ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords n) ∞ (Coords n) := by
    have := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, Coords n)) (n := ∞) (0 : Coords n)
    rwa [chartAt_self_eq] at this
  refine ⟨{OpenPartialHomeomorph.refl (Coords n)}, singleton_subset_iff.mpr hmem,
    fun x ↦ ⟨_, rfl, by simp⟩, ?_⟩
  rintro φ rfl ψ rfl y - -
  have e : (fun z ↦ (OpenPartialHomeomorph.refl (Coords n))
      ((OpenPartialHomeomorph.refl (Coords n)).symm z)) = fun z ↦ z := rfl
  rw [e, fderiv_fun_id]
  simp

/-- **Flat space-time can tell future from past:** the time direction itself. -/
theorem minkowski_isTimeOrientable : IsTimeOrientable minkowski := by
  refine ⟨fun _ ↦ (Pi.single 0 1 : Coords 4), ?_, fun x ↦ ?_⟩
  · have hc : Continuous (fun x : Coords 4 ↦ (x, (Pi.single 0 1 : Coords 4))) :=
      continuous_id.prodMk continuous_const
    exact (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, Coords 4)).symm.continuous.comp hc
  · change tableMeasure flatG x (Pi.single 0 1) (Pi.single 0 1) < 0
    rw [show tableMeasure flatG x (Pi.single 0 1) (Pi.single 0 1) = flatG 0 0 x from
      formOf_single_single _ 0 0]
    simp [flatG]

end Minkowski

/-! ## A ray of light falling into Schwarzschild's mass -/

section Ray

/-- Schwarzschild's length measure of mass `m` on coordinate space (labels `t`, `r`, `θ`, `φ`). -/
noncomputable abbrev schwMeasure (m : ℝ) : LengthMeasure 𝓘(ℝ, Coords 4) (Coords 4) :=
  flatMeasure (tableMeasure (roundG (schwA m) (schwB m)))

/-- **A ray of light falling straight into the mass,** outside the rim, on the equator. At the
parameter `s < -2m` it is at the distance `r = -s` and the time `t = s - 2m log (-s / 2m - 1)`:
the textbooks' ingoing radial light ray (`t + r + 2m log (r / 2m - 1)` stays the same), with the
distance itself, up to its sign, as the path's own parameter. -/
noncomputable def inRay (m s : ℝ) : Coords 4 :=
  ![s - 2 * m * log (-s / (2 * m) - 1), -s, π / 2, 0]

variable {m : ℝ}

theorem inRay_arg_pos (hm : 0 < m) {s : ℝ} (hs : s < -2 * m) : 0 < -s / (2 * m) - 1 := by
  rw [sub_pos, lt_div_iff₀ (by positivity)]
  linarith

theorem inRay_one (s : ℝ) : inRay m s 1 = -s := by simp [inRay]

theorem inRay_two (s : ℝ) : inRay m s 2 = π / 2 := by simp [inRay]

theorem hasDerivAt_inRay_zero (hm : 0 < m) {s : ℝ} (hs : s < -2 * m) :
    HasDerivAt (fun s ↦ inRay m s 0) (s / (s + 2 * m)) s := by
  have hu : HasDerivAt (fun s : ℝ ↦ -s / (2 * m) - 1) (-1 / (2 * m)) s :=
    ((hasDerivAt_id s).neg.div_const (2 * m)).sub_const 1
  have hl := hu.log (inRay_arg_pos hm hs).ne'
  have h : HasDerivAt (fun s : ℝ ↦ s - 2 * m * log (-s / (2 * m) - 1))
      (1 - 2 * m * (-1 / (2 * m) / (-s / (2 * m) - 1))) s :=
    (hasDerivAt_id s).sub (hl.const_mul (2 * m))
  have e : (fun s ↦ inRay m s 0) = fun s : ℝ ↦ s - 2 * m * log (-s / (2 * m) - 1) := by
    funext s
    simp [inRay]
  rw [e]
  convert h using 1
  have h1 : s + 2 * m ≠ 0 := by linarith
  have h3 : -s - 2 * m ≠ 0 := by linarith
  have hm0 : m ≠ 0 := hm.ne'
  field_simp
  ring

theorem deriv_deriv_inRay_zero (hm : 0 < m) {s : ℝ} (hs : s < -2 * m) :
    deriv (deriv fun s ↦ inRay m s 0) s = 2 * m / (s + 2 * m) ^ 2 := by
  have hev : (deriv fun s ↦ inRay m s 0) =ᶠ[𝓝 s] fun s ↦ s / (s + 2 * m) := by
    filter_upwards [Iio_mem_nhds hs] with s' hs'
    exact (hasDerivAt_inRay_zero hm hs').deriv
  rw [hev.deriv_eq]
  have h1 : s + 2 * m ≠ 0 := by linarith
  have h : HasDerivAt (fun x : ℝ ↦ x / (x + 2 * m))
      ((1 * (s + 2 * m) - s * 1) / (s + 2 * m) ^ 2) s :=
    (hasDerivAt_id s).div ((hasDerivAt_id s).add_const (2 * m)) h1
  rw [h.deriv]
  ring

theorem deriv_inRay_one (s : ℝ) : deriv (fun s ↦ inRay m s 1) s = -1 := by
  have e : (fun s ↦ inRay m s 1) = fun s : ℝ ↦ -s := funext fun s ↦ inRay_one s
  rw [e]
  simp

theorem deriv_deriv_inRay_one (s : ℝ) : deriv (deriv fun s ↦ inRay m s 1) s = 0 := by
  have e : (deriv fun s ↦ inRay m s 1) = fun _ ↦ -1 := funext fun s ↦ deriv_inRay_one s
  rw [e]
  simp

theorem deriv_inRay_two (s : ℝ) : deriv (fun s ↦ inRay m s 2) s = 0 := by simp [inRay]

theorem deriv_deriv_inRay_two (s : ℝ) : deriv (deriv fun s ↦ inRay m s 2) s = 0 := by
  simp [inRay]

theorem deriv_inRay_three (s : ℝ) : deriv (fun s ↦ inRay m s 3) s = 0 := by simp [inRay]

theorem deriv_deriv_inRay_three (s : ℝ) : deriv (deriv fun s ↦ inRay m s 3) s = 0 := by
  simp [inRay]

/-- Along the ray, the connection of Schwarzschild's table read with Lean's inverse matrix is the
connection of the round table written out (`roundΓ`). -/
theorem christoffel_schw_inRay (hm : 0 < m) {s : ℝ} (hs : s < -2 * m) (a b c : Fin 4) :
    christoffel (selfTable (schwMeasure m)) (selfTableInv (schwMeasure m)) a b c (inRay m s)
      = roundΓ (schwA m) (schwB m) a b c (inRay m s) := by
  have hreg : Regular (schwA m) (schwB m) (inRay m s) :=
    schwarzschild_regular m (by rw [inRay_one]; linarith) (by rw [inRay_one]; linarith)
      (by rw [inRay_two, sin_pi_div_two]; norm_num)
  rw [christoffel_congr_inv (ginv' := roundGinv (schwA m) (schwB m))
    (fun a b ↦ selfTableInv_table_at (roundG_mul_roundGinv hreg) a b), selfTable_table,
    christoffel_round]

/-- **The falling ray obeys the equation of free fall** at every parameter `s < -2m`. -/
theorem inRay_isFreeFallAt (hm : 0 < m) {s : ℝ} (hs : s < -2 * m) :
    IsFreeFallAt (christoffel (selfTable (schwMeasure m)) (selfTableInv (schwMeasure m)))
      (inRay m) s := by
  rw [isFreeFallAt_congr (christoffel_schw_inRay hm hs)]
  have hr : -s ≠ 0 := by linarith
  have h1 : s + 2 * m ≠ 0 := by linarith
  have hs0 : s ≠ 0 := by linarith
  have hA : 1 - 2 * m / -s ≠ 0 := by
    rw [div_neg, sub_neg_eq_add]
    intro h0
    field_simp at h0
    apply h1
    linarith
  have dA := (hasDerivAt_schwA m hr).deriv
  have dB := (hasDerivAt_schwB m hr hA).deriv
  have d0 := (hasDerivAt_inRay_zero hm hs).deriv
  have dd0 := deriv_deriv_inRay_zero hm hs
  have h1' : m * 2 + s ≠ 0 := by linarith
  have h1'' : 2 * m + s ≠ 0 := by linarith
  have hm0 : m ≠ 0 := hm.ne'
  have e0 : freeFallExpr (roundΓ (schwA m) (schwB m)) (inRay m) s 0 = 0 := by
    have hk : (m * 2 + s)⁻¹ * (m * 2 + s) = 1 := inv_mul_cancel₀ h1'
    simp only [freeFallExpr, Fin.sum_univ_four, roundΓ_apply, d0, dd0, deriv_inRay_three,
      inRay_one, inRay_two]
    simp [rPart, θPart, pF, constOne, constZero, dA, schwA]
    field_simp
    linear_combination (-2 * m) * hk
  have e1 : freeFallExpr (roundΓ (schwA m) (schwB m)) (inRay m) s 1 = 0 := by
    simp only [freeFallExpr, Fin.sum_univ_four, roundΓ_apply, d0, deriv_inRay_three, inRay_one,
      inRay_two]
    simp [rPart, θPart, qF, rF, constOne, constZero, dA, dB, schwB]
    field_simp
    ring
  have e2 : freeFallExpr (roundΓ (schwA m) (schwB m)) (inRay m) s 2 = 0 := by
    simp only [freeFallExpr, Fin.sum_univ_four, roundΓ_apply, d0, deriv_inRay_three, inRay_one,
      inRay_two]
    simp [rPart, θPart, constOne, constZero]
  have e3 : freeFallExpr (roundΓ (schwA m) (schwB m)) (inRay m) s 3 = 0 := by
    simp only [freeFallExpr, Fin.sum_univ_four, roundΓ_apply, d0, deriv_deriv_inRay_three,
      deriv_inRay_three, inRay_one, inRay_two]
    simp [rPart, θPart, constOne, constZero]
  intro a
  fin_cases a
  exacts [e0, e1, e2, e3]

/-- **A ray of light falling into Schwarzschild's mass is a path of free fall,** on all of its
parameters outside the rim. -/
theorem inRay_isFreeFallPath (hm : 0 < m) :
    IsFreeFallPath (schwMeasure m) (inRay m) (Iio (-2 * m)) := by
  rw [isFreeFallPath_self_iff]
  refine ⟨isOpen_Iio, ordConnected_Iio, ?_, fun s hs ↦ inRay_isFreeFallAt hm hs⟩
  have c0 : ContDiffOn ℝ ∞ (fun s ↦ inRay m s 0) (Iio (-2 * m)) := by
    have e : (fun s ↦ inRay m s 0) = fun s : ℝ ↦ s - 2 * m * log (-s / (2 * m) - 1) := by
      funext s
      simp [inRay]
    rw [e]
    refine contDiffOn_id.sub (contDiffOn_const.mul (ContDiffOn.log ?_ ?_))
    · exact ((contDiffOn_id.neg.div_const _).sub contDiffOn_const)
    · exact fun s hs ↦ (inRay_arg_pos hm hs).ne'
  have c1 : ContDiffOn ℝ ∞ (fun s ↦ inRay m s 1) (Iio (-2 * m)) := by
    have e : (fun s ↦ inRay m s 1) = fun s : ℝ ↦ -s := funext fun s ↦ inRay_one s
    rw [e]
    exact contDiffOn_id.neg
  have c2 : ContDiffOn ℝ ∞ (fun s ↦ inRay m s 2) (Iio (-2 * m)) := by
    simp only [inRay_two]
    exact contDiffOn_const
  have c3 : ContDiffOn ℝ ∞ (fun s ↦ inRay m s 3) (Iio (-2 * m)) := by
    simp only [inRay]
    exact contDiffOn_const
  refine contDiffOn_pi.mpr fun i ↦ ?_
  fin_cases i
  exacts [c0, c1, c2, c3]

/-- The same ray, run at a clock that is not its own: at the time `u > 0` it is where `inRay` is
at the parameter `-2m - u²`. -/
noncomputable def inRaySlow (m u : ℝ) : Coords 4 := inRay m (-2 * m - u ^ 2)

/-- **Run at a clock that is not its own, the ray does not obey the equation of free fall:** the
equation fixes the clock along a path (the path's own time, up to a shift and a steady rate). -/
theorem inRaySlow_not_falls (hm : 0 < m) {u : ℝ} (hu : 0 < u) :
    ¬ IsFreeFallAt (christoffel (selfTable (schwMeasure m)) (selfTableInv (schwMeasure m)))
      (inRaySlow m) u := by
  have hs : -2 * m - u ^ 2 < -2 * m := by nlinarith
  rw [isFreeFallAt_congr (γ := inRaySlow m) (τ := u) (christoffel_schw_inRay hm hs)]
  intro h
  have hσ : HasDerivAt (fun u : ℝ ↦ -2 * m - u ^ 2) (-(2 * u)) u := by
    have := (hasDerivAt_pow 2 u).const_sub (-2 * m)
    convert this using 1
    norm_num
  have hc : HasDerivAt (fun u ↦ inRaySlow m u 0)
      ((-2 * m - u ^ 2) / (-2 * m - u ^ 2 + 2 * m) * -(2 * u)) u :=
    HasDerivAt.comp (h := fun u : ℝ ↦ -2 * m - u ^ 2) u (hasDerivAt_inRay_zero hm hs) hσ
  have d0 := hc.deriv
  have e1 : (fun u ↦ inRaySlow m u 1) = fun u : ℝ ↦ 2 * m + u ^ 2 := by
    funext u
    simp only [inRaySlow, inRay_one]
    ring
  have d1 : deriv (fun u ↦ inRaySlow m u 1) u = 2 * u := by
    rw [e1]
    simp
  have dd1 : deriv (deriv fun u ↦ inRaySlow m u 1) u = 2 := by
    have e : (deriv fun u ↦ inRaySlow m u 1) = fun u ↦ 2 * u := by
      funext u
      rw [e1]
      simp
    rw [e]
    simp
  have d2 : deriv (fun u ↦ inRaySlow m u 2) u = 0 := by simp [inRaySlow, inRay]
  have d3 : deriv (fun u ↦ inRaySlow m u 3) u = 0 := by simp [inRaySlow, inRay]
  have p1 : inRaySlow m u 1 = 2 * m + u ^ 2 := congrFun e1 u
  have p2 : inRaySlow m u 2 = π / 2 := inRay_two _
  have hr : 2 * m + u ^ 2 ≠ 0 := by positivity
  have hu0 : u ≠ 0 := hu.ne'
  have hA : 1 - 2 * m / (2 * m + u ^ 2) ≠ 0 := by
    intro h0
    field_simp at h0
    nlinarith
  have dA := (hasDerivAt_schwA m hr).deriv
  have dB := (hasDerivAt_schwB m hr hA).deriv
  have key : freeFallExpr (roundΓ (schwA m) (schwB m)) (inRaySlow m) u 1 = 2 := by
    have hv : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0
    simp only [freeFallExpr, Fin.sum_univ_four, roundΓ_apply, d0, d1, dd1, d2, d3, p1, p2]
    simp [rPart, θPart, qF, rF, constOne, constZero, dA, dB, schwB]
    field_simp
    linear_combination (4 * m * u ^ 6 + 16 * m ^ 2 * u ^ 4 + 16 * m ^ 3 * u ^ 2)
      * ((u * u⁻¹) ^ 3 + (u * u⁻¹) ^ 2 + u * u⁻¹ + 1) * hv
  have h1 := h 1
  rw [key] at h1
  norm_num at h1

/-- So on no interval of positive times is the slowly run ray a path of free fall. -/
theorem inRaySlow_not_isFreeFallPath (hm : 0 < m) {J : Set ℝ} (hJ : J.Nonempty)
    (hJ0 : J ⊆ Ioi 0) : ¬ IsFreeFallPath (schwMeasure m) (inRaySlow m) J := by
  intro h
  obtain ⟨u, hu⟩ := hJ
  exact inRaySlow_not_falls hm (hJ0 hu) (((isFreeFallPath_self_iff _ _ _).mp h).2.2.2 u hu)

/-- **A ray of light falling to the centre inside the rim.** At the parameter `s` between `-2m`
and `0` it is at the distance `r = -s` and the time `t = s - 2m log (1 + s / 2m)`, on the equator.
It reaches the centre at the parameter `0`, a finite time. -/
noncomputable def inRayIn (m s : ℝ) : Coords 4 :=
  ![s - 2 * m * log (1 + s / (2 * m)), -s, π / 2, 0]

theorem inRayIn_arg_pos (hm : 0 < m) {s : ℝ} (hs : -2 * m < s) : 0 < 1 + s / (2 * m) := by
  have h : -1 < s / (2 * m) := by
    rw [lt_div_iff₀ (by positivity)]
    linarith
  linarith

theorem inRayIn_one (s : ℝ) : inRayIn m s 1 = -s := by simp [inRayIn]

theorem inRayIn_two (s : ℝ) : inRayIn m s 2 = π / 2 := by simp [inRayIn]

theorem hasDerivAt_inRayIn_zero (hm : 0 < m) {s : ℝ} (hs : -2 * m < s) :
    HasDerivAt (fun s ↦ inRayIn m s 0) (s / (s + 2 * m)) s := by
  have hu : HasDerivAt (fun s : ℝ ↦ 1 + s / (2 * m)) (1 / (2 * m)) s :=
    ((hasDerivAt_id s).div_const (2 * m)).const_add 1
  have hl := hu.log (inRayIn_arg_pos hm hs).ne'
  have h : HasDerivAt (fun s : ℝ ↦ s - 2 * m * log (1 + s / (2 * m)))
      (1 - 2 * m * (1 / (2 * m) / (1 + s / (2 * m)))) s :=
    (hasDerivAt_id s).sub (hl.const_mul (2 * m))
  have e : (fun s ↦ inRayIn m s 0) = fun s : ℝ ↦ s - 2 * m * log (1 + s / (2 * m)) := by
    funext s
    simp [inRayIn]
  rw [e]
  convert h using 1
  have h1 : s + 2 * m ≠ 0 := by linarith
  have hk : (s + m * 2)⁻¹ * (s + m * 2) = 1 := inv_mul_cancel₀ (by linarith)
  have hm0 : m ≠ 0 := hm.ne'
  field_simp
  linear_combination (2 * m) * hk

theorem deriv_deriv_inRayIn_zero (hm : 0 < m) {s : ℝ} (hs : -2 * m < s) :
    deriv (deriv fun s ↦ inRayIn m s 0) s = 2 * m / (s + 2 * m) ^ 2 := by
  have hev : (deriv fun s ↦ inRayIn m s 0) =ᶠ[𝓝 s] fun s ↦ s / (s + 2 * m) := by
    filter_upwards [Ioi_mem_nhds hs] with s' hs'
    exact (hasDerivAt_inRayIn_zero hm hs').deriv
  rw [hev.deriv_eq]
  have h1 : s + 2 * m ≠ 0 := by linarith
  have h : HasDerivAt (fun x : ℝ ↦ x / (x + 2 * m))
      ((1 * (s + 2 * m) - s * 1) / (s + 2 * m) ^ 2) s :=
    (hasDerivAt_id s).div ((hasDerivAt_id s).add_const (2 * m)) h1
  rw [h.deriv]
  ring

theorem deriv_inRayIn_three (s : ℝ) : deriv (fun s ↦ inRayIn m s 3) s = 0 := by simp [inRayIn]

theorem deriv_deriv_inRayIn_three (s : ℝ) : deriv (deriv fun s ↦ inRayIn m s 3) s = 0 := by
  simp [inRayIn]

theorem christoffel_schw_inRayIn {s : ℝ} (hs : -2 * m < s) (hs0 : s < 0)
    (a b c : Fin 4) :
    christoffel (selfTable (schwMeasure m)) (selfTableInv (schwMeasure m)) a b c (inRayIn m s)
      = roundΓ (schwA m) (schwB m) a b c (inRayIn m s) := by
  have hreg : Regular (schwA m) (schwB m) (inRayIn m s) :=
    schwarzschild_regular_inside m (by rw [inRayIn_one]; linarith)
      (by rw [inRayIn_one]; linarith) (by rw [inRayIn_two, sin_pi_div_two]; norm_num)
  rw [christoffel_congr_inv (ginv' := roundGinv (schwA m) (schwB m))
    (fun a b ↦ selfTableInv_table_at (roundG_mul_roundGinv hreg) a b), selfTable_table,
    christoffel_round]

/-- **The ray inside the rim obeys the equation of free fall** at every parameter between `-2m`
and `0`. -/
theorem inRayIn_isFreeFallAt (hm : 0 < m) {s : ℝ} (hs : -2 * m < s) (hs0 : s < 0) :
    IsFreeFallAt (christoffel (selfTable (schwMeasure m)) (selfTableInv (schwMeasure m)))
      (inRayIn m) s := by
  rw [isFreeFallAt_congr (christoffel_schw_inRayIn hs hs0)]
  have hr : -s ≠ 0 := by linarith
  have h1 : s + 2 * m ≠ 0 := by linarith
  have hs00 : s ≠ 0 := hs0.ne
  have hA : 1 - 2 * m / -s ≠ 0 := by
    rw [div_neg, sub_neg_eq_add]
    intro h0
    field_simp at h0
    apply h1
    linarith
  have dA := (hasDerivAt_schwA m hr).deriv
  have dB := (hasDerivAt_schwB m hr hA).deriv
  have d0 := (hasDerivAt_inRayIn_zero hm hs).deriv
  have dd0 := deriv_deriv_inRayIn_zero hm hs
  have h1' : m * 2 + s ≠ 0 := by linarith
  have h1'' : 2 * m + s ≠ 0 := by linarith
  have hm0 : m ≠ 0 := hm.ne'
  have e0 : freeFallExpr (roundΓ (schwA m) (schwB m)) (inRayIn m) s 0 = 0 := by
    have hk : (m * 2 + s)⁻¹ * (m * 2 + s) = 1 := inv_mul_cancel₀ h1'
    simp only [freeFallExpr, Fin.sum_univ_four, roundΓ_apply, d0, dd0, deriv_inRayIn_three,
      inRayIn_one, inRayIn_two]
    simp [rPart, θPart, pF, constOne, constZero, dA, schwA]
    field_simp
    linear_combination (-2 * m) * hk
  have e1 : freeFallExpr (roundΓ (schwA m) (schwB m)) (inRayIn m) s 1 = 0 := by
    simp only [freeFallExpr, Fin.sum_univ_four, roundΓ_apply, d0, deriv_inRayIn_three,
      inRayIn_one, inRayIn_two]
    simp [rPart, θPart, qF, rF, constOne, constZero, dA, dB, schwB]
    field_simp
    ring
  have e2 : freeFallExpr (roundΓ (schwA m) (schwB m)) (inRayIn m) s 2 = 0 := by
    simp only [freeFallExpr, Fin.sum_univ_four, roundΓ_apply, d0, deriv_inRayIn_three,
      inRayIn_one, inRayIn_two]
    simp [rPart, θPart, constOne, constZero]
  have e3 : freeFallExpr (roundΓ (schwA m) (schwB m)) (inRayIn m) s 3 = 0 := by
    simp only [freeFallExpr, Fin.sum_univ_four, roundΓ_apply, d0, deriv_deriv_inRayIn_three,
      deriv_inRayIn_three, inRayIn_one, inRayIn_two]
    simp [rPart, θPart, constOne, constZero]
  intro a
  fin_cases a
  exacts [e0, e1, e2, e3]

/-- **A ray of light inside the rim is a path of free fall** on the parameters between `-2m` and
`0`. -/
theorem inRayIn_isFreeFallPath (hm : 0 < m) :
    IsFreeFallPath (schwMeasure m) (inRayIn m) (Ioo (-2 * m) 0) := by
  rw [isFreeFallPath_self_iff]
  refine ⟨isOpen_Ioo, ordConnected_Ioo, ?_, fun s hs ↦ inRayIn_isFreeFallAt hm hs.1 hs.2⟩
  have c0 : ContDiffOn ℝ ∞ (fun s ↦ inRayIn m s 0) (Ioo (-2 * m) 0) := by
    have e : (fun s ↦ inRayIn m s 0) = fun s : ℝ ↦ s - 2 * m * log (1 + s / (2 * m)) := by
      funext s
      simp [inRayIn]
    rw [e]
    refine contDiffOn_id.sub (contDiffOn_const.mul (ContDiffOn.log ?_ ?_))
    · exact contDiffOn_const.add (contDiffOn_id.div_const _)
    · exact fun s hs ↦ (inRayIn_arg_pos hm hs.1).ne'
  have c1 : ContDiffOn ℝ ∞ (fun s ↦ inRayIn m s 1) (Ioo (-2 * m) 0) := by
    have e : (fun s ↦ inRayIn m s 1) = fun s : ℝ ↦ -s := funext fun s ↦ inRayIn_one s
    rw [e]
    exact contDiffOn_id.neg
  have c2 : ContDiffOn ℝ ∞ (fun s ↦ inRayIn m s 2) (Ioo (-2 * m) 0) := by
    simp only [inRayIn_two]
    exact contDiffOn_const
  have c3 : ContDiffOn ℝ ∞ (fun s ↦ inRayIn m s 3) (Ioo (-2 * m) 0) := by
    simp only [inRayIn]
    exact contDiffOn_const
  refine contDiffOn_pi.mpr fun i ↦ ?_
  fin_cases i
  exacts [c0, c1, c2, c3]

/-- **Along that ray the spheres shrink to zero** as it reaches the centre at the parameter `0`,
as the second case of the completeness condition allows. -/
theorem inRayIn_sizeSq :
    Tendsto (fun s ↦ sizeSq (schwMeasure m) turns (inRayIn m s)) (𝓝[<] 0) (𝓝 0) := by
  have e : ∀ s, sizeSq (schwMeasure m) turns (inRayIn m s) = s ^ 2 := fun s ↦ by
    rw [schwarzschild_sizeSq m (by rw [inRayIn_two, sin_pi_div_two]; norm_num), inRayIn_one]
    ring
  simp only [e]
  have h : Tendsto (fun s : ℝ ↦ s ^ 2) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_pow 2).tendsto (0 : ℝ)
  exact h.mono_left nhdsWithin_le_nhds

end Ray

/-! ## Kruskal's whole space-time: the wrap charts and the four folds -/

section Folds

theorem kruskalRegion_open : IsOpen kruskalRegion := by
  have h1 : IsOpen {x : Coords 4 | -1 < x 1 ^ 2 - x 0 ^ 2} :=
    isOpen_lt continuous_const (by fun_prop)
  have h2 : IsOpen {x : Coords 4 | sin (x 2) ≠ 0} :=
    isOpen_ne_fun (by fun_prop) continuous_const
  exact h1.inter h2

/-- **Every wrap chart keeps lengths:** it is a length-keeping map from Kruskal's table into
Kruskal's whole space-time, on all of Kruskal's region. -/
theorem kruskalChart_isKruskalMapOn (m : ℝ) {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R.transpose * R = 1) :
    IsKruskalMapOn m (flatMeasure (tableMeasure (kruskalG m))) (kruskalChart R) kruskalRegion :=
  (kruskalWrap_isKruskalMapOn m kruskalRegion_open fun _ hx ↦ hx.1).sym (by simp) hR

/-- A mirror of ordinary space (Householder's) that takes the point `(1, 0, 0)` of the sphere to
the point `y`; the identity if `y` is that point. -/
noncomputable def turnTo (y : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  if y 0 = 1 then 1 else
    !![y 0, y 1, y 2;
      y 1, 1 - y 1 ^ 2 * (1 - y 0)⁻¹, -(y 1 * y 2 * (1 - y 0)⁻¹);
      y 2, -(y 1 * y 2 * (1 - y 0)⁻¹), 1 - y 2 ^ 2 * (1 - y 0)⁻¹]

theorem turnTo_orthogonal {y : Fin 3 → ℝ} (hy : y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 = 1) :
    (turnTo y).transpose * turnTo y = 1 := by
  unfold turnTo
  split_ifs with h
  · simp
  · have hc : 1 - y 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    set k := (1 - y 0)⁻¹ with hk
    have hk1 : k * (1 - y 0) = 1 := inv_mul_cancel₀ hc
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    · linear_combination hy
    · linear_combination (-(y 1 * k)) * hy - y 1 * (1 + y 0) * hk1
    · linear_combination (-(y 2 * k)) * hy - y 2 * (1 + y 0) * hk1
    · linear_combination (-(y 1 * k)) * hy - y 1 * (1 + y 0) * hk1
    · linear_combination y 1 ^ 2 * k ^ 2 * hy + y 1 ^ 2 * (k * (1 + y 0) - 1) * hk1
    · linear_combination y 1 * y 2 * k ^ 2 * hy + y 1 * y 2 * (k * (1 + y 0) - 1) * hk1
    · linear_combination (-(y 2 * k)) * hy - y 2 * (1 + y 0) * hk1
    · linear_combination y 1 * y 2 * k ^ 2 * hy + y 1 * y 2 * (k * (1 + y 0) - 1) * hk1
    · linear_combination y 2 ^ 2 * k ^ 2 * hy + y 2 ^ 2 * (k * (1 + y 0) - 1) * hk1

theorem turnTo_col {y : Fin 3 → ℝ} (hy : y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 = 1) :
    turnTo y 0 0 = y 0 ∧ turnTo y 1 0 = y 1 ∧ turnTo y 2 0 = y 2 := by
  unfold turnTo
  split_ifs with h
  · have h12 : y 1 ^ 2 + y 2 ^ 2 = 0 := by rw [h] at hy; linarith
    have h1 : y 1 = 0 := by nlinarith [sq_nonneg (y 1), sq_nonneg (y 2)]
    have h2 : y 2 = 0 := by nlinarith [sq_nonneg (y 1), sq_nonneg (y 2)]
    simp [h, h1, h2]
  · simp

/-- **The wrap charts reach every point of Kruskal's whole space-time,** the poles of the sphere
included: every point is the image of a point of Kruskal's region under the wrap chart turned by
some turn or mirror `R`. -/
theorem kruskalChart_covers {p : Coords 5} (hp : p ∈ kruskalSpace) :
    ∃ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 ∧
      ∃ x ∈ kruskalRegion, kruskalChart R x = p := by
  have hy : (![p 2, p 3, p 4] : Fin 3 → ℝ) 0 ^ 2 + ![p 2, p 3, p 4] 1 ^ 2
      + ![p 2, p 3, p 4] 2 ^ 2 = 1 := by simpa using hp.2
  obtain ⟨c0, c1, c2⟩ := turnTo_col hy
  have c0' : turnTo ![p 2, p 3, p 4] 0 0 = p 2 := c0
  have c1' : turnTo ![p 2, p 3, p 4] 1 0 = p 3 := c1
  have c2' : turnTo ![p 2, p 3, p 4] 2 0 = p 4 := c2
  refine ⟨turnTo ![p 2, p 3, p 4], turnTo_orthogonal hy, ![p 0, p 1, π / 2, 0], ⟨?_, ?_⟩, ?_⟩
  · simpa using hp.1
  · simp
  · funext i
    fin_cases i <;> simp [kruskalChart, kruskalSym, kruskalWrap, c0', c1', c2']

theorem neg_one_orthogonal : (-1 : Matrix (Fin 3) (Fin 3) ℝ).transpose * (-1) = 1 := by simp

theorem kruskalFolds_lightSign {L : Matrix (Fin 2) (Fin 2) ℝ} (hL : L ∈ kruskalFolds) :
    L.transpose * lightSign2 * L = lightSign2 := by
  simp only [kruskalFolds, mem_insert_iff, mem_singleton_iff] at hL
  rcases hL with rfl | rfl | rfl | rfl <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [lightSign2, Matrix.mul_apply, Matrix.diagonal_apply])

/-- **Each fold sends Kruskal's whole space-time to itself.** -/
theorem kruskalFold_mem {L : Matrix (Fin 2) (Fin 2) ℝ} (hL : L ∈ kruskalFolds) {p : Coords 5}
    (hp : p ∈ kruskalSpace) : kruskalFold L p ∈ kruskalSpace :=
  kruskalSym_mem (kruskalFolds_lightSign hL) neg_one_orthogonal hp

/-- **Each fold keeps Kruskal's lengths.** -/
theorem kruskalFold_measure (m : ℝ) {L : Matrix (Fin 2) (Fin 2) ℝ} (hL : L ∈ kruskalFolds)
    (p u w : Coords 5) :
    tableMeasure (kruskalWhole m) (kruskalFold L p) (kruskalFold L u) (kruskalFold L w)
      = tableMeasure (kruskalWhole m) p u w :=
  kruskalSym_measure m (kruskalFolds_lightSign hL) neg_one_orthogonal p u w

/-- **Each fold undoes itself.** -/
theorem kruskalFold_fold {L : Matrix (Fin 2) (Fin 2) ℝ} (hL : L ∈ kruskalFolds) (p : Coords 5) :
    kruskalFold L (kruskalFold L p) = p := by
  simp only [kruskalFolds, mem_insert_iff, mem_singleton_iff] at hL
  rcases hL with rfl | rfl | rfl | rfl <;>
    (funext i; fin_cases i <;> simp [kruskalFold, kruskalSym])

/-- **No fold leaves a point of Kruskal's whole space-time where it is:** every fold sends the
point `y` of the sphere to the opposite point. -/
theorem kruskalFold_ne (L : Matrix (Fin 2) (Fin 2) ℝ) {p : Coords 5} (hp : p ∈ kruskalSpace) :
    kruskalFold L p ≠ p := by
  intro h
  have e2 : kruskalFold L p 2 = -p 2 := by simp [kruskalFold, kruskalSym]
  have e3 : kruskalFold L p 3 = -p 3 := by simp [kruskalFold, kruskalSym]
  have e4 : kruskalFold L p 4 = -p 4 := by simp [kruskalFold, kruskalSym]
  have h2 : p 2 = 0 := by
    have := congrFun h 2
    rw [e2] at this
    linarith
  have h3 : p 3 = 0 := by
    have := congrFun h 3
    rw [e3] at this
    linarith
  have h4 : p 4 = 0 := by
    have := congrFun h 4
    rw [e4] at this
    linarith
  have h5 : p 2 ^ 2 + p 3 ^ 2 + p 4 ^ 2 = 1 := hp.2
  rw [h2, h3, h4] at h5
  norm_num at h5

end Folds

end GravityInLean.Curved
