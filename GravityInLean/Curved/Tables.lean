/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Curved.Flat
public import GravityInLean.NewCoordinates
public import GravityInLean.Symmetry

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Tables of functions, read as objects on a curved space

Everywhere else in this project a length measure is a table of functions of the coordinates, and
curvature, the connection and symmetry are formulas for the entries of such tables
(`Curvature.lean`, `Symmetry.lean`). This file reads a table as a length measure on flat
coordinate space in the sense of `Basic.lean`, and shows that the two languages agree:

* `isConnectionOf_table`: the textbooks' formula for the connection (`christoffel`) gives the
  connection that belongs to the length measure, in the sense of `Basic.lean`.
* `ricciAt_table`: the curvature of `Basic.lean`, for that connection, is the coordinate formula
  `ricci` of `Curvature.lean`.
* `leavesUnchangedAt_table_iff`: "moving along a field leaves the length measure unchanged" in
  the sense of `Basic.lean` is the coordinate formula `LeavesUnchangedAt` of `Symmetry.lean`.
* `mlieBracket_fieldOf`: the bracket of two fields of arrows, in coordinates.

So every result this project has proved in coordinates is a result about the notions of
`Basic.lean`, on the part of space-time those coordinates cover. `KnownAnswers.lean` uses this for
a sphere, for de Sitter's space-time and for Schwarzschild's.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Filter Topology

open scoped Manifold ContDiff

variable {n : ℕ}

/-! ## A table of numbers as a two-slot function -/

/-- Reading off one coordinate of a step, as a linear function. -/
noncomputable def coordL (a : Fin n) : Coords n →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) a

@[simp] theorem coordL_apply (a : Fin n) (v : Coords n) : coordL a v = v a := rfl

/-- The basic two-slot function for the entry `(a, b)`: it multiplies the `a`-part of its first
step by the `b`-part of its second. -/
noncomputable def unitForm (p : Fin n × Fin n) : Coords n →L[ℝ] Coords n →L[ℝ] ℝ :=
  (coordL p.1).smulRight (coordL p.2)

@[simp] theorem unitForm_apply (p : Fin n × Fin n) (v w : Coords n) :
    unitForm p v w = v p.1 * w p.2 := by
  simp [unitForm]

/-- The two-slot function that a table of numbers describes:
`(v, w) ↦ ∑ a b, T a b * v a * w b`. -/
noncomputable def formOf (T : Fin n → Fin n → ℝ) : Coords n →L[ℝ] Coords n →L[ℝ] ℝ :=
  ∑ p : Fin n × Fin n, T p.1 p.2 • unitForm p

theorem formOf_apply (T : Fin n → Fin n → ℝ) (v w : Coords n) :
    formOf T v w = ∑ a, ∑ b, T a b * v a * w b := by
  simp only [formOf, sum_apply, smul_apply, unitForm_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring

theorem formOf_single_left (T : Fin n → Fin n → ℝ) (a : Fin n) (w : Coords n) :
    formOf T (Pi.single a 1) w = ∑ b, T a b * w b := by
  rw [formOf_apply, Finset.sum_eq_single a]
  · simp
  · intro a' _ h
    simp [Pi.single_eq_of_ne h]
  · simp

theorem formOf_single_right (T : Fin n → Fin n → ℝ) (v : Coords n) (b : Fin n) :
    formOf T v (Pi.single b 1) = ∑ a, T a b * v a := by
  rw [formOf_apply]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_eq_single b]
  · simp
  · intro b' _ h
    simp [Pi.single_eq_of_ne h]
  · simp

theorem formOf_single_single (T : Fin n → Fin n → ℝ) (a b : Fin n) :
    formOf T (Pi.single a 1) (Pi.single b 1) = T a b := by
  rw [formOf_single_left, Finset.sum_eq_single b]
  · simp
  · intro b' _ h
    simp [Pi.single_eq_of_ne h]
  · simp

/-- The basic correction for the entry `(a, b, c)`. -/
noncomputable def unitCorr (p : Fin n × Fin n × Fin n) : Coords n →L[ℝ] Coords n →L[ℝ] Coords n :=
  (coordL p.2.2).smulRight ((coordL p.2.1).smulRight (Pi.single p.1 (1 : ℝ) : Coords n))

/-- The correction of a connection that a table of numbers `T a b c` describes: for the arrow `z`
and the step `v` it gives the arrow with the parts `∑ b c, T a b c * v b * z c`. -/
noncomputable def corrOf (T : Fin n → Fin n → Fin n → ℝ) :
    Coords n →L[ℝ] Coords n →L[ℝ] Coords n :=
  ∑ p : Fin n × Fin n × Fin n, T p.1 p.2.1 p.2.2 • unitCorr p

theorem corrOf_apply (T : Fin n → Fin n → Fin n → ℝ) (z v : Coords n) (a : Fin n) :
    corrOf T z v a = ∑ b, ∑ c, T a b c * v b * z c := by
  simp only [corrOf, unitCorr, sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    coordL_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun c _ ↦ by simp; ring
  · intro a' _ h
    simp [Pi.single_eq_of_ne' h]
  · simp

theorem corrOf_single_single (T : Fin n → Fin n → Fin n → ℝ) (c b a : Fin n) :
    corrOf T (Pi.single c 1) (Pi.single b 1) a = T a b c := by
  rw [corrOf_apply, Finset.sum_eq_single b]
  · rw [Finset.sum_eq_single c]
    · simp
    · intro c' _ h
      simp [Pi.single_eq_of_ne h]
    · simp
  · intro b' _ h
    simp [Pi.single_eq_of_ne h]
  · simp

/-! ## Tables of functions -/

/-- The length measure on flat coordinate space that a table of functions describes. -/
noncomputable def tableMeasure (g : Fin n → Fin n → Coords n → ℝ) :
    Coords n → Coords n →L[ℝ] Coords n →L[ℝ] ℝ :=
  fun x ↦ formOf fun a b ↦ g a b x

/-- The correction of a connection that a table of functions describes. -/
noncomputable def tableCorr (Γ : Fin n → Fin n → Fin n → Coords n → ℝ) :
    Coords n → Coords n →L[ℝ] Coords n →L[ℝ] Coords n :=
  fun x ↦ corrOf fun a b c ↦ Γ a b c x

/-- The field of arrows on flat coordinate space with the given parts. -/
noncomputable def fieldOf (ξ : Fin n → Coords n → ℝ) : Arrows 𝓘(ℝ, Coords n) (Coords n) :=
  arrows fun y k ↦ ξ k y

theorem plain_fieldOf (ξ : Fin n → Coords n → ℝ) : plain (fieldOf ξ) = fun y k ↦ ξ k y := rfl

section Slopes

variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The slope of a sum of fixed objects with changing weights. -/
theorem hasFDerivAt_sum_smul_const {c : ι → Coords n → ℝ} (B : ι → F) {x : Coords n}
    (hc : ∀ i, DifferentiableAt ℝ (c i) x) :
    HasFDerivAt (fun y ↦ ∑ i, c i y • B i) (∑ i, (fderiv ℝ (c i) x).smulRight (B i)) x :=
  HasFDerivAt.fun_sum fun i _ ↦ (hc i).hasFDerivAt.smul_const (B i)

end Slopes

/-- A slope along any step, from the slopes along the coordinates. -/
theorem fderiv_eq_sum_slope {f : Coords n → ℝ} {x : Coords n} (hf : DifferentiableAt ℝ f x)
    (v : Coords n) : fderiv ℝ f x v = ∑ m, v m * slope m f x := by
  rw [clm_apply_eq_sum]
  exact Finset.sum_congr rfl fun m _ ↦ by rw [slope_eq_fderiv hf]

section TableSlopes

variable {g : Fin n → Fin n → Coords n → ℝ} {Γ : Fin n → Fin n → Fin n → Coords n → ℝ}
  {x : Coords n}

theorem differentiableAt_tableMeasure (hg : ∀ a b, DifferentiableAt ℝ (g a b) x) :
    DifferentiableAt ℝ (tableMeasure g) x :=
  (hasFDerivAt_sum_smul_const (c := fun p : Fin n × Fin n ↦ g p.1 p.2) unitForm
    fun p ↦ hg p.1 p.2).differentiableAt

/-- The slope of the length measure of a table is the table of slopes. -/
theorem fderiv_tableMeasure (hg : ∀ a b, DifferentiableAt ℝ (g a b) x) (v : Coords n) :
    fderiv ℝ (tableMeasure g) x v = formOf fun a b ↦ fderiv ℝ (g a b) x v := by
  have h := (hasFDerivAt_sum_smul_const (c := fun p : Fin n × Fin n ↦ g p.1 p.2) unitForm
    fun p ↦ hg p.1 p.2).fderiv
  change fderiv ℝ (fun y ↦ ∑ p : Fin n × Fin n, g p.1 p.2 y • unitForm p) x v = _
  rw [h]
  simp [formOf]

theorem differentiableAt_tableCorr (hΓ : ∀ a b c, DifferentiableAt ℝ (Γ a b c) x) :
    DifferentiableAt ℝ (tableCorr Γ) x :=
  (hasFDerivAt_sum_smul_const (c := fun p : Fin n × Fin n × Fin n ↦ Γ p.1 p.2.1 p.2.2) unitCorr
    fun p ↦ hΓ p.1 p.2.1 p.2.2).differentiableAt

/-- The slope of the correction of a table is the table of slopes. -/
theorem fderiv_tableCorr (hΓ : ∀ a b c, DifferentiableAt ℝ (Γ a b c) x) (u : Coords n) :
    fderiv ℝ (tableCorr Γ) x u = corrOf fun a b c ↦ fderiv ℝ (Γ a b c) x u := by
  have h := (hasFDerivAt_sum_smul_const
    (c := fun p : Fin n × Fin n × Fin n ↦ Γ p.1 p.2.1 p.2.2) unitCorr
    fun p ↦ hΓ p.1 p.2.1 p.2.2).fderiv
  change fderiv ℝ (fun y ↦ ∑ p : Fin n × Fin n × Fin n, Γ p.1 p.2.1 p.2.2 y • unitCorr p) x u = _
  rw [h]
  simp [corrOf]

end TableSlopes

/-! ## The connection -/

section Connection

variable {g ginv : Fin n → Fin n → Coords n → ℝ} {x : Coords n}

/-- **The slopes of a length measure, written with its connection.** This is "the connection keeps
lengths", entry by entry, for the textbooks' formula for the connection. -/
theorem slope_eq_christoffel_sum (hsymm : ∀ᶠ y in 𝓝 x, ∀ a b, g a b y = g b a y)
    (hinv : ∀ a c, ∑ b, g a b x * ginv b c x = if a = c then 1 else 0) (m a b : Fin n) :
    slope m (g a b) x
      = ∑ d, g d b x * christoffel g ginv d m a x + ∑ d, g a d x * christoffel g ginv d m b x := by
  have hev : ∀ α β, g α β =ᶠ[𝓝 x] g β α := fun α β ↦ hsymm.mono fun w hw ↦ hw α β
  have hval : ∀ α β, g α β x = g β α x := fun α β ↦ (hev α β).eq_of_nhds
  -- Lowering the upper index of the connection undoes the inverse in its formula.
  have low : ∀ c m a : Fin n, ∑ d, g c d x * christoffel g ginv d m a x
      = 1 / 2 * (slope m (g c a) x + slope a (g c m) x - slope c (g m a) x) := by
    intro c m a
    simp only [christoffel]
    calc ∑ d, g c d x * (1 / 2 * ∑ e, ginv d e x
            * (slope m (g e a) x + slope a (g e m) x - slope e (g m a) x))
        = 1 / 2 * ∑ e, (∑ d, g c d x * ginv d e x)
            * (slope m (g e a) x + slope a (g e m) x - slope e (g m a) x) := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun e _ ↦ Finset.sum_congr rfl fun d _ ↦ by ring
      _ = 1 / 2 * (slope m (g c a) x + slope a (g c m) x - slope c (g m a) x) := by
          simp only [hinv, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
            ite_true]
  have e1 : ∑ d, g d b x * christoffel g ginv d m a x
      = ∑ d, g b d x * christoffel g ginv d m a x :=
    Finset.sum_congr rfl fun d _ ↦ by rw [hval d b]
  rw [e1, low b m a, low a m b, slope_congr (hev b a) m, slope_congr (hev b m) a,
    slope_congr (hev m a) b]
  ring

theorem corrOf_symm {T : Fin n → Fin n → Fin n → ℝ} (hT : ∀ a b c, T a b c = T a c b)
    (u v : Coords n) : corrOf T u v = corrOf T v u := by
  funext a
  rw [corrOf_apply, corrOf_apply, Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun b _ ↦ by rw [hT a b c]; ring

/-- The slopes of the length measure of a table are accounted for by the correction of its
connection, for any three steps. -/
theorem table_keepsLengths (hg : ∀ a b, DifferentiableAt ℝ (g a b) x)
    (hsymm : ∀ᶠ y in 𝓝 x, ∀ a b, g a b y = g b a y)
    (hinv : ∀ a c, ∑ b, g a b x * ginv b c x = if a = c then 1 else 0) (v y z : Coords n) :
    fderiv ℝ (tableMeasure g) x v y z
      = tableMeasure g x (tableCorr (christoffel g ginv) x y v) z
        + tableMeasure g x y (tableCorr (christoffel g ginv) x z v) := by
  refine eq_of_basis₃ (Pi.basisFun ℝ (Fin n)) (fderiv ℝ (tableMeasure g) x)
    (fun v y z ↦ tableMeasure g x (tableCorr (christoffel g ginv) x y v) z
      + tableMeasure g x y (tableCorr (christoffel g ginv) x z v)) ?_ ?_ ?_ ?_ v y z
  · intro y z
    exact ⟨fun a b ↦ by simp only [map_add, add_apply]; ring,
      fun c a ↦ by simp only [map_smul, smul_apply, smul_eq_mul]; ring⟩
  · intro v z
    exact ⟨fun a b ↦ by simp only [map_add, add_apply]; ring,
      fun c a ↦ by simp only [map_smul, smul_apply, smul_eq_mul]; ring⟩
  · intro v y
    exact ⟨fun a b ↦ by simp only [map_add, add_apply]; ring,
      fun c a ↦ by simp only [map_smul, smul_apply, smul_eq_mul]; ring⟩
  · intro i j k
    simp only [Pi.basisFun_apply]
    rw [fderiv_tableMeasure hg, formOf_single_single, ← slope_eq_fderiv (hg j k)]
    simp only [tableMeasure, tableCorr]
    rw [formOf_single_right, formOf_single_left]
    simp only [corrOf_single_single]
    exact slope_eq_christoffel_sum hsymm hinv i j k

/-- **The textbooks' formula gives the connection of the length measure.** Take a table of
functions that is symmetric, differentiable and has an inverse on an open region. Then "the plain
slope plus the Christoffel symbols" is the connection that belongs to the table's length measure,
in the sense of `Basic.lean`. -/
theorem isConnectionOf_table {s : Set (Coords n)} (hs : IsOpen s)
    (hg : ∀ x ∈ s, ∀ a b, DifferentiableAt ℝ (g a b) x)
    (hsymm : ∀ x ∈ s, ∀ a b, g a b x = g b a x)
    (hinv : ∀ x ∈ s, ∀ a c, ∑ b, g a b x * ginv b c x = if a = c then 1 else 0) :
    IsConnectionOf (flatMeasure (tableMeasure g))
      (flatTransport (tableCorr (christoffel g ginv))) s where
  isOpen := hs
  isConnection := (isCovariantDerivativeOn_flatTransport _).mono (Set.subset_univ s)
  noTwist := fun x hx X Y _ _ ↦ by
    have hnear : ∀ᶠ y in 𝓝 x, ∀ a b, g a b y = g b a y :=
      Filter.eventually_of_mem (hs.mem_nhds hx) fun y hy ↦ hsymm y hy
    exact flat_noTwist
      (fun u v ↦ corrOf_symm (fun a b c ↦ christoffel_symm hnear a b c) u v) X Y
  keepsLengths := fun x hx Y Z hY hZ v ↦ by
    have hnear : ∀ᶠ y in 𝓝 x, ∀ a b, g a b y = g b a y :=
      Filter.eventually_of_mem (hs.mem_nhds hx) fun y hy ↦ hsymm y hy
    exact flat_keepsLengths (differentiableAt_tableMeasure (hg x hx))
      (fun v y z ↦ table_keepsLengths (hg x hx) hnear (hinv x hx) v y z) Y Z hY hZ v

end Connection

/-! ## Curvature -/

section Curvature

variable {Γ : Fin n → Fin n → Fin n → Coords n → ℝ} {x : Coords n}

theorem sum_mul_single (F : Fin n → ℝ) (c : Fin n) :
    ∑ c', F c' * (Pi.single c (1 : ℝ) : Coords n) c' = F c := by
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ h
    simp [Pi.single_eq_of_ne h]
  · simp

theorem corrOf_single_right (T : Fin n → Fin n → Fin n → ℝ) (z : Coords n) (m a : Fin n) :
    corrOf T z (Pi.single m 1) a = ∑ c, T a m c * z c := by
  rw [corrOf_apply, Finset.sum_eq_single m]
  · simp
  · intro b' _ h
    simp [Pi.single_eq_of_ne h]
  · simp

/-- The full curvature of the connection of a table, on the basic steps: the textbooks' formula
for the Riemann tensor. -/
theorem curvatureMap_tableCorr_single (hΓ : ∀ a b c, DifferentiableAt ℝ (Γ a b c) x)
    (b c m a : Fin n) :
    curvatureMap (tableCorr Γ) x (Pi.single b 1) (Pi.single c 1) (Pi.single m 1) a
      = slope m (Γ a b c) x - slope b (Γ a m c) x + ∑ d, Γ a m d x * Γ d b c x
        - ∑ d, Γ a b d x * Γ d m c x := by
  rw [curvatureMap_apply, fderiv_tableCorr hΓ, fderiv_tableCorr hΓ]
  simp only [Pi.sub_apply, Pi.add_apply, tableCorr, corrOf_single_right, sum_mul_single]
  rw [slope_eq_fderiv (hΓ a b c), slope_eq_fderiv (hΓ a m c)]

/-- The trace of a linear function of coordinate vectors: the sum of its diagonal parts. -/
theorem trace_eq_sum_diag (L : Coords n →ₗ[ℝ] Coords n) :
    LinearMap.trace ℝ (Coords n) L = ∑ m, L (Pi.single m 1) m := by
  rw [← traceIn_eq_trace (Pi.basisFun ℝ (Fin n)) L]
  simp [traceIn]

/-- **The curvature of `Basic.lean` is the coordinate formula `ricci`.** For the connection that a
table of functions describes (differentiable, and symmetric in its two lower slots), the
curvature at a point in the sense of `Basic.lean`, applied to two steps, is the table `ricci`
of `Curvature.lean` applied to those steps. -/
theorem ricciAt_table (hΓ : ∀ a b c, DifferentiableAt ℝ (Γ a b c) x)
    (hsymm : ∀ᶠ y in 𝓝 x, ∀ a b c, Γ a b c y = Γ a c b y)
    (v w : TangentSpace 𝓘(ℝ, Coords n) x) :
    ricciAt (flatTransport (tableCorr Γ)) x v w = formOf (fun b c ↦ ricci Γ c b x) v w := by
  rw [ricciAt_flat (differentiableAt_tableCorr hΓ)]
  have hev : ∀ a b c, Γ a b c =ᶠ[𝓝 x] Γ a c b := fun a b c ↦ hsymm.mono fun y hy ↦ hy a b c
  have hval : ∀ a b c, Γ a b c x = Γ a c b x := fun a b c ↦ (hev a b c).eq_of_nhds
  symm
  refine eq_of_basis₂ (Pi.basisFun ℝ (Fin n)) (formOf fun b c ↦ ricci Γ c b x)
    (fun v w ↦ LinearMap.trace ℝ (Coords n)
      (curvatureMap (tableCorr Γ) x v w : Coords n →ₗ[ℝ] Coords n)) ?_ ?_ ?_ v w
  · intro w
    exact ⟨fun a b ↦ by rw [curvatureMap_add_left]; simp,
      fun c a ↦ by rw [curvatureMap_smul_left]; simp⟩
  · intro v
    exact ⟨fun a b ↦ by rw [curvatureMap_add_right]; simp,
      fun c a ↦ by rw [curvatureMap_smul_right]; simp⟩
  · intro b c
    simp only [Pi.basisFun_apply]
    rw [formOf_single_single, trace_eq_sum_diag]
    have t : ∀ m, curvatureMap (tableCorr Γ) x (Pi.single b 1) (Pi.single c 1) (Pi.single m 1) m
        = slope m (Γ m c b) x - slope b (Γ m c m) x + ∑ d, Γ m m d x * Γ d c b x
          - ∑ d, Γ m b d x * Γ d c m x := by
      intro m
      rw [curvatureMap_tableCorr_single hΓ, slope_congr (hev m b c) m,
        slope_congr (hev m m c) b]
      simp only [hval _ b c, hval _ m c]
    simp only [ContinuousLinearMap.coe_coe, t, ricci, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]

end Curvature

/-! ## Symmetry -/

section Symmetry

variable {g : Fin n → Fin n → Coords n → ℝ} {ξ : Fin n → Coords n → ℝ} {x : Coords n}

/-- The slope of a field of arrows given by its parts: part by part. -/
theorem fderiv_fieldOf_apply (hξ : ∀ k, DifferentiableAt ℝ (ξ k) x) (v : Coords n) (k : Fin n) :
    fderiv ℝ (plain (fieldOf ξ)) x v k = fderiv ℝ (ξ k) x v := by
  rw [plain_fieldOf, fderiv_pi hξ]
  rfl

theorem differentiableAt_fieldOf (hξ : ∀ k, DifferentiableAt ℝ (ξ k) x) :
    DifferentiableAt ℝ (plain (fieldOf ξ)) x := by
  rw [plain_fieldOf]
  exact differentiableAt_pi.2 hξ

/-- **"Unchanged along a field" of `Basic.lean` is the coordinate formula of `Symmetry.lean`.** -/
theorem leavesUnchangedAt_table_iff (hg : ∀ a b, DifferentiableAt ℝ (g a b) x)
    (hξ : ∀ k, DifferentiableAt ℝ (ξ k) x) :
    Curved.LeavesUnchangedAt (flatMeasure (tableMeasure g)) (fieldOf ξ) x
      ↔ GravityInLean.LeavesUnchangedAt g ξ x := by
  rw [leavesUnchangedAt_flat_iff (differentiableAt_tableMeasure hg) (differentiableAt_fieldOf hξ)]
  -- The two-slot expression in Killing's equation is the table `lieD`.
  have key : ∀ y z : Coords n, formOf (fun a b ↦ lieD g ξ a b x) y z
      = fderiv ℝ (tableMeasure g) x (plain (fieldOf ξ) x) y z
        + tableMeasure g x (fderiv ℝ (plain (fieldOf ξ)) x y) z
        + tableMeasure g x y (fderiv ℝ (plain (fieldOf ξ)) x z) := by
    intro y z
    refine eq_of_basis₂ (Pi.basisFun ℝ (Fin n)) (formOf fun a b ↦ lieD g ξ a b x)
      (fun y z ↦ fderiv ℝ (tableMeasure g) x (plain (fieldOf ξ) x) y z
        + tableMeasure g x (fderiv ℝ (plain (fieldOf ξ)) x y) z
        + tableMeasure g x y (fderiv ℝ (plain (fieldOf ξ)) x z)) ?_ ?_ ?_ y z
    · intro z
      exact ⟨fun a b ↦ by simp only [map_add, add_apply]; ring,
        fun c a ↦ by simp only [map_smul, smul_apply, smul_eq_mul]; ring⟩
    · intro y
      exact ⟨fun a b ↦ by simp only [map_add]; ring,
        fun c a ↦ by simp only [map_smul, smul_eq_mul]; ring⟩
    · intro a b
      have hs : ∀ k a, fderiv ℝ (ξ k) x (Pi.single a 1) = slope a (ξ k) x :=
        fun k a ↦ (slope_eq_fderiv (hξ k) a).symm
      simp only [Pi.basisFun_apply]
      rw [formOf_single_single, fderiv_tableMeasure hg, formOf_single_single]
      simp only [tableMeasure]
      rw [formOf_single_right, formOf_single_left, fderiv_eq_sum_slope (hg a b)]
      simp only [fderiv_fieldOf_apply hξ, hs]
      simp only [plain_fieldOf, lieD, Finset.sum_add_distrib]
  constructor
  · intro h a b
    have h1 := h (Pi.single a 1) (Pi.single b 1)
    rw [← key, formOf_single_single] at h1
    exact h1
  · intro h y z
    rw [← key, formOf_apply]
    exact Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun b _ ↦ by
      rw [h a b, zero_mul, zero_mul]

/-- **The bracket of two fields of arrows, in coordinates.** -/
theorem mlieBracket_fieldOf {X Y : Fin n → Coords n → ℝ}
    (hX : ∀ k, DifferentiableAt ℝ (X k) x) (hY : ∀ k, DifferentiableAt ℝ (Y k) x) (k : Fin n) :
    VectorField.mlieBracket 𝓘(ℝ, Coords n) (fieldOf X) (fieldOf Y) x k
      = ∑ m, X m x * slope m (Y k) x - ∑ m, Y m x * slope m (X k) x := by
  rw [mlieBracket_flat]
  change fderiv ℝ (plain (fieldOf Y)) x (plain (fieldOf X) x) k
    - fderiv ℝ (plain (fieldOf X)) x (plain (fieldOf Y) x) k = _
  rw [fderiv_fieldOf_apply hY, fderiv_fieldOf_apply hX, fderiv_eq_sum_slope (hY k),
    fderiv_eq_sum_slope (hX k)]
  rfl

end Symmetry

/-! ## A table that is good on a region -/

section Regular

variable {g ginv : Fin n → Fin n → Coords n → ℝ} {s : Set (Coords n)}

/-- **A table of functions that is good on a region,** together with a second table: the region
is open, the entries are smooth there, the table is symmetric there, and the second table is its
inverse there. This is what every coordinate description of a space-time in this project
provides, away from the places where its coordinates fail. -/
structure IsRegularTableOn (g ginv : Fin n → Fin n → Coords n → ℝ) (s : Set (Coords n)) :
    Prop where
  /-- The region is open. -/
  isOpen : IsOpen s
  /-- The entries are smooth on the region. -/
  smooth : ∀ a b, ContDiffOn ℝ ∞ (g a b) s
  /-- The table is symmetric on the region. -/
  symm : ∀ x ∈ s, ∀ a b, g a b x = g b a x
  /-- The second table is the inverse of the first on the region. -/
  inverse : ∀ x ∈ s, ∀ a c, ∑ b, g a b x * ginv b c x = if a = c then 1 else 0

namespace IsRegularTableOn

variable {x : Coords n}

theorem contDiffAt (h : IsRegularTableOn g ginv s) (hx : x ∈ s) (a b : Fin n) :
    ContDiffAt ℝ ∞ (g a b) x :=
  (h.smooth a b).contDiffAt (h.isOpen.mem_nhds hx)

theorem differentiableAt (h : IsRegularTableOn g ginv s) (hx : x ∈ s) (a b : Fin n) :
    DifferentiableAt ℝ (g a b) x :=
  (h.contDiffAt hx a b).differentiableAt (by simp)

theorem eventually_symm (h : IsRegularTableOn g ginv s) (hx : x ∈ s) :
    ∀ᶠ y in 𝓝 x, ∀ a b, g a b y = g b a y :=
  Filter.eventually_of_mem (h.isOpen.mem_nhds hx) fun y hy ↦ h.symm y hy

theorem eventually_inverse (h : IsRegularTableOn g ginv s) (hx : x ∈ s) :
    ∀ᶠ y in 𝓝 x, ∀ a c, ∑ b, g a b y * ginv b c y = if a = c then 1 else 0 :=
  Filter.eventually_of_mem (h.isOpen.mem_nhds hx) fun y hy ↦ h.inverse y hy

/-- The connection of a good table can be differentiated. That the inverse table is smooth is
not assumed: it follows (`contDiffAt_of_inverse`). -/
theorem differentiableAt_christoffel (h : IsRegularTableOn g ginv s) (hx : x ∈ s)
    (a b c : Fin n) : DifferentiableAt ℝ (christoffel g ginv a b c) x :=
  GravityInLean.differentiableAt_christoffel
    (fun α β ↦ (h.contDiffAt hx α β).of_le (by simp))
    (fun α β ↦ (contDiffAt_of_inverse (k := 1)
      (fun a b ↦ (h.contDiffAt hx a b).of_le (by simp)) (h.eventually_inverse hx)
      α β).differentiableAt (by simp)) a b c

theorem eventually_christoffel_symm (h : IsRegularTableOn g ginv s) (hx : x ∈ s) :
    ∀ᶠ y in 𝓝 x, ∀ a b c, christoffel g ginv a b c y = christoffel g ginv a c b y :=
  (h.eventually_symm hx).eventually_nhds.mono fun _ hz a b c ↦ christoffel_symm hz a b c

/-- The length measure of a good table does not depend on the order of its two steps. -/
theorem measure_symm (h : IsRegularTableOn g ginv s) (hx : x ∈ s) (v w : Coords n) :
    tableMeasure g x v w = tableMeasure g x w v := by
  simp only [tableMeasure, formOf_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦ by
    rw [h.symm x hx a b]
    ring

/-- For the length measure of a good table, no step is at right angles to all steps. -/
theorem nondegenerate (h : IsRegularTableOn g ginv s) (hx : x ∈ s) :
    Nondegenerate fun v w : Coords n ↦ tableMeasure g x v w := by
  intro v hv
  have h1 : ∀ b, ∑ a, g a b x * v a = 0 := fun b ↦ by
    have h0 := hv (Pi.single b 1)
    simp only [tableMeasure] at h0
    rwa [formOf_single_right] at h0
  funext c
  have h2 : v c = ∑ b, (∑ a, g a b x * v a) * ginv b c x := by
    calc v c = ∑ a, v a * (if a = c then 1 else 0) := by simp
      _ = ∑ a, v a * ∑ b, g a b x * ginv b c x := by simp only [h.inverse x hx]
      _ = ∑ b, (∑ a, g a b x * v a) * ginv b c x := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦ by ring
  rw [h2]
  simp [h1]

/-- The length measure of a good table is smooth in the sense of curved spaces. -/
theorem isSmoothOn (h : IsRegularTableOn g ginv s) :
    IsSmoothOn (flatMeasure (tableMeasure g)) s := by
  rw [isSmoothOn_flat_iff]
  change ContDiffOn ℝ ∞ (fun x ↦ ∑ p : Fin n × Fin n, g p.1 p.2 x • unitForm p) s
  exact ContDiffOn.sum fun p _ ↦ (h.smooth p.1 p.2).smul contDiffOn_const

/-- **A good table is a length measure in the sense of `Basic.lean`.** -/
theorem isLengthMeasureOn (h : IsRegularTableOn g ginv s) :
    IsLengthMeasureOn (flatMeasure (tableMeasure g)) s where
  symm := fun _ hx v w ↦ h.measure_symm hx v w
  nondegenerate := fun _ hx ↦ h.nondegenerate hx
  smooth := h.isSmoothOn

/-- **The textbooks' formula gives its connection.** -/
theorem isConnectionOf (h : IsRegularTableOn g ginv s) :
    IsConnectionOf (flatMeasure (tableMeasure g))
      (flatTransport (tableCorr (christoffel g ginv))) s :=
  isConnectionOf_table h.isOpen (fun _ hx a b ↦ h.differentiableAt hx a b) h.symm h.inverse

/-- **Its curvature in the sense of `Basic.lean` is the coordinate formula.** -/
theorem ricciAt (h : IsRegularTableOn g ginv s) (hx : x ∈ s)
    (v w : TangentSpace 𝓘(ℝ, Coords n) x) :
    ricciAt (flatTransport (tableCorr (christoffel g ginv))) x v w
      = formOf (fun b c ↦ ricci (christoffel g ginv) c b x) v w :=
  ricciAt_table (fun a b c ↦ h.differentiableAt_christoffel hx a b c)
    (h.eventually_christoffel_symm hx) v w

/-- **Empty in coordinates is empty in the sense of `Basic.lean`.** If the coordinate formula for
the curvature vanishes on the region, space is empty there. -/
theorem isEmptyOn (h : IsRegularTableOn g ginv s) (hflat : ∀ x ∈ s, IsRicciFlatAt g ginv x) :
    IsEmptyOn (flatMeasure (tableMeasure g)) s :=
  ⟨flatTransport (tableCorr (christoffel g ginv)), h.isConnectionOf, fun x hx v w ↦ by
    rw [h.ricciAt hx, formOf_apply]
    exact Finset.sum_eq_zero fun b _ ↦ Finset.sum_eq_zero fun c _ ↦ by
      rw [hflat x hx c b, zero_mul, zero_mul]⟩

/-- The curvature of ANY connection of a good table's length measure is the coordinate formula:
the connection is not a matter of choice. -/
theorem ricciAt_of_isConnectionOf (h : IsRegularTableOn g ginv s)
    {cov : Transport 𝓘(ℝ, Coords n) (Coords n)}
    (hcov : IsConnectionOf (flatMeasure (tableMeasure g)) cov s) (hx : x ∈ s)
    (v w : TangentSpace 𝓘(ℝ, Coords n) x) :
    Curved.ricciAt cov x v w = formOf (fun b c ↦ ricci (christoffel g ginv) c b x) v w := by
  rw [ricciAt_eq_of_isConnectionOf h.isLengthMeasureOn h.isConnectionOf hcov hx
    (differentiableAt_tableCorr fun a b c ↦ h.differentiableAt_christoffel hx a b c),
    h.ricciAt hx]

/-- **Empty in the sense of `Basic.lean` is empty in coordinates, and the other way round.** For a
good table, space is empty on the region exactly when the coordinate formula for the curvature
vanishes at every point of it. -/
theorem isEmptyOn_iff (h : IsRegularTableOn g ginv s) :
    IsEmptyOn (flatMeasure (tableMeasure g)) s ↔ ∀ x ∈ s, IsRicciFlatAt g ginv x := by
  constructor
  · rintro ⟨cov, hcov, hric⟩ x hx i j
    have h1 := hric x hx (Pi.single j 1 : Coords n) (Pi.single i 1 : Coords n)
    rw [h.ricciAt_of_isConnectionOf hcov hx, formOf_single_single] at h1
    exact h1
  · exact h.isEmptyOn

end IsRegularTableOn

end Regular

end GravityInLean.Curved
