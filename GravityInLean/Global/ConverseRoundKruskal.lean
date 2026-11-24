/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.KruskalChart
public import GravityInLean.Global.RoundTools
public import GravityInLean.BothWays.PullRound
public import GravityInLean.Rim.Round

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# A space-time with a length-keeping map into Kruskal's looks the same from every side

This is the "round" half of `GlobalBirkhoffConverse` for Kruskal's
(`IsKruskalMapOn.exists_round`): if a space-time has a length-keeping map `D` into Kruskal's
whole space-time of a positive mass on a region, then on that region it looks the same from
every side, by three fields of arrows found from the map.

**The three fields.** On Kruskal's whole space-time the three turns of the sphere are the fields
`sphereTurn i`: at the point `(T, X, y)` the step `(0, 0, e × y)`, for the three axes `e`, in
the order in which the three standard turns `turns` of the table are wrapped to them
(`fderiv_kruskalWrap_turns`). The field `turnFields D i` of the curved space is, at each point
`q`, the step that `D` carries to `sphereTurn i` at `D q`. There is one such step at each point
of the region, because near the point `D` is a chart of Kruskal's space-time.

**Why they do the job.** Near each point of the region, `D` is a chart `φ` of the curved space,
then the wrapping, then a turn or mirror `R` of the sphere (`IsKruskalMapOn.exists_chart`). A
turn or mirror of the sphere carries each of the three turns of the sphere to a fixed mix of the
three, and the mix is a rotation even when `R` is a mirror (`frameMix R`,
`kruskalSym_sphereTurn`). So in the chart the three fields are a fixed rotation of the three
standard turns (`turnFields_eq_pushField`). Kruskal's table looks the same from every side by
the standard turns (`kruskalIsRound`), so by the rotated ones (`IsRoundOn.mix`), and that comes
back along the chart (`isRoundOn_pull`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set Matrix

open scoped Manifold ContDiff Topology

/-- Two lists of five numbers are the same when their five numbers are. -/
theorem coords5_ext {u w : Coords 5} (h0 : u 0 = w 0) (h1 : u 1 = w 1) (h2 : u 2 = w 2)
    (h3 : u 3 = w 3) (h4 : u 4 = w 4) : u = w := by
  funext l
  fin_cases l
  exacts [h0, h1, h2, h3, h4]

/-! ## The three turns of the sphere, on Kruskal's whole space-time -/

/-- **The three turns of the sphere,** as steps at the point `p = (T, X, y)` of Kruskal's whole
space-time: `(0, 0, e × y)` for the axes `e = (0, 1, 0)`, `(1, 0, 0)`, `(0, 0, 1)`, in this
order. It is the order in which the standard turns `turns` of Kruskal's table are wrapped to
them. -/
def sphereTurn : Fin 3 → Coords 5 → Coords 5 :=
  ![fun p ↦ ![0, 0, p 4, 0, -p 2], fun p ↦ ![0, 0, 0, -p 4, p 3], fun p ↦ ![0, 0, -p 3, p 2, 0]]

/-- Wrapping carries the first standard turn of the table to the first turn of the sphere. -/
theorem fderiv_kruskalWrap_turns_zero {x : Coords 4} (hs : sin (x 2) ≠ 0) :
    fderiv ℝ kruskalWrap x (turns 0 x) = sphereTurn 0 (kruskalWrap x) := by
  obtain ⟨c, hc, hcot⟩ : ∃ c : ℝ, c * sin (x 2) = cos (x 2) ∧ negCot (x 2) = -c :=
    ⟨cos (x 2) / sin (x 2), div_mul_cancel₀ _ hs, rfl⟩
  have h1 := Real.sin_sq_add_cos_sq (x 3)
  have t : ∀ k, (turns 0 x : Coords 4) k = rotY k x := fun k ↦ rfl
  have a0 : (turns 0 x : Coords 4) 0 = 0 := by
    rw [t]
    simp [rotY]
  have a1 : (turns 0 x : Coords 4) 1 = 0 := by
    rw [t]
    simp [rotY]
  have a2 : (turns 0 x : Coords 4) 2 = cos (x 3) := by
    rw [t]
    simp [rotY, sepA, constOne]
  have a3 : (turns 0 x : Coords 4) 3 = -(c * sin (x 3)) := by
    rw [t]
    simp [rotY, sepA, hcot]
  rw [fderiv_kruskalWrap]
  refine coords5_ext ?_ ?_ ?_ ?_ ?_ <;>
    simp only [sphereTurn, kruskalWrap, Matrix.cons_val, a0, a1, a2, a3] <;>
    first
    | ring1
    | linear_combination cos (x 2) * h1 + sin (x 3) ^ 2 * hc
    | linear_combination (-(sin (x 3) * cos (x 3))) * hc

/-- Wrapping carries the second standard turn of the table to the second turn of the sphere. -/
theorem fderiv_kruskalWrap_turns_one {x : Coords 4} (hs : sin (x 2) ≠ 0) :
    fderiv ℝ kruskalWrap x (turns 1 x) = sphereTurn 1 (kruskalWrap x) := by
  obtain ⟨c, hc, hcot⟩ : ∃ c : ℝ, c * sin (x 2) = cos (x 2) ∧ negCot (x 2) = -c :=
    ⟨cos (x 2) / sin (x 2), div_mul_cancel₀ _ hs, rfl⟩
  have h1 := Real.sin_sq_add_cos_sq (x 3)
  have t : ∀ k, (turns 1 x : Coords 4) k = rotX k x := fun k ↦ rfl
  have a0 : (turns 1 x : Coords 4) 0 = 0 := by
    rw [t]
    simp [rotX]
  have a1 : (turns 1 x : Coords 4) 1 = 0 := by
    rw [t]
    simp [rotX]
  have a2 : (turns 1 x : Coords 4) 2 = -sin (x 3) := by
    rw [t]
    simp [rotX, sepA, constOne, negSin]
  have a3 : (turns 1 x : Coords 4) 3 = -(c * cos (x 3)) := by
    rw [t]
    simp [rotX, sepA, hcot]
  rw [fderiv_kruskalWrap]
  refine coords5_ext ?_ ?_ ?_ ?_ ?_ <;>
    simp only [sphereTurn, kruskalWrap, Matrix.cons_val, a0, a1, a2, a3] <;>
    first
    | ring1
    | linear_combination (sin (x 3) * cos (x 3)) * hc
    | linear_combination (-(cos (x 3) ^ 2)) * hc - cos (x 2) * h1

/-- Wrapping carries the third standard turn of the table to the third turn of the sphere. -/
theorem fderiv_kruskalWrap_turns_two (x : Coords 4) :
    fderiv ℝ kruskalWrap x (turns 2 x) = sphereTurn 2 (kruskalWrap x) := by
  have t : ∀ k, (turns 2 x : Coords 4) k = rotZ k x := fun k ↦ rfl
  have a0 : (turns 2 x : Coords 4) 0 = 0 := by
    rw [t]
    simp [rotZ]
  have a1 : (turns 2 x : Coords 4) 1 = 0 := by
    rw [t]
    simp [rotZ]
  have a2 : (turns 2 x : Coords 4) 2 = 0 := by
    rw [t]
    simp [rotZ]
  have a3 : (turns 2 x : Coords 4) 3 = 1 := by
    rw [t]
    simp [rotZ]
  rw [fderiv_kruskalWrap]
  refine coords5_ext ?_ ?_ ?_ ?_ ?_ <;>
    simp only [sphereTurn, kruskalWrap, Matrix.cons_val, a0, a1, a2, a3] <;>
    first
    | ring1

/-- **Wrapping carries the three standard turns of Kruskal's table to the three turns of the
sphere,** off the poles. -/
theorem fderiv_kruskalWrap_turns {x : Coords 4} (hs : sin (x 2) ≠ 0) (j : Fin 3) :
    fderiv ℝ kruskalWrap x (turns j x) = sphereTurn j (kruskalWrap x) := by
  fin_cases j
  exacts [fderiv_kruskalWrap_turns_zero hs, fderiv_kruskalWrap_turns_one hs,
    fderiv_kruskalWrap_turns_two x]

/-! ## What a turn or mirror of the sphere does to the three turns -/

section Frame

variable {R : Matrix (Fin 3) (Fin 3) ℝ}

/-- **For a turn or mirror `R` of ordinary space,** `det R` is `1` or `-1`
(`det R * det R = 1`), and the cross product of two rows of `R` is `det R` times the third row.
-/
theorem orthogonal_cofactors (hR : R.transpose * R = 1) :
    R.det * R.det = 1
      ∧ (R 1 1 * R 2 2 - R 1 2 * R 2 1 = R.det * R 0 0
        ∧ R 1 2 * R 2 0 - R 1 0 * R 2 2 = R.det * R 0 1
        ∧ R 1 0 * R 2 1 - R 1 1 * R 2 0 = R.det * R 0 2)
      ∧ (R 2 1 * R 0 2 - R 2 2 * R 0 1 = R.det * R 1 0
        ∧ R 2 2 * R 0 0 - R 2 0 * R 0 2 = R.det * R 1 1
        ∧ R 2 0 * R 0 1 - R 2 1 * R 0 0 = R.det * R 1 2)
      ∧ (R 0 1 * R 1 2 - R 0 2 * R 1 1 = R.det * R 2 0
        ∧ R 0 2 * R 1 0 - R 0 0 * R 1 2 = R.det * R 2 1
        ∧ R 0 0 * R 1 1 - R 0 1 * R 1 0 = R.det * R 2 2) := by
  have hRR : R * R.transpose = 1 := mul_eq_one_comm.mp hR
  have hdd : R.det * R.det = 1 := by
    have h := congrArg Matrix.det hR
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  have hadj : R.adjugate = R.det • R.transpose := by
    calc R.adjugate = R.adjugate * (R * R.transpose) := by rw [hRR, mul_one]
      _ = (R.adjugate * R) * R.transpose := by rw [mul_assoc]
      _ = R.det • R.transpose := by rw [Matrix.adjugate_mul, Matrix.smul_mul, one_mul]
  rw [Matrix.adjugate_fin_three] at hadj
  have e : ∀ i j, _ = _ := fun i j ↦ congrFun (congrFun hadj i) j
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e10 := e 1 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  have e22 := e 2 2
  simp [Matrix.transpose_apply] at e00 e01 e02 e10 e11 e12 e20 e21 e22
  exact ⟨hdd, ⟨by linarith, by linarith, by linarith⟩, ⟨by linarith, by linarith, by linarith⟩,
    ⟨by linarith, by linarith, by linarith⟩⟩

/-- **The mix of the three turns of the sphere that goes with a turn or mirror `R`:** the table
`det R · R`, with its first two rows and its first two columns changed over (the three turns of
the sphere are listed with their first two axes changed over). It is a rotation even when `R`
is a mirror. -/
noncomputable def frameMix (R : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![R.det * R 1 1, R.det * R 1 0, R.det * R 1 2;
     R.det * R 0 1, R.det * R 0 0, R.det * R 0 2;
     R.det * R 2 1, R.det * R 2 0, R.det * R 2 2]

/-- The mix that goes with a turn or mirror keeps the lengths of ordinary space. -/
theorem frameMix_orthogonal (hR : R.transpose * R = 1) :
    frameMix R * (frameMix R).transpose = 1 := by
  obtain ⟨hdd, -, -, -⟩ := orthogonal_cofactors hR
  have hT : R.transpose.transpose * R.transpose = 1 := by
    rw [Matrix.transpose_transpose]
    exact mul_eq_one_comm.mp hR
  obtain ⟨p00, p11, p22, p01, p02, p12⟩ := orthogonal_entries hT
  have P00 : R 0 0 * R 0 0 + R 0 1 * R 0 1 + R 0 2 * R 0 2 = 1 := p00
  have P11 : R 1 0 * R 1 0 + R 1 1 * R 1 1 + R 1 2 * R 1 2 = 1 := p11
  have P22 : R 2 0 * R 2 0 + R 2 1 * R 2 1 + R 2 2 * R 2 2 = 1 := p22
  have P01 : R 0 0 * R 1 0 + R 0 1 * R 1 1 + R 0 2 * R 1 2 = 0 := p01
  have P02 : R 0 0 * R 2 0 + R 0 1 * R 2 1 + R 0 2 * R 2 2 = 0 := p02
  have P12 : R 1 0 * R 2 0 + R 1 1 * R 2 1 + R 1 2 * R 2 2 = 0 := p12
  have a00 : frameMix R 0 0 = R.det * R 1 1 := rfl
  have a01 : frameMix R 0 1 = R.det * R 1 0 := rfl
  have a02 : frameMix R 0 2 = R.det * R 1 2 := rfl
  have a10 : frameMix R 1 0 = R.det * R 0 1 := rfl
  have a11 : frameMix R 1 1 = R.det * R 0 0 := rfl
  have a12 : frameMix R 1 2 = R.det * R 0 2 := rfl
  have a20 : frameMix R 2 0 = R.det * R 2 1 := rfl
  have a21 : frameMix R 2 1 = R.det * R 2 0 := rfl
  have a22 : frameMix R 2 2 = R.det * R 2 2 := rfl
  have key : ∀ a b : Fin 3, (frameMix R * (frameMix R).transpose) a b
      = frameMix R a 0 * frameMix R b 0 + frameMix R a 1 * frameMix R b 1
        + frameMix R a 2 * frameMix R b 2 := fun a b ↦ by
    rw [Matrix.mul_apply, Fin.sum_univ_three]
    rfl
  -- on the diagonal: a row of `R` has length one, and `det R * det R = 1`
  have dia : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2 →
      (frameMix R * (frameMix R).transpose) a a = (1 : Matrix (Fin 3) (Fin 3) ℝ) a a := by
    rintro a (rfl | rfl | rfl) <;> rw [key, Matrix.one_apply_eq] <;>
      simp only [a00, a01, a02, a10, a11, a12, a20, a21, a22] <;>
      first
      | linear_combination (R.det * R.det) * P00 + hdd
      | linear_combination (R.det * R.det) * P11 + hdd
      | linear_combination (R.det * R.det) * P22 + hdd
  -- off the diagonal: two different rows of `R` are at right angles
  have off : ∀ a b : Fin 3, a ≠ b →
      (frameMix R * (frameMix R).transpose) a b = (1 : Matrix (Fin 3) (Fin 3) ℝ) a b := by
    intro a b hab
    rw [key, Matrix.one_apply_ne hab]
    have ha : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> decide
    have hb : b = 0 ∨ b = 1 ∨ b = 2 := by fin_cases b <;> decide
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first
      | exact absurd rfl hab
      | (simp only [a00, a01, a02, a10, a11, a12, a20, a21, a22]
         first
         | linear_combination (R.det * R.det) * P01
         | linear_combination (R.det * R.det) * P02
         | linear_combination (R.det * R.det) * P12)
  ext i j
  by_cases hij : i = j
  · rw [hij]
    exact dia j (by fin_cases j <;> decide)
  · exact off i j hij

/-- The mix that goes with a turn or mirror is a turn: its determinant is `1`. -/
theorem frameMix_det (hR : R.transpose * R = 1) : (frameMix R).det = 1 := by
  obtain ⟨hdd, -, -, -⟩ := orthogonal_cofactors hR
  have hE := Matrix.det_fin_three R
  have a00 : frameMix R 0 0 = R.det * R 1 1 := rfl
  have a01 : frameMix R 0 1 = R.det * R 1 0 := rfl
  have a02 : frameMix R 0 2 = R.det * R 1 2 := rfl
  have a10 : frameMix R 1 0 = R.det * R 0 1 := rfl
  have a11 : frameMix R 1 1 = R.det * R 0 0 := rfl
  have a12 : frameMix R 1 2 = R.det * R 0 2 := rfl
  have a20 : frameMix R 2 0 = R.det * R 2 1 := rfl
  have a21 : frameMix R 2 1 = R.det * R 2 0 := rfl
  have a22 : frameMix R 2 2 = R.det * R 2 2 := rfl
  rw [Matrix.det_fin_three, a00, a01, a02, a10, a11, a12, a20, a21, a22]
  linear_combination (-(R.det ^ 3)) * hE + (R.det * R.det + 1) * hdd

/-- **A turn or mirror of the sphere carries the three turns of the sphere to a fixed mix of the
three.** The symmetry `kruskalSym L R` of Kruskal's whole space-time, applied to the mix
`frameMix R` of the three turns of the sphere at `p`, gives the turn number `i` of the sphere at
the point that the symmetry makes of `p`. -/
theorem kruskalSym_sphereTurn (hR : R.transpose * R = 1) (L : Matrix (Fin 2) (Fin 2) ℝ)
    (i : Fin 3) (p : Coords 5) :
    kruskalSym L R (frameMix R i 0 • sphereTurn 0 p + frameMix R i 1 • sphereTurn 1 p
        + frameMix R i 2 • sphereTurn 2 p)
      = sphereTurn i (kruskalSym L R p) := by
  obtain ⟨hdd, ⟨K00, K01, K02⟩, ⟨K10, K11, K12⟩, ⟨K20, K21, K22⟩⟩ := orthogonal_cofactors hR
  have a00 : frameMix R 0 0 = R.det * R 1 1 := rfl
  have a01 : frameMix R 0 1 = R.det * R 1 0 := rfl
  have a02 : frameMix R 0 2 = R.det * R 1 2 := rfl
  have a10 : frameMix R 1 0 = R.det * R 0 1 := rfl
  have a11 : frameMix R 1 1 = R.det * R 0 0 := rfl
  have a12 : frameMix R 1 2 = R.det * R 0 2 := rfl
  have a20 : frameMix R 2 0 = R.det * R 2 1 := rfl
  have a21 : frameMix R 2 1 = R.det * R 2 0 := rfl
  have a22 : frameMix R 2 2 = R.det * R 2 2 := rfl
  have key : ∀ i' : Fin 3, i' = 0 ∨ i' = 1 ∨ i' = 2 →
      kruskalSym L R (frameMix R i' 0 • sphereTurn 0 p + frameMix R i' 1 • sphereTurn 1 p
          + frameMix R i' 2 • sphereTurn 2 p)
        = sphereTurn i' (kruskalSym L R p) := by
    rintro i' (rfl | rfl | rfl) <;> refine coords5_ext ?_ ?_ ?_ ?_ ?_ <;>
      simp only [kruskalSym, sphereTurn, Matrix.cons_val, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, a00, a01, a02, a10, a11, a12, a20, a21, a22] <;>
      first
      | ring1
      | linear_combination (R.det * p 2) * K00 + (R.det * p 3) * K01 + (R.det * p 4) * K02
          + (p 2 * R 0 0 + p 3 * R 0 1 + p 4 * R 0 2) * hdd
      | linear_combination (R.det * p 2) * K10 + (R.det * p 3) * K11 + (R.det * p 4) * K12
          + (p 2 * R 1 0 + p 3 * R 1 1 + p 4 * R 1 2) * hdd
      | linear_combination (R.det * p 2) * K20 + (R.det * p 3) * K21 + (R.det * p 4) * K22
          + (p 2 * R 2 0 + p 3 * R 2 1 + p 4 * R 2 2) * hdd
      | linear_combination (-(R.det * p 2)) * K00 - (R.det * p 3) * K01 - (R.det * p 4) * K02
          - (p 2 * R 0 0 + p 3 * R 0 1 + p 4 * R 0 2) * hdd
      | linear_combination (-(R.det * p 2)) * K10 - (R.det * p 3) * K11 - (R.det * p 4) * K12
          - (p 2 * R 1 0 + p 3 * R 1 1 + p 4 * R 1 2) * hdd
      | linear_combination (-(R.det * p 2)) * K20 - (R.det * p 3) * K21 - (R.det * p 4) * K22
          - (p 2 * R 2 0 + p 3 * R 2 1 + p 4 * R 2 2) * hdd
  exact key i (by fin_cases i <;> decide)

end Frame

/-! ## The three fields of the curved space -/

section Fields

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  [IsManifold 𝓘(ℝ, Coords 4) ∞ M] {m : ℝ} {g : LengthMeasure 𝓘(ℝ, Coords 4) M} {s : Set M}

/-- **The three fields that a map `D` into Kruskal's whole space-time gives:** at the point `q`,
the step that `D` carries to the turn number `i` of the sphere at `D q` (a step chosen without
meaning where there is none). -/
noncomputable def turnFields (D : M → Coords 5) (i : Fin 3) : Arrows 𝓘(ℝ, Coords 4) M :=
  fun q ↦ Classical.epsilon fun v : TangentSpace 𝓘(ℝ, Coords 4) q ↦
    mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 5) D q v = sphereTurn i (D q)

/-- **The field is the one step that the map carries to the turn of the sphere:** a
length-keeping map carries no step to zero, so there is at most one. -/
theorem turnFields_eq {D : M → Coords 5} (hD : IsKruskalMapOn m g D s) (hg : IsSpaceTimeOn g s)
    {q : M} (hq : q ∈ s) {i : Fin 3} {v : TangentSpace 𝓘(ℝ, Coords 4) q}
    (hv : mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 5) D q v = sphereTurn i (D q)) :
    turnFields D i q = v := by
  have h1 := Classical.epsilon_spec
    (p := fun u : TangentSpace 𝓘(ℝ, Coords 4) q ↦
      mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 5) D q u = sphereTurn i (D q)) ⟨v, hv⟩
  exact hD.mfderiv_injective hg hq (h1.trans hv.symm)

/-- **In a chart in which the map is the wrapping followed by a turn or mirror `R` of the
sphere, the three fields are a fixed rotation of the three standard turns,** taken to the curved
space by the chart. -/
theorem turnFields_eq_pushField {D : M → Coords 5} (hD : IsKruskalMapOn m g D s)
    (hg : IsSpaceTimeOn g s) {R : Matrix (Fin 3) (Fin 3) ℝ}
    {φ : OpenPartialHomeomorph M (Coords 4)} (hR : R.transpose * R = 1)
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M) (hsub : φ.source ⊆ s)
    (hreg : ∀ q' ∈ φ.source, φ q' ∈ kruskalRegion)
    (hDφ : ∀ q' ∈ φ.source, D q' = kruskalSym 1 R (kruskalWrap (φ q'))) (i : Fin 3) {q : M}
    (hq : q ∈ φ.source) :
    turnFields D i q = Join.pushField φ (mixFields (frameMix R) turns i) q := by
  refine turnFields_eq hD hg (hsub hq) ?_
  have hsin : sin (φ q 2) ≠ 0 := (hreg q hq).2
  have hφd : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q :=
    (contMDiffAt_of_mem_maximalAtlas hφ hq).mdifferentiableAt (by simp)
  have hFd : DifferentiableAt ℝ (kruskalSym 1 R ∘ kruskalWrap) (φ q) :=
    ((contDiff_kruskalSym_wrap 1 R).differentiable (by simp)).differentiableAt
  have hev : D =ᶠ[𝓝 q] (kruskalSym 1 R ∘ kruskalWrap) ∘ φ :=
    Filter.eventuallyEq_of_mem (φ.open_source.mem_nhds hq) hDφ
  -- the map carries a step as the chart, the wrapping and the turn of the sphere carry it
  have e1 : mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 5) D q
        (Join.pushField φ (mixFields (frameMix R) turns i) q)
      = kruskalSym 1 R (fderiv ℝ kruskalWrap (φ q)
          (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q
            (Join.pushField φ (mixFields (frameMix R) turns i) q))) := by
    rw [mfderiv_of_eventuallyEq_comp hFd hφd hev, fderiv_kruskalSym_wrap]
  -- the chart reads the field it has taken to the curved space as the field itself
  have e2 : (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q
        (Join.pushField φ (mixFields (frameMix R) turns i) q) : Coords 4)
      = mixFields (frameMix R) turns i (φ q) :=
    Join.chart_mfderiv_comp_symm' hφ hq _
  -- wrapping carries the mix of the standard turns to the mix of the turns of the sphere
  have hz : (mixFields (frameMix R) turns i (φ q) : Coords 4)
      = frameMix R i 0 • (turns 0 (φ q) : Coords 4) + frameMix R i 1 • (turns 1 (φ q) : Coords 4)
        + frameMix R i 2 • (turns 2 (φ q) : Coords 4) := rfl
  have e3 : fderiv ℝ kruskalWrap (φ q) (mixFields (frameMix R) turns i (φ q))
      = frameMix R i 0 • sphereTurn 0 (kruskalWrap (φ q))
        + frameMix R i 1 • sphereTurn 1 (kruskalWrap (φ q))
        + frameMix R i 2 • sphereTurn 2 (kruskalWrap (φ q)) := by
    rw [hz, map_add, map_add, map_smul, map_smul, map_smul, fderiv_kruskalWrap_turns hsin 0,
      fderiv_kruskalWrap_turns hsin 1, fderiv_kruskalWrap_turns hsin 2]
  rw [e1, e2, e3, hDφ q hq]
  exact kruskalSym_sphereTurn hR 1 i _

/-- **A space-time with a length-keeping map into Kruskal's whole space-time of a positive mass
looks the same from every side,** on the region of the map, by three fields of arrows found from
the map: the steps that the map carries to the three turns of the sphere. -/
theorem IsKruskalMapOn.exists_round {D : M → Coords 5} (hm : 0 < m)
    (hD : IsKruskalMapOn m g D s) (hg : IsSpaceTimeOn g s) :
    ∃ ξ : Fin 3 → Arrows 𝓘(ℝ, Coords 4) M, IsRoundOn g ξ s := by
  refine ⟨turnFields D, isRoundOn_of_local hD.1 fun q hq ↦ ?_⟩
  obtain ⟨R, φ, hR, hφ, hqφ, hsub, h⟩ := hD.exists_chart hg hq
  refine ⟨φ.source, hqφ, ?_⟩
  have htarget : φ.target ⊆ kruskalRegion := fun x hx ↦ by
    have h1 := (h (φ.symm x) (φ.map_target hx)).1
    rwa [φ.right_inv hx] at h1
  -- Kruskal's table looks the same from every side by the rotated standard turns
  have h1 : IsRoundOn (flatMeasure (tableMeasure (kruskalG m)))
      (mixFields (frameMix R) turns) φ.target :=
    isRoundOn_sub ((kruskalIsRound m hm).mix (frameMix_orthogonal hR) (frameMix_det hR))
      φ.open_target htarget
  -- that comes back along the chart
  have hread : BothWays.ReadsAs φ g (tableMeasure (kruskalG m)) :=
    fun q' hq' v w ↦ (h q' hq').2.2 v w
  have h2 := BothWays.isRoundOn_pull hφ hread h1
  exact h2.congr fun i q' hq' ↦
    turnFields_eq_pushField hD hg hR hφ hsub (fun q'' hq'' ↦ (h q'' hq'').1)
      (fun q'' hq'' ↦ (h q'' hq'').2.1) i hq'

end Fields

end GravityInLean.Curved
