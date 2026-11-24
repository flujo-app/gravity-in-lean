/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.Checks

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# The symmetries of Schwarzschild's whole space-time are symmetries

A shift of time (possibly turned round) with a turn or mirror of space keeps the table
`schwSpaceG`; for mass zero so does every Lorentz transformation followed by a shift. So a
length-keeping map followed by such a symmetry is again length-keeping.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

section SchwSym

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  [IsManifold 𝓘(ℝ, Coords 4) ∞ M] {m : ℝ} {g : LengthMeasure 𝓘(ℝ, Coords 4) M} {s : Set M}
  {ε c : ℝ} {R : Matrix (Fin 3) (Fin 3) ℝ}

/-- A symmetry keeps the product of two space parts, whatever is done to time. -/
theorem schwSym_dot (hR : R.transpose * R = 1) (ε c ε' c' : ℝ) (z u : Coords 4) :
    schwSym ε c R z 1 * schwSym ε' c' R u 1 + schwSym ε c R z 2 * schwSym ε' c' R u 2
        + schwSym ε c R z 3 * schwSym ε' c' R u 3
      = z 1 * u 1 + z 2 * u 2 + z 3 * u 3 := by
  obtain ⟨o00, o11, o22, o01, o02, o12⟩ := orthogonal_entries hR
  simp only [schwSym, Matrix.cons_val]
  linear_combination z 1 * u 1 * o00 + z 2 * u 2 * o11 + z 3 * u 3 * o22
    + (z 1 * u 2 + z 2 * u 1) * o01 + (z 1 * u 3 + z 3 * u 1) * o02
    + (z 2 * u 3 + z 3 * u 2) * o12

/-- A symmetry keeps the distance from the centre. -/
theorem schwSym_sumSq (hR : R.transpose * R = 1) (z : Coords 4) :
    schwSym ε c R z 1 ^ 2 + schwSym ε c R z 2 ^ 2 + schwSym ε c R z 3 ^ 2
      = z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 := by
  have h := schwSym_dot hR ε c ε c z z
  linear_combination h

/-- A symmetry is smooth. -/
theorem contDiff_schwSym (ε c : ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) :
    ContDiff ℝ ∞ (schwSym ε c R) := by
  refine contDiff_pi.mpr fun i ↦ ?_
  have a : ∀ j : Fin 4, ContDiff ℝ ∞ (fun x : Coords 4 ↦ x j) :=
    fun j ↦ contDiff_apply ℝ (fun _ : Fin 4 ↦ ℝ) j
  fin_cases i
  · exact (contDiff_const.mul (a 0)).add contDiff_const
  · exact ((contDiff_const.mul (a 1)).add (contDiff_const.mul (a 2))).add
      (contDiff_const.mul (a 3))
  · exact ((contDiff_const.mul (a 1)).add (contDiff_const.mul (a 2))).add
      (contDiff_const.mul (a 3))
  · exact ((contDiff_const.mul (a 1)).add (contDiff_const.mul (a 2))).add
      (contDiff_const.mul (a 3))

/-- The derivative of a symmetry is the symmetry without its shift of time, at every point. -/
theorem fderiv_schwSym (ε c : ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) (z u : Coords 4) :
    fderiv ℝ (schwSym ε c R) z u = schwSym ε 0 R u := by
  have hd : DifferentiableAt ℝ (schwSym ε c R) z :=
    ((contDiff_schwSym ε c R).differentiable (by simp)).differentiableAt
  funext i
  rw [fderiv_pi_apply hd]
  have a : ∀ j : Fin 4, HasFDerivAt (fun q : Coords 4 ↦ q j) (ContinuousLinearMap.proj j) z :=
    fun j ↦ hasFDerivAt_apply (𝕜 := ℝ) j z
  fin_cases i
  · have e : HasFDerivAt (fun q : Coords 4 ↦ ε * q 0 + c) _ z :=
      ((a 0).const_mul ε).add_const c
    change fderiv ℝ (fun q : Coords 4 ↦ ε * q 0 + c) z u = ε * u 0 + 0
    rw [e.fderiv]
    simp
  · have e : HasFDerivAt (fun q : Coords 4 ↦ R 0 0 * q 1 + R 0 1 * q 2 + R 0 2 * q 3) _ z :=
      (((a 1).const_mul (R 0 0)).add ((a 2).const_mul (R 0 1))).add ((a 3).const_mul (R 0 2))
    change fderiv ℝ (fun q : Coords 4 ↦ R 0 0 * q 1 + R 0 1 * q 2 + R 0 2 * q 3) z u
      = R 0 0 * u 1 + R 0 1 * u 2 + R 0 2 * u 3
    rw [e.fderiv]
    simp
  · have e : HasFDerivAt (fun q : Coords 4 ↦ R 1 0 * q 1 + R 1 1 * q 2 + R 1 2 * q 3) _ z :=
      (((a 1).const_mul (R 1 0)).add ((a 2).const_mul (R 1 1))).add ((a 3).const_mul (R 1 2))
    change fderiv ℝ (fun q : Coords 4 ↦ R 1 0 * q 1 + R 1 1 * q 2 + R 1 2 * q 3) z u
      = R 1 0 * u 1 + R 1 1 * u 2 + R 1 2 * u 3
    rw [e.fderiv]
    simp
  · have e : HasFDerivAt (fun q : Coords 4 ↦ R 2 0 * q 1 + R 2 1 * q 2 + R 2 2 * q 3) _ z :=
      (((a 1).const_mul (R 2 0)).add ((a 2).const_mul (R 2 1))).add ((a 3).const_mul (R 2 2))
    change fderiv ℝ (fun q : Coords 4 ↦ R 2 0 * q 1 + R 2 1 * q 2 + R 2 2 * q 3) z u
      = R 2 0 * u 1 + R 2 1 * u 2 + R 2 2 * u 3
    rw [e.fderiv]
    simp

/-- **A symmetry keeps Schwarzschild's lengths,** steps carried by its derivative. -/
theorem schwSym_measure (m : ℝ) (hε : ε = 1 ∨ ε = -1) (hR : R.transpose * R = 1)
    (z u w : Coords 4) :
    tableMeasure (schwSpaceG m) (schwSym ε c R z) (fderiv ℝ (schwSym ε c R) z u)
        (fderiv ℝ (schwSym ε c R) z w) = tableMeasure (schwSpaceG m) z u w := by
  have hρ : centreDist (schwSym ε c R z) = centreDist z := by
    rw [centreDist, centreDist, schwSym_sumSq hR]
  have h0 : ∀ a : Coords 4, schwSym ε 0 R a 0 = ε * a 0 := fun a ↦ by simp [schwSym]
  have hε2 : ε * ε = 1 := by
    rcases hε with h | h <;> rw [h] <;> norm_num
  have huw := schwSym_dot hR ε 0 ε 0 u w
  have hzu := schwSym_dot hR ε c ε 0 z u
  have hzw := schwSym_dot hR ε c ε 0 z w
  rw [schwSpace_apply, schwSpace_apply, fderiv_schwSym, fderiv_schwSym, hρ, h0 u, h0 w, huw,
    hzu, hzw]
  linear_combination (-schwA m (centreDist z) * (u 0 * w 0)) * hε2

/-- **A length-keeping map into Schwarzschild's whole space-time, followed by a symmetry, is
again one.** -/
theorem IsSchwarzschildMapOn.sym {D : M → Coords 4} (hD : IsSchwarzschildMapOn m g D s)
    (hε : ε = 1 ∨ ε = -1) (hR : R.transpose * R = 1) :
    IsSchwarzschildMapOn m g (fun q ↦ schwSym ε c R (D q)) s := by
  obtain ⟨hs, hsm, hpt⟩ := hD
  refine ⟨hs, (contDiff_schwSym ε c R).contMDiff.comp_contMDiffOn hsm,
    fun q hq ↦ ⟨?_, fun v w ↦ ?_⟩⟩
  · refine (hpt q hq).1.imp id fun h ↦ ?_
    rw [schwSym_sumSq hR]
    exact h
  have hDq : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D q :=
    (hsm.contMDiffAt (hs.mem_nhds hq)).mdifferentiableAt (by simp)
  have hΦ : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) (schwSym ε c R) (D q) :=
    ((contDiff_schwSym ε c R).contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  change g q v w = flatMeasure (tableMeasure (schwSpaceG m)) (schwSym ε c R (D q))
    (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) (schwSym ε c R ∘ D) q v)
    (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) (schwSym ε c R ∘ D) q w)
  rw [mfderiv_comp_apply q hΦ hDq v, mfderiv_comp_apply q hΦ hDq w, mfderiv_eq_fderiv,
    (hpt q hq).2 v w]
  exact (schwSym_measure m hε hR (D q) _ _).symm

/-! ## Flat space-time: Lorentz transformations and shifts -/

/-- The flat length of two steps, `-u₀ w₀ + u₁ w₁ + u₂ w₂ + u₃ w₃`, written with the matrix
of signs. -/
theorem lightSign4_dot (u w : Coords 4) :
    u ⬝ᵥ lightSign4.mulVec w = -(u 0 * w 0) + (u 1 * w 1 + u 2 * w 2 + u 3 * w 3) := by
  simp only [dotProduct, lightSign4, Matrix.mulVec_diagonal, Fin.sum_univ_four, Matrix.cons_val]
  ring

/-- **A Lorentz transformation keeps the flat length of two steps.** -/
theorem lorentz_flat {Λ : Matrix (Fin 4) (Fin 4) ℝ}
    (hΛ : Λ.transpose * lightSign4 * Λ = lightSign4) (u w : Coords 4) :
    -(Λ.mulVec u 0 * Λ.mulVec w 0) + (Λ.mulVec u 1 * Λ.mulVec w 1 + Λ.mulVec u 2 * Λ.mulVec w 2
        + Λ.mulVec u 3 * Λ.mulVec w 3)
      = -(u 0 * w 0) + (u 1 * w 1 + u 2 * w 2 + u 3 * w 3) := by
  rw [← lightSign4_dot, ← lightSign4_dot, ← Matrix.vecMul_transpose Λ u,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec (Λ.mulVec w) Λ.transpose lightSign4,
    Matrix.mulVec_mulVec w (Λ.transpose * lightSign4) Λ, hΛ]

/-- A matrix followed by a shift, at every point, has the matrix as its derivative. -/
theorem hasFDerivAt_mulVec_add (Λ : Matrix (Fin 4) (Fin 4) ℝ) (b z : Coords 4) :
    HasFDerivAt (fun x : Coords 4 ↦ Λ.mulVec x + b)
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin Λ)) z :=
  (LinearMap.toContinuousLinearMap (Matrix.mulVecLin Λ)).hasFDerivAt.add_const b

/-- A matrix followed by a shift is smooth. -/
theorem contDiff_mulVec_add (Λ : Matrix (Fin 4) (Fin 4) ℝ) (b : Coords 4) :
    ContDiff ℝ ∞ (fun x : Coords 4 ↦ Λ.mulVec x + b) :=
  (LinearMap.toContinuousLinearMap (Matrix.mulVecLin Λ)).contDiff.add contDiff_const

/-- The derivative of a matrix followed by a shift carries a step by the matrix. -/
theorem fderiv_mulVec_add (Λ : Matrix (Fin 4) (Fin 4) ℝ) (b z u : Coords 4) :
    fderiv ℝ (fun x : Coords 4 ↦ Λ.mulVec x + b) z u = Λ.mulVec u := by
  rw [(hasFDerivAt_mulVec_add Λ b z).fderiv]
  rfl

/-- **A Lorentz transformation and a shift keep the lengths of flat space-time,** steps
carried by the derivative. -/
theorem lorentz_measure {Λ : Matrix (Fin 4) (Fin 4) ℝ}
    (hΛ : Λ.transpose * lightSign4 * Λ = lightSign4) (b z u w : Coords 4) :
    tableMeasure (schwSpaceG 0) (Λ.mulVec z + b)
        (fderiv ℝ (fun x : Coords 4 ↦ Λ.mulVec x + b) z u)
        (fderiv ℝ (fun x : Coords 4 ↦ Λ.mulVec x + b) z w)
      = tableMeasure (schwSpaceG 0) z u w := by
  rw [schwSpace_zero_apply, schwSpace_zero_apply, fderiv_mulVec_add, fderiv_mulVec_add,
    lorentz_flat hΛ]

/-- **A length-keeping map into flat space-time, followed by a Lorentz transformation and a
shift, is again one.** -/
theorem IsSchwarzschildMapOn.lorentz {D : M → Coords 4} (hD : IsSchwarzschildMapOn 0 g D s)
    {Λ : Matrix (Fin 4) (Fin 4) ℝ} (hΛ : Λ.transpose * lightSign4 * Λ = lightSign4)
    (b : Coords 4) : IsSchwarzschildMapOn 0 g (fun q ↦ Λ.mulVec (D q) + b) s := by
  obtain ⟨hs, hsm, hpt⟩ := hD
  refine ⟨hs, (contDiff_mulVec_add Λ b).contMDiff.comp_contMDiffOn hsm,
    fun q hq ↦ ⟨Or.inl rfl, fun v w ↦ ?_⟩⟩
  have hDq : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) D q :=
    (hsm.contMDiffAt (hs.mem_nhds hq)).mdifferentiableAt (by simp)
  have hΦ : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4)
      (fun x : Coords 4 ↦ Λ.mulVec x + b) (D q) :=
    ((contDiff_mulVec_add Λ b).contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  change g q v w = flatMeasure (tableMeasure (schwSpaceG 0)) (Λ.mulVec (D q) + b)
    (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) ((fun x : Coords 4 ↦ Λ.mulVec x + b) ∘ D) q v)
    (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) ((fun x : Coords 4 ↦ Λ.mulVec x + b) ∘ D) q w)
  rw [mfderiv_comp_apply q hΦ hDq v, mfderiv_comp_apply q hΦ hDq w, mfderiv_eq_fderiv,
    (hpt q hq).2 v w]
  exact (lorentz_measure hΛ b (D q) _ _).symm

end SchwSym

end GravityInLean.Curved
