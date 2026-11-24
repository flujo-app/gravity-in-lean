/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Global.KruskalPlane
public import GravityInLean.Global.SphereRigid
public import GravityInLean.Global.KruskalChart
public import GravityInLean.Join.CarryBracket
public import GravityInLean.Rim.Table

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# Two length-keeping maps into Kruskal's differ by a symmetry near every point

* `KeepsKruskalOn.local`: a map of coordinate space that keeps Kruskal's table is, after
  wrapping round the sphere, a symmetry `kruskalSym L R` near every point.
* `IsKruskalMapOn.local_unique`: two length-keeping maps into Kruskal's whole space-time differ
  by a symmetry near every point (the change of charts between them keeps Kruskal's table).
* `IsKruskalMapOn.sym_unique`: a symmetry is fixed by what it does to a length-keeping map near
  one point.
* `unique_kruskal`: on a region in one piece, two length-keeping maps differ by one symmetry.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Curved

open Real Set

open scoped Manifold ContDiff Topology

/-! ## The symmetries, one after another -/

/-- Two symmetries of Kruskal's whole space-time, one after the other, are the symmetry of the
two matrix products. -/
theorem kruskalSym_comp (L L' : Matrix (Fin 2) (Fin 2) ℝ) (R R' : Matrix (Fin 3) (Fin 3) ℝ)
    (p : Coords 5) : kruskalSym L R (kruskalSym L' R' p) = kruskalSym (L * L') (R * R') p := by
  funext i
  fin_cases i <;>
    simp [kruskalSym, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three] <;> ring

/-- The symmetry of the two unit matrices does nothing. -/
theorem kruskalSym_one (p : Coords 5) : kruskalSym 1 1 p = p := by
  funext i
  fin_cases i <;> simp [kruskalSym]

/-- Two turns or mirrors, one after the other, are a turn or mirror. -/
theorem orthogonal_mul {A B : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.transpose * A = 1)
    (hB : B.transpose * B = 1) : (A * B).transpose * (A * B) = 1 := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc A.transpose, hA,
    Matrix.one_mul, hB]

/-! ## A symmetry is fixed by what it does to a point of the sphere and the steps from it -/

/-- A row of three numbers is fixed by what it gives on a point of the unit sphere off the poles
and on the two steps along the angles from that point. -/
theorem row_eq_of_frame {a b : Fin 3 → ℝ} {θ φ : ℝ} (hsin : sin θ ≠ 0)
    (hA : a 0 * (sin θ * cos φ) + a 1 * (sin θ * sin φ) + a 2 * cos θ
      = b 0 * (sin θ * cos φ) + b 1 * (sin θ * sin φ) + b 2 * cos θ)
    (hB : a 0 * (cos θ * cos φ) + a 1 * (cos θ * sin φ) + a 2 * (-sin θ)
      = b 0 * (cos θ * cos φ) + b 1 * (cos θ * sin φ) + b 2 * (-sin θ))
    (hC : a 0 * (-(sin θ * sin φ)) + a 1 * (sin θ * cos φ) + a 2 * 0
      = b 0 * (-(sin θ * sin φ)) + b 1 * (sin θ * cos φ) + b 2 * 0) :
    a 0 = b 0 ∧ a 1 = b 1 ∧ a 2 = b 2 := by
  have hθ := Real.sin_sq_add_cos_sq θ
  have hφ := Real.sin_sq_add_cos_sq φ
  have hC' : -(a 0 - b 0) * sin φ + (a 1 - b 1) * cos φ = 0 := by
    have e : sin θ * (-(a 0 - b 0) * sin φ + (a 1 - b 1) * cos φ) = 0 := by
      linear_combination hC
    exact (mul_eq_zero.1 e).resolve_left hsin
  have hD : (a 0 - b 0) * cos φ + (a 1 - b 1) * sin φ = 0 := by
    linear_combination sin θ * hA + cos θ * hB
      - ((a 0 - b 0) * cos φ + (a 1 - b 1) * sin φ) * hθ
  refine ⟨?_, ?_, ?_⟩
  · linear_combination cos φ * hD - sin φ * hC' - (a 0 - b 0) * hφ
  · linear_combination sin φ * hD + cos φ * hC' - (a 1 - b 1) * hφ
  · linear_combination cos θ * hA - sin θ * hB - (a 2 - b 2) * hθ

/-- **Two symmetries that agree on a wrapped point off the poles and on all wrapped steps from
it are the same.** -/
theorem kruskalSym_eq_of_frame {L L' : Matrix (Fin 2) (Fin 2) ℝ}
    {R R' : Matrix (Fin 3) (Fin 3) ℝ} {y : Coords 4} (hsin : sin (y 2) ≠ 0)
    (h0 : kruskalSym L R (kruskalWrap y) = kruskalSym L' R' (kruskalWrap y))
    (hd : ∀ u : Coords 4, kruskalSym L R (fderiv ℝ kruskalWrap y u)
      = kruskalSym L' R' (fderiv ℝ kruskalWrap y u)) : L = L' ∧ R = R' := by
  -- the wrapped steps along the four coordinates
  have v0 : fderiv ℝ kruskalWrap y (Pi.single 0 1) = ![1, 0, 0, 0, 0] := by
    rw [fderiv_kruskalWrap]
    simp
  have v1 : fderiv ℝ kruskalWrap y (Pi.single 1 1) = ![0, 1, 0, 0, 0] := by
    rw [fderiv_kruskalWrap]
    simp
  have v2 : fderiv ℝ kruskalWrap y (Pi.single 2 1)
      = ![0, 0, cos (y 2) * cos (y 3), cos (y 2) * sin (y 3), -sin (y 2)] := by
    rw [fderiv_kruskalWrap]
    simp
  have v3 : fderiv ℝ kruskalWrap y (Pi.single 3 1)
      = ![0, 0, -(sin (y 2) * sin (y 3)), sin (y 2) * cos (y 3), 0] := by
    rw [fderiv_kruskalWrap]
    simp
  have e0 := hd (Pi.single 0 1)
  have e1 := hd (Pi.single 1 1)
  have e2 := hd (Pi.single 2 1)
  have e3 := hd (Pi.single 3 1)
  rw [v0] at e0
  rw [v1] at e1
  rw [v2] at e2
  rw [v3] at e3
  -- the matrix of `(T, X)`: read off from the steps along `T` and `X`
  have l00 : L 0 0 * 1 + L 0 1 * 0 = L' 0 0 * 1 + L' 0 1 * 0 := congrFun e0 0
  have l10 : L 1 0 * 1 + L 1 1 * 0 = L' 1 0 * 1 + L' 1 1 * 0 := congrFun e0 1
  have l01 : L 0 0 * 0 + L 0 1 * 1 = L' 0 0 * 0 + L' 0 1 * 1 := congrFun e1 0
  have l11 : L 1 0 * 0 + L 1 1 * 1 = L' 1 0 * 0 + L' 1 1 * 1 := congrFun e1 1
  -- the matrix of the sphere: row by row, from the point and the steps along the two angles
  have r0 := row_eq_of_frame (a := R 0) (b := R' 0) hsin (congrFun h0 2) (congrFun e2 2)
    (congrFun e3 2)
  have r1 := row_eq_of_frame (a := R 1) (b := R' 1) hsin (congrFun h0 3) (congrFun e2 3)
    (congrFun e3 3)
  have r2 := row_eq_of_frame (a := R 2) (b := R' 2) hsin (congrFun h0 4) (congrFun e2 4)
    (congrFun e3 4)
  constructor
  · ext i j
    fin_cases i <;> fin_cases j
    · change L 0 0 = L' 0 0
      linarith
    · change L 0 1 = L' 0 1
      linarith
    · change L 1 0 = L' 1 0
      linarith
    · change L 1 1 = L' 1 1
      linarith
  · ext i j
    fin_cases i <;> fin_cases j
    exacts [r0.1, r0.2.1, r0.2.2, r1.1, r1.2.1, r1.2.2, r2.1, r2.2.1, r2.2.2]

/-! ## A map that keeps Kruskal's table is a symmetry near every point -/

/-- The only labels of coordinate space from the third on are the third and the fourth. -/
theorem fin_four_of_two_le : ∀ i : Fin 4, 2 ≤ i.val → i = 2 ∨ i = 3 := by decide

/-- **A map of coordinate space that keeps Kruskal's table is a symmetry of Kruskal's whole
space-time, near every point:** after wrapping round the sphere, it is `kruskalSym L R`. -/
theorem KeepsKruskalOn.local {m : ℝ} {f : Coords 4 → Coords 4} {W : Set (Coords 4)}
    {x₀ : Coords 4} (hm : 0 < m) (h : KeepsKruskalOn m f W) (hx₀ : x₀ ∈ W) :
    ∃ (L : Matrix (Fin 2) (Fin 2) ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ),
      L.transpose * lightSign2 * L = lightSign2 ∧ R.transpose * R = 1 ∧
        ∀ᶠ x in 𝓝 x₀, kruskalWrap (f x) = kruskalSym L R (kruskalWrap x) := by
  have hW : IsOpen W := h.1
  -- the `(T, X)` part
  obtain ⟨L, hL, hplane⟩ := h.plane hm hx₀
  -- the angles: what `sphere_rigid` asks for
  have hfW : ContDiffOn ℝ ∞ f W := fun x hx ↦ (h.2.2.2 x hx).1.contDiffWithinAt
  have hsin : ∀ x ∈ W, sin (x 2) ≠ 0 ∧ sin (f x 2) ≠ 0 := fun x hx ↦
    ⟨(h.2.1 hx).2, (h.2.2.1 x hx).2⟩
  have hsplit : ∀ x ∈ W,
      jac f 2 0 x = 0 ∧ jac f 2 1 x = 0 ∧ jac f 3 0 x = 0 ∧ jac f 3 1 x = 0 := fun x hx ↦
    ⟨h.split hm hx 2 0 (Or.inr ⟨by decide, by decide⟩),
      h.split hm hx 2 1 (Or.inr ⟨by decide, by decide⟩),
      h.split hm hx 3 0 (Or.inr ⟨by decide, by decide⟩),
      h.split hm hx 3 1 (Or.inr ⟨by decide, by decide⟩)⟩
  have hkeep : ∀ x ∈ W, ∀ i j : Fin 4, 2 ≤ i.val → 2 ≤ j.val →
      jac f 2 i x * jac f 2 j x + sin (f x 2) ^ 2 * (jac f 3 i x * jac f 3 j x)
        = if i = j then (if i = 2 then 1 else sin (x 2) ^ 2) else 0 := by
    intro x hx i j hi hj
    have hfd : DifferentiableAt ℝ f x := (h.2.2.2 x hx).1.differentiableAt (by simp)
    have c : ∀ a k : Fin 4, fderiv ℝ f x (Pi.single k 1) a = jac f a k x := fun a k ↦
      (jac_eq_fderiv hfd a k).symm
    have hS : kruskalS m (f x 0) (f x 1) = kruskalS m (x 0) (x 1) := by
      unfold kruskalS
      rw [h.radius hm hx]
    have hSpos : 0 < kruskalS m (x 0) (x 1) := kruskalS_pos hm (h.2.1 hx).1
    -- lengths of the steps along the angles, before and after
    have hcar : tableMeasure (kruskalG m) (f x) (fderiv ℝ f x (Pi.single i 1))
        (fderiv ℝ f x (Pi.single j 1))
          = tableMeasure (kruskalG m) x (Pi.single i 1) (Pi.single j 1) :=
      (h.2.2.2 x hx).2.self_of_nhds (Pi.single i 1) (Pi.single j 1)
    have z0i : jac f 0 i x = 0 := h.split hm hx 0 i (Or.inl ⟨by decide, hi⟩)
    have z0j : jac f 0 j x = 0 := h.split hm hx 0 j (Or.inl ⟨by decide, hj⟩)
    have z1i : jac f 1 i x = 0 := h.split hm hx 1 i (Or.inl ⟨by decide, hi⟩)
    have z1j : jac f 1 j x = 0 := h.split hm hx 1 j (Or.inl ⟨by decide, hj⟩)
    rw [kruskalG_apply, kruskalG_apply, c 0 i, c 0 j, c 1 i, c 1 j, c 2 i, c 2 j, c 3 i,
      c 3 j, z0i, z0j, z1i, z1j, hS] at hcar
    obtain rfl | rfl := fin_four_of_two_le i hi <;> obtain rfl | rfl := fin_four_of_two_le j hj
    · have e : kruskalS m (x 0) (x 1)
          * (jac f 2 2 x * jac f 2 2 x + sin (f x 2) ^ 2 * (jac f 3 2 x * jac f 3 2 x))
          = kruskalS m (x 0) (x 1) * 1 := by
        simp only [Pi.single_apply, Fin.reduceEq, ↓reduceIte] at hcar
        linear_combination hcar
      simpa using mul_left_cancel₀ hSpos.ne' e
    · have e : kruskalS m (x 0) (x 1)
          * (jac f 2 2 x * jac f 2 3 x + sin (f x 2) ^ 2 * (jac f 3 2 x * jac f 3 3 x))
          = kruskalS m (x 0) (x 1) * 0 := by
        simp only [Pi.single_apply, Fin.reduceEq, ↓reduceIte] at hcar
        linear_combination hcar
      simpa using mul_left_cancel₀ hSpos.ne' e
    · have e : kruskalS m (x 0) (x 1)
          * (jac f 2 3 x * jac f 2 2 x + sin (f x 2) ^ 2 * (jac f 3 3 x * jac f 3 2 x))
          = kruskalS m (x 0) (x 1) * 0 := by
        simp only [Pi.single_apply, Fin.reduceEq, ↓reduceIte] at hcar
        linear_combination hcar
      simpa using mul_left_cancel₀ hSpos.ne' e
    · have e : kruskalS m (x 0) (x 1)
          * (jac f 2 3 x * jac f 2 3 x + sin (f x 2) ^ 2 * (jac f 3 3 x * jac f 3 3 x))
          = kruskalS m (x 0) (x 1) * sin (x 2) ^ 2 := by
        simp only [Pi.single_apply, Fin.reduceEq, ↓reduceIte] at hcar
        linear_combination hcar
      simpa using mul_left_cancel₀ hSpos.ne' e
  obtain ⟨R, hR, hsphere⟩ := sphere_rigid hW hx₀ hfW hsin hsplit hkeep
  -- together, entry by entry
  refine ⟨L, R, hL, hR, ?_⟩
  filter_upwards [hplane, hsphere] with x hp hs
  have s0 : sin (f x 2) * cos (f x 3) = R 0 0 * (sin (x 2) * cos (x 3))
      + R 0 1 * (sin (x 2) * sin (x 3)) + R 0 2 * cos (x 2) :=
    (congrFun hs 0).trans (mulVec_three R _ 0)
  have s1 : sin (f x 2) * sin (f x 3) = R 1 0 * (sin (x 2) * cos (x 3))
      + R 1 1 * (sin (x 2) * sin (x 3)) + R 1 2 * cos (x 2) :=
    (congrFun hs 1).trans (mulVec_three R _ 1)
  have s2 : cos (f x 2) = R 2 0 * (sin (x 2) * cos (x 3))
      + R 2 1 * (sin (x 2) * sin (x 3)) + R 2 2 * cos (x 2) :=
    (congrFun hs 2).trans (mulVec_three R _ 2)
  funext i
  fin_cases i
  exacts [hp.1, hp.2, s0, s1, s2]

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coords 4) M]
  [IsManifold 𝓘(ℝ, Coords 4) ∞ M] {m : ℝ} {g : LengthMeasure 𝓘(ℝ, Coords 4) M} {s : Set M}

omit [IsManifold 𝓘(ℝ, Coords 4) ∞ M] in
/-- **Chain rule for a map that is, near a point, a map of coordinate space after another map
into coordinate space.** -/
theorem mfderiv_of_eventuallyEq_comp_coords {ψ φ : M → Coords 4} {F : Coords 4 → Coords 4}
    {q : M} (hF : DifferentiableAt ℝ F (φ q))
    (hφ : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q) (hev : ψ =ᶠ[𝓝 q] F ∘ φ)
    (v : TangentSpace 𝓘(ℝ, Coords 4) q) :
    mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) ψ q v
      = fderiv ℝ F (φ q) (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ q v) := by
  have hF' : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) F (φ q) := hF.mdifferentiableAt
  have h1 : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) (F ∘ φ) q := hF'.comp q hφ
  have h2 : mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) ψ q
      = mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) (F ∘ φ) q :=
    (h1.hasMFDerivAt.congr_of_eventuallyEq_abuse hev).mfderiv
  have h3 : mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) ψ q v
      = mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) (F ∘ φ) q v :=
    congrArg (fun A : Coords 4 →L[ℝ] Coords 4 ↦ A v) h2
  rw [h3, mfderiv_comp_apply q hF' hφ v, mfderiv_eq_fderiv]
  rfl

omit [IsManifold 𝓘(ℝ, Coords 4) ∞ M] in
/-- **The change of charts between two charts that both read `g` as Kruskal's table keeps
Kruskal's table.** -/
theorem keepsKruskalOn_of_charts {φ φ' : OpenPartialHomeomorph M (Coords 4)}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M)
    (hφ' : φ' ∈ IsManifold.maximalAtlas 𝓘(ℝ, Coords 4) ∞ M)
    (h : ∀ p ∈ φ.source, φ p ∈ kruskalRegion ∧ ∀ v w : TangentSpace 𝓘(ℝ, Coords 4) p,
      g p v w = flatMeasure (tableMeasure (kruskalG m)) (φ p)
        (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ p v)
        (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ p w))
    (h' : ∀ p ∈ φ'.source, φ' p ∈ kruskalRegion ∧ ∀ v w : TangentSpace 𝓘(ℝ, Coords 4) p,
      g p v w = flatMeasure (tableMeasure (kruskalG m)) (φ' p)
        (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ' p v)
        (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ' p w)) :
    KeepsKruskalOn m (fun y ↦ φ' (φ.symm y)) (φ.target ∩ φ.symm ⁻¹' φ'.source) := by
  have hW : IsOpen (φ.target ∩ φ.symm ⁻¹' φ'.source) :=
    φ.isOpen_inter_preimage_symm φ'.open_source
  obtain ⟨f, hfdef⟩ : ∃ f : Coords 4 → Coords 4, f = fun y ↦ φ' (φ.symm y) := ⟨_, rfl⟩
  rw [← hfdef]
  have hfy : ∀ y, f y = φ' (φ.symm y) := fun y ↦ by rw [hfdef]
  have hfW : ContDiffOn ℝ ∞ f (φ.target ∩ φ.symm ⁻¹' φ'.source) :=
    (contMDiffOn_iff_contDiffOn.1
      ((contMDiffOn_of_mem_maximalAtlas hφ').comp
        ((contMDiffOn_symm_of_mem_maximalAtlas hφ).mono inter_subset_left)
        fun z hz ↦ hz.2)).congr fun y _ ↦ hfy y
  -- in terms of points `p` of the curved space
  have key : ∀ p ∈ φ.source ∩ φ'.source, ∀ a b : TangentSpace 𝓘(ℝ, Coords 4) p,
      tableMeasure (kruskalG m) (f (φ p))
          (fderiv ℝ f (φ p) (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ p a))
          (fderiv ℝ f (φ p) (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ p b))
        = tableMeasure (kruskalG m) (φ p) (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ p a)
          (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ p b) := by
    intro p hp a b
    have hfp : f (φ p) = φ' p := by rw [hfy, φ.left_inv hp.1]
    have hpW : φ p ∈ φ.target ∩ φ.symm ⁻¹' φ'.source := by
      refine ⟨φ.map_source hp.1, ?_⟩
      rw [mem_preimage, φ.left_inv hp.1]
      exact hp.2
    have hF : DifferentiableAt ℝ f (φ p) :=
      (hfW.contDiffAt (hW.mem_nhds hpW)).differentiableAt (by simp)
    have hφm : MDifferentiableAt 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ p :=
      (contMDiffAt_of_mem_maximalAtlas hφ hp.1).mdifferentiableAt (by simp)
    have hev : (φ' : M → Coords 4) =ᶠ[𝓝 p] f ∘ φ :=
      Filter.eventuallyEq_of_mem (φ.open_source.mem_nhds hp.1) fun p' hp' ↦ by
        change φ' p' = f (φ p')
        rw [hfy, φ.left_inv hp']
    have hchain : ∀ v : TangentSpace 𝓘(ℝ, Coords 4) p,
        fderiv ℝ f (φ p) (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ p v)
          = mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ' p v := fun v ↦
      (mfderiv_of_eventuallyEq_comp_coords hF hφm hev v).symm
    calc tableMeasure (kruskalG m) (f (φ p))
          (fderiv ℝ f (φ p) (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ p a))
          (fderiv ℝ f (φ p) (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ p b))
        = tableMeasure (kruskalG m) (φ' p) (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ' p a)
          (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ' p b) := by rw [hfp, hchain a, hchain b]
      _ = g p a b := ((h' p hp.2).2 a b).symm
      _ = tableMeasure (kruskalG m) (φ p) (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ p a)
          (mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ p b) := (h p hp.1).2 a b
  -- in terms of points `z` of coordinate space
  have key2 : ∀ (p : M) (z : Coords 4), φ p = z → p ∈ φ.source ∩ φ'.source →
      ∀ u v : Coords 4, tableMeasure (kruskalG m) (f z) (fderiv ℝ f z u) (fderiv ℝ f z v)
        = tableMeasure (kruskalG m) z u v := by
    rintro p z rfl hp u v
    obtain ⟨e, he⟩ := Join.chart_isInvertible_mfderiv hφ hp.1
    have hsurj : ∀ w : Coords 4, ∃ a : TangentSpace 𝓘(ℝ, Coords 4) p,
        mfderiv 𝓘(ℝ, Coords 4) 𝓘(ℝ, Coords 4) φ p a = w := fun w ↦
      ⟨e.symm w, by rw [← he]; exact e.apply_symm_apply w⟩
    obtain ⟨a, rfl⟩ := hsurj u
    obtain ⟨b, rfl⟩ := hsurj v
    exact key p hp a b
  refine ⟨hW, fun z hz ↦ ?_, fun z hz ↦ ?_, fun z hz ↦ ⟨hfW.contDiffAt (hW.mem_nhds hz), ?_⟩⟩
  · have hz' := (h (φ.symm z) (φ.map_target hz.1)).1
    rwa [φ.right_inv hz.1] at hz'
  · rw [hfy]
    exact (h' (φ.symm z) hz.2).1
  · exact Filter.eventually_of_mem (hW.mem_nhds hz) fun z' hz' ↦
      key2 (φ.symm z') z' (φ.right_inv hz'.1) ⟨φ.map_target hz'.1, hz'.2⟩

/-- **Two length-keeping maps into Kruskal's differ by a symmetry near every point of the
region.** -/
theorem IsKruskalMapOn.local_unique {D D' : M → Coords 5} (hm : 0 < m)
    (hD : IsKruskalMapOn m g D s) (hD' : IsKruskalMapOn m g D' s) (hg : IsSpaceTimeOn g s)
    {q : M} (hq : q ∈ s) :
    ∃ (L : Matrix (Fin 2) (Fin 2) ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ),
      L.transpose * lightSign2 * L = lightSign2 ∧ R.transpose * R = 1 ∧
        ∀ᶠ q' in 𝓝 q, D' q' = kruskalSym L R (D q') := by
  obtain ⟨R₁, φ, hR₁, hφ, hqφ, -, h⟩ := hD.exists_chart hg hq
  obtain ⟨R₂, φ', hR₂, hφ', hqφ', -, h'⟩ := hD'.exists_chart hg hq
  -- the change of charts keeps Kruskal's table, so it is a symmetry near `φ q`
  have hK := keepsKruskalOn_of_charts hφ hφ' (fun p hp ↦ ⟨(h p hp).1, (h p hp).2.2⟩)
    (fun p hp ↦ ⟨(h' p hp).1, (h' p hp).2.2⟩)
  have hqW : φ q ∈ φ.target ∩ φ.symm ⁻¹' φ'.source := by
    refine ⟨φ.map_source hqφ, ?_⟩
    rw [mem_preimage, φ.left_inv hqφ]
    exact hqφ'
  obtain ⟨L, R₀, hL, hR₀, hloc⟩ := hK.local hm hqW
  have hpull : ∀ᶠ q' in 𝓝 q, kruskalWrap (φ' (φ.symm (φ q')))
      = kruskalSym L R₀ (kruskalWrap (φ q')) := (φ.continuousAt hqφ).eventually hloc
  have hR₁' : R₁.transpose.transpose * R₁.transpose = 1 := by
    rw [Matrix.transpose_transpose]
    exact mul_eq_one_comm.mp hR₁
  refine ⟨L, R₂ * R₀ * R₁.transpose, hL, orthogonal_mul (orthogonal_mul hR₂ hR₀) hR₁', ?_⟩
  filter_upwards [hpull, φ.open_source.mem_nhds hqφ, φ'.open_source.mem_nhds hqφ']
    with q' h1 h2 h3
  -- undo the chart of `D`: the wrapped labels are a turn of `D`
  have hw : kruskalWrap (φ q') = kruskalSym 1 R₁.transpose (D q') := by
    rw [(h q' h2).2.1, kruskalSym_comp, hR₁, one_mul, kruskalSym_one]
  rw [φ.left_inv h2] at h1
  rw [(h' q' h3).2.1, h1, hw, kruskalSym_comp, kruskalSym_comp]
  simp only [one_mul, mul_one, mul_assoc]

/-- **A symmetry is fixed by what it does to a length-keeping map near one point.** -/
theorem IsKruskalMapOn.sym_unique {D : M → Coords 5} (hD : IsKruskalMapOn m g D s)
    (hg : IsSpaceTimeOn g s) {q : M} (hq : q ∈ s)
    {L L' : Matrix (Fin 2) (Fin 2) ℝ} {R R' : Matrix (Fin 3) (Fin 3) ℝ}
    (h : ∀ᶠ q' in 𝓝 q, kruskalSym L R (D q') = kruskalSym L' R' (D q')) : L = L' ∧ R = R' := by
  obtain ⟨R₁, φ, hR₁, hφ, hqφ, -, hφall⟩ := hD.exists_chart hg hq
  -- near `φ q` in coordinate space the two symmetries agree after wrapping
  have hev : (kruskalSym L (R * R₁) ∘ kruskalWrap)
      =ᶠ[𝓝 (φ q)] (kruskalSym L' (R' * R₁) ∘ kruskalWrap) := by
    rw [← φ.map_nhds_eq hqφ]
    refine Filter.eventually_map.2 ?_
    filter_upwards [h, φ.open_source.mem_nhds hqφ] with q' hq' hq'φ
    have e : ∀ (K : Matrix (Fin 2) (Fin 2) ℝ) (S : Matrix (Fin 3) (Fin 3) ℝ),
        kruskalSym K (S * R₁) (kruskalWrap (φ q')) = kruskalSym K S (D q') := fun K S ↦ by
      rw [(hφall q' hq'φ).2.1, kruskalSym_comp, mul_one]
    change kruskalSym L (R * R₁) (kruskalWrap (φ q'))
      = kruskalSym L' (R' * R₁) (kruskalWrap (φ q'))
    rw [e, e]
    exact hq'
  -- so they agree on the wrapped point and on all wrapped steps from it
  have h0 : kruskalSym L (R * R₁) (kruskalWrap (φ q))
      = kruskalSym L' (R' * R₁) (kruskalWrap (φ q)) := hev.self_of_nhds
  have hd : ∀ u : Coords 4, kruskalSym L (R * R₁) (fderiv ℝ kruskalWrap (φ q) u)
      = kruskalSym L' (R' * R₁) (fderiv ℝ kruskalWrap (φ q) u) := by
    intro u
    have e := congrArg (fun A : Coords 4 →L[ℝ] Coords 5 ↦ A u) hev.fderiv_eq
    rw [← fderiv_kruskalSym_wrap, ← fderiv_kruskalSym_wrap]
    exact e
  obtain ⟨hLL, hRR⟩ := kruskalSym_eq_of_frame (hφall q hqφ).1.2 h0 hd
  have hR₁' : R₁ * R₁.transpose = 1 := mul_eq_one_comm.mp hR₁
  refine ⟨hLL, ?_⟩
  calc R = R * R₁ * R₁.transpose := by rw [Matrix.mul_assoc, hR₁', Matrix.mul_one]
    _ = R' * R₁ * R₁.transpose := by rw [hRR]
    _ = R' := by rw [Matrix.mul_assoc, hR₁', Matrix.mul_one]

/-- **Two length-keeping maps into Kruskal's on a region in one piece differ by one symmetry:**
the first part of `GlobalBirkhoffUnique`. -/
theorem unique_kruskal (hs : IsPreconnected s) (hg : IsSpaceTimeOn g s) (hm : 0 < m)
    (D D' : M → Coords 5) (hD : IsKruskalMapOn m g D s) (hD' : IsKruskalMapOn m g D' s) :
    ∃ (L : Matrix (Fin 2) (Fin 2) ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ),
      L.transpose * lightSign2 * L = lightSign2 ∧ R.transpose * R = 1 ∧
        ∀ q ∈ s, D' q = kruskalSym L R (D q) := by
  by_cases hne : s.Nonempty
  swap
  · exact ⟨1, 1, by simp, by simp, fun q hq ↦ (hne ⟨q, hq⟩).elim⟩
  obtain ⟨q₀, hq₀⟩ := hne
  obtain ⟨L, R, hL, hR, h₀⟩ := hD.local_unique hm hD' hg hq₀
  refine ⟨L, R, hL, hR, ?_⟩
  -- the points near which the symmetry is `(L, R)`, and those near which it is another one
  have hu : IsOpen {q : M | ∀ᶠ q' in 𝓝 q, D' q' = kruskalSym L R (D q')} :=
    isOpen_setOfPred_eventually_nhds
  have hv : IsOpen {q : M | ∃ (L' : Matrix (Fin 2) (Fin 2) ℝ) (R' : Matrix (Fin 3) (Fin 3) ℝ),
      (L', R') ≠ (L, R) ∧ ∀ᶠ q' in 𝓝 q, D' q' = kruskalSym L' R' (D q')} := by
    rw [isOpen_iff_mem_nhds]
    rintro q ⟨L', R', hne', hq⟩
    filter_upwards [hq.eventually_nhds] with q' hq'
    exact ⟨L', R', hne', hq'⟩
  have hsuv : s ⊆ {q : M | ∀ᶠ q' in 𝓝 q, D' q' = kruskalSym L R (D q')}
      ∪ {q : M | ∃ (L' : Matrix (Fin 2) (Fin 2) ℝ) (R' : Matrix (Fin 3) (Fin 3) ℝ),
        (L', R') ≠ (L, R) ∧ ∀ᶠ q' in 𝓝 q, D' q' = kruskalSym L' R' (D q')} := by
    intro q hq
    obtain ⟨L', R', -, -, hq'⟩ := hD.local_unique hm hD' hg hq
    by_cases e : (L', R') = (L, R)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      exact Or.inl hq'
    · exact Or.inr ⟨L', R', e, hq'⟩
  -- a point near which both hold would have two symmetries
  have hsub : s ⊆ {q : M | ∀ᶠ q' in 𝓝 q, D' q' = kruskalSym L R (D q')} := by
    by_contra hcon
    obtain ⟨q, hq, hqu⟩ := Set.not_subset.1 hcon
    obtain ⟨q₁, hq₁, hq₁u, L', R', hne', hq₁v⟩ :=
      hs _ _ hu hv hsuv ⟨q₀, hq₀, h₀⟩ ⟨q, hq, (hsuv hq).resolve_left hqu⟩
    have hboth : ∀ᶠ q' in 𝓝 q₁, kruskalSym L R (D q') = kruskalSym L' R' (D q') := by
      filter_upwards [hq₁u, hq₁v] with q' e1 e2
      rw [← e1, ← e2]
    obtain ⟨e1, e2⟩ := hD.sym_unique hg hq₁ hboth
    exact hne' (by rw [e1, e2])
  exact fun q hq ↦ (hsub hq).self_of_nhds

end GravityInLean.Curved
