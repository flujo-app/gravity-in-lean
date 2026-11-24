/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Turns.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct

import Mathlib.Tactic

/-!
# Two functions that vanish where the middle field rests

Board item `task:turns-rest-map`. For three fields `η 0`, `η 1`, `η 2` (maps from points to
arrows of four numbers), `restMap η q` is the pair of ordinary dot products of `η 1 q` with
`η 0 q` and with `η 2 q`. Where `η 1` is zero, both are zero; `Surface.lean` shows the converse
near a point and uses the zero set as the surface. This file shows that `restMap η` is smooth,
what its slope is at a point where `η 1` is zero, and that the Gram determinant of `η 0`, `η 2`
is continuous.
-/

@[expose] public section

namespace GravityInLean.Turns

open Set Metric Topology Matrix

open scoped ContDiff

/-- The pair of dot products of the middle field with the two outer ones. -/
def restMap (η : Fin 3 → Coords 4 → Coords 4) (q : Coords 4) : ℝ × ℝ :=
  (η 0 q ⬝ᵥ η 1 q, η 2 q ⬝ᵥ η 1 q)

variable {η : Fin 3 → Coords 4 → Coords 4} {s : Set (Coords 4)} {p : Coords 4}

/-- The dot product of two smooth fields is a smooth function. -/
theorem contDiffOn_dot {X Y : Coords 4 → Coords 4} (hX : ContDiffOn ℝ ∞ X s)
    (hY : ContDiffOn ℝ ∞ Y s) : ContDiffOn ℝ ∞ (fun q ↦ X q ⬝ᵥ Y q) s := by
  unfold dotProduct
  exact ContDiffOn.sum fun k _ ↦ ((contDiffOn_pi.mp hX) k).mul ((contDiffOn_pi.mp hY) k)

/-- The dot product of two fields that have a slope at `p` has a slope at `p`. -/
theorem differentiableAt_dot {X Y : Coords 4 → Coords 4} (hX : DifferentiableAt ℝ X p)
    (hY : DifferentiableAt ℝ Y p) : DifferentiableAt ℝ (fun q ↦ X q ⬝ᵥ Y q) p := by
  unfold dotProduct
  exact DifferentiableAt.fun_sum fun k _ ↦
    ((differentiableAt_pi.mp hX) k).mul ((differentiableAt_pi.mp hY) k)

/-- The product rule for the dot product of two fields: its slope along `v` is the first field
dotted with the slope of the second, plus the second dotted with the slope of the first. -/
theorem fderiv_dot_apply {X Y : Coords 4 → Coords 4} (hX : DifferentiableAt ℝ X p)
    (hY : DifferentiableAt ℝ Y p) (v : Coords 4) :
    fderiv ℝ (fun q ↦ X q ⬝ᵥ Y q) p v =
      X p ⬝ᵥ fderiv ℝ Y p v + Y p ⬝ᵥ fderiv ℝ X p v := by
  have h : HasFDerivAt (fun q ↦ ∑ k, X q k * Y q k) _ p :=
    HasFDerivAt.fun_sum fun k _ ↦
      ((hasFDerivAt_pi'.mp hX.hasFDerivAt) k).mul ((hasFDerivAt_pi'.mp hY.hasFDerivAt) k)
  have h' : fderiv ℝ (fun q ↦ X q ⬝ᵥ Y q) p = _ := h.fderiv
  rw [h']
  simp [dotProduct, sum_apply, Finset.sum_add_distrib]

/-- The pair of dot products is smooth where the fields are. -/
theorem contDiffOn_restMap (hη : ∀ i, ContDiffOn ℝ ∞ (η i) s) :
    ContDiffOn ℝ ∞ (restMap η) s :=
  (contDiffOn_dot (hη 0) (hη 1)).prodMk (contDiffOn_dot (hη 2) (hη 1))

/-- At a point where the middle field is zero, the slope of the pair of dot products along `v`
is the pair of dot products of the outer fields with the slope of the middle field along `v`. -/
theorem fderiv_restMap (hd : ∀ i, DifferentiableAt ℝ (η i) p) (h1 : η 1 p = 0) (v : Coords 4) :
    fderiv ℝ (restMap η) p v =
      (η 0 p ⬝ᵥ fderiv ℝ (η 1) p v, η 2 p ⬝ᵥ fderiv ℝ (η 1) p v) := by
  have h : fderiv ℝ (restMap η) p = (fderiv ℝ (fun q ↦ η 0 q ⬝ᵥ η 1 q) p).prod
      (fderiv ℝ (fun q ↦ η 2 q ⬝ᵥ η 1 q) p) :=
    (differentiableAt_dot (hd 0) (hd 1)).fderiv_prodMk (differentiableAt_dot (hd 2) (hd 1))
  rw [h, ContinuousLinearMap.prod_apply, fderiv_dot_apply (hd 0) (hd 1),
    fderiv_dot_apply (hd 2) (hd 1), h1]
  simp

/-- The Gram determinant of the two outer fields is continuous where the fields are smooth. -/
theorem continuousOn_gram (hη : ∀ i, ContDiffOn ℝ ∞ (η i) s) :
    ContinuousOn (fun q ↦ (η 0 q ⬝ᵥ η 0 q) * (η 2 q ⬝ᵥ η 2 q) - (η 0 q ⬝ᵥ η 2 q) ^ 2) s :=
  ((contDiffOn_dot (hη 0) (hη 0)).continuousOn.mul (contDiffOn_dot (hη 2) (hη 2)).continuousOn).sub
    ((contDiffOn_dot (hη 0) (hη 2)).continuousOn.pow 2)

end GravityInLean.Turns
