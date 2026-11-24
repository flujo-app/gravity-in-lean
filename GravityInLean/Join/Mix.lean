/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Goals.Turns
public import GravityInLean.SameSymmetry
public import GravityInLean.SameSpacetime

import Mathlib.Tactic

/-!
# A fixed mix of fields that leave a table unchanged leaves it unchanged

Board item `task:join-mix` (part B, step 4 of the route to `birkhoffNoCoordinates`).

`turnsCoordinates` gives new coordinates in which the three standard turns are a fixed mix
(a rotation `R`) of the three given fields `ξ`. This file draws the consequence for the table of
functions `g`: written in the new coordinates, it is left unchanged by the three standard turns.

* `lieD_mix`: the change of a table along a field is linear in the field, for fixed numbers.
* `leavesUnchangedAt_mix`: so a fixed mix of fields that leave the table unchanged leaves it
  unchanged.
* `isRoundAt_inNewCoords`: the table in the new coordinates of `turnsCoordinates` looks the same
  from every side (`IsRoundAt`) at every point of the patch.

Only coordinates are used here; no curved spaces.
-/

@[expose] public section

namespace GravityInLean.Join

open Real Filter Topology

open scoped ContDiff

/-- The slope of a fixed mix of functions is the same mix of their slopes. -/
theorem slope_mix {n : ℕ} {ι : Type*} [Fintype ι] {f : ι → Coords n → ℝ} {x : Coords n}
    (c : ι → ℝ) (hd : ∀ j, DifferentiableAt ℝ (f j) x) (i : Fin n) :
    slope i (fun y ↦ ∑ j, c j * f j y) x = ∑ j, c j * slope i (f j) x := by
  have hc : ∀ j, DifferentiableAt ℝ (fun _ : Coords n ↦ c j) x := fun j ↦ differentiableAt_const _
  have h0 : ∀ j, slope i (fun _ : Coords n ↦ c j) x = 0 := fun j ↦ by simp [slope]
  rw [slope_sum (F := fun j y ↦ c j * f j y) (fun j ↦ (hc j).mul (hd j)) i]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [slope_mul (hc j) (hd j) i, h0 j, zero_mul, zero_add]

/-- **The change of a table along a field is linear in the field.** Along a fixed mix
`∑ j, c j * ξ j` of fields the table changes by the same mix of its changes along each `ξ j`.
The parts of the fields must be differentiable at the point. -/
theorem lieD_mix {n : ℕ} {ι : Type*} [Fintype ι] {g : Fin n → Fin n → Coords n → ℝ}
    {ξ : ι → Fin n → Coords n → ℝ} {x : Coords n} (c : ι → ℝ)
    (hd : ∀ j k, DifferentiableAt ℝ (ξ j k) x) (a b : Fin n) :
    lieD g (fun k y ↦ ∑ j, c j * ξ j k y) a b x = ∑ j, c j * lieD g (ξ j) a b x := by
  have hs : ∀ i k, slope i (fun y ↦ ∑ j, c j * ξ j k y) x = ∑ j, c j * slope i (ξ j k) x :=
    fun i k ↦ slope_mix c (fun j ↦ hd j k) i
  have hk : ∀ k, (∑ j, c j * ξ j k x) * slope k (g a b) x
        + g k b x * (∑ j, c j * slope a (ξ j k) x) + g a k x * (∑ j, c j * slope b (ξ j k) x)
      = ∑ j, c j * (ξ j k x * slope k (g a b) x + g k b x * slope a (ξ j k) x
          + g a k x * slope b (ξ j k) x) := by
    intro k
    rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  calc lieD g (fun k y ↦ ∑ j, c j * ξ j k y) a b x
      = ∑ k, ∑ j, c j * (ξ j k x * slope k (g a b) x + g k b x * slope a (ξ j k) x
          + g a k x * slope b (ξ j k) x) := by
        simp only [lieD, hs]
        exact Finset.sum_congr rfl fun k _ ↦ hk k
    _ = ∑ j, ∑ k, c j * (ξ j k x * slope k (g a b) x + g k b x * slope a (ξ j k) x
          + g a k x * slope b (ξ j k) x) := Finset.sum_comm
    _ = ∑ j, c j * lieD g (ξ j) a b x := by
        simp only [lieD, Finset.mul_sum]

/-- **A fixed mix of fields that leave a table unchanged leaves it unchanged.** If each of the
fields `ξ j` leaves the table `g` unchanged at `x` (Killing's equation), then so does
`∑ j, c j * ξ j` for fixed numbers `c j`. -/
theorem leavesUnchangedAt_mix {g : Fin 4 → Fin 4 → Coords 4 → ℝ}
    {ξ : Fin 3 → Fin 4 → Coords 4 → ℝ} {x : Coords 4} (c : Fin 3 → ℝ)
    (hd : ∀ j k, DifferentiableAt ℝ (ξ j k) x) (h : ∀ j, LeavesUnchangedAt g (ξ j) x) :
    LeavesUnchangedAt g (fun k y ↦ ∑ j, c j * ξ j k y) x := by
  intro a b
  rw [lieD_mix c hd a b]
  exact Finset.sum_eq_zero fun j _ ↦ by rw [h j a b, mul_zero]

/-- The first standard turn in the list `stdTurn` is `rotY`. -/
theorem stdTurn_zero : stdTurn 0 = rotY := rfl

/-- The second standard turn in the list `stdTurn` is `rotX`. -/
theorem stdTurn_one : stdTurn 1 = rotX := rfl

/-- The third standard turn in the list `stdTurn` is `rotZ`. -/
theorem stdTurn_two : stdTurn 2 = rotZ := rfl

/-- **In the coordinates that fit the turns, the table looks the same from every side.** Take a
good table `g` on a region `s` with three fields that turn, and new coordinates `Φ` on an open
patch `W` as `turnsCoordinates` gives them: smooth, into `s`, losing no direction, off the
poles, and turning each standard turn into a fixed mix `∑ j, R i j * ξ j` of the three fields.
Then the table written in the new coordinates, `inNewCoords Φ g`, is left unchanged by the
three turns `rotX`, `rotY`, `rotZ` at every point of `W`. -/
theorem isRoundAt_inNewCoords {g ginv : Fin 4 → Fin 4 → Coords 4 → ℝ}
    {ξ : Fin 3 → Fin 4 → Coords 4 → ℝ} {s : Set (Coords 4)}
    (hg : Curved.IsRegularTableOn g ginv s) (hξ : TurnsOn g ξ s)
    {Φ : Coords 4 → Coords 4} {R : Matrix (Fin 3) (Fin 3) ℝ} {W : Set (Coords 4)}
    (hW : IsOpen W) (hΦs : ∀ y ∈ W, Φ y ∈ s) (hΦ : ContDiffOn ℝ ∞ Φ W)
    (hdet : ∀ y ∈ W, sin (y 2) ≠ 0 ∧ (tab (jac Φ) y).det ≠ 0)
    (hturn : ∀ y ∈ W, ∀ i α, ∑ μ, jac Φ α μ y * stdTurn i μ y = ∑ j, R i j * ξ j α (Φ y)) :
    ∀ y ∈ W, IsRoundAt (inNewCoords Φ g) y := by
  intro y hy
  have hWy : W ∈ 𝓝 y := hW.mem_nhds hy
  have hsin : sin (y 2) ≠ 0 := (hdet y hy).1
  have hys : Φ y ∈ s := hΦs y hy
  -- The given fields can be differentiated at the old point.
  have hξd : ∀ j k, DifferentiableAt ℝ (ξ j k) (Φ y) := fun j k ↦
    ((hξ.smooth j k).contDiffAt (hg.isOpen.mem_nhds hys)).differentiableAt (by simp)
  -- The change of coordinates is twice smoothly differentiable.
  have hΦ2 : ∀ α, ContDiffAt ℝ 2 (fun z ↦ Φ z α) y := fun α ↦
    ((contDiffAt_pi.1 (hΦ.contDiffAt hWy)) α).of_le (by norm_num)
  -- One standard turn at a time.
  have key : ∀ i, (∀ μ, DifferentiableAt ℝ (stdTurn i μ) y) →
      LeavesUnchangedAt (inNewCoords Φ g) (stdTurn i) y := by
    intro i hi
    refine (leavesUnchangedAt_inNewCoords (ξ := fun α z ↦ ∑ j, R i j * ξ j α z) hΦ2
      (fun α β ↦ hg.differentiableAt hys α β) ?_ hi ?_ (hdet y hy).2).2
      (leavesUnchangedAt_mix (R i) hξd fun j ↦ hξ.unchanged j _ hys)
    · intro α
      exact DifferentiableAt.fun_sum fun j _ ↦ (hξd j α).const_mul (R i j)
    · filter_upwards [hWy] with z hz α using hturn z hz i α
  have h0 := key 0 (by rw [stdTurn_zero]; exact differentiableAt_rotY hsin)
  have h1 := key 1 (by rw [stdTurn_one]; exact differentiableAt_rotX hsin)
  have h2 := key 2 (by rw [stdTurn_two]; exact differentiableAt_rotZ y)
  rw [stdTurn_zero] at h0
  rw [stdTurn_one] at h1
  rw [stdTurn_two] at h2
  exact ⟨h1, h0, h2⟩

end GravityInLean.Join
