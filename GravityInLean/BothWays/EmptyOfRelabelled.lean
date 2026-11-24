/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.BothWays.OffRim
public import GravityInLean.Goals.ExactlyWhen

import Mathlib.Tactic

/-!
# From "Schwarzschild's after new labels" to "empty"

Board item `task:bothways-coords-backward`. One direction of Birkhoff's theorem in coordinates,
said both ways (`BirkhoffExactlyWhenInCoordinates`): a round table that is Schwarzschild's after
new labels for time and distance is empty.

The argument computes no curvature.

* `relabelled_eq_inNewCoords`: the lengths of all steps agree and both tables are symmetric, so
  the table *is* Schwarzschild's table written in the new labels, entry by entry, on the region.
* `contDiffAt_relabel`: the change of labels is smooth, because the new time and the radius are.
* `empty_of_relabelled`: Schwarzschild's table is empty in any coordinates, off the rim
  (`schwarzschild_ricciFlat_inNewCoords_offRim`), and "empty at a point" only depends on the
  table near the point.

The condition in `IsSchwarzschildRelabelled` that the table of slopes of the two new labels can
be inverted is not used: it follows from the rest, since the table `g` has an inverse.
-/

@[expose] public section

namespace GravityInLean

open Real Filter Topology Set

open scoped ContDiff

/-- A symmetric table that gives every step the length that a round table gives the same step
after new labels `T`, `R` for time and distance is that round table written in the new labels,
entry by entry. -/
theorem relabelled_eq_inNewCoords {g : Fin 4 → Fin 4 → Coords 4 → ℝ} {A B : ℝ → ℝ}
    {T R : ℝ → ℝ → ℝ} {x : Coords 4} (hsymm : ∀ i j, g i j x = g j i x)
    (hlen : ∀ v : Coords 4, stepLength g x v
      = stepLength (roundG A B) (relabel T R x) (relabelStep T R x v)) (i j : Fin 4) :
    g i j x = inNewCoords (relabel T R) (roundG A B) i j x := by
  refine eq_of_stepLength_eq hsymm
    (fun a b => inNewCoords_symm (fun α β => roundG_symm _ _ α β _) a b) (fun v => ?_) i j
  rw [stepLength_inNewCoords, hlen v]
  congr 1
  funext α
  exact relabelStep_eq_jac T R x v α

/-- A change of the labels for time and distance is smooth of every order at a point of the
region, when the two new labels are smooth functions of time and distance on the region. -/
theorem contDiffAt_relabel {T R : ℝ → ℝ → ℝ} {J I : Set ℝ} (hJ : IsOpen J) (hI : IsOpen I)
    (hT : ContDiffOn ℝ ∞ (Function.uncurry T) (J ×ˢ I))
    (hR : ContDiffOn ℝ ∞ (Function.uncurry R) (J ×ˢ I)) {x : Coords 4} (h0 : x 0 ∈ J)
    (h1 : x 1 ∈ I) (α : Fin 4) : ContDiffAt ℝ ∞ (fun z => relabel T R z α) x := by
  have p : ∀ k : Fin 4, ContDiffAt ℝ ∞ (fun z : Coords 4 => z k) x :=
    fun k => contDiffAt_apply ℝ (fun _ : Fin 4 => ℝ) k x
  have hpair : ContDiffAt ℝ ∞ (fun y : Coords 4 => (y 0, y 1)) x := (p 0).prodMk (p 1)
  have hmem : J ×ˢ I ∈ 𝓝 (x 0, x 1) := (hJ.prod hI).mem_nhds ⟨h0, h1⟩
  have hTx : ContDiffAt ℝ ∞ (Function.uncurry T) (x 0, x 1) := hT.contDiffAt hmem
  have hRx : ContDiffAt ℝ ∞ (Function.uncurry R) (x 0, x 1) := hR.contDiffAt hmem
  have c0 : ContDiffAt ℝ ∞ (fun y : Coords 4 => T (y 0) (y 1)) x :=
    ContDiffAt.comp (g := Function.uncurry T) x hTx hpair
  have c1 : ContDiffAt ℝ ∞ (fun y : Coords 4 => R (y 0) (y 1)) x :=
    ContDiffAt.comp (g := Function.uncurry R) x hRx hpair
  fin_cases α
  · exact c0
  · exact c1
  · exact p 2
  · exact p 3

/-- **Schwarzschild's after new labels is empty.** A round table (`RoundSetting`) that is
Schwarzschild's after new labels for time and distance (`IsSchwarzschildRelabelled`) makes space
empty at every point of the region. -/
theorem empty_of_relabelled {g ginv : Fin 4 → Fin 4 → Coords 4 → ℝ} {J I : Set ℝ}
    (h : RoundSetting g ginv J I) (hS : IsSchwarzschildRelabelled g J I) :
    ∀ x, InRegion J I x → IsRicciFlatAt g ginv x := by
  obtain ⟨M, T, hT, hR, hall⟩ := hS
  intro x hx
  -- Near `x`, every point is in the region.
  have hnear : ∀ᶠ y in 𝓝 x, InRegion J I y :=
    (isOpen_inRegion h.openJ h.openI).mem_nhds hx
  -- On the region the table is Schwarzschild's table written in the new labels.
  have hentry : ∀ y, InRegion J I y → ∀ i j,
      g i j y = inNewCoords (relabel T (radius (sizeOf g))) (roundG (schwA M) (schwB M)) i j y :=
    fun y hy i j => relabelled_eq_inNewCoords (h.symm y hy) (hall y hy).2.2 i j
  have heq : ∀ i j,
      inNewCoords (relabel T (radius (sizeOf g))) (roundG (schwA M) (schwB M)) i j
        =ᶠ[𝓝 x] g i j :=
    fun i j => hnear.mono fun y hy => (hentry y hy i j).symm
  -- The change of labels is smooth at `x`.
  have hΦ : ∀ α, ContDiffAt ℝ 3 (fun z => relabel T (radius (sizeOf g)) z α) x :=
    fun α => (contDiffAt_relabel h.openJ h.openI hT hR hx.1 hx.2.1 α).of_le
      (by norm_num : (3 : WithTop ℕ∞) ≤ ∞)
  -- It lands at a positive radius, off the rim and off the poles.
  have hr : 0 < relabel T (radius (sizeOf g)) x 1 := by
    have hpos : 0 < sizeOf g (x 0) (x 1) :=
      (h.spaceTime _ (onEquator_inRegion hx.1 hx.2.1)).1
    have e : relabel T (radius (sizeOf g)) x 1 = √(sizeOf g (x 0) (x 1)) := by
      simp [relabel, radius]
    rw [e]
    exact Real.sqrt_pos.mpr hpos
  have hrim : relabel T (radius (sizeOf g)) x 1 ≠ 2 * M := by
    have e : relabel T (radius (sizeOf g)) x 1 = radius (sizeOf g) (x 0) (x 1) := by
      simp [relabel]
    rw [e]
    exact (hall x hx).2.1
  have hs : sin (relabel T (radius (sizeOf g)) x 2) ≠ 0 := by
    have e : relabel T (radius (sizeOf g)) x 2 = x 2 := by simp [relabel]
    rw [e]
    exact hx.sin_ne
  -- The inverse of the table is an inverse of Schwarzschild's table in the new labels.
  have hinv' : ∀ᶠ y in 𝓝 x, ∀ μ κ,
      ∑ ν, inNewCoords (relabel T (radius (sizeOf g))) (roundG (schwA M) (schwB M)) μ ν y
          * ginv ν κ y
        = if μ = κ then 1 else 0 :=
    hnear.mono fun y hy μ κ => by
      rw [← h.inverse y hy μ κ]
      exact Finset.sum_congr rfl fun ν _ => by rw [hentry y hy μ ν]
  have hflat := schwarzschild_ricciFlat_inNewCoords_offRim M hΦ hr hrim hs hinv'
  exact (isRicciFlatAt_congr heq (fun _ _ => EventuallyEq.rfl)).mp hflat

end GravityInLean
