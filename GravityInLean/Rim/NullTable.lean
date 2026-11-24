/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Join.Patch
public import GravityInLean.Join.NewTable

import Mathlib.Tactic

/-!
# A change of the two labels keeps the setting and "empty"

Board item `task:rim-null-table`. Take the general round shape
`-A dt² + 2 C dt dρ + B dρ² + S (dθ² + sin²θ dφ²)` and write time and distance as smooth
functions of two new labels: `t = τ(a, b)`, `ρ = ϱ(a, b)`. The time-distance part becomes
`-pullA da² + 2 pullC da db + pullB db²`, and the size of the spheres becomes `pullS`.

`nullTable`: if the old four functions are in the setting of the general theorem, solve the
equations of empty space and are smooth, and the change of labels is a genuine one (its table of
slopes has a determinant that is not zero), then the same holds for the four new functions.

On paper: the determinant of the new time-distance part is the old one times the square of the
determinant of the slopes. The change of coordinates `relabel τ ϱ` of coordinate space turns the
old table into the new one (entries from the lengths of steps), and "empty" does not depend on
the coordinates.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GravityInLean.Rim

open GravityInLean.Join

open Real Filter Topology Set

open scoped ContDiff

/-- The new clock function: `-A dt² + 2 C dt dρ + B dρ²` gives the step `da` the squared length
`-pullA`. -/
noncomputable def pullA (A B C τ ϱ : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  A (τ a b) (ϱ a b) * dt τ a b ^ 2 - 2 * C (τ a b) (ϱ a b) * (dt τ a b * dt ϱ a b)
    - B (τ a b) (ϱ a b) * dt ϱ a b ^ 2

/-- The new cross term: what `-A dt² + 2 C dt dρ + B dρ²` gives to the pair of steps `da`,
`db`. -/
noncomputable def pullC (A B C τ ϱ : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  -A (τ a b) (ϱ a b) * (dt τ a b * dr τ a b)
    + C (τ a b) (ϱ a b) * (dt τ a b * dr ϱ a b + dr τ a b * dt ϱ a b)
    + B (τ a b) (ϱ a b) * (dt ϱ a b * dr ϱ a b)

/-- The new ruler function: `-A dt² + 2 C dt dρ + B dρ²` gives the step `db` the squared length
`pullB`. -/
noncomputable def pullB (A B C τ ϱ : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  -A (τ a b) (ϱ a b) * dr τ a b ^ 2 + 2 * C (τ a b) (ϱ a b) * (dr τ a b * dr ϱ a b)
    + B (τ a b) (ϱ a b) * dr ϱ a b ^ 2

/-- The size of the spheres, as a function of the new labels. -/
noncomputable def pullS (S τ ϱ : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ := S (τ a b) (ϱ a b)

/-- The points of coordinate space with time in `J`, distance label in `I`, off the poles, form
an open set when `J` and `I` are open. -/
theorem isOpen_offPoles {J I : Set ℝ} (hJ : IsOpen J) (hI : IsOpen I) :
    IsOpen {y : Coords 4 | y 0 ∈ J ∧ y 1 ∈ I ∧ sin (y 2) ≠ 0} := by
  have h0 : IsOpen {y : Coords 4 | y 0 ∈ J} := hJ.preimage (continuous_apply 0)
  have h1 : IsOpen {y : Coords 4 | y 1 ∈ I} := hI.preimage (continuous_apply 1)
  have h2 : IsOpen {y : Coords 4 | sin (y 2) ≠ 0} :=
    isOpen_ne_fun (Real.continuous_sin.comp (continuous_apply 2)) continuous_const
  exact h0.inter (h1.inter h2)

/-- **The general round shape in new labels is the general round shape of the pulled parts.**
The change of coordinates `relabel τ ϱ` of coordinate space turns the table of `A`, `B`, `C`,
`S` into the table of `pullA`, `pullB`, `pullC`, `pullS`. Nothing is assumed: both tables give
every step the same length. -/
theorem inNewCoords_relabel_genG (A B C S τ ϱ : ℝ → ℝ → ℝ) :
    inNewCoords (relabel τ ϱ) (genG A B C S)
      = genG (pullA A B C τ ϱ) (pullB A B C τ ϱ) (pullC A B C τ ϱ) (pullS S τ ϱ) := by
  funext i j y
  refine eq_of_stepLength_eq
    (fun i j => inNewCoords_symm (fun α β => genG_symm A B C S α β _) i j)
    (fun i j => genG_symm _ _ _ _ i j y) (fun v => ?_) i j
  have e3 : (fun α => ∑ μ, jac (relabel τ ϱ) α μ y * v μ) = relabelStep τ ϱ y v :=
    funext fun α => (relabelStep_eq_jac τ ϱ y v α).symm
  have r0 : relabel τ ϱ y 0 = τ (y 0) (y 1) := rfl
  have r1 : relabel τ ϱ y 1 = ϱ (y 0) (y 1) := rfl
  have r2 : relabel τ ϱ y 2 = y 2 := rfl
  have s0 : relabelStep τ ϱ y v 0 = dt τ (y 0) (y 1) * v 0 + dr τ (y 0) (y 1) * v 1 := rfl
  have s1 : relabelStep τ ϱ y v 1 = dt ϱ (y 0) (y 1) * v 0 + dr ϱ (y 0) (y 1) * v 1 := rfl
  have s2 : relabelStep τ ϱ y v 2 = v 2 := rfl
  have s3 : relabelStep τ ϱ y v 3 = v 3 := rfl
  rw [stepLength_inNewCoords, e3, stepLength_gen, stepLength_gen, r0, r1, r2, s0, s1, s2, s3]
  simp only [pullA, pullB, pullC, pullS]
  ring

/-- The determinant of the new time-distance part is the old one times the square of the
determinant of the slopes of the change of labels. -/
theorem det2_pull (A B C τ ϱ : ℝ → ℝ → ℝ) (a b : ℝ) :
    det2 (pullA A B C τ ϱ) (pullB A B C τ ϱ) (pullC A B C τ ϱ) a b
      = det2 A B C (τ a b) (ϱ a b) * (dt τ a b * dr ϱ a b - dr τ a b * dt ϱ a b) ^ 2 := by
  simp only [det2, pullA, pullB, pullC]
  ring

/-- **A change of the two labels keeps the setting and "empty".** Four smooth functions in the
setting of the general theorem that solve the equations of empty space, written in two new
labels by a smooth, genuine change of labels, are again in the setting, solve the equations of
empty space, and are smooth. -/
theorem nullTable {A B C S τ ϱ : ℝ → ℝ → ℝ} {J I J' I' : Set ℝ}
    (hset : SettingG A B C S J I) (hE : IsEmptyOnG A B C S J I)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (J ×ˢ I))
    (hB : ContDiffOn ℝ ∞ (Function.uncurry B) (J ×ˢ I))
    (hC : ContDiffOn ℝ ∞ (Function.uncurry C) (J ×ˢ I))
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (J ×ˢ I))
    (hJ' : IsOpen J') (hJ'c : IsPreconnected J') (hI' : IsOpen I') (hI'c : IsPreconnected I')
    (hτ : ContDiffOn ℝ ∞ (Function.uncurry τ) (J' ×ˢ I'))
    (hϱ : ContDiffOn ℝ ∞ (Function.uncurry ϱ) (J' ×ˢ I'))
    (hmaps : ∀ a ∈ J', ∀ b ∈ I', τ a b ∈ J ∧ ϱ a b ∈ I)
    (hdet : ∀ a ∈ J', ∀ b ∈ I', dt τ a b * dr ϱ a b - dr τ a b * dt ϱ a b ≠ 0) :
    SettingG (pullA A B C τ ϱ) (pullB A B C τ ϱ) (pullC A B C τ ϱ) (pullS S τ ϱ) J' I' ∧
    IsEmptyOnG (pullA A B C τ ϱ) (pullB A B C τ ϱ) (pullC A B C τ ϱ) (pullS S τ ϱ) J' I' ∧
    ContDiffOn ℝ ∞ (Function.uncurry (pullA A B C τ ϱ)) (J' ×ˢ I') ∧
    ContDiffOn ℝ ∞ (Function.uncurry (pullB A B C τ ϱ)) (J' ×ˢ I') ∧
    ContDiffOn ℝ ∞ (Function.uncurry (pullC A B C τ ϱ)) (J' ×ˢ I') ∧
    ContDiffOn ℝ ∞ (Function.uncurry (pullS S τ ϱ)) (J' ×ˢ I') := by
  have hU' : IsOpen (J' ×ˢ I') := hJ'.prod hI'
  -- The four new functions are smooth: old functions after the change of labels, times slopes.
  have hmapsTo : MapsTo (fun q : ℝ × ℝ => (τ q.1 q.2, ϱ q.1 q.2)) (J' ×ˢ I') (J ×ˢ I) :=
    fun q hq => ⟨(hmaps _ hq.1 _ hq.2).1, (hmaps _ hq.1 _ hq.2).2⟩
  have hpair : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => (τ q.1 q.2, ϱ q.1 q.2)) (J' ×ˢ I') :=
    hτ.prodMk hϱ
  have cA : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => A (τ q.1 q.2) (ϱ q.1 q.2)) (J' ×ˢ I') :=
    hA.comp hpair hmapsTo
  have cB : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => B (τ q.1 q.2) (ϱ q.1 q.2)) (J' ×ˢ I') :=
    hB.comp hpair hmapsTo
  have cC : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => C (τ q.1 q.2) (ϱ q.1 q.2)) (J' ×ˢ I') :=
    hC.comp hpair hmapsTo
  have cS : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => S (τ q.1 q.2) (ϱ q.1 q.2)) (J' ×ˢ I') :=
    hS.comp hpair hmapsTo
  have τt : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => dt τ q.1 q.2) (J' ×ˢ I') := contDiffOn_dt hU' hτ
  have τr : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => dr τ q.1 q.2) (J' ×ˢ I') := contDiffOn_dr hU' hτ
  have ϱt : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => dt ϱ q.1 q.2) (J' ×ˢ I') := contDiffOn_dt hU' hϱ
  have ϱr : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => dr ϱ q.1 q.2) (J' ×ˢ I') := contDiffOn_dr hU' hϱ
  have c2 : ContDiffOn ℝ ∞ (fun _ : ℝ × ℝ => (2 : ℝ)) (J' ×ˢ I') := contDiffOn_const
  have hA' : ContDiffOn ℝ ∞ (Function.uncurry (pullA A B C τ ϱ)) (J' ×ˢ I') :=
    ((cA.mul (τt.pow 2)).sub ((c2.mul cC).mul (τt.mul ϱt))).sub (cB.mul (ϱt.pow 2))
  have hC' : ContDiffOn ℝ ∞ (Function.uncurry (pullC A B C τ ϱ)) (J' ×ˢ I') :=
    ((cA.neg.mul (τt.mul τr)).add (cC.mul ((τt.mul ϱr).add (τr.mul ϱt)))).add
      (cB.mul (ϱt.mul ϱr))
  have hB' : ContDiffOn ℝ ∞ (Function.uncurry (pullB A B C τ ϱ)) (J' ×ˢ I') :=
    ((cA.neg.mul (τr.pow 2)).add ((c2.mul cC).mul (τr.mul ϱr))).add (cB.mul (ϱr.pow 2))
  have hS' : ContDiffOn ℝ ∞ (Function.uncurry (pullS S τ ϱ)) (J' ×ˢ I') := cS
  -- The setting: the new determinant is the old one times a square that is not zero.
  have hset' : SettingG (pullA A B C τ ϱ) (pullB A B C τ ϱ) (pullC A B C τ ϱ) (pullS S τ ϱ)
      J' I' :=
    { openJ := hJ'
      onePieceJ := hJ'c
      openI := hI'
      onePieceI := hI'c
      smoothA := fun a ha b hb =>
        (hA'.contDiffAt (hU'.mem_nhds (mk_mem_prod ha hb))).of_le (by norm_num)
      smoothB := fun a ha b hb =>
        (hB'.contDiffAt (hU'.mem_nhds (mk_mem_prod ha hb))).of_le (by norm_num)
      smoothC := fun a ha b hb =>
        (hC'.contDiffAt (hU'.mem_nhds (mk_mem_prod ha hb))).of_le (by norm_num)
      smoothS := fun a ha b hb =>
        (hS'.contDiffAt (hU'.mem_nhds (mk_mem_prod ha hb))).of_le (by norm_num)
      spaceTime := fun a ha b hb => by
        rw [det2_pull]
        exact mul_pos (hset.spaceTime _ (hmaps a ha b hb).1 _ (hmaps a ha b hb).2)
          (sq_pos_iff.mpr (hdet a ha b hb))
      S_pos := fun a ha b hb => hset.S_pos _ (hmaps a ha b hb).1 _ (hmaps a ha b hb).2 }
  -- Empty: the new table is the old one in the coordinates `relabel τ ϱ`, and "empty" does not
  -- depend on the coordinates.
  have hE' : IsEmptyOnG (pullA A B C τ ϱ) (pullB A B C τ ϱ) (pullC A B C τ ϱ) (pullS S τ ϱ)
      J' I' := by
    intro x hx0 hx1 hxs
    have hV := isOpen_offPoles hJ' hI'
    have hxV : x ∈ {y : Coords 4 | y 0 ∈ J' ∧ y 1 ∈ I' ∧ sin (y 2) ≠ 0} := ⟨hx0, hx1, hxs⟩
    have hΦ : ContDiffOn ℝ ∞ (relabel τ ϱ)
        {y : Coords 4 | y 0 ∈ J' ∧ y 1 ∈ I' ∧ sin (y 2) ≠ 0} :=
      contDiffOn_relabel hτ hϱ (fun y hy => ⟨hy.1, hy.2.1⟩)
    have h0 : relabel τ ϱ x 0 ∈ J := (hmaps _ hx0 _ hx1).1
    have h1 : relabel τ ϱ x 1 ∈ I := (hmaps _ hx0 _ hx1).2
    have h2 : sin (relabel τ ϱ x 2) ≠ 0 := hxs
    have hΦxV : relabel τ ϱ x ∈ {y : Coords 4 | y 0 ∈ J ∧ y 1 ∈ I ∧ sin (y 2) ≠ 0} :=
      ⟨h0, h1, h2⟩
    have hflat : IsRicciFlatAt (genG A B C S) (genGinv A B C S) (relabel τ ϱ x) :=
      hE _ h0 h1 h2
    have hg : ∀ α β, ContDiffAt ℝ 2 (genG A B C S α β) (relabel τ ϱ x) := fun α β =>
      contDiffAt_genG (hset.smoothA _ h0 _ h1) (hset.smoothB _ h0 _ h1) (hset.smoothC _ h0 _ h1)
        (hset.smoothS _ h0 _ h1) α β
    have hsymm : ∀ᶠ z in 𝓝 (relabel τ ϱ x), ∀ α β, genG A B C S α β z = genG A B C S β α z :=
      Filter.Eventually.of_forall fun z α β => genG_symm A B C S α β z
    have hinv : ∀ᶠ z in 𝓝 (relabel τ ϱ x), ∀ α γ,
        ∑ β, genG A B C S α β z * genGinv A B C S β γ z = if α = γ then 1 else 0 :=
      ((isOpen_offPoles hset.openJ hset.openI).eventually_mem hΦxV).mono fun z hz α γ =>
        genG_mul_genGinv (hset.spaceTime _ hz.1 _ hz.2.1).ne' (hset.S_pos _ hz.1 _ hz.2.1).ne'
          hz.2.2 α γ
    have hinv' : ∀ᶠ y in 𝓝 x, ∀ μ κ,
        ∑ ν, inNewCoords (relabel τ ϱ) (genG A B C S) μ ν y
          * genGinv (pullA A B C τ ϱ) (pullB A B C τ ϱ) (pullC A B C τ ϱ) (pullS S τ ϱ) ν κ y
          = if μ = κ then 1 else 0 :=
      (hV.eventually_mem hxV).mono fun y hy μ κ => by
        rw [inNewCoords_relabel_genG]
        exact genG_mul_genGinv (hset'.spaceTime _ hy.1 _ hy.2.1).ne'
          (hset'.S_pos _ hy.1 _ hy.2.1).ne' hy.2.2 μ κ
    rw [← inNewCoords_relabel_genG]
    exact (isRicciFlatAt_inNewCoords (patch_contDiffAt_three hV hΦ hxV) hg hsymm hinv hinv').mpr
      hflat
  exact ⟨hset', hE', hA', hB', hC', hS'⟩

end GravityInLean.Rim
