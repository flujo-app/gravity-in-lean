/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Rim.RadiusSmooth
public import GravityInLean.Rim.NullForm
public import GravityInLean.Rim.NullKruskal
public import GravityInLean.BirkhoffGeneral
public import GravityInLean.Potential

import Mathlib.Tactic

/-!
# The core in two labels: an empty round shape of positive mass is Kruskal's

Board item `task:rim-core`. Steps 8 to 12 of the route, said for functions of time and
distance alone. Four smooth functions `A`, `B`, `C`, `S` on a box, in the setting of the general
theorem (`SettingG`), solve the equations of empty space, and the mass function has the positive
value `m` at the point `(t₀, ρ₀)`. Then near that point there are two new labels `T` and `X`,
smooth functions of time and distance, in which the time-distance part is Kruskal's:
`-A dt² + 2 C dt dρ + B dρ² = kruskalA m T X · (-dT² + dX²)`, and `S` is Kruskal's `r²`.
Nothing is asked of the slope of `S`: the point may be on the rim.
-/

@[expose] public section

namespace GravityInLean

open Set

open scoped ContDiff

namespace Rim

open Curved

/-- A function of time and distance that is differentiable at a point has its time slope there,
the distance held fixed. -/
theorem hasDerivAt_dt_of_differentiableAt {u : ℝ → ℝ → ℝ} {t ρ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry u) (t, ρ)) :
    HasDerivAt (fun s ↦ u s ρ) (dt u t ρ) t :=
  (hasDerivAt_along_t h).differentiableAt.hasDerivAt

/-- A function of time and distance that is differentiable at a point has its distance slope
there, the time held fixed. -/
theorem hasDerivAt_dr_of_differentiableAt {u : ℝ → ℝ → ℝ} {t ρ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry u) (t, ρ)) :
    HasDerivAt (fun s ↦ u t s) (dr u t ρ) ρ :=
  (hasDerivAt_along_r h).differentiableAt.hasDerivAt

/-- **Chain rule for two new labels, in time.** If `T` is `T'` read at the labels `u`, `v`, its
time slope is the slope of `T'` in its first label times the time slope of `u`, plus the slope
of `T'` in its second label times the time slope of `v`. -/
theorem dt_comp_labels {T T' u v : ℝ → ℝ → ℝ} (hT : ∀ t ρ, T t ρ = T' (u t ρ) (v t ρ))
    {t ρ : ℝ} (hT' : DifferentiableAt ℝ (Function.uncurry T') (u t ρ, v t ρ))
    (hu : DifferentiableAt ℝ (Function.uncurry u) (t, ρ))
    (hv : DifferentiableAt ℝ (Function.uncurry v) (t, ρ)) :
    dt T t ρ = dt T' (u t ρ) (v t ρ) * dt u t ρ + dr T' (u t ρ) (v t ρ) * dt v t ρ := by
  have e : (fun s ↦ T s ρ) = fun s ↦ T' (u s ρ) (v s ρ) := funext fun s ↦ hT s ρ
  change deriv (fun s ↦ T s ρ) t = _
  rw [e]
  exact (hasDerivAt_comp_path (a := fun s ↦ u s ρ) (b := fun s ↦ v s ρ) hT'
    (hasDerivAt_dt_of_differentiableAt hu) (hasDerivAt_dt_of_differentiableAt hv)).deriv

/-- **Chain rule for two new labels, in distance.** As `dt_comp_labels`, with the distance
slopes of `u` and `v`. -/
theorem dr_comp_labels {T T' u v : ℝ → ℝ → ℝ} (hT : ∀ t ρ, T t ρ = T' (u t ρ) (v t ρ))
    {t ρ : ℝ} (hT' : DifferentiableAt ℝ (Function.uncurry T') (u t ρ, v t ρ))
    (hu : DifferentiableAt ℝ (Function.uncurry u) (t, ρ))
    (hv : DifferentiableAt ℝ (Function.uncurry v) (t, ρ)) :
    dr T t ρ = dt T' (u t ρ) (v t ρ) * dr u t ρ + dr T' (u t ρ) (v t ρ) * dr v t ρ := by
  have e : (fun s ↦ T t s) = fun s ↦ T' (u t s) (v t s) := funext fun s ↦ hT t s
  change deriv (fun s ↦ T t s) ρ = _
  rw [e]
  exact (hasDerivAt_comp_path (a := fun s ↦ u t s) (b := fun s ↦ v t s) hT'
    (hasDerivAt_dr_of_differentiableAt hu) (hasDerivAt_dr_of_differentiableAt hv)).deriv

/-- **The core in two labels.** An empty round shape whose mass function is `m > 0` at a point
is, near that point, Kruskal's of mass `m` in new labels `T`, `X` for time and distance. -/
theorem kruskal_core {A B C S : ℝ → ℝ → ℝ} {J I : Set ℝ} (hset : SettingG A B C S J I)
    (hE : IsEmptyOnG A B C S J I)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (J ×ˢ I))
    (hB : ContDiffOn ℝ ∞ (Function.uncurry B) (J ×ˢ I))
    (hC : ContDiffOn ℝ ∞ (Function.uncurry C) (J ×ˢ I))
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (J ×ˢ I))
    {t₀ ρ₀ : ℝ} (ht₀ : t₀ ∈ J) (hρ₀ : ρ₀ ∈ I) {m : ℝ} (hm : m = massFn A B C S t₀ ρ₀)
    (hmpos : 0 < m) :
    ∃ (T X : ℝ → ℝ → ℝ) (N : Set (ℝ × ℝ)), IsOpen N ∧ (t₀, ρ₀) ∈ N ∧ N ⊆ J ×ˢ I ∧
      ContDiffOn ℝ ∞ (Function.uncurry T) N ∧ ContDiffOn ℝ ∞ (Function.uncurry X) N ∧
      ∀ x ∈ N, -1 < X x.1 x.2 ^ 2 - T x.1 x.2 ^ 2 ∧
        kruskalS m (T x.1 x.2) (X x.1 x.2) = S x.1 x.2 ∧
        A x.1 x.2 = kruskalA m (T x.1 x.2) (X x.1 x.2)
          * (dt T x.1 x.2 ^ 2 - dt X x.1 x.2 ^ 2) ∧
        C x.1 x.2 = kruskalA m (T x.1 x.2) (X x.1 x.2)
          * (dt X x.1 x.2 * dr X x.1 x.2 - dt T x.1 x.2 * dr T x.1 x.2) ∧
        B x.1 x.2 = kruskalA m (T x.1 x.2) (X x.1 x.2)
          * (dr X x.1 x.2 ^ 2 - dr T x.1 x.2 ^ 2) := by
  -- labels along the paths of light, and the shape in them
  obtain ⟨u, v, N, F, S', J', I', hNo, hN0, hNsub, hu, hv, hset', hE', hF, hS', hrel⟩ :=
    exists_nullForm hset hE hA hB hC hS ht₀ hρ₀
  have hrel' : ∀ t ρ, (t, ρ) ∈ N → u t ρ ∈ J' ∧ v t ρ ∈ I' ∧
      S t ρ = S' (u t ρ) (v t ρ) ∧
      A t ρ = -2 * F (u t ρ) (v t ρ) * (dt u t ρ * dt v t ρ) ∧
      C t ρ = F (u t ρ) (v t ρ) * (dt u t ρ * dr v t ρ + dr u t ρ * dt v t ρ) ∧
      B t ρ = 2 * F (u t ρ) (v t ρ) * (dr u t ρ * dr v t ρ) ∧
      massFn zero2 zero2 F S' (u t ρ) (v t ρ) = massFn A B C S t ρ :=
    fun t ρ hx ↦ hrel (t, ρ) hx
  obtain ⟨ha₀, hb₀, -, -, -, -, hm₀⟩ := hrel' t₀ ρ₀ hN0
  -- the mass function of the new shape is `m` on its whole box
  have hmass : ∀ a ∈ J', ∀ b ∈ I', massFn zero2 zero2 F S' a b = m := fun a ha b hb ↦
    (massFn_const hset' hE' a ha _ ha₀ b hb _ hb₀).trans (hm₀.trans hm.symm)
  -- Kruskal's labels as functions of the labels along the paths of light
  obtain ⟨T', X', hT', hX', hK⟩ := kruskal_core_null hset' hE' hF hS' hmpos hmass ha₀ hb₀
  obtain ⟨T, hT⟩ : ∃ T : ℝ → ℝ → ℝ, ∀ t ρ, T t ρ = T' (u t ρ) (v t ρ) := ⟨_, fun _ _ ↦ rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℝ → ℝ → ℝ, ∀ t ρ, X t ρ = X' (u t ρ) (v t ρ) := ⟨_, fun _ _ ↦ rfl⟩
  have hmaps : MapsTo (fun x : ℝ × ℝ ↦ (Function.uncurry u x, Function.uncurry v x)) N
      (J' ×ˢ I') := fun x hx ↦ ⟨(hrel x hx).1, (hrel x hx).2.1⟩
  have hTs : ContDiffOn ℝ ∞ (Function.uncurry T) N :=
    (hT'.comp (hu.prodMk hv) hmaps).congr fun x _ ↦ hT x.1 x.2
  have hXs : ContDiffOn ℝ ∞ (Function.uncurry X) N :=
    (hX'.comp (hu.prodMk hv) hmaps).congr fun x _ ↦ hX x.1 x.2
  have hbox : IsOpen (J' ×ˢ I') := hset'.openJ.prod hset'.openI
  -- at every point: the chain rule, then Kruskal's form of the new shape
  have key : ∀ t ρ, (t, ρ) ∈ N → -1 < X t ρ ^ 2 - T t ρ ^ 2 ∧
      kruskalS m (T t ρ) (X t ρ) = S t ρ ∧
      A t ρ = kruskalA m (T t ρ) (X t ρ) * (dt T t ρ ^ 2 - dt X t ρ ^ 2) ∧
      C t ρ = kruskalA m (T t ρ) (X t ρ) * (dt X t ρ * dr X t ρ - dt T t ρ * dr T t ρ) ∧
      B t ρ = kruskalA m (T t ρ) (X t ρ) * (dr X t ρ ^ 2 - dr T t ρ ^ 2) := by
    intro t ρ hx
    obtain ⟨ha, hb, hSeq, hAeq, hCeq, hBeq, -⟩ := hrel' t ρ hx
    obtain ⟨k1, k2, k3, k4, k5⟩ := hK _ ha _ hb
    have hud : DifferentiableAt ℝ (Function.uncurry u) (t, ρ) :=
      (hu.contDiffAt (hNo.mem_nhds hx)).differentiableAt (by simp)
    have hvd : DifferentiableAt ℝ (Function.uncurry v) (t, ρ) :=
      (hv.contDiffAt (hNo.mem_nhds hx)).differentiableAt (by simp)
    have hTd : DifferentiableAt ℝ (Function.uncurry T') (u t ρ, v t ρ) :=
      (hT'.contDiffAt (hbox.mem_nhds ⟨ha, hb⟩)).differentiableAt (by simp)
    have hXd : DifferentiableAt ℝ (Function.uncurry X') (u t ρ, v t ρ) :=
      (hX'.contDiffAt (hbox.mem_nhds ⟨ha, hb⟩)).differentiableAt (by simp)
    rw [hT t ρ, hX t ρ, dt_comp_labels hT hTd hud hvd, dt_comp_labels hX hXd hud hvd,
      dr_comp_labels hT hTd hud hvd, dr_comp_labels hX hXd hud hvd]
    refine ⟨k1, k2.trans hSeq.symm, ?_, ?_, ?_⟩
    · linear_combination hAeq - 2 * dt u t ρ * dt v t ρ * k4
        - kruskalA m (T' (u t ρ) (v t ρ)) (X' (u t ρ) (v t ρ)) * dt u t ρ ^ 2 * k3
        + kruskalA m (T' (u t ρ) (v t ρ)) (X' (u t ρ) (v t ρ)) * dt v t ρ ^ 2 * k5
    · linear_combination hCeq + (dt u t ρ * dr v t ρ + dr u t ρ * dt v t ρ) * k4
        + kruskalA m (T' (u t ρ) (v t ρ)) (X' (u t ρ) (v t ρ)) * dt u t ρ * dr u t ρ * k3
        - kruskalA m (T' (u t ρ) (v t ρ)) (X' (u t ρ) (v t ρ)) * dt v t ρ * dr v t ρ * k5
    · linear_combination hBeq + 2 * dr u t ρ * dr v t ρ * k4
        + kruskalA m (T' (u t ρ) (v t ρ)) (X' (u t ρ) (v t ρ)) * dr u t ρ ^ 2 * k3
        - kruskalA m (T' (u t ρ) (v t ρ)) (X' (u t ρ) (v t ρ)) * dr v t ρ ^ 2 * k5
  exact ⟨T, X, N, hNo, hN0, hNsub, hTs, hXs, fun x hx ↦ key x.1 x.2 hx⟩

end Rim

end GravityInLean
