/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Connection.Candidate
public import GravityInLean.Connection.Middle

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# The candidate is a connection

Board item `task:checks-connection-isconnection`. Part of the proof that every length measure
has a connection. The candidate `koszulCov g` obeys the two rules of a connection of the standard
library (`IsCovariantDerivativeOn`): the sum rule and the product rule. Both are read off from
the same rules for Koszul's expression (`Middle.lean`), measured against every step, because a
step is known once its measure against every step is known.
-/

@[expose] public section

namespace GravityInLean.Curved

open Bundle FiberBundle VectorField

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : LengthMeasure I M} {s : Set M} {x : M}

/-- **The candidate is a connection** on an open region where `g` is a length measure: it obeys
the sum rule and the product rule. -/
theorem isCovariantDerivativeOn_koszulCov (hg : IsLengthMeasureOn g s) (hs : IsOpen s) :
    IsCovariantDerivativeOn E (koszulCov g) s where
  add {Y Y' x} hY hY' hx := by
    -- two linear maps on steps are equal if they agree on every step `v`, and two steps are
    -- equal if they measure the same against every step `w`
    ext v
    apply hg.eq_of_forall_measure_eq hx
    intro w
    have hv := mdifferentiableAt_extend I E v
    have hw := mdifferentiableAt_extend I E w
    have h1 := koszulCov_spec_extend hg hs hx (mdifferentiableAt_add_section hY hY') v w
    have h2 := koszulCov_spec_extend hg hs hx hY v w
    have h3 := koszulCov_spec_extend hg hs hx hY' v w
    have h4 := koszulExpr_add_middle hg hs hx hv hY hY' hw
    have e : g x ((koszulCov g Y x + koszulCov g Y' x) v) w
        = g x (koszulCov g Y x v) w + g x (koszulCov g Y' x v) w := by
      rw [add_apply, map_add, add_apply]
    rw [e]
    linarith
  leibniz {Y f x} hY hf hx := by
    ext v
    apply hg.eq_of_forall_measure_eq hx
    intro w
    have hv := mdifferentiableAt_extend I E v
    have hw := mdifferentiableAt_extend I E w
    have h1 := koszulCov_spec_extend hg hs hx (hf.smul_section hY) v w
    have h2 := koszulCov_spec_extend hg hs hx hY v w
    have h4 := koszulExpr_smul_middle hg hs hx hv hY hw hf
    rw [extend_apply_self, extend_apply_self] at h4
    have e : g x ((f x • koszulCov g Y x + (d% f x).smulRight (Y x)) v) w
        = f x * g x (koszulCov g Y x v) w + d% f x v * g x (Y x) w := by
      rw [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, map_add, add_apply,
        map_smul, map_smul, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
    rw [e]
    linear_combination (1 / 2) * h1 + (1 / 2) * h4 - (f x / 2) * h2

end GravityInLean.Curved
