/-
Copyright (c) 2026 flujo-app. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: flujo-app
-/
module

public import GravityInLean.Connection.Tensorial1
public import GravityInLean.Connection.Tensorial3
public import GravityInLean.Connection.Sharp

import Mathlib.Geometry.Manifold.Notation
import Mathlib.Tactic

/-!
# The connection that Koszul's expression names

Board item `task:checks-connection-candidate`. Part of the proof that every length measure has a
connection. This file defines the candidate, `koszulCov g`, and proves the one fact about it from
which the other files work (`koszulCov_spec`): for fields `X`, `Y`, `Z` that can be
differentiated at a point of the region, twice "the change of `Y` along `X`, measured against
`Z`" is Koszul's expression.

How the candidate is found. Koszul's expression depends on `X` and `Z` only through the steps
`X x` and `Z x` (`Tensorial1.lean`, `Tensorial3.lean`), so for fixed `Y` it is a two-slot
function of steps at `x`. Because no step is at right angles to all steps, such a function is
"apply a linear map to the first step, then measure against the second" for exactly one linear
map (`Sharp.lean`). Half of that linear map is the change of `Y` at `x`.
-/

@[expose] public section

namespace GravityInLean.Curved

open Bundle FiberBundle VectorField

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : LengthMeasure I M} {s : Set M} {x : M}

open Classical in
/-- **The candidate for the connection of `g`.** The change of the field `Y` at `x` is the linear
map `A` on steps for which twice `g(A v, w)` is Koszul's expression, for all steps `v`, `w`
(extended to fields in the standard library's way). If there is no such map, the change is zero;
`exists_koszulCov` shows that there is one wherever it matters. -/
noncomputable def koszulCov (g : LengthMeasure I M) : Transport I M := fun Y x ↦
  if h : ∃ A : TangentSpace I x →L[ℝ] TangentSpace I x, ∀ v w : TangentSpace I x,
      2 * g x (A v) w = koszulExpr g (extend E v) Y (extend E w) x
  then Classical.choose h else 0

/-- **Koszul's expression sees its outer fields only through their steps at the point:** the
fields `X` and `Z` may be replaced by the standard extensions of the steps `X x` and `Z x`. -/
theorem koszulExpr_extend (hg : IsLengthMeasureOn g s) (hs : IsOpen s) (hx : x ∈ s)
    {X Y Z : Arrows I M} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    koszulExpr g (extend E (X x)) Y (extend E (Z x)) x = koszulExpr g X Y Z x :=
  TensorialAt.pointwise₂ (Φ := fun X Z ↦ koszulExpr g X Y Z x)
    (fun _ hZ' ↦ tensorialAt_koszulExpr_first hg hs hx hY hZ')
    (fun _ hX' ↦ tensorialAt_koszulExpr_third hg hs hx hX' hY)
    (mdifferentiableAt_extend I E (X x)) hX (mdifferentiableAt_extend I E (Z x)) hZ
    (extend_apply_self E (X x)) (extend_apply_self E (Z x))

/-- **There is a linear map that Koszul's expression names**, at every point of the region and
for every field `Y` that can be differentiated there. -/
theorem exists_koszulCov (hg : IsLengthMeasureOn g s) (hs : IsOpen s) (hx : x ∈ s)
    {Y : Arrows I M} (hY : MDiffAt (T% Y) x) :
    ∃ A : TangentSpace I x →L[ℝ] TangentSpace I x, ∀ v w : TangentSpace I x,
      2 * g x (A v) w = koszulExpr g (extend E v) Y (extend E w) x := by
  have : FiniteDimensional ℝ (TangentSpace I x) :=
    (tangentSpaceCastModel I x).symm.toLinearEquiv.finiteDimensional
  -- Koszul's expression for fixed `Y`, as a two-slot function of steps at `x`.
  let B : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    TensorialAt.mkHom₂ (fun X Z ↦ koszulExpr g X Y Z x) x
      (fun _ hZ ↦ tensorialAt_koszulExpr_first hg hs hx hY hZ)
      (fun _ hX ↦ tensorialAt_koszulExpr_third hg hs hx hX hY)
  have hB : ∀ v w : TangentSpace I x, B v w = koszulExpr g (extend E v) Y (extend E w) x :=
    fun v w ↦ TensorialAt.mkHom₂_apply_eq_extend _ _ v w
  -- Turn "measure against the second step" back into a step, and take half of it.
  let A₀ : TangentSpace I x →ₗ[ℝ] TangentSpace I x := (1 / 2 : ℝ) • (sharp (g x) ∘ₗ flat B)
  refine ⟨LinearMap.toContinuousLinearMap A₀, fun v w ↦ ?_⟩
  have h1 : g x (sharp (g x) (flat B v)) w = B v w :=
    sharp_apply (g x) (hg.nondegenerate x hx) (flat B v) w
  have h2 : LinearMap.toContinuousLinearMap A₀ v = (1 / 2 : ℝ) • sharp (g x) (flat B v) := rfl
  have h3 : g x ((1 / 2 : ℝ) • sharp (g x) (flat B v)) w
      = (1 / 2 : ℝ) * g x (sharp (g x) (flat B v)) w := by
    rw [map_smul]
    rfl
  rw [h2, h3, h1, hB v w]
  ring

/-- **What the candidate does, for two steps:** twice the change of `Y` along the step `v`,
measured against the step `w`, is Koszul's expression for the standard extensions. -/
theorem koszulCov_spec_extend (hg : IsLengthMeasureOn g s) (hs : IsOpen s) (hx : x ∈ s)
    {Y : Arrows I M} (hY : MDiffAt (T% Y) x) (v w : TangentSpace I x) :
    2 * g x (koszulCov g Y x v) w = koszulExpr g (extend E v) Y (extend E w) x := by
  have h := exists_koszulCov hg hs hx hY
  have e : koszulCov g Y x = Classical.choose h := dite_eq_left h
  rw [e]
  exact Classical.choose_spec h v w

/-- **What the candidate does, for three fields** (Koszul's formula, now as the definition):
twice the change of `Y` along `X`, measured against `Z`, is Koszul's expression. -/
theorem koszulCov_spec (hg : IsLengthMeasureOn g s) (hs : IsOpen s) (hx : x ∈ s)
    {X Y Z : Arrows I M} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    2 * g x (koszulCov g Y x (X x)) (Z x) = koszulExpr g X Y Z x :=
  (koszulCov_spec_extend hg hs hx hY (X x) (Z x)).trans (koszulExpr_extend hg hs hx hX hY hZ)

end GravityInLean.Curved
