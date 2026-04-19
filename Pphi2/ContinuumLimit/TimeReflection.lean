/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Continuum Time Reflection

Time reflection on Schwartz test functions and tempered distributions over
`ℝ²`, packaged independently of the continuum-limit inheritance proofs.
-/

import Pphi2.ContinuumLimit.Convergence

noncomputable section

namespace Pphi2

open GaussianField

/-- Time reflection as a linear map on ℝ²: (t,x) ↦ (-t,x). -/
private def timeReflLinear : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun p := (WithLp.equiv 2 (Fin 2 → ℝ)).symm (fun i =>
    if i = (0 : Fin 2) then -(WithLp.equiv 2 (Fin 2 → ℝ) p i) else WithLp.equiv 2 (Fin 2 → ℝ) p i)
  map_add' p q := by ext i; simp [WithLp.equiv]; split <;> ring
  map_smul' c p := by ext i; simp [WithLp.equiv, smul_eq_mul]

private lemma timeReflLinear_involutive : Function.Involutive timeReflLinear := by
  intro p; ext i; simp [timeReflLinear, WithLp.equiv]; split <;> ring

private noncomputable def timeReflCLE : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (LinearEquiv.ofInvolutive timeReflLinear timeReflLinear_involutive).toContinuousLinearEquiv

noncomputable def continuumTimeReflection :
    ContinuumTestFunction 2 →L[ℝ] ContinuumTestFunction 2 :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ timeReflCLE

/-- Evaluation of `continuumTimeReflection`: negates the 0th coordinate.
`(Θf)(p) = f((-p₀, p₁, ...))`. -/
@[simp]
theorem continuumTimeReflection_apply_coord (f : ContinuumTestFunction 2)
    (p : EuclideanSpace ℝ (Fin 2)) :
    (continuumTimeReflection f) p =
    f ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (fun i =>
      if i = (0 : Fin 2) then -(WithLp.equiv 2 (Fin 2 → ℝ) p i)
      else WithLp.equiv 2 (Fin 2 → ℝ) p i)) := by
  simp [continuumTimeReflection, timeReflCLE, timeReflLinear,
    SchwartzMap.compCLMOfContinuousLinearEquiv, LinearEquiv.ofInvolutive]

/-- Time reflection on distributions (the dual action).

For `ω ∈ S'(ℝ²)`, `(Θ*ω)(f) = ω(Θf)` where `Θf(t,x) = f(-t,x)`.
This is the composition of the continuous linear functional ω with the
time reflection CLM on Schwartz space. -/
def distribTimeReflection :
    Configuration (ContinuumTestFunction 2) →
    Configuration (ContinuumTestFunction 2) :=
  fun ω => ω.comp continuumTimeReflection

/-- `distribTimeReflection` evaluation: `(Θ*ω)(f) = ω(Θf)`. -/
@[simp]
theorem distribTimeReflection_apply
    (ω : Configuration (ContinuumTestFunction 2))
    (f : ContinuumTestFunction 2) :
    distribTimeReflection ω f = ω (continuumTimeReflection f) := rfl

/-- `distribTimeReflection` is continuous on Configuration space.

Each evaluation `(distribTimeReflection ω) f = ω (continuumTimeReflection f)`
is continuous in ω (it's `WeakDual.eval_continuous` at the fixed test function
`continuumTimeReflection f`). Continuity of `distribTimeReflection` follows
from the universal property of the weak-* topology. -/
theorem distribTimeReflection_continuous :
    Continuous distribTimeReflection := by
  apply WeakDual.continuous_of_continuous_eval
  intro f
  change Continuous (fun ω : GaussianField.Configuration (ContinuumTestFunction 2) =>
    (distribTimeReflection ω) f)
  simp only [distribTimeReflection_apply]
  exact WeakDual.eval_continuous (continuumTimeReflection f)

end Pphi2

end
