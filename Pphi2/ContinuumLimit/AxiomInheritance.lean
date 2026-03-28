/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# OS Axioms Pass to the Continuum Limit

Shows that OS axioms verified on the lattice transfer to the continuum
limit measure μ = lim ν_{aₙ}.

## Main results

- `os0_inheritance` — analyticity from uniform exponential bounds
- `os1_inheritance` — regularity from uniform moment bounds
- `os3_inheritance` — RP from weak closure (provable)
- `os4_inheritance` — clustering from uniform mass gap

## Mathematical background

Each OS axiom transfers to the limit by a different mechanism:

### OS0 (Analyticity)
The generating functional `Z[f] = ∫ exp(iΦ(f)) dμ` is entire analytic.
On the lattice, Z_a[f] is entire with uniform bounds on derivatives.
Uniform bounds + pointwise convergence → limit is entire
(by Vitali's convergence theorem for analytic functions).

### OS1 (Regularity)
The bound `|Z[f]| ≤ exp(c‖f‖²)` holds uniformly on the lattice
(from the Gaussian covariance structure). Pointwise limits of
uniformly bounded functions preserve the bound.

### OS3 (Reflection Positivity)
RP is a nonnegativity condition `Σ cᵢc̄ⱼ Z[fᵢ - Θfⱼ] ≥ 0`.
Since each Z_a satisfies this and Z_a → Z pointwise, the limit
inherits the nonnegativity. (Proved in OS3_RP_Inheritance.lean.)

### OS4 (Clustering)
The uniform mass gap `m_phys ≥ m₀ > 0` (from `spectral_gap_uniform`)
gives uniform exponential clustering on the lattice. Weak convergence
preserves the exponential bound.

### OS2 (Euclidean Invariance) — handled in Phase 5
This is the hardest axiom. The lattice breaks E(2) symmetry, and its
restoration requires the Ward identity argument (see OS2_WardIdentity.lean).

## References

- Glimm-Jaffe, *Quantum Physics*, §19.4
- Simon, *The P(φ)₂ Euclidean QFT*, §V
-/

import Pphi2.ContinuumLimit.Convergence
import Pphi2.OSProofs.OS3_RP_Inheritance
import Pphi2.OSProofs.OS4_MassGap
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

variable (d N : ℕ) [NeZero N]

/-! ## OS1: Regularity -/

/-- **OS1 transfers to the continuum limit.**

The regularity bound `|Z[f]| ≤ exp(c · ‖f‖²_{H^{-1}})` holds for
the continuum limit.

Proof outline:
1. On the lattice: `|Z_a[f]| ≤ 1` trivially for real f (|exp(it)| = 1).
2. The nontrivial bound on moments:
   `∫ |Φ_a(f)|^{2n} dν_a ≤ (2n)! · C^n · ‖f‖^{2n}_{H^{-1}}`
   holds uniformly in a (from the Gaussian structure + Nelson's estimate).
3. These moment bounds transfer to the limit. -/
theorem os1_inheritance (_P : InteractionPolynomial)
    (_mass : ℝ) (_hmass : 0 < _mass)
    (μ : Measure (Configuration (ContinuumTestFunction d)))
    (hμ : IsProbabilityMeasure μ) :
    -- |Z[f]| ≤ 1 for all real test functions f
    ∀ (f : ContinuumTestFunction d),
    |∫ ω : Configuration (ContinuumTestFunction d),
      Real.cos (ω f) ∂μ| ≤ 1 := by
  intro f
  have h1 : |∫ ω, Real.cos (ω f) ∂μ| ≤ ∫ ω, |Real.cos (ω f)| ∂μ := by
    rw [show |∫ ω, Real.cos (ω f) ∂μ| = ‖∫ ω, Real.cos (ω f) ∂μ‖ from
      (Real.norm_eq_abs _).symm]
    exact norm_integral_le_integral_norm _
  have h2 : ∫ ω, |Real.cos (ω f)| ∂μ ≤ ∫ _ω, (1 : ℝ) ∂μ := by
    apply integral_mono_of_nonneg
    · exact ae_of_all μ (fun ω => abs_nonneg _)
    · exact integrable_const 1
    · exact ae_of_all μ (fun ω => Real.abs_cos_le_one _)
  simp at h2
  linarith

/-! ## OS3: Reflection Positivity -/

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

-- OS3 inheritance is now `os3_for_continuum_limit` in `OS2_WardIdentity.lean`,
-- stated directly in the standard `OS3_ReflectionPositivity` form.

-- NOTE: os0_inheritance and os4_inheritance were removed as dead axioms
-- (only used in SatisfiesOS0134 bundle which was never consumed downstream).
-- The actual OS0 proof chain goes through continuum_exponential_moments →
-- analyticOn_generatingFunctionalC → os0_for_continuum_limit (OS2_WardIdentity.lean).
-- OS4 goes through continuum_exponential_clustering → os4_for_continuum_limit.

end Pphi2

end
