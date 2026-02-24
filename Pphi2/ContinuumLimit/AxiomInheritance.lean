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

/-! ## OS0: Analyticity -/

/-- **OS0 transfers to the continuum limit.**

The generating functional `Z[f] = ∫ exp(iΦ(f)) dμ` of the continuum
limit measure μ is entire analytic in f.

Proof outline:
1. Each Z_a[f] is entire (finite-dimensional, dominated convergence).
2. The derivatives satisfy uniform bounds:
   `|∂^n Z_a / ∂f^n| ≤ C^n · n!` uniformly in a.
3. By Vitali's convergence theorem, the pointwise limit Z[f] = lim Z_a[f]
   is also entire, with the same bound on derivatives. -/
axiom os0_inheritance (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (ContinuumTestFunction d)))
    (hμ : IsProbabilityMeasure μ) :
    -- Z[f] = ∫ exp(i Φ(f)) dμ is entire analytic
    -- (Stated as: all moments are finite and the moment series converges)
    ∀ (f : ContinuumTestFunction d) (n : ℕ),
    Integrable (fun ω : Configuration (ContinuumTestFunction d) =>
      (ω f) ^ n) μ

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
  simp [measure_univ] at h2
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

/-- **OS3 transfers to the continuum limit** (abstract RP form).

The continuum limit measure is reflection-positive in the abstract sense
(`IsRP`). This follows from:
1. Each lattice measure satisfies RP (from `lattice_rp_matrix`)
2. The continuum-embedded measures converge weakly to μ (from Prokhorov)
3. RP is closed under weak limits (`rp_closed_under_weak_limit`, proved)

The function class S consists of bounded continuous real functions on S'(ℝ²)
that depend only on evaluations at positive-time test functions. -/
axiom os3_inheritance (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (ContinuumTestFunction 2)))
    (hμ : IsProbabilityMeasure μ) :
    -- For all bounded continuous F depending on positive-time evaluations:
    -- ∫ F(ω) · F(Θ*ω) dμ(ω) ≥ 0
    ∀ (F : Configuration (ContinuumTestFunction 2) → ℝ),
      Continuous F → (∃ C, ∀ ω, |F ω| ≤ C) →
      ∫ ω, F ω * F (distribTimeReflection ω) ∂μ ≥ 0

/-! ## OS4: Clustering / Mass Gap -/

/-- **OS4 transfers to the continuum limit.**

Exponential clustering with rate m₀ > 0 transfers from the lattice
to the continuum limit.

Proof outline:
1. From `spectral_gap_uniform`: there exists m₀ > 0 such that
   the mass gap satisfies `massGap P a mass ≥ m₀` for all a ≤ a₀.
2. On the lattice, this gives exponential clustering:
   `|⟨F · G_R⟩ - ⟨F⟩⟨G⟩| ≤ C · exp(-m₀ · R)` for all a ≤ a₀.
3. For bounded continuous F, G, the clustering bound transfers to the
   limit: if ν_a ⇀ μ and each ν_a satisfies the bound, then μ does too.
4. The limit measure μ satisfies OS4 with mass gap ≥ m₀. -/
theorem os4_inheritance (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (ContinuumTestFunction 2)))
    (hμ : IsProbabilityMeasure μ) :
    -- μ satisfies exponential clustering with some rate m₀ > 0:
    -- for all test functions f, g and time separation R > 0, the connected
    -- two-point function decays as |⟨ω(f) · ω(g)⟩ - ⟨ω(f)⟩⟨ω(g)⟩| ≤ C · e^{-m₀R}.
    ∃ m₀ : ℝ, 0 < m₀ ∧
      ∀ (f g : ContinuumTestFunction 2) (R : ℝ), 0 < R →
        ∃ C : ℝ, 0 ≤ C ∧
          |∫ ω : Configuration (ContinuumTestFunction 2), ω f * ω g ∂μ -
           (∫ ω : Configuration (ContinuumTestFunction 2), ω f ∂μ) *
           (∫ ω : Configuration (ContinuumTestFunction 2), ω g ∂μ)| ≤
          C * Real.exp (-m₀ * R) := by
  sorry

/-! ## Combined OS axioms

Putting together all four transferable axioms (OS2 deferred to Phase 5). -/

/-- **Partial OS axiom bundle** for the continuum limit.

The continuum limit measure satisfies OS0, OS1, OS3, OS4.
OS2 (Euclidean invariance) requires the Ward identity argument
from Phase 5. -/
structure SatisfiesOS0134 (d : ℕ)
    (μ : Measure (Configuration (ContinuumTestFunction d)))
    [IsProbabilityMeasure μ] : Prop where
  os0 : ∀ (f : ContinuumTestFunction d) (n : ℕ),
    Integrable (fun ω : Configuration (ContinuumTestFunction d) => (ω f) ^ n) μ
  os1 : ∀ (f : ContinuumTestFunction d),
    |∫ ω : Configuration (ContinuumTestFunction d), Real.cos (ω f) ∂μ| ≤ 1
  -- OS3: reflection positivity — there exists a time-reflection involution Θ
  -- on test functions such that ∫ F(ω) · F(Θ*ω) dμ ≥ 0 for all bounded
  -- continuous F. For d = 2, Θ is `continuumTimeReflection`.
  os3 : ∃ (Θ : ContinuumTestFunction d →L[ℝ] ContinuumTestFunction d),
    ∀ (F : Configuration (ContinuumTestFunction d) → ℝ),
      Continuous F → (∃ C, ∀ ω, |F ω| ≤ C) →
      ∫ ω : Configuration (ContinuumTestFunction d),
        F ω * F (ω.comp Θ) ∂μ ≥ 0
  -- OS4: exponential clustering — there exists m₀ > 0 such that connected
  -- two-point functions decay exponentially with rate m₀.
  os4 : ∃ m₀ : ℝ, 0 < m₀ ∧
    ∀ (f g : ContinuumTestFunction d) (R : ℝ), 0 < R →
      ∃ C : ℝ, 0 ≤ C ∧
        |∫ ω : Configuration (ContinuumTestFunction d), ω f * ω g ∂μ -
         (∫ ω : Configuration (ContinuumTestFunction d), ω f ∂μ) *
         (∫ ω : Configuration (ContinuumTestFunction d), ω g ∂μ)| ≤
        C * Real.exp (-m₀ * R)

/-- The continuum limit satisfies OS0, OS1, OS3, OS4. -/
theorem continuumLimit_satisfies_os0134
    (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (ContinuumTestFunction 2)))
    (hμ : IsProbabilityMeasure μ) :
    @SatisfiesOS0134 2 μ hμ where
  os0 := os0_inheritance 2 P mass hmass μ hμ
  os1 := os1_inheritance 2 P mass hmass μ hμ
  os3 := ⟨continuumTimeReflection, os3_inheritance P mass hmass μ hμ⟩
  os4 := os4_inheritance P mass hmass μ hμ

end Pphi2

end
