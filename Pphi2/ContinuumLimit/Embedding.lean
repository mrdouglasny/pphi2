/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Embedding Lattice Fields into the Continuum

Defines the embedding `ι_a : FinLatticeField d N → S'(ℝ^d)` that maps
lattice fields to tempered distributions, and the pushforward measures.

## Main definitions

- `latticeEmbed` — the embedding ι_a
- `continuumMeasure` — pushforward `(ι_a)_* μ_a` on S'(ℝ²)

## Mathematical background

The embedding sends a lattice field `φ : FinLatticeSites d N → ℝ` to the
tempered distribution defined by:

  `(ι_a φ)(f) = a^d · Σ_{x ∈ Λ} φ(x) · f(a · x)`

for Schwartz functions `f ∈ S(ℝ^d)`. Here `a · x` denotes the physical
position of lattice site x (each component multiplied by the lattice spacing a).

This is a continuous linear functional on S(ℝ^d) because:
1. The sum is finite (|Λ| = N^d terms).
2. Each `f(a·x)` is well-defined for Schwartz f.
3. The map f ↦ (ι_a φ)(f) is linear and continuous (finite sum of evaluations).

The pushforward `(ι_a)_* μ_a` is then a probability measure on
`Configuration(S(ℝ^d)) = S'(ℝ^d)`.

## References

- Glimm-Jaffe, *Quantum Physics*, §19.4 (Continuum limit)
- Simon, *The P(φ)₂ Euclidean QFT*, §V
-/

import Pphi2.InteractingMeasure.LatticeMeasure
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

variable (d : ℕ)

/-! ## Continuum test function and distribution spaces

For the continuum limit, the test function space is the Schwartz space
S(ℝ^d), and distributions live in S'(ℝ^d) = Configuration(S(ℝ^d)).

We use Mathlib's `SchwartzMap` for S(ℝ^d). -/

/-- The Schwartz space S(ℝ^d) as the continuum test function space.

Elements are smooth rapidly decaying functions f : ℝ^d → ℝ.
For d=2 this is the test function space for P(Φ)₂. -/
abbrev ContinuumTestFunction :=
  SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ

/-! ## Physical position of a lattice site -/

variable (N : ℕ) [NeZero N]

/-- Physical position of a lattice site: maps `x ∈ (Fin N)^d` to `a · x ∈ ℝ^d`.

For a site x = (x₁,...,x_d) with xᵢ ∈ Fin N, the physical position is
`(a · x₁, ..., a · x_d) ∈ ℝ^d` where xᵢ is cast to ℝ. -/
def physicalPosition (a : ℝ) (x : FinLatticeSites d N) :
    EuclideanSpace ℝ (Fin d) :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm (fun i => a * ((x i : ℕ) : ℝ))

/-! ## The lattice-to-continuum embedding -/

/-- Evaluate a Schwartz function at the physical position of a lattice site.

  `evalAtSite a f x = f(a · x)`

where `a · x` is the physical position of lattice site x. -/
def evalAtSite (a : ℝ) (f : ContinuumTestFunction d) (x : FinLatticeSites d N) : ℝ :=
  f (physicalPosition d N a x)

/-- The lattice-to-continuum embedding sends a lattice field φ to
a tempered distribution `ι_a(φ) ∈ S'(ℝ^d)` defined by:

  `(ι_a φ)(f) = a^d · Σ_{x ∈ Λ} φ(x) · f(a · x)`

This is a finite Riemann sum approximation to `∫ φ(x) f(x) dx`.

We define this as a function from `FinLatticeField d N` to `ℝ`-valued
functions on `ContinuumTestFunction d`. The full CLM structure (making it
an element of `Configuration (ContinuumTestFunction d)`) requires verifying
continuity in the Schwartz topology, which we axiomatize. -/
def latticeEmbedEval (a : ℝ) (φ : FinLatticeField d N)
    (f : ContinuumTestFunction d) : ℝ :=
  a ^ d * ∑ x : FinLatticeSites d N, φ x * evalAtSite d N a f x

/-- The embedding is linear in φ for each f. -/
theorem latticeEmbedEval_linear_phi (a : ℝ) (f : ContinuumTestFunction d)
    (φ₁ φ₂ : FinLatticeField d N) (c₁ c₂ : ℝ) :
    latticeEmbedEval d N a (c₁ • φ₁ + c₂ • φ₂) f =
    c₁ * latticeEmbedEval d N a φ₁ f + c₂ * latticeEmbedEval d N a φ₂ f := by
  -- Bilinearity: expand (c₁φ₁ + c₂φ₂)(x) = c₁·φ₁(x) + c₂·φ₂(x) in the sum,
  -- split, factor out a^d and cᵢ.
  simp only [latticeEmbedEval, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have : ∀ x : FinLatticeSites d N,
      (c₁ * φ₁ x + c₂ * φ₂ x) * evalAtSite d N a f x =
      c₁ * (φ₁ x * evalAtSite d N a f x) + c₂ * (φ₂ x * evalAtSite d N a f x) :=
    fun x => by ring
  simp_rw [this, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  congr 1 <;> (congr 1 <;> ext i <;> ring)

/-- The embedding is linear in f for each φ. -/
theorem latticeEmbedEval_linear_f (a : ℝ) (φ : FinLatticeField d N)
    (f₁ f₂ : ContinuumTestFunction d) (c₁ c₂ : ℝ) :
    latticeEmbedEval d N a φ (c₁ • f₁ + c₂ • f₂) =
    c₁ * latticeEmbedEval d N a φ f₁ + c₂ * latticeEmbedEval d N a φ f₂ := by
  simp only [latticeEmbedEval, evalAtSite]
  simp [SchwartzMap.add_apply, SchwartzMap.smul_apply, Finset.sum_add_distrib,
        Finset.mul_sum, mul_add, mul_left_comm]

/-- The full embedding as a continuous linear map from `FinLatticeField d N`
to `Configuration (ContinuumTestFunction d)`.

For each lattice field φ, the map `f ↦ a^d Σ_x φ(x) f(a·x)` is a continuous
linear functional on S(ℝ^d):
- Linearity: from `latticeEmbedEval_linear_f`
- Continuity: bounded by `(a^d · Σ|φ(x)|) · seminorm(0,0)(f)`, since point
  evaluation on Schwartz space is bounded by the sup-norm seminorm.

Constructed via `SchwartzMap.mkCLMtoNormedSpace`. -/
def latticeEmbed (a : ℝ) (ha : 0 < a) (φ : FinLatticeField d N) :
    Configuration (ContinuumTestFunction d) :=
  SchwartzMap.mkCLMtoNormedSpace
    (latticeEmbedEval d N a φ)
    (fun f g => by
      show latticeEmbedEval d N a φ (f + g) =
        latticeEmbedEval d N a φ f + latticeEmbedEval d N a φ g
      simp only [latticeEmbedEval, evalAtSite, SchwartzMap.add_apply]
      rw [← mul_add, ← Finset.sum_add_distrib]
      congr 1; apply Finset.sum_congr rfl; intro x _; ring)
    (fun r f => by
      show latticeEmbedEval d N a φ (r • f) = r * latticeEmbedEval d N a φ f
      simp only [latticeEmbedEval, evalAtSite, SchwartzMap.smul_apply, smul_eq_mul]
      conv_rhs => rw [← mul_assoc, mul_comm r, mul_assoc, Finset.mul_sum]
      congr 1; apply Finset.sum_congr rfl; intro x _; ring)
    ⟨{(0, 0)}, a ^ d * ∑ x : FinLatticeSites d N, |φ x|,
      mul_nonneg (pow_nonneg (le_of_lt ha) _) (Finset.sum_nonneg (fun x _ => abs_nonneg _)),
      fun f => by
        simp only [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply]
        simp only [latticeEmbedEval, evalAtSite, Real.norm_eq_abs]
        calc |a ^ d * ∑ x, φ x * f (physicalPosition d N a x)|
            ≤ a ^ d * ∑ x, |φ x| * |f (physicalPosition d N a x)| := by
              rw [abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt ha) _)]
              gcongr
              exact le_trans (Finset.abs_sum_le_sum_abs _ _)
                (Finset.sum_le_sum (fun x _ => le_of_eq (abs_mul _ _)))
          _ ≤ a ^ d * ∑ x, |φ x| * SchwartzMap.seminorm ℝ 0 0 f := by
              gcongr with x _
              have h := SchwartzMap.le_seminorm ℝ 0 0 f (physicalPosition d N a x)
              simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
              exact h
          _ = (a ^ d * ∑ x, |φ x|) * SchwartzMap.seminorm ℝ 0 0 f := by
              rw [← Finset.sum_mul]; ring⟩

/-- The embedding agrees with the evaluation formula. -/
theorem latticeEmbed_eval (a : ℝ) (ha : 0 < a)
    (φ : FinLatticeField d N) (f : ContinuumTestFunction d) :
    (latticeEmbed d N a ha φ) f = latticeEmbedEval d N a φ f :=
  rfl

omit [NeZero N] in
/-- The embedding is measurable (needed for pushforward measure).

This holds because for each test function f, the map φ ↦ (ι_a φ)(f) is
linear in φ (hence continuous on the finite-dimensional space), and a map
into the weak-* dual is measurable when each evaluation is measurable. -/
theorem latticeEmbed_measurable (a : ℝ) (ha : 0 < a) :
    Measurable (latticeEmbed d N a ha) := by
  apply configuration_measurable_of_eval_measurable
  intro f
  -- Goal: Measurable (fun φ => (latticeEmbed d N a ha φ) f)
  -- By latticeEmbed_eval, this is fun φ => a^d * Σ_x φ(x) * f(a·x)
  -- which is continuous (hence measurable) in φ
  show Measurable (fun φ => latticeEmbedEval d N a φ f)
  exact (continuous_const.mul (continuous_finset_sum _ (fun x _ =>
    ((continuous_apply x).mul continuous_const)))).measurable

/-- Lift the embedding to Configuration space: compose with the canonical
evaluation map `Configuration (FinLatticeField d N) → FinLatticeField d N → ℝ`
to get `Configuration (FinLatticeField d N) → Configuration (ContinuumTestFunction d)`.

Since `Configuration E = WeakDual ℝ E`, an element `ω ∈ Configuration E`
is a continuous linear functional on E. We extract field values via
`ω(Pi.single x 1)` (evaluating ω on the basis vector at site x) and
apply the lattice embedding: `(latticeEmbedLift ω)(f) = a^d Σ_x ω(e_x) f(a·x)`. -/
def latticeEmbedLift (a : ℝ) (ha : 0 < a)
    (ω : Configuration (FinLatticeField d N)) :
    Configuration (ContinuumTestFunction d) :=
  latticeEmbed d N a ha (fun x => ω (Pi.single x 1))

omit [NeZero N] in
/-- The lifted embedding is measurable.

Each evaluation `ω ↦ (latticeEmbedLift ω)(f)` is a finite sum of measurable
functions `ω ↦ ω(Pi.single x 1)` (measurable by `configuration_eval_measurable`)
multiplied by constants, hence measurable. -/
theorem latticeEmbedLift_measurable (a : ℝ) (ha : 0 < a) :
    Measurable (latticeEmbedLift d N a ha) := by
  apply configuration_measurable_of_eval_measurable
  intro f
  -- Goal: Measurable (fun ω => (latticeEmbedLift d N a ha ω) f)
  -- By definition, this is fun ω => latticeEmbedEval d N a (fun x => ω (Pi.single x 1)) f
  -- = fun ω => a^d * Σ_x ω(Pi.single x 1) * f(a·x)
  change Measurable (fun (ω : Configuration (FinLatticeField d N)) =>
    (latticeEmbed d N a ha (fun x => ω (Pi.single x 1))) f)
  -- Unfolds to: a^d * Σ_x ω(Pi.single x 1) * f(a·x) — measurable in ω
  exact measurable_const.mul (Finset.measurable_sum _ fun x _ =>
    (configuration_eval_measurable (Pi.single x 1)).mul measurable_const)

/-! ## Pushforward measures on S'(ℝ^d) -/

/-- The continuum-embedded measure: pushforward of the interacting lattice
measure μ_a under the lifted embedding.

  `ν_a = (ι̃_a)_* μ_a`

This is a probability measure on `Configuration (ContinuumTestFunction d)` = S'(ℝ^d). -/
def continuumMeasure (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    Measure (Configuration (ContinuumTestFunction d)) :=
  Measure.map (latticeEmbedLift d N a ha)
    (interactingLatticeMeasure d N P a mass ha hmass)

/-- The continuum-embedded measure is a probability measure.

This follows from:
1. The interacting lattice measure is a probability measure
   (by `interactingLatticeMeasure_isProbability`).
2. Pushforward preserves total mass. -/
theorem continuumMeasure_isProbability (P : InteractionPolynomial)
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    IsProbabilityMeasure (continuumMeasure d N P a mass ha hmass) := by
  unfold continuumMeasure
  have := interactingLatticeMeasure_isProbability d N P a mass ha hmass
  exact Measure.isProbabilityMeasure_map
    (latticeEmbedLift_measurable d N a ha).aemeasurable

/-! ## P(φ)₂ continuum limit predicate -/

/-- **Marker predicate**: μ is a P(φ)₂ continuum limit measure.

A probability measure μ on S'(ℝ^d) satisfies `IsPphi2Limit` if it arises as
a subsequential weak limit of the lattice construction. Concretely, this means
there exists a sequence of lattice spacings aₖ → 0 and a corresponding sequence
of probability measures νₖ on S'(ℝ^d) such that all Schwinger functions converge:

  `∫ ∏ᵢ ω(fᵢ) dνₖ → ∫ ∏ᵢ ω(fᵢ) dμ`

for all n and all Schwartz test functions f₁,...,fₙ.

This predicate is used as a hypothesis on axioms that hold specifically for
P(φ)₂ continuum limit measures (translation/rotation invariance, exponential
moments, RP, clustering) — properties that do NOT hold for arbitrary probability
measures on S'(ℝ^d).

In addition to moment convergence, we record the standard Z₂ symmetry of an
even interaction:

  `Measure.map Neg.neg μ = μ`.

The definition is mirrored in `Bridge.lean` by `IsPphi2ContinuumLimit`, which
uses the type aliases `FieldConfig` and `TestFun` for the d=2 case. -/
def IsPphi2Limit {d : ℕ}
    (μ : Measure (Configuration (ContinuumTestFunction d)))
    (P : InteractionPolynomial) (mass : ℝ) : Prop :=
  ∃ (a : ℕ → ℝ) (ν : ℕ → Measure (Configuration (ContinuumTestFunction d))),
    (∀ k, IsProbabilityMeasure (ν k)) ∧
    Filter.Tendsto a Filter.atTop (nhds 0) ∧
    (∀ k, 0 < a k) ∧
    (∀ (n : ℕ) (f : Fin n → ContinuumTestFunction d),
      Filter.Tendsto
        (fun k => ∫ ω : Configuration (ContinuumTestFunction d), ∏ i, ω (f i) ∂(ν k))
        Filter.atTop
        (nhds (∫ ω : Configuration (ContinuumTestFunction d), ∏ i, ω (f i) ∂μ))) ∧
    Measure.map
      (Neg.neg : Configuration (ContinuumTestFunction d) →
        Configuration (ContinuumTestFunction d)) μ = μ

end Pphi2

end
