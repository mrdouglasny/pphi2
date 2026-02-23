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
to `Configuration (ContinuumTestFunction d)` (axiomatized).

Making this rigorous requires showing that for each φ, the map
`f ↦ a^d Σ_x φ(x) f(a·x)` is continuous in the Schwartz topology.
This holds because evaluation at a point is continuous on S(ℝ^d),
and a finite sum of continuous functionals is continuous. -/
axiom latticeEmbed (a : ℝ) (ha : 0 < a) :
    FinLatticeField d N → Configuration (ContinuumTestFunction d)

/-- The embedding preserves the evaluation formula. -/
axiom latticeEmbed_eval (a : ℝ) (ha : 0 < a)
    (φ : FinLatticeField d N) (f : ContinuumTestFunction d) :
    (latticeEmbed d N a ha φ) f = latticeEmbedEval d N a φ f

/-- The embedding is measurable (needed for pushforward measure). -/
axiom latticeEmbed_measurable (a : ℝ) (ha : 0 < a) :
    Measurable (latticeEmbed d N a ha)

/-- Lift the embedding to Configuration space: compose with the canonical
evaluation map `Configuration (FinLatticeField d N) → FinLatticeField d N → ℝ`
to get `Configuration (FinLatticeField d N) → Configuration (ContinuumTestFunction d)`.

Since `Configuration E = WeakDual ℝ E`, an element `ω ∈ Configuration E`
is a continuous linear functional on E. The lifted embedding sends ω to
the distribution `f ↦ ω(a^d Σ_x δ_x · f(a·x))`. -/
axiom latticeEmbedLift (a : ℝ) (ha : 0 < a) :
    Configuration (FinLatticeField d N) →
    Configuration (ContinuumTestFunction d)

/-- The lifted embedding is measurable. -/
axiom latticeEmbedLift_measurable (a : ℝ) (ha : 0 < a) :
    Measurable (latticeEmbedLift d N a ha)

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
  sorry

end Pphi2

end
