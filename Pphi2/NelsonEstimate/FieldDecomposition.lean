/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Field Decomposition Sketch — `(φ_S, φ_R)` Joint Gaussian Setup

Sketch of the genuine Glimm–Jaffe field decomposition for the bridge
discharge. Defines the structure that captures `(φ_S, φ_R)` as
independent Gaussian fields with covariances `C_S(T), C_R(T)`, and
shows how the lattice `LatticeRoughErrorSetup` can be built from
such a structure.

## Status

**Sketch / structural file.** Defines the API surface that the
field-decomposition Phase 1 work needs to populate. The actual
construction (joint measure, pushforward identity, chaos analysis
of E_R) is not built here — only the interface. See
`docs/polynomial-chaos-exp-moment-bridge-proof-plan.md` for the
mathematical plan.

## Why this structural file?

The plan-revision recognized that the simpler Wick-constant
decomposition cannot achieve uniform-in-N L² bounds. The genuine
bridge discharge needs:

* A joint measure `μ_S × μ_R` on a doubled space, with two
  independent Gaussian fields of covariances `C_S(T), C_R(T)`.
* The pushforward identity: under the addition map
  `(φ_S, φ_R) ↦ φ_S + φ_R`, the joint measure pushes to the lattice
  GFF `latticeGaussianMeasure`.
* Chaos analysis of the Wick-binomial-expanded
  `E_R = V(φ_S + φ_R) - V_S(φ_S)`, leveraging the fact that every
  term contains at least one φ_R factor.
* L² bounds via `roughCovariance_sq_summable`, controlling
  `‖C_R‖²_HS ≤ L^d · T · c_a` uniformly in N.

This file isolates the structural interface so the missing pieces
are explicit.

## Main definitions (sketch)

* `FieldDecomposition d N a mass`: bundle of the joint Gaussian
  structure (two independent Gaussian fields with covariances
  `C_S(T), C_R(T)`) plus the pushforward identity.

## Main theorems (planned)

* `latticeRoughErrorSetup_of_fieldDecomp`: from a
  `FieldDecomposition`, construct the
  `LatticeRoughErrorSetup` that the existing abstract bridge
  derivation (`bridgeAxiom_of_setup_real`) consumes.

The construction uses:
- The smooth-side bound `smooth_interaction_lower_bound_log_uniform`
  (already a theorem) applied to V_S(φ_S).
- The chaos analysis on the Wick-binomial expansion of E_R.
- The L² bound via `roughCovariance_sq_summable`.
- `chaos_neg_tail_bound` (already a theorem) for the rough tail.
- `lintegral_layer_cake_lt_top_of_eventual_decay` (already a
  theorem) for the integrability hypothesis.

## References

- pphi2/docs/polynomial-chaos-exp-moment-bridge-proof-plan.md
  (revised 2026-05-09).
- Glimm-Jaffe, *Quantum Physics*, Ch. 8.
- Simon, *P(φ)₂ Euclidean QFT*, Ch. V.
-/

import Pphi2.NelsonEstimate.LatticeBridge
import Pphi2.NelsonEstimate.LatticeSetup
import Pphi2.NelsonEstimate.CovarianceSplit
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section

namespace Pphi2

open MeasureTheory GaussianField

variable (d N : ℕ) [NeZero N] (a mass : ℝ)

/-- **Bundle of the field-decomposition setup at cutoff scale `T`.**

A `FieldDecomposition T` packages:
- A joint measure on a "doubled" Gaussian space (the smooth and
  rough fields' Gaussian phase-space).
- The smooth and rough field maps from the joint variables to
  `Configuration (FinLatticeField d N)`.
- The pushforward identity: under addition `(φ_S, φ_R) ↦ φ_S + φ_R`,
  the joint measure pushes to the lattice GFF.

In the canonical realization (per the plan):
- The doubled space is `(FinLatticeSites d N → ℝ) × (FinLatticeSites d N → ℝ)`,
  with the product measure `Measure.pi (gaussianReal 0 1) ×
  Measure.pi (gaussianReal 0 1)`.
- `φ_S(η_S)(x) := Σ_k √(C_S(T,k)) · e_k(x) · η_S(k)`.
- `φ_R(η_R)(x) := Σ_k √(C_R(T,k)) · e_k(x) · η_R(k)`.
- The pushforward equals the GFF by characteristic-function
  uniqueness (the variances `C_S + C_R = C` match).

This file leaves the `FieldDecomposition` structure abstract — its
concrete construction is the substantive Phase 1 work. The fields
required match those needed by `LatticeRoughErrorSetup` once the
addition pushforward is in hand. -/
structure FieldDecomposition (T : ℝ) where
  /-- The "doubled" Gaussian space type carrying the joint
  variables `(η_S, η_R)`. In the canonical realization, this is
  `(FinLatticeSites d N → ℝ) × (FinLatticeSites d N → ℝ)`. -/
  Joint : Type
  /-- Measurable space structure on the joint type. -/
  jointMeasurable : MeasurableSpace Joint
  /-- The joint Gaussian measure (product of two `stdGaussianFin n`'s
  in the canonical realization). -/
  μ_joint : @Measure Joint jointMeasurable
  /-- The joint measure is a probability measure. -/
  jointProbability : @IsProbabilityMeasure Joint jointMeasurable μ_joint
  /-- The smooth field: from joint variables to a configuration. -/
  φ_S : Joint → Configuration (FinLatticeField d N)
  /-- The rough field similarly. -/
  φ_R : Joint → Configuration (FinLatticeField d N)
  /-- Both field maps are measurable. -/
  φ_S_measurable :
    @Measurable Joint (Configuration (FinLatticeField d N)) jointMeasurable
      instMeasurableSpaceConfiguration φ_S
  φ_R_measurable :
    @Measurable Joint (Configuration (FinLatticeField d N)) jointMeasurable
      instMeasurableSpaceConfiguration φ_R
  /-- **Pushforward identity:** `(η_S, η_R) ↦ φ_S(η_S) + φ_R(η_R)`
  pushes the joint measure to the lattice GFF.
  Requires `0 < a, 0 < mass` for the GFF to be defined; these are
  implicit hypotheses on `(a, mass)` in the consumers. -/
  pushforward_eq_GFF :
    ∀ (ha : 0 < a) (hmass : 0 < mass),
    @Measure.map Joint (Configuration (FinLatticeField d N))
        jointMeasurable instMeasurableSpaceConfiguration
        (fun ξ => φ_S ξ + φ_R ξ) μ_joint =
      latticeGaussianMeasure d N a mass ha hmass

/-! ## Phase 1 work that remains

To complete the bridge discharge, the following remain:

1. **Construct a canonical `FieldDecomposition T`** for each `T > 0`,
   using:
   - The gaussian-field theorems
     `gffOrthonormalProj_pushforward_eq_stdGaussian`,
     `gffOrthonormalCoord_independent` (now theorems).
   - `Measure.pi` for the product structure.
   - Spectral decomposition: φ_S, φ_R as linear combinations of the
     η_S, η_R variables weighted by `√(smoothCovEigenvalue T k)`,
     `√(roughCovEigenvalue T k)`.

2. **Pushforward identity proof**: by characteristic-function
   uniqueness, since `C_S(T, k) + C_R(T, k) = (a^d λ_k)^{-1}` (per
   `covariance_split` in CovarianceSplit.lean) and `gaussianReal` is
   characterized by its variance.

3. **Wick binomial expansion of `V(φ_S + φ_R)`**: apply
   `wickMonomial_pow_sum_expansion` (theorem in gaussian-field) at
   each lattice site to expand `:φ(x)^n:_{c_S+c_R}` into the
   bivariate Wick binomial terms.

4. **Chaos membership of `E_R`**: each term in the Wick binomial
   has at least one `:φ_R(x)^k:_{c_R}` factor. As a function on
   `Joint = (η_S, η_R)`, the rough-side projection (integration
   over η_S at fixed η_R, or vice versa) is a polynomial of total
   degree `≤ deg P` in η_R alone, hence in `wienerChaosLE` of the
   rough Gaussian.

5. **L² bound on `E_R`**: by Wick orthogonality on the rough
   marginal, `‖E_R‖²_{L²(μ_joint)} ≤ Σ (combinatorial coefficients)
   · ‖C_R‖²_HS^k`. Apply `roughCovariance_sq_summable` for the
   uniform bound.

6. **Construct `LatticeRoughErrorSetup`** from the
   `FieldDecomposition`: V_S, E_R lift from `Joint` to
   `Configuration` via the pushforward; smooth-side bound transfers
   from `smooth_interaction_lower_bound_log_uniform`; rough tail from
   `chaos_neg_tail_bound` applied to E_R; integrability via
   `lintegral_layer_cake_lt_top_of_eventual_decay`.

7. **Apply `bridgeAxiom_of_setup_real`** to get
   `polynomial_chaos_exp_moment_bridge` as a theorem.

The structural skeleton above isolates the missing pieces. Once a
`FieldDecomposition T` instance is constructed (steps 1-2), the
remaining steps (3-7) feed into the existing abstract chain. -/

end Pphi2
