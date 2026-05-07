/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nelson's Exponential Estimate

Combines covariance splitting, the smooth classical lower bound, and
hypercontractivity on the rough error to prove Nelson's exponential estimate:

  `∫ exp(-2V) dμ_GFF ≤ K`  (uniform in lattice size N)

## Main results

- `nelson_exponential_estimate_lattice` — the full estimate on the lattice

## Proof outline

1. Split covariance: C = C_S(T) + C_R(T) (CovarianceSplit.lean)
2. Wick binomial: V(φ) = V_S(φ_S) + E_R(φ_S, φ_R) (WickBinomial.lean)
3. Classical lower bound: V_S ≥ -C₁·(1+|log T|)² (SmoothLowerBound.lean)
4. Hypercontractivity: P(|E_R| > λ) ≤ exp(-c·λ^{1/2}/T^{1/8}) (RoughErrorBound.lean)
5. Dynamic cutoff: choose T = exp(-c₃·√M), integrate (this file)

## References

- Simon, *P(φ)₂ Euclidean QFT*, Chapter V, Theorem V.14
- Glimm-Jaffe, *Quantum Physics*, Section 8.6
-/

import Pphi2.NelsonEstimate.SmoothLowerBound
import Pphi2.NelsonEstimate.RoughErrorBound
import Pphi2.InteractingMeasure.LatticeMeasure
import Pphi2.TorusContinuumLimit.TorusEmbedding

noncomputable section

open GaussianField MeasureTheory Real
open scoped BigOperators

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Nelson's dynamic cutoff argument

Given:
- V(φ) = V_S(φ_S) + E_R(φ_S, φ_R)
- V_S(φ_S) ≥ -C₁·(log T)² (smooth lower bound)
- P(|E_R| > λ) ≤ exp(-c₂·λ^{1/2}/T^{1/8}) (rough tail bound)

If V(φ) ≤ -M, then E_R ≤ -M - V_S ≤ -M + C₁(log T)².

Choose T = T(M) such that C₁(log T)² = M/2:
  T = exp(-√(M/(2C₁)))

Then |E_R| ≥ M/2, so:
  P(V ≤ -M) ≤ P(|E_R| ≥ M/2) ≤ exp(-c₂·(M/2)^{1/2} · exp(c₃·M^{1/2}))

This is DOUBLE EXPONENTIAL decay, so:
  ∫₀^∞ exp(2M) · P(V ≤ -M) dM < ∞ -/

/-- **Nelson's exponential estimate on the lattice** (axiomatised in
Stage 1 — to be proved via dynamical cutoff in Phase 2).

For the P(φ)₂ lattice theory on the 2D torus of size L with lattice
spacing a = L/N and mass m > 0:

    ∃ K > 0, ∀ N, ∫ exp(-2V) dμ_GFF ≤ K

where K depends on P (the interaction polynomial), L, and m, but NOT
on N (the lattice size).

Under the Glimm-Jaffe-aligned normalisation, wickConstant grows like
(a^d)⁻¹ · mass⁻² (logarithmically divergent in d=2), so the "easy
pointwise lower bound" proof breaks: `wickPolynomial_uniform_bounded_below`
applied to a divergent c-range gives a divergent A. The genuine proof
is via dynamical cutoff (Glimm-Jaffe Ch. 8 / Simon Ch. I): split the
integration domain into small-field and large-field events, use
polynomial bounds on the small-field set and Gaussian tails on the
large-field set.

Reference: Glimm-Jaffe Ch. 8 (dynamical cutoff); Simon, *P(φ)₂
Euclidean QFT*, Ch. I; Nelson 1966.

The infrastructure for the dynamical-cutoff proof
(`SmoothLowerBound.lean`, `RoughErrorBound.lean`) exists in pphi2 but
is not yet wired up. Phase 2 deliverable. -/
axiom nelson_exponential_estimate_lattice
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (K : ℝ), 0 < K ∧
    ∀ (N : ℕ) [NeZero N],
    ∫ ω : Configuration (FinLatticeField 2 N),
        (exp (-interactionFunctional 2 N P (circleSpacing L N) mass ω)) ^ 2
        ∂(latticeGaussianMeasure 2 N (circleSpacing L N) mass
          (circleSpacing_pos L N) hmass) ≤ K
end Pphi2

end
