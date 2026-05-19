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
import Pphi2.NelsonEstimate.PolynomialChaosBridge
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

/-- **Nelson's exponential estimate on the lattice** (Phase 2 master
result, derived from `polynomial_chaos_exp_moment_bridge`).

For the P(φ)₂ lattice theory on the 2D torus of size L with lattice
spacing a = L/N and mass m > 0:

    ∃ K > 0, ∀ N, ∫ exp(-2V) dμ_GFF ≤ K

where K depends on P, L, and m, but NOT on N. Specialization of
`nelson_exponential_estimate_master` (in `PolynomialChaosBridge.lean`)
to the symmetric-torus geometry `a = circleSpacing L N`. The
substantive content (Glimm-Jaffe Ch. 8 / Simon Ch. I dynamical cutoff)
is in the bridge axiom; this specialization just chooses the spacing.

The `a ≤ 1` constraint of the master is satisfied for `N ≥ ⌈L⌉`
(`circleSpacing L N = L/N ≤ 1`); the existential here doesn't need
that, since for finite `N < ⌈L⌉` we can absorb the value into the
witness `K`. -/
theorem nelson_exponential_estimate_lattice
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (K : ℝ), 0 < K ∧
    ∀ (N : ℕ) [NeZero N],
    ∫ ω : Configuration (FinLatticeField 2 N),
        (exp (-interactionFunctional 2 N P (circleSpacing L N) mass ω)) ^ 2
        ∂(latticeGaussianMeasure 2 N (circleSpacing L N) mass
          (circleSpacing_pos L N) hmass) ≤ K := by
  obtain ⟨K, hK_pos, hbound⟩ :=
    nelson_exponential_estimate_master (d := 2) rfl P mass L hL.out hmass
  refine ⟨K, hK_pos, fun N _ => ?_⟩
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hvol : (N : ℝ) * circleSpacing L N = L := by
    rw [circleSpacing_eq]
    field_simp [hN]
  exact hbound N (circleSpacing L N) (circleSpacing_pos L N) hvol

end Pphi2

end
