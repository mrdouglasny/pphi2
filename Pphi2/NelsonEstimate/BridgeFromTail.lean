/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Abstract Bridge from Smooth/Rough Decomposition + Tail Bound

The Glimm–Jaffe Ch. 8 dynamical-cutoff master glue, in abstract form:
given a smooth/rough decomposition of `V` and a doubly-exponential
tail bound on the rough error, the Boltzmann L² moment is uniformly
bounded.

This is the **abstract** version of the bridge: it takes the rough
tail bound `μ {E_R(M) ≤ -M/2} ≤ ψ M` as a hypothesis and produces
the conclusion `∫ exp(-V)² dμ ≤ K`. The lattice instantiation in
`PolynomialChaosBridge.lean` then provides the rough tail bound from
the polynomial-chaos concentration result on the lattice GFF.

## Main result

* `expSqNeg_lintegral_le_of_dynamical_cutoff` — given
  - smooth/rough decomposition `V = V_S(M) + E_R(M)` for each `M`,
  - smooth deterministic bound `V_S(M) ≥ -M/2`,
  - rough tail bound `μ {E_R(M) ≤ -M/2} ≤ ψ M` for `M > 0`,
  - integrability of `exp(2t) · ψ(t)` on `(0, ∞)`,
  conclude `∫⁻ exp(-V)² dμ ≤ μ(univ) + 2 ∫⁻ exp(2t) · ψ(t) dt`.

## References

- Glimm and Jaffe, *Quantum Physics*, Ch. 8 (the dynamical cutoff).
- pphi2/docs/polynomial-chaos-exp-moment-bridge-proof-plan.md.
-/

import Pphi2.NelsonEstimate.LayerCake
import Pphi2.NelsonEstimate.DynamicalCutoff

noncomputable section

namespace Pphi2.BridgeFromTail

open MeasureTheory Pphi2 Pphi2.LayerCake Pphi2.DynamicalCutoff

/-- **Abstract master glue: dynamical cutoff + layer-cake → exp moment bound.**

For any measure `μ` on `α` (with `SFinite μ`) and a measurable
real-valued function `V`, given:

* an `M`-parameterised decomposition `V = V_S(M) + E_R(M)`,
* a deterministic smooth lower bound `V_S(M)(ω) ≥ -M/2` for all `ω`,
  all `M`,
* a rough-error tail bound `μ {ω | E_R(M)(ω) ≤ -M/2} ≤ ψ M` for
  `M > 0`,

the Boltzmann L² moment is bounded by:
$$
\int_\alpha (e^{-V(\omega)})^2 \, d\mu \;\le\; \mu(\alpha) +
  \int_0^\infty \psi(t) \cdot 2 e^{2t} \, dt.
$$

The right-hand side is finite when `t ↦ exp(2t) · ψ(t)` is
`lintegral`-integrable on `(0, ∞)` — which holds for the
doubly-exponential tail bounds produced by the dynamical cutoff
applied to a polynomial-chaos rough error.

**Proof structure:**
1. `measure_le_neg_of_smooth_rough_split` (DynamicalCutoff.lean):
   the smooth bound + rough tail give `μ {V ≤ -M} ≤ ψ M` for
   `M > 0`.
2. `lintegral_expSq_neg_le_of_tail` (LayerCake.lean): substitute
   that tail bound into the layer-cake to get the master form. -/
theorem expSqNeg_lintegral_le_of_dynamical_cutoff
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    (V : α → ℝ) (hV : Measurable V)
    (V_S E_R : ℝ → α → ℝ)
    (hdecomp : ∀ M ω, V ω = V_S M ω + E_R M ω)
    (hsmooth : ∀ M ω, -(M / 2) ≤ V_S M ω)
    (ψ : ℝ → ENNReal)
    (htail : ∀ M, 0 < M → μ {ω | E_R M ω ≤ -(M / 2)} ≤ ψ M) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-V ω) ^ 2) ∂μ ≤
      μ Set.univ +
        ∫⁻ t in Set.Ioi (0 : ℝ),
          ψ t * ENNReal.ofReal (2 * Real.exp (2 * t)) := by
  refine lintegral_expSq_neg_le_of_tail μ V hV ψ ?_
  intro t ht
  exact measure_le_neg_of_smooth_rough_split μ V V_S E_R hdecomp hsmooth ψ htail t ht

end Pphi2.BridgeFromTail
