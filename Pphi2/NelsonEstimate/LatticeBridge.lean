/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lattice Bridge — From Phase-1 Hypotheses to the Master Bridge

The abstract Phase 2 chain (`BridgeFromTail.lean`,
`IntegrabilityHelpers.lean`) reduces the master bridge axiom
`polynomial_chaos_exp_moment_bridge` to a structural hypothesis on
the lattice GFF: an `M`-parametrised smooth/rough decomposition with
deterministic smooth bound, lattice rough-error tail bound, and the
tail's integrability against `exp(2t)`.

This file defines that hypothesis bundle as
`LatticeRoughErrorSetup` and derives the bridge axiom from it as a
theorem.

The final Phase 1 work — proving the rough chaos membership +
`L²`-norm bound on the lattice — feeds in by constructing a
`LatticeRoughErrorSetup`. Once that construction lands, the bridge
axiom becomes a one-liner application of `bridgeAxiom_of_setup`.

## Main definitions

* `LatticeRoughErrorSetup d P mass`: bundle of the smooth/rough
  decomposition + smooth bound + rough tail bound + integrability.

## Main theorems

* `bridgeAxiom_of_setup`: from such a setup, derive the conclusion
  of `polynomial_chaos_exp_moment_bridge`.

## References

- pphi2/docs/polynomial-chaos-exp-moment-bridge-proof-plan.md.
-/

import Pphi2.NelsonEstimate.BridgeFromTail
import Pphi2.NelsonEstimate.IntegrabilityHelpers
import Pphi2.NelsonEstimate.PolynomialChaosBridge

noncomputable section

namespace Pphi2.LatticeBridge

open MeasureTheory Pphi2 GaussianField BridgeFromTail IntegrabilityHelpers

/-- **Bundle of Phase 1 hypotheses for the bridge derivation.**

For a fixed interaction polynomial `P` and mass `mass`, contains
everything the abstract chain needs to conclude
`∃ K, ∀ a N, ∫ exp(-V)² dμ ≤ K`:

* an `M`-parametrised smooth/rough decomposition
  `V = V_S(a, N, M, ·) + E_R(a, N, M, ·)`,
* a uniform deterministic smooth bound `V_S ≥ -M/2`,
* a uniform-in-`(a, N)` rough-error tail bound parametrised by `ψ`,
* integrability of `ψ(t) · 2 exp(2t)` on `(0, ∞)`.

The "uniform-in-`(a, N)`" structure is captured by `ψ` and the
tail-integrability bound depending only on `(P, mass)`, not on
`(a, N)`. -/
structure LatticeRoughErrorSetup
    (d : ℕ) (P : InteractionPolynomial) (mass : ℝ) where
  /-- The smooth-side interaction at depth `M`. -/
  V_S : ∀ (a : ℝ) (N : ℕ) [NeZero N],
    ℝ → Configuration (FinLatticeField d N) → ℝ
  /-- The rough-side error at depth `M`. -/
  E_R : ∀ (a : ℝ) (N : ℕ) [NeZero N],
    ℝ → Configuration (FinLatticeField d N) → ℝ
  /-- The decomposition holds pointwise. -/
  hdecomp : ∀ (a : ℝ) (N : ℕ) [NeZero N]
              (M : ℝ) (ω : Configuration (FinLatticeField d N)),
    interactionFunctional d N P a mass ω = V_S a N M ω + E_R a N M ω
  /-- Deterministic smooth lower bound `V_S ≥ -M/2`. -/
  hsmooth : ∀ (a : ℝ) (N : ℕ) [NeZero N]
              (M : ℝ) (ω : Configuration (FinLatticeField d N)),
    -(M / 2) ≤ V_S a N M ω
  /-- The uniform tail-bound function `ψ : ℝ → ℝ≥0∞`. -/
  ψ : ℝ → ENNReal
  /-- The rough-error tail bound: uniform in `(a, N)` by virtue of
  not naming them in `ψ`'s codomain. -/
  htail : ∀ (a : ℝ) (ha : 0 < a) (hmass : 0 < mass)
            (N : ℕ) [NeZero N] (M : ℝ), 0 < M →
    (latticeGaussianMeasure d N a mass ha hmass)
        {ω | E_R a N M ω ≤ -(M/2)} ≤ ψ M
  /-- Integrability of `ψ(t) · 2 exp(2t)` on `(0, ∞)`. -/
  hintegral :
    ∫⁻ M in Set.Ioi (0 : ℝ),
      ψ M * ENNReal.ofReal (2 * Real.exp (2 * M)) < ⊤
  /-- `interactionFunctional` is measurable (needed for the abstract
  chain). -/
  hV_meas : ∀ (a : ℝ) (N : ℕ) [NeZero N],
    Measurable (fun ω : Configuration (FinLatticeField d N) =>
      interactionFunctional d N P a mass ω)

/-- **Master bridge from the Phase 1 hypothesis bundle.**

Given a `LatticeRoughErrorSetup`, the lattice Boltzmann L² moment
is uniformly bounded:
$$
\exists K > 0, \forall (a > 0)(N), \int (\exp(-V_a))^2 \, d\mu \le K.
$$

The witness `K = 1 + (∫⁻ ψ(t) · 2 exp(2t)).toReal`.

**Proof:** apply `expSqNeg_lintegral_le_of_dynamical_cutoff` for
each `(a, N)`, then convert from `lintegral` to `integral` and
absorb `μ(univ) = 1`. The integrability hypothesis ensures the
witness is finite (and uniform in `(a, N)` since the tail integral
doesn't depend on them). -/
theorem bridgeAxiom_of_setup
    {d : ℕ} {P : InteractionPolynomial} {mass : ℝ} (hmass : 0 < mass)
    (S : LatticeRoughErrorSetup d P mass) :
    ∃ (K : ℝ), 0 < K ∧
    ∀ (a : ℝ) (ha : 0 < a),
    ∀ (N : ℕ) [NeZero N],
    ∫⁻ ω : Configuration (FinLatticeField d N),
        ENNReal.ofReal ((Real.exp (-interactionFunctional d N P a mass ω))^2)
        ∂(latticeGaussianMeasure d N a mass ha hmass) ≤
      1 +
        ∫⁻ M in Set.Ioi (0 : ℝ),
          S.ψ M * ENNReal.ofReal (2 * Real.exp (2 * M)) := by
  refine ⟨1, one_pos, ?_⟩
  intro a ha N _
  have h_abstract :
    ∫⁻ ω, ENNReal.ofReal ((Real.exp (-interactionFunctional d N P a mass ω))^2)
        ∂(latticeGaussianMeasure d N a mass ha hmass) ≤
      (latticeGaussianMeasure d N a mass ha hmass) Set.univ +
        ∫⁻ t in Set.Ioi (0 : ℝ),
          S.ψ t * ENNReal.ofReal (2 * Real.exp (2 * t)) := by
    refine expSqNeg_lintegral_le_of_dynamical_cutoff
      (latticeGaussianMeasure d N a mass ha hmass)
      (fun ω => interactionFunctional d N P a mass ω)
      (S.hV_meas a N)
      (fun M ω => S.V_S a N M ω)
      (fun M ω => S.E_R a N M ω)
      ?_ ?_ S.ψ ?_
    · intro M ω; exact S.hdecomp a N M ω
    · intro M ω; exact S.hsmooth a N M ω
    · intro t ht; exact S.htail a ha hmass N t ht
  refine h_abstract.trans ?_
  -- (latticeGaussianMeasure ...) univ = 1 since it's a probability measure.
  have h_prob : (latticeGaussianMeasure d N a mass ha hmass) Set.univ = 1 :=
    measure_univ
  rw [h_prob]

/-- **Bridge in the real-valued integral form**, matching the
signature of `polynomial_chaos_exp_moment_bridge`.

Same content as `bridgeAxiom_of_setup` but with `∫` instead of `∫⁻`,
producing a real-valued bound. The witness is
`K = 1 + (∫⁻ ψ(t) · 2 exp(2t)).toReal`, finite by `S.hintegral`. -/
theorem bridgeAxiom_of_setup_real
    {d : ℕ} {P : InteractionPolynomial} {mass : ℝ} (hmass : 0 < mass)
    (S : LatticeRoughErrorSetup d P mass) :
    ∃ (K : ℝ), 0 < K ∧
    ∀ (a : ℝ) (ha : 0 < a),
    ∀ (N : ℕ) [NeZero N],
    ∫ ω : Configuration (FinLatticeField d N),
        (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2
        ∂(latticeGaussianMeasure d N a mass ha hmass) ≤
      1 + (∫⁻ M in Set.Ioi (0 : ℝ),
        S.ψ M * ENNReal.ofReal (2 * Real.exp (2 * M))).toReal := by
  set L_ψ : ENNReal := ∫⁻ M in Set.Ioi (0 : ℝ),
    S.ψ M * ENNReal.ofReal (2 * Real.exp (2 * M))
  have hL_ψ_lt_top : L_ψ < ⊤ := S.hintegral
  set K : ℝ := 1 + L_ψ.toReal
  have hK_pos : 0 < K := by
    have hL_ψ_nn : 0 ≤ L_ψ.toReal := ENNReal.toReal_nonneg
    simp [K]; linarith
  refine ⟨K, hK_pos, ?_⟩
  intro a ha N _
  obtain ⟨_, _, h_lin⟩ := bridgeAxiom_of_setup hmass S
  have h_lin' := h_lin a ha N
  -- h_lin' : ∫⁻ ω, ofReal((exp(-V))^2) ∂μ ≤ 1 + L_ψ.
  -- Convert to ∫: `∫ f = (∫⁻ ofReal f).toReal` for nonneg f
  -- (when `∫⁻ ofReal f < ⊤`).
  have h_integrand_nn :
      ∀ ω, 0 ≤ (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2 :=
    fun _ => sq_nonneg _
  have h_meas_sq :
      Measurable (fun ω : Configuration (FinLatticeField d N) =>
        (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2) := by
    have h_V := S.hV_meas a N
    exact ((h_V.neg).exp).pow_const 2
  -- The lintegral of `ofReal((exp(-V))^2)` is bounded by `1 + L_ψ`,
  -- hence finite, so `(exp(-V))^2` is `Integrable`.
  have h_lintegral_lt_top :
      ∫⁻ ω, ENNReal.ofReal ((Real.exp (-interactionFunctional d N P a mass ω)) ^ 2)
          ∂(latticeGaussianMeasure d N a mass ha hmass) < ⊤ := by
    refine lt_of_le_of_lt h_lin' ?_
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hL_ψ_lt_top⟩
  -- Use `integral_eq_lintegral_of_nonneg` to convert.
  have h_integrable :
      Integrable (fun ω : Configuration (FinLatticeField d N) =>
        (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2)
        (latticeGaussianMeasure d N a mass ha hmass) := by
    refine ⟨h_meas_sq.aestronglyMeasurable, ?_⟩
    -- HasFiniteIntegral: ∫⁻ ‖f‖ₑ ∂μ < ⊤. For nonneg f, ‖f‖ₑ = ofReal f.
    rw [hasFiniteIntegral_iff_norm]
    have h_norm_eq : ∀ ω,
        ‖((Real.exp (-interactionFunctional d N P a mass ω)) ^ 2)‖ =
        (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2 := by
      intro ω
      exact Real.norm_of_nonneg (h_integrand_nn ω)
    simp_rw [h_norm_eq]
    exact h_lintegral_lt_top
  have h_int_eq :
      ∫ ω, (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2
          ∂(latticeGaussianMeasure d N a mass ha hmass) =
        (∫⁻ ω, ENNReal.ofReal
          ((Real.exp (-interactionFunctional d N P a mass ω)) ^ 2)
          ∂(latticeGaussianMeasure d N a mass ha hmass)).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall h_integrand_nn)
      h_meas_sq.aestronglyMeasurable]
  rw [h_int_eq]
  -- Now: (∫⁻ ofReal f).toReal ≤ K = 1 + L_ψ.toReal.
  have h_toReal_le :
      (∫⁻ ω, ENNReal.ofReal ((Real.exp (-interactionFunctional d N P a mass ω)) ^ 2)
        ∂(latticeGaussianMeasure d N a mass ha hmass)).toReal ≤
      (1 + L_ψ).toReal := by
    apply ENNReal.toReal_mono
    · exact ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hL_ψ_lt_top⟩ |>.ne
    · exact h_lin'
  refine h_toReal_le.trans ?_
  rw [ENNReal.toReal_add ENNReal.one_ne_top hL_ψ_lt_top.ne]
  simp [K]

end Pphi2.LatticeBridge
