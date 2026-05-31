/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Heterogeneous Nelson exponential estimate (Z_Nt × Z_Ns)

The Nelson `L²` exp-moment bound for the P(φ)₂ interacting measure on the isotropic
heterogeneous lattice, uniform in `(Nt, Ns, a)` at fixed volume `Lt·Ls`. Obtained by the
**B-lean route**: the genuine analytic input — the Glimm–Jaffe dynamical-cutoff smooth/rough
chaos decomposition — is isolated as the vetted axiom `asymChaosCutoffDecomposition`, and the
final bound is assembled by the *proved, generic* dynamical-cutoff engine
`bridgeAxiom_of_setup_real_generic` (`NelsonEstimate/GenericBridge.lean`).

## Main results

- `asymChaosCutoffDecomposition` — **axiom**: existence of the uniform-`ψ` chaos decomposition.
- `asymNelson_exponential_estimate_iso` — **theorem**: `∃ K, ∀ (Nt,Ns,a), ∫ exp(-2V)² ≤ K`.

## Reference

- Glimm–Jaffe, *Quantum Physics*, Ch. 8 (dynamical cutoff / polynomial chaos).
- Simon, *The P(φ)₂ Euclidean QFT* (1974), Thm V.12, V.15 (the exp-moment bound is uniform in
  the UV cutoff at fixed volume — the basis for the `ψ`-uniformity here).
-/

import Pphi2.AsymTorus.AsymLatticeMeasure
import Pphi2.NelsonEstimate.AsymRoughErrorChaosStd
import Pphi2.NelsonEstimate.AsymSmoothLowerBound
import Pphi2.NelsonEstimate.GenericBridge
import Pphi2.NelsonEstimate.PolynomialChaosBridge

noncomputable section

open MeasureTheory GaussianField

namespace Pphi2

/-- Naturality of `interactionFunctionalAsym` under the joint→config pushforward
`asymCanonicalSumConfig`: evaluating the lattice interaction at the synthesized
sum-field equals the asym joint full-interaction functional. The shared
`wickConstantAsym Nt Ns a mass` Wick constant (no `T` dependence) and
`asymCanonicalSumConfig_apply_delta` make this definitional. -/
theorem interactionFunctionalAsym_asymCanonicalSumConfig_eq
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ) (P : InteractionPolynomial)
    (η : AsymCanonicalJoint Nt Ns) :
    interactionFunctionalAsym Nt Ns P a mass
        (asymCanonicalSumConfig Nt Ns a mass T η) =
      asymCanonicalFullInteractionJoint Nt Ns a mass T P η := by
  unfold interactionFunctionalAsym asymCanonicalFullInteractionJoint
  congr 1
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [asymCanonicalSumConfig_apply_delta]

/-- **Heterogeneous polynomial-chaos dynamical-cutoff decomposition** (textbook axiom).

For the P(φ)₂ theory on the isotropic heterogeneous lattice `Z_Nt × Z_Ns` (single spacing `a`,
periods `Lt = Nt·a`, `Ls = Ns·a`, fixed volume `Lt·Ls`), the Wick-ordered interaction
`V_a = interactionFunctionalAsym` admits the Glimm–Jaffe dynamical-cutoff smooth/rough
decomposition: there is a tail function `ψ` (super-exponentially small, **uniform in
`(Nt, Ns, a)`**, with `∫₀^∞ ψ·2e^{2M} < ∞`) such that for every `(Nt, Ns, a)` with `Nt·a = Lt`,
`Ns·a = Ls` there is an `M`-parametrised split `V_a = V_S(M) + E_R(M)` with the deterministic
smooth lower bound `V_S(M) ≥ -M/2` and the rough-error tail
`μ_{GFF,asym}{E_R(M) ≤ -M/2} ≤ ψ(M)`.

This is the heterogeneous analogue of the *proved* (zero-axiom) square decomposition
(`canonicalSmoothInteraction`/`canonicalRoughError` + `canonicalSmoothInteraction_lower_bound_…`
+ `canonicalRoughError_cutoff_tail_uniform`). `InteractionPolynomial` already encodes the
even-degree / bounded-below hypothesis on `P`; `m > 0` gives the IR mass gap that makes the
bound volume-controlled and shape-independent.

Reference: Glimm–Jaffe Ch. 8; Simon, *P(φ)₂*, Thm V.12/V.15.
Strategy: port the square polynomial-chaos cutoff decomposition
(`FieldDecomposition`/`RoughErrorBound`/`CovarianceBoundsGJ`) to `Z_Nt × Z_Ns` using the
heterogeneous DFT (Phase-1b `AsymCovariance`) for the smooth/rough covariance split and the
heat-kernel/hypercontractivity bounds for the rough tail; the volume `Lt·Ls` (not the aspect
ratio) controls the constants.

✅ Vetted: deep-think-gemini (Standard / Likely correct) — uniformity in `(Nt,Ns,a)` at fixed
volume confirmed against Simon V.12/V.15; UV singularity is isotropic so the rectangle adds no
obstruction; mass gap controls the IR.

**Discharged 2026-05-31** (UNIT 7) via the trivial split `V_S(M, ω) := -(M/2)`,
`E_R(M, ω) := V_a(ω) + M/2`. C1 and C2 are then definitional; C3 uses the
pushforward `latticeGaussianMeasureAsym = (asymCanonicalJointMeasure).map asymCanonicalSumConfig`
+ the naturality `interactionFunctionalAsym ∘ asymCanonicalSumConfig =
asymCanonicalFullInteractionJoint` + UNIT 2's smooth lower bound (to subset
`{full ≤ -M} ⊆ {rough ≤ -M/2}` for `M ≥ 2C`) + UNIT 6's polynomial-chaos
negative-tail bound `asymCanonicalRoughError_neg_tail_uniform`. The witness
`ψ := degreePiecewiseTail P K C` and its integrability
`degreePiecewiseTail_layerCake_lt_top` are reused verbatim from the square
side (lattice-agnostic, parameterized only by `(P, K, C)`). -/
theorem asymChaosCutoffDecomposition
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Lt Ls : ℝ) (hLt : 0 < Lt) (hLs : 0 < Ls) :
    ∃ ψ : ℝ → ENNReal,
      (∫⁻ M in Set.Ioi (0 : ℝ), ψ M * ENNReal.ofReal (2 * Real.exp (2 * M)) < ⊤) ∧
      ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
        (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
        ∃ V_S E_R : ℝ → Configuration (AsymLatticeField Nt Ns) → ℝ,
          (∀ M ω, interactionFunctionalAsym Nt Ns P a mass ω = V_S M ω + E_R M ω) ∧
          (∀ M ω, -(M / 2) ≤ V_S M ω) ∧
          (∀ M, 0 < M →
            (latticeGaussianMeasureAsym Nt Ns a mass ha hmass)
              {ω | E_R M ω ≤ -(M / 2)} ≤ ψ M) := by
  obtain ⟨C, hC_pos, hsmooth⟩ :=
    asymCanonicalSmoothInteraction_lower_bound_at_cutoff_uniform
      P mass Lt Ls hLt hLs hmass
  obtain ⟨K, hK_pos, htail⟩ :=
    asymCanonicalRoughError_neg_tail_uniform P mass Lt Ls hLt hLs hmass
  refine ⟨degreePiecewiseTail P K C,
          degreePiecewiseTail_layerCake_lt_top P K C hK_pos hC_pos, ?_⟩
  intro Nt Ns _ _ a ha hvolt hvols
  refine ⟨fun M _ω => -(M / 2),
          fun M ω => interactionFunctionalAsym Nt Ns P a mass ω + M / 2,
          ?_, ?_, ?_⟩
  · -- C1: V_a(ω) = -(M/2) + (V_a(ω) + M/2)
    intro M ω; ring
  · -- C2: -(M/2) ≤ -(M/2)
    intro M ω; rfl
  · -- C3: μ_GFF{E_R M ≤ -(M/2)} ≤ ψ(M)
    intro M hM_pos
    by_cases hLarge : 2 * C ≤ M
    · -- Large-M branch: pushforward + naturality + UNIT 2 + UNIT 6
      have hT_pos :
          0 < Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M :=
        Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale_pos P C M
      -- Rewrite the E_R-sublevel set as a V_a-sublevel set.
      have hset_eq :
          {ω : Configuration (AsymLatticeField Nt Ns) |
              interactionFunctionalAsym Nt Ns P a mass ω + M / 2 ≤ -(M / 2)} =
            {ω | interactionFunctionalAsym Nt Ns P a mass ω ≤ -M} := by
        ext ω
        simp only [Set.mem_setOf_eq]
        constructor <;> intro h <;> linarith
      rw [hset_eq]
      -- Push the lattice GFF measure back to the joint measure.
      rw [show latticeGaussianMeasureAsym Nt Ns a mass ha hmass =
          (asymCanonicalJointMeasure Nt Ns).map
            (asymCanonicalSumConfig Nt Ns a mass
              (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M)) from
        (asymCanonicalJointMeasure_map_sumConfig Nt Ns a mass ha hmass _ hT_pos).symm]
      -- V_a is measurable, so the sublevel set is measurable.
      have hV_meas : Measurable (interactionFunctionalAsym Nt Ns P a mass) :=
        interactionFunctionalAsym_measurable Nt Ns P a mass
      have hset_meas :
          MeasurableSet
            {ω : Configuration (AsymLatticeField Nt Ns) |
              interactionFunctionalAsym Nt Ns P a mass ω ≤ -M} :=
        hV_meas measurableSet_Iic
      rw [Measure.map_apply
        (asymCanonicalSumConfig_measurable Nt Ns a mass _) hset_meas]
      -- Naturality replaces V_a ∘ sumConfig with asymCanonicalFullInteractionJoint.
      have hnat_eq :
          (asymCanonicalSumConfig Nt Ns a mass
              (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M)) ⁻¹'
            {ω | interactionFunctionalAsym Nt Ns P a mass ω ≤ -M} =
          {η : AsymCanonicalJoint Nt Ns |
              asymCanonicalFullInteractionJoint Nt Ns a mass
                (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M) P η ≤ -M} := by
        ext η
        simp only [Set.mem_preimage, Set.mem_setOf_eq]
        rw [interactionFunctionalAsym_asymCanonicalSumConfig_eq]
      rw [hnat_eq]
      -- {full ≤ -M} ⊆ {rough ≤ -M/2} via UNIT 2's smooth lower bound.
      have hsubset :
          {η : AsymCanonicalJoint Nt Ns |
              asymCanonicalFullInteractionJoint Nt Ns a mass
                (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M) P η ≤ -M} ⊆
            {η : AsymCanonicalJoint Nt Ns |
                asymCanonicalRoughError Nt Ns a mass
                  (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M) P η ≤
                  -(M / 2)} := by
        intro η h_full_le
        simp only [Set.mem_setOf_eq] at h_full_le ⊢
        have h_smooth := hsmooth Nt Ns a ha hvolt hvols M hLarge η
        have h_full_eq :
            asymCanonicalFullInteractionJoint Nt Ns a mass
              (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M) P η =
              asymCanonicalSmoothInteraction Nt Ns a mass
                  (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M) P η +
                asymCanonicalRoughError Nt Ns a mass
                  (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M) P η := by
          unfold asymCanonicalRoughError; ring
        rw [h_full_eq] at h_full_le
        linarith
      refine le_trans (measure_mono hsubset) ?_
      -- UNIT 6 bound on the rough negative tail at t = M/2.
      have hM_half_pos : 0 < M / 2 := by linarith
      have htail' :=
        htail Nt Ns a ha hvolt hvols
          (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M) hT_pos
          (M / 2) hM_half_pos
      -- ψ(M) at M ≥ 2C is degreeCutoffTail, which matches the UNIT 6 RHS modulo
      -- the exponent identity `2 / P.n = 1 / degreeCutoffPower P`.
      rw [show degreePiecewiseTail P K C M =
            degreeCutoffTail P K C M from by
        unfold degreePiecewiseTail
        rw [if_neg (not_lt.mpr hLarge)]]
      simpa [degreeCutoffTail,
        two_div_degree_eq_inv_cutoffPower P] using htail'
    · -- Small-M branch: ψ(M) = 1, and any probability measure of any set is ≤ 1.
      rw [show degreePiecewiseTail P K C M = 1 from by
        unfold degreePiecewiseTail
        rw [if_pos (lt_of_not_ge hLarge)]]
      exact prob_le_one

/-- **Heterogeneous Nelson exponential estimate** (uniform in `(Nt, Ns, a)` at fixed volume).

`∃ K > 0, ∀ (Nt, Ns, a)` with `Nt·a = Lt`, `Ns·a = Ls`,
`∫ (exp(-V_a))² dμ_{GFF,asym} ≤ K`. The B-lean assembly: the chaos decomposition axiom feeds
the proved generic dynamical-cutoff bridge, with `K = 1 + (∫⁻ ψ·2e^{2M}).toReal` (uniform,
since `ψ` is). Heterogeneous analogue of the square `nelson_exponential_estimate_master`. -/
theorem asymNelson_exponential_estimate_iso
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Lt Ls : ℝ) (hLt : 0 < Lt) (hLs : 0 < Ls) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
      (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
      ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (Real.exp (-interactionFunctionalAsym Nt Ns P a mass ω)) ^ 2
        ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) ≤ K := by
  obtain ⟨ψ, hint, hsetup⟩ := asymChaosCutoffDecomposition P mass hmass Lt Ls hLt hLs
  refine ⟨1 + (∫⁻ M in Set.Ioi (0 : ℝ),
      ψ M * ENNReal.ofReal (2 * Real.exp (2 * M))).toReal, by positivity, ?_⟩
  intro Nt Ns _ _ a ha hvolt hvols
  obtain ⟨V_S, E_R, hdec, hsm, htail⟩ := hsetup Nt Ns a ha hvolt hvols
  exact Pphi2.BridgeFromTail.bridgeAxiom_of_setup_real_generic
    (latticeGaussianMeasureAsym Nt Ns a mass ha hmass)
    (interactionFunctionalAsym Nt Ns P a mass)
    (interactionFunctionalAsym_measurable Nt Ns P a mass)
    V_S E_R hdec hsm ψ htail hint

end Pphi2

end

