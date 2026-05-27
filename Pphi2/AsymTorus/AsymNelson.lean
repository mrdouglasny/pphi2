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
import Pphi2.NelsonEstimate.GenericBridge

noncomputable section

open MeasureTheory GaussianField

namespace Pphi2

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
obstruction; mass gap controls the IR. -/
axiom asymChaosCutoffDecomposition
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
              {ω | E_R M ω ≤ -(M / 2)} ≤ ψ M)

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

