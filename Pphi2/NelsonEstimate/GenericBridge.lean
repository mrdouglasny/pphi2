/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Generic real-valued dynamical-cutoff bridge

`bridgeAxiom_of_setup_real` (`LatticeBridge.lean`) packages the abstract engine
`expSqNeg_lintegral_le_of_dynamical_cutoff` (`BridgeFromTail.lean`) into a real-valued
exp-moment bound — but hard-wires the target to `Configuration (FinLatticeField d N)`,
`interactionFunctional d N`, `latticeGaussianMeasure d N`. The engine itself is already
fully generic (`{α} [MeasurableSpace α] (μ) [SFinite μ] (V) …`), so this file lifts the
real-valued wrapper to an **arbitrary measurable target** `(X, μ, V)`.

Instantiating at `FinLatticeField d N` recovers the square Nelson bridge; instantiating at
`AsymLatticeField Nt Ns` gives the heterogeneous one (Phase-2 #3, B-lean step 1).

## Main result

* `bridgeAxiom_of_setup_real_generic` — from a smooth/rough decomposition of `V` with a
  deterministic smooth bound, a rough-error tail bound, and the tail's integrability against
  `2 exp(2t)`, conclude `∫ exp(-V)² dμ ≤ 1 + (∫⁻ ψ·2exp(2t)).toReal` over any probability
  measure `μ`.
-/

import Pphi2.NelsonEstimate.BridgeFromTail

noncomputable section

namespace Pphi2.BridgeFromTail

open MeasureTheory

/-- **Generic real-valued dynamical-cutoff bridge.** Target-agnostic version of
`Pphi2.LatticeBridge.bridgeAxiom_of_setup_real`: for any probability measure `μ` on a
measurable space `X` and measurable `V : X → ℝ`, given an `M`-parametrised smooth/rough
decomposition `V = V_S(M) + E_R(M)` with deterministic smooth bound `V_S(M) ≥ -M/2`, a rough
tail bound `μ {E_R(M) ≤ -M/2} ≤ ψ M` for `M > 0`, and integrability of `ψ(t)·2exp(2t)`,
the Boltzmann `L²` moment is bounded:
`∫ (exp(-V))² dμ ≤ 1 + (∫⁻ ψ(t)·2exp(2t) dt).toReal`. -/
theorem bridgeAxiom_of_setup_real_generic
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (V : X → ℝ) (hV : Measurable V)
    (V_S E_R : ℝ → X → ℝ)
    (hdecomp : ∀ M ω, V ω = V_S M ω + E_R M ω)
    (hsmooth : ∀ M ω, -(M / 2) ≤ V_S M ω)
    (ψ : ℝ → ENNReal)
    (htail : ∀ M, 0 < M → μ {ω | E_R M ω ≤ -(M / 2)} ≤ ψ M)
    (hintegral :
      ∫⁻ M in Set.Ioi (0 : ℝ), ψ M * ENNReal.ofReal (2 * Real.exp (2 * M)) < ⊤) :
    ∫ ω, (Real.exp (-V ω)) ^ 2 ∂μ ≤
      1 + (∫⁻ M in Set.Ioi (0 : ℝ),
        ψ M * ENNReal.ofReal (2 * Real.exp (2 * M))).toReal := by
  set L_ψ : ENNReal := ∫⁻ M in Set.Ioi (0 : ℝ), ψ M * ENNReal.ofReal (2 * Real.exp (2 * M))
  have hL_ψ_lt_top : L_ψ < ⊤ := hintegral
  -- lintegral bound from the (already generic) abstract engine, with μ univ = 1
  have h_lin :
      ∫⁻ ω, ENNReal.ofReal ((Real.exp (-V ω)) ^ 2) ∂μ ≤ 1 + L_ψ := by
    have h := expSqNeg_lintegral_le_of_dynamical_cutoff μ V hV V_S E_R hdecomp hsmooth ψ htail
    rwa [measure_univ] at h
  have h_integrand_nn : ∀ ω, 0 ≤ (Real.exp (-V ω)) ^ 2 := fun _ => sq_nonneg _
  have h_meas_sq : Measurable (fun ω => (Real.exp (-V ω)) ^ 2) := (hV.neg.exp).pow_const 2
  have h_int_eq :
      ∫ ω, (Real.exp (-V ω)) ^ 2 ∂μ =
        (∫⁻ ω, ENNReal.ofReal ((Real.exp (-V ω)) ^ 2) ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h_integrand_nn)
      h_meas_sq.aestronglyMeasurable]
  rw [h_int_eq]
  have h_toReal_le :
      (∫⁻ ω, ENNReal.ofReal ((Real.exp (-V ω)) ^ 2) ∂μ).toReal ≤ (1 + L_ψ).toReal :=
    ENNReal.toReal_mono (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hL_ψ_lt_top⟩).ne h_lin
  refine h_toReal_le.trans ?_
  rw [ENNReal.toReal_add ENNReal.one_ne_top hL_ψ_lt_top.ne]
  simp

end Pphi2.BridgeFromTail
