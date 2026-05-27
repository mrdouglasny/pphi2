/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Exponential moments pass to bounded-continuous weak limits

If a sequence of probability measures `νₙ` on `Configuration E` converges in the
bounded-continuous sense to `ν` and has an exponential-moment bound `∫ exp(|ω f|) dνₙ ≤ Bₙ` with
`Bₙ → B∞`, then the limit inherits it: `exp(|ω f|)` is `ν`-integrable and `∫ exp(|ω f|) dν ≤ B∞`.

The argument is the standard truncation + monotone convergence: `min(exp(|ω f|), M)` is bounded
continuous, so its `ν`-integral is the limit of its `νₙ`-integrals (≤ Bₙ → B∞); then
`lintegral_iSup` sends `M → ∞`.

## Main result

* `GaussianField.weakLimit_exponential_moment` — generic over the test-function space `E`.

This is the space-agnostic core of `Pphi2.limit_exponential_moment` (`IRLimit/CylinderOS.lean`),
reused for the isotropic UV continuum limit on the asymmetric torus.
-/

import GaussianField.Construction
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

noncomputable section

open MeasureTheory Filter Topology

namespace GaussianField

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [DyninMityaginSpace E]

omit [DyninMityaginSpace E] in
/-- **Exponential moments pass to bounded-continuous weak limits.**

If probability measures `νseq n` on `Configuration E` converge to `ν` against bounded continuous
functions and satisfy a (possibly `n`-dependent) exponential-moment bound
`∫ exp(|ω f|) dνseq n ≤ B n` with `B n → Binf`, then `exp(|ω f|)` is `ν`-integrable and
`∫ exp(|ω f|) dν ≤ Binf`. Proof: truncate by `min(·, M+1)` (bounded continuous, so its `ν`-integral
is the limit of the `νseq n`-integrals, each `≤ B n`, hence `≤ Binf`), then monotone convergence
(`lintegral_iSup`) as `M → ∞`.

The convergent-bound form (rather than a constant `B`) lets the sharp lattice bound `K·exp(σ²_n)`
with `σ²_n → G` pass to the limit as `K·exp(G)`. -/
theorem weakLimit_exponential_moment
    (νseq : ℕ → Measure (Configuration E))
    (_hνseq_prob : ∀ n, IsProbabilityMeasure (νseq n))
    (ν : Measure (Configuration E)) [IsProbabilityMeasure ν]
    (hbc : ∀ (g : Configuration E → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Tendsto (fun n => ∫ ω, g ω ∂(νseq n)) atTop (nhds (∫ ω, g ω ∂ν)))
    (f : E) (B : ℕ → ℝ) (Binf : ℝ) (hB : Tendsto B atTop (nhds Binf))
    (h_unif : ∀ n, Integrable (fun ω => Real.exp (|ω f|)) (νseq n) ∧
      ∫ ω, Real.exp (|ω f|) ∂(νseq n) ≤ B n) :
    Integrable (fun ω => Real.exp (|ω f|)) ν ∧
    ∫ ω, Real.exp (|ω f|) ∂ν ≤ Binf := by
  have hexp_nn : ∀ ω : Configuration E, 0 ≤ Real.exp (|ω f|) := fun ω => (Real.exp_pos _).le
  have heval_ae : AEStronglyMeasurable (fun ω : Configuration E => ω f) ν :=
    (configuration_eval_measurable f).aestronglyMeasurable
  have heval_cont : Continuous (fun ω : Configuration E => ω f) := WeakDual.eval_continuous f
  have hexp_meas : AEStronglyMeasurable (fun ω : Configuration E => Real.exp (|ω f|)) ν :=
    (Real.continuous_exp.comp continuous_abs).comp_aestronglyMeasurable heval_ae
  have hgM_nn : ∀ (M : ℕ) (ω : Configuration E),
      0 ≤ min (Real.exp (|ω f|)) (↑(M + 1) : ℝ) :=
    fun M ω => le_min (Real.exp_pos _).le (by positivity)
  -- For each M, ∫ min(exp(|ω f|), M+1) dν ≤ Binf (bounded-continuous limit of νseq integrals,
  -- each ≤ B n, with B n → Binf)
  have hgM_int_le : ∀ M : ℕ, ∫ ω, min (Real.exp (|ω f|)) (↑(M + 1) : ℝ) ∂ν ≤ Binf := by
    intro M
    have hgM_cont : Continuous (fun ω : Configuration E =>
        min (Real.exp (|ω f|)) (↑(M + 1) : ℝ)) :=
      (Real.continuous_exp.comp (continuous_abs.comp heval_cont)).min continuous_const
    have hgM_bound : ∃ C : ℝ, ∀ ω : Configuration E,
        |min (Real.exp (|ω f|)) (↑(M + 1) : ℝ)| ≤ C :=
      ⟨↑(M + 1), fun ω => by rw [abs_of_nonneg (hgM_nn M ω)]; exact min_le_right _ _⟩
    have hbc_gM := hbc _ hgM_cont hgM_bound
    have hgM_le_B : ∀ n, ∫ ω, min (Real.exp (|ω f|)) (↑(M + 1) : ℝ) ∂(νseq n) ≤ B n :=
      fun n => (integral_mono_of_nonneg (ae_of_all _ (hgM_nn M)) (h_unif n).1
        (ae_of_all _ fun ω => min_le_left _ _)).trans (h_unif n).2
    exact le_of_tendsto_of_tendsto' hbc_gM hB hgM_le_B
  -- MCT via lintegral_iSup
  have hgMenr_meas : ∀ M : ℕ, Measurable (fun ω : Configuration E =>
      ENNReal.ofReal (min (Real.exp (|ω f|)) (↑(M + 1) : ℝ))) :=
    fun M => ENNReal.measurable_ofReal.comp
      ((Real.measurable_exp.comp
        (measurable_abs.comp (configuration_eval_measurable f))).min measurable_const)
  have hgMenr_mono : Monotone (fun (M : ℕ) (ω : Configuration E) =>
      ENNReal.ofReal (min (Real.exp (|ω f|)) (↑(M + 1) : ℝ))) :=
    fun m n hmn ω => ENNReal.ofReal_le_ofReal
      (min_le_min_left _ (by exact_mod_cast Nat.add_le_add_right hmn 1))
  have hgMenr_iSup : ∀ ω : Configuration E,
      ⨆ M : ℕ, ENNReal.ofReal (min (Real.exp (|ω f|)) (↑(M + 1) : ℝ)) =
      ENNReal.ofReal (Real.exp (|ω f|)) := by
    intro ω
    apply le_antisymm
    · exact iSup_le fun M => ENNReal.ofReal_le_ofReal (min_le_left _ _)
    · apply le_iSup_of_le (Nat.ceil (Real.exp (|ω f|)))
      apply ENNReal.ofReal_le_ofReal
      apply le_min le_rfl
      have h1 : Real.exp (|ω f|) ≤ ↑⌈Real.exp (|ω f|)⌉₊ := Nat.le_ceil _
      have h2 : (⌈Real.exp (|ω f|)⌉₊ : ℝ) ≤ ↑(⌈Real.exp (|ω f|)⌉₊ + 1) := by push_cast; linarith
      linarith
  have hlint_iSup : ∫⁻ ω, ENNReal.ofReal (Real.exp (|ω f|)) ∂ν =
      ⨆ (M : ℕ), ∫⁻ ω, ENNReal.ofReal (min (Real.exp (|ω f|)) (↑(M + 1) : ℝ)) ∂ν := by
    have : (fun ω : Configuration E => ENNReal.ofReal (Real.exp (|ω f|))) =
        fun ω => ⨆ (M : ℕ), ENNReal.ofReal (min (Real.exp (|ω f|)) (↑(M + 1) : ℝ)) :=
      funext fun ω => (hgMenr_iSup ω).symm
    rw [this, lintegral_iSup hgMenr_meas hgMenr_mono]
  have hlint_gM_le : ∀ (M : ℕ),
      ∫⁻ ω, ENNReal.ofReal (min (Real.exp (|ω f|)) (↑(M + 1) : ℝ)) ∂ν ≤ ENNReal.ofReal Binf := by
    intro M
    have hgM_ae : AEStronglyMeasurable
        (fun ω : Configuration E => min (Real.exp (|ω f|)) (↑(M + 1) : ℝ)) ν :=
      ((Real.continuous_exp.comp continuous_abs).min continuous_const)
        |>.comp_aestronglyMeasurable heval_ae
    have hgM_integrable : Integrable
        (fun ω => min (Real.exp (|ω f|)) (↑(M + 1) : ℝ)) ν :=
      Integrable.of_bound hgM_ae (↑(M + 1) : ℝ) (ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (hgM_nn M ω)]; exact min_le_right _ _)
    rw [← ofReal_integral_eq_lintegral_ofReal hgM_integrable (ae_of_all _ (hgM_nn M))]
    exact ENNReal.ofReal_le_ofReal (hgM_int_le M)
  have hlint_le : ∫⁻ ω, ENNReal.ofReal (Real.exp (|ω f|)) ∂ν ≤ ENNReal.ofReal Binf :=
    hlint_iSup ▸ iSup_le (fun (M : ℕ) => hlint_gM_le M)
  have hint : Integrable (fun ω => Real.exp (|ω f|)) ν := by
    rw [← lintegral_ofReal_ne_top_iff_integrable hexp_meas (ae_of_all _ hexp_nn)]
    exact (hlint_le.trans_lt ENNReal.ofReal_lt_top).ne
  -- Binf ≥ 0: each B n ≥ ∫ exp(|·|) dνseq n ≥ 0, and B n → Binf
  have hB_nn : 0 ≤ Binf :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hB
      (fun n => le_trans (integral_nonneg (fun ω => hexp_nn ω)) (h_unif n).2)
  have hint_le : ∫ ω, Real.exp (|ω f|) ∂ν ≤ Binf := by
    have heq := ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hexp_nn)
    rw [← heq] at hlint_le
    exact (ENNReal.ofReal_le_ofReal_iff hB_nn).mp hlint_le
  exact ⟨hint, hint_le⟩

end GaussianField

end
