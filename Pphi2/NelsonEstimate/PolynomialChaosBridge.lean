/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Polynomial Chaos Bridge: Cluster A Master Theorem

This file packages the four pphi2 Cluster A axioms (the Nelson
exponential estimate in its various lattice flavors) into a single
master theorem `nelson_exponential_estimate_master`, derived from a
single bridge axiom that mirrors the polynomial-chaos concentration
theorem upstream in `markov-semigroups`.

## The bridge axiom

`polynomial_chaos_exp_moment_bridge` is the lattice-Wick-polynomial
specialization of Janson's Theorem 5.10
(`GaussianHilbert.PolynomialChaosConcentration`). It states
the dynamical-cutoff conclusion: for the lattice GFF on `(ℤ/Nℤ)^d`
with spacing `a` and mass `m > 0`, and a fixed even interaction
polynomial `P`,

  ∃ K, ∀ N, ∫ exp(-2 V_a(ω))² dμ_GFF ≤ K  uniformly in N.

The proof in `markov-semigroups` is the three-step Glimm–Jaffe Ch. 8
chain (smooth lower bound on `V_S`; polynomial-chaos concentration
on `E_R`; dynamical cutoff `T = T(M)` and integration). The smooth-side
infrastructure (`SmoothLowerBound.lean`) and the rough-side scaffolding
(`RoughErrorBound.lean`, currently `True`-stub theorems) are already
in pphi2; once `markov-semigroups`'s `polynomial_chaos_concentration`
becomes a theorem and the GFF↔standard-Gaussian change-of-variables
bridge is available, this axiom becomes a derivation rather than an
assertion.

Because pphi2 cannot currently depend on `markov-semigroups` at the
lakefile level (Mathlib pin synchronization across the project family
is a separate maintenance task), we state this bridge as a pphi2-internal
`axiom` with cross-references to the upstream files. When the dependency
wires up, the bridge is replaceable by a one-line `import + apply`.

## What this collapses

- `nelson_exponential_estimate_lattice` (was `axiom`, now `theorem`)
- `exponential_moment_bound` (was `axiom`, now `theorem`)
- `asymNelson_exponential_estimate` (was `axiom`, now `theorem`)

The fourth Cluster A axiom (`asymTorusInteracting_exponentialMomentBound`
in `AsymTorus/AsymTorusOS.lean`) is structurally different — it lifts
the bound to the limit measure via BC convergence — and is handled
in its own derivation (still in `AsymTorusOS.lean`).

Net change: 3 statements with identical shape → 1 master theorem +
1 bridge axiom; net reduction of 2 axioms. The 4th axiom converts
similarly via a separate BC-limit lemma.

## References

- pphi2/docs/polynomial-chaos-concentration.md — the full math writeup
  (Jaffe-suggested LD framing; 2-pass Gemini-vetted).
- markov-semigroups/docs/polynomial-chaos-roadmap.md — the upstream
  implementation plan.
- gaussian-hilbert/GaussianHilbert/PolynomialChaosConcentration.lean
  — the upstream Janson Theorem 5.10 axiom.
- Glimm and Jaffe, *Quantum Physics*, Ch. 8 — the dynamical cutoff proof.
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I.
-/

import Pphi2.WickOrdering.WickPolynomial
import Pphi2.InteractingMeasure.LatticeMeasure
import Pphi2.NelsonEstimate.RoughErrorBound
import Pphi2.NelsonEstimate.IntegrabilityHelpers
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section

open MeasureTheory Real GaussianField Filter

namespace Pphi2

variable (d : ℕ)

private def quarticCutoffTail (K C : ℝ) (M : ℝ) : ENNReal :=
  ENNReal.ofReal
    (2 * Real.exp
      (-(Pphi2.ChaosTailBridge.chaosTailConstant 4) *
        ((M / 2) /
          (2 * Real.sqrt
            (K * (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M) *
              (1 + |Real.log (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M)|) ^ 3))) ^
          ((2 : ℝ) / 4)))

private lemma quarticCutoffTail_le_two (K C M : ℝ) (hM_nonneg : 0 ≤ M) :
    quarticCutoffTail K C M ≤ 2 := by
  unfold quarticCutoffTail
  have h_exp_le_one :
      Real.exp
        (-(Pphi2.ChaosTailBridge.chaosTailConstant 4) *
          ((M / 2) /
            (2 * Real.sqrt
              (K * (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M) *
                (1 + |Real.log (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M)|) ^ 3))) ^
            (1 / 2 : ℝ)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hbase :
        0 ≤
          (Pphi2.ChaosTailBridge.chaosTailConstant 4) *
            ((M / 2) /
              (2 * Real.sqrt
                (K * (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M) *
                  (1 + |Real.log (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M)|) ^ 3))) ^
              ((2 : ℝ) / 4) := by
      have hconst :
          0 ≤ Pphi2.ChaosTailBridge.chaosTailConstant 4 := by
        exact le_of_lt (Pphi2.ChaosTailBridge.chaosTailConstant_pos 4 (by norm_num))
      have hbase_nonneg :
          0 ≤
            (M / 2) /
              (2 * Real.sqrt
                (K * (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M) *
                  (1 + |Real.log (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M)|) ^ 3)) := by
        refine div_nonneg ?_ ?_
        · exact div_nonneg hM_nonneg (by norm_num)
        · positivity
      have hrpow :
          0 ≤
            ((M / 2) /
              (2 * Real.sqrt
                (K * (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M) *
                  (1 + |Real.log (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M)|) ^ 3))) ^
              ((2 : ℝ) / 4) := by
        exact Real.rpow_nonneg hbase_nonneg _
      exact mul_nonneg hconst hrpow
    linarith
  have h_le : ENNReal.ofReal
      (2 * Real.exp
        (-(Pphi2.ChaosTailBridge.chaosTailConstant 4) *
          ((M / 2) /
            (2 * Real.sqrt
              (K * (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M) *
                (1 + |Real.log (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M)|) ^ 3))) ^
            ((2 : ℝ) / 4))) ≤ ENNReal.ofReal 2 := by
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith
  simpa using h_le

private lemma one_add_abs_log_dynamicalCutoff_eq_sqrt
    {C M : ℝ} (hC_pos : 0 < C) (hM : 2 * C < M) :
    1 + |Real.log (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M)| =
      Real.sqrt (M / (2 * C)) := by
  rw [Pphi2.DynamicalCutoff.dynamicalCutoffScale_eq_exp C M hM, Real.log_exp]
  have hdiv_pos : 0 < M / (2 * C) := by
    refine div_pos ?_ ?_
    · linarith
    · positivity
  have hsqrt_ge_one : 1 ≤ Real.sqrt (M / (2 * C)) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    apply Real.sqrt_le_sqrt
    rw [one_le_div (by positivity)]
    linarith
  have hnonpos : 1 - Real.sqrt (M / (2 * C)) ≤ 0 := by
    linarith
  rw [abs_of_nonpos hnonpos]
  ring

private lemma sqrt_exp_sub (s : ℝ) :
    Real.sqrt (Real.exp (1 - s)) = Real.exp ((1 - s) / 2) := by
  rw [Real.sqrt_eq_rpow]
  rw [show (Real.exp (1 - s)) ^ (1 / 2 : ℝ) =
      Real.exp (((1 - s) : ℝ) * (1 / 2 : ℝ)) by
    rw [← Real.exp_mul]]
  ring_nf

private lemma sqrt_pow_three {s : ℝ} (hs : 0 ≤ s) :
    Real.sqrt (s ^ 3) = s ^ (3 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
  norm_num

/-- Explicit canonical-joint rough tail at the dynamical cutoff scale,
specialized to the pure quartic case. -/
theorem canonicalRoughError_cutoff_tail_quartic_uniform
    (P : InteractionPolynomial)
    (h_pure : ∀ m : Fin P.n, P.coeff m = 0)
    (h_quartic : P.n = 4)
    (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (C : ℝ), 0 < C →
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a)
        (hvol : (N : ℝ) * a = L)
        (M : ℝ), 2 * C ≤ M →
          (canonicalJointMeasure 2 N)
            {η | canonicalRoughError 2 N a mass
                (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M) P η ≤ -(M / 2)} ≤
              quarticCutoffTail K C M := by
  obtain ⟨K, hK_pos, htail⟩ :=
    canonicalRoughError_neg_tail_uniform_in_aN P mass L hL hmass
  refine ⟨K, hK_pos, ?_⟩
  intro C hC_pos N _ a ha hvol M hM
  have hT_pos :
      0 < Pphi2.DynamicalCutoff.dynamicalCutoffScale C M :=
    Pphi2.DynamicalCutoff.dynamicalCutoffScale_pos C M
  have hM_pos : 0 < M := by
    linarith
  have htail' :=
    htail N a ha hvol
      (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M) hT_pos
      (M / 2) (by linarith)
  simpa [quarticCutoffTail, h_quartic] using htail'

private def quarticPiecewiseTail (K C : ℝ) (M : ℝ) : ENNReal :=
  if M < 2 * C then 1 else quarticCutoffTail K C M

private lemma quarticPiecewiseTail_le_two
    (K C M : ℝ) (hM_nonneg : 0 ≤ M) :
    quarticPiecewiseTail K C M ≤ 2 := by
  unfold quarticPiecewiseTail
  split_ifs with hM
  · norm_num
  · exact quarticCutoffTail_le_two K C M hM_nonneg

private def quarticDecayConstant (K C : ℝ) : ℝ :=
  Pphi2.ChaosTailBridge.chaosTailConstant 4 *
    Real.sqrt (C / (2 * Real.sqrt K * Real.exp (1 / 2)))

private lemma quarticDecayConstant_pos
    {K C : ℝ} (hK_pos : 0 < K) (hC_pos : 0 < C) :
    0 < quarticDecayConstant K C := by
  unfold quarticDecayConstant
  have hchaos :
      0 < Pphi2.ChaosTailBridge.chaosTailConstant 4 :=
    Pphi2.ChaosTailBridge.chaosTailConstant_pos 4 (by norm_num)
  have hsqrt :
      0 < Real.sqrt (C / (2 * Real.sqrt K * Real.exp (1 / 2))) := by
    apply Real.sqrt_pos.2
    refine div_pos hC_pos ?_
    positivity
  exact mul_pos hchaos hsqrt

private lemma quartic_exp_growth_threshold
    {A B : ℝ} (hA_pos : 0 < A) :
    ∃ S : ℝ, 1 ≤ S ∧
      ∀ s : ℝ, S ≤ s → B * s ^ (2 : ℝ) ≤ A * Real.exp (s / 4) := by
  have h_tendsto :
      Filter.Tendsto
        (fun s : ℝ => A * Real.exp (s / 4) / s ^ (2 : ℝ))
        Filter.atTop Filter.atTop := by
    have h_base :
        Filter.Tendsto
          (fun s : ℝ => (s ^ (2 : ℝ))⁻¹ * Real.exp (s * (1 / 4)))
          Filter.atTop Filter.atTop := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      tendsto_exp_mul_div_rpow_atTop (2 : ℝ) (1 / 4) (by positivity)
    have h_mul :
        Filter.Tendsto
          (fun s : ℝ => A * ((s ^ (2 : ℝ))⁻¹ * Real.exp (s * (1 / 4))))
          Filter.atTop Filter.atTop :=
      Tendsto.const_mul_atTop hA_pos h_base
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h_mul
  obtain ⟨S₀, hS₀⟩ :=
    (Filter.mem_atTop_sets.mp <|
      h_tendsto.eventually_ge_atTop B)
  let S := max 1 S₀
  refine ⟨S, le_max_left _ _, ?_⟩
  intro s hs
  have hs_ge_one : (1 : ℝ) ≤ s := le_trans (le_max_left _ _) hs
  have hs_sq_pos : 0 < s ^ (2 : ℝ) := by
    positivity
  exact (le_div_iff₀ hs_sq_pos).mp <| hS₀ s (le_trans (le_max_right _ _) hs)

/-- The explicit pure-quartic cutoff tail is layer-cake integrable. -/
theorem quarticPiecewiseTail_layerCake_lt_top
    (K C : ℝ) (hK_pos : 0 < K) (hC_pos : 0 < C) :
    ∫⁻ M in Set.Ioi (0 : ℝ),
      quarticPiecewiseTail K C M * ENNReal.ofReal (2 * Real.exp (2 * M)) < ⊤ := by
  let A := quarticDecayConstant K C
  have hA_pos : 0 < A := quarticDecayConstant_pos hK_pos hC_pos
  obtain ⟨S, hS_ge_one, hS_growth⟩ :=
    quartic_exp_growth_threshold (A := A) (B := 6 * C + Real.log 4) hA_pos
  let T₀ : ℝ := 2 * C * S ^ (2 : ℝ)
  have hT₀_pos : 0 < T₀ := by
    positivity
  refine Pphi2.IntegrabilityHelpers.lintegral_layer_cake_lt_top_of_eventual_decay
    (ψ := quarticPiecewiseTail K C) T₀ hT₀_pos ?_ ?_
  · have hsmall_le :
        ∫⁻ t in Set.Ioc (0 : ℝ) T₀,
          quarticPiecewiseTail K C t * ENNReal.ofReal (2 * Real.exp (2 * t)) ≤
          ∫⁻ t in Set.Ioc (0 : ℝ) T₀, ENNReal.ofReal (4 * Real.exp (2 * T₀)) := by
      apply MeasureTheory.setLIntegral_mono' measurableSet_Ioc
      intro M hM
      have hM_nonneg : 0 ≤ M := hM.1.le
      have htail :
          quarticPiecewiseTail K C M ≤ 2 :=
        quarticPiecewiseTail_le_two K C M hM_nonneg
      have hexp :
          2 * Real.exp (2 * M) ≤ 2 * Real.exp (2 * T₀) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        apply Real.exp_le_exp.mpr
        nlinarith [hM.2]
      calc
        quarticPiecewiseTail K C M *
            ENNReal.ofReal (2 * Real.exp (2 * M))
            ≤ 2 * ENNReal.ofReal (2 * Real.exp (2 * T₀)) := by
                exact mul_le_mul' htail (ENNReal.ofReal_le_ofReal hexp)
        _ = ENNReal.ofReal (4 * Real.exp (2 * T₀)) := by
            calc
              2 * ENNReal.ofReal (2 * Real.exp (2 * T₀))
                  = ENNReal.ofReal 2 * ENNReal.ofReal (2 * Real.exp (2 * T₀)) := by
                      norm_num
              _ = ENNReal.ofReal (2 * (2 * Real.exp (2 * T₀))) := by
                    rw [← ENNReal.ofReal_mul]
                    positivity
              _ = ENNReal.ofReal (4 * Real.exp (2 * T₀)) := by
                    congr 1
                    ring
    have hsmall_const :
        ∫⁻ t in Set.Ioc (0 : ℝ) T₀, ENNReal.ofReal (4 * Real.exp (2 * T₀)) < ⊤ := by
      rw [MeasureTheory.setLIntegral_const]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Ioc_lt_top
    exact lt_of_le_of_lt hsmall_le hsmall_const
  · intro M hM
    have hM_gt2C : 2 * C < M := by
      have hS_nonneg : 0 ≤ S := by linarith
      have hS_sq_ge_one : (1 : ℝ) ≤ S ^ (2 : ℝ) := by
        have hS_mul : (1 : ℝ) * 1 ≤ S * S :=
          mul_le_mul hS_ge_one hS_ge_one (by positivity) hS_nonneg
        simpa [pow_two] using hS_mul
      calc
        2 * C ≤ 2 * C * S ^ (2 : ℝ) := by
          nlinarith [hC_pos.le, hS_sq_ge_one]
        _ < M := hM
    have hM_pos : 0 < M := by linarith
    have hdiv_pos : 0 < M / (2 * C) := by
      refine div_pos hM_pos ?_
      positivity
    let s : ℝ := Real.sqrt (M / (2 * C))
    have hs_sq : s ^ (2 : ℝ) = M / (2 * C) := by
      simp [s, Real.sq_sqrt hdiv_pos.le]
    have hs_ge : S ≤ s := by
      have hS_nonneg : 0 ≤ S := by linarith
      rw [show S = Real.sqrt (S ^ (2 : ℝ)) by
        simpa using (Real.sqrt_sq hS_nonneg).symm]
      apply Real.sqrt_le_sqrt
      have : S ^ (2 : ℝ) ≤ M / (2 * C) := by
        refine (le_div_iff₀ ?_).mpr ?_
        · positivity
        · linarith
      simpa [hs_sq] using this
    have hs_ge_one : (1 : ℝ) ≤ s := le_trans hS_ge_one hs_ge
    have hs_nonneg : 0 ≤ s := by linarith
    have hT_eq :
        Pphi2.DynamicalCutoff.dynamicalCutoffScale C M = Real.exp (1 - s) := by
      simpa [s] using Pphi2.DynamicalCutoff.dynamicalCutoffScale_eq_exp C M hM_gt2C
    have hlog_eq :
        1 + |Real.log (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M)| = s := by
      simpa [s] using
        one_add_abs_log_dynamicalCutoff_eq_sqrt (C := C) (M := M) hC_pos hM_gt2C
    have hsqrt_three_le : Real.sqrt (s ^ 3) ≤ s ^ (2 : ℝ) := by
      have hs2_nonneg : 0 ≤ s ^ (2 : ℝ) := by positivity
      have hs_le_sq : s ≤ s ^ (2 : ℝ) := by
        have hs_mul := mul_le_mul_of_nonneg_right hs_ge_one hs_nonneg
        simpa [pow_two, one_mul] using hs_mul
      have hsq :
          s ^ 3 ≤ (s ^ (2 : ℝ)) ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_right hs_le_sq hs2_nonneg
        simpa [pow_two, pow_succ, mul_assoc] using hmul
      have hsqrt := Real.sqrt_le_sqrt hsq
      simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg hs2_nonneg] using hsqrt
    have hden_eq :
        2 *
            Real.sqrt
              (K * Pphi2.DynamicalCutoff.dynamicalCutoffScale C M *
                (1 + |Real.log (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M)|) ^ 3) =
          2 * Real.sqrt K * Real.exp ((1 - s) / 2) * Real.sqrt (s ^ 3) := by
      rw [hT_eq]
      have hlog_exp : 1 + |Real.log (Real.exp (1 - s))| = s := by
        rw [Real.log_exp]
        have hnonpos : 1 - s ≤ 0 := by linarith
        rw [abs_of_nonpos hnonpos]
        ring
      rw [hlog_exp]
      rw [show K * Real.exp (1 - s) * s ^ 3 = K * (Real.exp (1 - s) * s ^ 3) by ring]
      rw [Real.sqrt_mul (le_of_lt hK_pos)]
      rw [show Real.sqrt (Real.exp (1 - s) * s ^ 3) =
          Real.exp ((1 - s) / 2) * Real.sqrt (s ^ 3) by
        rw [Real.sqrt_mul (by positivity)]
        rw [sqrt_exp_sub]]
      ring
    have hden_le :
        2 *
            Real.sqrt
              (K * Pphi2.DynamicalCutoff.dynamicalCutoffScale C M *
                (1 + |Real.log (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M)|) ^ 3) ≤
          2 * Real.sqrt K * Real.exp ((1 - s) / 2) * s ^ (2 : ℝ) := by
      rw [hden_eq]
      have hfac : 0 ≤ 2 * Real.sqrt K * Real.exp ((1 - s) / 2) := by
        positivity
      nlinarith
    have hM_half_eq : M / 2 = C * s ^ (2 : ℝ) := by
      rw [hs_sq]
      field_simp [hC_pos.ne']
    have hratio_eq :
        (M / 2) / (2 * Real.sqrt K * Real.exp ((1 - s) / 2) * s ^ (2 : ℝ)) =
          C / (2 * Real.sqrt K * Real.exp ((1 - s) / 2)) := by
      rw [hM_half_eq]
      have hden : 2 * Real.sqrt K * Real.exp ((1 - s) / 2) ≠ 0 := by
        positivity
      have hs_sq_ne : s ^ (2 : ℝ) ≠ 0 := by
        rw [hs_sq]
        positivity
      field_simp [hden, hs_sq_ne]
    have hratio_lower :
        C / (2 * Real.sqrt K * Real.exp ((1 - s) / 2)) ≤
          (M / 2) /
            (2 *
              Real.sqrt
                (K * Pphi2.DynamicalCutoff.dynamicalCutoffScale C M *
                  (1 + |Real.log (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M)|) ^ 3)) := by
      calc
        C / (2 * Real.sqrt K * Real.exp ((1 - s) / 2))
            =
              (M / 2) / (2 * Real.sqrt K * Real.exp ((1 - s) / 2) * s ^ (2 : ℝ)) :=
          hratio_eq.symm
        _ ≤
            (M / 2) /
              (2 *
                Real.sqrt
                  (K * Pphi2.DynamicalCutoff.dynamicalCutoffScale C M *
                    (1 + |Real.log (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M)|) ^ 3)) := by
            have hden_pos :
                0 <
                  2 *
                    Real.sqrt
                      (K * Pphi2.DynamicalCutoff.dynamicalCutoffScale C M *
                        (1 + |Real.log (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M)|) ^ 3) := by
              have hpow_pos :
                  0 <
                    (1 + |Real.log (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M)|) ^ 3 := by
                positivity
              have hinner_pos :
                  0 <
                    K * Pphi2.DynamicalCutoff.dynamicalCutoffScale C M *
                      (1 + |Real.log (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M)|) ^ 3 := by
                refine mul_pos ?_ hpow_pos
                exact mul_pos hK_pos (Pphi2.DynamicalCutoff.dynamicalCutoffScale_pos C M)
              refine mul_pos (by positivity) (Real.sqrt_pos.2 ?_)
              exact hinner_pos
            have hM_half_nonneg : 0 ≤ M / 2 := by linarith
            refine div_le_div_of_nonneg_left hM_half_nonneg hden_pos hden_le
    have hsqrt_rewrite :
        Real.sqrt (C / (2 * Real.sqrt K * Real.exp ((1 - s) / 2))) =
          Real.sqrt (C / (2 * Real.sqrt K * Real.exp (1 / 2))) * Real.exp (s / 4) := by
      have hsplit :
          C / (2 * Real.sqrt K * Real.exp ((1 - s) / 2)) =
            (C / (2 * Real.sqrt K * Real.exp (1 / 2))) * Real.exp (s / 2) := by
        have hden1 : 2 * Real.sqrt K * Real.exp ((1 - s) / 2) ≠ 0 := by positivity
        have hden2 : 2 * Real.sqrt K * Real.exp (1 / 2) ≠ 0 := by positivity
        rw [show Real.exp ((1 - s) / 2) = Real.exp (1 / 2) * Real.exp (-(s / 2)) by
          rw [show ((1 - s) / 2 : ℝ) = (1 / 2 : ℝ) + (-(s / 2)) by ring]
          rw [Real.exp_add]]
        field_simp [hden1, hden2]
        symm
        calc
          Real.exp (-(s / 2)) * Real.exp (s / 2) =
              Real.exp (-(s / 2) + s / 2) := by
                rw [← Real.exp_add]
          _ = 1 := by
                ring_nf
                rw [Real.exp_zero]
      rw [hsplit, Real.sqrt_mul (by
        refine div_nonneg hC_pos.le ?_
        positivity)]
      rw [show Real.sqrt (Real.exp (s / 2)) = Real.exp (s / 4) by
        rw [Real.sqrt_eq_rpow]
        rw [show (Real.exp (s / 2)) ^ (1 / 2 : ℝ) =
            Real.exp ((s / 2 : ℝ) * (1 / 2 : ℝ)) by
          rw [← Real.exp_mul]]
        ring_nf]
    have hsqrt_lower :
        Real.sqrt (C / (2 * Real.sqrt K * Real.exp ((1 - s) / 2))) ≤
          Real.sqrt
            ((M / 2) /
              (2 *
                Real.sqrt
                  (K * Pphi2.DynamicalCutoff.dynamicalCutoffScale C M *
                    (1 + |Real.log (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M)|) ^ 3))) := by
      exact Real.sqrt_le_sqrt hratio_lower
    have hchaos :
        quarticDecayConstant K C * Real.exp (s / 4) ≤
          Pphi2.ChaosTailBridge.chaosTailConstant 4 *
            Real.sqrt
              ((M / 2) /
                (2 *
                  Real.sqrt
                    (K * Pphi2.DynamicalCutoff.dynamicalCutoffScale C M *
                      (1 + |Real.log (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M)|) ^ 3))) := by
      have hleft_eq :
          quarticDecayConstant K C * Real.exp (s / 4) =
            Pphi2.ChaosTailBridge.chaosTailConstant 4 *
              Real.sqrt (C / (2 * Real.sqrt K * Real.exp ((1 - s) / 2))) := by
        unfold quarticDecayConstant
        rw [mul_assoc, ← hsqrt_rewrite]
      rw [hleft_eq]
      exact mul_le_mul_of_nonneg_left hsqrt_lower
        (le_of_lt (Pphi2.ChaosTailBridge.chaosTailConstant_pos 4 (by norm_num)))
    have htail_bound :
        quarticCutoffTail K C M ≤
          ENNReal.ofReal
            (2 * Real.exp (-(quarticDecayConstant K C * Real.exp (s / 4)))) := by
      unfold quarticCutoffTail
      apply ENNReal.ofReal_le_ofReal
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      apply Real.exp_le_exp.mpr
      have hchaos' :
          quarticDecayConstant K C * Real.exp (s / 4) ≤
            Pphi2.ChaosTailBridge.chaosTailConstant 4 *
              ((M / 2) /
                (2 *
                  Real.sqrt
                    (K * Pphi2.DynamicalCutoff.dynamicalCutoffScale C M *
                      (1 + |Real.log (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M)|) ^ 3))) ^
                ((2 : ℝ) / 4) := by
        simpa [show ((2 : ℝ) / 4) = (1 / 2 : ℝ) by norm_num, Real.sqrt_eq_rpow] using hchaos
      nlinarith [hchaos']
    have hs_sq_ge_one : (1 : ℝ) ≤ s ^ (2 : ℝ) := by
      nlinarith [hs_ge_one]
    have hlog_four_nonneg : 0 ≤ Real.log 4 := by
      exact le_of_lt (Real.log_pos (by norm_num))
    have hgrowth_s :
        (6 * C + Real.log 4) * s ^ (2 : ℝ) ≤ A * Real.exp (s / 4) :=
      hS_growth s hs_ge
    have hlog_growth :
        Real.log 4 + 6 * C * s ^ (2 : ℝ) ≤ A * Real.exp (s / 4) := by
      calc
        Real.log 4 + 6 * C * s ^ (2 : ℝ) ≤
            (Real.log 4 + 6 * C) * s ^ (2 : ℝ) := by
              nlinarith [hs_sq_ge_one, hlog_four_nonneg, hC_pos.le]
        _ = (6 * C + Real.log 4) * s ^ (2 : ℝ) := by ring
        _ ≤ A * Real.exp (s / 4) := hgrowth_s
    have hreal_bound :
        4 * Real.exp (2 * M - A * Real.exp (s / 4)) ≤ Real.exp (-M) := by
      have hM_eq : M = 2 * C * s ^ (2 : ℝ) := by
        rw [hs_sq]
        field_simp [hC_pos.ne']
      have hexp :
          Real.log 4 + (2 * M - A * Real.exp (s / 4)) ≤ -M := by
        rw [hM_eq]
        linarith
      calc
        4 * Real.exp (2 * M - A * Real.exp (s / 4))
            = Real.exp (Real.log 4) * Real.exp (2 * M - A * Real.exp (s / 4)) := by
                rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)]
        _ = Real.exp (Real.log 4 + (2 * M - A * Real.exp (s / 4))) := by
              rw [← Real.exp_add]
        _ ≤ Real.exp (-M) := Real.exp_le_exp.mpr hexp
    unfold quarticPiecewiseTail
    rw [if_neg (not_lt.mpr (le_of_lt hM_gt2C))]
    calc
      quarticCutoffTail K C M * ENNReal.ofReal (2 * Real.exp (2 * M))
          ≤
            ENNReal.ofReal
              (2 * Real.exp (-(quarticDecayConstant K C * Real.exp (s / 4)))) *
              ENNReal.ofReal (2 * Real.exp (2 * M)) := by
                exact mul_le_mul' htail_bound le_rfl
      _ =
          ENNReal.ofReal
            ((2 * Real.exp (-(quarticDecayConstant K C * Real.exp (s / 4)))) *
              (2 * Real.exp (2 * M))) := by
                rw [← ENNReal.ofReal_mul]
                positivity
      _ = ENNReal.ofReal (4 * Real.exp (2 * M - A * Real.exp (s / 4))) := by
            congr 1
            calc
              (2 * Real.exp (-(quarticDecayConstant K C * Real.exp (s / 4)))) *
                  (2 * Real.exp (2 * M))
                  = 4 *
                      (Real.exp (-(quarticDecayConstant K C * Real.exp (s / 4))) *
                        Real.exp (2 * M)) := by ring
              _ = 4 * Real.exp (-(quarticDecayConstant K C * Real.exp (s / 4)) + 2 * M) := by
                    rw [← Real.exp_add]
              _ = 4 * Real.exp (2 * M - A * Real.exp (s / 4)) := by
                    congr 1
                    simpa [A, mul_comm, mul_left_comm, mul_assoc] using
                      show -(quarticDecayConstant K C * Real.exp (s / 4)) + 2 * M =
                          2 * M - A * Real.exp (s / 4) by ring
      _ ≤ ENNReal.ofReal (Real.exp (-M)) := ENNReal.ofReal_le_ofReal hreal_bound

private lemma two_div_degree_eq_inv_cutoffPower (P : InteractionPolynomial) :
    ((2 : ℝ) / P.n) =
      (1 / (Pphi2.DynamicalCutoff.degreeCutoffPower P : ℝ)) := by
  obtain ⟨k, hk⟩ := P.hn_even
  have hk_pos : 0 < k := by
    have hnk : 4 ≤ k + k := by simpa [hk] using P.hn_ge
    omega
  have hkpow : Pphi2.DynamicalCutoff.degreeCutoffPower P = k := by
    dsimp [Pphi2.DynamicalCutoff.degreeCutoffPower]
    rw [hk]
    omega
  rw [hk, hkpow]
  field_simp [show (k : ℝ) ≠ 0 by exact_mod_cast (ne_of_gt hk_pos)]
  simpa [two_mul]

private def degreeCutoffTail
    (P : InteractionPolynomial) (K C : ℝ) (M : ℝ) : ENNReal :=
  ENNReal.ofReal
    (2 * Real.exp
      (-(Pphi2.ChaosTailBridge.chaosTailConstant P.n) *
        ((M / 2) /
          (2 * Real.sqrt
            (K * (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M) *
              (1 + |Real.log (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M)|) ^
                (P.n - 1)))) ^
          (1 / (Pphi2.DynamicalCutoff.degreeCutoffPower P : ℝ))))

private lemma degreeCutoffTail_le_two
    (P : InteractionPolynomial) (K C M : ℝ) (hM_nonneg : 0 ≤ M) :
    degreeCutoffTail P K C M ≤ 2 := by
  unfold degreeCutoffTail
  have h_exp_le_one :
      Real.exp
        (-(Pphi2.ChaosTailBridge.chaosTailConstant P.n) *
          ((M / 2) /
            (2 * Real.sqrt
              (K * (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M) *
                (1 + |Real.log (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M)|) ^
                  (P.n - 1)))) ^
            (1 / (Pphi2.DynamicalCutoff.degreeCutoffPower P : ℝ))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hbase :
        0 ≤
          Pphi2.ChaosTailBridge.chaosTailConstant P.n *
            ((M / 2) /
              (2 * Real.sqrt
                (K * (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M) *
                  (1 + |Real.log (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M)|) ^
                    (P.n - 1)))) ^
              (1 / (Pphi2.DynamicalCutoff.degreeCutoffPower P : ℝ)) := by
      have hconst :
          0 ≤ Pphi2.ChaosTailBridge.chaosTailConstant P.n := by
        exact le_of_lt <|
          Pphi2.ChaosTailBridge.chaosTailConstant_pos P.n (by
            have := P.hn_ge
            omega)
      have hbase_nonneg :
          0 ≤
            (M / 2) /
              (2 * Real.sqrt
                (K * (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M) *
                  (1 + |Real.log (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M)|) ^
                    (P.n - 1))) := by
        refine div_nonneg ?_ ?_
        · exact div_nonneg hM_nonneg (by norm_num)
        · positivity
      have hrpow :
          0 ≤
            ((M / 2) /
              (2 * Real.sqrt
                (K * (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M) *
                  (1 + |Real.log (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M)|) ^
                    (P.n - 1)))) ^
              (1 / (Pphi2.DynamicalCutoff.degreeCutoffPower P : ℝ)) := by
        exact Real.rpow_nonneg hbase_nonneg _
      exact mul_nonneg hconst hrpow
    linarith
  have h_le : ENNReal.ofReal
      (2 * Real.exp
        (-(Pphi2.ChaosTailBridge.chaosTailConstant P.n) *
          ((M / 2) /
            (2 * Real.sqrt
              (K * (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M) *
                (1 + |Real.log (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M)|) ^
                  (P.n - 1)))) ^
            (1 / (Pphi2.DynamicalCutoff.degreeCutoffPower P : ℝ)))) ≤ ENNReal.ofReal 2 := by
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith
  simpa using h_le

theorem canonicalRoughError_cutoff_tail_uniform
    (P : InteractionPolynomial)
    (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (C : ℝ), 0 < C →
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a)
        (hvol : (N : ℝ) * a = L)
        (M : ℝ), 2 * C ≤ M →
          (canonicalJointMeasure 2 N)
            {η | canonicalRoughError 2 N a mass
                (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M) P η ≤ -(M / 2)} ≤
              degreeCutoffTail P K C M := by
  obtain ⟨K, hK_pos, htail⟩ :=
    canonicalRoughError_neg_tail_uniform_in_aN P mass L hL hmass
  refine ⟨K, hK_pos, ?_⟩
  intro C hC_pos N _ a ha hvol M hM
  have hT_pos :
      0 < Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M :=
    Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale_pos P C M
  have hM_pos : 0 < M := by linarith
  have htail' :=
    htail N a ha hvol
      (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M) hT_pos
      (M / 2) (by linarith)
  simpa [degreeCutoffTail, two_div_degree_eq_inv_cutoffPower P] using htail'

private def degreePiecewiseTail
    (P : InteractionPolynomial) (K C : ℝ) (M : ℝ) : ENNReal :=
  if M < 2 * C then 1 else degreeCutoffTail P K C M

private lemma degreePiecewiseTail_le_two
    (P : InteractionPolynomial) (K C M : ℝ) (hM_nonneg : 0 ≤ M) :
    degreePiecewiseTail P K C M ≤ 2 := by
  unfold degreePiecewiseTail
  split_ifs with hM
  · norm_num
  · exact degreeCutoffTail_le_two P K C M hM_nonneg

/-- Integrability of the degree-adapted piecewise cutoff tail.

This is the remaining analytic gap in the fully theorem-derived
general even-`P` bounded-volume bridge. -/
axiom degreePiecewiseTail_layerCake_lt_top
    (P : InteractionPolynomial)
    (K C : ℝ) (hK_pos : 0 < K) (hC_pos : 0 < C) :
    ∫⁻ M in Set.Ioi (0 : ℝ),
      degreePiecewiseTail P K C M *
        ENNReal.ofReal (2 * Real.exp (2 * M)) < ⊤

/-- Bounded-volume bridge from a canonical-joint degree-cutoff rough tail. -/
theorem polynomial_chaos_exp_moment_bridge_bounded_of_tail
    {d : ℕ} (hd : d = 2) (P : InteractionPolynomial)
    (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (C : ℝ)
    (hsmooth :
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a)
        (hvol : (N : ℝ) * a = L)
        (M : ℝ), 2 * C ≤ M →
        ∀ (η : CanonicalJoint d N),
          -(M / 2) ≤
            canonicalSmoothInteraction d N a mass
              (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M) P η)
    (ψ : ℝ → ENNReal)
    (hintegral :
      ∫⁻ M in Set.Ioi (0 : ℝ),
        (if M < 2 * C then (1 : ENNReal) else ψ M) *
          ENNReal.ofReal (2 * Real.exp (2 * M)) < ⊤)
    (htail :
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a)
        (hvol : (N : ℝ) * a = L)
        (M : ℝ), 2 * C ≤ M →
          (canonicalJointMeasure d N)
            {η | canonicalRoughError d N a mass
                (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M) P η ≤ -(M / 2)} ≤
              ψ M) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a)
        (hvol : (N : ℝ) * a = L),
        ∫ ω : Configuration (FinLatticeField d N),
          (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2
          ∂(latticeGaussianMeasure d N a mass ha hmass) ≤ K := by
  let K : ℝ := 1 + (∫⁻ M in Set.Ioi (0 : ℝ),
    (if M < 2 * C then (1 : ENNReal) else ψ M) *
      ENNReal.ofReal (2 * Real.exp (2 * M))).toReal
  refine ⟨K, by
    have h_nonneg :
        0 ≤ (∫⁻ M in Set.Ioi (0 : ℝ),
          (if M < 2 * C then (1 : ENNReal) else ψ M) *
            ENNReal.ofReal (2 * Real.exp (2 * M))).toReal :=
      ENNReal.toReal_nonneg
    exact add_pos_of_pos_of_nonneg (by norm_num) h_nonneg, ?_⟩
  intro N _ a ha hvol
  simpa [K] using
    (expMoment_bound_of_cutoff_degree_tail
      (d := d) P mass L hmass C hsmooth ψ hintegral
      N a ha hvol (htail N a ha hvol))

/-- Bounded-volume bridge with the explicit degree-cutoff tail substituted. -/
theorem polynomial_chaos_exp_moment_bridge_bounded_of_cutoffTail
    (P : InteractionPolynomial)
    (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (K C : ℝ) (hC_pos : 0 < C)
    (hsmooth :
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a)
        (hvol : (N : ℝ) * a = L)
        (M : ℝ), 2 * C ≤ M →
        ∀ (η : CanonicalJoint 2 N),
          -(M / 2) ≤
            canonicalSmoothInteraction 2 N a mass
              (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M) P η)
    (htail :
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a)
        (hvol : (N : ℝ) * a = L)
        (M : ℝ), 2 * C ≤ M →
          (canonicalJointMeasure 2 N)
            {η | canonicalRoughError 2 N a mass
                (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M) P η ≤ -(M / 2)} ≤
              degreeCutoffTail P K C M)
    (hintegral :
      ∫⁻ M in Set.Ioi (0 : ℝ),
        degreePiecewiseTail P K C M *
          ENNReal.ofReal (2 * Real.exp (2 * M)) < ⊤) :
    ∃ K' : ℝ, 0 < K' ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a)
        (hvol : (N : ℝ) * a = L),
        ∫ ω : Configuration (FinLatticeField 2 N),
          (Real.exp (-interactionFunctional 2 N P a mass ω)) ^ 2
          ∂(latticeGaussianMeasure 2 N a mass ha hmass) ≤ K' := by
  exact
    polynomial_chaos_exp_moment_bridge_bounded_of_tail
      (d := 2) rfl P mass L hL hmass C
      hsmooth
      (degreeCutoffTail P K C)
      (by simpa [degreePiecewiseTail] using hintegral)
      htail

/-- General even-`P` bounded-volume bridge with the proved degree-adapted
smooth bound and explicit canonical-joint rough cutoff tail substituted. -/
theorem polynomial_chaos_exp_moment_bridge_bounded
    (P : InteractionPolynomial)
    (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ K' : ℝ, 0 < K' ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a)
        (hvol : (N : ℝ) * a = L),
        ∫ ω : Configuration (FinLatticeField 2 N),
          (Real.exp (-interactionFunctional 2 N P a mass ω)) ^ 2
          ∂(latticeGaussianMeasure 2 N a mass ha hmass) ≤ K' := by
  obtain ⟨C, hC_pos, hsmooth⟩ :=
    canonicalSmoothInteraction_lower_bound_at_cutoff_uniform
      (d := 2) rfl P mass L hL hmass
  obtain ⟨K, hK_pos, htail⟩ :=
    canonicalRoughError_cutoff_tail_uniform
      P mass L hL hmass
  exact
    polynomial_chaos_exp_moment_bridge_bounded_of_cutoffTail
      P mass L hL hmass K C hC_pos
      hsmooth
      (htail C hC_pos)
      (degreePiecewiseTail_layerCake_lt_top P K C hK_pos hC_pos)

/-- Fixed-volume Nelson bridge in the only dimension used downstream. -/
theorem polynomial_chaos_exp_moment_bridge
    (hd : d = 2) (P : InteractionPolynomial)
    (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a)
        (_hvol : (N : ℝ) * a = L),
        ∫ ω : Configuration (FinLatticeField d N),
          (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2
          ∂(latticeGaussianMeasure d N a mass ha hmass) ≤ K := by
  subst d
  simpa using polynomial_chaos_exp_moment_bridge_bounded P mass L hL hmass

/-- Fixed-volume master theorem for the lattice Nelson estimate. -/
theorem nelson_exponential_estimate_master
    (hd : d = 2) (P : InteractionPolynomial)
    (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a)
        (_hvol : (N : ℝ) * a = L),
        ∫ ω : Configuration (FinLatticeField d N),
          (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2
          ∂(latticeGaussianMeasure d N a mass ha hmass) ≤ K :=
  polynomial_chaos_exp_moment_bridge (d := d) hd P mass L hL hmass

/-- Compatibility wrapper preserving the pre-refactor `a ≤ 1` interface used by
`Hypercontractivity.lean`. This remains axiomatic until the non-fixed-volume
consumer is reworked onto the bounded-volume bridge. -/
axiom nelson_exponential_estimate_master_bounded
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (K : ℝ), 0 < K ∧
    ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
    ∀ (N : ℕ) [NeZero N],
    ∫ ω : Configuration (FinLatticeField d N),
        (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2
        ∂(latticeGaussianMeasure d N a mass ha hmass) ≤ K

end Pphi2
