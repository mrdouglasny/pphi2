/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L² bound on the rough-field error

Step 1 of the discharge of `polynomial_chaos_exp_moment_bridge`. Bounds
the L² norm (variance) of the rough-field error of a Wick-polynomial
interaction on the canonical joint Gaussian measure.

## Main result

`rough_error_variance` — for any `InteractionPolynomial P`,
`∫ E_R² ∂μ_joint ≤ K · T · (1 + |log T|)^{P.n − 1}`
with `K` uniform in `(a, N)` at fixed `(L, mass, P)`.

Phase 2 (separate file) will feed this into `polynomial_chaos_concentration`
(Janson's Theorem 5.10, available in `gaussian-hilbert`) to obtain the L^p
and stretched-exponential tail bounds needed by `LatticeRoughErrorSetup`.

## Plan

See `docs/rough-error-variance-plan.md` for the full step-by-step plan and
review history. Five-step structure (S1–S5: pointwise binomial decomposition,
reindexing by smooth/rough degree pair, cross-term orthogonality on the
joint measure, per-term L² bound, final assembly).

## Upstream prerequisites (sorry'd, Phase 2 textbook discharge)

Two `(a, N)`-uniform Glimm–Jaffe Ch. 8 (Thm 8.5.2) Fourier estimates:
- `canonicalSmoothCovariance_le_log` — smooth covariance L^∞ uniform
- `canonicalRoughCovariance_pow_sum_le` — rough covariance L^m sum uniform

Quarantined to `CovarianceSplit.lean` once Codex hits the exact API needed.

## References

- Glimm–Jaffe, *Quantum Physics*, Ch. 8 (dynamical cutoff, Theorem 8.5.2)
- Simon, *The P(φ)₂ Euclidean Quantum Field Theory*, Ch. V (Nelson estimate)
- Janson, *Gaussian Hilbert Spaces*, Theorem 5.10 (polynomial-chaos
  concentration)
-/

import Pphi2.NelsonEstimate.CovarianceBoundsGJ
import Pphi2.NelsonEstimate.ChaosTailBridge
import Pphi2.NelsonEstimate.LatticeBridge
import Pphi2.NelsonEstimate.ChaosMoment
import Pphi2.WickOrdering.WickPolynomial

noncomputable section

open MeasureTheory GaussianField
open scoped BigOperators

namespace Pphi2

variable (d N : ℕ) [NeZero N] (a mass : ℝ)

/-! ## Definitions

Three random variables on the canonical joint Gaussian measure
`canonicalJointMeasure d N = Measure.prod (Π gaussianReal) (Π gaussianReal)`:

* `canonicalSmoothInteraction P T η` — Wick polynomial of `P` evaluated at
  the smooth field, with smooth Wick subtraction `c_S = smoothWickConstant`,
  weighted by lattice volume `a^d` and summed over sites.
* `canonicalFullInteractionJoint P T η` — Wick polynomial of `P` evaluated
  at the full field `φ_S + φ_R`, with full Wick subtraction `c = wickConstant`.
* `canonicalRoughError P T η` — the difference. By the Wick binomial
  identity (`wickMonomial_add_binomial`), this is a sum of cross-terms
  each containing at least one rough-field factor `:φ_R^m:` with `m ≥ 1`.

Names are deliberately distinct from `latticeSmoothInteraction` /
`latticeRoughError` in `LatticeSetup.lean`, which are deterministic
versions on `Configuration` for the dynamical-cutoff layer-cake.
-/

/-- Wick-polynomial interaction evaluated at the smooth field, weighted
by lattice volume and summed over sites. Lives on the canonical joint
Gaussian measure. -/
def canonicalSmoothInteraction (T : ℝ) (P : InteractionPolynomial)
    (η : CanonicalJoint d N) : ℝ :=
  a ^ d * ∑ x : FinLatticeSites d N,
    wickPolynomial P (smoothWickConstant d N a mass T)
      (canonicalSmoothFieldFunction d N a mass T η x)

/-- Wick-polynomial interaction evaluated at the full field `φ_S + φ_R`,
weighted by lattice volume and summed over sites. Lives on the canonical
joint Gaussian measure. -/
def canonicalFullInteractionJoint (T : ℝ) (P : InteractionPolynomial)
    (η : CanonicalJoint d N) : ℝ :=
  a ^ d * ∑ x : FinLatticeSites d N,
    wickPolynomial P (wickConstant d N a mass)
      (canonicalSumFieldFunction d N a mass T η x)

/-- The rough-field error: full Wick interaction minus smooth Wick
interaction. By `wickMonomial_add_binomial` + cancellation of the all-smooth
term, this expands to a sum of cross-terms each containing at least one
factor `:φ_R^m:` with `m ≥ 1`. -/
def canonicalRoughError (T : ℝ) (P : InteractionPolynomial)
    (η : CanonicalJoint d N) : ℝ :=
  canonicalFullInteractionJoint d N a mass T P η -
    canonicalSmoothInteraction d N a mass T P η

@[simp] theorem canonicalFullInteractionJoint_eq_interactionFunctional
    (T : ℝ) (P : InteractionPolynomial) (η : CanonicalJoint d N) :
    canonicalFullInteractionJoint d N a mass T P η =
      interactionFunctional d N P a mass
        (canonicalSumConfig d N a mass T η) := by
  unfold canonicalFullInteractionJoint interactionFunctional
  simp

@[simp] theorem canonicalSmoothInteraction_eq_latticeSmoothInteraction
    (T : ℝ) (P : InteractionPolynomial) (η : CanonicalJoint d N) :
    canonicalSmoothInteraction d N a mass T P η =
      Pphi2.LatticeSetup.latticeSmoothInteraction d N a mass P T
        (canonicalSmoothConfig d N a mass T η) := by
  unfold canonicalSmoothInteraction Pphi2.LatticeSetup.latticeSmoothInteraction
  congr 1
  refine Finset.sum_congr rfl ?_
  intro x hx
  simp [canonicalSmoothConfig, latticeFieldToConfig_apply, finLatticeDelta]

theorem integral_exp_neg_interaction_sq_eq_canonicalJoint
    (P : InteractionPolynomial) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T) :
    ∫ ω : Configuration (FinLatticeField d N),
        (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2
        ∂(latticeGaussianMeasure d N a mass ha hmass) =
      ∫ η : CanonicalJoint d N,
        (Real.exp (-canonicalFullInteractionJoint d N a mass T P η)) ^ 2
        ∂(canonicalJointMeasure d N) := by
  symm
  simpa [canonicalFullInteractionJoint_eq_interactionFunctional
    (d := d) (N := N) (a := a) (mass := mass) T P] using
    (integral_comp_canonicalSumConfig
      (d := d) (N := N) (a := a) (mass := mass)
      ha hmass T hT
      (F := fun ω : Configuration (FinLatticeField d N) =>
        (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2)
      ((interactionFunctional_measurable d N P a mass).neg.exp.pow_const 2))

theorem canonicalSmoothInteraction_lower_bound_at_cutoff_quartic
    (P : InteractionPolynomial) (h_pure : ∀ m : Fin P.n, P.coeff m = 0)
    (h_quartic : P.n = 4)
    (ha : 0 < a) (hmass : 0 < mass)
    (hd : d = 2) (L : ℝ) (hL : 0 < L) (ha_eq : a = L / N)
    (M : ℝ) (hM : 2 * smoothBoundConstant d a mass L ≤ M)
    (η : CanonicalJoint d N) :
    -(M / 2) ≤
      canonicalSmoothInteraction d N a mass
        (Pphi2.DynamicalCutoff.dynamicalCutoffScale
          (smoothBoundConstant d a mass L) M) P η := by
  rw [canonicalSmoothInteraction_eq_latticeSmoothInteraction
    (d := d) (N := N) (a := a) (mass := mass)
    (T := Pphi2.DynamicalCutoff.dynamicalCutoffScale
      (smoothBoundConstant d a mass L) M) P η]
  exact Pphi2.LatticeSetup.latticeSmoothInteraction_lower_bound_at_cutoff_quartic
    (d := d) (N := N) (a := a) (mass := mass)
    P h_pure h_quartic ha hmass hd L hL ha_eq M hM
    (canonicalSmoothConfig d N a mass
      (Pphi2.DynamicalCutoff.dynamicalCutoffScale
        (smoothBoundConstant d a mass L) M) η)

theorem canonicalSmoothInteraction_lower_bound_log_uniform_in_aN
    {d : ℕ} (hd : d = 2) (P : InteractionPolynomial)
    (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a)
        (_hvol : (N : ℝ) * a = L)
        (T : ℝ) (_hT : 0 < T)
        (η : CanonicalJoint d N),
        -(C * (1 + |Real.log T|) ^ Pphi2.DynamicalCutoff.degreeCutoffPower P) ≤
          canonicalSmoothInteraction d N a mass T P η := by
  obtain ⟨A, B, hA_nn, hB_nn, hABound⟩ :=
    smoothWickConstant_le_log_uniform_in_aN hd mass L hL hmass
  obtain ⟨A0, hA0_nn, hpoly_lb⟩ := wickPolynomial_lower_bound_general P
  let K : ℝ := A + B
  let C : ℝ :=
    L ^ d * A0 * (1 + K ^ Pphi2.DynamicalCutoff.degreeCutoffPower P) + 1
  refine ⟨C, by positivity, ?_⟩
  intro N _ a ha hvol T hT η
  have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have ha_eq : a = L / N := by
    apply (eq_div_iff hN_ne).2
    simpa [mul_comm] using hvol
  rw [canonicalSmoothInteraction_eq_latticeSmoothInteraction
    (d := d) (N := N) (a := a) (mass := mass) T P η]
  have hc_S_nn : 0 ≤ smoothWickConstant d N a mass T := by
    unfold smoothWickConstant
    have ha_d_pos : (0 : ℝ) < a ^ d := pow_pos ha d
    apply mul_nonneg (le_of_lt (inv_pos.mpr ha_d_pos))
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro m hm
    exact le_of_lt (smoothCovEigenvalue_pos d N a mass T hT m ha hmass)
  have hu_one : 1 ≤ 1 + |Real.log T| := by
    linarith [abs_nonneg (Real.log T)]
  have hA_le : A ≤ A * (1 + |Real.log T|) := by
    simpa using mul_le_mul_of_nonneg_left hu_one hA_nn
  have h_cS_bound :
      smoothWickConstant d N a mass T ≤ K * (1 + |Real.log T|) := by
    calc
      smoothWickConstant d N a mass T
          ≤ A + B * (1 + |Real.log T|) := hABound N a ha hvol T hT
      _ ≤ A * (1 + |Real.log T|) + B * (1 + |Real.log T|) := by
          linarith
      _ = K * (1 + |Real.log T|) := by
          simp [K]
          ring
  have hcard :
      (Fintype.card (FinLatticeSites d N) : ℝ) = (N : ℝ) ^ d := by
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    push_cast
    rfl
  have hvol_pow :
      a ^ d * (Fintype.card (FinLatticeSites d N) : ℝ) = L ^ d := by
    rw [hcard, ha_eq, div_pow]
    simp only [div_eq_mul_inv]
    field_simp [hN_ne]
  have h_lower :
      -(L ^ d * A0 *
          (1 + smoothWickConstant d N a mass T ^
            Pphi2.DynamicalCutoff.degreeCutoffPower P)) ≤
        a ^ d * ∑ x : FinLatticeSites d N,
          wickPolynomial P (smoothWickConstant d N a mass T)
            ((canonicalSmoothConfig d N a mass T η) (finLatticeDelta d N x)) := by
    have h_site :
        ∀ x : FinLatticeSites d N,
          -(A0 * (1 + smoothWickConstant d N a mass T ^
              Pphi2.DynamicalCutoff.degreeCutoffPower P)) ≤
            wickPolynomial P (smoothWickConstant d N a mass T)
              ((canonicalSmoothConfig d N a mass T η) (finLatticeDelta d N x)) := by
      intro x
      simpa [Pphi2.DynamicalCutoff.degreeCutoffPower] using
        hpoly_lb (smoothWickConstant d N a mass T)
          ((canonicalSmoothConfig d N a mass T η) (finLatticeDelta d N x)) hc_S_nn
    have h_sum_const :
        -((Fintype.card (FinLatticeSites d N) : ℝ) *
            (A0 * (1 + smoothWickConstant d N a mass T ^
              Pphi2.DynamicalCutoff.degreeCutoffPower P))) ≤
          ∑ x : FinLatticeSites d N,
            wickPolynomial P (smoothWickConstant d N a mass T)
              ((canonicalSmoothConfig d N a mass T η) (finLatticeDelta d N x)) := by
      calc
        ∑ x : FinLatticeSites d N,
            wickPolynomial P (smoothWickConstant d N a mass T)
              ((canonicalSmoothConfig d N a mass T η) (finLatticeDelta d N x))
            ≥ ∑ _x : FinLatticeSites d N,
                (-(A0 * (1 + smoothWickConstant d N a mass T ^
                  Pphi2.DynamicalCutoff.degreeCutoffPower P))) :=
              Finset.sum_le_sum fun x _ => h_site x
        _ = (Fintype.card (FinLatticeSites d N) : ℝ) *
              (-(A0 * (1 + smoothWickConstant d N a mass T ^
                Pphi2.DynamicalCutoff.degreeCutoffPower P))) := by
              simp [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        _ = _ := by ring
    have ha_pow_nonneg : 0 ≤ a ^ d := pow_nonneg ha.le d
    have h_scaled := mul_le_mul_of_nonneg_left h_sum_const ha_pow_nonneg
    have hscaled_eq :
        a ^ d *
            -(↑(Fintype.card (FinLatticeSites d N)) *
                (A0 *
                  (1 + smoothWickConstant d N a mass T ^
                    Pphi2.DynamicalCutoff.degreeCutoffPower P))) =
          -(L ^ d * A0 *
              (1 + smoothWickConstant d N a mass T ^
                Pphi2.DynamicalCutoff.degreeCutoffPower P)) := by
      calc
        a ^ d *
            -(↑(Fintype.card (FinLatticeSites d N)) *
                (A0 *
                  (1 + smoothWickConstant d N a mass T ^
                    Pphi2.DynamicalCutoff.degreeCutoffPower P)))
            = -(a ^ d * ↑(Fintype.card (FinLatticeSites d N)) *
                (A0 *
                  (1 + smoothWickConstant d N a mass T ^
                    Pphi2.DynamicalCutoff.degreeCutoffPower P))) := by ring
        _ = -(L ^ d * A0 *
              (1 + smoothWickConstant d N a mass T ^
                Pphi2.DynamicalCutoff.degreeCutoffPower P)) := by
              rw [hvol_pow]
              ring
    rw [hscaled_eq] at h_scaled
    exact h_scaled
  have hu_pow_one :
      1 ≤ (1 + |Real.log T|) ^ Pphi2.DynamicalCutoff.degreeCutoffPower P := by
    have := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hu_one
      (Pphi2.DynamicalCutoff.degreeCutoffPower P)
    simpa using this
  have hpow_bound :
      1 + smoothWickConstant d N a mass T ^ Pphi2.DynamicalCutoff.degreeCutoffPower P ≤
        (1 + K ^ Pphi2.DynamicalCutoff.degreeCutoffPower P) *
          (1 + |Real.log T|) ^ Pphi2.DynamicalCutoff.degreeCutoffPower P := by
    have hpow :
        smoothWickConstant d N a mass T ^ Pphi2.DynamicalCutoff.degreeCutoffPower P ≤
          (K * (1 + |Real.log T|)) ^ Pphi2.DynamicalCutoff.degreeCutoffPower P := by
      exact pow_le_pow_left₀ hc_S_nn h_cS_bound _
    calc
      1 + smoothWickConstant d N a mass T ^ Pphi2.DynamicalCutoff.degreeCutoffPower P
          ≤ 1 + (K * (1 + |Real.log T|)) ^
              Pphi2.DynamicalCutoff.degreeCutoffPower P := by
                linarith
      _ = 1 + K ^ Pphi2.DynamicalCutoff.degreeCutoffPower P *
            (1 + |Real.log T|) ^ Pphi2.DynamicalCutoff.degreeCutoffPower P := by
              rw [mul_pow]
      _ ≤ (1 + |Real.log T|) ^ Pphi2.DynamicalCutoff.degreeCutoffPower P +
            K ^ Pphi2.DynamicalCutoff.degreeCutoffPower P *
              (1 + |Real.log T|) ^ Pphi2.DynamicalCutoff.degreeCutoffPower P := by
              linarith
      _ = (1 + K ^ Pphi2.DynamicalCutoff.degreeCutoffPower P) *
            (1 + |Real.log T|) ^ Pphi2.DynamicalCutoff.degreeCutoffPower P := by
              ring
  have h_sum :
      -(L ^ d * A0 * (1 + K ^ Pphi2.DynamicalCutoff.degreeCutoffPower P) *
          (1 + |Real.log T|) ^ Pphi2.DynamicalCutoff.degreeCutoffPower P) ≤
        a ^ d * ∑ x : FinLatticeSites d N,
          wickPolynomial P (smoothWickConstant d N a mass T)
            ((canonicalSmoothConfig d N a mass T η) (finLatticeDelta d N x)) := by
    have h_chain :
        -(L ^ d * A0 * (1 + K ^ Pphi2.DynamicalCutoff.degreeCutoffPower P) *
            (1 + |Real.log T|) ^ Pphi2.DynamicalCutoff.degreeCutoffPower P) ≤
          -(L ^ d * A0 *
            (1 + smoothWickConstant d N a mass T ^
              Pphi2.DynamicalCutoff.degreeCutoffPower P)) := by
      apply neg_le_neg
      have hpref_nonneg : 0 ≤ L ^ d * A0 := by positivity
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hpow_bound hpref_nonneg
    exact le_trans h_chain h_lower
  have hC_ge :
      L ^ d * A0 * (1 + K ^ Pphi2.DynamicalCutoff.degreeCutoffPower P) ≤ C := by
    simp [C]
  have h_sum' :
      -(C * (1 + |Real.log T|) ^ Pphi2.DynamicalCutoff.degreeCutoffPower P) ≤
        a ^ d * ∑ x : FinLatticeSites d N,
          wickPolynomial P (smoothWickConstant d N a mass T)
            ((canonicalSmoothConfig d N a mass T η) (finLatticeDelta d N x)) := by
    have h_chain :
        -(C * (1 + |Real.log T|) ^ Pphi2.DynamicalCutoff.degreeCutoffPower P) ≤
          -(L ^ d * A0 * (1 + K ^ Pphi2.DynamicalCutoff.degreeCutoffPower P) *
            (1 + |Real.log T|) ^ Pphi2.DynamicalCutoff.degreeCutoffPower P) := by
      apply neg_le_neg
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hC_ge
          (show 0 ≤ (1 + |Real.log T|) ^ Pphi2.DynamicalCutoff.degreeCutoffPower P by
            positivity)
    exact le_trans h_chain h_sum
  simpa using h_sum'

theorem canonicalSmoothInteraction_lower_bound_at_cutoff_uniform
    {d : ℕ} (hd : d = 2) (P : InteractionPolynomial)
    (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a)
        (_hvol : (N : ℝ) * a = L)
        (M : ℝ), 2 * C ≤ M →
        ∀ (η : CanonicalJoint d N),
          -(M / 2) ≤
            canonicalSmoothInteraction d N a mass
              (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M) P η := by
  obtain ⟨C, hC_pos, hbound⟩ :=
    canonicalSmoothInteraction_lower_bound_log_uniform_in_aN
      (d := d) hd P mass L hL hmass
  refine ⟨C, hC_pos, ?_⟩
  intro N _ a ha hvol M hM η
  have hT_pos :
      0 < Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M :=
    Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale_pos P C M
  have h_smooth :=
    hbound N a ha hvol
      (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M) hT_pos η
  have h_cutoff :
      C * (1 + |Real.log (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M)|) ^
          Pphi2.DynamicalCutoff.degreeCutoffPower P ≤ M / 2 :=
    Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale_log_pow_le P C M hC_pos hM
  linarith

/-- **Nelson bridge reduction from a large-`M` canonical-joint rough tail.**

Fix a cutoff constant `C` with the property that the smooth interaction at
`T(M) = dynamicalCutoffScale C M` is bounded below by `-M/2` for all `M ≥ 2C`.
If, in the same regime, the canonical-joint rough error has tail bound `ψ`,
then the lattice Boltzmann `L²` moment is bounded by the layer-cake integral
for the piecewise tail

* `1` on `0 < M < 2C` (trivial small-`M` control),
* `ψ(M)` on `M ≥ 2C`.

This is the bridge-facing reduction theorem for the genuine field
decomposition: all remaining substance is in the large-`M` rough tail. -/
theorem expMoment_bound_of_cutoff_quartic_tail
    {d : ℕ} (P : InteractionPolynomial)
    (mass L : ℝ) (hmass : 0 < mass)
    (C : ℝ)
    (hsmooth :
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a)
        (_hvol : (N : ℝ) * a = L)
        (M : ℝ), 2 * C ≤ M →
        ∀ (η : CanonicalJoint d N),
          -(M / 2) ≤
            canonicalSmoothInteraction d N a mass
              (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M) P η)
    (ψ : ℝ → ENNReal)
    (hintegral :
      ∫⁻ M in Set.Ioi (0 : ℝ),
        (if M < 2 * C then (1 : ENNReal) else ψ M) *
          ENNReal.ofReal (2 * Real.exp (2 * M)) < ⊤) :
    ∀ (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a)
      (_hvol : (N : ℝ) * a = L),
      (∀ M : ℝ, 2 * C ≤ M →
        (canonicalJointMeasure d N)
          {η | canonicalRoughError d N a mass
              (Pphi2.DynamicalCutoff.dynamicalCutoffScale C M) P η ≤ -(M / 2)} ≤
            ψ M) →
      ∫ ω : Configuration (FinLatticeField d N),
          (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2
          ∂(latticeGaussianMeasure d N a mass ha hmass) ≤
        1 + (∫⁻ M in Set.Ioi (0 : ℝ),
          (if M < 2 * C then (1 : ENNReal) else ψ M) *
            ENNReal.ofReal (2 * Real.exp (2 * M))).toReal := by
  intro N _ a ha hvol htail
  let Tfun : ℝ → ℝ := fun M =>
    Pphi2.DynamicalCutoff.dynamicalCutoffScale C M
  let π : ℝ → CanonicalJoint d N → Configuration (FinLatticeField d N) := fun M =>
    canonicalSumConfig d N a mass (Tfun M)
  let V_S : ℝ → CanonicalJoint d N → ℝ := fun M η =>
    if hlarge : 2 * C ≤ M then
      canonicalSmoothInteraction d N a mass (Tfun M) P η
    else
      -(M / 2)
  let E_R : ℝ → CanonicalJoint d N → ℝ := fun M η =>
    if hlarge : 2 * C ≤ M then
      canonicalRoughError d N a mass (Tfun M) P η
    else
      canonicalFullInteractionJoint d N a mass (Tfun M) P η + M / 2
  exact
    Pphi2.LatticeBridge.bridgeAxiom_of_varying_coupled_setup_real
      (d := d) (P := P) (mass := mass)
      a ha hmass N
      (μ := canonicalJointMeasure d N)
      π
      (hπ_meas := by
        intro M
        exact canonicalSumConfig_measurable (d := d) (N := N) (a := a) (mass := mass) (Tfun M))
      (hpush := by
        intro M
        exact canonicalJointMeasure_map_canonicalSumConfig
          (d := d) (N := N) (a := a) (mass := mass) ha hmass (Tfun M)
          (Pphi2.DynamicalCutoff.dynamicalCutoffScale_pos C M))
      V_S E_R
      (hdecomp := by
        intro M η
        by_cases hlarge : 2 * C ≤ M
        · simp [π, V_S, E_R, Tfun, hlarge, canonicalRoughError]
        · simp [π, V_S, E_R, Tfun, hlarge, canonicalFullInteractionJoint_eq_interactionFunctional]
      )
      (hsmooth := by
        intro M η
        by_cases hlarge : 2 * C ≤ M
        · simpa [V_S, hlarge] using hsmooth N a ha hvol M hlarge η
        · simp [V_S, hlarge]
      )
      (ψ := fun M => if M < 2 * C then (1 : ENNReal) else ψ M)
      (htail := by
        intro M hM
        by_cases hlarge : 2 * C ≤ M
        · simpa [E_R, hlarge, if_neg (not_lt.mpr hlarge)] using htail M hlarge
        · have htriv :
            (canonicalJointMeasure d N)
                {η | E_R M η ≤ -(M / 2)} ≤ 1 := by
              refine le_trans (measure_mono (Set.subset_univ _)) ?_
              simp
          simpa [E_R, hlarge, if_pos (lt_of_not_ge hlarge)] using htriv
      )
      hintegral

/-- Degree-adapted bridge reduction from a large-`M` canonical-joint rough tail.

This is the general even-`P` analogue of
`expMoment_bound_of_cutoff_quartic_tail`, using the degree-dependent
cutoff scale `degreeDynamicalCutoffScale`. -/
theorem expMoment_bound_of_cutoff_degree_tail
    {d : ℕ} (P : InteractionPolynomial)
    (mass L : ℝ) (hmass : 0 < mass)
    (C : ℝ)
    (hsmooth :
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a)
        (_hvol : (N : ℝ) * a = L)
        (M : ℝ), 2 * C ≤ M →
        ∀ (η : CanonicalJoint d N),
          -(M / 2) ≤
            canonicalSmoothInteraction d N a mass
              (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M) P η)
    (ψ : ℝ → ENNReal)
    (hintegral :
      ∫⁻ M in Set.Ioi (0 : ℝ),
        (if M < 2 * C then (1 : ENNReal) else ψ M) *
          ENNReal.ofReal (2 * Real.exp (2 * M)) < ⊤) :
    ∀ (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a)
      (_hvol : (N : ℝ) * a = L),
      (∀ M : ℝ, 2 * C ≤ M →
        (canonicalJointMeasure d N)
          {η | canonicalRoughError d N a mass
              (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M) P η ≤ -(M / 2)} ≤
            ψ M) →
      ∫ ω : Configuration (FinLatticeField d N),
          (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2
          ∂(latticeGaussianMeasure d N a mass ha hmass) ≤
        1 + (∫⁻ M in Set.Ioi (0 : ℝ),
          (if M < 2 * C then (1 : ENNReal) else ψ M) *
            ENNReal.ofReal (2 * Real.exp (2 * M))).toReal := by
  intro N _ a ha hvol htail
  let Tfun : ℝ → ℝ := fun M =>
    Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M
  let π : ℝ → CanonicalJoint d N → Configuration (FinLatticeField d N) := fun M =>
    canonicalSumConfig d N a mass (Tfun M)
  let V_S : ℝ → CanonicalJoint d N → ℝ := fun M η =>
    if hlarge : 2 * C ≤ M then
      canonicalSmoothInteraction d N a mass (Tfun M) P η
    else
      -(M / 2)
  let E_R : ℝ → CanonicalJoint d N → ℝ := fun M η =>
    if hlarge : 2 * C ≤ M then
      canonicalRoughError d N a mass (Tfun M) P η
    else
      canonicalFullInteractionJoint d N a mass (Tfun M) P η + M / 2
  exact
    Pphi2.LatticeBridge.bridgeAxiom_of_varying_coupled_setup_real
      (d := d) (P := P) (mass := mass)
      a ha hmass N
      (μ := canonicalJointMeasure d N)
      π
      (hπ_meas := by
        intro M
        exact canonicalSumConfig_measurable (d := d) (N := N) (a := a) (mass := mass) (Tfun M))
      (hpush := by
        intro M
        exact canonicalJointMeasure_map_canonicalSumConfig
          (d := d) (N := N) (a := a) (mass := mass) ha hmass (Tfun M)
          (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale_pos P C M))
      V_S E_R
      (hdecomp := by
        intro M η
        by_cases hlarge : 2 * C ≤ M
        · simp [π, V_S, E_R, Tfun, hlarge, canonicalRoughError]
        · simp [π, V_S, E_R, Tfun, hlarge, canonicalFullInteractionJoint_eq_interactionFunctional]
      )
      (hsmooth := by
        intro M η
        by_cases hlarge : 2 * C ≤ M
        · simpa [V_S, hlarge] using hsmooth N a ha hvol M hlarge η
        · simp [V_S, hlarge]
      )
      (ψ := fun M => if M < 2 * C then (1 : ENNReal) else ψ M)
      (htail := by
        intro M hM
        by_cases hlarge : 2 * C ≤ M
        · simpa [E_R, hlarge, if_neg (not_lt.mpr hlarge)] using htail M hlarge
        · have htriv :
            (canonicalJointMeasure d N)
                {η | E_R M η ≤ -(M / 2)} ≤ 1 := by
              refine le_trans (measure_mono (Set.subset_univ _)) ?_
              simp
          simpa [E_R, hlarge, if_pos (lt_of_not_ge hlarge)] using htriv
      )
      hintegral

/-- **Canonical-joint rough tail from a transported standard-Gaussian chaos.**

If the canonical rough error is represented pointwise by an `L²` random
variable `F` on the transported standard Gaussian, and `F` lies in
`wienerChaosLE n m` with an external norm bound `‖F‖ ≤ K`, then the
negative tail of `canonicalRoughError` is controlled by the universal
Janson exponent from `chaos_neg_tail_bound`.

This isolates the only remaining substantive work for the Nelson bridge:
construct the standard-Gaussian representative of `canonicalRoughError`
and prove its chaos-membership / norm control. The measure transport itself
is now theorem-level. -/
theorem canonicalRoughError_neg_tail_of_stdGaussian
    {d N : ℕ} [NeZero N] (a mass T : ℝ) (P : InteractionPolynomial)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ c_m : ℝ, 0 < c_m ∧
      ∀ (F : MeasureTheory.Lp ℝ 2
          (GaussianHilbert.stdGaussianFin
            (Fintype.card (CanonicalJointSumIndex d N)))),
        F ∈ GaussianHilbert.wienerChaosLE
              (Fintype.card (CanonicalJointSumIndex d N)) m →
        ∀ (K : ℝ), 0 < K → ‖F‖ ≤ K →
        (∀ η : CanonicalJoint d N,
          (F : (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ)
            (canonicalJointStdGaussianMeasurableEquiv d N η) =
              canonicalRoughError d N a mass T P η) →
        ∀ (t : ℝ), 0 < t →
          (canonicalJointMeasure d N)
            {η | canonicalRoughError d N a mass T P η ≤ -t} ≤
              2 * ENNReal.ofReal
                (Real.exp (-c_m * (t / (2 * K)) ^ ((2 : ℝ) / m))) := by
  obtain ⟨c_m, hc_m_pos, htail⟩ :=
    Pphi2.ChaosTailBridge.chaos_neg_tail_bound
      (Fintype.card (CanonicalJointSumIndex d N)) m hm
  refine ⟨c_m, hc_m_pos, ?_⟩
  intro F hF_chaos K hK_pos hF_norm hrepr t ht
  have hset_eq :
      {η | canonicalRoughError d N a mass T P η ≤ -t} =
        (canonicalJointStdGaussianMeasurableEquiv d N) ⁻¹'
          {ω |
            (F : (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ) ω ≤ -t} := by
    ext η
    simp [hrepr η]
  have hset_meas :
      MeasurableSet
        {ω |
          (F : (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ) ω ≤ -t} := by
    simpa [Set.preimage, Set.setOf_mem_eq] using
      (MeasureTheory.Lp.stronglyMeasurable F).measurable
        (isClosed_Iic.measurableSet : MeasurableSet (Set.Iic (-t)))
  calc
    (canonicalJointMeasure d N) {η | canonicalRoughError d N a mass T P η ≤ -t}
        =
      (canonicalJointMeasure d N)
        ((canonicalJointStdGaussianMeasurableEquiv d N) ⁻¹'
          {ω |
            (F : (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ) ω ≤ -t}) := by
          rw [hset_eq]
    _ =
      (Measure.map
        (canonicalJointStdGaussianMeasurableEquiv d N)
        (canonicalJointMeasure d N))
        {ω |
          (F : (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ) ω ≤ -t} := by
            symm
            rw [Measure.map_apply
              (canonicalJointStdGaussianMeasurableEquiv d N).measurable hset_meas]
    _ =
      (GaussianHilbert.stdGaussianFin
        (Fintype.card (CanonicalJointSumIndex d N)))
        {ω |
          (F : (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ) ω ≤ -t} := by
            rw [canonicalJointMeasure_map_stdGaussian (d := d) (N := N)]
    _ ≤
      2 * ENNReal.ofReal
        (Real.exp (-c_m * (t / (2 * K)) ^ ((2 : ℝ) / m))) :=
          htail F hF_chaos K hK_pos hF_norm t ht

/-- The explicit-constant version of
`canonicalRoughError_neg_tail_of_stdGaussian`. This is the form needed for
uniformity in the lattice size `N`: the tail exponent is fixed to
`chaosTailConstant m`, which depends only on the chaos degree. -/
theorem canonicalRoughError_neg_tail_of_stdGaussian_explicit
    {d N : ℕ} [NeZero N] (a mass T : ℝ) (P : InteractionPolynomial)
    (m : ℕ) (hm : 1 ≤ m) :
    ∀ (F : MeasureTheory.Lp ℝ 2
        (GaussianHilbert.stdGaussianFin
          (Fintype.card (CanonicalJointSumIndex d N)))),
      F ∈ GaussianHilbert.wienerChaosLE
            (Fintype.card (CanonicalJointSumIndex d N)) m →
      ∀ (K : ℝ), 0 < K → ‖F‖ ≤ K →
      (∀ η : CanonicalJoint d N,
        (F : (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ)
          (canonicalJointStdGaussianMeasurableEquiv d N η) =
            canonicalRoughError d N a mass T P η) →
      ∀ (t : ℝ), 0 < t →
        (canonicalJointMeasure d N)
          {η | canonicalRoughError d N a mass T P η ≤ -t} ≤
            2 * ENNReal.ofReal
              (Real.exp
                (-(Pphi2.ChaosTailBridge.chaosTailConstant m) *
                  (t / (2 * K)) ^ ((2 : ℝ) / m))) := by
  intro F hF_chaos K hK_pos hF_norm hrepr t ht
  have hset_eq :
      {η | canonicalRoughError d N a mass T P η ≤ -t} =
        (canonicalJointStdGaussianMeasurableEquiv d N) ⁻¹'
          {ω |
            (F : (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ) ω ≤ -t} := by
    ext η
    simp [hrepr η]
  have hset_meas :
      MeasurableSet
        {ω |
          (F : (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ) ω ≤ -t} := by
    simpa [Set.preimage, Set.setOf_mem_eq] using
      (MeasureTheory.Lp.stronglyMeasurable F).measurable
        (isClosed_Iic.measurableSet : MeasurableSet (Set.Iic (-t)))
  calc
    (canonicalJointMeasure d N) {η | canonicalRoughError d N a mass T P η ≤ -t}
        =
      (canonicalJointMeasure d N)
        ((canonicalJointStdGaussianMeasurableEquiv d N) ⁻¹'
          {ω |
            (F : (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ) ω ≤ -t}) := by
          rw [hset_eq]
    _ =
      (Measure.map
        (canonicalJointStdGaussianMeasurableEquiv d N)
        (canonicalJointMeasure d N))
        {ω |
          (F : (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ) ω ≤ -t} := by
            symm
            rw [Measure.map_apply
              (canonicalJointStdGaussianMeasurableEquiv d N).measurable hset_meas]
    _ =
      (GaussianHilbert.stdGaussianFin
        (Fintype.card (CanonicalJointSumIndex d N)))
        {ω |
          (F : (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ) ω ≤ -t} := by
            rw [canonicalJointMeasure_map_stdGaussian (d := d) (N := N)]
    _ ≤
      2 * ENNReal.ofReal
        (Real.exp
          (-(Pphi2.ChaosTailBridge.chaosTailConstant m) *
            (t / (2 * K)) ^ ((2 : ℝ) / m))) :=
          Pphi2.ChaosTailBridge.chaos_neg_tail_bound_explicit
            (Fintype.card (CanonicalJointSumIndex d N)) m hm
            F hF_chaos K hK_pos hF_norm t ht

/-- AE-transport version of
`canonicalRoughError_neg_tail_of_stdGaussian_explicit`.

This is the form compatible with the natural `Lp` representative
`hf.toLp f`: the transported standard-Gaussian function only agrees with the
canonical rough error almost everywhere, not pointwise. -/
theorem canonicalRoughError_neg_tail_of_stdGaussian_explicit_ae
    {d N : ℕ} [NeZero N] (a mass T : ℝ) (P : InteractionPolynomial)
    (m : ℕ) (hm : 1 ≤ m) :
    ∀ (F : MeasureTheory.Lp ℝ 2
        (GaussianHilbert.stdGaussianFin
          (Fintype.card (CanonicalJointSumIndex d N)))),
      F ∈ GaussianHilbert.wienerChaosLE
            (Fintype.card (CanonicalJointSumIndex d N)) m →
      ∀ (K : ℝ), 0 < K → ‖F‖ ≤ K →
      (∀ᵐ η ∂(canonicalJointMeasure d N),
        (F : (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ)
          (canonicalJointStdGaussianMeasurableEquiv d N η) =
            canonicalRoughError d N a mass T P η) →
      ∀ (t : ℝ), 0 < t →
        (canonicalJointMeasure d N)
          {η | canonicalRoughError d N a mass T P η ≤ -t} ≤
            2 * ENNReal.ofReal
              (Real.exp
                (-(Pphi2.ChaosTailBridge.chaosTailConstant m) *
                  (t / (2 * K)) ^ ((2 : ℝ) / m))) := by
  intro F hF_chaos K hK_pos hF_norm hrepr t ht
  have hset_ae :
      {η | canonicalRoughError d N a mass T P η ≤ -t} =ᵐ[canonicalJointMeasure d N]
        (canonicalJointStdGaussianMeasurableEquiv d N) ⁻¹'
          {ω |
            (F : (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ) ω ≤ -t} := by
    filter_upwards [hrepr] with η hη
    change
      (canonicalRoughError d N a mass T P η ≤ -t) =
        (((F : (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ)
          (canonicalJointStdGaussianMeasurableEquiv d N η)) ≤ -t)
    rw [← hη]
  have hset_meas :
      MeasurableSet
        {ω |
          (F : (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ) ω ≤ -t} := by
    simpa [Set.preimage, Set.setOf_mem_eq] using
      (MeasureTheory.Lp.stronglyMeasurable F).measurable
        (isClosed_Iic.measurableSet : MeasurableSet (Set.Iic (-t)))
  calc
    (canonicalJointMeasure d N) {η | canonicalRoughError d N a mass T P η ≤ -t}
        =
      (canonicalJointMeasure d N)
        ((canonicalJointStdGaussianMeasurableEquiv d N) ⁻¹'
          {ω |
            (F : (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ) ω ≤ -t}) := by
          exact measure_congr hset_ae
    _ =
      (Measure.map
        (canonicalJointStdGaussianMeasurableEquiv d N)
        (canonicalJointMeasure d N))
        {ω |
          (F : (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ) ω ≤ -t} := by
            symm
            rw [Measure.map_apply
              (canonicalJointStdGaussianMeasurableEquiv d N).measurable]
            exact hset_meas
    _ =
      (GaussianHilbert.stdGaussianFin
        (Fintype.card (CanonicalJointSumIndex d N)))
        {ω |
          (F : (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ) ω ≤ -t} := by
            rw [canonicalJointMeasure_map_stdGaussian (d := d) (N := N)]
    _ ≤
      2 * ENNReal.ofReal
        (Real.exp
          (-(Pphi2.ChaosTailBridge.chaosTailConstant m) *
            (t / (2 * K)) ^ ((2 : ℝ) / m))) :=
      Pphi2.ChaosTailBridge.chaos_neg_tail_bound_explicit
        (Fintype.card (CanonicalJointSumIndex d N)) m hm
        F hF_chaos K hK_pos hF_norm t ht

private lemma wickMonomial_one_eq_hermiteEval (n : ℕ) (x : ℝ) :
    wickMonomial n 1 x =
      ((Polynomial.hermite n).map (Int.castRingHom ℝ)).eval x := by
  simpa using (wickMonomial_eq_hermite n 1 (by norm_num : (0 : ℝ) < 1) x)

/-- Exported for the asym chaos-membership port: product Wick monomials are Hermite
multi-evaluations at unit covariance. -/
lemma multiWickMonomial_eq_hermiteMultiEval
    {n : ℕ} (α : Fin n → ℕ) (ξ : Fin n → ℝ) :
    (∏ i, wickMonomial (α i) 1 (ξ i)) =
      GaussianHilbert.hermiteMultiEval α ξ := by
  unfold GaussianHilbert.hermiteMultiEval
  refine Finset.prod_congr rfl ?_
  intro i hi
  exact wickMonomial_one_eq_hermiteEval (α i) (ξ i)

/-- Exported for the asym chaos-membership port: local and root Wick monomial names agree. -/
theorem wickMonomial_eq_root_local : ∀ (n : ℕ) (c x : ℝ),
    wickMonomial n c x = _root_.wickMonomial n c x
  | 0, _, _ => rfl
  | 1, _, _ => rfl
  | n + 2, c, x => by
      simp only [Pphi2.wickMonomial_succ_succ, _root_.wickMonomial_succ_succ]
      rw [wickMonomial_eq_root_local (n + 1), wickMonomial_eq_root_local n]

private theorem finite_hermite_sum_mem_wienerChaosLE
    {n d : ℕ} (s : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℝ)
    (hdeg : ∀ α ∈ s, GaussianHilbert.MultiIndex.totalDegree α ≤ d)
    (f : (Fin n → ℝ) → ℝ)
    (hf_def : f = fun ξ => ∑ α ∈ s, c α * GaussianHilbert.hermiteMultiEval α ξ)
    (hf : MeasureTheory.MemLp f 2 (GaussianHilbert.stdGaussianFin n)) :
    (hf.toLp f) ∈ GaussianHilbert.wienerChaosLE n d := by
  classical
  have h_toLp :
      hf.toLp f =
        ∑ α ∈ s, c α • GaussianHilbert.hermiteMultiLp α := by
    apply MeasureTheory.Lp.ext
    refine (MemLp.coeFn_toLp hf).trans ?_
    rw [hf_def]
    have h_sum :
        (((∑ α ∈ s, c α • GaussianHilbert.hermiteMultiLp α :
            MeasureTheory.Lp ℝ 2 (GaussianHilbert.stdGaussianFin n)) :
          (Fin n → ℝ) → ℝ)) =ᵐ[GaussianHilbert.stdGaussianFin n]
          ∑ α ∈ s,
            (((c α • GaussianHilbert.hermiteMultiLp α :
                MeasureTheory.Lp ℝ 2 (GaussianHilbert.stdGaussianFin n)) :
              (Fin n → ℝ) → ℝ)) :=
      MeasureTheory.Lp.coeFn_finset_sum s
        (fun α => c α • GaussianHilbert.hermiteMultiLp α)
    have h_each :
        ∀ α ∈ (s : Set (Fin n → ℕ)),
          ∀ᵐ x ∂(GaussianHilbert.stdGaussianFin n),
            ((c α • GaussianHilbert.hermiteMultiLp α :
                MeasureTheory.Lp ℝ 2 (GaussianHilbert.stdGaussianFin n)) :
              (Fin n → ℝ) → ℝ) x =
              c α * GaussianHilbert.hermiteMultiEval α x := by
      intro α _
      refine (MeasureTheory.Lp.coeFn_smul (c α)
          (GaussianHilbert.hermiteMultiLp α)).trans ?_
      filter_upwards [GaussianHilbert.hermiteMultiLp_coeFn α] with x hx
      simp [hx, smul_eq_mul]
    have h_ae_all :
        ∀ᵐ x ∂(GaussianHilbert.stdGaussianFin n),
          ∀ α ∈ (s : Set (Fin n → ℕ)),
            ((c α • GaussianHilbert.hermiteMultiLp α :
                MeasureTheory.Lp ℝ 2 (GaussianHilbert.stdGaussianFin n)) :
              (Fin n → ℝ) → ℝ) x =
              c α * GaussianHilbert.hermiteMultiEval α x :=
      (ae_ball_iff s.countable_toSet).mpr h_each
    have h_func :
        (fun ξ => ∑ α ∈ s, c α * GaussianHilbert.hermiteMultiEval α ξ)
          =ᵐ[GaussianHilbert.stdGaussianFin n]
            ∑ α ∈ s,
              (((c α • GaussianHilbert.hermiteMultiLp α :
                  MeasureTheory.Lp ℝ 2 (GaussianHilbert.stdGaussianFin n)) :
                (Fin n → ℝ) → ℝ)) := by
      filter_upwards [h_ae_all] with x hx
      rw [Finset.sum_apply]
      exact (Finset.sum_congr rfl fun α hα => hx α (Finset.mem_coe.mpr hα)).symm
    exact h_func.trans h_sum.symm
  rw [h_toLp]
  apply Submodule.sum_mem
  intro α hα
  apply Submodule.smul_mem
  have h_mem :
      GaussianHilbert.hermiteMultiLp α ∈
        GaussianHilbert.wienerChaos n
          (GaussianHilbert.MultiIndex.totalDegree α) :=
    GaussianHilbert.hermiteMultiLp_mem_wienerChaos n α
  have h_lt :
      GaussianHilbert.MultiIndex.totalDegree α < d + 1 :=
    Nat.lt_succ_of_le (hdeg α hα)
  have h_le :
      GaussianHilbert.wienerChaos n
          (GaussianHilbert.MultiIndex.totalDegree α) ≤
        GaussianHilbert.wienerChaosLE n d := by
    rw [GaussianHilbert.wienerChaosLE]
    refine le_iSup_of_le (GaussianHilbert.MultiIndex.totalDegree α) ?_
    refine le_iSup_of_le (Finset.mem_range.mpr h_lt) ?_
    exact le_rfl
  exact h_le h_mem

private theorem finite_wick_sum_mem_wienerChaosLE
    {n d : ℕ} (s : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℝ)
    (hdeg : ∀ α ∈ s, GaussianHilbert.MultiIndex.totalDegree α ≤ d)
    (f : (Fin n → ℝ) → ℝ)
    (hf_def : f = fun ξ => ∑ α ∈ s, c α * ∏ i, wickMonomial (α i) 1 (ξ i))
    (hf : MeasureTheory.MemLp f 2 (GaussianHilbert.stdGaussianFin n)) :
    (hf.toLp f) ∈ GaussianHilbert.wienerChaosLE n d := by
  classical
  have h_eq :
      f = fun ξ => ∑ α ∈ s, c α * GaussianHilbert.hermiteMultiEval α ξ := by
    rw [hf_def]
    funext ξ
    refine Finset.sum_congr rfl ?_
    intro α hα
    rw [multiWickMonomial_eq_hermiteMultiEval α ξ]
  exact finite_hermite_sum_mem_wienerChaosLE s c hdeg f h_eq hf

/-- Exported for the asym chaos-membership port: finite indexed Wick sums of
bounded total degree lie in the corresponding finite Wiener chaos filtration. -/
theorem finite_indexed_wick_sum_mem_wienerChaosLE
    {ι : Type*} {n d : ℕ}
    (s : Finset ι) (β : ι → Fin n → ℕ) (c : ι → ℝ)
    (hdeg : ∀ i ∈ s, GaussianHilbert.MultiIndex.totalDegree (β i) ≤ d)
    (f : (Fin n → ℝ) → ℝ)
    (hf_def : f = fun ξ => ∑ i ∈ s, c i * ∏ j, wickMonomial (β i j) 1 (ξ j))
    (hf : MeasureTheory.MemLp f 2 (GaussianHilbert.stdGaussianFin n)) :
    (hf.toLp f) ∈ GaussianHilbert.wienerChaosLE n d := by
  classical
  have h_eq :
      f = fun ξ => ∑ i ∈ s, c i * GaussianHilbert.hermiteMultiEval (β i) ξ := by
    rw [hf_def]
    funext ξ
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [multiWickMonomial_eq_hermiteMultiEval (β i) ξ]
  have h_toLp :
      hf.toLp f =
        ∑ i ∈ s, c i • GaussianHilbert.hermiteMultiLp (β i) := by
    apply MeasureTheory.Lp.ext
    refine (MemLp.coeFn_toLp hf).trans ?_
    rw [h_eq]
    have h_sum :
        (((∑ i ∈ s, c i • GaussianHilbert.hermiteMultiLp (β i) :
            MeasureTheory.Lp ℝ 2 (GaussianHilbert.stdGaussianFin n)) :
          (Fin n → ℝ) → ℝ)) =ᵐ[GaussianHilbert.stdGaussianFin n]
          ∑ i ∈ s,
            (((c i • GaussianHilbert.hermiteMultiLp (β i) :
                MeasureTheory.Lp ℝ 2 (GaussianHilbert.stdGaussianFin n)) :
              (Fin n → ℝ) → ℝ)) :=
      MeasureTheory.Lp.coeFn_finset_sum s
        (fun i => c i • GaussianHilbert.hermiteMultiLp (β i))
    have h_each :
        ∀ i ∈ (s : Set ι),
          ∀ᵐ x ∂(GaussianHilbert.stdGaussianFin n),
            ((c i • GaussianHilbert.hermiteMultiLp (β i) :
                MeasureTheory.Lp ℝ 2 (GaussianHilbert.stdGaussianFin n)) :
              (Fin n → ℝ) → ℝ) x =
              c i * GaussianHilbert.hermiteMultiEval (β i) x := by
      intro i _
      refine (MeasureTheory.Lp.coeFn_smul (c i)
          (GaussianHilbert.hermiteMultiLp (β i))).trans ?_
      filter_upwards [GaussianHilbert.hermiteMultiLp_coeFn (β i)] with x hx
      simp [hx, smul_eq_mul]
    have h_ae_all :
        ∀ᵐ x ∂(GaussianHilbert.stdGaussianFin n),
          ∀ i ∈ (s : Set ι),
            ((c i • GaussianHilbert.hermiteMultiLp (β i) :
                MeasureTheory.Lp ℝ 2 (GaussianHilbert.stdGaussianFin n)) :
              (Fin n → ℝ) → ℝ) x =
              c i * GaussianHilbert.hermiteMultiEval (β i) x :=
      (ae_ball_iff s.countable_toSet).mpr h_each
    have h_func :
        (fun ξ => ∑ i ∈ s, c i * GaussianHilbert.hermiteMultiEval (β i) ξ)
          =ᵐ[GaussianHilbert.stdGaussianFin n]
            ∑ i ∈ s,
              (((c i • GaussianHilbert.hermiteMultiLp (β i) :
                  MeasureTheory.Lp ℝ 2 (GaussianHilbert.stdGaussianFin n)) :
                (Fin n → ℝ) → ℝ)) := by
      filter_upwards [h_ae_all] with x hx
      rw [Finset.sum_apply]
      exact (Finset.sum_congr rfl fun i hi => hx i (Finset.mem_coe.mpr hi)).symm
    exact h_func.trans h_sum.symm
  rw [h_toLp]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  have h_mem :
      GaussianHilbert.hermiteMultiLp (β i) ∈
        GaussianHilbert.wienerChaos n
          (GaussianHilbert.MultiIndex.totalDegree (β i)) :=
    GaussianHilbert.hermiteMultiLp_mem_wienerChaos n (β i)
  have h_lt :
      GaussianHilbert.MultiIndex.totalDegree (β i) < d + 1 :=
    Nat.lt_succ_of_le (hdeg i hi)
  have h_le :
      GaussianHilbert.wienerChaos n
          (GaussianHilbert.MultiIndex.totalDegree (β i)) ≤
        GaussianHilbert.wienerChaosLE n d := by
    rw [GaussianHilbert.wienerChaosLE]
    refine le_iSup_of_le (GaussianHilbert.MultiIndex.totalDegree (β i)) ?_
    refine le_iSup_of_le (Finset.mem_range.mpr h_lt) ?_
    exact le_rfl
  exact h_le h_mem

private abbrev canonicalStdIndex (d N : ℕ) [NeZero N] :=
  Fin (Fintype.card (CanonicalJointSumIndex d N))

private def canonicalStdInlIndex (d N : ℕ) [NeZero N]
    (m : Fin d → Fin N) : canonicalStdIndex d N :=
  Fintype.equivFin (CanonicalJointSumIndex d N) (Sum.inl m)

private def canonicalStdInrIndex (d N : ℕ) [NeZero N]
    (m : Fin d → Fin N) : canonicalStdIndex d N :=
  Fintype.equivFin (CanonicalJointSumIndex d N) (Sum.inr m)

private def canonicalJointMultiIndexOfPair (d N : ℕ) [NeZero N]
    (αS αR : (Fin d → Fin N) → ℕ) :
    canonicalStdIndex d N → ℕ :=
  fun i => Sum.elim αS αR ((Fintype.equivFin (CanonicalJointSumIndex d N)).symm i)

@[simp] private lemma canonicalJointMultiIndexOfPair_inl
    (αS αR : (Fin d → Fin N) → ℕ) (m : Fin d → Fin N) :
    canonicalJointMultiIndexOfPair d N αS αR
        (canonicalStdInlIndex d N m) = αS m := by
  unfold canonicalJointMultiIndexOfPair canonicalStdInlIndex
  simp

@[simp] private lemma canonicalJointMultiIndexOfPair_inr
    (αS αR : (Fin d → Fin N) → ℕ) (m : Fin d → Fin N) :
    canonicalJointMultiIndexOfPair d N αS αR
        (canonicalStdInrIndex d N m) = αR m := by
  unfold canonicalJointMultiIndexOfPair canonicalStdInrIndex
  simp

private lemma canonicalJointMultiIndexOfPair_totalDegree
    (αS αR : (Fin d → Fin N) → ℕ) :
    GaussianHilbert.MultiIndex.totalDegree
        (canonicalJointMultiIndexOfPair d N αS αR) =
      (∑ m : Fin d → Fin N, αS m) +
        ∑ m : Fin d → Fin N, αR m := by
  unfold GaussianHilbert.MultiIndex.totalDegree canonicalJointMultiIndexOfPair
  simpa [Fintype.sum_sum_type] using
    (Equiv.sum_comp
      (Fintype.equivFin (CanonicalJointSumIndex d N)).symm
      (fun s : CanonicalJointSumIndex d N => Sum.elim αS αR s))

private lemma canonicalJointMultiIndexOfPair_wick_prod
    (αS αR : (Fin d → Fin N) → ℕ) (ξ : canonicalStdIndex d N → ℝ) :
    (∏ i : canonicalStdIndex d N,
        wickMonomial
          (Sum.elim αS αR
            ((Fintype.equivFin (CanonicalJointSumIndex d N)).symm i))
          1 (ξ i)) =
      (∏ m : Fin d → Fin N,
        wickMonomial (αS m) 1
          (ξ (canonicalStdInlIndex d N m))) *
      ∏ m : Fin d → Fin N,
        wickMonomial (αR m) 1
          (ξ (canonicalStdInrIndex d N m)) := by
  let f : CanonicalJointSumIndex d N → ℝ :=
    fun s =>
      wickMonomial (Sum.elim αS αR s) 1
        (ξ (Fintype.equivFin (CanonicalJointSumIndex d N) s))
  calc
    ∏ i : Fin (Fintype.card (CanonicalJointSumIndex d N)),
        wickMonomial
          (Sum.elim αS αR
            ((Fintype.equivFin (CanonicalJointSumIndex d N)).symm i))
          1 (ξ i)
      = ∏ s : CanonicalJointSumIndex d N, f s := by
          simpa [f] using
            (Equiv.prod_comp
              (Fintype.equivFin (CanonicalJointSumIndex d N)).symm
              (fun s : CanonicalJointSumIndex d N =>
                wickMonomial (Sum.elim αS αR s) 1
                  (ξ (Fintype.equivFin (CanonicalJointSumIndex d N) s))))
    _ = (∏ m : Fin d → Fin N, f (Sum.inl m)) *
          ∏ m : Fin d → Fin N, f (Sum.inr m) := by
            rw [show (∏ s : CanonicalJointSumIndex d N,
                wickMonomial (Sum.elim αS αR s) 1
                  (ξ (Fintype.equivFin (CanonicalJointSumIndex d N) s))) =
                  ∏ s : CanonicalJointSumIndex d N, f s by
                  simp [f]]
            exact Fintype.prod_sum_type f
    _ = (∏ m : Fin d → Fin N,
          wickMonomial (αS m) 1
            (ξ (canonicalStdInlIndex d N m))) *
        ∏ m : Fin d → Fin N,
          wickMonomial (αR m) 1
            (ξ (canonicalStdInrIndex d N m)) := by
              simp [f, canonicalStdInlIndex, canonicalStdInrIndex]

@[simp] private lemma canonicalJointStdGaussianMeasurableEquiv_symm_fst
    (ξ : canonicalStdIndex d N → ℝ) (m : Fin d → Fin N) :
    ((canonicalJointStdGaussianMeasurableEquiv d N).symm ξ).1 m =
      ξ (canonicalStdInlIndex d N m) := by
  rfl

@[simp] private lemma canonicalJointStdGaussianMeasurableEquiv_symm_snd
    (ξ : canonicalStdIndex d N → ℝ) (m : Fin d → Fin N) :
    ((canonicalJointStdGaussianMeasurableEquiv d N).symm ξ).2 m =
      ξ (canonicalStdInrIndex d N m) := by
  rfl

/-- Exported for the asym chaos-membership port: multinomial Wick expansion coefficient. -/
def wickExpansionCoeff {ι : Type*} [Fintype ι]
    (k : ℕ) (γ : ι → ℝ) (α : ι → ℕ) : ℝ :=
  ((k.factorial : ℝ) / ∏ j, ((α j).factorial : ℝ)) *
    ∏ j, γ j ^ α j

private def canonicalSiteCrossStd
    (T : ℝ) (x : FinLatticeSites d N) (k j : ℕ)
    (ξ : canonicalStdIndex d N → ℝ) : ℝ :=
  wickMonomial j (smoothWickConstant d N a mass T)
      (canonicalSmoothFieldFunction d N a mass T
        ((canonicalJointStdGaussianMeasurableEquiv d N).symm ξ) x) *
    wickMonomial (k - j) (roughWickConstant d N a mass T)
      (canonicalRoughFieldFunction d N a mass T
        ((canonicalJointStdGaussianMeasurableEquiv d N).symm ξ) x)

private lemma canonicalEigenvalue_pos_local
    (_ha : 0 < a) (hmass : 0 < mass) (m : Fin d → Fin N) :
    0 < canonicalEigenvalue d N a mass m := by
  unfold canonicalEigenvalue
  have hsum_nonneg : 0 ≤ ∑ i : Fin d, latticeEigenvalue1d N a (m i) :=
    Finset.sum_nonneg (fun i _ => latticeEigenvalue1d_nonneg N a (m i))
  nlinarith [sq_pos_of_pos hmass]

private lemma canonicalSmoothWeight_nonneg_local
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (m : Fin d → Fin N) :
    0 ≤ canonicalSmoothWeight d N a mass T m := by
  unfold canonicalSmoothWeight
  exact div_nonneg (le_of_lt (Real.exp_pos _))
    (canonicalEigenvalue_pos_local (d := d) (N := N) (a := a) (mass := mass) ha hmass m).le

private lemma canonicalRoughWeight_nonneg_local
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T) (m : Fin d → Fin N) :
    0 ≤ canonicalRoughWeight d N a mass T m := by
  unfold canonicalRoughWeight
  have hLam :=
    canonicalEigenvalue_pos_local (d := d) (N := N) (a := a) (mass := mass) ha hmass m
  have h_exp_le : Real.exp (-T * canonicalEigenvalue d N a mass m) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith
  have h_num : 0 ≤ 1 - Real.exp (-T * canonicalEigenvalue d N a mass m) := by
    linarith
  exact div_nonneg h_num hLam.le

private lemma canonicalSmoothGamma_sq_sum_eq_wickConstant
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (x : FinLatticeSites d N) :
    ∑ m : Fin d → Fin N, (canonicalSmoothGamma d N a mass T x m) ^ 2 =
      smoothWickConstant d N a mass T := by
  rw [← canonicalSmoothFieldFunction_self_moment_eq_smoothWickConstant
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x]
  unfold canonicalSmoothFieldFunction_self_moment_diag
  rw [canonicalSmoothFieldFunction_covariance_eq
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x x]
  unfold canonicalSmoothCovariance
  have ha_d_pos : (0 : ℝ) < a ^ d := pow_pos ha d
  calc
    ∑ m : Fin d → Fin N, (canonicalSmoothGamma d N a mass T x m) ^ 2
      = ∑ m : Fin d → Fin N,
          (a ^ d : ℝ)⁻¹ *
            (canonicalSmoothWeight d N a mass T m *
              latticeFourierProductBasisFun N d m x *
              latticeFourierProductBasisFun N d m x /
              latticeFourierProductNormSq N d m) := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              have hC :
                  0 ≤ canonicalSmoothWeight d N a mass T m /
                    latticeFourierProductNormSq N d m := by
                apply div_nonneg
                · exact canonicalSmoothWeight_nonneg_local
                    (d := d) (N := N) (a := a) (mass := mass) ha hmass T m
                · exact (latticeFourierProductNormSq_pos (N := N) d m).le
              have h_sq :
                  Real.sqrt
                      (canonicalSmoothWeight d N a mass T m /
                        latticeFourierProductNormSq N d m) *
                    Real.sqrt
                      (canonicalSmoothWeight d N a mass T m /
                        latticeFourierProductNormSq N d m) =
                  canonicalSmoothWeight d N a mass T m /
                    latticeFourierProductNormSq N d m :=
                Real.mul_self_sqrt hC
              have h_gamma :
                  canonicalSmoothGamma d N a mass T x m =
                    (Real.sqrt (a ^ d))⁻¹ *
                      (Real.sqrt
                          (canonicalSmoothWeight d N a mass T m /
                            latticeFourierProductNormSq N d m) *
                        latticeFourierProductBasisFun N d m x) := by
                rfl
              rw [h_gamma, sq]
              calc
                ((Real.sqrt (a ^ d))⁻¹ *
                    (Real.sqrt
                        (canonicalSmoothWeight d N a mass T m /
                          latticeFourierProductNormSq N d m) *
                      latticeFourierProductBasisFun N d m x)) *
                    ((Real.sqrt (a ^ d))⁻¹ *
                      (Real.sqrt
                          (canonicalSmoothWeight d N a mass T m /
                            latticeFourierProductNormSq N d m) *
                        latticeFourierProductBasisFun N d m x))
                    =
                  ((Real.sqrt (a ^ d))⁻¹ * (Real.sqrt (a ^ d))⁻¹) *
                    (Real.sqrt
                        (canonicalSmoothWeight d N a mass T m /
                          latticeFourierProductNormSq N d m) *
                      Real.sqrt
                        (canonicalSmoothWeight d N a mass T m /
                          latticeFourierProductNormSq N d m)) *
                    (latticeFourierProductBasisFun N d m x *
                      latticeFourierProductBasisFun N d m x) := by
                        ring
                _ = (a ^ d : ℝ)⁻¹ *
                    (canonicalSmoothWeight d N a mass T m /
                      latticeFourierProductNormSq N d m) *
                    ((latticeFourierProductBasisFun N d m x) ^ 2) := by
                      rw [← mul_inv, ← Real.sqrt_mul (le_of_lt ha_d_pos),
                        Real.sqrt_mul_self (le_of_lt ha_d_pos), h_sq]
                      ring
                _ = (a ^ d : ℝ)⁻¹ *
                    (canonicalSmoothWeight d N a mass T m *
                      latticeFourierProductBasisFun N d m x *
                      latticeFourierProductBasisFun N d m x /
                      latticeFourierProductNormSq N d m) := by
                        ring
    _ = (a ^ d : ℝ)⁻¹ *
        ∑ m : Fin d → Fin N,
          canonicalSmoothWeight d N a mass T m *
            latticeFourierProductBasisFun N d m x *
            latticeFourierProductBasisFun N d m x /
            latticeFourierProductNormSq N d m := by
              rw [← Finset.mul_sum]

private lemma canonicalRoughGamma_sq_sum_eq_wickConstant
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (x : FinLatticeSites d N) :
    ∑ m : Fin d → Fin N, (canonicalRoughGamma d N a mass T x m) ^ 2 =
      roughWickConstant d N a mass T := by
  rw [← canonicalRoughFieldFunction_self_moment_eq_roughWickConstant
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x]
  unfold canonicalRoughFieldFunction_self_moment_diag
  rw [canonicalRoughFieldFunction_covariance_eq
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x x]
  unfold canonicalRoughCovariance
  have ha_d_pos : (0 : ℝ) < a ^ d := pow_pos ha d
  calc
    ∑ m : Fin d → Fin N, (canonicalRoughGamma d N a mass T x m) ^ 2
      = ∑ m : Fin d → Fin N,
          (a ^ d : ℝ)⁻¹ *
            (canonicalRoughWeight d N a mass T m *
              latticeFourierProductBasisFun N d m x *
              latticeFourierProductBasisFun N d m x /
              latticeFourierProductNormSq N d m) := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              have hC :
                  0 ≤ canonicalRoughWeight d N a mass T m /
                    latticeFourierProductNormSq N d m := by
                apply div_nonneg
                · exact canonicalRoughWeight_nonneg_local
                    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT m
                · exact (latticeFourierProductNormSq_pos (N := N) d m).le
              have h_sq :
                  Real.sqrt
                      (canonicalRoughWeight d N a mass T m /
                        latticeFourierProductNormSq N d m) *
                    Real.sqrt
                      (canonicalRoughWeight d N a mass T m /
                        latticeFourierProductNormSq N d m) =
                  canonicalRoughWeight d N a mass T m /
                    latticeFourierProductNormSq N d m :=
                Real.mul_self_sqrt hC
              have h_gamma :
                  canonicalRoughGamma d N a mass T x m =
                    (Real.sqrt (a ^ d))⁻¹ *
                      (Real.sqrt
                          (canonicalRoughWeight d N a mass T m /
                            latticeFourierProductNormSq N d m) *
                        latticeFourierProductBasisFun N d m x) := by
                rfl
              rw [h_gamma, sq]
              calc
                ((Real.sqrt (a ^ d))⁻¹ *
                    (Real.sqrt
                        (canonicalRoughWeight d N a mass T m /
                          latticeFourierProductNormSq N d m) *
                      latticeFourierProductBasisFun N d m x)) *
                    ((Real.sqrt (a ^ d))⁻¹ *
                      (Real.sqrt
                          (canonicalRoughWeight d N a mass T m /
                            latticeFourierProductNormSq N d m) *
                        latticeFourierProductBasisFun N d m x))
                    =
                  ((Real.sqrt (a ^ d))⁻¹ * (Real.sqrt (a ^ d))⁻¹) *
                    (Real.sqrt
                        (canonicalRoughWeight d N a mass T m /
                          latticeFourierProductNormSq N d m) *
                      Real.sqrt
                        (canonicalRoughWeight d N a mass T m /
                          latticeFourierProductNormSq N d m)) *
                    (latticeFourierProductBasisFun N d m x *
                      latticeFourierProductBasisFun N d m x) := by
                        ring
                _ = (a ^ d : ℝ)⁻¹ *
                    (canonicalRoughWeight d N a mass T m /
                      latticeFourierProductNormSq N d m) *
                    ((latticeFourierProductBasisFun N d m x) ^ 2) := by
                      rw [← mul_inv, ← Real.sqrt_mul (le_of_lt ha_d_pos),
                        Real.sqrt_mul_self (le_of_lt ha_d_pos), h_sq]
                      ring
                _ = (a ^ d : ℝ)⁻¹ *
                    (canonicalRoughWeight d N a mass T m *
                      latticeFourierProductBasisFun N d m x *
                      latticeFourierProductBasisFun N d m x /
                      latticeFourierProductNormSq N d m) := by
                        ring
    _ = (a ^ d : ℝ)⁻¹ *
        ∑ m : Fin d → Fin N,
          canonicalRoughWeight d N a mass T m *
            latticeFourierProductBasisFun N d m x *
            latticeFourierProductBasisFun N d m x /
            latticeFourierProductNormSq N d m := by
              rw [← Finset.mul_sum]

private lemma canonicalSmoothFieldFunction_std_eq_sum_gamma
    (T : ℝ) (x : FinLatticeSites d N) (ξ : canonicalStdIndex d N → ℝ) :
    canonicalSmoothFieldFunction d N a mass T
        ((canonicalJointStdGaussianMeasurableEquiv d N).symm ξ) x =
      ∑ m : Fin d → Fin N,
        canonicalSmoothGamma d N a mass T x m * ξ (canonicalStdInlIndex d N m) := by
  simpa using
    (canonicalSmoothFieldFunctionOfFst_eq_sum_gamma
      (d := d) (N := N) (a := a) (mass := mass) T
      (((canonicalJointStdGaussianMeasurableEquiv d N).symm ξ).1) x)

private lemma canonicalRoughFieldFunction_std_eq_sum_gamma
    (T : ℝ) (x : FinLatticeSites d N) (ξ : canonicalStdIndex d N → ℝ) :
    canonicalRoughFieldFunction d N a mass T
        ((canonicalJointStdGaussianMeasurableEquiv d N).symm ξ) x =
      ∑ m : Fin d → Fin N,
        canonicalRoughGamma d N a mass T x m * ξ (canonicalStdInrIndex d N m) := by
  simpa using
    (canonicalRoughFieldFunctionOfSnd_eq_sum_gamma
      (d := d) (N := N) (a := a) (mass := mass) T
      (((canonicalJointStdGaussianMeasurableEquiv d N).symm ξ).2) x)

private theorem canonicalSiteCrossStd_mem_wienerChaosLE
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (x : FinLatticeSites d N) (k j : ℕ) (hjk : j ≤ k) :
    ∃ hf : MeasureTheory.MemLp
        (canonicalSiteCrossStd d N a mass T x k j) 2
        (GaussianHilbert.stdGaussianFin
          (Fintype.card (CanonicalJointSumIndex d N))),
      (hf.toLp (canonicalSiteCrossStd d N a mass T x k j)) ∈
        GaussianHilbert.wienerChaosLE
          (Fintype.card (CanonicalJointSumIndex d N)) k := by
  classical
  let γS : (Fin d → Fin N) → ℝ := canonicalSmoothGamma d N a mass T x
  let γR : (Fin d → Fin N) → ℝ := canonicalRoughGamma d N a mass T x
  let sS := multiIndicesOfTotalDegree (Fin d → Fin N) j
  let sR := multiIndicesOfTotalDegree (Fin d → Fin N) (k - j)
  let β : ((Fin d → Fin N) → ℕ) × ((Fin d → Fin N) → ℕ) →
      canonicalStdIndex d N → ℕ :=
    fun p => canonicalJointMultiIndexOfPair d N p.1 p.2
  let c : ((Fin d → Fin N) → ℕ) × ((Fin d → Fin N) → ℕ) → ℝ :=
    fun p =>
      wickExpansionCoeff j γS p.1 *
        wickExpansionCoeff (k - j) γR p.2
  let f : (canonicalStdIndex d N → ℝ) → ℝ :=
    canonicalSiteCrossStd d N a mass T x k j
  let g : (canonicalStdIndex d N → ℝ) → ℝ :=
    fun ξ => ∑ p ∈ sS.product sR, c p * ∏ i, wickMonomial (β p i) 1 (ξ i)
  have hf_def : f = g := by
    funext ξ
    unfold f g canonicalSiteCrossStd c β wickExpansionCoeff
    rw [show smoothWickConstant d N a mass T = ∑ m : Fin d → Fin N, (γS m) ^ 2 from by
      simpa [γS] using
        (canonicalSmoothGamma_sq_sum_eq_wickConstant
          (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x).symm]
    rw [show roughWickConstant d N a mass T = ∑ m : Fin d → Fin N, (γR m) ^ 2 from by
      simpa [γR] using
        (canonicalRoughGamma_sq_sum_eq_wickConstant
          (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x).symm]
    rw [canonicalSmoothFieldFunction_std_eq_sum_gamma
      (d := d) (N := N) (a := a) (mass := mass) T x ξ]
    rw [canonicalRoughFieldFunction_std_eq_sum_gamma
      (d := d) (N := N) (a := a) (mass := mass) T x ξ]
    rw [show
      wickMonomial j (∑ m : Fin d → Fin N, (γS m) ^ 2)
          (∑ m : Fin d → Fin N, canonicalSmoothGamma d N a mass T x m *
            ξ (canonicalStdInlIndex d N m)) =
        ∑ α ∈ sS,
          wickExpansionCoeff j γS α *
            ∏ m : Fin d → Fin N, wickMonomial (α m) 1 (ξ (canonicalStdInlIndex d N m)) from by
              simpa [γS, wickMonomial_eq_root_local] using
                (wickMonomial_pow_sum_expansion_of_totalDegree
                  (γ := γS) (ξ := fun m => ξ (canonicalStdInlIndex d N m)) (k := j))]
    rw [show
      wickMonomial (k - j) (∑ m : Fin d → Fin N, (γR m) ^ 2)
          (∑ m : Fin d → Fin N, canonicalRoughGamma d N a mass T x m *
            ξ (canonicalStdInrIndex d N m)) =
        ∑ α ∈ sR,
          wickExpansionCoeff (k - j) γR α *
            ∏ m : Fin d → Fin N, wickMonomial (α m) 1 (ξ (canonicalStdInrIndex d N m)) from by
              simpa [γR, wickMonomial_eq_root_local] using
                (wickMonomial_pow_sum_expansion_of_totalDegree
                  (γ := γR) (ξ := fun m => ξ (canonicalStdInrIndex d N m)) (k := k - j))]
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr rfl ?_
    intro p hp
    rcases p with ⟨αS, αR⟩
    calc
      (wickExpansionCoeff j γS αS * ∏ m, wickMonomial (αS m) 1 (ξ (canonicalStdInlIndex d N m))) *
          (wickExpansionCoeff (k - j) γR αR *
            ∏ m, wickMonomial (αR m) 1 (ξ (canonicalStdInrIndex d N m)))
        =
          (wickExpansionCoeff j γS αS * wickExpansionCoeff (k - j) γR αR) *
            ((∏ m, wickMonomial (αS m) 1 (ξ (canonicalStdInlIndex d N m))) *
              ∏ m, wickMonomial (αR m) 1 (ξ (canonicalStdInrIndex d N m))) := by
                ring
      _ =
          (wickExpansionCoeff j γS αS * wickExpansionCoeff (k - j) γR αR) *
            ∏ i, wickMonomial (canonicalJointMultiIndexOfPair d N αS αR i) 1 (ξ i) := by
              simpa [canonicalJointMultiIndexOfPair] using
                (congrArg
                  (fun z =>
                    (wickExpansionCoeff j γS αS * wickExpansionCoeff (k - j) γR αR) * z)
                  (canonicalJointMultiIndexOfPair_wick_prod
                    (d := d) (N := N) αS αR ξ).symm)
      _ = ((↑j.factorial / ∏ j, ↑(αS j).factorial) * ∏ j, γS j ^ αS j) *
            ((↑(k - j).factorial / ∏ j, ↑(αR j).factorial) * ∏ j, γR j ^ αR j) *
              ∏ i, wickMonomial (canonicalJointMultiIndexOfPair d N αS αR i) 1 (ξ i) := by
                unfold wickExpansionCoeff
                ring
  have hg_memLp : MeasureTheory.MemLp g 2
      (GaussianHilbert.stdGaussianFin
        (Fintype.card (CanonicalJointSumIndex d N))) := by
    refine memLp_finset_sum (sS.product sR) ?_
    intro p hp
    have h_term :
        MeasureTheory.MemLp
          (fun ξ : canonicalStdIndex d N → ℝ =>
            c p * ∏ i, wickMonomial (β p i) 1 (ξ i))
          2
          (GaussianHilbert.stdGaussianFin
            (Fintype.card (CanonicalJointSumIndex d N))) := by
      have h_eq :
          (fun ξ : canonicalStdIndex d N → ℝ =>
            c p * ∏ i, wickMonomial (β p i) 1 (ξ i)) =
          fun ξ => c p * GaussianHilbert.hermiteMultiEval (β p) ξ := by
        funext ξ
        rw [multiWickMonomial_eq_hermiteMultiEval (β p) ξ]
      rw [h_eq]
      exact (GaussianHilbert.hermiteMultiEval_memLp (β p)).const_mul (c p)
    exact h_term
  let hf : MeasureTheory.MemLp
      (canonicalSiteCrossStd d N a mass T x k j) 2
      (GaussianHilbert.stdGaussianFin
        (Fintype.card (CanonicalJointSumIndex d N))) := by
          simpa [f, g, hf_def] using hg_memLp
  refine ⟨hf, ?_⟩
  refine finite_indexed_wick_sum_mem_wienerChaosLE
    (s := sS.product sR) β c ?_
    (canonicalSiteCrossStd d N a mass T x k j)
    (by simpa [f, g] using hf_def)
    hf
  intro p hp
  rcases Finset.mem_product.mp hp with ⟨hpS, hpR⟩
  have hpSdeg : ∑ m : Fin d → Fin N, p.1 m = j := by
    have hpS' : (∀ a : Fin d → Fin N, p.1 a ≤ j) ∧ ∑ a : Fin d → Fin N, p.1 a = j := by
      simpa [sS, multiIndicesOfTotalDegree] using hpS
    exact hpS'.2
  have hpRdeg : ∑ m : Fin d → Fin N, p.2 m = k - j := by
    have hpR' : (∀ a : Fin d → Fin N, p.2 a ≤ k - j) ∧
        ∑ a : Fin d → Fin N, p.2 a = k - j := by
      simpa [sR, multiIndicesOfTotalDegree] using hpR
    exact hpR'.2
  calc
    GaussianHilbert.MultiIndex.totalDegree (β p)
        = (∑ m : Fin d → Fin N, p.1 m) +
            ∑ m : Fin d → Fin N, p.2 m := by
              simpa [GaussianHilbert.MultiIndex.totalDegree] using
                canonicalJointMultiIndexOfPair_totalDegree
                  (d := d) (N := N) p.1 p.2
    _ = j + (k - j) := by rw [hpSdeg, hpRdeg]
    _ ≤ k := by
          exact le_of_eq (Nat.add_sub_of_le hjk)

/-! ## S1: pointwise binomial decomposition

Expand each per-site difference of Wick polynomials via the binomial
identity `wickPolynomial_add_sub_self` (which itself comes from
`wickMonomial_add_binomial` plus cancellation of the all-smooth term).
After substituting the covariance split `c = c_S + c_R` (via
`wickConstant_split`) and the field split `φ = φ_S + φ_R` (via
`canonicalSumFieldFunction_eq_smooth_plus_rough`), the rough error
becomes a finite sum of cross-terms each containing at least one
factor `:φ_R^{k - j}:_{c_R}` with `k - j ≥ 1`.

S2 (reindexing the (k, j) sum by (j, m := k − j) with `m ≥ 1`) is
done in subsequent lemmas as needed for S3/S4. -/

/-- The rough error equals the per-site difference of full minus smooth
Wick polynomials. Trivial unfolding; useful as the starting point for
the binomial decomposition (S1). -/
lemma canonicalRoughError_eq_sum_diff (T : ℝ) (P : InteractionPolynomial)
    (η : CanonicalJoint d N) :
    canonicalRoughError d N a mass T P η =
      a ^ d * ∑ x : FinLatticeSites d N,
        (wickPolynomial P (wickConstant d N a mass)
            (canonicalSumFieldFunction d N a mass T η x) -
          wickPolynomial P (smoothWickConstant d N a mass T)
            (canonicalSmoothFieldFunction d N a mass T η x)) := by
  unfold canonicalRoughError canonicalFullInteractionJoint canonicalSmoothInteraction
  rw [← mul_sub, ← Finset.sum_sub_distrib]

/-- **S1: pointwise binomial decomposition.** The rough error expands
into cross-terms `:φ_S^k:_{c_S} · :φ_R^{n − k}:_{c_R}` (one per leading
binomial index `k < P.n`) plus per-coefficient cross-terms
`:φ_S^k:_{c_S} · :φ_R^{m − k}:_{c_R}` (one per `(m, k)` with `m < P.n`,
`k < m`), each weighted by `a^d` and summed over sites. The constraint
`k < · ` (strict) comes from cancellation of the all-smooth `k = ·` term
against `canonicalSmoothInteraction`.

This is the algebraic content of S1 in
`docs/rough-error-variance-plan.md`. The proof uses
`wickPolynomial_add_sub_self` after substituting the covariance and
field splits. -/
lemma canonicalRoughError_pointwise_decomposition
    (T : ℝ) (P : InteractionPolynomial) (η : CanonicalJoint d N) :
    canonicalRoughError d N a mass T P η =
    a ^ d * ∑ x : FinLatticeSites d N,
      ((1 / P.n : ℝ) * ∑ k ∈ Finset.range P.n,
          (P.n.choose k : ℝ) *
            wickMonomial k (smoothWickConstant d N a mass T)
              (canonicalSmoothFieldFunction d N a mass T η x) *
            wickMonomial (P.n - k) (roughWickConstant d N a mass T)
              (canonicalRoughFieldFunction d N a mass T η x)
      + ∑ m : Fin P.n, P.coeff m * ∑ k ∈ Finset.range (m : ℕ),
          ((m : ℕ).choose k : ℝ) *
            wickMonomial k (smoothWickConstant d N a mass T)
              (canonicalSmoothFieldFunction d N a mass T η x) *
            wickMonomial ((m : ℕ) - k) (roughWickConstant d N a mass T)
              (canonicalRoughFieldFunction d N a mass T η x)) := by
  rw [canonicalRoughError_eq_sum_diff]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [wickConstant_split d N a mass T,
      canonicalSumFieldFunction_eq_smooth_plus_rough d N a mass T η x]
  exact wickPolynomial_add_sub_self P
    (smoothWickConstant d N a mass T)
    (roughWickConstant d N a mass T)
    (canonicalSmoothFieldFunction d N a mass T η x)
    (canonicalRoughFieldFunction d N a mass T η x)

/-! ## S2: reindex by (smooth-degree, rough-degree)

Define the per-(k, j) cross-term `M_{k,j}(η) = a^d · Σ_x :φ_S^j(x):_{c_S}
· :φ_R^{k-j}(x):_{c_R}`. The rough error is then a finite sum
`Σ_{(k, j)} A(k, j) · M_{k, j}(η)` where `A(k, j) = (Polynomial coeff at
degree k) · C(k, j)`. The constraint `j < k` (so `k - j ≥ 1`, at least
one rough factor) is inherited from S1.

This is the form S3 (Wick cross-term orthogonality) and S4 (per-term L²
bound) consume directly. -/

/-- Per-`(k, j)` cross-term of the rough error: `a^d` times the
position-sum of `:φ_S^j(x):_{c_S} · :φ_R^{k-j}(x):_{c_R}`. The L² norm
of the rough error decomposes (via Wick orthogonality) as a sum of L²
norms of these cross-terms. -/
def canonicalCrossTerm (T : ℝ) (η : CanonicalJoint d N) (k j : ℕ) : ℝ :=
  a ^ d * ∑ x : FinLatticeSites d N,
    wickMonomial j (smoothWickConstant d N a mass T)
      (canonicalSmoothFieldFunction d N a mass T η x) *
    wickMonomial (k - j) (roughWickConstant d N a mass T)
      (canonicalRoughFieldFunction d N a mass T η x)

/-- **S2: reindex pointwise decomposition into a sum of named cross-terms.**
The rough error equals a `(P.coeff)`-weighted sum of `canonicalCrossTerm`
values, with the leading `(1 / P.n)` term handled separately. The sum
range `j ∈ Finset.range k` ensures `k - j ≥ 1` (at least one rough
factor per term). -/
lemma canonicalRoughError_eq_sum_over_cross_terms
    (T : ℝ) (P : InteractionPolynomial) (η : CanonicalJoint d N) :
    canonicalRoughError d N a mass T P η =
    (1 / P.n : ℝ) * ∑ j ∈ Finset.range P.n,
        (P.n.choose j : ℝ) * canonicalCrossTerm d N a mass T η P.n j
    + ∑ m : Fin P.n, P.coeff m *
        ∑ j ∈ Finset.range (m : ℕ),
          ((m : ℕ).choose j : ℝ) *
            canonicalCrossTerm d N a mass T η (m : ℕ) j := by
  rw [canonicalRoughError_pointwise_decomposition]
  -- Strategy:
  -- (1) split the per-x sum over the (lead + terms) structure;
  -- (2) for each piece, push a^d and outer scalars inside the sum,
  --     swap Σ_x with the binomial-index Σ_j (or Σ_m, Σ_j), then pull
  --     coefficients back out and recognise canonicalCrossTerm.
  rw [Finset.sum_add_distrib, mul_add]
  unfold canonicalCrossTerm
  refine congr_arg₂ (· + ·) ?_ ?_
  · -- Leading (1/n) term:
    -- a^d * Σ_x (1/n * Σ_j C(n,j) * sm_j * ru_{n-j})
    --   = (1/n) * Σ_j C(n,j) * (a^d * Σ_x sm_j * ru_{n-j})
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [mul_assoc, ← Finset.mul_sum]
    ring
  · -- Per-coefficient terms:
    -- a^d * Σ_x Σ_m c_m * Σ_j C(m,j) * sm_j * ru_{m-j}
    --   = Σ_m c_m * Σ_j C(m,j) * (a^d * Σ_x sm_j * ru_{m-j})
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [mul_assoc, ← Finset.mul_sum]
    ring

/-- Exported for the asym chaos-membership port: Wiener chaos filtrations are monotone. -/
lemma wienerChaosLE_mono
    {n k l : ℕ} (hkl : k ≤ l) :
    GaussianHilbert.wienerChaosLE n k ≤
      GaussianHilbert.wienerChaosLE n l := by
  rw [GaussianHilbert.wienerChaosLE, GaussianHilbert.wienerChaosLE]
  refine iSup₂_le fun i hi => ?_
  refine le_iSup_of_le i ?_
  refine le_iSup_of_le ?_ le_rfl
  exact Finset.mem_range.mpr <|
    lt_of_lt_of_le (Finset.mem_range.mp hi) (Nat.succ_le_succ hkl)

/-- Standard-Gaussian representative of a single rough cross-term. -/
private def canonicalCrossTermStd
    (T : ℝ) (k j : ℕ) (ξ : canonicalStdIndex d N → ℝ) : ℝ :=
  a ^ d * ∑ x : FinLatticeSites d N, canonicalSiteCrossStd d N a mass T x k j ξ

@[simp] private lemma canonicalCrossTermStd_eq
    (T : ℝ) (η : CanonicalJoint d N) (k j : ℕ) :
    canonicalCrossTermStd d N a mass T k j
        (canonicalJointStdGaussianMeasurableEquiv d N η) =
      canonicalCrossTerm d N a mass T η k j := by
  unfold canonicalCrossTermStd canonicalCrossTerm canonicalSiteCrossStd
  simp

private theorem canonicalCrossTermStd_mem_wienerChaosLE
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (k j : ℕ) (hjk : j ≤ k) :
    ∃ hf : MeasureTheory.MemLp
        (canonicalCrossTermStd d N a mass T k j) 2
        (GaussianHilbert.stdGaussianFin
          (Fintype.card (CanonicalJointSumIndex d N))),
      (hf.toLp (canonicalCrossTermStd d N a mass T k j)) ∈
        GaussianHilbert.wienerChaosLE
          (Fintype.card (CanonicalJointSumIndex d N)) k := by
  classical
  let μ := GaussianHilbert.stdGaussianFin
    (Fintype.card (CanonicalJointSumIndex d N))
  let hfSite :
      ∀ x : FinLatticeSites d N,
        MeasureTheory.MemLp
          (fun ξ : canonicalStdIndex d N → ℝ =>
            canonicalSiteCrossStd d N a mass T x k j ξ) 2 μ :=
    fun x =>
      Classical.choose <|
        canonicalSiteCrossStd_mem_wienerChaosLE
          (d := d) (N := N) (a := a) (mass := mass)
          ha hmass T hT x k j hjk
  have hfSite_spec :
      ∀ x : FinLatticeSites d N,
        ((hfSite x).toLp
          (fun ξ : canonicalStdIndex d N → ℝ =>
            canonicalSiteCrossStd d N a mass T x k j ξ)) ∈
          GaussianHilbert.wienerChaosLE
            (Fintype.card (CanonicalJointSumIndex d N)) k := by
    intro x
    exact
      Classical.choose_spec <|
        canonicalSiteCrossStd_mem_wienerChaosLE
          (d := d) (N := N) (a := a) (mass := mass)
          ha hmass T hT x k j hjk
  have hsum_memLp :
      MeasureTheory.MemLp
        (fun ξ : canonicalStdIndex d N → ℝ =>
          ∑ x : FinLatticeSites d N, canonicalSiteCrossStd d N a mass T x k j ξ)
        2 μ := by
    refine memLp_finset_sum Finset.univ ?_
    intro x hx
    simpa using hfSite x
  let hf : MeasureTheory.MemLp
      (canonicalCrossTermStd d N a mass T k j) 2 μ := by
        simpa [canonicalCrossTermStd] using hsum_memLp.const_mul (a ^ d)
  refine ⟨hf, ?_⟩
  have h_toLp :
      hf.toLp (canonicalCrossTermStd d N a mass T k j) =
        (a ^ d) • ∑ x : FinLatticeSites d N,
          (hfSite x).toLp
            (fun ξ : canonicalStdIndex d N → ℝ =>
              canonicalSiteCrossStd d N a mass T x k j ξ) := by
    apply MeasureTheory.Lp.ext
    refine (MemLp.coeFn_toLp hf).trans ?_
    symm
    refine (MeasureTheory.Lp.coeFn_smul (a ^ d)
      (∑ x : FinLatticeSites d N,
        (hfSite x).toLp
          (fun ξ : canonicalStdIndex d N → ℝ =>
            canonicalSiteCrossStd d N a mass T x k j ξ))).trans ?_
    have hsum_coe :
        (((∑ x : FinLatticeSites d N,
            (hfSite x).toLp
              (fun ξ : canonicalStdIndex d N → ℝ =>
                canonicalSiteCrossStd d N a mass T x k j ξ) :
              MeasureTheory.Lp ℝ 2 μ) :
          (canonicalStdIndex d N → ℝ) → ℝ)) =ᵐ[μ]
            ∑ x : FinLatticeSites d N,
              (((hfSite x).toLp
                (fun ξ : canonicalStdIndex d N → ℝ =>
                  canonicalSiteCrossStd d N a mass T x k j ξ) :
                  MeasureTheory.Lp ℝ 2 μ) :
                (canonicalStdIndex d N → ℝ) → ℝ) :=
      MeasureTheory.Lp.coeFn_finset_sum Finset.univ
        (fun x =>
          (hfSite x).toLp
            (fun ξ : canonicalStdIndex d N → ℝ =>
              canonicalSiteCrossStd d N a mass T x k j ξ))
    have h_each :
        ∀ x ∈ ((Finset.univ : Finset (FinLatticeSites d N)) : Set (FinLatticeSites d N)),
          ∀ᵐ ξ ∂μ,
            (((hfSite x).toLp
              (fun ξ : canonicalStdIndex d N → ℝ =>
                canonicalSiteCrossStd d N a mass T x k j ξ) :
                MeasureTheory.Lp ℝ 2 μ) :
              (canonicalStdIndex d N → ℝ) → ℝ) ξ =
              canonicalSiteCrossStd d N a mass T x k j ξ := by
      intro x _
      exact MemLp.coeFn_toLp (hfSite x)
    have h_ae_all :
        ∀ᵐ ξ ∂μ,
          ∀ x ∈ ((Finset.univ : Finset (FinLatticeSites d N)) : Set (FinLatticeSites d N)),
            (((hfSite x).toLp
              (fun ξ : canonicalStdIndex d N → ℝ =>
                canonicalSiteCrossStd d N a mass T x k j ξ) :
                MeasureTheory.Lp ℝ 2 μ) :
              (canonicalStdIndex d N → ℝ) → ℝ) ξ =
              canonicalSiteCrossStd d N a mass T x k j ξ :=
      (ae_ball_iff (Finset.univ : Finset (FinLatticeSites d N)).countable_toSet).mpr h_each
    filter_upwards [hsum_coe, h_ae_all] with ξ hsumξ hξ
    rw [Pi.smul_apply, hsumξ, Finset.sum_apply, canonicalCrossTermStd]
    congr 1
    exact Finset.sum_congr rfl fun x hx =>
      hξ x (Finset.mem_coe.mpr hx)
  rw [h_toLp]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro x hx
  exact hfSite_spec x

private theorem canonicalCrossTermLinearCombo_mem_wienerChaosLE
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (k l : ℕ) (hkl : k ≤ l) (c : ℕ → ℝ) :
    ∃ hf : MeasureTheory.MemLp
        (fun ξ : canonicalStdIndex d N → ℝ =>
          ∑ j ∈ Finset.range k, c j * canonicalCrossTermStd d N a mass T k j ξ)
        2
        (GaussianHilbert.stdGaussianFin
          (Fintype.card (CanonicalJointSumIndex d N))),
      (hf.toLp
        (fun ξ : canonicalStdIndex d N → ℝ =>
          ∑ j ∈ Finset.range k, c j * canonicalCrossTermStd d N a mass T k j ξ)) ∈
        GaussianHilbert.wienerChaosLE
          (Fintype.card (CanonicalJointSumIndex d N)) l := by
  classical
  let μ := GaussianHilbert.stdGaussianFin
    (Fintype.card (CanonicalJointSumIndex d N))
  let F : ℕ → MeasureTheory.Lp ℝ 2 μ := fun j =>
    if hj : j ∈ Finset.range k then
      let hfj :=
        Classical.choose <|
          canonicalCrossTermStd_mem_wienerChaosLE
            (d := d) (N := N) (a := a) (mass := mass)
            ha hmass T hT k j (Nat.le_of_lt (Finset.mem_range.mp hj))
      hfj.toLp (canonicalCrossTermStd d N a mass T k j)
    else 0
  have hmemLp :
      MeasureTheory.MemLp
        (fun ξ : canonicalStdIndex d N → ℝ =>
          ∑ j ∈ Finset.range k, c j * canonicalCrossTermStd d N a mass T k j ξ)
        2 μ := by
    refine memLp_finset_sum (Finset.range k) ?_
    intro j hj
    let hfj :=
      Classical.choose <|
        canonicalCrossTermStd_mem_wienerChaosLE
          (d := d) (N := N) (a := a) (mass := mass)
          ha hmass T hT k j (Nat.le_of_lt (Finset.mem_range.mp hj))
    simpa using (hfj.const_mul (c j))
  refine ⟨hmemLp, ?_⟩
  have h_toLp :
      hmemLp.toLp
        (fun ξ : canonicalStdIndex d N → ℝ =>
          ∑ j ∈ Finset.range k, c j * canonicalCrossTermStd d N a mass T k j ξ) =
        ∑ j ∈ Finset.range k, c j • F j := by
    apply MeasureTheory.Lp.ext
    refine (MemLp.coeFn_toLp hmemLp).trans ?_
    symm
    have hsum_coe :
        (((∑ j ∈ Finset.range k, c j • F j : MeasureTheory.Lp ℝ 2 μ) :
          (canonicalStdIndex d N → ℝ) → ℝ)) =ᵐ[μ]
            ∑ j ∈ Finset.range k,
              (((c j • F j : MeasureTheory.Lp ℝ 2 μ) :
                (canonicalStdIndex d N → ℝ) → ℝ)) :=
      MeasureTheory.Lp.coeFn_finset_sum (Finset.range k) (fun j => c j • F j)
    have h_each :
        ∀ j ∈ ((Finset.range k : Finset ℕ) : Set ℕ),
          ∀ᵐ ξ ∂μ,
            (((c j • F j : MeasureTheory.Lp ℝ 2 μ) :
              (canonicalStdIndex d N → ℝ) → ℝ) ξ) =
              c j * canonicalCrossTermStd d N a mass T k j ξ := by
      intro j hjset
      have hj : j ∈ Finset.range k := Finset.mem_coe.mp hjset
      dsimp [F]
      simp only [hj, ↓reduceDIte]
      let hfj :=
        Classical.choose <|
          canonicalCrossTermStd_mem_wienerChaosLE
            (d := d) (N := N) (a := a) (mass := mass)
            ha hmass T hT k j (Nat.le_of_lt (Finset.mem_range.mp hj))
      refine (MeasureTheory.Lp.coeFn_smul (c j)
        (hfj.toLp (canonicalCrossTermStd d N a mass T k j))).trans ?_
      filter_upwards [MemLp.coeFn_toLp hfj] with ξ hξ
      simp [hξ, smul_eq_mul]
    have h_ae_all :
        ∀ᵐ ξ ∂μ,
          ∀ j ∈ ((Finset.range k : Finset ℕ) : Set ℕ),
            (((c j • F j : MeasureTheory.Lp ℝ 2 μ) :
              (canonicalStdIndex d N → ℝ) → ℝ) ξ) =
              c j * canonicalCrossTermStd d N a mass T k j ξ :=
      (ae_ball_iff (Finset.range k).countable_toSet).mpr h_each
    refine hsum_coe.trans ?_
    filter_upwards [h_ae_all] with ξ hξ
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun j hj =>
      hξ j (Finset.mem_coe.mpr hj)
  rw [h_toLp]
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  have hmemk :
      F j ∈ GaussianHilbert.wienerChaosLE
        (Fintype.card (CanonicalJointSumIndex d N)) k := by
    dsimp [F]
    simp only [hj, ↓reduceDIte]
    exact Classical.choose_spec <|
      canonicalCrossTermStd_mem_wienerChaosLE
        (d := d) (N := N) (a := a) (mass := mass)
        ha hmass T hT k j (Nat.le_of_lt (Finset.mem_range.mp hj))
  exact wienerChaosLE_mono (n := Fintype.card (CanonicalJointSumIndex d N)) hkl hmemk

/-- Standard-Gaussian representative of the full canonical rough error. -/
private def canonicalRoughErrorStd
    (T : ℝ) (P : InteractionPolynomial) (ξ : canonicalStdIndex d N → ℝ) : ℝ :=
  (1 / P.n : ℝ) * ∑ j ∈ Finset.range P.n,
      (P.n.choose j : ℝ) * canonicalCrossTermStd d N a mass T P.n j ξ
  + ∑ m : Fin P.n, P.coeff m *
      ∑ j ∈ Finset.range (m : ℕ),
        ((m : ℕ).choose j : ℝ) *
          canonicalCrossTermStd d N a mass T (m : ℕ) j ξ

@[simp] private lemma canonicalRoughErrorStd_eq
    (T : ℝ) (P : InteractionPolynomial) (η : CanonicalJoint d N) :
    canonicalRoughErrorStd d N a mass T P
        (canonicalJointStdGaussianMeasurableEquiv d N η) =
      canonicalRoughError d N a mass T P η := by
  rw [canonicalRoughError_eq_sum_over_cross_terms]
  unfold canonicalRoughErrorStd
  refine congr_arg₂ (· + ·) ?_ ?_
  · simp only [canonicalCrossTermStd_eq]
  · refine Finset.sum_congr rfl ?_
    intro m hm
    simp only [canonicalCrossTermStd_eq]

private theorem canonicalRoughErrorStd_mem_wienerChaosLE
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (P : InteractionPolynomial) :
    ∃ hf : MeasureTheory.MemLp
        (canonicalRoughErrorStd d N a mass T P) 2
        (GaussianHilbert.stdGaussianFin
          (Fintype.card (CanonicalJointSumIndex d N))),
      (hf.toLp (canonicalRoughErrorStd d N a mass T P)) ∈
        GaussianHilbert.wienerChaosLE
          (Fintype.card (CanonicalJointSumIndex d N)) P.n := by
  classical
  let μ := GaussianHilbert.stdGaussianFin
    (Fintype.card (CanonicalJointSumIndex d N))
  let leadSum : (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ := fun ξ =>
    ∑ j ∈ Finset.range P.n,
      (P.n.choose j : ℝ) * canonicalCrossTermStd d N a mass T P.n j ξ
  let lead : (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ := fun ξ =>
    (1 / P.n : ℝ) • leadSum ξ
  obtain ⟨hfLeadSum, hLeadSumChaos⟩ :=
    canonicalCrossTermLinearCombo_mem_wienerChaosLE
      (d := d) (N := N) (a := a) (mass := mass)
      ha hmass T hT P.n P.n le_rfl (fun j => (P.n.choose j : ℝ))
  let hfLead : MeasureTheory.MemLp lead 2 μ := hfLeadSum.const_smul (1 / P.n : ℝ)
  have hLeadChaos :
      (hfLead.toLp lead) ∈
        GaussianHilbert.wienerChaosLE
          (Fintype.card (CanonicalJointSumIndex d N)) P.n := by
    have hLead_toLp :
        hfLead.toLp lead =
          (1 / P.n : ℝ) • hfLeadSum.toLp leadSum := by
      simpa [lead, leadSum] using
        (MeasureTheory.MemLp.toLp_const_smul (1 / P.n : ℝ) hfLeadSum)
    rw [hLead_toLp]
    exact Submodule.smul_mem _ _ hLeadSumChaos
  let perInner : Fin P.n →
      ((Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ) := fun m ξ =>
    ∑ j ∈ Finset.range (m : ℕ),
      ((m : ℕ).choose j : ℝ) *
        canonicalCrossTermStd d N a mass T (m : ℕ) j ξ
  let per : (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ := fun ξ =>
    ∑ m : Fin P.n, P.coeff m * perInner m ξ
  have hPerInner :
      ∀ m : Fin P.n,
        ∃ hf : MeasureTheory.MemLp (perInner m) 2 μ,
          (hf.toLp (perInner m)) ∈
            GaussianHilbert.wienerChaosLE
              (Fintype.card (CanonicalJointSumIndex d N)) P.n := by
    intro m
    exact canonicalCrossTermLinearCombo_mem_wienerChaosLE
      (d := d) (N := N) (a := a) (mass := mass)
      ha hmass T hT (m : ℕ) P.n (Nat.le_of_lt m.2)
      (fun j => ((m : ℕ).choose j : ℝ))
  let hfPerInner : ∀ m : Fin P.n, MeasureTheory.MemLp (perInner m) 2 μ :=
    fun m => (hPerInner m).choose
  have hPerInnerChaos :
      ∀ m : Fin P.n,
        ((hfPerInner m).toLp (perInner m)) ∈
          GaussianHilbert.wienerChaosLE
            (Fintype.card (CanonicalJointSumIndex d N)) P.n := by
    intro m
    exact (hPerInner m).choose_spec
  have hfPer : MeasureTheory.MemLp per 2 μ := by
    refine memLp_finset_sum Finset.univ ?_
    intro m hm
    simpa [perInner] using (hfPerInner m).const_mul (P.coeff m)
  have hPerChaos :
      (hfPer.toLp per) ∈
        GaussianHilbert.wienerChaosLE
          (Fintype.card (CanonicalJointSumIndex d N)) P.n := by
    have hPer_toLp :
        hfPer.toLp per =
          ∑ m : Fin P.n, P.coeff m • (hfPerInner m).toLp (perInner m) := by
      apply MeasureTheory.Lp.ext
      refine (MemLp.coeFn_toLp hfPer).trans ?_
      symm
      have hsum_coe :
          (((∑ m : Fin P.n, P.coeff m • (hfPerInner m).toLp (perInner m) :
              MeasureTheory.Lp ℝ 2 μ) :
            (canonicalStdIndex d N → ℝ) → ℝ)) =ᵐ[μ]
              ∑ m : Fin P.n,
                (((P.coeff m • (hfPerInner m).toLp (perInner m) :
                    MeasureTheory.Lp ℝ 2 μ) :
                  (canonicalStdIndex d N → ℝ) → ℝ)) :=
        MeasureTheory.Lp.coeFn_finset_sum Finset.univ
          (fun m => P.coeff m • (hfPerInner m).toLp (perInner m))
      have h_each :
          ∀ m ∈ ((Finset.univ : Finset (Fin P.n)) : Set (Fin P.n)),
            ∀ᵐ ξ ∂μ,
              (((P.coeff m • (hfPerInner m).toLp (perInner m) :
                  MeasureTheory.Lp ℝ 2 μ) :
                (canonicalStdIndex d N → ℝ) → ℝ) ξ) =
                P.coeff m * perInner m ξ := by
        intro m hm
        refine (MeasureTheory.Lp.coeFn_smul (P.coeff m)
          ((hfPerInner m).toLp (perInner m))).trans ?_
        filter_upwards [MemLp.coeFn_toLp (hfPerInner m)] with ξ hξ
        simp [hξ, smul_eq_mul]
      have h_ae_all :
          ∀ᵐ ξ ∂μ,
            ∀ m ∈ ((Finset.univ : Finset (Fin P.n)) : Set (Fin P.n)),
              (((P.coeff m • (hfPerInner m).toLp (perInner m) :
                  MeasureTheory.Lp ℝ 2 μ) :
                (canonicalStdIndex d N → ℝ) → ℝ) ξ) =
                P.coeff m * perInner m ξ :=
        (ae_ball_iff (Finset.univ : Finset (Fin P.n)).countable_toSet).mpr h_each
      refine hsum_coe.trans ?_
      filter_upwards [h_ae_all] with ξ hξ
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun m hm =>
        hξ m (Finset.mem_coe.mpr hm)
    rw [hPer_toLp]
    apply Submodule.sum_mem
    intro m hm
    exact Submodule.smul_mem _ _ (hPerInnerChaos m)
  have hf : MeasureTheory.MemLp (canonicalRoughErrorStd d N a mass T P) 2 μ := by
    change MeasureTheory.MemLp (fun ξ => lead ξ + per ξ) 2 μ
    simpa using hfLead.add hfPer
  refine ⟨hf, ?_⟩
  have h_toLp :
      hf.toLp (canonicalRoughErrorStd d N a mass T P) =
        hfLead.toLp lead + hfPer.toLp per := by
    calc
      hf.toLp (canonicalRoughErrorStd d N a mass T P)
          = MeasureTheory.MemLp.toLp (fun ξ => lead ξ + per ξ) (hfLead.add hfPer) := by
              apply MeasureTheory.MemLp.toLp_congr hf (hfLead.add hfPer)
              filter_upwards with ξ
              simp [canonicalRoughErrorStd, lead, leadSum, per, perInner, smul_eq_mul]
      _ = hfLead.toLp lead + hfPer.toLp per := by
            simpa using (MeasureTheory.MemLp.toLp_add hfLead hfPer)
  rw [h_toLp]
  exact Submodule.add_mem _ hLeadChaos hPerChaos

/-- Standard-Gaussian representative of the **smooth** interaction: the `j=k` (pure-smooth) diagonal
cross-terms. `canonicalSmoothInteractionStd (equiv η) = canonicalSmoothInteraction η`. -/
private def canonicalSmoothInteractionStd
    (T : ℝ) (P : InteractionPolynomial) (ξ : canonicalStdIndex d N → ℝ) : ℝ :=
  (1 / P.n : ℝ) * canonicalCrossTermStd d N a mass T P.n P.n ξ
  + ∑ m : Fin P.n, P.coeff m * canonicalCrossTermStd d N a mass T (m : ℕ) (m : ℕ) ξ

/-- The smooth-interaction std representative agrees with `canonicalSmoothInteraction` after the
std-Gaussian equivalence: the `j=k` diagonal cross-terms reassemble the smooth Wick polynomial
(the diagonal decomposition, proved inline). -/
@[simp] private lemma canonicalSmoothInteractionStd_eq
    (T : ℝ) (P : InteractionPolynomial) (η : CanonicalJoint d N) :
    canonicalSmoothInteractionStd d N a mass T P
        (canonicalJointStdGaussianMeasurableEquiv d N η) =
      canonicalSmoothInteraction d N a mass T P η := by
  unfold canonicalSmoothInteractionStd
  simp only [canonicalCrossTermStd_eq]
  refine Eq.symm ?_
  unfold canonicalSmoothInteraction canonicalCrossTerm
  simp only [Nat.sub_self, wickMonomial_zero, mul_one, wickPolynomial]
  rw [Finset.sum_add_distrib, mul_add]
  refine congr_arg₂ (· + ·) ?_ ?_
  · rw [← Finset.mul_sum]; ring
  · simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [mul_assoc, ← Finset.mul_sum]
    ring

/-- The smooth interaction's standard-Gaussian representative lies in the degree-≤`P.n` Wiener
chaos: each diagonal cross-term `crossTermStd(k,k)` is in `wienerChaosLE … k ⊆ wienerChaosLE … P.n`.
Mirrors `canonicalRoughErrorStd_mem_wienerChaosLE` with single diagonal terms. -/
private theorem canonicalSmoothInteractionStd_mem_wienerChaosLE
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T) (P : InteractionPolynomial) :
    ∃ hf : MeasureTheory.MemLp
        (canonicalSmoothInteractionStd d N a mass T P) 2
        (GaussianHilbert.stdGaussianFin (Fintype.card (CanonicalJointSumIndex d N))),
      (hf.toLp (canonicalSmoothInteractionStd d N a mass T P)) ∈
        GaussianHilbert.wienerChaosLE (Fintype.card (CanonicalJointSumIndex d N)) P.n := by
  classical
  let μ := GaussianHilbert.stdGaussianFin (Fintype.card (CanonicalJointSumIndex d N))
  obtain ⟨hfLeadT, hLeadTChaos⟩ :=
    canonicalCrossTermStd_mem_wienerChaosLE
      (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT P.n P.n le_rfl
  let lead : (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ := fun ξ =>
    (1 / P.n : ℝ) • canonicalCrossTermStd d N a mass T P.n P.n ξ
  let hfLead : MeasureTheory.MemLp lead 2 μ := hfLeadT.const_smul (1 / P.n : ℝ)
  have hLeadChaos :
      (hfLead.toLp lead) ∈
        GaussianHilbert.wienerChaosLE (Fintype.card (CanonicalJointSumIndex d N)) P.n := by
    have hLead_toLp :
        hfLead.toLp lead =
          (1 / P.n : ℝ) • hfLeadT.toLp (canonicalCrossTermStd d N a mass T P.n P.n) := by
      simpa [lead] using (MeasureTheory.MemLp.toLp_const_smul (1 / P.n : ℝ) hfLeadT)
    rw [hLead_toLp]
    exact Submodule.smul_mem _ _ hLeadTChaos
  let perTerm : Fin P.n → ((Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ) :=
    fun m ξ => canonicalCrossTermStd d N a mass T (m : ℕ) (m : ℕ) ξ
  let per : (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ := fun ξ =>
    ∑ m : Fin P.n, P.coeff m * perTerm m ξ
  have hPerTerm :
      ∀ m : Fin P.n,
        ∃ hf : MeasureTheory.MemLp (perTerm m) 2 μ,
          (hf.toLp (perTerm m)) ∈
            GaussianHilbert.wienerChaosLE (Fintype.card (CanonicalJointSumIndex d N)) P.n := by
    intro m
    obtain ⟨hfm, hfmChaos⟩ :=
      canonicalCrossTermStd_mem_wienerChaosLE
        (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT (m : ℕ) (m : ℕ) le_rfl
    exact ⟨hfm, wienerChaosLE_mono (Nat.le_of_lt m.2) hfmChaos⟩
  let hfPerTerm : ∀ m : Fin P.n, MeasureTheory.MemLp (perTerm m) 2 μ :=
    fun m => (hPerTerm m).choose
  have hPerTermChaos :
      ∀ m : Fin P.n,
        ((hfPerTerm m).toLp (perTerm m)) ∈
          GaussianHilbert.wienerChaosLE (Fintype.card (CanonicalJointSumIndex d N)) P.n :=
    fun m => (hPerTerm m).choose_spec
  have hfPer : MeasureTheory.MemLp per 2 μ := by
    refine memLp_finset_sum Finset.univ ?_
    intro m _
    simpa [perTerm] using (hfPerTerm m).const_mul (P.coeff m)
  have hPerChaos :
      (hfPer.toLp per) ∈
        GaussianHilbert.wienerChaosLE (Fintype.card (CanonicalJointSumIndex d N)) P.n := by
    have hPer_toLp :
        hfPer.toLp per =
          ∑ m : Fin P.n, P.coeff m • (hfPerTerm m).toLp (perTerm m) := by
      apply MeasureTheory.Lp.ext
      refine (MemLp.coeFn_toLp hfPer).trans ?_
      symm
      have hsum_coe :
          (((∑ m : Fin P.n, P.coeff m • (hfPerTerm m).toLp (perTerm m) :
              MeasureTheory.Lp ℝ 2 μ) : (canonicalStdIndex d N → ℝ) → ℝ)) =ᵐ[μ]
              ∑ m : Fin P.n,
                (((P.coeff m • (hfPerTerm m).toLp (perTerm m) :
                    MeasureTheory.Lp ℝ 2 μ) : (canonicalStdIndex d N → ℝ) → ℝ)) :=
        MeasureTheory.Lp.coeFn_finset_sum Finset.univ
          (fun m => P.coeff m • (hfPerTerm m).toLp (perTerm m))
      have h_each :
          ∀ m ∈ ((Finset.univ : Finset (Fin P.n)) : Set (Fin P.n)),
            ∀ᵐ ξ ∂μ,
              (((P.coeff m • (hfPerTerm m).toLp (perTerm m) :
                  MeasureTheory.Lp ℝ 2 μ) : (canonicalStdIndex d N → ℝ) → ℝ) ξ) =
                P.coeff m * perTerm m ξ := by
        intro m _
        refine (MeasureTheory.Lp.coeFn_smul (P.coeff m)
          ((hfPerTerm m).toLp (perTerm m))).trans ?_
        filter_upwards [MemLp.coeFn_toLp (hfPerTerm m)] with ξ hξ
        simp [hξ, smul_eq_mul]
      have h_ae_all :
          ∀ᵐ ξ ∂μ,
            ∀ m ∈ ((Finset.univ : Finset (Fin P.n)) : Set (Fin P.n)),
              (((P.coeff m • (hfPerTerm m).toLp (perTerm m) :
                  MeasureTheory.Lp ℝ 2 μ) : (canonicalStdIndex d N → ℝ) → ℝ) ξ) =
                P.coeff m * perTerm m ξ :=
        (ae_ball_iff (Finset.univ : Finset (Fin P.n)).countable_toSet).mpr h_each
      refine hsum_coe.trans ?_
      filter_upwards [h_ae_all] with ξ hξ
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun m hm => hξ m (Finset.mem_coe.mpr hm)
    rw [hPer_toLp]
    apply Submodule.sum_mem
    intro m _
    exact Submodule.smul_mem _ _ (hPerTermChaos m)
  have hf : MeasureTheory.MemLp (canonicalSmoothInteractionStd d N a mass T P) 2 μ := by
    change MeasureTheory.MemLp (fun ξ => lead ξ + per ξ) 2 μ
    simpa using hfLead.add hfPer
  refine ⟨hf, ?_⟩
  have h_toLp :
      hf.toLp (canonicalSmoothInteractionStd d N a mass T P) =
        hfLead.toLp lead + hfPer.toLp per := by
    calc
      hf.toLp (canonicalSmoothInteractionStd d N a mass T P)
          = MeasureTheory.MemLp.toLp (fun ξ => lead ξ + per ξ) (hfLead.add hfPer) := by
              apply MeasureTheory.MemLp.toLp_congr hf (hfLead.add hfPer)
              filter_upwards with ξ
              simp [canonicalSmoothInteractionStd, lead, per, perTerm, smul_eq_mul]
      _ = hfLead.toLp lead + hfPer.toLp per := by
            simpa using (MeasureTheory.MemLp.toLp_add hfLead hfPer)
  rw [h_toLp]
  exact Submodule.add_mem _ hLeadChaos hPerChaos

/-- **Smooth-interaction moment bound (Bonami–Nelson).** `∫ |V_smooth|^p ≤
((P.n+1)(p-1)^{P.n/2})^p · (∫ |V_smooth|²)^{p/2}` on the joint measure (`p ≥ 2`). Combines the
smooth chaos membership with `chaosLE_moment_le` (G1) and the measure-preserving std↔joint transfer. -/
theorem canonicalSmoothInteraction_moment_le
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T) (P : InteractionPolynomial)
    (p : ℝ) (hp : 2 ≤ p) :
    ∫ η, |canonicalSmoothInteraction d N a mass T P η| ^ p ∂(canonicalJointMeasure d N)
      ≤ (((P.n : ℝ) + 1) * (p - 1) ^ ((P.n : ℝ) / 2)) ^ p
        * (∫ η, |canonicalSmoothInteraction d N a mass T P η| ^ (2 : ℝ)
            ∂(canonicalJointMeasure d N)) ^ (p / 2) := by
  classical
  obtain ⟨hf, hchaos⟩ := canonicalSmoothInteractionStd_mem_wienerChaosLE
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT P
  have hG1 := chaosLE_moment_le
    (hf.toLp (canonicalSmoothInteractionStd d N a mass T P)) hchaos p hp
  have hcoe := MemLp.coeFn_toLp hf
  have hmp : MeasureTheory.MeasurePreserving (canonicalJointStdGaussianMeasurableEquiv d N)
      (canonicalJointMeasure d N)
      (GaussianHilbert.stdGaussianFin (Fintype.card (CanonicalJointSumIndex d N))) :=
    ⟨(canonicalJointStdGaussianMeasurableEquiv d N).measurable,
      canonicalJointMeasure_map_stdGaussian (d := d) (N := N)⟩
  have htransfer : ∀ q : ℝ,
      ∫ ξ, |canonicalSmoothInteractionStd d N a mass T P ξ| ^ q
          ∂(GaussianHilbert.stdGaussianFin (Fintype.card (CanonicalJointSumIndex d N)))
        = ∫ η, |canonicalSmoothInteraction d N a mass T P η| ^ q
            ∂(canonicalJointMeasure d N) := by
    intro q
    rw [← hmp.integral_comp (canonicalJointStdGaussianMeasurableEquiv d N).measurableEmbedding
      (fun ξ => |canonicalSmoothInteractionStd d N a mass T P ξ| ^ q)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    simp only [canonicalSmoothInteractionStd_eq]
  have hp_eq : ∫ ξ, |((hf.toLp (canonicalSmoothInteractionStd d N a mass T P) :
        MeasureTheory.Lp ℝ 2 (GaussianHilbert.stdGaussianFin
          (Fintype.card (CanonicalJointSumIndex d N)))) :
        (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ) ξ| ^ p
      ∂(GaussianHilbert.stdGaussianFin (Fintype.card (CanonicalJointSumIndex d N)))
      = ∫ ξ, |canonicalSmoothInteractionStd d N a mass T P ξ| ^ p
          ∂(GaussianHilbert.stdGaussianFin (Fintype.card (CanonicalJointSumIndex d N))) :=
    integral_congr_ae (hcoe.mono fun ξ h => by simp only [h])
  have h2_eq : ∫ ξ, |((hf.toLp (canonicalSmoothInteractionStd d N a mass T P) :
        MeasureTheory.Lp ℝ 2 (GaussianHilbert.stdGaussianFin
          (Fintype.card (CanonicalJointSumIndex d N)))) :
        (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ) ξ| ^ (2 : ℝ)
      ∂(GaussianHilbert.stdGaussianFin (Fintype.card (CanonicalJointSumIndex d N)))
      = ∫ ξ, |canonicalSmoothInteractionStd d N a mass T P ξ| ^ (2 : ℝ)
          ∂(GaussianHilbert.stdGaussianFin (Fintype.card (CanonicalJointSumIndex d N))) :=
    integral_congr_ae (hcoe.mono fun ξ h => by simp only [h])
  rw [hp_eq, h2_eq, htransfer p, htransfer (2 : ℝ)] at hG1
  exact hG1

/-- **Rough-error moment bound (Bonami–Nelson).** `∫ |V_rough|^p ≤
((P.n+1)(p-1)^{P.n/2})^p · (∫ |V_rough|²)^{p/2}` on the joint measure (`p ≥ 2`). Same as the smooth
bound, using the rough chaos membership `canonicalRoughErrorStd_mem_wienerChaosLE`. -/
theorem canonicalRoughError_moment_le
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T) (P : InteractionPolynomial)
    (p : ℝ) (hp : 2 ≤ p) :
    ∫ η, |canonicalRoughError d N a mass T P η| ^ p ∂(canonicalJointMeasure d N)
      ≤ (((P.n : ℝ) + 1) * (p - 1) ^ ((P.n : ℝ) / 2)) ^ p
        * (∫ η, |canonicalRoughError d N a mass T P η| ^ (2 : ℝ)
            ∂(canonicalJointMeasure d N)) ^ (p / 2) := by
  classical
  obtain ⟨hf, hchaos⟩ := canonicalRoughErrorStd_mem_wienerChaosLE
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT P
  have hG1 := chaosLE_moment_le
    (hf.toLp (canonicalRoughErrorStd d N a mass T P)) hchaos p hp
  have hcoe := MemLp.coeFn_toLp hf
  have hmp : MeasureTheory.MeasurePreserving (canonicalJointStdGaussianMeasurableEquiv d N)
      (canonicalJointMeasure d N)
      (GaussianHilbert.stdGaussianFin (Fintype.card (CanonicalJointSumIndex d N))) :=
    ⟨(canonicalJointStdGaussianMeasurableEquiv d N).measurable,
      canonicalJointMeasure_map_stdGaussian (d := d) (N := N)⟩
  have htransfer : ∀ q : ℝ,
      ∫ ξ, |canonicalRoughErrorStd d N a mass T P ξ| ^ q
          ∂(GaussianHilbert.stdGaussianFin (Fintype.card (CanonicalJointSumIndex d N)))
        = ∫ η, |canonicalRoughError d N a mass T P η| ^ q
            ∂(canonicalJointMeasure d N) := by
    intro q
    rw [← hmp.integral_comp (canonicalJointStdGaussianMeasurableEquiv d N).measurableEmbedding
      (fun ξ => |canonicalRoughErrorStd d N a mass T P ξ| ^ q)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    simp only [canonicalRoughErrorStd_eq]
  have hp_eq : ∫ ξ, |((hf.toLp (canonicalRoughErrorStd d N a mass T P) :
        MeasureTheory.Lp ℝ 2 (GaussianHilbert.stdGaussianFin
          (Fintype.card (CanonicalJointSumIndex d N)))) :
        (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ) ξ| ^ p
      ∂(GaussianHilbert.stdGaussianFin (Fintype.card (CanonicalJointSumIndex d N)))
      = ∫ ξ, |canonicalRoughErrorStd d N a mass T P ξ| ^ p
          ∂(GaussianHilbert.stdGaussianFin (Fintype.card (CanonicalJointSumIndex d N))) :=
    integral_congr_ae (hcoe.mono fun ξ h => by simp only [h])
  have h2_eq : ∫ ξ, |((hf.toLp (canonicalRoughErrorStd d N a mass T P) :
        MeasureTheory.Lp ℝ 2 (GaussianHilbert.stdGaussianFin
          (Fintype.card (CanonicalJointSumIndex d N)))) :
        (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ) ξ| ^ (2 : ℝ)
      ∂(GaussianHilbert.stdGaussianFin (Fintype.card (CanonicalJointSumIndex d N)))
      = ∫ ξ, |canonicalRoughErrorStd d N a mass T P ξ| ^ (2 : ℝ)
          ∂(GaussianHilbert.stdGaussianFin (Fintype.card (CanonicalJointSumIndex d N))) :=
    integral_congr_ae (hcoe.mono fun ξ h => by simp only [h])
  rw [hp_eq, h2_eq, htransfer p, htransfer (2 : ℝ)] at hG1
  exact hG1

/-- Standard-Gaussian representative of the **full** interaction (`V_full = V_smooth + V_rough`). -/
private def canonicalFullInteractionJointStd
    (T : ℝ) (P : InteractionPolynomial) (ξ : canonicalStdIndex d N → ℝ) : ℝ :=
  canonicalSmoothInteractionStd d N a mass T P ξ + canonicalRoughErrorStd d N a mass T P ξ

@[simp] private lemma canonicalFullInteractionJointStd_eq
    (T : ℝ) (P : InteractionPolynomial) (η : CanonicalJoint d N) :
    canonicalFullInteractionJointStd d N a mass T P
        (canonicalJointStdGaussianMeasurableEquiv d N η) =
      canonicalFullInteractionJoint d N a mass T P η := by
  unfold canonicalFullInteractionJointStd
  rw [canonicalSmoothInteractionStd_eq, canonicalRoughErrorStd_eq]
  unfold canonicalRoughError; ring

private theorem canonicalFullInteractionJointStd_mem_wienerChaosLE
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T) (P : InteractionPolynomial) :
    ∃ hf : MeasureTheory.MemLp
        (canonicalFullInteractionJointStd d N a mass T P) 2
        (GaussianHilbert.stdGaussianFin (Fintype.card (CanonicalJointSumIndex d N))),
      (hf.toLp (canonicalFullInteractionJointStd d N a mass T P)) ∈
        GaussianHilbert.wienerChaosLE (Fintype.card (CanonicalJointSumIndex d N)) P.n := by
  obtain ⟨hfS, hSchaos⟩ := canonicalSmoothInteractionStd_mem_wienerChaosLE
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT P
  obtain ⟨hfR, hRchaos⟩ := canonicalRoughErrorStd_mem_wienerChaosLE
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT P
  refine ⟨hfS.add hfR, ?_⟩
  have h_toLp :
      (hfS.add hfR).toLp (canonicalFullInteractionJointStd d N a mass T P) =
        hfS.toLp (canonicalSmoothInteractionStd d N a mass T P)
          + hfR.toLp (canonicalRoughErrorStd d N a mass T P) := by
    simpa [canonicalFullInteractionJointStd] using (MeasureTheory.MemLp.toLp_add hfS hfR)
  rw [h_toLp]
  exact Submodule.add_mem _ hSchaos hRchaos

/-- **Full-interaction moment bound (Bonami–Nelson).** `∫ |V_full|^p ≤
((P.n+1)(p-1)^{P.n/2})^p · (∫ |V_full|²)^{p/2}` on the joint measure (`p ≥ 2`). -/
theorem canonicalFullInteractionJoint_moment_le
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T) (P : InteractionPolynomial)
    (p : ℝ) (hp : 2 ≤ p) :
    ∫ η, |canonicalFullInteractionJoint d N a mass T P η| ^ p ∂(canonicalJointMeasure d N)
      ≤ (((P.n : ℝ) + 1) * (p - 1) ^ ((P.n : ℝ) / 2)) ^ p
        * (∫ η, |canonicalFullInteractionJoint d N a mass T P η| ^ (2 : ℝ)
            ∂(canonicalJointMeasure d N)) ^ (p / 2) := by
  classical
  obtain ⟨hf, hchaos⟩ := canonicalFullInteractionJointStd_mem_wienerChaosLE
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT P
  have hG1 := chaosLE_moment_le
    (hf.toLp (canonicalFullInteractionJointStd d N a mass T P)) hchaos p hp
  have hcoe := MemLp.coeFn_toLp hf
  have hmp : MeasureTheory.MeasurePreserving (canonicalJointStdGaussianMeasurableEquiv d N)
      (canonicalJointMeasure d N)
      (GaussianHilbert.stdGaussianFin (Fintype.card (CanonicalJointSumIndex d N))) :=
    ⟨(canonicalJointStdGaussianMeasurableEquiv d N).measurable,
      canonicalJointMeasure_map_stdGaussian (d := d) (N := N)⟩
  have htransfer : ∀ q : ℝ,
      ∫ ξ, |canonicalFullInteractionJointStd d N a mass T P ξ| ^ q
          ∂(GaussianHilbert.stdGaussianFin (Fintype.card (CanonicalJointSumIndex d N)))
        = ∫ η, |canonicalFullInteractionJoint d N a mass T P η| ^ q
            ∂(canonicalJointMeasure d N) := by
    intro q
    rw [← hmp.integral_comp (canonicalJointStdGaussianMeasurableEquiv d N).measurableEmbedding
      (fun ξ => |canonicalFullInteractionJointStd d N a mass T P ξ| ^ q)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    simp only [canonicalFullInteractionJointStd_eq]
  have hp_eq : ∫ ξ, |((hf.toLp (canonicalFullInteractionJointStd d N a mass T P) :
        MeasureTheory.Lp ℝ 2 (GaussianHilbert.stdGaussianFin
          (Fintype.card (CanonicalJointSumIndex d N)))) :
        (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ) ξ| ^ p
      ∂(GaussianHilbert.stdGaussianFin (Fintype.card (CanonicalJointSumIndex d N)))
      = ∫ ξ, |canonicalFullInteractionJointStd d N a mass T P ξ| ^ p
          ∂(GaussianHilbert.stdGaussianFin (Fintype.card (CanonicalJointSumIndex d N))) :=
    integral_congr_ae (hcoe.mono fun ξ h => by simp only [h])
  have h2_eq : ∫ ξ, |((hf.toLp (canonicalFullInteractionJointStd d N a mass T P) :
        MeasureTheory.Lp ℝ 2 (GaussianHilbert.stdGaussianFin
          (Fintype.card (CanonicalJointSumIndex d N)))) :
        (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) → ℝ) ξ| ^ (2 : ℝ)
      ∂(GaussianHilbert.stdGaussianFin (Fintype.card (CanonicalJointSumIndex d N)))
      = ∫ ξ, |canonicalFullInteractionJointStd d N a mass T P ξ| ^ (2 : ℝ)
          ∂(GaussianHilbert.stdGaussianFin (Fintype.card (CanonicalJointSumIndex d N))) :=
    integral_congr_ae (hcoe.mono fun ξ h => by simp only [h])
  rw [hp_eq, h2_eq, htransfer p, htransfer (2 : ℝ)] at hG1
  exact hG1

/-! ## Generic L² Pythagoras (two functions)

Reusable: when `∫ L · R = 0`, `∫ (L + R)² = ∫ L² + ∫ R²`. Pure
integration linearity + the orthogonality input. Used to combine the
leading and per-coefficient pieces of `canonicalRoughError`. -/

/-- L² Pythagoras for two real-valued functions whose cross integral
vanishes. Pure integration linearity. -/
lemma integral_sq_add_of_inner_eq_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (L R : α → ℝ)
    (h_orth : ∫ x, L x * R x ∂μ = 0)
    (h_int_LL : Integrable (fun x => L x ^ 2) μ)
    (h_int_RR : Integrable (fun x => R x ^ 2) μ)
    (h_int_LR : Integrable (fun x => L x * R x) μ) :
    ∫ x, (L x + R x) ^ 2 ∂μ = ∫ x, L x ^ 2 ∂μ + ∫ x, R x ^ 2 ∂μ := by
  -- (L + R)² = L² + 2(LR) + R² pointwise
  have h_expand : ∀ x, (L x + R x) ^ 2 =
      L x ^ 2 + 2 * (L x * R x) + R x ^ 2 := by intros; ring
  have h_int_2LR : Integrable (fun x => 2 * (L x * R x)) μ := h_int_LR.const_mul 2
  calc ∫ x, (L x + R x) ^ 2 ∂μ
      = ∫ x, L x ^ 2 + 2 * (L x * R x) + R x ^ 2 ∂μ := by
        simp_rw [h_expand]
    _ = (∫ x, L x ^ 2 + 2 * (L x * R x) ∂μ) + ∫ x, R x ^ 2 ∂μ :=
        MeasureTheory.integral_add (h_int_LL.add h_int_2LR) h_int_RR
    _ = ∫ x, L x ^ 2 ∂μ + ∫ x, 2 * (L x * R x) ∂μ + ∫ x, R x ^ 2 ∂μ := by
        rw [MeasureTheory.integral_add h_int_LL h_int_2LR]
    _ = ∫ x, L x ^ 2 ∂μ + 2 * ∫ x, L x * R x ∂μ + ∫ x, R x ^ 2 ∂μ := by
        rw [MeasureTheory.integral_const_mul]
    _ = ∫ x, L x ^ 2 ∂μ + 2 * 0 + ∫ x, R x ^ 2 ∂μ := by rw [h_orth]
    _ = ∫ x, L x ^ 2 ∂μ + ∫ x, R x ^ 2 ∂μ := by ring

/-! ## Generic cross-sum vanish

For two finite-indexed coefficient sums whose pairwise cross-integrals
all vanish, the integral of their product vanishes. Used to combine
the leading and per-coefficient pieces of `canonicalRoughError` via
`integral_sq_add_of_inner_eq_zero`. -/

/-- Integrability of the product of two finite coefficient sums, assuming
pairwise integrability of every cross-product term. -/
lemma integrable_sum_mul_sum_of_pairwise
    {α ιA ιB : Type*} [MeasurableSpace α] {μ : Measure α}
    (sA : Finset ιA) (sB : Finset ιB)
    (cA : ιA → ℝ) (cB : ιB → ℝ)
    (fA : ιA → α → ℝ) (fB : ιB → α → ℝ)
    (h_int : ∀ iA ∈ sA, ∀ iB ∈ sB, Integrable (fun x => fA iA x * fB iB x) μ) :
    Integrable (fun x => (∑ iA ∈ sA, cA iA * fA iA x) *
         (∑ iB ∈ sB, cB iB * fB iB x)) μ := by
  have h_expand : (fun x => (∑ iA ∈ sA, cA iA * fA iA x) *
        (∑ iB ∈ sB, cB iB * fB iB x)) =
      (fun x => ∑ iA ∈ sA, ∑ iB ∈ sB,
        (cA iA * cB iB) * (fA iA x * fB iB x)) := by
    funext x
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun iA _ => ?_
    refine Finset.sum_congr rfl fun iB _ => ?_
    ring
  refine (MeasureTheory.integrable_finset_sum sA fun iA hiA =>
    MeasureTheory.integrable_finset_sum sB fun iB hiB =>
      (h_int iA hiA iB hiB).const_mul (cA iA * cB iB)).congr ?_
  filter_upwards with x
  exact (congrFun h_expand x).symm

/-- Integrability of the square of a finite coefficient sum, assuming
pairwise integrability of all products `f i * f j`. -/
lemma integrable_sq_real_sum_of_pairwise
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) (f : ι → α → ℝ) (a : ι → ℝ)
    (h_int : ∀ i ∈ s, ∀ j ∈ s, Integrable (fun x => f i x * f j x) μ) :
    Integrable (fun x => (∑ i ∈ s, a i * f i x) ^ 2) μ := by
  simpa [sq] using
    (integrable_sum_mul_sum_of_pairwise
      (μ := μ) s s a a f f h_int)

/-- Cross-integral of two finite sums vanishes when each pairwise
cross-integral does. Pure sum + integration linearity given the
pairwise orthogonality input. -/
lemma integral_sum_mul_sum_eq_zero_of_orth
    {α ιA ιB : Type*} [MeasurableSpace α] {μ : Measure α}
    (sA : Finset ιA) (sB : Finset ιB)
    (cA : ιA → ℝ) (cB : ιB → ℝ)
    (fA : ιA → α → ℝ) (fB : ιB → α → ℝ)
    (h_orth : ∀ iA ∈ sA, ∀ iB ∈ sB, ∫ x, fA iA x * fB iB x ∂μ = 0)
    (h_int : ∀ iA ∈ sA, ∀ iB ∈ sB, Integrable (fun x => fA iA x * fB iB x) μ) :
    ∫ x, (∑ iA ∈ sA, cA iA * fA iA x) *
         (∑ iB ∈ sB, cB iB * fB iB x) ∂μ = 0 := by
  -- Pointwise expand (Σ a f) * (Σ b g) = Σ Σ (a b) (f g)
  have h_expand : (fun x => (∑ iA ∈ sA, cA iA * fA iA x) *
        (∑ iB ∈ sB, cB iB * fB iB x)) =
      (fun x => ∑ iA ∈ sA, ∑ iB ∈ sB,
        (cA iA * cB iB) * (fA iA x * fB iB x)) := by
    funext x
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun iA _ => ?_
    refine Finset.sum_congr rfl fun iB _ => ?_
    ring
  rw [h_expand]
  -- Outer integration linearity
  rw [MeasureTheory.integral_finset_sum sA (fun iA hiA =>
    MeasureTheory.integrable_finset_sum sB (fun iB hiB =>
      (h_int iA hiA iB hiB).const_mul (cA iA * cB iB)))]
  apply Finset.sum_eq_zero
  intros iA hiA
  -- Inner integration linearity
  rw [MeasureTheory.integral_finset_sum sB (fun iB hiB =>
    (h_int iA hiA iB hiB).const_mul (cA iA * cB iB))]
  apply Finset.sum_eq_zero
  intros iB hiB
  -- Pull constants out, apply orthogonality
  rw [MeasureTheory.integral_const_mul, h_orth iA hiA iB hiB, mul_zero]

/-! ## Generic L²-orthogonality reduction

Reusable lemma not specific to the rough-error setting: for a finite-indexed
family `f i` of real-valued functions that are pairwise L²-orthogonal under
a measure `μ`, the integral of the squared real-coefficient sum reduces to
a single sum of squared coefficients times squared L² norms (no off-diagonal
contribution).

Given:
- `s : Finset ι` and `f : ι → α → ℝ` with `a : ι → ℝ` coefficients,
- pairwise orthogonality `∫ f i · f j ∂μ = 0` for `i ≠ j` in `s`,
- pairwise integrability of products `f i · f j`,

then `∫ (∑ i, a i · f i)² ∂μ = ∑ i, (a i)² · ∫ (f i)² ∂μ`. -/
lemma integral_sq_real_sum_of_pairwise_orthogonal
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) (f : ι → α → ℝ) (a : ι → ℝ)
    (h_orth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∫ x, f i x * f j x ∂μ = 0)
    (h_int : ∀ i ∈ s, ∀ j ∈ s, Integrable (fun x => f i x * f j x) μ) :
    ∫ x, (∑ i ∈ s, a i * f i x) ^ 2 ∂μ =
    ∑ i ∈ s, (a i) ^ 2 * ∫ x, (f i x) ^ 2 ∂μ := by
  classical
  -- Step 1: expand the square pointwise as a double sum
  have h_expand : (fun x => (∑ i ∈ s, a i * f i x) ^ 2) =
      (fun x => ∑ i ∈ s, ∑ j ∈ s, (a i * a j) * (f i x * f j x)) := by
    funext x
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h_expand]
  -- Step 2: integration linearity (outer sum)
  have h_int_inner : ∀ i ∈ s, Integrable
      (fun x => ∑ j ∈ s, (a i * a j) * (f i x * f j x)) μ := by
    intros i hi
    apply MeasureTheory.integrable_finset_sum
    intros j hj
    exact (h_int i hi j hj).const_mul (a i * a j)
  rw [MeasureTheory.integral_finset_sum s h_int_inner]
  refine Finset.sum_congr rfl fun i hi => ?_
  -- Step 3: integration linearity (inner sum) + pull constants out
  rw [MeasureTheory.integral_finset_sum s
        (fun j hj => (h_int i hi j hj).const_mul (a i * a j))]
  have h_const : ∀ j ∈ s,
      ∫ x, (a i * a j) * (f i x * f j x) ∂μ =
      (a i * a j) * ∫ x, f i x * f j x ∂μ := by
    intros j _
    exact MeasureTheory.integral_const_mul _ _
  rw [Finset.sum_congr rfl h_const]
  -- Step 4: split diagonal vs off-diagonal; off-diagonal vanishes by orthogonality
  rw [show ∑ j ∈ s, (a i * a j) * ∫ x, f i x * f j x ∂μ =
        ∑ j ∈ s.erase i, (a i * a j) * ∫ x, f i x * f j x ∂μ +
        (a i * a i) * ∫ x, f i x * f i x ∂μ from
      (Finset.sum_erase_add s _ hi).symm]
  rw [show ∑ j ∈ s.erase i, (a i * a j) * ∫ x, f i x * f j x ∂μ = 0 from ?_]
  · -- Diagonal piece: (a i * a i) * ∫ f i * f i = (a i)^2 * ∫ (f i)^2
    rw [zero_add]
    have h_eq : ∀ x, f i x * f i x = (f i x) ^ 2 := fun x => by ring
    simp_rw [h_eq]
    congr 1
    ring
  · -- Off-diagonal vanishes
    apply Finset.sum_eq_zero
    intros j hj
    rw [Finset.mem_erase] at hj
    rw [h_orth i hi j hj.2 (Ne.symm hj.1), mul_zero]

/-! ## S3: cross-term orthogonality

Distinct `(k, j) ≠ (k', j')` give zero cross-expectation:
`∫ canonicalCrossTerm k j · canonicalCrossTerm k' j' ∂canonicalJointMeasure = 0`.

**Proof path** (deferred): the joint measure is `Measure.prod μ_S μ_R`
(see `FieldDecomposition.lean:47`), and the cross-term factorises as
`(smooth Wick monomial in η.1) · (rough Wick monomial in η.2)`. Apply
`MeasureTheory.integral_prod_mul` to split into a smooth integral
times a rough integral. Then the **2-site Wick power formula** (the
canonical analog of `gff_wickPower_two_site_inner`) gives a Kronecker
delta on each factor: smooth integral vanishes unless `j = j'`, rough
integral vanishes unless `k - j = k' - j'`. Combined: vanishes unless
`(k, j) = (k', j')`.

The 2-site Wick formula itself is the standard Janson-Hilbert
identity `∫ :φ(x)^n: :φ(y)^m: dμ = δ_{n,m} · n! · C(x,y)^n` for a
centered Gaussian field with covariance `C`. On the canonical side
this reduces (via `wickMonomial_pow_sum_expansion_of_totalDegree`
from gaussian-field) to multivariate Hermite orthogonality on the
standard product Gaussian (`hermiteMulti_orthogonality` from
gaussian-hilbert). Either provable in-repo or addable upstream.

S3 is the gating sorry for the L²-sq decomposition that S4 needs. -/

/-- **S3 (sorry'd): cross-term orthogonality.** Distinct `(k, j)` and
`(k', j')` give zero cross-expectation under the canonical joint
measure. Together with `MeasureTheory.integral_prod_mul`, this is the
one analytical input S4 needs from the Wick-orthogonality side.

See module docstring above for the proof sketch. -/
lemma canonicalCrossTerm_inner_eq_zero
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (k j k' j' : ℕ)
    (hj : j ∈ Finset.range k) (hj' : j' ∈ Finset.range k')
    (h : (k, j) ≠ (k', j')) :
    ∫ η, canonicalCrossTerm d N a mass T η k j *
         canonicalCrossTerm d N a mass T η k' j'
         ∂(canonicalJointMeasure d N) = 0 := by
  let cS := smoothWickConstant d N a mass T
  let cR := roughWickConstant d N a mass T
  let μS : Measure ((Fin d → Fin N) → ℝ) :=
    Measure.pi (fun _ : Fin d → Fin N => ProbabilityTheory.gaussianReal 0 1)
  let μR : Measure ((Fin d → Fin N) → ℝ) :=
    Measure.pi (fun _ : Fin d → Fin N => ProbabilityTheory.gaussianReal 0 1)
  let term : FinLatticeSites d N → FinLatticeSites d N → CanonicalJoint d N → ℝ :=
    fun x y η =>
      (wickMonomial j cS (canonicalSmoothFieldFunction d N a mass T η x) *
          wickMonomial j' cS (canonicalSmoothFieldFunction d N a mass T η y)) *
        (wickMonomial (k - j) cR (canonicalRoughFieldFunction d N a mass T η x) *
          wickMonomial (k' - j') cR (canonicalRoughFieldFunction d N a mass T η y))
  have h_term_int :
      ∀ x y, Integrable (term x y) (canonicalJointMeasure d N) := by
    intro x y
    rw [canonicalJointMeasure]
    let f : ((Fin d → Fin N) → ℝ) → ℝ := fun η_S =>
      wickMonomial j cS (canonicalSmoothFieldFunctionOfFst d N a mass T η_S x) *
        wickMonomial j' cS (canonicalSmoothFieldFunctionOfFst d N a mass T η_S y)
    let g : ((Fin d → Fin N) → ℝ) → ℝ := fun η_R =>
      wickMonomial (k - j) cR (canonicalRoughFieldFunctionOfSnd d N a mass T η_R x) *
        wickMonomial (k' - j') cR (canonicalRoughFieldFunctionOfSnd d N a mass T η_R y)
    have hf : Integrable f μS := by
      simpa [f, μS, cS] using
        (canonicalSmoothWickPower_two_site_marginal_integrable
          (d := d) (N := N) (a := a) (mass := mass)
          ha hmass T hT j j' x y)
    have hg : Integrable g μR := by
      simpa [g, μR, cR] using
        (canonicalRoughWickPower_two_site_marginal_integrable
          (d := d) (N := N) (a := a) (mass := mass)
          ha hmass T hT (k - j) (k' - j') x y)
    simpa
        [term, CanonicalJoint, f, g, μS, μR, cS, cR,
          mul_assoc, mul_left_comm, mul_comm] using
      (Integrable.mul_prod (μ := μS) (ν := μR) hf hg)
  have h_expand :
      ∀ η : CanonicalJoint d N,
        canonicalCrossTerm d N a mass T η k j *
            canonicalCrossTerm d N a mass T η k' j' =
          ((a ^ d) * (a ^ d)) * ∑ x : FinLatticeSites d N,
            ∑ y : FinLatticeSites d N, term x y η := by
    intro η
    unfold canonicalCrossTerm term
    rw [show
      (a ^ d * ∑ x,
          wickMonomial j (smoothWickConstant d N a mass T)
              (canonicalSmoothFieldFunction d N a mass T η x) *
            wickMonomial (k - j) (roughWickConstant d N a mass T)
              (canonicalRoughFieldFunction d N a mass T η x)) *
        (a ^ d * ∑ x,
          wickMonomial j' (smoothWickConstant d N a mass T)
              (canonicalSmoothFieldFunction d N a mass T η x) *
            wickMonomial (k' - j') (roughWickConstant d N a mass T)
              (canonicalRoughFieldFunction d N a mass T η x)) =
      ((a ^ d) * (a ^ d)) *
      ((∑ x,
          wickMonomial j (smoothWickConstant d N a mass T)
              (canonicalSmoothFieldFunction d N a mass T η x) *
            wickMonomial (k - j) (roughWickConstant d N a mass T)
              (canonicalRoughFieldFunction d N a mass T η x)) *
        (∑ x,
          wickMonomial j' (smoothWickConstant d N a mass T)
              (canonicalSmoothFieldFunction d N a mass T η x) *
            wickMonomial (k' - j') (roughWickConstant d N a mass T)
              (canonicalRoughFieldFunction d N a mass T η x))) by
      ring]
    rw [Finset.sum_mul_sum]
    simp [cS, cR, mul_assoc, mul_left_comm]
  simp_rw [h_expand]
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_finset_sum _ (fun x _ =>
    MeasureTheory.integrable_finset_sum _ (fun y _ => h_term_int x y))]
  suffices hsum :
      ∑ x : FinLatticeSites d N,
        ∫ η, ∑ y : FinLatticeSites d N, term x y η ∂(canonicalJointMeasure d N) = 0 by
    rw [hsum]
    ring
  apply Finset.sum_eq_zero
  intro x hx
  rw [MeasureTheory.integral_finset_sum _ (fun y _ => h_term_int x y)]
  apply Finset.sum_eq_zero
  intro y hy
  have h_factor :
      ∫ η, term x y η ∂(canonicalJointMeasure d N) =
        (∫ η_S, wickMonomial j cS (canonicalSmoothFieldFunctionOfFst d N a mass T η_S x) *
            wickMonomial j' cS (canonicalSmoothFieldFunctionOfFst d N a mass T η_S y) ∂μS) *
        (∫ η_R,
            wickMonomial (k - j) cR
              (canonicalRoughFieldFunctionOfSnd d N a mass T η_R x) *
            wickMonomial (k' - j') cR
              (canonicalRoughFieldFunctionOfSnd d N a mass T η_R y) ∂μR) := by
    rw [canonicalJointMeasure]
    simpa
        [term, CanonicalJoint, μS, μR, cS, cR,
          mul_assoc, mul_left_comm, mul_comm] using
      (integral_prod_mul
        (μ := μS) (ν := μR)
        (f := fun η_S =>
          wickMonomial j cS (canonicalSmoothFieldFunctionOfFst d N a mass T η_S x) *
            wickMonomial j' cS (canonicalSmoothFieldFunctionOfFst d N a mass T η_S y))
        (g := fun η_R =>
          wickMonomial (k - j) cR (canonicalRoughFieldFunctionOfSnd d N a mass T η_R x) *
            wickMonomial (k' - j') cR (canonicalRoughFieldFunctionOfSnd d N a mass T η_R y)))
  have hj_lt : j < k := Finset.mem_range.mp hj
  have hj'_lt : j' < k' := Finset.mem_range.mp hj'
  by_cases hjj : j = j'
  · have hrough : k - j ≠ k' - j' := by
      intro hsub
      apply h
      have hk : k = k' := by
        calc
          k = (k - j) + j := by
            symm
            exact Nat.sub_add_cancel (Nat.le_of_lt hj_lt)
          _ = (k' - j') + j' := by
            simpa [hjj] using congrArg (fun t => t + j) hsub
          _ = k' := Nat.sub_add_cancel (Nat.le_of_lt hj'_lt)
      simp [hk, hjj]
    rw [h_factor]
    rw [canonicalRoughWickPower_two_site_marginal_eq_zero_of_ne
      (d := d) (N := N) (a := a) (mass := mass)
      ha hmass T hT
      (k - j) (k' - j') hrough x y]
    ring
  · rw [h_factor]
    rw [canonicalSmoothWickPower_two_site_marginal_eq_zero_of_ne
      (d := d) (N := N) (a := a) (mass := mass)
      ha hmass T hT
      j j' hjj x y]
    ring

/-! ## S3 application — `(c · binomial sum)`-style L²-sq decomposition

A shared helper that handles BOTH the leading `(1 / P.n)` piece and
each per-coefficient `P.coeff m` piece of `canonicalRoughError`: for any
fixed `(k, c)`, the L² norm of `c · Σ_j C(k, j) · cross(k, j)` decomposes
into the sum-of-squares form via the generic orthogonality reduction.

The leading-piece application is `k = P.n, c = 1 / P.n`; each
per-coefficient application is `k = m, c = P.coeff m` for `m : Fin P.n`.
The full per-coefficient sum (over `m`) is a further outer application
of the orthogonality reduction (left for follow-up). -/

/-- Generic helper: the L²-sq of `c · Σ_j C(k, j) · cross(k, j)`
decomposes into a sum of squared inner coefficients times squared L²
norms of the cross-terms. Both the leading piece and each per-coefficient
inner sum are special cases of this lemma. -/
lemma canonicalCrossTerm_scaled_inner_sum_l2_sq
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T) (k : ℕ) (c : ℝ)
    (h_int : ∀ j ∈ Finset.range k, ∀ j' ∈ Finset.range k,
        Integrable (fun η =>
            canonicalCrossTerm d N a mass T η k j *
            canonicalCrossTerm d N a mass T η k j')
            (canonicalJointMeasure d N)) :
    ∫ η, (c * ∑ j ∈ Finset.range k,
              (k.choose j : ℝ) * canonicalCrossTerm d N a mass T η k j) ^ 2
        ∂(canonicalJointMeasure d N) =
    ∑ j ∈ Finset.range k,
      (c * (k.choose j : ℝ)) ^ 2 *
        ∫ η, (canonicalCrossTerm d N a mass T η k j) ^ 2
            ∂(canonicalJointMeasure d N) := by
  -- Rewrite c · Σ_j ... as Σ_j (c · C(k, j)) · cross_j
  have h_pull : ∀ η, c * ∑ j ∈ Finset.range k,
        (k.choose j : ℝ) * canonicalCrossTerm d N a mass T η k j =
      ∑ j ∈ Finset.range k,
        (c * (k.choose j : ℝ)) *
          canonicalCrossTerm d N a mass T η k j := by
    intro η
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [h_pull]
  -- Apply the generic L²-orthogonality reduction
  apply integral_sq_real_sum_of_pairwise_orthogonal
    (Finset.range k)
    (fun j η => canonicalCrossTerm d N a mass T η k j)
    (fun j => c * (k.choose j : ℝ))
  · -- orthogonality: distinct j give zero cross-expectation (apply stub at k = k')
    intros j hj j' hj' hne
    refine canonicalCrossTerm_inner_eq_zero d N a mass ha hmass T hT k j k j' hj hj' ?_
    intro h
    exact hne (congrArg Prod.snd h)
  · -- integrability hypothesis (pass through)
    exact h_int

/-- L²-sq decomposition of the leading `(1 / P.n)` piece of the rough
error. Direct application of `canonicalCrossTerm_scaled_inner_sum_l2_sq`
with `k = P.n` and `c = 1 / P.n`. -/
lemma canonicalRoughError_leading_l2_sq
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T) (P : InteractionPolynomial)
    (h_int : ∀ j ∈ Finset.range P.n, ∀ j' ∈ Finset.range P.n,
        Integrable (fun η =>
            canonicalCrossTerm d N a mass T η P.n j *
            canonicalCrossTerm d N a mass T η P.n j')
            (canonicalJointMeasure d N)) :
    ∫ η, ((1 / P.n : ℝ) * ∑ j ∈ Finset.range P.n,
              (P.n.choose j : ℝ) * canonicalCrossTerm d N a mass T η P.n j) ^ 2
        ∂(canonicalJointMeasure d N) =
    ∑ j ∈ Finset.range P.n,
      ((1 / P.n : ℝ) * (P.n.choose j : ℝ)) ^ 2 *
        ∫ η, (canonicalCrossTerm d N a mass T η P.n j) ^ 2
            ∂(canonicalJointMeasure d N) :=
  canonicalCrossTerm_scaled_inner_sum_l2_sq d N a mass ha hmass T hT P.n (1 / P.n : ℝ) h_int

/-- L²-sq decomposition of a single per-coefficient `P.coeff m` piece
of the rough error (one fixed `m : Fin P.n`). Direct application of
`canonicalCrossTerm_scaled_inner_sum_l2_sq` with `k = m` and
`c = P.coeff m`. The full per-coefficient sum further sums these over
`m` (left for follow-up). -/
lemma canonicalRoughError_perCoeff_l2_sq
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T) (P : InteractionPolynomial) (m : Fin P.n)
    (h_int : ∀ j ∈ Finset.range (m : ℕ), ∀ j' ∈ Finset.range (m : ℕ),
        Integrable (fun η =>
            canonicalCrossTerm d N a mass T η (m : ℕ) j *
            canonicalCrossTerm d N a mass T η (m : ℕ) j')
            (canonicalJointMeasure d N)) :
    ∫ η, (P.coeff m * ∑ j ∈ Finset.range (m : ℕ),
              ((m : ℕ).choose j : ℝ) *
                canonicalCrossTerm d N a mass T η (m : ℕ) j) ^ 2
        ∂(canonicalJointMeasure d N) =
    ∑ j ∈ Finset.range (m : ℕ),
      (P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2 *
        ∫ η, (canonicalCrossTerm d N a mass T η (m : ℕ) j) ^ 2
            ∂(canonicalJointMeasure d N) :=
  canonicalCrossTerm_scaled_inner_sum_l2_sq d N a mass ha hmass T hT (m : ℕ) (P.coeff m) h_int

/-! ## S3 outer cross: ∫ Lead · PerCoef = 0

Apply `integral_sum_mul_sum_eq_zero_of_orth` to vanish the cross
integral between the leading `(1/P.n)` piece and the per-coefficient
piece of `canonicalRoughError`. Each (P.n, j) vs (m, j') pair has
P.n ≠ m (since m : Fin P.n implies m < P.n), so the cross integral
vanishes by `canonicalCrossTerm_inner_eq_zero`. -/

/-- The cross integral between the leading and per-coefficient pieces
of `canonicalRoughError` vanishes.

Specifically: with `Lead = (1/P.n) · Σ_j C(P.n,j) · cross(P.n, j)`
and `PerCoef = Σ_m P.coeff m · (Σ_{j'} C(m, j') · cross(m, j'))`,
`∫ Lead · PerCoef ∂μ = 0`. The pairwise orthogonality between
`(P.n, j)` and `(m, j')` indices gives the result via
`integral_sum_mul_sum_eq_zero_of_orth`. -/
lemma canonicalLeading_perCoeff_inner_eq_zero
    (T : ℝ) (P : InteractionPolynomial)
    (h_orth_pairs : ∀ j ∈ Finset.range P.n,
        ∀ m ∈ (Finset.univ : Finset (Fin P.n)),
        ∫ η, canonicalCrossTerm d N a mass T η P.n j *
              ∑ j' ∈ Finset.range (m : ℕ),
                ((m : ℕ).choose j' : ℝ) *
                  canonicalCrossTerm d N a mass T η (m : ℕ) j'
              ∂(canonicalJointMeasure d N) = 0)
    (h_int : ∀ j ∈ Finset.range P.n,
        ∀ m ∈ (Finset.univ : Finset (Fin P.n)),
        Integrable (fun η =>
            canonicalCrossTerm d N a mass T η P.n j *
            ∑ j' ∈ Finset.range (m : ℕ),
              ((m : ℕ).choose j' : ℝ) *
                canonicalCrossTerm d N a mass T η (m : ℕ) j')
            (canonicalJointMeasure d N)) :
    ∫ η, ((1 / P.n : ℝ) * ∑ j ∈ Finset.range P.n,
              (P.n.choose j : ℝ) * canonicalCrossTerm d N a mass T η P.n j) *
         (∑ m : Fin P.n, P.coeff m *
              ∑ j' ∈ Finset.range (m : ℕ),
                ((m : ℕ).choose j' : ℝ) *
                  canonicalCrossTerm d N a mass T η (m : ℕ) j')
        ∂(canonicalJointMeasure d N) = 0 := by
  -- Pull (1/P.n) into the sum: (1/P.n) · Σ_j ... = Σ_j ((1/P.n) · ...) ...
  have h_pull : ∀ η, (1 / P.n : ℝ) * ∑ j ∈ Finset.range P.n,
        (P.n.choose j : ℝ) * canonicalCrossTerm d N a mass T η P.n j =
      ∑ j ∈ Finset.range P.n,
        ((1 / P.n : ℝ) * (P.n.choose j : ℝ)) *
          canonicalCrossTerm d N a mass T η P.n j := by
    intro η
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [h_pull]
  -- Apply the cross-sum vanish helper
  exact integral_sum_mul_sum_eq_zero_of_orth
    (Finset.range P.n) (Finset.univ : Finset (Fin P.n))
    (fun j => (1 / P.n : ℝ) * (P.n.choose j : ℝ))
    (fun m => P.coeff m)
    (fun j η => canonicalCrossTerm d N a mass T η P.n j)
    (fun m η => ∑ j' ∈ Finset.range (m : ℕ),
        ((m : ℕ).choose j' : ℝ) *
          canonicalCrossTerm d N a mass T η (m : ℕ) j')
    h_orth_pairs
    h_int

/-! ## S3 final assembly (level 1): split E_R² into Lead² + PerCoef²

Composing S2 (Lead + PerCoef form), the cross-vanish lemma
`canonicalLeading_perCoeff_inner_eq_zero`, and the Pythagoras helper
`integral_sq_add_of_inner_eq_zero`. -/

/-- The L²-sq of `canonicalRoughError` splits into L²-sq of the leading
piece plus L²-sq of the per-coefficient piece, given:
* pairwise orthogonality between leading and per-coefficient cross-terms
  (provable from `canonicalCrossTerm_inner_eq_zero` since `m < P.n`);
* integrability of `Lead²`, `PerCoef²`, `Lead · PerCoef`;
* integrability of all leading × per-coefficient cross-term pairs.

The further decomposition of `∫ Lead²` and `∫ PerCoef²` into
sums-of-squares uses `canonicalRoughError_leading_l2_sq` and a yet-to-be-
done outer-orthogonality reduction over `m : Fin P.n` of
`canonicalRoughError_perCoeff_l2_sq`. -/
theorem canonicalRoughError_l2_sq_eq_lead_plus_perCoef_sq
    (T : ℝ) (P : InteractionPolynomial)
    (h_orth_lead_perCoef : ∀ j ∈ Finset.range P.n,
        ∀ m ∈ (Finset.univ : Finset (Fin P.n)),
        ∫ η, canonicalCrossTerm d N a mass T η P.n j *
              ∑ j' ∈ Finset.range (m : ℕ),
                ((m : ℕ).choose j' : ℝ) *
                  canonicalCrossTerm d N a mass T η (m : ℕ) j'
              ∂(canonicalJointMeasure d N) = 0)
    (h_int_lead_sq : Integrable (fun η =>
        ((1 / P.n : ℝ) * ∑ j ∈ Finset.range P.n,
          (P.n.choose j : ℝ) * canonicalCrossTerm d N a mass T η P.n j) ^ 2)
        (canonicalJointMeasure d N))
    (h_int_perCoef_sq : Integrable (fun η =>
        (∑ m : Fin P.n, P.coeff m * ∑ j' ∈ Finset.range (m : ℕ),
          ((m : ℕ).choose j' : ℝ) *
            canonicalCrossTerm d N a mass T η (m : ℕ) j') ^ 2)
        (canonicalJointMeasure d N))
    (h_int_cross : Integrable (fun η =>
        ((1 / P.n : ℝ) * ∑ j ∈ Finset.range P.n,
          (P.n.choose j : ℝ) * canonicalCrossTerm d N a mass T η P.n j) *
        (∑ m : Fin P.n, P.coeff m * ∑ j' ∈ Finset.range (m : ℕ),
          ((m : ℕ).choose j' : ℝ) *
            canonicalCrossTerm d N a mass T η (m : ℕ) j'))
        (canonicalJointMeasure d N))
    (h_int_pairs : ∀ j ∈ Finset.range P.n,
        ∀ m ∈ (Finset.univ : Finset (Fin P.n)),
        Integrable (fun η =>
            canonicalCrossTerm d N a mass T η P.n j *
            ∑ j' ∈ Finset.range (m : ℕ),
              ((m : ℕ).choose j' : ℝ) *
                canonicalCrossTerm d N a mass T η (m : ℕ) j')
            (canonicalJointMeasure d N)) :
    ∫ η, (canonicalRoughError d N a mass T P η) ^ 2
        ∂(canonicalJointMeasure d N) =
    (∫ η, ((1 / P.n : ℝ) * ∑ j ∈ Finset.range P.n,
          (P.n.choose j : ℝ) * canonicalCrossTerm d N a mass T η P.n j) ^ 2
        ∂(canonicalJointMeasure d N)) +
    (∫ η, (∑ m : Fin P.n, P.coeff m * ∑ j' ∈ Finset.range (m : ℕ),
          ((m : ℕ).choose j' : ℝ) *
            canonicalCrossTerm d N a mass T η (m : ℕ) j') ^ 2
        ∂(canonicalJointMeasure d N)) := by
  -- Rewrite canonicalRoughError to its (Lead + PerCoef) form via S2
  simp_rw [canonicalRoughError_eq_sum_over_cross_terms d N a mass T P]
  -- Apply Pythagoras
  exact integral_sq_add_of_inner_eq_zero _ _
    (canonicalLeading_perCoeff_inner_eq_zero d N a mass T P
      h_orth_lead_perCoef h_int_pairs)
    h_int_lead_sq h_int_perCoef_sq h_int_cross

/-! ## S3 outer-orth on `Σ_m`: ∫ PerCoef² = Σ_m ∫ R_m²

Apply `integral_sq_real_sum_of_pairwise_orthogonal` (with all
coefficients = 1) to the per-coefficient sum, treating each
`R_m η = P.coeff m · Σ_j' C(m, j') · cross(m, j') η` as a single
function of `η`. Conditional on:
* pairwise orthogonality of the `R_m` (provable from
  `canonicalCrossTerm_inner_eq_zero` between `(m, j)` and `(m', j')`
  for `m ≠ m'`);
* pairwise integrability of `R_m · R_m'`.
-/

/-- The L²-sq of the per-coefficient piece decomposes into a sum of
L²-sq of the per-`m` `R_m` pieces, given pairwise orthogonality of
the `R_m`'s. -/
lemma canonicalRoughError_perCoef_outer_l2_sq
    (T : ℝ) (P : InteractionPolynomial)
    (h_orth_m : ∀ m ∈ (Finset.univ : Finset (Fin P.n)),
        ∀ m' ∈ (Finset.univ : Finset (Fin P.n)),
        m ≠ m' →
        ∫ η, (P.coeff m * ∑ j ∈ Finset.range (m : ℕ),
                ((m : ℕ).choose j : ℝ) *
                  canonicalCrossTerm d N a mass T η (m : ℕ) j) *
              (P.coeff m' * ∑ j' ∈ Finset.range (m' : ℕ),
                ((m' : ℕ).choose j' : ℝ) *
                  canonicalCrossTerm d N a mass T η (m' : ℕ) j')
              ∂(canonicalJointMeasure d N) = 0)
    (h_int_m : ∀ m ∈ (Finset.univ : Finset (Fin P.n)),
        ∀ m' ∈ (Finset.univ : Finset (Fin P.n)),
        Integrable (fun η =>
            (P.coeff m * ∑ j ∈ Finset.range (m : ℕ),
                ((m : ℕ).choose j : ℝ) *
                  canonicalCrossTerm d N a mass T η (m : ℕ) j) *
            (P.coeff m' * ∑ j' ∈ Finset.range (m' : ℕ),
                ((m' : ℕ).choose j' : ℝ) *
                  canonicalCrossTerm d N a mass T η (m' : ℕ) j'))
            (canonicalJointMeasure d N)) :
    ∫ η, (∑ m : Fin P.n, P.coeff m *
              ∑ j ∈ Finset.range (m : ℕ),
                ((m : ℕ).choose j : ℝ) *
                  canonicalCrossTerm d N a mass T η (m : ℕ) j) ^ 2
        ∂(canonicalJointMeasure d N) =
    ∑ m : Fin P.n,
      ∫ η, (P.coeff m * ∑ j ∈ Finset.range (m : ℕ),
                ((m : ℕ).choose j : ℝ) *
                  canonicalCrossTerm d N a mass T η (m : ℕ) j) ^ 2
          ∂(canonicalJointMeasure d N) := by
  -- Rewrite Σ_m R_m as Σ_m 1 · R_m so the generic lemma's `a` slot is unit
  have h_one_smul : ∀ η, ∑ m : Fin P.n, P.coeff m *
        ∑ j ∈ Finset.range (m : ℕ),
          ((m : ℕ).choose j : ℝ) *
            canonicalCrossTerm d N a mass T η (m : ℕ) j =
      ∑ m : Fin P.n, (1 : ℝ) *
        (P.coeff m * ∑ j ∈ Finset.range (m : ℕ),
          ((m : ℕ).choose j : ℝ) *
            canonicalCrossTerm d N a mass T η (m : ℕ) j) := by
    intro η
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  simp_rw [h_one_smul]
  -- Apply the generic L²-orthogonality reduction
  have h := integral_sq_real_sum_of_pairwise_orthogonal
    (Finset.univ : Finset (Fin P.n))
    (fun m η => P.coeff m * ∑ j ∈ Finset.range (m : ℕ),
        ((m : ℕ).choose j : ℝ) *
          canonicalCrossTerm d N a mass T η (m : ℕ) j)
    (fun _ => (1 : ℝ))
    h_orth_m
    h_int_m
  -- The result has `1^2 *` factors that we collapse
  rw [h]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-! ## S3 final composition: ∫ E_R² as a full sum-of-squares

Composes the four pieces of the L²-sq chain:
* `canonicalRoughError_l2_sq_eq_lead_plus_perCoef_sq`
* `canonicalRoughError_leading_l2_sq`
* `canonicalRoughError_perCoef_outer_l2_sq`
* `canonicalRoughError_perCoeff_l2_sq` (one per m)
into the explicit sum-of-squares form needed by S4. -/

/-- **Full L²-sq decomposition of `canonicalRoughError`.** Composes the
leading + per-coefficient split, the leading sum-of-squares, the outer
orthogonality on `Σ_m`, and the per-`m` sum-of-squares.

The result expresses `∫ canonicalRoughError² dμ_joint` as the sum of
squared coefficients times squared L² norms of `canonicalCrossTerm`
values, ranging over all `(k, j)` indices appearing in
`canonicalRoughError` (i.e. `k = P.n` for the leading piece and
`k = m, m : Fin P.n` for the per-coefficient pieces). -/
theorem canonicalRoughError_l2_sq_eq
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T) (P : InteractionPolynomial)
    -- Cross-vanish (orthogonality) hypotheses
    (h_orth_lead_perCoef : ∀ j ∈ Finset.range P.n,
        ∀ m ∈ (Finset.univ : Finset (Fin P.n)),
        ∫ η, canonicalCrossTerm d N a mass T η P.n j *
              ∑ j' ∈ Finset.range (m : ℕ),
                ((m : ℕ).choose j' : ℝ) *
                  canonicalCrossTerm d N a mass T η (m : ℕ) j'
              ∂(canonicalJointMeasure d N) = 0)
    (h_orth_m_outer : ∀ m ∈ (Finset.univ : Finset (Fin P.n)),
        ∀ m' ∈ (Finset.univ : Finset (Fin P.n)),
        m ≠ m' →
        ∫ η, (P.coeff m * ∑ j ∈ Finset.range (m : ℕ),
                ((m : ℕ).choose j : ℝ) *
                  canonicalCrossTerm d N a mass T η (m : ℕ) j) *
              (P.coeff m' * ∑ j' ∈ Finset.range (m' : ℕ),
                ((m' : ℕ).choose j' : ℝ) *
                  canonicalCrossTerm d N a mass T η (m' : ℕ) j')
              ∂(canonicalJointMeasure d N) = 0)
    -- Integrability hypotheses
    (h_int_lead_sq : Integrable (fun η =>
        ((1 / P.n : ℝ) * ∑ j ∈ Finset.range P.n,
          (P.n.choose j : ℝ) * canonicalCrossTerm d N a mass T η P.n j) ^ 2)
        (canonicalJointMeasure d N))
    (h_int_perCoef_sq : Integrable (fun η =>
        (∑ m : Fin P.n, P.coeff m * ∑ j' ∈ Finset.range (m : ℕ),
          ((m : ℕ).choose j' : ℝ) *
            canonicalCrossTerm d N a mass T η (m : ℕ) j') ^ 2)
        (canonicalJointMeasure d N))
    (h_int_cross_lead_perCoef : Integrable (fun η =>
        ((1 / P.n : ℝ) * ∑ j ∈ Finset.range P.n,
          (P.n.choose j : ℝ) * canonicalCrossTerm d N a mass T η P.n j) *
        (∑ m : Fin P.n, P.coeff m * ∑ j' ∈ Finset.range (m : ℕ),
          ((m : ℕ).choose j' : ℝ) *
            canonicalCrossTerm d N a mass T η (m : ℕ) j'))
        (canonicalJointMeasure d N))
    (h_int_pairs_lead_perCoef : ∀ j ∈ Finset.range P.n,
        ∀ m ∈ (Finset.univ : Finset (Fin P.n)),
        Integrable (fun η =>
            canonicalCrossTerm d N a mass T η P.n j *
            ∑ j' ∈ Finset.range (m : ℕ),
              ((m : ℕ).choose j' : ℝ) *
                canonicalCrossTerm d N a mass T η (m : ℕ) j')
            (canonicalJointMeasure d N))
    (h_int_R_m_pairs : ∀ m ∈ (Finset.univ : Finset (Fin P.n)),
        ∀ m' ∈ (Finset.univ : Finset (Fin P.n)),
        Integrable (fun η =>
            (P.coeff m * ∑ j ∈ Finset.range (m : ℕ),
                ((m : ℕ).choose j : ℝ) *
                  canonicalCrossTerm d N a mass T η (m : ℕ) j) *
            (P.coeff m' * ∑ j' ∈ Finset.range (m' : ℕ),
                ((m' : ℕ).choose j' : ℝ) *
                  canonicalCrossTerm d N a mass T η (m' : ℕ) j'))
            (canonicalJointMeasure d N))
    (h_int_leading_pairs : ∀ j ∈ Finset.range P.n,
        ∀ j' ∈ Finset.range P.n,
        Integrable (fun η =>
            canonicalCrossTerm d N a mass T η P.n j *
            canonicalCrossTerm d N a mass T η P.n j')
            (canonicalJointMeasure d N))
    (h_int_perCoeff_pairs : ∀ m : Fin P.n,
        ∀ j ∈ Finset.range (m : ℕ),
        ∀ j' ∈ Finset.range (m : ℕ),
        Integrable (fun η =>
            canonicalCrossTerm d N a mass T η (m : ℕ) j *
            canonicalCrossTerm d N a mass T η (m : ℕ) j')
            (canonicalJointMeasure d N)) :
    ∫ η, (canonicalRoughError d N a mass T P η) ^ 2
        ∂(canonicalJointMeasure d N) =
    (∑ j ∈ Finset.range P.n,
      ((1 / P.n : ℝ) * (P.n.choose j : ℝ)) ^ 2 *
        ∫ η, (canonicalCrossTerm d N a mass T η P.n j) ^ 2
            ∂(canonicalJointMeasure d N))
    + ∑ m : Fin P.n,
        ∑ j ∈ Finset.range (m : ℕ),
          (P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2 *
            ∫ η, (canonicalCrossTerm d N a mass T η (m : ℕ) j) ^ 2
                ∂(canonicalJointMeasure d N) := by
  -- Step 1: split E_R² into Lead² + PerCoef²
  rw [canonicalRoughError_l2_sq_eq_lead_plus_perCoef_sq d N a mass T P
      h_orth_lead_perCoef h_int_lead_sq h_int_perCoef_sq
      h_int_cross_lead_perCoef h_int_pairs_lead_perCoef]
  -- Step 2: ∫ Lead² → leading sum-of-squares
  rw [canonicalRoughError_leading_l2_sq d N a mass ha hmass T hT P h_int_leading_pairs]
  -- Step 3: ∫ PerCoef² → Σ_m ∫ R_m²
  rw [canonicalRoughError_perCoef_outer_l2_sq d N a mass T P
      h_orth_m_outer h_int_R_m_pairs]
  -- Step 4: For each m, ∫ R_m² → per-m sum-of-squares
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  exact canonicalRoughError_perCoeff_l2_sq d N a mass ha hmass T hT P m (h_int_perCoeff_pairs m)

lemma canonicalCrossTerm_pair_integrable
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (k j k' j' : ℕ) :
    Integrable (fun η =>
        canonicalCrossTerm d N a mass T η k j *
          canonicalCrossTerm d N a mass T η k' j')
      (canonicalJointMeasure d N) := by
  let cS := smoothWickConstant d N a mass T
  let cR := roughWickConstant d N a mass T
  let μS : Measure ((Fin d → Fin N) → ℝ) :=
    Measure.pi (fun _ : Fin d → Fin N => ProbabilityTheory.gaussianReal 0 1)
  let μR : Measure ((Fin d → Fin N) → ℝ) :=
    Measure.pi (fun _ : Fin d → Fin N => ProbabilityTheory.gaussianReal 0 1)
  let term : FinLatticeSites d N → FinLatticeSites d N → CanonicalJoint d N → ℝ :=
    fun x y η =>
      (wickMonomial j cS (canonicalSmoothFieldFunction d N a mass T η x) *
          wickMonomial j' cS (canonicalSmoothFieldFunction d N a mass T η y)) *
        (wickMonomial (k - j) cR (canonicalRoughFieldFunction d N a mass T η x) *
          wickMonomial (k' - j') cR (canonicalRoughFieldFunction d N a mass T η y))
  have h_term_int :
      ∀ x y, Integrable (term x y) (canonicalJointMeasure d N) := by
    intro x y
    rw [canonicalJointMeasure]
    let f : ((Fin d → Fin N) → ℝ) → ℝ := fun η_S =>
      wickMonomial j cS (canonicalSmoothFieldFunctionOfFst d N a mass T η_S x) *
        wickMonomial j' cS (canonicalSmoothFieldFunctionOfFst d N a mass T η_S y)
    let g : ((Fin d → Fin N) → ℝ) → ℝ := fun η_R =>
      wickMonomial (k - j) cR (canonicalRoughFieldFunctionOfSnd d N a mass T η_R x) *
        wickMonomial (k' - j') cR (canonicalRoughFieldFunctionOfSnd d N a mass T η_R y)
    have hf : Integrable f μS := by
      simpa [f, μS, cS] using
        (canonicalSmoothWickPower_two_site_marginal_integrable
          (d := d) (N := N) (a := a) (mass := mass)
          ha hmass T hT j j' x y)
    have hg : Integrable g μR := by
      simpa [g, μR, cR] using
        (canonicalRoughWickPower_two_site_marginal_integrable
          (d := d) (N := N) (a := a) (mass := mass)
          ha hmass T hT (k - j) (k' - j') x y)
    simpa [term, CanonicalJoint, f, g, μS, μR, cS, cR,
      mul_assoc, mul_left_comm, mul_comm] using
      (Integrable.mul_prod (μ := μS) (ν := μR) hf hg)
  have h_expand :
      ∀ η : CanonicalJoint d N,
        canonicalCrossTerm d N a mass T η k j *
            canonicalCrossTerm d N a mass T η k' j' =
          ((a ^ d) * (a ^ d)) * ∑ x : FinLatticeSites d N,
            ∑ y : FinLatticeSites d N, term x y η := by
    intro η
    unfold canonicalCrossTerm term
    rw [show
      (a ^ d * ∑ x,
          wickMonomial j (smoothWickConstant d N a mass T)
              (canonicalSmoothFieldFunction d N a mass T η x) *
            wickMonomial (k - j) (roughWickConstant d N a mass T)
              (canonicalRoughFieldFunction d N a mass T η x)) *
        (a ^ d * ∑ x,
          wickMonomial j' (smoothWickConstant d N a mass T)
              (canonicalSmoothFieldFunction d N a mass T η x) *
            wickMonomial (k' - j') (roughWickConstant d N a mass T)
              (canonicalRoughFieldFunction d N a mass T η x)) =
      ((a ^ d) * (a ^ d)) *
      ((∑ x,
          wickMonomial j (smoothWickConstant d N a mass T)
              (canonicalSmoothFieldFunction d N a mass T η x) *
            wickMonomial (k - j) (roughWickConstant d N a mass T)
              (canonicalRoughFieldFunction d N a mass T η x)) *
        (∑ x,
          wickMonomial j' (smoothWickConstant d N a mass T)
              (canonicalSmoothFieldFunction d N a mass T η x) *
            wickMonomial (k' - j') (roughWickConstant d N a mass T)
              (canonicalRoughFieldFunction d N a mass T η x))) by
      ring]
    rw [Finset.sum_mul_sum]
    simp [cS, cR, mul_assoc, mul_left_comm]
  have h_sum_int :
      Integrable
        (fun η => ((a ^ d) * (a ^ d)) * ∑ x : FinLatticeSites d N,
          ∑ y : FinLatticeSites d N, term x y η)
        (canonicalJointMeasure d N) := by
    refine (MeasureTheory.integrable_finset_sum _ fun x _ =>
      MeasureTheory.integrable_finset_sum _ fun y _ =>
        h_term_int x y).const_mul _
  refine h_sum_int.congr ?_
  filter_upwards with η
  exact (h_expand η).symm

lemma canonicalCrossTerm_l2_sq_eq_covSum
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (k j : ℕ) :
    ∫ η, (canonicalCrossTerm d N a mass T η k j) ^ 2
        ∂(canonicalJointMeasure d N) =
      ((a ^ d) * (a ^ d)) * ((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
        ∑ x : FinLatticeSites d N,
          ∑ y : FinLatticeSites d N,
            canonicalSmoothCovariance d N a mass T x y ^ j *
              canonicalRoughCovariance d N a mass T x y ^ (k - j) := by
  let cS := smoothWickConstant d N a mass T
  let cR := roughWickConstant d N a mass T
  let μS : Measure ((Fin d → Fin N) → ℝ) :=
    Measure.pi (fun _ : Fin d → Fin N => ProbabilityTheory.gaussianReal 0 1)
  let μR : Measure ((Fin d → Fin N) → ℝ) :=
    Measure.pi (fun _ : Fin d → Fin N => ProbabilityTheory.gaussianReal 0 1)
  let term : FinLatticeSites d N → FinLatticeSites d N → CanonicalJoint d N → ℝ :=
    fun x y η =>
      (wickMonomial j cS (canonicalSmoothFieldFunction d N a mass T η x) *
          wickMonomial j cS (canonicalSmoothFieldFunction d N a mass T η y)) *
        (wickMonomial (k - j) cR (canonicalRoughFieldFunction d N a mass T η x) *
          wickMonomial (k - j) cR (canonicalRoughFieldFunction d N a mass T η y))
  have h_term_int :
      ∀ x y, Integrable (term x y) (canonicalJointMeasure d N) := by
    intro x y
    rw [canonicalJointMeasure]
    let f : ((Fin d → Fin N) → ℝ) → ℝ := fun η_S =>
      wickMonomial j cS (canonicalSmoothFieldFunctionOfFst d N a mass T η_S x) *
        wickMonomial j cS (canonicalSmoothFieldFunctionOfFst d N a mass T η_S y)
    let g : ((Fin d → Fin N) → ℝ) → ℝ := fun η_R =>
      wickMonomial (k - j) cR (canonicalRoughFieldFunctionOfSnd d N a mass T η_R x) *
        wickMonomial (k - j) cR (canonicalRoughFieldFunctionOfSnd d N a mass T η_R y)
    have hf : Integrable f μS := by
      simpa [f, μS, cS] using
        (canonicalSmoothWickPower_two_site_marginal_integrable
          (d := d) (N := N) (a := a) (mass := mass)
          ha hmass T hT j j x y)
    have hg : Integrable g μR := by
      simpa [g, μR, cR] using
        (canonicalRoughWickPower_two_site_marginal_integrable
          (d := d) (N := N) (a := a) (mass := mass)
          ha hmass T hT (k - j) (k - j) x y)
    simpa [term, CanonicalJoint, f, g, μS, μR, cS, cR,
      mul_assoc, mul_left_comm, mul_comm] using
      (Integrable.mul_prod (μ := μS) (ν := μR) hf hg)
  have h_expand :
      ∀ η : CanonicalJoint d N,
        (canonicalCrossTerm d N a mass T η k j) ^ 2 =
          ((a ^ d) * (a ^ d)) * ∑ x : FinLatticeSites d N,
            ∑ y : FinLatticeSites d N, term x y η := by
    intro η
    rw [sq]
    unfold canonicalCrossTerm term
    rw [show
      (a ^ d * ∑ x,
          wickMonomial j (smoothWickConstant d N a mass T)
              (canonicalSmoothFieldFunction d N a mass T η x) *
            wickMonomial (k - j) (roughWickConstant d N a mass T)
              (canonicalRoughFieldFunction d N a mass T η x)) *
        (a ^ d * ∑ x,
          wickMonomial j (smoothWickConstant d N a mass T)
              (canonicalSmoothFieldFunction d N a mass T η x) *
            wickMonomial (k - j) (roughWickConstant d N a mass T)
              (canonicalRoughFieldFunction d N a mass T η x)) =
      ((a ^ d) * (a ^ d)) *
      ((∑ x,
          wickMonomial j (smoothWickConstant d N a mass T)
              (canonicalSmoothFieldFunction d N a mass T η x) *
            wickMonomial (k - j) (roughWickConstant d N a mass T)
              (canonicalRoughFieldFunction d N a mass T η x)) *
        (∑ x,
          wickMonomial j (smoothWickConstant d N a mass T)
              (canonicalSmoothFieldFunction d N a mass T η x) *
            wickMonomial (k - j) (roughWickConstant d N a mass T)
              (canonicalRoughFieldFunction d N a mass T η x))) by
      ring]
    rw [Finset.sum_mul_sum]
    simp [cS, cR, mul_assoc, mul_left_comm]
  simp_rw [h_expand]
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_finset_sum _ (fun x _ =>
    MeasureTheory.integrable_finset_sum _ (fun y _ => h_term_int x y))]
  have hxy :
      ∀ x y,
        ∫ η, term x y η ∂(canonicalJointMeasure d N) =
          ((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
            (canonicalSmoothCovariance d N a mass T x y ^ j *
              canonicalRoughCovariance d N a mass T x y ^ (k - j)) := by
    intro x y
    have h_factor :
        ∫ η, term x y η ∂(canonicalJointMeasure d N) =
          (∫ η_S, wickMonomial j cS (canonicalSmoothFieldFunctionOfFst d N a mass T η_S x) *
              wickMonomial j cS (canonicalSmoothFieldFunctionOfFst d N a mass T η_S y) ∂μS) *
          (∫ η_R,
              wickMonomial (k - j) cR
                (canonicalRoughFieldFunctionOfSnd d N a mass T η_R x) *
              wickMonomial (k - j) cR
                (canonicalRoughFieldFunctionOfSnd d N a mass T η_R y) ∂μR) := by
      rw [canonicalJointMeasure]
      simpa [term, CanonicalJoint, μS, μR, cS, cR,
        mul_assoc, mul_left_comm, mul_comm] using
        (integral_prod_mul
          (μ := μS) (ν := μR)
          (f := fun η_S =>
            wickMonomial j cS (canonicalSmoothFieldFunctionOfFst d N a mass T η_S x) *
              wickMonomial j cS (canonicalSmoothFieldFunctionOfFst d N a mass T η_S y))
          (g := fun η_R =>
            wickMonomial (k - j) cR (canonicalRoughFieldFunctionOfSnd d N a mass T η_R x) *
              wickMonomial (k - j) cR (canonicalRoughFieldFunctionOfSnd d N a mass T η_R y)))
    rw [h_factor]
    rw [canonicalSmoothWickPower_two_site_marginal_eq_diag
      (d := d) (N := N) (a := a) (mass := mass)
      ha hmass T hT j x y]
    rw [canonicalRoughWickPower_two_site_marginal_eq_diag
      (d := d) (N := N) (a := a) (mass := mass)
      ha hmass T hT (k - j) x y]
    ring
  calc
    ((a ^ d) * (a ^ d)) *
        ∑ x : FinLatticeSites d N,
          ∫ η, ∑ y : FinLatticeSites d N, term x y η ∂(canonicalJointMeasure d N)
      = ((a ^ d) * (a ^ d)) *
          ∑ x : FinLatticeSites d N,
            ∑ y : FinLatticeSites d N,
              ∫ η, term x y η ∂(canonicalJointMeasure d N) := by
                congr 1
                refine Finset.sum_congr rfl ?_
                intro x hx
                rw [MeasureTheory.integral_finset_sum _ (fun y _ => h_term_int x y)]
    _ = ((a ^ d) * (a ^ d)) *
          ∑ x : FinLatticeSites d N,
            ∑ y : FinLatticeSites d N,
              (((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
                (canonicalSmoothCovariance d N a mass T x y ^ j *
                  canonicalRoughCovariance d N a mass T x y ^ (k - j))) := by
                    congr 1
                    refine Finset.sum_congr rfl ?_
                    intro x hx
                    refine Finset.sum_congr rfl ?_
                    intro y hy
                    rw [hxy x y]
    _ = ((a ^ d) * (a ^ d)) *
          (((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
            ∑ x : FinLatticeSites d N,
              ∑ y : FinLatticeSites d N,
                (canonicalSmoothCovariance d N a mass T x y ^ j *
                  canonicalRoughCovariance d N a mass T x y ^ (k - j))) := by
                    have hfactor :
                        ∑ x : FinLatticeSites d N,
                          ∑ y : FinLatticeSites d N,
                            ((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
                              (canonicalSmoothCovariance d N a mass T x y ^ j *
                                canonicalRoughCovariance d N a mass T x y ^ (k - j)) =
                          ((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
                          ∑ x : FinLatticeSites d N,
                            ∑ y : FinLatticeSites d N,
                              (canonicalSmoothCovariance d N a mass T x y ^ j *
                                canonicalRoughCovariance d N a mass T x y ^ (k - j)) := by
                          simp [Finset.mul_sum, mul_assoc, mul_comm]
                    rw [hfactor]
    _ = ((a ^ d) * (a ^ d)) * ((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
          ∑ x : FinLatticeSites d N,
            ∑ y : FinLatticeSites d N,
              (canonicalSmoothCovariance d N a mass T x y ^ j *
                canonicalRoughCovariance d N a mass T x y ^ (k - j)) := by
                  ring

/-! ## S4: per-cross-term L² bound

For each `(k, j)` with rough-degree `k - j ≥ 1` (so the cross-term has
at least one rough-field factor) and `k ≤ P.n`, the L² norm squared
of `canonicalCrossTerm η k j` is bounded by `K · T · (1 + |log T|)^j`
uniformly in `(a, N)` at fixed `(L, mass)`.

**Proof path** (deferred): apply the diagonal 2-site Wick formulas
(smooth and rough) inside `MeasureTheory.integral_prod_mul` to get
  `‖cross(k, j)‖²_L² = (a^d)² · Σ_{x,y} (j! · C_S(x,y)^j) · ((k-j)! · C_R(x,y)^{k-j})`
then apply the upstream `(a, N)`-uniform Glimm-Jaffe bounds:
* `canonicalSmoothCovariance_le_log` on `‖C_S‖_∞ ≤ A + B|log T|`
* `canonicalRoughCovariance_pow_sum_le` on `a^d Σ_y C_R(x,y)^m ≤ C_m · T`
and finite (size-`L^d`) volume sums on x.

Net bound `O(T · (1+|log T|)^j)` uniformly in `(a, N)`. -/

/-- **S4 (sorry'd): per-cross-term L² bound.** For `(k, j)` with
`1 ≤ k - j` (rough degree at least one) and `k ≤ P.n`, there exists
a constant `K` (uniform in `(a, N)` at fixed `(L, mass)`) bounding
`∫ canonicalCrossTerm² dμ_joint ≤ K · T · (1 + |log T|)^j`.

Depends on:
* the canonical-side diagonal 2-site Wick power formula, and
* the upstream `(a, N)`-uniform Glimm-Jaffe Fourier estimates
  (`canonicalSmoothCovariance_le_log`, `canonicalRoughCovariance_pow_sum_le`).

See module docstring above for the full proof sketch. -/
theorem canonicalCrossTerm_l2_sq_le
    {d : ℕ} (_hd : d = 2) (mass L : ℝ) (_hL : 0 < L) (_hmass : 0 < mass)
    (k j : ℕ) (_hkj : 1 ≤ k - j) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a)
        (_h_vol : (N : ℝ) * a = L)
        (T : ℝ) (_hT : 0 < T),
        ∫ η, (canonicalCrossTerm d N a mass T η k j) ^ 2
            ∂(canonicalJointMeasure d N) ≤
        K * T * (1 + |Real.log T|) ^ j := by
  subst _hd
  rcases smoothWickConstant_le_log_uniform_in_aN
      (d := 2) rfl mass L _hL _hmass with
    ⟨A, B, hA, hB, h_smooth_uniform⟩
  rcases canonicalRoughCovariance_pow_sum_le_uniform_in_aN
      (d := 2) rfl mass L _hL _hmass (k - j) _hkj with
    ⟨C, hC_pos, h_rough_uniform⟩
  let K : ℝ := ((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
    (L ^ 2) * (A + B + 1) ^ j * C
  refine ⟨K, ?_, ?_⟩
  · have hfacj : 0 < (j.factorial : ℝ) := by positivity
    have hfacr : 0 < (((k - j).factorial : ℝ)) := by positivity
    have hL2 : 0 < L ^ 2 := by positivity
    have hAB1 : 0 < A + B + 1 := by linarith
    have hpow : 0 < (A + B + 1) ^ j := pow_pos hAB1 j
    dsimp [K]
    positivity
  · intro N _ a ha h_vol T hT
    have ha2_nonneg : 0 ≤ a ^ 2 := sq_nonneg a
    have hfac_nonneg : 0 ≤ (j.factorial : ℝ) * ((k - j).factorial : ℝ) := by positivity
    have h_card_nat : Fintype.card (FinLatticeSites 2 N) = N ^ 2 := by
      simp only [FinLatticeSites, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    have h_card :
        (Fintype.card (FinLatticeSites 2 N) : ℝ) = (N : ℝ) ^ 2 := by
      rw [h_card_nat]
      norm_num
    have h_vol_sq :
        a ^ 2 * (Fintype.card (FinLatticeSites 2 N) : ℝ) = L ^ 2 := by
      rw [h_card]
      calc
        a ^ 2 * (N : ℝ) ^ 2 = ((N : ℝ) * a) ^ 2 := by ring
        _ = L ^ 2 := by rw [h_vol]
    have hsmooth_nonneg : 0 ≤ smoothWickConstant 2 N a mass T := by
      unfold smoothWickConstant
      have ha2_pos : 0 < a ^ 2 := pow_pos ha 2
      have hsum_nonneg :
          0 ≤ ∑ m ∈ Finset.range (Fintype.card (FinLatticeSites 2 N)),
            smoothCovEigenvalue 2 N a mass T m := by
        refine Finset.sum_nonneg fun m hm => ?_
        unfold smoothCovEigenvalue
        apply div_nonneg
        · positivity
        · exact le_of_lt (latticeEigenvalue_pos 2 N a mass ha _hmass m)
      apply mul_nonneg (le_of_lt (inv_pos.mpr ha2_pos))
      apply mul_nonneg
      · positivity
      · exact hsum_nonneg
    have h_log_nonneg : 0 ≤ 1 + |Real.log T| := by
      positivity
    have h_log_one : 1 ≤ 1 + |Real.log T| := by
      linarith [abs_nonneg (Real.log T)]
    have h_smooth_linear :
        smoothWickConstant 2 N a mass T ≤
          (A + B + 1) * (1 + |Real.log T|) := by
      have hbase := h_smooth_uniform N a ha h_vol T hT
      calc
        smoothWickConstant 2 N a mass T ≤ A + B * (1 + |Real.log T|) := hbase
        _ ≤ (A + B) * (1 + |Real.log T|) := by
          nlinarith [hA, hB, h_log_nonneg]
        _ ≤ (A + B + 1) * (1 + |Real.log T|) := by
          nlinarith [h_log_nonneg]
    have h_smooth_pow :
        smoothWickConstant 2 N a mass T ^ j ≤
          (A + B + 1) ^ j * (1 + |Real.log T|) ^ j := by
      calc
        smoothWickConstant 2 N a mass T ^ j ≤
            ((A + B + 1) * (1 + |Real.log T|)) ^ j :=
          pow_le_pow_left₀ hsmooth_nonneg h_smooth_linear j
        _ = (A + B + 1) ^ j * (1 + |Real.log T|) ^ j := by
          rw [mul_pow]
    have h_abs_sum :
        ∑ x : FinLatticeSites 2 N,
          ∑ y : FinLatticeSites 2 N,
            canonicalSmoothCovariance 2 N a mass T x y ^ j *
              canonicalRoughCovariance 2 N a mass T x y ^ (k - j)
        ≤
        ∑ x : FinLatticeSites 2 N,
          ∑ y : FinLatticeSites 2 N,
            |canonicalSmoothCovariance 2 N a mass T x y| ^ j *
              |canonicalRoughCovariance 2 N a mass T x y| ^ (k - j) := by
      refine Finset.sum_le_sum ?_
      intro x hx
      refine Finset.sum_le_sum ?_
      intro y hy
      simpa [abs_mul, abs_pow] using
        (le_abs_self
          (canonicalSmoothCovariance 2 N a mass T x y ^ j *
            canonicalRoughCovariance 2 N a mass T x y ^ (k - j)))
    have h_summand_bound :
        ∀ x y : FinLatticeSites 2 N,
          |canonicalSmoothCovariance 2 N a mass T x y| ^ j *
              |canonicalRoughCovariance 2 N a mass T x y| ^ (k - j)
            ≤
          smoothWickConstant 2 N a mass T ^ j *
            |canonicalRoughCovariance 2 N a mass T x y| ^ (k - j) := by
      intro x y
      have hxy :=
        abs_canonicalSmoothCovariance_le_smoothWickConstant
          (d := 2) (N := N) (a := a) (mass := mass) ha _hmass T hT x y
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg _) hxy j)
        (pow_nonneg (abs_nonneg _) _)
    have h_sum_bound :
        ∑ x : FinLatticeSites 2 N,
          ∑ y : FinLatticeSites 2 N,
            |canonicalSmoothCovariance 2 N a mass T x y| ^ j *
              |canonicalRoughCovariance 2 N a mass T x y| ^ (k - j)
        ≤
        smoothWickConstant 2 N a mass T ^ j *
          ∑ x : FinLatticeSites 2 N,
            ∑ y : FinLatticeSites 2 N,
              |canonicalRoughCovariance 2 N a mass T x y| ^ (k - j) := by
      calc
        ∑ x : FinLatticeSites 2 N,
            ∑ y : FinLatticeSites 2 N,
              |canonicalSmoothCovariance 2 N a mass T x y| ^ j *
                |canonicalRoughCovariance 2 N a mass T x y| ^ (k - j)
          ≤
            ∑ x : FinLatticeSites 2 N,
              ∑ y : FinLatticeSites 2 N,
                (smoothWickConstant 2 N a mass T ^ j *
                  |canonicalRoughCovariance 2 N a mass T x y| ^ (k - j)) := by
              refine Finset.sum_le_sum ?_
              intro x hx
              refine Finset.sum_le_sum ?_
              intro y hy
              exact h_summand_bound x y
        _ = smoothWickConstant 2 N a mass T ^ j *
              ∑ x : FinLatticeSites 2 N,
                ∑ y : FinLatticeSites 2 N,
                  |canonicalRoughCovariance 2 N a mass T x y| ^ (k - j) := by
              simp [Finset.mul_sum, mul_comm]
    have h_rough_sum :
        a ^ 2 *
          ∑ x : FinLatticeSites 2 N,
            (a ^ 2 *
              ∑ y : FinLatticeSites 2 N,
                |canonicalRoughCovariance 2 N a mass T x y| ^ (k - j))
        ≤
        L ^ 2 * (C * T) := by
      have h_inner :
          ∑ x : FinLatticeSites 2 N,
            (a ^ 2 *
              ∑ y : FinLatticeSites 2 N,
                |canonicalRoughCovariance 2 N a mass T x y| ^ (k - j))
          ≤
          ∑ x : FinLatticeSites 2 N, C * T := by
        refine Finset.sum_le_sum ?_
        intro x hx
        exact h_rough_uniform N a ha h_vol T hT x
      calc
        a ^ 2 *
            ∑ x : FinLatticeSites 2 N,
              (a ^ 2 *
                ∑ y : FinLatticeSites 2 N,
                  |canonicalRoughCovariance 2 N a mass T x y| ^ (k - j))
          ≤
            a ^ 2 * ∑ x : FinLatticeSites 2 N, C * T :=
              mul_le_mul_of_nonneg_left h_inner ha2_nonneg
        _ = (a ^ 2 * (Fintype.card (FinLatticeSites 2 N) : ℝ)) * (C * T) := by
              simp [mul_assoc, mul_left_comm, mul_comm]
        _ = L ^ 2 * (C * T) := by rw [h_vol_sq]
    calc
      ∫ η, (canonicalCrossTerm 2 N a mass T η k j) ^ 2
          ∂(canonicalJointMeasure 2 N)
        = ((a ^ 2) * (a ^ 2)) * ((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
            ∑ x : FinLatticeSites 2 N,
              ∑ y : FinLatticeSites 2 N,
                canonicalSmoothCovariance 2 N a mass T x y ^ j *
                  canonicalRoughCovariance 2 N a mass T x y ^ (k - j) := by
            simpa using
              canonicalCrossTerm_l2_sq_eq_covSum
                (d := 2) (N := N) (a := a) (mass := mass) ha _hmass T hT k j
      _ ≤ ((a ^ 2) * (a ^ 2)) * ((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
            ∑ x : FinLatticeSites 2 N,
              ∑ y : FinLatticeSites 2 N,
                (|canonicalSmoothCovariance 2 N a mass T x y| ^ j *
                  |canonicalRoughCovariance 2 N a mass T x y| ^ (k - j)) := by
            gcongr
      _ ≤ ((a ^ 2) * (a ^ 2)) * ((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
            (smoothWickConstant 2 N a mass T ^ j *
              ∑ x : FinLatticeSites 2 N,
                ∑ y : FinLatticeSites 2 N,
                  |canonicalRoughCovariance 2 N a mass T x y| ^ (k - j)) := by
            gcongr
      _ = ((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
            (smoothWickConstant 2 N a mass T ^ j) *
            (a ^ 2 *
              ∑ x : FinLatticeSites 2 N,
                (a ^ 2 *
                  ∑ y : FinLatticeSites 2 N,
                    |canonicalRoughCovariance 2 N a mass T x y| ^ (k - j))) := by
            simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      _ ≤ ((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
            (smoothWickConstant 2 N a mass T ^ j) *
            (L ^ 2 * (C * T)) := by
            gcongr
      _ ≤ ((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
            ((A + B + 1) ^ j * (1 + |Real.log T|) ^ j) *
            (L ^ 2 * (C * T)) := by
            gcongr
      _ = K * T * (1 + |Real.log T|) ^ j := by
            dsimp [K]
            ring

/-! ## Main theorem (statement, proof TBD)

`rough_error_variance` quantifies `K` outside the lattice binders so it
cannot depend on `(a, N)` and break continuum-limit uniformity. The
constraint `(N : ℝ) * a = L` pins the macroscopic period. The polylog
exponent `P.n − 1` is the maximum power of `‖C_S‖_∞ ≤ 1 + |log T|` that
appears in any cross-term (since `m ≥ 1` forces `j ≤ P.n − 1`).
-/

/-- **L² bound on the rough-field error** of a Wick-polynomial interaction.

For any `InteractionPolynomial P` and macroscopic period `L > 0`, there
exists a constant `K(P, mass, L) > 0` such that for every lattice
discretization `(N, a)` with `(N : ℝ) * a = L`,

  `∫ η, (canonicalRoughError d N a mass T P η)² ∂(canonicalJointMeasure d N)
    ≤ K · T · (1 + |log T|)^{P.n − 1}`.

The bound is uniform in `(a, N)` at fixed `(L, mass, P)`. The polylog
factor comes from the smooth covariance `‖C_S‖_∞ ≤ A + B · |log T|`;
the linear `T` factor comes from the rough covariance L^m summability.

This is **Step 1** of the discharge of `polynomial_chaos_exp_moment_bridge`
(`PolynomialChaosBridge.lean:116`). Phase 2 feeds this into
`polynomial_chaos_concentration` (Janson 5.10) for L^p and tail bounds.

See `docs/rough-error-variance-plan.md` for the full proof plan. -/
theorem rough_error_variance
    {d : ℕ} (_hd : d = 2) (P : InteractionPolynomial)
    (L mass : ℝ) (_hL : 0 < L) (_hmass : 0 < mass) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a)
        (_h_vol : (N : ℝ) * a = L)
        (T : ℝ) (_hT : 0 < T),
        ∫ η, (canonicalRoughError d N a mass T P η) ^ 2
          ∂(canonicalJointMeasure d N) ≤
        K * T * (1 + |Real.log T|) ^ (P.n - 1) := by
  subst _hd
  classical
  let KLeadFun : ℕ → ℝ := fun j =>
    if hj : j ∈ Finset.range P.n then
      Classical.choose
        (canonicalCrossTerm_l2_sq_le
          (d := 2) rfl mass L _hL _hmass P.n j
          (Nat.succ_le_of_lt (Nat.sub_pos_of_lt (Finset.mem_range.mp hj))))
    else 1
  let KPerFun : Fin P.n → ℕ → ℝ := fun m j =>
    if hj : j ∈ Finset.range (m : ℕ) then
      Classical.choose
        (canonicalCrossTerm_l2_sq_le
          (d := 2) rfl mass L _hL _hmass (m : ℕ) j
          (Nat.succ_le_of_lt (Nat.sub_pos_of_lt (Finset.mem_range.mp hj))))
    else 1
  let KLeadSum : ℝ :=
    ∑ j ∈ Finset.range P.n,
      (((1 / P.n : ℝ) * (P.n.choose j : ℝ)) ^ 2) * KLeadFun j
  let KPerSum : ℝ :=
    ∑ m : Fin P.n,
      ∑ j ∈ Finset.range (m : ℕ),
        ((P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2) * KPerFun m j
  let K0 : ℝ := KLeadSum + KPerSum
  let K : ℝ := K0 + 1
  have hKLead_pos : ∀ j (hj : j ∈ Finset.range P.n), 0 < KLeadFun j := by
    intro j hj
    dsimp [KLeadFun]
    rw [dif_pos hj]
    exact
      (Classical.choose_spec
        (canonicalCrossTerm_l2_sq_le
          (d := 2) rfl mass L _hL _hmass P.n j
          (Nat.succ_le_of_lt (Nat.sub_pos_of_lt (Finset.mem_range.mp hj))))).1
  have hKLead_bound :
      ∀ j (hj : j ∈ Finset.range P.n),
        ∀ (N : ℕ) [NeZero N] (a : ℝ), 0 < a → (N : ℝ) * a = L →
          ∀ (T : ℝ), 0 < T →
            ∫ η, (canonicalCrossTerm 2 N a mass T η P.n j) ^ 2
              ∂(canonicalJointMeasure 2 N) ≤
            KLeadFun j * T * (1 + |Real.log T|) ^ j := by
    intro j hj N _ a ha h_vol T hT
    dsimp [KLeadFun]
    rw [dif_pos hj]
    exact
      (Classical.choose_spec
        (canonicalCrossTerm_l2_sq_le
          (d := 2) rfl mass L _hL _hmass P.n j
          (Nat.succ_le_of_lt (Nat.sub_pos_of_lt (Finset.mem_range.mp hj))))).2 N a ha h_vol T hT
  have hKPer_pos :
      ∀ (m : Fin P.n) (j : ℕ) (hj : j ∈ Finset.range (m : ℕ)), 0 < KPerFun m j := by
    intro m j hj
    dsimp [KPerFun]
    rw [dif_pos hj]
    exact
      (Classical.choose_spec
        (canonicalCrossTerm_l2_sq_le
          (d := 2) rfl mass L _hL _hmass (m : ℕ) j
          (Nat.succ_le_of_lt (Nat.sub_pos_of_lt (Finset.mem_range.mp hj))))).1
  have hKPer_bound :
      ∀ (m : Fin P.n) (j : ℕ) (hj : j ∈ Finset.range (m : ℕ)),
        ∀ (N : ℕ) [NeZero N] (a : ℝ), 0 < a → (N : ℝ) * a = L →
          ∀ (T : ℝ), 0 < T →
            ∫ η, (canonicalCrossTerm 2 N a mass T η (m : ℕ) j) ^ 2
              ∂(canonicalJointMeasure 2 N) ≤
            KPerFun m j * T * (1 + |Real.log T|) ^ j := by
    intro m j hj N _ a ha h_vol T hT
    dsimp [KPerFun]
    rw [dif_pos hj]
    exact
      (Classical.choose_spec
        (canonicalCrossTerm_l2_sq_le
          (d := 2) rfl mass L _hL _hmass (m : ℕ) j
          (Nat.succ_le_of_lt (Nat.sub_pos_of_lt (Finset.mem_range.mp hj))))).2 N a ha h_vol T hT
  refine ⟨K, by
    have hLead_nonneg : 0 ≤ KLeadSum := by
      dsimp [KLeadSum]
      refine Finset.sum_nonneg fun j hj => ?_
      exact mul_nonneg (sq_nonneg _) (le_of_lt (hKLead_pos j hj))
    have hPer_nonneg : 0 ≤ KPerSum := by
      dsimp [KPerSum]
      refine Finset.sum_nonneg fun m hm => ?_
      refine Finset.sum_nonneg fun j hj => ?_
      exact mul_nonneg (sq_nonneg _) (le_of_lt (hKPer_pos m j hj))
    dsimp [K, K0]
    linarith, ?_⟩
  intro N _ a ha h_vol T hT
  let u : ℝ := 1 + |Real.log T|
  have hu_one : 1 ≤ u := by
    dsimp [u]
    linarith [abs_nonneg (Real.log T)]
  have hu_nonneg : 0 ≤ u := by
    linarith
  have h_common_nonneg : 0 ≤ T * u ^ (P.n - 1) := by
    positivity
  have h_int_leading_pairs :
      ∀ j ∈ Finset.range P.n,
        ∀ j' ∈ Finset.range P.n,
        Integrable (fun η =>
            canonicalCrossTerm 2 N a mass T η P.n j *
            canonicalCrossTerm 2 N a mass T η P.n j')
          (canonicalJointMeasure 2 N) := by
    intro j hj j' hj'
    exact canonicalCrossTerm_pair_integrable 2 N a mass ha _hmass T hT P.n j P.n j'
  have h_int_perCoeff_pairs :
      ∀ m : Fin P.n,
        ∀ j ∈ Finset.range (m : ℕ),
        ∀ j' ∈ Finset.range (m : ℕ),
        Integrable (fun η =>
            canonicalCrossTerm 2 N a mass T η (m : ℕ) j *
            canonicalCrossTerm 2 N a mass T η (m : ℕ) j')
          (canonicalJointMeasure 2 N) := by
    intro m j hj j' hj'
    exact canonicalCrossTerm_pair_integrable 2 N a mass ha _hmass T hT (m : ℕ) j (m : ℕ) j'
  have h_int_pairs_lead_perCoef :
      ∀ j ∈ Finset.range P.n,
        ∀ m ∈ (Finset.univ : Finset (Fin P.n)),
        Integrable (fun η =>
            canonicalCrossTerm 2 N a mass T η P.n j *
            ∑ j' ∈ Finset.range (m : ℕ),
              ((m : ℕ).choose j' : ℝ) *
                canonicalCrossTerm 2 N a mass T η (m : ℕ) j')
          (canonicalJointMeasure 2 N) := by
    intro j hj m hm
    simpa using
      (integrable_sum_mul_sum_of_pairwise
        (μ := canonicalJointMeasure 2 N)
        ({j} : Finset ℕ) (Finset.range (m : ℕ))
        (fun _ => (1 : ℝ))
        (fun j' => ((m : ℕ).choose j' : ℝ))
        (fun _ η => canonicalCrossTerm 2 N a mass T η P.n j)
        (fun j' η => canonicalCrossTerm 2 N a mass T η (m : ℕ) j')
        (by
          intro i hi i' hi'
          exact canonicalCrossTerm_pair_integrable
            2 N a mass ha _hmass T hT P.n j (m : ℕ) i'))
  have h_orth_lead_perCoef :
      ∀ j ∈ Finset.range P.n,
        ∀ m ∈ (Finset.univ : Finset (Fin P.n)),
        ∫ η, canonicalCrossTerm 2 N a mass T η P.n j *
              ∑ j' ∈ Finset.range (m : ℕ),
                ((m : ℕ).choose j' : ℝ) *
                  canonicalCrossTerm 2 N a mass T η (m : ℕ) j'
              ∂(canonicalJointMeasure 2 N) = 0 := by
    intro j hj m hm
    simpa using
      (integral_sum_mul_sum_eq_zero_of_orth
        (μ := canonicalJointMeasure 2 N)
        ({j} : Finset ℕ) (Finset.range (m : ℕ))
        (fun _ => (1 : ℝ))
        (fun j' => ((m : ℕ).choose j' : ℝ))
        (fun _ η => canonicalCrossTerm 2 N a mass T η P.n j)
        (fun j' η => canonicalCrossTerm 2 N a mass T η (m : ℕ) j')
        (by
          intro i hi i' hi'
          have hi_eq : i = j := by simpa using hi
          subst i
          refine canonicalCrossTerm_inner_eq_zero
            2 N a mass ha _hmass T hT P.n j (m : ℕ) i' hj hi' ?_
          intro hpair
          exact (Nat.ne_of_lt m.2) ((congrArg Prod.fst hpair).symm))
        (by
          intro i hi i' hi'
          exact canonicalCrossTerm_pair_integrable
            2 N a mass ha _hmass T hT P.n j (m : ℕ) i'))
  have h_int_R_m_pairs :
      ∀ m ∈ (Finset.univ : Finset (Fin P.n)),
        ∀ m' ∈ (Finset.univ : Finset (Fin P.n)),
        Integrable (fun η =>
            (P.coeff m * ∑ j ∈ Finset.range (m : ℕ),
                ((m : ℕ).choose j : ℝ) *
                  canonicalCrossTerm 2 N a mass T η (m : ℕ) j) *
            (P.coeff m' * ∑ j' ∈ Finset.range (m' : ℕ),
                ((m' : ℕ).choose j' : ℝ) *
                  canonicalCrossTerm 2 N a mass T η (m' : ℕ) j'))
          (canonicalJointMeasure 2 N) := by
    intro m hm m' hm'
    simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
      (integrable_sum_mul_sum_of_pairwise
        (μ := canonicalJointMeasure 2 N)
        (Finset.range (m : ℕ)) (Finset.range (m' : ℕ))
        (fun j => P.coeff m * ((m : ℕ).choose j : ℝ))
        (fun j' => P.coeff m' * ((m' : ℕ).choose j' : ℝ))
        (fun j η => canonicalCrossTerm 2 N a mass T η (m : ℕ) j)
        (fun j' η => canonicalCrossTerm 2 N a mass T η (m' : ℕ) j')
        (by
          intro j hj j' hj'
          exact canonicalCrossTerm_pair_integrable
            2 N a mass ha _hmass T hT (m : ℕ) j (m' : ℕ) j'))
  have h_orth_m_outer :
      ∀ m ∈ (Finset.univ : Finset (Fin P.n)),
        ∀ m' ∈ (Finset.univ : Finset (Fin P.n)),
        m ≠ m' →
        ∫ η, (P.coeff m * ∑ j ∈ Finset.range (m : ℕ),
                ((m : ℕ).choose j : ℝ) *
                  canonicalCrossTerm 2 N a mass T η (m : ℕ) j) *
              (P.coeff m' * ∑ j' ∈ Finset.range (m' : ℕ),
                ((m' : ℕ).choose j' : ℝ) *
                  canonicalCrossTerm 2 N a mass T η (m' : ℕ) j')
              ∂(canonicalJointMeasure 2 N) = 0 := by
    intro m hm m' hm' hmm'
    simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
      (integral_sum_mul_sum_eq_zero_of_orth
        (μ := canonicalJointMeasure 2 N)
        (Finset.range (m : ℕ)) (Finset.range (m' : ℕ))
        (fun j => P.coeff m * ((m : ℕ).choose j : ℝ))
        (fun j' => P.coeff m' * ((m' : ℕ).choose j' : ℝ))
        (fun j η => canonicalCrossTerm 2 N a mass T η (m : ℕ) j)
        (fun j' η => canonicalCrossTerm 2 N a mass T η (m' : ℕ) j')
        (by
          intro j hj j' hj'
          refine canonicalCrossTerm_inner_eq_zero
            2 N a mass ha _hmass T hT (m : ℕ) j (m' : ℕ) j' hj hj' ?_
          intro hpair
          exact hmm' (Fin.ext (congrArg Prod.fst hpair)))
        (by
          intro j hj j' hj'
          exact canonicalCrossTerm_pair_integrable
            2 N a mass ha _hmass T hT (m : ℕ) j (m' : ℕ) j'))
  have h_int_lead_sq :
      Integrable (fun η =>
        ((1 / P.n : ℝ) * ∑ j ∈ Finset.range P.n,
          (P.n.choose j : ℝ) * canonicalCrossTerm 2 N a mass T η P.n j) ^ 2)
        (canonicalJointMeasure 2 N) := by
    simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
      (integrable_sq_real_sum_of_pairwise
        (μ := canonicalJointMeasure 2 N)
        (Finset.range P.n)
        (fun j η => canonicalCrossTerm 2 N a mass T η P.n j)
        (fun j => (1 / P.n : ℝ) * (P.n.choose j : ℝ))
        h_int_leading_pairs)
  have h_int_perCoef_sq :
      Integrable (fun η =>
        (∑ m : Fin P.n, P.coeff m * ∑ j' ∈ Finset.range (m : ℕ),
          ((m : ℕ).choose j' : ℝ) *
            canonicalCrossTerm 2 N a mass T η (m : ℕ) j') ^ 2)
        (canonicalJointMeasure 2 N) := by
    simpa using
      (integrable_sq_real_sum_of_pairwise
        (μ := canonicalJointMeasure 2 N)
        (Finset.univ : Finset (Fin P.n))
        (fun m η => P.coeff m * ∑ j' ∈ Finset.range (m : ℕ),
          ((m : ℕ).choose j' : ℝ) *
            canonicalCrossTerm 2 N a mass T η (m : ℕ) j')
        (fun _ => (1 : ℝ))
        h_int_R_m_pairs)
  have h_int_cross_lead_perCoef :
      Integrable (fun η =>
        ((1 / P.n : ℝ) * ∑ j ∈ Finset.range P.n,
          (P.n.choose j : ℝ) * canonicalCrossTerm 2 N a mass T η P.n j) *
        (∑ m : Fin P.n, P.coeff m * ∑ j' ∈ Finset.range (m : ℕ),
          ((m : ℕ).choose j' : ℝ) *
            canonicalCrossTerm 2 N a mass T η (m : ℕ) j'))
        (canonicalJointMeasure 2 N) := by
    simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
      (integrable_sum_mul_sum_of_pairwise
        (μ := canonicalJointMeasure 2 N)
        (Finset.range P.n) (Finset.univ : Finset (Fin P.n))
        (fun j => (1 / P.n : ℝ) * (P.n.choose j : ℝ))
        (fun m => P.coeff m)
        (fun j η => canonicalCrossTerm 2 N a mass T η P.n j)
        (fun m η => ∑ j' ∈ Finset.range (m : ℕ),
          ((m : ℕ).choose j' : ℝ) *
            canonicalCrossTerm 2 N a mass T η (m : ℕ) j')
        h_int_pairs_lead_perCoef)
  have h_decomp :=
    canonicalRoughError_l2_sq_eq 2 N a mass ha _hmass T hT P
      h_orth_lead_perCoef h_orth_m_outer
      h_int_lead_sq h_int_perCoef_sq h_int_cross_lead_perCoef
      h_int_pairs_lead_perCoef h_int_R_m_pairs
      h_int_leading_pairs h_int_perCoeff_pairs
  have h_lead_sum_bound :
      ∑ j ∈ Finset.range P.n,
        ((1 / P.n : ℝ) * (P.n.choose j : ℝ)) ^ 2 *
          ∫ η, (canonicalCrossTerm 2 N a mass T η P.n j) ^ 2
            ∂(canonicalJointMeasure 2 N)
      ≤
      KLeadSum * T * u ^ (P.n - 1) := by
    calc
      ∑ j ∈ Finset.range P.n,
          ((1 / P.n : ℝ) * (P.n.choose j : ℝ)) ^ 2 *
            ∫ η, (canonicalCrossTerm 2 N a mass T η P.n j) ^ 2
              ∂(canonicalJointMeasure 2 N)
        ≤
        ∑ j ∈ Finset.range P.n,
          ((((1 / P.n : ℝ) * (P.n.choose j : ℝ)) ^ 2) * KLeadFun j) *
            T * u ^ (P.n - 1) := by
              refine Finset.sum_le_sum ?_
              intro j hj
              have hj_le : j ≤ P.n - 1 := Nat.le_pred_of_lt (Finset.mem_range.mp hj)
              have hpow : u ^ j ≤ u ^ (P.n - 1) := pow_le_pow_right₀ hu_one hj_le
              have hcoeff_nonneg :
                  0 ≤ ((1 / P.n : ℝ) * (P.n.choose j : ℝ)) ^ 2 := sq_nonneg _
              calc
                ((1 / P.n : ℝ) * (P.n.choose j : ℝ)) ^ 2 *
                    ∫ η, (canonicalCrossTerm 2 N a mass T η P.n j) ^ 2
                      ∂(canonicalJointMeasure 2 N)
                  ≤
                    ((1 / P.n : ℝ) * (P.n.choose j : ℝ)) ^ 2 *
                      (KLeadFun j * T * u ^ j) :=
                    mul_le_mul_of_nonneg_left
                      (by simpa [u] using hKLead_bound j hj N a ha h_vol T hT)
                      hcoeff_nonneg
                _ ≤
                    ((1 / P.n : ℝ) * (P.n.choose j : ℝ)) ^ 2 *
                      (KLeadFun j * T * u ^ (P.n - 1)) := by
                    apply mul_le_mul_of_nonneg_left ?_ hcoeff_nonneg
                    have hKT_nonneg : 0 ≤ KLeadFun j * T :=
                      mul_nonneg (le_of_lt (hKLead_pos j hj)) (le_of_lt hT)
                    exact mul_le_mul_of_nonneg_left hpow hKT_nonneg
                _ = ((((1 / P.n : ℝ) * (P.n.choose j : ℝ)) ^ 2) * KLeadFun j) *
                      T * u ^ (P.n - 1) := by ring
      _ = KLeadSum * T * u ^ (P.n - 1) := by
            have h_reassoc :
                ∑ j ∈ Finset.range P.n,
                  ((1 / P.n : ℝ) * (P.n.choose j : ℝ)) ^ 2 * KLeadFun j * T * u ^ (P.n - 1) =
                ∑ j ∈ Finset.range P.n,
                  ((1 / P.n : ℝ) * (P.n.choose j : ℝ)) ^ 2 *
                    (KLeadFun j * (T * u ^ (P.n - 1))) := by
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  ring
            rw [h_reassoc]
            calc
              ∑ j ∈ Finset.range P.n,
                  ((1 / P.n : ℝ) * (P.n.choose j : ℝ)) ^ 2 * (KLeadFun j * (T * u ^ (P.n - 1)))
                =
                  ∑ j ∈ Finset.range P.n,
                    (((1 / P.n : ℝ) * (P.n.choose j : ℝ)) ^ 2 * KLeadFun j) *
                      (T * u ^ (P.n - 1)) := by
                        refine Finset.sum_congr rfl ?_
                        intro j hj
                        ring
              _ =
                  (∑ x ∈ Finset.range P.n,
                    ((1 / P.n : ℝ) * (P.n.choose x : ℝ)) ^ 2 * KLeadFun x) *
                      (T * u ^ (P.n - 1)) := by
                        exact (Finset.sum_mul
                          (s := Finset.range P.n)
                          (f := fun x =>
                            ((1 / P.n : ℝ) * (P.n.choose x : ℝ)) ^ 2 * KLeadFun x)
                          (a := T * u ^ (P.n - 1))).symm
              _ = KLeadSum * T * u ^ (P.n - 1) := by
                    simp [KLeadSum, mul_assoc]
  have h_per_sum_bound :
      ∑ m : Fin P.n,
        ∑ j ∈ Finset.range (m : ℕ),
          (P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2 *
            ∫ η, (canonicalCrossTerm 2 N a mass T η (m : ℕ) j) ^ 2
              ∂(canonicalJointMeasure 2 N)
      ≤
      KPerSum * T * u ^ (P.n - 1) := by
    calc
      ∑ m : Fin P.n,
          ∑ j ∈ Finset.range (m : ℕ),
            (P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2 *
              ∫ η, (canonicalCrossTerm 2 N a mass T η (m : ℕ) j) ^ 2
                ∂(canonicalJointMeasure 2 N)
        ≤
        ∑ m : Fin P.n,
          ∑ j ∈ Finset.range (m : ℕ),
            (((P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2) * KPerFun m j) *
              T * u ^ (P.n - 1) := by
                refine Finset.sum_le_sum ?_
                intro m hm
                refine Finset.sum_le_sum ?_
                intro j hj
                have hj_le : j ≤ P.n - 1 := by
                  exact Nat.le_pred_of_lt (lt_trans (Finset.mem_range.mp hj) m.2)
                have hpow : u ^ j ≤ u ^ (P.n - 1) := pow_le_pow_right₀ hu_one hj_le
                have hcoeff_nonneg :
                    0 ≤ (P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2 := sq_nonneg _
                calc
                  (P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2 *
                      ∫ η, (canonicalCrossTerm 2 N a mass T η (m : ℕ) j) ^ 2
                        ∂(canonicalJointMeasure 2 N)
                    ≤
                      (P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2 *
                        (KPerFun m j * T * u ^ j) :=
                      mul_le_mul_of_nonneg_left
                        (by simpa [u] using hKPer_bound m j hj N a ha h_vol T hT)
                        hcoeff_nonneg
                  _ ≤
                      (P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2 *
                        (KPerFun m j * T * u ^ (P.n - 1)) := by
                      apply mul_le_mul_of_nonneg_left ?_ hcoeff_nonneg
                      have hKT_nonneg : 0 ≤ KPerFun m j * T :=
                        mul_nonneg (le_of_lt (hKPer_pos m j hj)) (le_of_lt hT)
                      exact mul_le_mul_of_nonneg_left hpow hKT_nonneg
                  _ = (((P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2) * KPerFun m j) *
                        T * u ^ (P.n - 1) := by ring
      _ = KPerSum * T * u ^ (P.n - 1) := by
            calc
              ∑ m : Fin P.n,
                  ∑ j ∈ Finset.range (m : ℕ),
                    (P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2 * KPerFun m j *
                      T * u ^ (P.n - 1)
                =
                  ∑ m : Fin P.n,
                    ((∑ j ∈ Finset.range (m : ℕ),
                        (P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2 * KPerFun m j) *
                      T * u ^ (P.n - 1)) := by
                        refine Finset.sum_congr rfl ?_
                        intro m hm
                        have h_reassoc :
                            ∑ j ∈ Finset.range (m : ℕ),
                              (P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2 * KPerFun m j * T *
                                u ^ (P.n - 1) =
                            ∑ j ∈ Finset.range (m : ℕ),
                              (P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2 *
                                (KPerFun m j * (T * u ^ (P.n - 1))) := by
                                  refine Finset.sum_congr rfl ?_
                                  intro j hj
                                  ring
                        rw [h_reassoc]
                        calc
                          ∑ j ∈ Finset.range (m : ℕ),
                              (P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2 *
                                (KPerFun m j * (T * u ^ (P.n - 1)))
                            =
                              ∑ j ∈ Finset.range (m : ℕ),
                                (((P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2) * KPerFun m j) *
                                  (T * u ^ (P.n - 1)) := by
                                    refine Finset.sum_congr rfl ?_
                                    intro j hj
                                    ring
                          _ =
                              (∑ j ∈ Finset.range (m : ℕ),
                                (P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2 * KPerFun m j) *
                                  (T * u ^ (P.n - 1)) := by
                                    exact (Finset.sum_mul
                                      (s := Finset.range (m : ℕ))
                                      (f := fun j =>
                                        (P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2 * KPerFun m j)
                                      (a := T * u ^ (P.n - 1))).symm
                          _ = (∑ j ∈ Finset.range (m : ℕ),
                                (P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2 * KPerFun m j) *
                                  T * u ^ (P.n - 1) := by
                                    ring
              _ =
                  (∑ m : Fin P.n,
                      ∑ j ∈ Finset.range (m : ℕ),
                        (P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2 * KPerFun m j) *
                    T * u ^ (P.n - 1) := by
                      have h_reassoc :
                          ∑ m : Fin P.n,
                            (∑ j ∈ Finset.range (m : ℕ),
                                (P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2 * KPerFun m j) * T *
                              u ^ (P.n - 1) =
                          ∑ m : Fin P.n,
                            (∑ j ∈ Finset.range (m : ℕ),
                                (P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2 * KPerFun m j) *
                              (T * u ^ (P.n - 1)) := by
                                refine Finset.sum_congr rfl ?_
                                intro m hm
                                ring
                      rw [h_reassoc]
                      simpa [KPerSum, mul_assoc] using
                        (Finset.sum_mul
                          (s := Finset.univ)
                          (f := fun m : Fin P.n =>
                            ∑ j ∈ Finset.range (m : ℕ),
                              (P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2 * KPerFun m j)
                          (a := T * u ^ (P.n - 1))).symm
  calc
    ∫ η, (canonicalRoughError 2 N a mass T P η) ^ 2
        ∂(canonicalJointMeasure 2 N)
      =
      (∑ j ∈ Finset.range P.n,
        ((1 / P.n : ℝ) * (P.n.choose j : ℝ)) ^ 2 *
          ∫ η, (canonicalCrossTerm 2 N a mass T η P.n j) ^ 2
              ∂(canonicalJointMeasure 2 N))
      + ∑ m : Fin P.n,
          ∑ j ∈ Finset.range (m : ℕ),
            (P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2 *
              ∫ η, (canonicalCrossTerm 2 N a mass T η (m : ℕ) j) ^ 2
                  ∂(canonicalJointMeasure 2 N) := h_decomp
    _ ≤ KLeadSum * T * u ^ (P.n - 1) + KPerSum * T * u ^ (P.n - 1) := by
          gcongr
    _ = K0 * T * u ^ (P.n - 1) := by
          dsimp [K0]
          ring
    _ ≤ K * T * u ^ (P.n - 1) := by
          have hK0_le_K : K0 ≤ K := by
            dsimp [K, K0]
            linarith
          simpa [mul_assoc] using
            (mul_le_mul_of_nonneg_right hK0_le_K h_common_nonneg)
    _ = K * T * (1 + |Real.log T|) ^ (P.n - 1) := by
          rfl

/-- Uniform canonical-joint rough negative tail from `rough_error_variance`.

This packages the canonical standard-Gaussian representative,
its `wienerChaosLE` membership, and the variance estimate into the
dimension-independent concentration bound. The only scale input is the
square root of the variance witness from `rough_error_variance`. -/
theorem canonicalRoughError_neg_tail_uniform_in_aN
    (P : InteractionPolynomial)
    (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a)
        (_hvol : (N : ℝ) * a = L)
        (T : ℝ) (_hT : 0 < T)
        (t : ℝ) (_ht : 0 < t),
        (canonicalJointMeasure 2 N)
          {η | canonicalRoughError 2 N a mass T P η ≤ -t} ≤
            2 * ENNReal.ofReal
              (Real.exp
                (-(Pphi2.ChaosTailBridge.chaosTailConstant P.n) *
                  (t /
                    (2 * Real.sqrt
                      (K * T * (1 + |Real.log T|) ^ (P.n - 1)))) ^
                    ((2 : ℝ) / P.n))) := by
  obtain ⟨K, hK_pos, hvar⟩ :=
    rough_error_variance (d := 2) rfl P L mass hL hmass
  refine ⟨K, hK_pos, ?_⟩
  intro N _ a ha hvol T hT t ht
  let nStd : ℕ := Fintype.card (CanonicalJointSumIndex 2 N)
  obtain ⟨hf, hF_chaos⟩ :=
    canonicalRoughErrorStd_mem_wienerChaosLE
      (d := 2) (N := N) (a := a) (mass := mass) ha hmass T hT P
  let F : MeasureTheory.Lp ℝ 2 (GaussianHilbert.stdGaussianFin nStd) :=
    hf.toLp (canonicalRoughErrorStd 2 N a mass T P)
  have hrepr_joint :
      ∀ᵐ η ∂(canonicalJointMeasure 2 N),
        (F : (Fin nStd → ℝ) → ℝ)
          (canonicalJointStdGaussianMeasurableEquiv 2 N η) =
            canonicalRoughError 2 N a mass T P η := by
    have hrepr_std :
        ∀ᵐ ξ ∂(GaussianHilbert.stdGaussianFin nStd),
          (F : (Fin nStd → ℝ) → ℝ) ξ =
            canonicalRoughErrorStd 2 N a mass T P ξ := by
      simpa [F] using
        (MemLp.coeFn_toLp hf :
          (hf.toLp (canonicalRoughErrorStd 2 N a mass T P) : (Fin nStd → ℝ) → ℝ)
            =ᵐ[GaussianHilbert.stdGaussianFin nStd]
              canonicalRoughErrorStd 2 N a mass T P)
    have hrepr_map :
        ∀ᵐ η ∂(canonicalJointMeasure 2 N),
          (F : (Fin nStd → ℝ) → ℝ)
            (canonicalJointStdGaussianMeasurableEquiv 2 N η) =
              canonicalRoughErrorStd 2 N a mass T P
                (canonicalJointStdGaussianMeasurableEquiv 2 N η) := by
      have hrepr_std' :
          ∀ᵐ ξ ∂((canonicalJointMeasure 2 N).map
            (canonicalJointStdGaussianMeasurableEquiv 2 N)),
            (F : (Fin nStd → ℝ) → ℝ) ξ =
              canonicalRoughErrorStd 2 N a mass T P ξ := by
        simpa [nStd, canonicalJointMeasure_map_stdGaussian (d := 2) (N := N)] using hrepr_std
      exact MeasureTheory.ae_of_ae_map
        (canonicalJointStdGaussianMeasurableEquiv 2 N).measurable.aemeasurable
        hrepr_std'
    filter_upwards [hrepr_map] with η hη
    simpa using hη.trans
      (canonicalRoughErrorStd_eq
        (d := 2) (N := N) (a := a) (mass := mass) (T := T) (P := P) η)
  have hF_norm_sq :
      ‖F‖ ^ 2 =
        ∫ ξ, (canonicalRoughErrorStd 2 N a mass T P ξ) ^ 2
          ∂(GaussianHilbert.stdGaussianFin nStd) := by
    change
      ‖hf.toLp (canonicalRoughErrorStd 2 N a mass T P)‖ ^ 2 =
        ∫ ξ, (canonicalRoughErrorStd 2 N a mass T P ξ) ^ 2
          ∂(GaussianHilbert.stdGaussianFin nStd)
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hf] with ξ hξ
    simp [hξ, sq]
  have hsq_integrable :
      Integrable (fun ξ => (canonicalRoughErrorStd 2 N a mass T P ξ) ^ 2)
        (GaussianHilbert.stdGaussianFin nStd) := hf.integrable_sq
  have hsq_integrable_map :
      Integrable (fun ξ => (canonicalRoughErrorStd 2 N a mass T P ξ) ^ 2)
        ((canonicalJointMeasure 2 N).map
          (canonicalJointStdGaussianMeasurableEquiv 2 N)) := by
    simpa [nStd, canonicalJointMeasure_map_stdGaussian (d := 2) (N := N)] using hsq_integrable
  have hstd_eq_joint :
      ∫ ξ, (canonicalRoughErrorStd 2 N a mass T P ξ) ^ 2
          ∂(GaussianHilbert.stdGaussianFin nStd) =
        ∫ η, (canonicalRoughError 2 N a mass T P η) ^ 2
          ∂(canonicalJointMeasure 2 N) := by
    rw [← canonicalJointMeasure_map_stdGaussian (d := 2) (N := N)]
    rw [integral_map
      (canonicalJointStdGaussianMeasurableEquiv 2 N).measurable.aemeasurable
      hsq_integrable_map.aestronglyMeasurable]
    refine integral_congr_ae ?_
    filter_upwards [Filter.Eventually.of_forall
      (fun η : CanonicalJoint 2 N =>
        canonicalRoughErrorStd_eq
          (d := 2) (N := N) (a := a) (mass := mass) (T := T) (P := P) η)] with η hη
    simp [hη]
  have hvar_bound :
      ‖F‖ ^ 2 ≤ K * T * (1 + |Real.log T|) ^ (P.n - 1) := by
    rw [hF_norm_sq, hstd_eq_joint]
    exact hvar N a ha hvol T hT
  have hscale_pos :
      0 <
        Real.sqrt (K * T * (1 + |Real.log T|) ^ (P.n - 1)) := by
    apply Real.sqrt_pos.2
    positivity
  have hscale_norm :
      ‖F‖ ≤ Real.sqrt (K * T * (1 + |Real.log T|) ^ (P.n - 1)) := by
    have hnonneg :
        0 ≤ K * T * (1 + |Real.log T|) ^ (P.n - 1) := by positivity
    have hsq :
        ‖F‖ ^ 2 ≤
          (Real.sqrt (K * T * (1 + |Real.log T|) ^ (P.n - 1))) ^ 2 := by
      simpa [Real.sq_sqrt hnonneg] using hvar_bound
    nlinarith [hsq, norm_nonneg F, Real.sqrt_nonneg (K * T * (1 + |Real.log T|) ^ (P.n - 1))]
  exact
    canonicalRoughError_neg_tail_of_stdGaussian_explicit_ae
      (d := 2) (N := N) a mass T P P.n
      (le_trans (by norm_num) P.hn_ge)
      F hF_chaos
      (Real.sqrt (K * T * (1 + |Real.log T|) ^ (P.n - 1)))
      hscale_pos hscale_norm hrepr_joint t ht

/-- **`(canonicalRoughError)²` is integrable** on the canonical joint measure. Extracted from the
`L²`/Wiener-chaos membership (`canonicalRoughErrorStd_mem_wienerChaosLE`): the std-Gaussian
representative is `MemLp 2`, hence its square is integrable, and this transfers to the joint measure
via the measurable equivalence (`canonicalRoughErrorStd_eq`). The exposed companion of
`rough_error_variance` (which bounds the integral but keeps integrability internal). -/
theorem canonicalRoughError_sq_integrable (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T) (P : InteractionPolynomial) :
    Integrable (fun η => (canonicalRoughError d N a mass T P η) ^ 2)
      (canonicalJointMeasure d N) := by
  obtain ⟨hf, _⟩ := canonicalRoughErrorStd_mem_wienerChaosLE
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT P
  have hsq_map : Integrable (fun ξ => (canonicalRoughErrorStd d N a mass T P ξ) ^ 2)
      ((canonicalJointMeasure d N).map (canonicalJointStdGaussianMeasurableEquiv d N)) := by
    simpa [canonicalJointMeasure_map_stdGaussian (d := d) (N := N)] using hf.integrable_sq
  have hcomp := (integrable_map_equiv (canonicalJointStdGaussianMeasurableEquiv d N)
    (fun ξ => (canonicalRoughErrorStd d N a mass T P ξ) ^ 2)).mp hsq_map
  refine hcomp.congr (Filter.Eventually.of_forall fun η => ?_)
  simp [Function.comp]

end Pphi2

end
