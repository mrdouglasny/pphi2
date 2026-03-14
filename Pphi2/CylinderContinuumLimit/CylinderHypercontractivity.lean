/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cylinder Hypercontractivity and Density Transfer

Establishes L^p control on the cylinder interaction and the Cauchy-Schwarz
density transfer bound from the interacting measure to the free measure.

## Main results

- `cylinderFieldEval_wickMonomial_integral` — Hermite orthogonality (axiom)
- `cylinderBoltzmannWeight_sq_integrable` — uniform L² bound on exp(-V) (axiom)
- `cylinderV_mean_nonpos` — ∫ V_{Λ,T} dμ_free ≤ 0
- `cylinderPartitionFunction_ge_one` — Z_{Λ,T} ≥ 1 by Jensen
- `cylinderDensityTransfer` — Cauchy-Schwarz density transfer

## Mathematical background

The key input is Nelson's hypercontractive estimate, proved in
`GaussianField.Hypercontractive` as the Gross log-Sobolev inequality.
Applied to the cylinder Fourier mode decomposition, it gives uniform
L^p bounds on Wick-ordered polynomials of the regularized field.

The density transfer (Cauchy-Schwarz) converts integrals against the
interacting measure to integrals against the free Gaussian measure:

  `∫ F dμ_V ≤ √K · (∫ F² dμ_free)^{1/2}`

where K = sup_Λ ∫ exp(-2V) dμ_free is the exponential moment bound.

## References

- Nelson, *Construction of quantum fields from Markoff fields* (1973)
- Gross, "Logarithmic Sobolev inequalities" (1975)
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. V, VIII
-/

import Pphi2.CylinderContinuumLimit.CylinderInteraction
import GaussianField.Properties

open GaussianField MeasureTheory

noncomputable section

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Axioms from hypercontractivity

These two axioms encode the analytical content of Nelson's hypercontractive
estimate applied to the cylinder field. They are consequences of the
Gross log-Sobolev inequality (`gross_log_sobolev` in gaussian-field)
applied to the Fourier mode decomposition of φ_Λ on S¹_L × ℝ. -/

/-- **Hermite orthogonality**: Wick monomials of degree ≥ 1 have zero
expectation under the free Gaussian measure.

Since `cylinderRegularizedFieldEval L Λ mass hmass θ t` is Gaussian
under the free measure with variance `cylinderWickConstant L mass Λ`,
and `wickMonomial n c` is the nth probabilist's Hermite polynomial
scaled to variance c, the integral vanishes by orthogonality.

This is the cylinder analogue of `wickMonomial_latticeGaussian`. -/
axiom cylinderFieldEval_wickMonomial_integral
    (n : ℕ) (hn : 1 ≤ n) (Λ : ℕ) (mass : ℝ) (hmass : 0 < mass) (θ t : ℝ) :
    Integrable (fun ω => wickMonomial n (cylinderWickConstant L mass Λ)
        (cylinderRegularizedFieldEval L Λ mass hmass θ t ω))
      (cylinderFreeMeasure L mass hmass) ∧
    ∫ ω, wickMonomial n (cylinderWickConstant L mass Λ)
        (cylinderRegularizedFieldEval L Λ mass hmass θ t ω)
      ∂(cylinderFreeMeasure L mass hmass) = 0

/-- **Exponential moment bound**: `∫ exp(-2V_{Λ,T}) dμ_free ≤ K` uniformly in Λ.

This is the key estimate combining:
1. Nelson's hypercontractive bound: ‖V_{Λ,T}‖_{Lp(μ_free)} ≤ C·p^{n/2}
2. Exponential moment from moment growth: Σ (2^k/k!) ‖V‖_{Lk}^k < ∞
3. Uniformity in Λ from Wick ordering (cancels UV divergence)

The bound K depends on P, L, T, mass but NOT on the UV cutoff Λ.
This is the cylinder analogue of `exponential_moment_bound`. -/
axiom cylinderBoltzmannWeight_sq_integrable
    (P : InteractionPolynomial) (T mass : ℝ) (hT : 0 < T) (hmass : 0 < mass) :
    ∃ K : ℝ, 0 < K ∧ ∀ Λ : ℕ,
    ∫ ω, (interactingBoltzmannWeight (cylinderV L P Λ T mass hT hmass) ω) ^ 2
      ∂(cylinderFreeMeasure L mass hmass) ≤ K

/-! ## Partition function lower bound

From Hermite orthogonality of Wick monomials, the interaction has
nonpositive mean: ∫ V dμ_free ≤ 0. Jensen's inequality then gives
Z = ∫ exp(-V) dμ_free ≥ exp(-∫V dμ_free) ≥ 1. -/

/-- **L² bound on the interaction**: V_{Λ,T} ∈ L²(μ_free).

The interaction `V = ∫₀ᴸ ∫₋ᵀᵀ :P(φ_Λ(θ,t)):_c dt dθ` is a polynomial
functional of the UV-regularized Gaussian field (with finitely many modes),
integrated over a compact spacetime domain. By Nelson's hypercontractive
estimate, each Wick monomial of the field is in L^p for all p < ∞, and the
spacetime integration over [0,L] × [-T,T] preserves L^p membership.

This is the cylinder analogue of the lattice fact that V = a^d Σ_x :P(φ(x)):
is in L^p (which follows immediately from `integrable_finset_sum` on the
lattice). On the cylinder the sum becomes a double interval integral, so the
proof additionally requires Fubini interchange and L^p stability under
Bochner integration — infrastructure not yet formalized. -/
axiom cylinderV_memLp_two
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    MemLp (cylinderV L P Λ T mass hT hmass) 2 (cylinderFreeMeasure L mass hmass)

/-- The interaction functional is integrable under the free measure.

Follows from the L² bound `cylinderV_memLp_two` and the fact that the free
measure is a probability measure (hence finite), so L² ⊂ L¹. -/
theorem cylinderV_integrable
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    Integrable (cylinderV L P Λ T mass hT hmass) (cylinderFreeMeasure L mass hmass) :=
  (cylinderV_memLp_two L P Λ T mass hT hmass).integrable one_le_two

/-- **Fubini interchange** for the cylinder interaction integral.

Swaps the Bochner integral `∫_ω` (against the free Gaussian measure on
field configurations) with the double interval integral
`∫₀ᴸ ∫₋ᵀᵀ` (over spacetime on the cylinder S¹_L × ℝ):

  `∫_ω (∫₀ᴸ ∫₋ᵀᵀ f(θ,t,ω) dt dθ) dμ(ω) = ∫₀ᴸ ∫₋ᵀᵀ (∫_ω f(θ,t,ω) dμ(ω)) dt dθ`

This is Tonelli/Fubini applied to the product of the probability measure μ_free
and Lebesgue measure on [0,L] × [-T,T]. The hypotheses (joint measurability,
integrability of the iterated integral) follow from the Wick polynomial
structure and the Gaussian moment bounds but are technically demanding in
Lean's measure theory library. -/
axiom cylinderV_fubini
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    ∫ ω, cylinderV L P Λ T mass hT hmass ω ∂(cylinderFreeMeasure L mass hmass) =
    ∫ θ in (0 : ℝ)..L, ∫ t in (-T)..T,
      ∫ ω, wickPolynomial P (cylinderWickConstant L mass Λ)
        (cylinderRegularizedFieldEval L Λ mass hmass θ t ω)
      ∂(cylinderFreeMeasure L mass hmass)

/-- Helper: integrability and integral computation for the Wick polynomial
of the regularized field at a single spacetime point (θ, t) under the
cylinder free measure.

`∫ :P(φ_Λ(θ,t)):_c dμ_free = P.coeff₀` because all Wick monomials of
order ≥ 1 have zero Gaussian mean, and `:x⁰:_c = 1`.

This is the cylinder analogue of `wickPolynomial_integral_eq_coeff_zero`
from the lattice case. -/
private lemma cylinderWickPolynomial_integral_eq_coeff_zero
    (P : InteractionPolynomial) (Λ : ℕ) (mass : ℝ) (hmass : 0 < mass)
    (θ t : ℝ) :
    ∫ ω, wickPolynomial P (cylinderWickConstant L mass Λ)
        (cylinderRegularizedFieldEval L Λ mass hmass θ t ω)
      ∂(cylinderFreeMeasure L mass hmass) =
    P.coeff ⟨0, by have := P.hn_ge; omega⟩ := by
  set μ := cylinderFreeMeasure L mass hmass
  set c := cylinderWickConstant L mass Λ
  set φ := cylinderRegularizedFieldEval L Λ mass hmass θ t
  haveI : IsProbabilityMeasure μ := GaussianField.measure_isProbability _
  -- Integrability of each term
  have h_lead_int : Integrable (fun ω =>
      (1 / P.n : ℝ) * wickMonomial P.n c (φ ω)) μ :=
    (cylinderFieldEval_wickMonomial_integral L P.n (by have := P.hn_ge; omega)
      Λ mass hmass θ t).1.const_mul _
  have h_term_int : ∀ m : Fin P.n, Integrable (fun ω =>
      P.coeff m * wickMonomial (m : ℕ) c (φ ω)) μ := by
    intro m
    by_cases hm : (m : ℕ) = 0
    · have : (fun ω => P.coeff m * wickMonomial (m : ℕ) c (φ ω)) = fun _ => P.coeff m := by
        ext ω; simp [hm]
      rw [this]; exact integrable_const _
    · exact ((cylinderFieldEval_wickMonomial_integral L m (by omega)
        Λ mass hmass θ t).1).const_mul _
  have h_sum_int : Integrable (fun ω =>
      ∑ m : Fin P.n, P.coeff m * wickMonomial (m : ℕ) c (φ ω)) μ :=
    integrable_finset_sum _ fun m _ => h_term_int m
  -- Integral = P.coeff 0
  change ∫ ω, ((1 / P.n : ℝ) * wickMonomial P.n c (φ ω) +
    ∑ m : Fin P.n, P.coeff m * wickMonomial (m : ℕ) c (φ ω)) ∂μ = _
  rw [integral_add h_lead_int h_sum_int,
      integral_const_mul,
      (cylinderFieldEval_wickMonomial_integral L P.n (by have := P.hn_ge; omega)
        Λ mass hmass θ t).2,
      mul_zero, zero_add,
      integral_finset_sum _ (fun m _ => h_term_int m)]
  simp_rw [integral_const_mul]
  -- Each integral: ∫ wM_m = 1 if m=0, 0 if m≥1
  have h_wm_eval : ∀ m : Fin P.n,
      ∫ ω, wickMonomial (↑m) c (φ ω) ∂μ = if (m : ℕ) = 0 then 1 else 0 := by
    intro m
    by_cases hm : (m : ℕ) = 0
    · simp_rw [if_pos hm, hm, wickMonomial_zero]
      simp [integral_const]
    · rw [if_neg hm, (cylinderFieldEval_wickMonomial_integral L m (by omega)
        Λ mass hmass θ t).2]
  simp_rw [h_wm_eval, mul_ite, mul_one, mul_zero]
  -- ∑ (if m.val = 0 then coeff m else 0) = coeff ⟨0, _⟩
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  -- The filter picks out exactly ⟨0, _⟩
  have : Finset.univ.filter (fun m : Fin P.n => (m : ℕ) = 0) =
      {⟨0, by have := P.hn_ge; omega⟩} := by
    ext m; simp [Fin.ext_iff]
  rw [this, Finset.sum_singleton]

/-- The mean of the interaction under the free measure is nonpositive:
`∫ V_{Λ,T} dμ_free ≤ 0`.

By Fubini (`cylinderV_fubini`), we swap the measure integral with the
spacetime integrals. Then by Hermite orthogonality
(`cylinderFieldEval_wickMonomial_integral`), each Wick monomial of
degree ≥ 1 integrates to zero, leaving only the constant term
`P.coeff[0]` which is ≤ 0 for an `InteractionPolynomial`.

The result follows because the double interval integral of a nonpositive
constant over [0,L] × [-T,T] is nonpositive. -/
theorem cylinderV_mean_nonpos
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    ∫ ω, cylinderV L P Λ T mass hT hmass ω ∂(cylinderFreeMeasure L mass hmass) ≤ 0 := by
  -- Step 1: Apply Fubini to swap ∫_ω with ∫_θ ∫_t
  rw [cylinderV_fubini L P Λ T mass hT hmass]
  -- Step 2: Evaluate the inner ω-integral at each (θ, t)
  simp_rw [cylinderWickPolynomial_integral_eq_coeff_zero L P Λ mass hmass]
  -- Goal: ∫ θ in 0..L, ∫ t in (-T)..T, P.coeff ⟨0, _⟩ ≤ 0
  -- The integral of a constant c over [a,b] is c * (b - a)
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  -- Goal: (T - -T) * P.coeff ⟨0, _⟩ * (L - 0) ≤ 0
  -- which is (2T) * P.coeff₀ * L ≤ 0
  have h2T : 0 < T - (-T) := by linarith
  have hL_pos : 0 < L - 0 := by linarith [hL.out]
  -- Goal: (L - 0) * ((T - -T) * P.coeff ⟨0, _⟩) ≤ 0
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact le_of_lt hL_pos
  · exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt h2T) P.coeff_zero_nonpos

/-- The partition function satisfies Z_{Λ,T} ≥ 1.

**Proof sketch**: By Hermite orthogonality, ∫ :P(φ_Λ(θ,t)): dμ_free = P.coeff[0] ≤ 0
for each (θ,t), so ∫ V dμ_free ≤ 0. Jensen's inequality for the convex
function exp gives Z = ∫ exp(-V) dμ ≥ exp(-∫V dμ) ≥ exp(0) = 1. -/
theorem cylinderPartitionFunction_ge_one
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    1 ≤ interactingPartitionFunction (cylinderV L P Λ T mass hT hmass)
      (cylinderFreeMeasure L mass hmass) := by
  -- Z = ∫ exp(-V) dμ_free where μ_free is a probability measure
  set V := cylinderV L P Λ T mass hT hmass
  set μ := cylinderFreeMeasure L mass hmass
  -- Step 1: Use exp(-x) ≥ 1 - x to get Z ≥ ∫ (1 - V) dμ
  have h_exp_lb : ∀ ω, 1 - V ω ≤ interactingBoltzmannWeight V ω := fun ω => by
    simp only [interactingBoltzmannWeight]
    linarith [Real.add_one_le_exp (-(V ω))]
  -- Step 2: Integrate both sides
  have h_int_lb : ∫ ω, (1 - V ω) ∂μ ≤ interactingPartitionFunction V μ := by
    apply integral_mono
    · exact (integrable_const 1).sub (cylinderV_integrable L P Λ T mass hT hmass)
    · exact interactingBoltzmannWeight_integrable V μ
        (cylinderInteractionFunctional_measurable L P Λ T mass hT hmass)
        (cylinderInteractionFunctional_bounded_below L P Λ T mass hT hmass)
    · exact h_exp_lb
  -- Step 3: Simplify ∫ (1 - V) dμ = 1 - ∫ V dμ ≥ 1
  rw [integral_sub (integrable_const 1) (cylinderV_integrable L P Λ T mass hT hmass),
    integral_const, probReal_univ, one_smul] at h_int_lb
  linarith [cylinderV_mean_nonpos L P Λ T mass hT hmass]

/-! ## Density transfer

The Cauchy-Schwarz density transfer converts integrals against the
interacting measure μ_V to integrals against the free measure μ_free.

For nonneg F with F² integrable under μ_free:
  `∫ F dμ_V = (1/Z) ∫ F·exp(-V) dμ_free`
            `≤ (1/Z) · (∫ F²)^{1/2} · (∫ exp(-2V))^{1/2}`  (Cauchy-Schwarz)
            `≤ K^{1/2} · (∫ F² dμ_free)^{1/2}`             (since Z ≥ 1) -/

/-- **Cauchy-Schwarz density transfer**: bounds interacting expectations
by free Gaussian expectations.

  `∫ F dμ_V ≤ √K · (∫ F² dμ_free)^{1/2}`

This is the cylinder analogue of `density_transfer_bound` from the lattice. -/
theorem cylinderDensityTransfer
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    (K : ℝ) (hK : 0 < K)
    (hK_bound : ∫ ω, (interactingBoltzmannWeight
        (cylinderV L P Λ T mass hT hmass) ω) ^ 2
      ∂(cylinderFreeMeasure L mass hmass) ≤ K)
    (F : Configuration (CylinderTestFunction L) → ℝ)
    (hF_nn : ∀ ω, 0 ≤ F ω)
    (hF_sq_int : Integrable (fun ω => F ω ^ 2)
      (cylinderFreeMeasure L mass hmass)) :
    ∫ ω, F ω ∂(cylinderInteractingMeasure L P Λ T mass hT hmass) ≤
    K ^ (1/2 : ℝ) * (∫ ω, F ω ^ 2
      ∂(cylinderFreeMeasure L mass hmass)) ^ (1/2 : ℝ) := by
  -- Abbreviations for the key objects
  set V := cylinderV L P Λ T mass hT hmass with hV_def
  set μ := cylinderFreeMeasure L mass hmass with hμ_def
  set Z := interactingPartitionFunction V μ with hZ_def
  -- Key properties of V
  have hV_meas : Measurable V := cylinderInteractionFunctional_measurable L P Λ T mass hT hmass
  have hV_below : ∃ B : ℝ, ∀ ω, V ω ≥ -B :=
    cylinderInteractionFunctional_bounded_below L P Λ T mass hT hmass
  -- Z > 0 and Z ≥ 1
  have hZ_pos : 0 < Z := interactingPartitionFunction_pos V μ hV_meas hV_below
  have hZ_ge_one : 1 ≤ Z := cylinderPartitionFunction_ge_one L P Λ T mass hT hmass
  -- Step 1: Expand the interacting measure integral
  -- cylinderInteractingMeasure = (1/Z) • μ.withDensity(exp(-V))
  show ∫ ω, F ω ∂(interactingMeasure V μ) ≤ _
  simp only [interactingMeasure]
  rw [integral_smul_measure]
  -- Now the LHS is: (ENNReal.ofReal Z)⁻¹.toReal • ∫ F dμ.withDensity(...)
  -- Step 2: Convert withDensity integral
  rw [integral_withDensity_eq_integral_toReal_smul₀
      (interactingBoltzmannWeight_ennreal_measurable V hV_meas).aemeasurable
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  -- Simplify toReal ∘ ofReal since exp(-V) > 0
  have h_toReal : ∀ ω, (ENNReal.ofReal (interactingBoltzmannWeight V ω)).toReal =
      interactingBoltzmannWeight V ω := fun ω =>
    ENNReal.toReal_ofReal (le_of_lt (interactingBoltzmannWeight_pos V ω))
  simp_rw [h_toReal, smul_eq_mul]
  -- Step 3: Simplify the scalar (1/Z)
  have h_scalar : (ENNReal.ofReal Z)⁻¹.toReal = Z⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (le_of_lt hZ_pos)]
  rw [h_scalar]
  -- Now LHS = Z⁻¹ * ∫ ω, exp(-V ω) * F ω ∂μ
  -- Step 4: Bound Z⁻¹ ≤ 1 (since Z ≥ 1)
  have hZinv_le_one : Z⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hZ_ge_one
  -- Step 5: Suffices to show Cauchy-Schwarz bound on the product integral
  suffices h_cs : ∫ ω, interactingBoltzmannWeight V ω * F ω ∂μ ≤
      K ^ (1/2 : ℝ) * (∫ ω, F ω ^ 2 ∂μ) ^ (1/2 : ℝ) by
    calc Z⁻¹ * ∫ ω, interactingBoltzmannWeight V ω * F ω ∂μ
        ≤ 1 * (K ^ (1/2 : ℝ) * (∫ ω, F ω ^ 2 ∂μ) ^ (1/2 : ℝ)) := by
          apply mul_le_mul hZinv_le_one h_cs
            (integral_nonneg fun ω =>
              mul_nonneg (le_of_lt (interactingBoltzmannWeight_pos V ω)) (hF_nn ω))
            one_pos.le
      _ = K ^ (1/2 : ℝ) * (∫ ω, F ω ^ 2 ∂μ) ^ (1/2 : ℝ) := one_mul _
  -- Step 6: Cauchy-Schwarz (Holder with p = q = 2)
  -- ∫ exp(-V) * F ≤ (∫ exp(-V)²)^{1/2} * (∫ F²)^{1/2} ≤ K^{1/2} * (∫ F²)^{1/2}
  -- Construct MemLp hypotheses for the Boltzmann weight and F
  have hBW_aesm : AEStronglyMeasurable (interactingBoltzmannWeight V) μ :=
    hV_meas.neg.exp.aestronglyMeasurable
  -- The Boltzmann weight is bounded (V ≥ -B implies exp(-V) ≤ exp(B)), hence in L^p for all p
  have hBW_memLp : MemLp (interactingBoltzmannWeight V) 2 μ := by
    obtain ⟨B, hB⟩ := hV_below
    exact memLp_of_bounded (a := 0) (b := Real.exp B)
      (ae_of_all _ fun ω => ⟨le_of_lt (interactingBoltzmannWeight_pos V ω),
        Real.exp_le_exp_of_le (by have := hB ω; linarith)⟩)
      hBW_aesm 2
  -- F is AEStronglyMeasurable: F = sqrt(F²) since F ≥ 0
  have hF_aesm : AEStronglyMeasurable F μ := by
    have : AEStronglyMeasurable (fun ω => Real.sqrt (F ω ^ 2)) μ :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hF_sq_int.aestronglyMeasurable
    exact this.congr (ae_of_all _ fun ω => by simp [Real.sqrt_sq (hF_nn ω)])
  have hF_memLp : MemLp F 2 μ :=
    (memLp_two_iff_integrable_sq hF_aesm).mpr hF_sq_int
  -- Apply Holder's inequality (Cauchy-Schwarz: p = q = 2)
  have h_holder : ∫ ω, interactingBoltzmannWeight V ω * F ω ∂μ ≤
      (∫ ω, interactingBoltzmannWeight V ω ^ (2:ℝ) ∂μ) ^ (1/2 : ℝ) *
      (∫ ω, F ω ^ (2:ℝ) ∂μ) ^ (1/2 : ℝ) :=
    integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (ae_of_all _ fun ω => le_of_lt (interactingBoltzmannWeight_pos V ω))
      (ae_of_all _ fun ω => hF_nn ω)
      (by rwa [show (ENNReal.ofReal (2:ℝ)) = 2 from by norm_num])
      (by rwa [show (ENNReal.ofReal (2:ℝ)) = 2 from by norm_num])
  -- Convert rpow to nat pow in the integrals to match hypotheses
  simp_rw [Real.rpow_two] at h_holder
  -- Bound (∫ exp(-V)²)^{1/2} ≤ K^{1/2} using hK_bound
  calc ∫ ω, interactingBoltzmannWeight V ω * F ω ∂μ
      ≤ (∫ ω, interactingBoltzmannWeight V ω ^ 2 ∂μ) ^ (1/2 : ℝ) *
        (∫ ω, F ω ^ 2 ∂μ) ^ (1/2 : ℝ) := h_holder
    _ ≤ K ^ (1/2 : ℝ) * (∫ ω, F ω ^ 2 ∂μ) ^ (1/2 : ℝ) := by
        apply mul_le_mul_of_nonneg_right
        · exact Real.rpow_le_rpow
            (integral_nonneg fun ω => sq_nonneg (interactingBoltzmannWeight V ω))
            hK_bound (by norm_num : (0:ℝ) ≤ 1/2)
        · exact Real.rpow_nonneg (integral_nonneg fun ω => sq_nonneg (F ω)) _

/-- **Uniform moment bound**: second moments under the interacting measure
are bounded uniformly in the UV cutoff Λ.

  `sup_Λ ∫ |ω(f)|² dμ_{Λ,T} ≤ C(f)`

Follows from density transfer + Gaussian second moments. -/
theorem cylinderInteracting_second_moment_bound
    (P : InteractionPolynomial) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    (f : CylinderTestFunction L) :
    ∃ C : ℝ, ∀ Λ : ℕ,
    ∫ ω, (ω f) ^ 2 ∂(cylinderInteractingMeasure L P Λ T mass hT hmass) ≤ C := by
  -- Step 1: Get uniform L² bound K on the Boltzmann weight (independent of Λ)
  obtain ⟨K, hK_pos, hK_bound⟩ := cylinderBoltzmannWeight_sq_integrable L P T mass hT hmass
  -- Step 2: Gaussian 4th moment integrability.
  -- The free measure is GaussianField.measure (cylinderMassOperator L mass hmass),
  -- so pairing_memLp gives ω(f) ∈ Lᵖ for all p. In particular p = 4 gives
  -- ∫ |ω(f)|⁴ dμ_free < ∞, which is exactly ∫ ((ω f)²)² dμ_free < ∞.
  have hF_sq_int : Integrable (fun ω : Configuration (CylinderTestFunction L) =>
      ((ω f) ^ 2) ^ 2) (cylinderFreeMeasure L mass hmass) := by
    -- ω(f) ∈ L⁴(μ_free) by Gaussian all-moments (pairing_memLp at p = 4)
    have h4 : MemLp (fun ω : Configuration (CylinderTestFunction L) => ω f)
        4 (cylinderFreeMeasure L mass hmass) := by
      exact_mod_cast pairing_memLp (cylinderMassOperator L mass hmass) f 4
    -- MemLp f 4 → MemLp (‖f‖^4) 1 by norm_rpow, i.e., Integrable (‖f‖^4)
    set μ_free := cylinderFreeMeasure L mass hmass
    have hmem := h4.norm_rpow (p := (4 : ENNReal))
      (by norm_num : (4 : ENNReal) ≠ 0) (by norm_num : (4 : ENNReal) ≠ ⊤)
    rw [memLp_one_iff_integrable] at hmem
    -- Convert rpow to pow and simplify ENNReal.toReal
    have h_int : Integrable (fun ω : Configuration (CylinderTestFunction L) =>
        ‖ω f‖ ^ (4 : ℕ)) μ_free := by
      refine hmem.congr (Filter.Eventually.of_forall fun ω => ?_)
      -- Goal: ‖ω f‖ ^ ENNReal.toReal 4 = ‖ω f‖ ^ 4
      simp [ENNReal.toReal_ofNat]
    -- For real x: ‖x‖^4 = (x^2)^2 since ‖x‖ = |x| and |x|^4 = (x^2)^2
    exact h_int.congr (Filter.Eventually.of_forall fun ω => by
      dsimp only
      rw [Real.norm_eq_abs]
      -- Goal: |ω f| ^ 4 = (ω f ^ 2) ^ 2
      -- Both sides equal (ω f)^4: use sq_abs on the RHS inner part
      conv_rhs => rw [show ω f ^ 2 = |ω f| ^ 2 from (sq_abs _).symm]
      ring)
  -- Step 3: Apply density transfer for each Λ.
  -- For F(ω) = (ω f)², which is nonneg, cylinderDensityTransfer gives:
  --   ∫ (ω f)² dμ_V ≤ K^(1/2) · (∫ ((ω f)²)² dμ_free)^(1/2)
  -- The RHS is independent of Λ (K is uniform, free measure doesn't depend on Λ).
  refine ⟨K ^ (1/2 : ℝ) * (∫ ω, ((ω f) ^ 2) ^ 2
    ∂(cylinderFreeMeasure L mass hmass)) ^ (1/2 : ℝ), fun Λ => ?_⟩
  exact cylinderDensityTransfer L P Λ T mass hT hmass K hK_pos (hK_bound Λ)
    (fun ω => (ω f) ^ 2) (fun ω => sq_nonneg _) hF_sq_int

end Pphi2

end
