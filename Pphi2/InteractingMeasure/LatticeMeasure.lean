/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Interacting Lattice Measure

Defines the P(Φ)₂ measure on the finite lattice as a perturbation of the
lattice Gaussian measure from gaussian-field:

  `dμ_a = (1/Z_a) · exp(-V_a(ω)) · dμ_{GFF,a}(ω)`

where `V_a(ω) = a^d Σ_x :P(ω(δ_x)):_a` is the Wick-ordered interaction.

## Main definitions

- `interactionFunctional` — V_a as a function of ω ∈ Configuration
- `partitionFunction` — Z_a = ∫ exp(-V_a) dμ_{GFF,a}
- `interactingLatticeMeasure` — the P(Φ)₂ lattice measure

## Mathematical background

The field configuration space is `Configuration (FinLatticeField d N) = WeakDual ℝ (FinLatticeField d N)`.
A configuration `ω` assigns to each test function `f` a real number `ω(f)`.
The "field value at site x" is `ω(δ_x)` where `δ_x = finLatticeDelta d N x`.

The Gaussian measure `μ_{GFF,a}` is `latticeGaussianMeasure d N a mass ha hmass`.
The interacting measure reweights it by `exp(-V_a)/Z_a`.

## References

- Glimm-Jaffe, *Quantum Physics*, §19.1
- Simon, *The P(φ)₂ Euclidean QFT*, §II
-/

import Pphi2.InteractingMeasure.LatticeAction
import Lattice.Covariance
import GaussianField.Construction

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

variable (d N : ℕ) [NeZero N]

/-! ## Field evaluation via delta functions -/

/-- Evaluate the field at lattice site x: `ω(δ_x)`.

For `ω ∈ Configuration (FinLatticeField d N) = WeakDual ℝ (FinLatticeField d N)`,
this extracts the "field value at site x" by pairing ω with the delta function. -/
def fieldAtSite (x : FinLatticeSites d N) :
    Configuration (FinLatticeField d N) → ℝ :=
  fun ω => ω (finLatticeDelta d N x)

/-! ## Interaction as a function of configurations -/

/-- The lattice interaction as a function of the configuration ω:

  `V_a(ω) = a^d · Σ_x :P(ω(δ_x)):_{c_a}`

This lifts `latticeInteraction` from fields φ to configurations ω by
evaluating ω at delta functions. -/
def interactionFunctional (P : InteractionPolynomial) (a mass : ℝ) :
    Configuration (FinLatticeField d N) → ℝ :=
  fun ω => a ^ d * ∑ x : FinLatticeSites d N,
    wickPolynomial P (wickConstant d N a mass) (ω (finLatticeDelta d N x))

/-- The interaction functional is measurable.

Each evaluation `ω ↦ ω(δ_x)` is measurable (by definition of the cylindrical
σ-algebra on Configuration), and `wickPolynomial` is a polynomial in the
evaluation, hence measurable. A finite sum of measurable functions is measurable. -/
private theorem wickMonomial_measurable (n : ℕ) (c : ℝ) (f : α → ℝ)
    {mα : MeasurableSpace α}
    (hf : @Measurable α ℝ mα (borel ℝ) f) :
    @Measurable α ℝ mα (borel ℝ) (fun x => wickMonomial n c (f x)) := by
  -- Induct on n with two-step hypothesis via strong induction
  suffices h : ∀ k ≤ n, @Measurable α ℝ mα (borel ℝ) (fun x => wickMonomial k c (f x)) from
    h n le_rfl
  intro k hk
  induction k using Nat.strongRecOn with
  | ind k ih =>
    match k with
    | 0 => exact measurable_const
    | 1 => exact hf
    | k + 2 =>
      simp only [wickMonomial_succ_succ]
      exact (hf.mul (ih (k + 1) (by omega) (by omega))).sub
        (measurable_const.mul (ih k (by omega) (by omega)))

theorem interactionFunctional_measurable (P : InteractionPolynomial) (a mass : ℝ) :
    @Measurable (Configuration (FinLatticeField d N)) ℝ
      instMeasurableSpaceConfiguration (borel ℝ)
      (interactionFunctional d N P a mass) := by
  unfold interactionFunctional
  apply Measurable.const_mul
  apply Finset.measurable_sum _ (fun x _ => ?_)
  unfold wickPolynomial
  apply Measurable.add
  · exact Measurable.const_mul
      (wickMonomial_measurable P.n (wickConstant d N a mass) _
        (configuration_eval_measurable _)) _
  · exact Finset.measurable_sum _ (fun m _ =>
      Measurable.const_mul
        (wickMonomial_measurable m (wickConstant d N a mass) _
          (configuration_eval_measurable _)) _)

/-- The interaction functional is bounded below (lifted from `latticeInteraction_bounded_below`). -/
theorem interactionFunctional_bounded_below (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (_hmass : 0 < mass) :
    ∃ B : ℝ, ∀ ω : Configuration (FinLatticeField d N),
    interactionFunctional d N P a mass ω ≥ -B := by
  obtain ⟨A, hA_pos, hA_bound⟩ := wickPolynomial_bounded_below P (wickConstant d N a mass)
  refine ⟨a ^ d * Fintype.card (FinLatticeSites d N) * A, fun ω => ?_⟩
  unfold interactionFunctional
  have ha_pow : (0 : ℝ) < a ^ d := pow_pos ha d
  calc a ^ d * ∑ x : FinLatticeSites d N,
        wickPolynomial P (wickConstant d N a mass) (ω (finLatticeDelta d N x))
      ≥ a ^ d * ∑ _x : FinLatticeSites d N, (-A) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt ha_pow)
        apply Finset.sum_le_sum
        intro x _
        exact hA_bound _
    _ = -(a ^ d * Fintype.card (FinLatticeSites d N) * A) := by
        simp [Finset.sum_const, mul_comm]
        ring

/-- The interaction functional is a sum of single-site functions.

Each term :P(ω(δ_x)): depends on ω only through the single evaluation ω(δ_x),
so V_a(ω) = a^d · Σ_x v_x(ω(δ_x)) where v_x(t) = :P(t):_{c_a}.
This is the key property enabling the FKG inequality via `fkg_perturbed`. -/
theorem interactionFunctional_single_site (P : InteractionPolynomial) (a mass : ℝ) :
    ∃ v : FinLatticeSites d N → (ℝ → ℝ),
      ∀ ω : Configuration (FinLatticeField d N),
        interactionFunctional d N P a mass ω =
          a ^ d * ∑ x, v x (ω (finLatticeDelta d N x)) :=
  ⟨fun _x τ => wickPolynomial P (wickConstant d N a mass) τ, fun _ω => rfl⟩

/-! ## Partition function -/

/-- The Boltzmann weight `exp(-V_a(ω))`. -/
def boltzmannWeight (P : InteractionPolynomial) (a mass : ℝ) :
    Configuration (FinLatticeField d N) → ℝ :=
  fun ω => Real.exp (-(interactionFunctional d N P a mass ω))

/-- The Boltzmann weight is strictly positive. -/
theorem boltzmannWeight_pos (P : InteractionPolynomial) (a mass : ℝ)
    (ω : Configuration (FinLatticeField d N)) :
    0 < boltzmannWeight d N P a mass ω :=
  Real.exp_pos _

/-- The Boltzmann weight is integrable with respect to the lattice Gaussian measure.

Since V_a is bounded below by -B, we have `exp(-V_a) ≤ exp(B)`, so
`∫ exp(-V_a) dμ_{GFF} ≤ exp(B) < ∞`. -/
theorem boltzmannWeight_integrable (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    Integrable (boltzmannWeight d N P a mass)
      (latticeGaussianMeasure d N a mass ha hmass) := by
  -- exp(-V) is bounded: V ≥ -B implies exp(-V) ≤ exp(B)
  obtain ⟨B, hB_bound⟩ := interactionFunctional_bounded_below d N P a mass ha hmass
  haveI := latticeGaussianMeasure_isProbability d N a mass ha hmass
  apply Integrable.of_bound (C := Real.exp B)
  · -- AEStronglyMeasurable: boltzmannWeight is measurable
    apply Measurable.aestronglyMeasurable
    exact (interactionFunctional_measurable d N P a mass).neg.exp
  · -- Bound: ‖exp(-V(ω))‖ ≤ exp(B)
    apply Filter.Eventually.of_forall
    intro ω
    simp only [boltzmannWeight, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp_of_le (by linarith [hB_bound ω])

/-- The partition function: `Z_a = ∫ exp(-V_a(ω)) dμ_{GFF,a}(ω)`.

This is strictly positive because the integrand is strictly positive
and the Gaussian measure is a probability measure. -/
def partitionFunction (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) : ℝ :=
  ∫ ω, boltzmannWeight d N P a mass ω
    ∂(latticeGaussianMeasure d N a mass ha hmass)

/-- The partition function is strictly positive.
Proof: exp(-V) > 0 everywhere, μ_{GFF} is a probability measure (total mass 1),
so the integral of a strictly positive integrable function is positive. -/
theorem partitionFunction_pos (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    0 < partitionFunction d N P a mass ha hmass := by
  unfold partitionFunction
  haveI := latticeGaussianMeasure_isProbability d N a mass ha hmass
  have hinteg := boltzmannWeight_integrable d N P a mass ha hmass
  -- Use integral_pos_iff_support_of_nonneg with exp > 0 everywhere
  rw [integral_pos_iff_support_of_nonneg
    (fun ω => le_of_lt (boltzmannWeight_pos d N P a mass ω)) hinteg]
  -- support of boltzmannWeight = univ (since exp > 0)
  have hsup : Function.support (boltzmannWeight d N P a mass) = Set.univ := by
    ext ω; simp [Function.mem_support, ne_of_gt (boltzmannWeight_pos d N P a mass ω)]
  rw [hsup]
  exact Measure.measure_univ_pos.mpr (IsProbabilityMeasure.ne_zero _)

/-! ## The interacting lattice measure -/

/-- The P(Φ)₂ interacting measure on the finite lattice:

  `dμ_a = (1/Z_a) · exp(-V_a(ω)) · dμ_{GFF,a}(ω)`

This is the Gaussian measure reweighted by the Boltzmann factor of the
Wick-ordered interaction. -/
def interactingLatticeMeasure (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    @Measure (Configuration (FinLatticeField d N)) instMeasurableSpaceConfiguration :=
  (ENNReal.ofReal (partitionFunction d N P a mass ha hmass))⁻¹ •
    (latticeGaussianMeasure d N a mass ha hmass).withDensity
      (fun ω => ENNReal.ofReal (boltzmannWeight d N P a mass ω))

/-- The interacting lattice measure is a probability measure. -/
theorem interactingLatticeMeasure_isProbability (P : InteractionPolynomial)
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    @IsProbabilityMeasure (Configuration (FinLatticeField d N))
      instMeasurableSpaceConfiguration
      (interactingLatticeMeasure d N P a mass ha hmass) := by
  constructor
  have hZ := partitionFunction_pos d N P a mass ha hmass
  have hZ_ne : ENNReal.ofReal (partitionFunction d N P a mass ha hmass) ≠ 0 :=
    ENNReal.ofReal_pos.mpr hZ |>.ne'
  have hZ_ne_top : ENNReal.ofReal (partitionFunction d N P a mass ha hmass) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  unfold interactingLatticeMeasure
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
  -- Need: ∫⁻ ofReal(boltzmannWeight) dμ = ofReal(Z)
  rw [← ofReal_integral_eq_lintegral_ofReal
    (boltzmannWeight_integrable d N P a mass ha hmass)
    (Filter.Eventually.of_forall (fun ω => le_of_lt (boltzmannWeight_pos d N P a mass ω)))]
  simp only [smul_eq_mul]
  exact ENNReal.inv_mul_cancel hZ_ne hZ_ne_top

/-! ## Schwinger functions

The n-point Schwinger functions of the interacting theory are computed as
expectations under the interacting measure. By construction, they equal
Gaussian expectations reweighted by exp(-V)/Z. -/

/-- Two-point Schwinger function of the interacting theory.

  `S₂(x,y) = (1/Z) ∫ ω(δ_x) · ω(δ_y) · exp(-V_a(ω)) dμ_{GFF}(ω)`

This should be compared with the free two-point function
`G_a(x,y) = lattice_cross_moment ... (δ_x) (δ_y)` from gaussian-field. -/
def schwinger2 (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (x y : FinLatticeSites d N) : ℝ :=
  ∫ ω : Configuration (FinLatticeField d N),
    ω (finLatticeDelta d N x) * ω (finLatticeDelta d N y)
    ∂(interactingLatticeMeasure d N P a mass ha hmass)

end Pphi2

end
