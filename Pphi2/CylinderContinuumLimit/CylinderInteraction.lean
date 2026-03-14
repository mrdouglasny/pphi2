/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# P(φ)₂ Interaction on the Cylinder S¹_L × ℝ

Defines the Wick-ordered interaction potential, Boltzmann weight, partition
function, and interacting measure for P(φ)₂ theory on the cylinder.

## Main definitions

- `cylinderWickConstant L mass Λ` — UV-regularized single-point variance
- `cylinderInteractionFunctional` — interaction V_{Λ,T} on field configurations
- `cylinderBoltzmannWeight` — Boltzmann weight `exp(-V)`
- `cylinderPartitionFunction` — partition function `Z = ∫ exp(-V) dμ`
- `cylinderInteractingMeasure` — interacting measure `(1/Z) exp(-V) dμ`
- `cylinderSchwinger2` — two-point Schwinger function ⟨ω(f)ω(g)⟩_V

## Mathematical background

### The P(φ)₂ interaction on the cylinder

For an even polynomial P of degree ≥ 4 (an `InteractionPolynomial`),
the interaction functional with UV cutoff Λ and IR cutoff [-T,T] is:

  `V_{Λ,T}(ω) = ∫_{S¹_L × [-T,T]} :P(φ_Λ(x)):_{c_Λ} dx`

where:
- `Λ` is a spatial mode cutoff (keeping Fourier modes |n| ≤ Λ)
- `T > 0` is the temporal half-extent
- `φ_Λ(x)` is the UV-regularized field at x
- `c_Λ = cylinderWickConstant L mass Λ` is the regularized variance

### Wick constant

The Wick constant `c_Λ = Σ_{|k|≤Λ} 1/(2ω_k L)` is the UV-regularized
single-point variance, using the cylinder dispersion relation
`ω_k = resolventFreq L mass k`. It diverges logarithmically as Λ → ∞
in d = 1+1. Wick ordering (via `wickPolynomial P c_Λ`) removes this
divergence from the interaction.

### Nelson's estimate

The interaction is bounded below: `V_{Λ,T}(ω) ≥ -B`. This ensures
`exp(-V)` is integrable and `Z > 0`, so the interacting measure
`dμ_V = (1/Z) exp(-V) dμ_free` is a well-defined probability measure.

## References

- Simon, *The P(φ)₂ Euclidean QFT*, Ch. V, VIII
- Glimm-Jaffe, *Quantum Physics*, §8.6, §19.1
- Nelson, "Construction of quantum fields from Markov fields" (1973)
-/

import Pphi2.WickOrdering.WickPolynomial
import Cylinder.GreenFunction

open GaussianField MeasureTheory

noncomputable section

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Cylinder Wick constant

The Wick constant `c_Λ(L, mass)` is the UV-regularized single-point variance
of the free field on S¹_L × ℝ:

  `c_Λ = Σ_{|k| ≤ Λ} 1 / (2ω_k · L)`

Using the natural enumeration via `fourierFreq`, this becomes a sum over
`n = 0, 1, ..., 2Λ` (covering modes k = 0, 1, -1, 2, -2, ..., Λ, -Λ).

This is the cylinder analogue of the lattice `wickConstant d N a mass`. -/

/-- **UV-cutoff Wick constant** on the cylinder S¹_L × ℝ.

  `c_Λ = Σ_{n=0}^{2Λ} 1 / (2 · ω_n · L)`

where `ω_n = resolventFreq L mass n` is the dispersion relation and the
sum over `n = 0, ..., 2Λ` covers all spatial Fourier modes `|k| ≤ Λ`
via the `fourierFreq` enumeration.

This is the regularized coincidence limit of the Green's function:
`c_Λ = G_Λ(x, x)` for the UV-cutoff two-point function. -/
def cylinderWickConstant (mass : ℝ) (Λ : ℕ) : ℝ :=
  (Finset.range (2 * Λ + 1)).sum fun n => 1 / (2 * resolventFreq L mass n * L)

/-- The Wick constant is strictly positive. -/
theorem cylinderWickConstant_pos (mass : ℝ) (hmass : 0 < mass) (Λ : ℕ) :
    0 < cylinderWickConstant L mass Λ := by
  unfold cylinderWickConstant
  apply Finset.sum_pos
  · intro n _
    apply div_pos one_pos
    apply mul_pos
    · apply mul_pos
      · norm_num
      · exact resolventFreq_pos L mass hmass n
    · exact hL.out
  · exact ⟨0, Finset.mem_range.mpr (by omega)⟩

/-! ## Cylinder interaction functional

The interaction functional `V_{Λ,T}` maps a field configuration
`ω ∈ Configuration(CylinderTestFunction L)` to the integrated Wick-ordered
interaction energy:

  `V_{Λ,T}(ω) = ∫_{S¹_L × [-T,T]} :P(φ_Λ(θ,t)(ω)):_{c_Λ} dθ dt`

where `φ_Λ` is the UV-regularized field with spatial mode cutoff Λ and
`c_Λ = cylinderWickConstant L mass Λ` is the Wick constant.

This uses `wickPolynomial P c_Λ` from `Pphi2.WickOrdering.WickPolynomial`
for the Wick-ordered polynomial evaluation. -/

/-- **Cylinder interaction functional** `V_{Λ,T}`.

The integrated Wick-ordered interaction with UV cutoff Λ (spatial mode
truncation) and IR cutoff T (temporal extent [-T, T]):

  `V_{Λ,T}(ω) = ∫_{S¹_L × [-T,T]} :P(φ_Λ(x)):_{c_Λ} dx`

**Future proof target**: Define concretely via spatial Fourier mode projection
and integration over the compact domain S¹_L × [-T, T]. -/
axiom cylinderInteractionFunctional
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    Configuration (CylinderTestFunction L) → ℝ

/-- The interaction functional is measurable. -/
axiom cylinderInteractionFunctional_measurable
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    Measurable (cylinderInteractionFunctional L P Λ T mass hT hmass)

/-- **Nelson's bound**: the interaction functional is bounded below.

  `∃ B, ∀ ω, V_{Λ,T}(ω) ≥ -B`

For fixed UV cutoff Λ and IR cutoff T, the bound follows from
`wickPolynomial_bounded_below` applied pointwise and integrated over
the compact domain S¹_L × [-T,T]. -/
axiom cylinderInteractionFunctional_bounded_below
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    ∃ B : ℝ, ∀ ω : Configuration (CylinderTestFunction L),
    cylinderInteractionFunctional L P Λ T mass hT hmass ω ≥ -B

/-! ## Boltzmann weight and partition function -/

/-- **Boltzmann weight** `exp(-V_{Λ,T})` for the P(φ)₂ interaction. -/
def cylinderBoltzmannWeight
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    Configuration (CylinderTestFunction L) → ℝ :=
  fun ω => Real.exp (-(cylinderInteractionFunctional L P Λ T mass hT hmass ω))

/-- The Boltzmann weight is strictly positive everywhere. -/
theorem cylinderBoltzmannWeight_pos
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    (ω : Configuration (CylinderTestFunction L)) :
    0 < cylinderBoltzmannWeight L P Λ T mass hT hmass ω :=
  Real.exp_pos _

/-- **Integrability of the Boltzmann weight** with respect to the free
Gaussian measure on the cylinder.

Follows from V bounded below (so exp(-V) ≤ exp(B)) and the Gaussian
measure being a probability measure (finite total mass). -/
theorem cylinderBoltzmannWeight_integrable
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    Integrable
      (cylinderBoltzmannWeight L P Λ T mass hT hmass)
      (GaussianField.measure (cylinderMassOperator L mass hmass)) := by
  obtain ⟨B, hB⟩ := cylinderInteractionFunctional_bounded_below L P Λ T mass hT hmass
  have hmeas : Measurable (cylinderBoltzmannWeight L P Λ T mass hT hmass) :=
    (cylinderInteractionFunctional_measurable L P Λ T mass hT hmass).neg.exp
  apply (memLp_of_bounded (a := 0) (b := Real.exp B)
    (ae_of_all _ (fun ω => ?_)) hmeas.aestronglyMeasurable (p := 1)).integrable le_rfl
  exact ⟨le_of_lt (cylinderBoltzmannWeight_pos L P Λ T mass hT hmass ω),
    Real.exp_le_exp_of_le (by linarith [hB ω])⟩

/-- **Partition function** `Z_{Λ,T}` for P(φ)₂ on the cylinder.

  `Z = ∫ exp(-V_{Λ,T}(ω)) dμ_free(ω)` -/
def cylinderPartitionFunction
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) : ℝ :=
  ∫ ω, cylinderBoltzmannWeight L P Λ T mass hT hmass ω
    ∂(GaussianField.measure (cylinderMassOperator L mass hmass))

/-- The partition function is strictly positive.

Proof: `exp(-V) > 0` everywhere, so its support is `univ`. The Gaussian
measure is a probability measure with `μ(univ) = 1 > 0`. By
`integral_pos_iff_support_of_nonneg`, the integral is positive. -/
theorem cylinderPartitionFunction_pos
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    0 < cylinderPartitionFunction L P Λ T mass hT hmass := by
  unfold cylinderPartitionFunction
  rw [integral_pos_iff_support_of_nonneg
    (fun ω => le_of_lt (cylinderBoltzmannWeight_pos L P Λ T mass hT hmass ω))
    (cylinderBoltzmannWeight_integrable L P Λ T mass hT hmass)]
  have h_support : Function.support (cylinderBoltzmannWeight L P Λ T mass hT hmass) = Set.univ := by
    ext ω
    simp [Function.mem_support,
      ne_of_gt (cylinderBoltzmannWeight_pos L P Λ T mass hT hmass ω)]
  rw [h_support, measure_univ]
  norm_num

/-! ## Interacting measure and Schwinger functions -/

/-- **P(φ)₂ interacting measure** on the cylinder.

  `dμ_V = (1/Z) · exp(-V) · dμ_free`

In the limits Λ → ∞ (UV) and T → ∞ (IR), the resulting theory should
converge to the full P(φ)₂ QFT on S¹_L × ℝ. -/
def cylinderInteractingMeasure
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    @Measure (Configuration (CylinderTestFunction L)) instMeasurableSpaceConfiguration :=
  (ENNReal.ofReal (cylinderPartitionFunction L P Λ T mass hT hmass))⁻¹ •
    (GaussianField.measure (cylinderMassOperator L mass hmass)).withDensity
      (fun ω => ENNReal.ofReal (cylinderBoltzmannWeight L P Λ T mass hT hmass ω))

/-- The Boltzmann weight is measurable (as an ENNReal-valued function). -/
theorem cylinderBoltzmannWeight_ennreal_measurable
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    @Measurable _ _ instMeasurableSpaceConfiguration _
      (fun ω => ENNReal.ofReal (cylinderBoltzmannWeight L P Λ T mass hT hmass ω)) :=
  (cylinderInteractionFunctional_measurable L P Λ T mass hT hmass).neg.exp.ennreal_ofReal

/-- The withDensity measure for the Boltzmann weight has finite mass equal to Z. -/
theorem cylinderWithDensity_mass
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    (GaussianField.measure (cylinderMassOperator L mass hmass)).withDensity
      (fun ω => ENNReal.ofReal (cylinderBoltzmannWeight L P Λ T mass hT hmass ω))
      Set.univ =
    ENNReal.ofReal (cylinderPartitionFunction L P Λ T mass hT hmass) := by
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ, MeasureTheory.setLIntegral_univ]
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (cylinderBoltzmannWeight_integrable L P Λ T mass hT hmass)
    (ae_of_all _ fun ω =>
      le_of_lt (cylinderBoltzmannWeight_pos L P Λ T mass hT hmass ω))).symm

/-- **The interacting measure is a probability measure.**

  `μ_V(univ) = (1/Z) · Z = 1` -/
instance cylinderInteractingMeasure_isProbabilityMeasure
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    @IsProbabilityMeasure _ instMeasurableSpaceConfiguration
      (cylinderInteractingMeasure L P Λ T mass hT hmass) := by
  constructor
  show (cylinderInteractingMeasure L P Λ T mass hT hmass) Set.univ = 1
  simp only [cylinderInteractingMeasure, Measure.smul_apply, smul_eq_mul]
  rw [cylinderWithDensity_mass]
  exact ENNReal.inv_mul_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr (cylinderPartitionFunction_pos L P Λ T mass hT hmass))
    ENNReal.ofReal_ne_top

/-- **Two-point Schwinger function** for the interacting theory.

  `S₂(f, g) = ∫ ω(f) · ω(g) dμ_V(ω)` -/
def cylinderSchwinger2
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    (f g : CylinderTestFunction L) : ℝ :=
  ∫ ω : Configuration (CylinderTestFunction L),
    ω f * ω g ∂(cylinderInteractingMeasure L P Λ T mass hT hmass)

/-- The two-point Schwinger function is symmetric. -/
theorem cylinderSchwinger2_symm
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    (f g : CylinderTestFunction L) :
    cylinderSchwinger2 L P Λ T mass hT hmass f g =
    cylinderSchwinger2 L P Λ T mass hT hmass g f := by
  simp only [cylinderSchwinger2]
  congr 1 with ω
  ring

/-- The **one-point Schwinger function** (expectation value of the field). -/
def cylinderSchwinger1
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    (f : CylinderTestFunction L) : ℝ :=
  ∫ ω : Configuration (CylinderTestFunction L),
    ω f ∂(cylinderInteractingMeasure L P Λ T mass hT hmass)

/-- The **interacting generating functional** (moment generating function).

  `Z_V(f) = ∫ exp(ω(f)) dμ_V(ω)` -/
def cylinderInteractingGeneratingFunctional
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    (f : CylinderTestFunction L) : ℝ :=
  ∫ ω : Configuration (CylinderTestFunction L),
    Real.exp (ω f) ∂(cylinderInteractingMeasure L P Λ T mass hT hmass)

/-- The Schwinger function formula via the free measure.

  `S₂(f, g) = (1/Z) ∫ ω(f) · ω(g) · exp(-V(ω)) dμ_free(ω)` -/
theorem cylinderSchwinger2_eq_free_expectation
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    (f g : CylinderTestFunction L) :
    cylinderSchwinger2 L P Λ T mass hT hmass f g =
    (cylinderPartitionFunction L P Λ T mass hT hmass)⁻¹ *
    ∫ ω, ω f * ω g * cylinderBoltzmannWeight L P Λ T mass hT hmass ω
      ∂(GaussianField.measure (cylinderMassOperator L mass hmass)) := by
  simp only [cylinderSchwinger2, cylinderInteractingMeasure]
  rw [integral_smul_measure]
  congr 1
  · simp [ENNReal.toReal_inv, ENNReal.toReal_ofReal
      (le_of_lt (cylinderPartitionFunction_pos L P Λ T mass hT hmass))]
  · rw [integral_withDensity_eq_integral_toReal_smul₀
        (cylinderBoltzmannWeight_ennreal_measurable L P Λ T mass hT hmass).aemeasurable
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    congr 1 with ω
    rw [ENNReal.toReal_ofReal
      (le_of_lt (cylinderBoltzmannWeight_pos L P Λ T mass hT hmass ω)),
      smul_eq_mul, mul_comm]

end Pphi2
