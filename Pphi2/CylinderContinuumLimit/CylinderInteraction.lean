/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# P(φ)₂ Interaction on the Cylinder S¹_L × ℝ

Defines the Wick-ordered interaction potential on the cylinder and instantiates
the general interacting measure framework from `InteractingMeasure.General`.

## Main definitions

- `cylinderWickConstant L mass Λ` — UV-regularized single-point variance
- `cylinderInteractionFunctional` — interaction V_{Λ,T} on field configurations
- `cylinderInteractingMeasure` — interacting measure via general framework
- `cylinderSchwinger2` — two-point Schwinger function via general framework

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
import Pphi2.InteractingMeasure.General
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

/-! ## Cylinder-specific abbreviations

The cylinder interacting measure, Schwinger functions, etc. are instances
of the general framework in `Pphi2.InteractingMeasure.General`, applied
to the cylinder interaction functional and free Gaussian measure. -/

/-- The cylinder interaction as a `Configuration → ℝ` function (for use
with the general interacting measure framework). -/
abbrev cylinderV (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :=
  cylinderInteractionFunctional L P Λ T mass hT hmass

/-- The free Gaussian measure on the cylinder. -/
abbrev cylinderFreeMeasure (mass : ℝ) (hmass : 0 < mass) :=
  GaussianField.measure (cylinderMassOperator L mass hmass)

/-- **P(φ)₂ interacting measure** on the cylinder.

  `dμ_V = (1/Z) · exp(-V) · dμ_free`

Instance of `interactingMeasure` from the general framework. -/
abbrev cylinderInteractingMeasure
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :=
  interactingMeasure (cylinderV L P Λ T mass hT hmass)
    (cylinderFreeMeasure L mass hmass)

/-- The interacting measure is a probability measure (from general framework). -/
instance cylinderInteractingMeasure_isProbabilityMeasure
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    IsProbabilityMeasure (cylinderInteractingMeasure L P Λ T mass hT hmass) :=
  interactingMeasure_isProbabilityMeasure
    (cylinderV L P Λ T mass hT hmass)
    (cylinderFreeMeasure L mass hmass)
    (cylinderInteractionFunctional_measurable L P Λ T mass hT hmass)
    (cylinderInteractionFunctional_bounded_below L P Λ T mass hT hmass)

/-- **Two-point Schwinger function** for the interacting theory.

  `S₂(f, g) = ∫ ω(f) · ω(g) dμ_V(ω)` -/
abbrev cylinderSchwinger2
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    (f g : CylinderTestFunction L) : ℝ :=
  schwinger2 (cylinderV L P Λ T mass hT hmass)
    (cylinderFreeMeasure L mass hmass) f g

/-- The two-point Schwinger function is symmetric (from general framework). -/
theorem cylinderSchwinger2_symm
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    (f g : CylinderTestFunction L) :
    cylinderSchwinger2 L P Λ T mass hT hmass f g =
    cylinderSchwinger2 L P Λ T mass hT hmass g f :=
  schwinger2_symm _ _ f g

/-- The **one-point Schwinger function** (expectation value of the field). -/
abbrev cylinderSchwinger1
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    (f : CylinderTestFunction L) : ℝ :=
  schwinger1 (cylinderV L P Λ T mass hT hmass)
    (cylinderFreeMeasure L mass hmass) f

/-- The **interacting generating functional** (moment generating function). -/
abbrev cylinderInteractingGeneratingFunctional
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    (f : CylinderTestFunction L) : ℝ :=
  interactingGeneratingFunctional (cylinderV L P Λ T mass hT hmass)
    (cylinderFreeMeasure L mass hmass) f

/-- The Schwinger function formula via the free measure (from general framework).

  `S₂(f, g) = (1/Z) ∫ ω(f) · ω(g) · exp(-V(ω)) dμ_free(ω)` -/
theorem cylinderSchwinger2_eq_free_expectation
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    (f g : CylinderTestFunction L) :
    cylinderSchwinger2 L P Λ T mass hT hmass f g =
    (interactingPartitionFunction (cylinderV L P Λ T mass hT hmass)
      (cylinderFreeMeasure L mass hmass))⁻¹ *
    ∫ ω, ω f * ω g * interactingBoltzmannWeight
      (cylinderV L P Λ T mass hT hmass) ω
      ∂(cylinderFreeMeasure L mass hmass) :=
  schwinger2_eq_free_expectation _ _
    (cylinderInteractionFunctional_measurable L P Λ T mass hT hmass)
    (cylinderInteractionFunctional_bounded_below L P Λ T mass hT hmass) f g

/-- The two-point Schwinger function is nonneg: `S₂(f, f) ≥ 0` (from general framework). -/
theorem cylinderSchwinger2_nonneg
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    (f : CylinderTestFunction L) :
    0 ≤ cylinderSchwinger2 L P Λ T mass hT hmass f f :=
  schwinger2_nonneg _ _ f

/-- **n-point cylinder Schwinger function** (from general framework). -/
abbrev cylinderSchwingerN
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    {n : ℕ} (f : Fin n → CylinderTestFunction L) : ℝ :=
  schwingerN (cylinderV L P Λ T mass hT hmass)
    (cylinderFreeMeasure L mass hmass) f

/-- The 0-point cylinder Schwinger function equals 1 (from general framework). -/
theorem cylinderSchwingerN_zero
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    cylinderSchwingerN L P Λ T mass hT hmass Fin.elim0 = 1 :=
  schwingerN_zero _ _
    (cylinderInteractionFunctional_measurable L P Λ T mass hT hmass)
    (cylinderInteractionFunctional_bounded_below L P Λ T mass hT hmass)

/-- The n-point Schwinger function is permutation-invariant (from general framework). -/
theorem cylinderSchwingerN_perm
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    {n : ℕ} (f : Fin n → CylinderTestFunction L) (σ : Equiv.Perm (Fin n)) :
    cylinderSchwingerN L P Λ T mass hT hmass (f ∘ σ) =
    cylinderSchwingerN L P Λ T mass hT hmass f :=
  schwingerN_perm _ _ f σ

/-- The interacting measure is absolutely continuous w.r.t. the free measure. -/
theorem cylinderInteractingMeasure_absolutelyContinuous
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    cylinderInteractingMeasure L P Λ T mass hT hmass ≪
    cylinderFreeMeasure L mass hmass :=
  interactingMeasure_absolutelyContinuous _ _

end Pphi2
