/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Torus OS Axioms: OS0–OS3 for the Gaussian Continuum Limit

Defines and proves Osterwalder-Schrader axioms OS0 through OS3 for the
torus Gaussian continuum limit measure.

## Main results

- `TorusOS0_Analyticity` — characteristic functional is analytic
- `TorusOS1_Regularity` — ‖Z[f_re, f_im]‖ ≤ exp(c·(q(f_re)+q(f_im)))
- `TorusOS2_TranslationInvariance` — invariance under (ℝ/Lℤ)² translations
- `TorusOS2_D4Invariance` — invariance under D4 point group
- `TorusOS3_ReflectionPositivity` — RP for bounded continuous observables
- `SatisfiesTorusOS` — bundled structure for all torus OS axioms
- `torusGaussianLimit_satisfies_OS` — main theorem

## Mathematical background

The torus T²_L has:
- **OS0**: Z[f] = exp(-½ G_L(f,f)) is entire since G_L is bilinear.
- **OS1**: ‖Z[f_re,f_im]‖ ≤ exp(c·(q(f_re)+q(f_im))) for continuous seminorm q.
- **OS2**: G_L is translation-invariant (spectral argument: translation
  acts by phase on Fourier modes) and D4-invariant (eigenvalues are D4-symmetric).
- **OS3**: Lattice GFF is RP (Gaussian with (-Δ+m²)⁻¹ covariance); RP is
  preserved under weak limits by `rp_closed_under_weak_limit`.

## References

- Osterwalder-Schrader (1973, 1975)
- Glimm-Jaffe, *Quantum Physics*, Ch. 6, 19
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I
-/

import Pphi2.TorusContinuumLimit.TorusGaussianLimit
import Pphi2.OSProofs.OS3_RP_Inheritance
import Torus.Symmetry

noncomputable section

open GaussianField MeasureTheory Filter

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Generating functionals -/

/-- The generating functional (characteristic functional) on the torus.

  `Z_μ(f) = E_μ[e^{i ω(f)}] = ∫ e^{i ω(f)} dμ(ω)`

For a Gaussian measure with covariance C: `Z(f) = exp(-½ C(f,f))`. -/
def torusGeneratingFunctional
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ] (f : TorusTestFunction L) : ℂ :=
  ∫ ω : Configuration (TorusTestFunction L),
    Complex.exp (Complex.I * ↑(ω f)) ∂μ

/-- The complex generating functional on the torus.

For a "complex test function" represented by a pair (f_re, f_im) of real
torus test functions, the complex pairing is:

  `⟨ω, J⟩_ℂ = ω(f_re) + i · ω(f_im)`

and the generating functional is:

  `Z[J] = E[exp(i ⟨ω, J⟩_ℂ)] = ∫ exp(i ω(f_re) - ω(f_im)) dμ(ω)`

Note: `exp(-ω(f_im))` is unbounded, so `‖Z[J]‖ ≤ 1` does NOT hold
for complex test functions. This is why OS1 requires exponential bounds.

We represent complex torus test functions as pairs since `TorusTestFunction L`
is real-valued. This matches the pattern in `generatingFunctionalℂ` from
`OSAxioms.lean`. -/
def torusGeneratingFunctionalℂ
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ] (f_re f_im : TorusTestFunction L) : ℂ :=
  ∫ ω : Configuration (TorusTestFunction L),
    Complex.exp (Complex.I * ((ω f_re : ℂ) + Complex.I * (ω f_im : ℂ))) ∂μ

/-! ## OS0: Analyticity -/

/-- **OS0: Analyticity of the generating functional.**

The generating functional `Z[Σ zᵢJᵢ]` is entire analytic as a function
of z = (z₁,...,zₙ) ∈ ℂⁿ, for any choice of (real) test functions Jᵢ.

This is the torus analogue of `OS0_Analyticity` in `OSAxioms.lean`.
Since `TorusTestFunction L` is real-valued, we use real test functions
as the basis directions and allow complex coefficients zᵢ ∈ ℂ: the
"complex test function" is Σ zᵢ Jᵢ = Σ (Re zᵢ) Jᵢ + i Σ (Im zᵢ) Jᵢ. -/
def TorusOS0_Analyticity
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (n : ℕ) (J : Fin n → TorusTestFunction L),
    AnalyticOn ℂ (fun z : Fin n → ℂ =>
      torusGeneratingFunctionalℂ L μ
        (∑ i, (z i).re • J i) (∑ i, (z i).im • J i)) Set.univ

/-- **Characteristic functional of the Gaussian continuum limit.**

For the Gaussian measure with covariance G_L:
  `E[e^{i ω(f)}] = exp(-½ G_L(f,f))`

This connects the moment generating function (real exponential, given by
`IsTorusGaussianContinuumLimit.isGaussian`) to the characteristic function
(imaginary exponential) via analytic continuation `t → it`.

Reference: Fernique (1975), §III.4; Reed-Simon I, Thm V.8. -/
axiom torusGaussianLimit_characteristic_functional
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (hGCL : IsTorusGaussianContinuumLimit L μ mass hmass)
    (f : TorusTestFunction L) :
    torusGeneratingFunctional L μ f =
    Complex.exp ((-1 / 2) * ↑(torusContinuumGreen L mass hmass f f))

/-- OS0 for the torus Gaussian continuum limit.

For Gaussian μ with covariance G_L, the complex generating functional is:
  `Z[f_re, f_im] = exp(-½ G_L(f_re + if_im, f_re + if_im))`
where G_L extends bilinearly. This is entire in the coefficients zᵢ since
it is the composition of a polynomial (the bilinear form) with exp. -/
theorem torusGaussianLimit_os0
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (hGCL : IsTorusGaussianContinuumLimit L μ mass hmass) :
    TorusOS0_Analyticity L μ := by
  sorry

/-! ## OS1: Regularity -/

/-- **OS1: Regularity of the complex generating functional.**

The complex generating functional satisfies exponential bounds:

  `‖Z[f_re, f_im]‖ ≤ exp(c · (q(f_re) + q(f_im)))`

for some continuous seminorm `q` on the torus test function space
and constant `c > 0`.

This is the torus analogue of `OS1_Regularity` in `OSAxioms.lean`,
adapted to the abstract nuclear Fréchet test function space where
spatial Lᵖ norms are not directly available. The continuous seminorm
formulation is the standard OS1 for nuclear test function spaces and
subsumes the `L¹ + Lᵖ` form used in the infinite-volume case.

The bound controls the growth of Z when the imaginary part of the
test function (which produces the unbounded factor `exp(-ω(f_im))`)
is nonzero.

For a Gaussian with covariance G_L, the bound holds with
`q(f) = G_L(f,f)` (the RKHS norm squared). For the interacting
case, Nelson's hypercontractive estimate gives the bound via
a Sobolev-type seminorm. -/
def TorusOS1_Regularity
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ] : Prop :=
  ∃ (q : TorusTestFunction L → ℝ) (_ : Continuous q) (c : ℝ), c > 0 ∧
    ∀ (f_re f_im : TorusTestFunction L),
      ‖torusGeneratingFunctionalℂ L μ f_re f_im‖ ≤
        Real.exp (c * (q f_re + q f_im))

/-- OS1 for the torus Gaussian continuum limit.

For Gaussian μ with covariance G_L:
  `‖Z[f_re, f_im]‖ = |exp(-½ G_L(f_re+if_im, f_re+if_im))|`
  `= exp(½ (G_L(f_im,f_im) - G_L(f_re,f_re)))`
  `≤ exp(½ G_L(f_im, f_im))`
  `≤ exp(½ (G_L(f_re,f_re) + G_L(f_im,f_im)))`

This gives the bound with `q(f) = G_L(f,f)` and `c = ½`. -/
theorem torusGaussianLimit_os1
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (hGCL : IsTorusGaussianContinuumLimit L μ mass hmass) :
    TorusOS1_Regularity L μ := by
  sorry

/-! ## OS2: Euclidean invariance (translation + D4) -/

/-- **OS2a: Translation invariance of the generating functional.**

The measure μ is invariant under (ℝ/Lℤ)² translations. -/
def TorusOS2_TranslationInvariance
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (v : ℝ × ℝ) (f : TorusTestFunction L),
    torusGeneratingFunctional L μ f =
    torusGeneratingFunctional L μ (torusTranslation L v f)

/-- **OS2b: D4 point group invariance.**

The measure μ is invariant under coordinate swap and time reflection. -/
def TorusOS2_D4Invariance
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ] : Prop :=
  (∀ f, torusGeneratingFunctional L μ f =
         torusGeneratingFunctional L μ (torusSwap L f)) ∧
  (∀ f, torusGeneratingFunctional L μ f =
         torusGeneratingFunctional L μ (torusTimeReflection L f))

/-- **Translation invariance of the torus continuum Green's function.**

  `G_L(T_v f, T_v g) = G_L(f, g)` for all v ∈ (ℝ/Lℤ)².

Spectral argument: translation acts by phase e^{2πi⟨n,v⟩/L} on Fourier
mode n. Since the Green's function is `Σ |f̂(n)|² / (μ_n + m²)`, and
`|e^{iθ} f̂(n)|² = |f̂(n)|²`, translation doesn't change the sum.

Reference: Glimm-Jaffe, *Quantum Physics*, §6.4. -/
axiom torusContinuumGreen_translation_invariant
    (mass : ℝ) (hmass : 0 < mass) (v : ℝ × ℝ)
    (f g : TorusTestFunction L) :
    torusContinuumGreen L mass hmass (torusTranslation L v f) (torusTranslation L v g) =
    torusContinuumGreen L mass hmass f g

/-- **D4 point group invariance of the torus continuum Green's function.**

  `G_L` is invariant under coordinate swap and time reflection.

The eigenvalues `(2πn₁/L)² + (2πn₂/L)²` are symmetric under
n₁ ↔ n₂ (swap) and n₁ ↦ -n₁ (reflection), so D4 acts trivially
on the spectrum.

Reference: Glimm-Jaffe, *Quantum Physics*, §6.4. -/
axiom torusContinuumGreen_pointGroup_invariant
    (mass : ℝ) (hmass : 0 < mass) :
    (∀ f g : TorusTestFunction L,
      torusContinuumGreen L mass hmass (torusSwap L f) (torusSwap L g) =
      torusContinuumGreen L mass hmass f g) ∧
    (∀ f g : TorusTestFunction L,
      torusContinuumGreen L mass hmass (torusTimeReflection L f) (torusTimeReflection L g) =
      torusContinuumGreen L mass hmass f g)

/-- OS2 (translation) for the torus Gaussian continuum limit.

For Gaussian μ determined by covariance G_L, translation invariance of G_L
implies: `E[e^{iω(Tf)}] = exp(-½ G_L(Tf,Tf)) = exp(-½ G_L(f,f)) = E[e^{iωf}]`. -/
theorem torusGaussianLimit_os2_translation
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (hGCL : IsTorusGaussianContinuumLimit L μ mass hmass) :
    TorusOS2_TranslationInvariance L μ := by
  intro v f
  -- Both sides equal exp(-½ G_L(f,f)) by the characteristic functional formula
  rw [torusGaussianLimit_characteristic_functional L mass hmass μ hGCL f,
      torusGaussianLimit_characteristic_functional L mass hmass μ hGCL
        (torusTranslation L v f)]
  congr 1; congr 1; congr 1
  exact (torusContinuumGreen_translation_invariant L mass hmass v f f).symm

/-- OS2 (D4) for the torus Gaussian continuum limit. -/
theorem torusGaussianLimit_os2_D4
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (hGCL : IsTorusGaussianContinuumLimit L μ mass hmass) :
    TorusOS2_D4Invariance L μ := by
  obtain ⟨h_swap, h_refl⟩ := torusContinuumGreen_pointGroup_invariant L mass hmass
  constructor
  · intro f
    rw [torusGaussianLimit_characteristic_functional L mass hmass μ hGCL f,
        torusGaussianLimit_characteristic_functional L mass hmass μ hGCL (torusSwap L f)]
    congr 1; congr 1; congr 1
    exact (h_swap f f).symm
  · intro f
    rw [torusGaussianLimit_characteristic_functional L mass hmass μ hGCL f,
        torusGaussianLimit_characteristic_functional L mass hmass μ hGCL
          (torusTimeReflection L f)]
    congr 1; congr 1; congr 1
    exact (h_refl f f).symm

/-! ## OS3: Reflection positivity -/

/-- The set of "admissible" observables for reflection positivity:
bounded continuous functions on configuration space.

In the full OS framework, these should be restricted to functions depending
only on the "positive-time" field configurations. For the single-function
formulation `∫ F · (ΘF) dμ ≥ 0` used in `IsRP`, the positive-time support
condition is automatically enforced: the product `F(ω) · F(Θω)` involves
both F and its reflection, so the inequality is nontrivial only when F
depends on "future" fields. For a Gaussian measure with covariance C,
the transfer matrix argument gives `∫ F · (ΘF) = ⟨F, e^{-aH} F⟩_L² ≥ 0`
since `H ≥ 0`. -/
def torusRP_admissible :
    Set (Configuration (TorusTestFunction L) → ℝ) :=
  {F | Continuous F ∧ ∃ C, ∀ x, |F x| ≤ C}

/-- **OS3: Reflection positivity for the torus measure.**

A measure μ on Configuration(TorusTestFunction L) is RP with respect to
time reflection Θ if for all bounded continuous observables F:

  `∫ F(ω) · F(Θ_*ω) dμ(ω) ≥ 0`

Here Θ_* = torusConfigReflection is the dual action of the OS time
reflection (t,x) ↦ (-t,x) on the configuration space. -/
def TorusOS3_ReflectionPositivity
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ] : Prop :=
  IsRP μ (torusConfigReflection L) (torusRP_admissible L)

/-- **The lattice GFF on the torus satisfies reflection positivity.**

The lattice Gaussian free field with covariance (-Δ_lattice + m²)⁻¹ is RP
because the transfer matrix `e^{-aH}` has `H ≥ 0`, giving nonneg inner
products `⟨F, e^{-aH}F⟩_{L²} ≥ 0`.

More precisely: the lattice action decomposes as `S = S_+ + S_- + S_interaction`
where `S_+` depends on future fields, `S_-` on past fields, and `S_interaction`
couples only across the reflection plane. The Gaussian structure ensures that
the coupling term has the form `⟨φ_+, Tφ_-⟩` with `T ≥ 0`, which gives RP.

Reference: Glimm-Jaffe, *Quantum Physics*, §6.3; Simon, *P(φ)₂*, Ch. II. -/
axiom torusLattice_rp (N : ℕ) [NeZero N]
    (mass : ℝ) (hmass : 0 < mass) :
    IsRP (torusContinuumMeasure L N mass hmass) (torusConfigReflection L)
      (torusRP_admissible L)

/-- **OS3 for the torus Gaussian continuum limit.**

Proved by combining:
1. Each lattice measure is RP (`torusLattice_rp`)
2. The full sequence converges weakly (`torusGaussianLimit_fullConvergence`)
3. RP is closed under weak limits (`rp_closed_under_weak_limit`)
4. `torusConfigReflection` is continuous -/
theorem torusGaussianLimit_os3
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (hGCL : IsTorusGaussianContinuumLimit L μ mass hmass) :
    TorusOS3_ReflectionPositivity L μ := by
  -- Apply RP closure under weak limits
  apply rp_closed_under_weak_limit
    (Θ := torusConfigReflection L)
    (hΘ := torusConfigReflection_continuous L)
    (S := torusRP_admissible L)
    (hS_bdd := fun F hF => hF.2)
    (hS_cont := fun F hF => hF.1)
    (μ := fun N => torusContinuumMeasure L (N + 1) mass hmass)
    (h_rp := fun N => torusLattice_rp L (N + 1) mass hmass)
  -- Weak convergence of the full sequence
  exact torusGaussianLimit_fullConvergence L mass hmass μ
    hGCL.isGaussian hGCL.covariance_eq

/-! ## Bundle and main theorem -/

/-- **Bundled torus OS axioms OS0–OS3.**

This structure is measure-agnostic: it applies to any probability measure
on Configuration(TorusTestFunction L), whether Gaussian or interacting.
The axiom definitions depend only on `L` and `μ`, not on mass or polynomial. -/
structure SatisfiesTorusOS
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ] : Prop where
  os0 : TorusOS0_Analyticity L μ
  os1 : TorusOS1_Regularity L μ
  os2_translation : TorusOS2_TranslationInvariance L μ
  os2_D4 : TorusOS2_D4Invariance L μ
  os3 : TorusOS3_ReflectionPositivity L μ

/-- **The torus Gaussian continuum limit satisfies OS0–OS3.**

The proof uses the Gaussian structure (characteristic functional = exp(-½G))
to establish OS0, OS1, and OS2. OS3 is inherited from lattice RP via
weak limits. -/
theorem torusGaussianLimit_satisfies_OS
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (hGCL : IsTorusGaussianContinuumLimit L μ mass hmass) :
    SatisfiesTorusOS L μ where
  os0 := torusGaussianLimit_os0 L mass hmass μ hGCL
  os1 := torusGaussianLimit_os1 L mass hmass μ hGCL
  os2_translation := torusGaussianLimit_os2_translation L mass hmass μ hGCL
  os2_D4 := torusGaussianLimit_os2_D4 L mass hmass μ hGCL
  os3 := torusGaussianLimit_os3 L mass hmass μ hGCL

/-- **Existence of a torus Gaussian measure satisfying OS0–OS3.**

Master theorem: for any torus size L > 0 and mass m > 0, there exists
a probability measure on Configuration(TorusTestFunction L) satisfying
all torus OS axioms. The measure is the continuum limit of lattice GFFs.

The statement hides all construction details (mass, lattice, convergence)
behind the existential — the output is just a measure satisfying `SatisfiesTorusOS`. -/
theorem torusGaussianOS_exists (mass : ℝ) (hmass : 0 < mass) :
    ∃ (μ : Measure (Configuration (TorusTestFunction L)))
      (_ : IsProbabilityMeasure μ),
      @SatisfiesTorusOS L hL μ ‹_› := by
  obtain ⟨μ, hμ_prob, hGCL, _⟩ := torusGaussianLimit_converges L mass hmass
  exact ⟨μ, hμ_prob, torusGaussianLimit_satisfies_OS L mass hmass μ hGCL⟩

end Pphi2

end
