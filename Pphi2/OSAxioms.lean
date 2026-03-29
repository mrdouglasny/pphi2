/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Measure-level Osterwalder-Schrader axioms for `P(Φ)₂`

Defines the measure-level OS axiom framework for the Glimm-Jaffe/Nelson lattice
construction. The axioms here are stated for probability measures on
`S'(ℝ²) = Configuration (ContinuumTestFunction 2)`.

This is intentionally the most concrete Euclidean layer in the repo: stronger
than the original Osterwalder-Schrader Schwinger-function formulation, and not
meant as a universal definition of QFT. The long-term architecture is to factor
these measure-level axioms through a shared abstract Schwinger/reconstruction
interface in `Common.QFT.*`.

The concrete formulas match those in `OSforGFF/OS_Axioms.lean`, adapted from
`d = 4` to `d = 2`.

## The five OS axioms

- **OS0 (Analyticity):** Z[Σ zᵢfᵢ] is entire analytic in z ∈ ℂⁿ.
- **OS1 (Regularity):** |Z[f]| ≤ exp(c(‖f‖₁ + ‖f‖ₚᵖ)).
- **OS2 (Euclidean Invariance):** Z[g·f] = Z[f] for g ∈ E(2).
- **OS3 (Reflection Positivity):** RP matrix is positive semidefinite.
- **OS4 (Clustering):** Z[f + T_a g] → Z[f]·Z[g] as |a| → ∞.

## References

- Osterwalder-Schrader (1973, 1975), Axiom formulation and reconstruction
- Glimm-Jaffe, *Quantum Physics*, Ch. 6, pp. 89–90
- Simon, *The P(φ)₂ Euclidean QFT*
-/

import Pphi2.ContinuumLimit.AxiomInheritance
import Mathlib.Analysis.Analytic.Basic

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

/-! ## Spacetime and test function setup for d=2 -/

/-- Spacetime for P(Φ)₂: Euclidean ℝ². -/
abbrev SpaceTime2 := EuclideanSpace ℝ (Fin 2)

/-- Real test functions: S(ℝ²). Same as `ContinuumTestFunction 2`. -/
abbrev TestFunction2 := ContinuumTestFunction 2

/-- Complex test functions: S(ℝ², ℂ). -/
abbrev TestFunction2ℂ := SchwartzMap SpaceTime2 ℂ

/-- Field configurations: S'(ℝ²) = WeakDual ℝ S(ℝ²). -/
abbrev FieldConfig2 := Configuration (ContinuumTestFunction 2)

/-- The distribution pairing ⟨ω, f⟩ for ω ∈ S'(ℝ²), f ∈ S(ℝ²). -/
def distribPairing (ω : FieldConfig2) (f : TestFunction2) : ℝ := ω f


/-! ## Generating functional -/

/-- The generating functional Z[f] = ∫ exp(i⟨ω, f⟩) dμ(ω).

This is the fundamental object in constructive QFT. For real test
functions f, this equals the characteristic function of the measure μ
evaluated at f. Following Glimm-Jaffe notation. -/
def generatingFunctional
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (f : TestFunction2) : ℂ :=
  ∫ ω : FieldConfig2, Complex.exp (Complex.I * ↑(ω f)) ∂μ

/-- Extract the real part of a complex Schwartz function as a real Schwartz function.

Given J : S(ℝ², ℂ), returns Re(J) : S(ℝ², ℝ) defined pointwise by x ↦ (J x).re.
Uses composition with `Complex.reCLM : ℂ →L[ℝ] ℝ`. -/
def schwartzRe (J : TestFunction2ℂ) : TestFunction2 :=
  SchwartzMap.mk (fun x => (J x).re)
    (Complex.reCLM.contDiff.comp J.smooth')
    (by
      intro k n
      obtain ⟨C, hC⟩ := J.decay' k n
      use C * ‖Complex.reCLM‖
      intro x
      have h_eq : (fun y => (J y).re) = Complex.reCLM ∘ J.toFun := rfl
      rw [h_eq, ContinuousLinearMap.iteratedFDeriv_comp_left Complex.reCLM
        J.smooth'.contDiffAt (WithTop.coe_le_coe.mpr le_top)]
      calc ‖x‖ ^ k * ‖Complex.reCLM.compContinuousMultilinearMap
              (iteratedFDeriv ℝ n J.toFun x)‖
          ≤ ‖x‖ ^ k * (‖Complex.reCLM‖ * ‖iteratedFDeriv ℝ n J.toFun x‖) :=
            mul_le_mul_of_nonneg_left
              (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _)
              (pow_nonneg (norm_nonneg _) _)
        _ = ‖Complex.reCLM‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n J.toFun x‖) := by ring
        _ ≤ ‖Complex.reCLM‖ * C := mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)
        _ = C * ‖Complex.reCLM‖ := by ring)

/-- Extract the imaginary part of a complex Schwartz function as a real Schwartz function.

Given J : S(ℝ², ℂ), returns Im(J) : S(ℝ², ℝ) defined pointwise by x ↦ (J x).im. -/
def schwartzIm (J : TestFunction2ℂ) : TestFunction2 :=
  SchwartzMap.mk (fun x => (J x).im)
    (Complex.imCLM.contDiff.comp J.smooth')
    (by
      intro k n
      obtain ⟨C, hC⟩ := J.decay' k n
      use C * ‖Complex.imCLM‖
      intro x
      have h_eq : (fun y => (J y).im) = Complex.imCLM ∘ J.toFun := rfl
      rw [h_eq, ContinuousLinearMap.iteratedFDeriv_comp_left Complex.imCLM
        J.smooth'.contDiffAt (WithTop.coe_le_coe.mpr le_top)]
      calc ‖x‖ ^ k * ‖Complex.imCLM.compContinuousMultilinearMap
              (iteratedFDeriv ℝ n J.toFun x)‖
          ≤ ‖x‖ ^ k * (‖Complex.imCLM‖ * ‖iteratedFDeriv ℝ n J.toFun x‖) :=
            mul_le_mul_of_nonneg_left
              (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _)
              (pow_nonneg (norm_nonneg _) _)
        _ = ‖Complex.imCLM‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n J.toFun x‖) := by ring
        _ ≤ ‖Complex.imCLM‖ * C := mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)
        _ = C * ‖Complex.imCLM‖ := by ring)

/-- The complex generating functional Z[J] for J ∈ S(ℝ², ℂ).

For complex J = f + ig with f, g real:
  Z[J] = ∫ exp(i⟨ω, f⟩ - ⟨ω, g⟩) dμ(ω)

This extends the real generating functional to complex test functions,
which is needed for the analyticity axiom (OS0). The complex pairing
⟨ω, J⟩_ℂ = ⟨ω, Re(J)⟩ + i·⟨ω, Im(J)⟩ extends the real distribution
ω ∈ S'(ℝ²) to complex test functions by linearity. -/
def generatingFunctionalℂ
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (J : TestFunction2ℂ) : ℂ :=
  -- ⟨ω, J⟩_ℂ = ⟨ω, Re(J)⟩ + i·⟨ω, Im(J)⟩
  -- Z[J] = ∫ exp(i · ⟨ω, J⟩_ℂ) dμ(ω)
  let f_re := schwartzRe J
  let f_im := schwartzIm J
  ∫ ω : FieldConfig2, Complex.exp (Complex.I * ((ω f_re : ℂ) + Complex.I * (ω f_im : ℂ))) ∂μ

/-! ## Euclidean group E(2) = ℝ² ⋊ O(2) -/

/-- Orthogonal linear isometry equivalences of ℝ² (the group O(2)).
Uses `LinearIsometryEquiv` (not `LinearIsometry`) so the inverse is available. -/
abbrev O2 := SpaceTime2 ≃ₗᵢ[ℝ] SpaceTime2

/-- Euclidean motion in 2D: rotation/reflection R ∈ O(2) + translation t ∈ ℝ². -/
structure E2 where
  R : O2
  t : SpaceTime2

/-- Action of g ∈ E(2) on a spacetime point: g · x = R(x) + t. -/
def E2.act (g : E2) (x : SpaceTime2) : SpaceTime2 := g.R x + g.t

/-- The inverse Euclidean action: `g⁻¹ · x = R⁻¹(x - t)`. -/
private def euclideanInverse (g : E2) (x : SpaceTime2) : SpaceTime2 :=
  g.R.symm (x - g.t)

private lemma euclideanInverse_hasTemperateGrowth (g : E2) :
    (euclideanInverse g).HasTemperateGrowth := by
  have hR := g.R.symm.toContinuousLinearEquiv.hasTemperateGrowth
  have hSub : (fun x : SpaceTime2 => x - g.t).HasTemperateGrowth :=
    ((ContinuousLinearMap.id ℝ SpaceTime2).hasTemperateGrowth).sub
      (Function.HasTemperateGrowth.const g.t)
  convert hR.comp hSub

private lemma euclideanInverse_antilipschitz (g : E2) :
    AntilipschitzWith 1 (euclideanInverse g) :=
  fun x y => by
    simp only [euclideanInverse, ENNReal.coe_one, one_mul]
    calc edist x y
        = edist (x - g.t) (y - g.t) := by rw [edist_sub_right]
      _ = edist (g.R.symm (x - g.t)) (g.R.symm (y - g.t)) :=
          (g.R.symm.isometry.edist_eq _ _).symm
      _ ≤ edist (g.R.symm (x - g.t)) (g.R.symm (y - g.t)) := le_refl _

/-- The pullback action of E(2) on real test functions:
  `(g · f)(x) = f(g⁻¹ · x)` where `g⁻¹ · x = R⁻¹(x - t)`.

Constructed via `compCLMOfAntilipschitz`: the inverse Euclidean action
is an affine isometry, which has temperate growth and is antilipschitz. -/
noncomputable def euclideanAction2 (g : E2) : TestFunction2 →L[ℝ] TestFunction2 :=
  SchwartzMap.compCLMOfAntilipschitz ℝ
    (euclideanInverse_hasTemperateGrowth g) (euclideanInverse_antilipschitz g)

/-- The pullback action on complex test functions. -/
noncomputable def euclideanAction2ℂ (g : E2) : TestFunction2ℂ →L[ℝ] TestFunction2ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℝ
    (euclideanInverse_hasTemperateGrowth g) (euclideanInverse_antilipschitz g)

/-! ## Time reflection -/

/-- Time reflection on ℝ²: (t, x) ↦ (-t, x).

This negates the first coordinate (time) and preserves the second
(space). It is an element of O(2) and an involution. -/
def timeReflection2 (p : SpaceTime2) : SpaceTime2 :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm
    (fun i => if i = 0 then -(WithLp.equiv 2 (Fin 2 → ℝ) p) i
              else (WithLp.equiv 2 (Fin 2 → ℝ) p) i)

/-- Time reflection is an involution: Θ² = id. -/
theorem timeReflection2_involution (p : SpaceTime2) :
    timeReflection2 (timeReflection2 p) = p := by
  simp only [timeReflection2]
  ext i
  simp
  split <;> simp

/-- Time reflection is a linear map on SpaceTime2. -/
def timeReflectionLinear : SpaceTime2 →ₗ[ℝ] SpaceTime2 where
  toFun := timeReflection2
  map_add' p q := by
    ext i
    simp [timeReflection2, WithLp.equiv, Equiv.symm]
    split <;> ring
  map_smul' c p := by
    ext i
    simp [timeReflection2, WithLp.equiv, Equiv.symm, smul_eq_mul]

/-- Time reflection as a continuous linear equivalence (it's an involution). -/
noncomputable def timeReflectionCLE : SpaceTime2 ≃L[ℝ] SpaceTime2 :=
  (LinearEquiv.ofInvolutive timeReflectionLinear
    timeReflection2_involution).toContinuousLinearEquiv

/-- The pullback of time reflection on real test functions:
  `(Θf)(t, x) = f(-t, x)`.

Constructed using `SchwartzMap.compCLMOfContinuousLinearEquiv` from Mathlib,
which composes a Schwartz function with a continuous linear equivalence. -/
noncomputable def compTimeReflection2 : TestFunction2 →L[ℝ] TestFunction2 :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ timeReflectionCLE

/-- Θf agrees with composition: (compTimeReflection2 f)(p) = f(timeReflection2 p). -/
theorem compTimeReflection2_apply (f : TestFunction2) (p : SpaceTime2) :
    compTimeReflection2 f p = f (timeReflection2 p) := rfl

/-- Translation of a real test function by a ∈ ℝ²:
  `(translate a f)(x) = f(x - a)`.

Constructed using `SchwartzMap.compCLMOfAntilipschitz` with the translation map
`x ↦ x - a`, which is an isometry with temperate growth. -/
noncomputable def SchwartzMap.translate (a : SpaceTime2) : TestFunction2 →L[ℝ] TestFunction2 :=
  SchwartzMap.compCLMOfAntilipschitz ℝ
    (show (fun x : SpaceTime2 => x - a).HasTemperateGrowth from
      ((ContinuousLinearMap.id ℝ SpaceTime2).hasTemperateGrowth).sub
        (Function.HasTemperateGrowth.const a))
    (show AntilipschitzWith 1 (fun x : SpaceTime2 => x - a) from
      fun x y => by simp [edist_sub_right])

/-! ## Positive-time test functions -/

/-- A spacetime point has positive time if its first coordinate is positive. -/
def hasPositiveTime2 (p : SpaceTime2) : Prop :=
  (WithLp.equiv 2 (Fin 2 → ℝ) p) 0 > 0

/-- The submodule of real test functions supported at positive time. -/
def positiveTimeSubmodule2 : Submodule ℝ TestFunction2 where
  carrier := { f : TestFunction2 | tsupport f ⊆ { p | hasPositiveTime2 p } }
  zero_mem' := by
    simp only [Set.mem_setOf_eq, tsupport]
    exact (closure_minimal Function.support_zero.subset isClosed_empty).trans (Set.empty_subset _)
  add_mem' := fun {f g} hf hg =>
    (tsupport_add f g).trans (Set.union_subset hf hg)
  smul_mem' := fun c f hf =>
    (tsupport_smul_subset_right (fun _ : SpaceTime2 => c) f).trans hf

/-- Type of real test functions supported at positive time t > 0. -/
abbrev PositiveTimeTestFunction2 := positiveTimeSubmodule2

/-! ## OS Axiom Definitions -/

/-- **OS0 (Analyticity):** The generating functional Z[Σ zᵢfᵢ] is
entire analytic as a function of z = (z₁,...,zₙ) ∈ ℂⁿ, for any
choice of complex test functions f₁,...,fₙ ∈ S(ℝ², ℂ).

This matches OSforGFF.OS0_Analyticity. -/
def OS0_Analyticity
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ] : Prop :=
  ∀ (n : ℕ) (J : Fin n → TestFunction2ℂ),
    AnalyticOn ℂ (fun z : Fin n → ℂ =>
      generatingFunctionalℂ μ (∑ i, z i • J i)) Set.univ

/-- **OS1 (Regularity):** The complex generating functional satisfies
exponential bounds controlled by Schwartz norms.

  `‖Z[J]‖ ≤ exp(c · (‖J‖₁ + ‖J‖_p^p))`

for some 1 ≤ p ≤ 2 and c > 0. When p = 2, this additionally requires
local integrability of the two-point function.

This matches OSforGFF.OS1_Regularity.

For P(Φ)₂, the relevant bound is `‖Z[f]‖ ≤ exp(c · ‖f‖²_{H^{-1}})`
from Nelson's hypercontractive estimate. -/
def OS1_Regularity
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ] : Prop :=
  ∃ (p : ℝ) (c : ℝ), 1 ≤ p ∧ p ≤ 2 ∧ c > 0 ∧
    ∀ (f : TestFunction2ℂ),
      ‖generatingFunctionalℂ μ f‖ ≤
        Real.exp (c * (∫ x, ‖f x‖ ∂volume + ∫ x, ‖f x‖ ^ p ∂volume))

/-- **OS2 (Euclidean Invariance):** The generating functional is
invariant under the Euclidean group E(2) = ℝ² ⋊ O(2).

  `Z[g · f] = Z[f]` for all g ∈ E(2), f ∈ S(ℝ², ℂ).

This matches OSforGFF.OS2_EuclideanInvariance. -/
def OS2_EuclideanInvariance
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ] : Prop :=
  ∀ (g : E2) (f : TestFunction2ℂ),
    generatingFunctionalℂ μ f =
    generatingFunctionalℂ μ (euclideanAction2ℂ g f)

/-- **OS3 (Reflection Positivity):** For any finite collection of
positive-time test functions f₁,...,fₙ and real coefficients c₁,...,cₙ,
the reflection positivity matrix is positive semidefinite:

  `Σᵢⱼ cᵢ cⱼ · Re(Z[fᵢ - Θfⱼ]) ≥ 0`

where Θ is the time reflection operator.

This matches OSforGFF.OS3_ReflectionPositivity. -/
def OS3_ReflectionPositivity
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ] : Prop :=
  ∀ (n : ℕ) (f : Fin n → PositiveTimeTestFunction2) (c : Fin n → ℝ),
    0 ≤ ∑ i, ∑ j, c i * c j *
      (generatingFunctional μ
        ((f i).val - compTimeReflection2 ((f j).val))).re

/-- **OS4 (Clustering):** Correlations between well-separated regions
decay to zero. The generating functional factors at large distances:

  `Z[f + T_a g] → Z[f] · Z[g]` as `‖a‖ → ∞`

This matches OSforGFF.OS4_Clustering.

For P(Φ)₂, the decay is exponential with rate m₀ > 0 (the mass gap),
but the axiom only requires convergence to zero. -/
def OS4_Clustering
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ] : Prop :=
  ∀ (f g : TestFunction2) (ε : ℝ), ε > 0 →
    ∃ (R : ℝ), R > 0 ∧ ∀ (a : SpaceTime2), ‖a‖ > R →
    ‖generatingFunctional μ (f + SchwartzMap.translate a g)
     - generatingFunctional μ f * generatingFunctional μ g‖ < ε

/-- **OS4 (Ergodicity):** Time-averaged observables converge to their
expectations in L²(μ).

  `(1/T) ∫₀ᵀ A(T_s ω) ds → 𝔼_μ[A]` in L²(μ) as T → ∞

This matches OSforGFF.OS4_Ergodicity.

The standard formulation uses "generating function" observables
A(ω) = Σⱼ zⱼ exp(⟨ω, fⱼ⟩). -/
def OS4_Ergodicity
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ] : Prop :=
  -- Ergodicity: the measure μ is ergodic under time translations.
  -- Stated via the generating functional: for any test function f,
  -- the time-averaged generating functional converges to the square
  -- of the one-point function (factorization = ergodicity).
  -- Equivalently: the only translation-invariant L² functions are constants a.e.
  ∀ (f g : TestFunction2),
    Filter.Tendsto
      (fun T : ℝ => (1 / T) * ∫ t in Set.Icc (0 : ℝ) T,
        (generatingFunctional μ
          (f + SchwartzMap.translate ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![t, 0]) g)).re)
      Filter.atTop
      (nhds ((generatingFunctional μ f).re * (generatingFunctional μ g).re))

/-! ## Full OS axiom bundle -/

/-- **Full Osterwalder-Schrader axiom bundle.**

A probability measure μ on S'(ℝ²) satisfying all five OS axioms.
By the OS reconstruction theorem (Osterwalder-Schrader 1973, 1975),
such a measure yields a Wightman QFT in 1+1 dimensions. -/
structure SatisfiesFullOS
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ] : Prop where
  os0 : OS0_Analyticity μ
  os1 : OS1_Regularity μ
  os2 : OS2_EuclideanInvariance μ
  os3 : OS3_ReflectionPositivity μ
  os4_clustering : OS4_Clustering μ
  os4_ergodicity : OS4_Ergodicity μ

end Pphi2

end
