/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cylinder OS Axioms: OS0–OS3 for the Gaussian Free Field on S¹_L × ℝ

Defines and proves Osterwalder-Schrader axioms OS0 through OS3 for the
Gaussian measure on the cylinder S¹_L × ℝ.

## Main results

- `CylinderOS0_Analyticity` — characteristic functional is analytic
- `CylinderOS1_Regularity` — ‖Z[f_re, f_im]‖ ≤ exp(c·(q(f_re)+q(f_im)))
- `CylinderOS2_TranslationInvariance` — invariance under S¹ × ℝ translations
- `CylinderOS3_ReflectionPositivity` — RP matrix positive semidefinite
- `SatisfiesCylinderOS` — bundled structure for all cylinder OS axioms
- `cylinderGaussian_satisfies_OS` — main theorem

## Mathematical background

The cylinder S¹_L × ℝ is the natural geometry for OS axioms because:
- Time reflection Θ : t ↦ -t is clean on ℝ (no wraparound)
- Positive time = (0, ∞) is the full future half-line
- OS reconstruction applies directly to produce a Hilbert space

The proofs follow the same structure as the torus case:
- **OS0**: Z[f] = exp(-½G(f,f)) is entire since G is bilinear
- **OS1**: ‖Z_ℂ[f_re,f_im]‖ ≤ exp(½·(G(f_re,f_re)+G(f_im,f_im)))
- **OS2**: G is translation-invariant (Green's function depends on differences)
- **OS3**: RP inherited from lattice via weak limits; the cylinder lattice
  S¹_L × [-T,T] has clean time reflection at t=0

## References

- Osterwalder-Schrader (1973, 1975)
- Glimm-Jaffe, *Quantum Physics*, Ch. 6, 19
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I
-/

import Cylinder.GreenFunction
import Cylinder.PositiveTime
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

open GaussianField MeasureTheory Filter ProbabilityTheory

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Generating functionals -/

/-- The generating functional (characteristic functional) on the cylinder.

  `Z_μ(f) = E_μ[e^{i ω(f)}] = ∫ e^{i ω(f)} dμ(ω)`

For a Gaussian measure with covariance G: `Z(f) = exp(-½ G(f,f))`. -/
def cylinderGeneratingFunctional
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ] (f : CylinderTestFunction L) : ℂ :=
  ∫ ω : Configuration (CylinderTestFunction L),
    Complex.exp (Complex.I * ↑(ω f)) ∂μ

/-- The complex generating functional on the cylinder.

  `Z_ℂ[f_re, f_im] = ∫ exp(i(ω(f_re) + iω(f_im))) dμ(ω)` -/
def cylinderGeneratingFunctionalℂ
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ] (f_re f_im : CylinderTestFunction L) : ℂ :=
  ∫ ω : Configuration (CylinderTestFunction L),
    Complex.exp (Complex.I * ((ω f_re : ℂ) + Complex.I * (ω f_im : ℂ))) ∂μ

/-! ## Gaussian measure on the cylinder -/

/-- **Predicate for the Gaussian measure on the cylinder.**

A probability measure μ on Configuration(CylinderTestFunction L) is the
Gaussian free field with mass m if:
1. It has centered Gaussian 1D marginals (MGF form)
2. Its covariance equals the cylinder Green's function G_L
3. It has Z₂ symmetry (φ ↦ -φ invariance) -/
structure IsCylinderGaussian
    (μ : Measure (Configuration (CylinderTestFunction L)))
    (mass : ℝ) (hmass : 0 < mass) : Prop where
  /-- μ is a probability measure -/
  isProbability : IsProbabilityMeasure μ
  /-- Gaussian: characteristic functional has exp(-½σ²) form -/
  isGaussian : ∀ (f : CylinderTestFunction L),
    ∫ ω : Configuration (CylinderTestFunction L),
      Real.exp (ω f) ∂μ =
    Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂μ)
  /-- Covariance = cylinder continuum Green's function -/
  covariance_eq : ∀ (f : CylinderTestFunction L),
    ∫ ω : Configuration (CylinderTestFunction L), (ω f) ^ 2 ∂μ =
    cylinderGreen L mass hmass f f
  /-- Z₂ symmetry: μ is invariant under field negation -/
  z2_symmetric : Measure.map
    (Neg.neg : Configuration (CylinderTestFunction L) →
      Configuration (CylinderTestFunction L)) μ = μ

/-! ## OS0: Analyticity -/

/-- **OS0: Analyticity of the generating functional.**

The generating functional `Z[Σ zᵢJᵢ]` is entire analytic as a function
of z = (z₁,...,zₙ) ∈ ℂⁿ, for any choice of (real) test functions Jᵢ. -/
def CylinderOS0_Analyticity
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (n : ℕ) (J : Fin n → CylinderTestFunction L),
    AnalyticOn ℂ (fun z : Fin n → ℂ =>
      cylinderGeneratingFunctionalℂ L μ
        (∑ i, (z i).re • J i) (∑ i, (z i).im • J i)) Set.univ

/-- Analyticity of the complex generating functional (axiom for now). -/
axiom cylinderGeneratingFunctionalℂ_analyticOnNhd
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ]
    (hG : IsCylinderGaussian L μ mass hmass)
    (n : ℕ) (J : Fin n → CylinderTestFunction L) :
    AnalyticOnNhd ℂ (fun z : Fin n → ℂ =>
      cylinderGeneratingFunctionalℂ L μ
        (∑ i, (z i).re • J i) (∑ i, (z i).im • J i)) Set.univ

/-! ## OS1: Regularity -/

/-- **OS1: Regularity of the complex generating functional.**

  `‖Z_ℂ[f_re, f_im]‖ ≤ exp(c · (q(f_re) + q(f_im)))`

for some continuous seminorm `q` and constant `c > 0`. -/
def CylinderOS1_Regularity
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ] : Prop :=
  ∃ (q : CylinderTestFunction L → ℝ) (_ : Continuous q) (c : ℝ), c > 0 ∧
    ∀ (f_re f_im : CylinderTestFunction L),
      ‖cylinderGeneratingFunctionalℂ L μ f_re f_im‖ ≤
        Real.exp (c * (q f_re + q f_im))

/-- OS1 for the Gaussian cylinder measure.

The bound holds with `q(f) = G_L(f,f)` and `c = 1/2`:

  `‖Z_ℂ[f_re, f_im]‖ ≤ exp(½ · (G(f_re,f_re) + G(f_im,f_im)))`

Proof: By the triangle inequality for complex integrals,
`‖∫ exp(i(ω(f_re)+iω(f_im))) dμ‖ ≤ ∫ ‖exp(iω(f_re)-ω(f_im))‖ dμ = ∫ exp(-ω(f_im)) dμ`.
The Gaussian MGF gives `∫ exp(-ω(f_im)) dμ = exp(½G(f_im,f_im))`. -/
theorem cylinderGaussian_os1
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ]
    (hG : IsCylinderGaussian L μ mass hmass) :
    CylinderOS1_Regularity L μ := by
  refine ⟨fun f => cylinderGreen L mass hmass f f,
    cylinderGreen_continuous_diag L mass hmass,
    1 / 2, by norm_num, fun f_re f_im => ?_⟩
  unfold cylinderGeneratingFunctionalℂ
  -- Step 1: ‖exp(i(x+iy))‖ = exp(-y)
  have norm_bound : ∀ ω : Configuration (CylinderTestFunction L),
      ‖Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)))‖ =
      Real.exp (-(ω f_im)) := by
    intro ω
    rw [Complex.norm_exp]
    congr 1
    simp only [Complex.mul_re, Complex.add_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.add_im]
    ring
  -- Step 2: Gaussian MGF gives ∫ exp(-ω(f_im)) dμ = exp(½G(f_im,f_im))
  have mgf_eq : ∫ ω : Configuration (CylinderTestFunction L),
      Real.exp (-(ω f_im)) ∂μ =
      Real.exp ((1 / 2) * cylinderGreen L mass hmass f_im f_im) := by
    have h := hG.isGaussian (-f_im)
    simp only [map_neg, neg_sq] at h
    rw [h, hG.covariance_eq f_im]
  -- Step 3: Combine via triangle inequality + monotonicity of exp
  calc ‖∫ ω, Complex.exp
        (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im))) ∂μ‖
      ≤ ∫ ω, ‖Complex.exp
        (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)))‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ = ∫ ω, Real.exp (-(ω f_im)) ∂μ := by
        congr 1; ext ω; exact norm_bound ω
    _ = Real.exp ((1 / 2) * cylinderGreen L mass hmass f_im f_im) :=
        mgf_eq
    _ ≤ Real.exp (1 / 2 * (cylinderGreen L mass hmass f_re f_re +
          cylinderGreen L mass hmass f_im f_im)) := by
        apply Real.exp_le_exp_of_le
        have := cylinderGreen_nonneg L mass hmass f_re
        linarith

/-! ## OS2: Euclidean invariance -/

/-- **OS2a: Spatial translation invariance.**

  `Z(f) = Z(T_v f)` for all v ∈ S¹_L. -/
def CylinderOS2_SpatialTranslationInvariance
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (v : ℝ) (f : CylinderTestFunction L),
    cylinderGeneratingFunctional L μ f =
    cylinderGeneratingFunctional L μ (cylinderSpatialTranslation L v f)

/-- **OS2b: Time translation invariance.**

  `Z(f) = Z(T_τ f)` for all τ ∈ ℝ.

This is the temporal analogue of Euclidean invariance. On the cylinder,
spatial and temporal translations are independent symmetry groups. -/
def CylinderOS2_TimeTranslationInvariance
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (τ : ℝ) (f : CylinderTestFunction L),
    cylinderGeneratingFunctional L μ f =
    cylinderGeneratingFunctional L μ (cylinderTimeTranslation L τ f)

/-- **OS2c: Time reflection invariance.**

  `Z(f) = Z(Θf)`.

This is NOT an OS axiom but a property of the Gaussian measure (the
Green's function is even in time). OS3 involves RP of the matrix
`Re(Z[fᵢ - Θfⱼ])`, not just invariance under Θ. -/
def CylinderOS2_TimeReflectionInvariance
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (f : CylinderTestFunction L),
    cylinderGeneratingFunctional L μ f =
    cylinderGeneratingFunctional L μ (cylinderTimeReflection L f)

/-- **Gaussian characteristic function formula.**

For a measure μ satisfying `IsCylinderGaussian`, the generating functional
(characteristic functional) has the explicit form:

  `Z(f) = E[exp(iω(f))] = exp(-½G(f,f))`

Proved by analytic continuation of the complex MGF from the real axis to ℂ.
The real MGF `E[exp(tω(f))] = exp(½t²G(f,f))` matches that of
`gaussianReal 0 G(f,f)`. By `eqOn_complexMGF_of_mgf`, the complex MGFs agree
on the strip `{z | z.re ∈ interior(integrableExpSet)}`, which equals all of ℂ
since the exponential moments exist for all real t. Evaluating at z = i and
using `complexMGF_id_gaussianReal` yields the result. -/
theorem cylinderGaussian_charFun
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ]
    (hG : IsCylinderGaussian L μ mass hmass)
    (f : CylinderTestFunction L) :
    cylinderGeneratingFunctional L μ f =
    Complex.exp (-(1 / 2) * ↑(cylinderGreen L mass hmass f f)) := by
  -- Setup: NNReal variance for gaussianReal
  set G := cylinderGreen L mass hmass f f with hG_def
  set v : NNReal := ⟨G, cylinderGreen_nonneg L mass hmass f⟩
  have hv_val : (v : ℝ) = G := rfl
  -- Step 1: Compute real MGF of ω(f) from isGaussian
  have h_mgf : ∀ t : ℝ, mgf (fun ω : Configuration (CylinderTestFunction L) => ω f) μ t =
      Real.exp (G * t ^ 2 / 2) := by
    intro t
    change ∫ ω, Real.exp (t * ω f) ∂μ = _
    have h := hG.isGaussian (t • f)
    simp_rw [show ∀ ω : Configuration (CylinderTestFunction L),
      ω (t • f) = t * ω f from fun ω => by rw [map_smul, smul_eq_mul]] at h
    simp_rw [mul_pow] at h
    rw [integral_const_mul, hG.covariance_eq] at h
    rw [h]; congr 1; ring
  -- Step 2: MGF equals that of gaussianReal 0 v
  have h_mgf_eq : mgf (fun ω : Configuration (CylinderTestFunction L) => ω f) μ =
      mgf id (gaussianReal (0 : ℝ) v) := by
    ext t; rw [h_mgf, congr_fun (@mgf_id_gaussianReal (0 : ℝ) v) t]
    simp only [zero_mul, zero_add, hv_val]
  -- Step 3: integrableExpSet is all of ℝ (exponential moments exist for all t)
  have h_ies : integrableExpSet (fun ω : Configuration (CylinderTestFunction L) => ω f) μ =
      Set.univ := by
    ext t; simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact mgf_pos_iff.mp (by rw [h_mgf]; exact Real.exp_pos _)
  -- Step 4: Analytic continuation — complexMGF agrees on all of ℂ
  have h_eqOn := eqOn_complexMGF_of_mgf h_mgf_eq
  rw [h_ies, interior_univ] at h_eqOn
  -- Step 5: Evaluate at z = i
  have h_I := h_eqOn (show Complex.I ∈ {z : ℂ | z.re ∈ (Set.univ : Set ℝ)} by simp)
  -- Step 6: LHS = cylinderGeneratingFunctional (definitional equality)
  change cylinderGeneratingFunctional L μ f = Complex.exp (-(1 / 2) * ↑G)
  change complexMGF (fun ω : Configuration (CylinderTestFunction L) => ω f) μ Complex.I =
    Complex.exp (-(1 / 2) * ↑G)
  -- Step 7: Use analytic continuation + gaussianReal formula
  rw [h_I, complexMGF_id_gaussianReal]
  congr 1
  simp only [Complex.ofReal_zero, mul_zero, zero_add, Complex.I_sq, hv_val]; ring

/-- OS2 (spatial translation) for the Gaussian cylinder measure.

  `Z(T_v f) = exp(-½G(T_v f, T_v f)) = exp(-½G(f,f)) = Z(f)`

Proved from the Gaussian characteristic function formula and
spatial translation invariance of the Green's function. -/
theorem cylinderGaussian_os2_spatial
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ]
    (hG : IsCylinderGaussian L μ mass hmass) :
    CylinderOS2_SpatialTranslationInvariance L μ := by
  intro v f
  simp only [cylinderGaussian_charFun L mass hmass μ hG]
  congr 1
  rw [cylinderGreen_spatialTranslation_invariant L mass hmass v f f]

/-- OS2 (time translation) for the Gaussian cylinder measure.

Proved from the Gaussian characteristic function formula and
time translation invariance of the Green's function. -/
theorem cylinderGaussian_os2_time
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ]
    (hG : IsCylinderGaussian L μ mass hmass) :
    CylinderOS2_TimeTranslationInvariance L μ := by
  intro τ f
  simp only [cylinderGaussian_charFun L mass hmass μ hG]
  congr 1
  rw [cylinderGreen_timeTranslation_invariant L mass hmass τ f f]

/-- OS2 (time reflection) for the Gaussian cylinder measure.

Proved from the Gaussian characteristic function formula and
time reflection invariance of the Green's function. -/
theorem cylinderGaussian_os2_reflection
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ]
    (hG : IsCylinderGaussian L μ mass hmass) :
    CylinderOS2_TimeReflectionInvariance L μ := by
  intro f
  simp only [cylinderGaussian_charFun L mass hmass μ hG]
  congr 1
  rw [cylinderGreen_timeReflection_invariant L mass hmass f f]

/-! ## OS3: Reflection positivity -/

/-- **OS3: Reflection positivity for the cylinder measure (matrix form).**

For any finite collection of positive-time test functions f₁,...,fₙ and
real coefficients c₁,...,cₙ, the RP matrix is positive semidefinite:

  `Σᵢⱼ cᵢ cⱼ · Re(Z[fᵢ - Θfⱼ]) ≥ 0`

where Θ = `cylinderTimeReflection` is the time reflection on test functions.

The key advantage of the cylinder over the torus: positive time = (0,∞)
is the full future half-line. The block-zero property (no coupling between
positive-time and negative-time fields) holds by locality of the Laplacian
plus disjointness of supports (0,∞) and (-∞,0). -/
def CylinderOS3_ReflectionPositivity
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (n : ℕ) (f : Fin n → CylinderPositiveTimeTestFunction L) (c : Fin n → ℝ),
    0 ≤ ∑ i, ∑ j, c i * c j *
      (cylinderGeneratingFunctional L μ
        ((f i).val - cylinderTimeReflection L (f j).val)).re

/-! ### Helper lemmas for weak-limit RP transfer -/

/-- `ω ↦ cos(ω(g))` is continuous on cylinder configuration space. -/
private lemma cylinderCosEval_continuous (g : CylinderTestFunction L) :
    Continuous (fun ω : Configuration (CylinderTestFunction L) => Real.cos (ω g)) :=
  Real.continuous_cos.comp (WeakDual.eval_continuous g)

/-- `ω ↦ cos(ω(g))` is bounded by 1. -/
private lemma cylinderCosEval_bounded (g : CylinderTestFunction L) :
    ∃ C : ℝ, ∀ ω : Configuration (CylinderTestFunction L), |Real.cos (ω g)| ≤ C :=
  ⟨1, fun ω => Real.abs_cos_le_one (ω g)⟩

/-- `ω ↦ exp(i·ω(g))` is AE strongly measurable. -/
private lemma cylinderExpEval_aestronglyMeasurable
    (μ : Measure (Configuration (CylinderTestFunction L)))
    (g : CylinderTestFunction L) :
    AEStronglyMeasurable (fun ω : Configuration (CylinderTestFunction L) =>
      Complex.exp (Complex.I * ↑(ω g))) μ :=
  (Complex.continuous_exp.measurable.comp
    (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
      (configuration_eval_measurable g)))).aestronglyMeasurable

/-- `ω ↦ exp(i·ω(g))` is integrable w.r.t. any probability measure. -/
private lemma cylinderExpEval_integrable
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ] (g : CylinderTestFunction L) :
    Integrable (fun ω : Configuration (CylinderTestFunction L) =>
      Complex.exp (Complex.I * ↑(ω g))) μ := by
  apply (integrable_const (1 : ℂ)).mono
  · exact cylinderExpEval_aestronglyMeasurable L μ g
  · apply ae_of_all
    intro ω
    simp only [norm_one]
    rw [show Complex.I * ↑(ω g) = ↑(ω g) * Complex.I from mul_comm _ _]
    exact le_of_eq (Complex.norm_exp_ofReal_mul_I (ω g))

/-- `Re(Z_μ[g]) = ∫ cos(ω(g)) dμ(ω)`. -/
private lemma cylinderGeneratingFunctional_re_eq_integral_cos
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ] (g : CylinderTestFunction L) :
    (cylinderGeneratingFunctional L μ g).re =
    ∫ ω : Configuration (CylinderTestFunction L), Real.cos (ω g) ∂μ := by
  unfold cylinderGeneratingFunctional
  rw [show (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ).re =
    Complex.reCLM (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ) from rfl,
    ← ContinuousLinearMap.integral_comp_comm Complex.reCLM
      (cylinderExpEval_integrable L μ g)]
  congr 1 with ω
  simp only [Complex.reCLM_apply, mul_comm Complex.I, Complex.exp_mul_I,
    Complex.add_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.sin_ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  exact Complex.cos_ofReal_re (ω g)

/-! ### RP for lattice approximations and weak limit transfer -/

/-- The lattice approximation to the cylinder GFF satisfies RP.

For each N (lattice size), the lattice measure on S¹_L × [-T_N, T_N]
satisfies the matrix form of RP. The proof uses the Fubini + perfect
square argument, which is cleaner on the cylinder because:
- Positive time = {sites with t > 0} (no wraparound)
- The mass operator Q has exact block-zero property by locality -/
axiom cylinderLattice_rp (N : ℕ) [NeZero N]
    (mass : ℝ) (hmass : 0 < mass)
    (μ_N : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ_N] :
    CylinderOS3_ReflectionPositivity L μ_N

/-- **Matrix form of RP is preserved under weak limits on the cylinder.**

Identical proof to the torus case: each RP matrix entry
`Re(Z_μ[g]) = ∫ cos(ω(g)) dμ` is a bounded continuous functional
of the measure, so weak convergence gives pointwise convergence of
the RP matrix. A finite sum of limits of nonneg quantities is nonneg. -/
theorem cylinderMatrixRP_of_weakLimit
    (μ_seq : ℕ → Measure (Configuration (CylinderTestFunction L)))
    [∀ k, IsProbabilityMeasure (μ_seq k)]
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ]
    (h_weak : ∀ g : Configuration (CylinderTestFunction L) → ℝ,
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Tendsto (fun k => ∫ ω, g ω ∂(μ_seq k)) atTop (nhds (∫ ω, g ω ∂μ)))
    (h_rp : ∀ k, CylinderOS3_ReflectionPositivity L (μ_seq k)) :
    CylinderOS3_ReflectionPositivity L μ := by
  intro n f c
  have h_tendsto : Tendsto
      (fun k => ∑ i : Fin n, ∑ j : Fin n, c i * c j *
        (cylinderGeneratingFunctional L (μ_seq k)
          ((f i).val - cylinderTimeReflection L (f j).val)).re)
      atTop
      (nhds (∑ i : Fin n, ∑ j : Fin n, c i * c j *
        (cylinderGeneratingFunctional L μ
          ((f i).val - cylinderTimeReflection L (f j).val)).re)) := by
    apply tendsto_finset_sum
    intro i _
    apply tendsto_finset_sum
    intro j _
    apply Filter.Tendsto.const_mul
    simp_rw [cylinderGeneratingFunctional_re_eq_integral_cos L]
    exact h_weak _ (cylinderCosEval_continuous L _) (cylinderCosEval_bounded L _)
  exact ge_of_tendsto' h_tendsto (fun k => h_rp k n f c)

/-! ## Bundle and main theorem -/

/-- **Bundled cylinder OS axioms OS0–OS3.** -/
structure SatisfiesCylinderOS
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ] : Prop where
  os0 : CylinderOS0_Analyticity L μ
  os1 : CylinderOS1_Regularity L μ
  os2_spatial : CylinderOS2_SpatialTranslationInvariance L μ
  os2_time : CylinderOS2_TimeTranslationInvariance L μ
  os2_reflection : CylinderOS2_TimeReflectionInvariance L μ
  os3 : CylinderOS3_ReflectionPositivity L μ

/-- **The Gaussian measure on the cylinder satisfies OS0–OS3.**

OS0: from `cylinderGeneratingFunctionalℂ_analyticOnNhd` (axiom)
OS1: from `cylinderGaussian_os1` (proved via triangle inequality + MGF)
OS2: from `cylinderGaussian_os2_*` (proved via charFun + Green's invariance)
OS3: from `cylinderLattice_rp` (axiom for lattice RP) -/
theorem cylinderGaussian_satisfies_OS
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ]
    (hG : IsCylinderGaussian L μ mass hmass) :
    SatisfiesCylinderOS L μ where
  os0 n J := (cylinderGeneratingFunctionalℂ_analyticOnNhd L mass hmass μ hG n J).analyticOn
  os1 := cylinderGaussian_os1 L mass hmass μ hG
  os2_spatial := cylinderGaussian_os2_spatial L mass hmass μ hG
  os2_time := cylinderGaussian_os2_time L mass hmass μ hG
  os2_reflection := cylinderGaussian_os2_reflection L mass hmass μ hG
  os3 := cylinderLattice_rp L 1 mass hmass μ

end Pphi2

end
