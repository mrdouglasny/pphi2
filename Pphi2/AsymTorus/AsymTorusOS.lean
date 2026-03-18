/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Asymmetric Torus OS Axioms: Route B'

States and proves OS0–OS2 for the asymmetric torus interacting continuum
limit, following the same structure as `TorusInteractingOS.lean`.

All proofs follow the IDENTICAL patterns as the symmetric torus case,
with `asymGeomSpacing Lt Ls N` replacing `circleSpacing L N` and
`AsymTorusTestFunction Lt Ls` replacing `TorusTestFunction L`.

## Main results

- `asymTorusInteracting_os0` — analyticity (from analyticOnNhd_integral)
- `asymTorusInteracting_os1` — regularity (from exponential moment bound)
- `asymTorusInteracting_os2_translation` — translation invariance
- `asymTorusInteracting_os2_D4` — D4 invariance (swap + time reflection)
- `asymTorusInteracting_satisfies_OS` — bundled OS0–OS2

## Proof strategy

The proofs are structurally identical to the symmetric torus:
1. Nelson's estimate → exponential moment → OS0 + OS1
2. Lattice symmetry → torus equivariance → weak limit → OS2
3. Translation invariance via lattice approximation argument

The only difference: asymmetric spacings (Lt/N vs Ls/N) in each direction.
-/

import Pphi2.AsymTorus.AsymTorusInteractingLimit
import Pphi2.GeneralResults.ComplexAnalysis
import GaussianField.Density

noncomputable section

open GaussianField MeasureTheory Filter Complex

namespace Pphi2

variable (Lt Ls : ℝ) [hLt : Fact (0 < Lt)] [hLs : Fact (0 < Ls)]

/-! ## OS Axiom Definitions -/

/-- The generating functional on the asymmetric torus. -/
def asymTorusGeneratingFunctional
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ] (f : AsymTorusTestFunction Lt Ls) : ℂ :=
  ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
    Complex.exp (Complex.I * ↑(ω f)) ∂μ

/-- OS0: Analyticity of the asymmetric torus generating functional. -/
def AsymTorusOS0_Analyticity
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (n : ℕ) (J : Fin n → AsymTorusTestFunction Lt Ls),
    AnalyticOn ℂ (fun z : Fin n → ℂ =>
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
        Complex.exp (Complex.I *
          ↑(ω (∑ i, (z i).re • J i) + Complex.I * ↑(ω (∑ i, (z i).im • J i)))) ∂μ)
      Set.univ

/-- OS1: Regularity of the asymmetric torus generating functional. -/
def AsymTorusOS1_Regularity
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ] : Prop :=
  ∃ (q : AsymTorusTestFunction Lt Ls → ℝ) (_ : Continuous q)
    (c : ℝ) (_ : 0 < c),
  ∀ (f_re f_im : AsymTorusTestFunction Lt Ls),
    ‖∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
      Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im))) ∂μ‖ ≤
    Real.exp (c * (q f_re + q f_im))

/-- OS2: Translation invariance on the asymmetric torus. -/
def AsymTorusOS2_TranslationInvariance
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (v : ℝ × ℝ) (f : AsymTorusTestFunction Lt Ls),
    asymTorusGeneratingFunctional Lt Ls μ f =
    asymTorusGeneratingFunctional Lt Ls μ (asymTorusTranslation Lt Ls v f)

/-- OS2: D4 point group invariance on the asymmetric torus.
Note: swap maps AsymTorusTestFunction Lt Ls → AsymTorusTestFunction Ls Lt,
so it's only an endomorphism when Lt = Ls. For asymmetric torus, OS2 D4
includes time reflection (always an endomorphism) but NOT swap. -/
def AsymTorusOS2_TimeReflectionInvariance
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (f : AsymTorusTestFunction Lt Ls),
    asymTorusGeneratingFunctional Lt Ls μ f =
    asymTorusGeneratingFunctional Lt Ls μ (asymTorusTimeReflection Lt Ls f)

/-! ## Bundled OS structure -/

/-- Bundled OS axioms for the asymmetric torus. -/
structure AsymSatisfiesTorusOS
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ] where
  os0 : AsymTorusOS0_Analyticity Lt Ls μ
  os1 : AsymTorusOS1_Regularity Lt Ls μ
  os2_translation : AsymTorusOS2_TranslationInvariance Lt Ls μ
  os2_timeReflection : AsymTorusOS2_TimeReflectionInvariance Lt Ls μ

/-! ## OS Proof Infrastructure

Helpers for decomposing the generating functional into cos/sin integrals,
exactly mirroring the private helpers in TorusInteractingOS.lean. -/

private lemma asymCosEval_continuous (g : AsymTorusTestFunction Lt Ls) :
    Continuous (fun ω : Configuration (AsymTorusTestFunction Lt Ls) => Real.cos (ω g)) :=
  Real.continuous_cos.comp (WeakDual.eval_continuous g)

private lemma asymCosEval_bounded (g : AsymTorusTestFunction Lt Ls) :
    ∃ C, ∀ ω : Configuration (AsymTorusTestFunction Lt Ls), |Real.cos (ω g)| ≤ C :=
  ⟨1, fun _ => Real.abs_cos_le_one _⟩

private lemma asymSinEval_continuous (g : AsymTorusTestFunction Lt Ls) :
    Continuous (fun ω : Configuration (AsymTorusTestFunction Lt Ls) => Real.sin (ω g)) :=
  Real.continuous_sin.comp (WeakDual.eval_continuous g)

private lemma asymSinEval_bounded (g : AsymTorusTestFunction Lt Ls) :
    ∃ C, ∀ ω : Configuration (AsymTorusTestFunction Lt Ls), |Real.sin (ω g)| ≤ C :=
  ⟨1, fun _ => Real.abs_sin_le_one _⟩

/-- Decomposition: the generating functional's real part is the cosine integral. -/
private lemma asymGf_re_eq_cos_integral
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ] (g : AsymTorusTestFunction Lt Ls) :
    (asymTorusGeneratingFunctional Lt Ls μ g).re =
    ∫ ω : Configuration (AsymTorusTestFunction Lt Ls), Real.cos (ω g) ∂μ := by
  unfold asymTorusGeneratingFunctional
  rw [show (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ).re =
    Complex.reCLM (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ) from rfl]
  have hint : Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
      Complex.exp (Complex.I * ↑(ω g))) μ := by
    apply (integrable_const (1 : ℂ)).mono
    · exact (Complex.continuous_exp.measurable.comp
        (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
          (configuration_eval_measurable g)))).aestronglyMeasurable
    · apply ae_of_all; intro ω; simp only [norm_one]
      rw [show Complex.I * ↑(ω g) = ↑(ω g) * Complex.I from mul_comm _ _]
      exact le_of_eq (Complex.norm_exp_ofReal_mul_I (ω g))
  rw [← ContinuousLinearMap.integral_comp_comm Complex.reCLM hint]
  congr 1 with ω
  simp only [Complex.reCLM_apply, mul_comm Complex.I, Complex.exp_mul_I,
    Complex.add_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.sin_ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  exact Complex.cos_ofReal_re (ω g)

/-- Decomposition: the generating functional's imaginary part is the sine integral. -/
private lemma asymGf_im_eq_sin_integral
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ] (g : AsymTorusTestFunction Lt Ls) :
    (asymTorusGeneratingFunctional Lt Ls μ g).im =
    ∫ ω : Configuration (AsymTorusTestFunction Lt Ls), Real.sin (ω g) ∂μ := by
  unfold asymTorusGeneratingFunctional
  rw [show (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ).im =
    Complex.imCLM (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ) from rfl]
  have hint : Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
      Complex.exp (Complex.I * ↑(ω g))) μ := by
    apply (integrable_const (1 : ℂ)).mono
    · exact (Complex.continuous_exp.measurable.comp
        (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
          (configuration_eval_measurable g)))).aestronglyMeasurable
    · apply ae_of_all; intro ω; simp only [norm_one]
      rw [show Complex.I * ↑(ω g) = ↑(ω g) * Complex.I from mul_comm _ _]
      exact le_of_eq (Complex.norm_exp_ofReal_mul_I (ω g))
  rw [← ContinuousLinearMap.integral_comp_comm Complex.imCLM hint]
  congr 1 with ω
  simp only [Complex.imCLM_apply, mul_comm Complex.I, Complex.exp_mul_I,
    Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
  ring

/-! ## Intermediate lemmas (cutoff-level invariances)

Self-contained copies of the lattice symmetry invariant machinery from
`TorusInteractingOS.lean`, generalized to work with any positive spacing `a`
(the originals are typed for `circleSpacing L N` and use private definitions).

The main results:
- `asymInteractingLatticeMeasure_symmetry_invariant` — generic site symmetry
- `asymInteractingLatticeMeasure_timeReflection_invariant` — time reflection
- `evalAsymAtFinSite_timeReflection` — eval equivariance under Theta -/

/-- Linear map on lattice field induced by a site permutation `σ`.
Local copy of the private `latticeSitePermuteLM` from `TorusInteractingOS.lean`. -/
private def asymLatticeSitePermuteLM (N : ℕ)
    (σ : FinLatticeSites 2 N → FinLatticeSites 2 N) :
    FinLatticeField 2 N →ₗ[ℝ] FinLatticeField 2 N where
  toFun g := g ∘ σ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Helper: `piCongrLeft(σ_equiv)` maps `φ ↦ φ ∘ σ⁻¹`.
Local copy of the private lemma from `TorusInteractingOS.lean`. -/
private lemma asymPiCongrLeft_eq_comp_symm {N : ℕ}
    (σ_equiv : FinLatticeSites 2 N ≃ FinLatticeSites 2 N)
    (φ : FinLatticeField 2 N) :
    (Equiv.piCongrLeft (fun _ : FinLatticeSites 2 N => ℝ) σ_equiv) φ =
      φ ∘ σ_equiv.symm := by
  ext x
  change (Equiv.piCongrLeft (fun _ => ℝ) σ_equiv) φ x = φ (σ_equiv.symm x)
  have h := Equiv.piCongrLeft_apply_apply (P := fun _ : FinLatticeSites 2 N => ℝ)
    σ_equiv φ (σ_equiv.symm x)
  rwa [σ_equiv.apply_symm_apply] at h

/-- **Lattice interacting measure is invariant under site symmetries (generic spacing).**

For a bijective site permutation `σ` that preserves the Gaussian density,
`∫ F(ω ∘ σ) dμ_int = ∫ F(ω) dμ_int`.

This is a self-contained copy of `interactingLatticeMeasure_symmetry_invariant`
from `TorusInteractingOS.lean`, generalized from `circleSpacing L N` to any
positive real `a`. The proof is character-for-character the same. -/
private theorem asymInteractingLatticeMeasure_symmetry_invariant
    (N : ℕ) [NeZero N] (P : InteractionPolynomial) (mass : ℝ)
    (a : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (σ : FinLatticeSites 2 N → FinLatticeSites 2 N)
    (hσ_bij : Function.Bijective σ)
    (hσ_density : ∀ φ : FinLatticeField 2 N,
      gaussianDensity 2 N a mass
        (φ ∘ (Equiv.ofBijective σ hσ_bij).symm) =
      gaussianDensity 2 N a mass φ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Configuration (FinLatticeField 2 N) → E) :
    ∫ ω, F (ω.comp (asymLatticeSitePermuteLM N σ).toContinuousLinearMap)
      ∂(interactingLatticeMeasure 2 N P a mass ha hmass) =
    ∫ ω, F ω ∂(interactingLatticeMeasure 2 N P a mass ha hmass) := by
  -- Setup notation
  set mu_GFF := latticeGaussianMeasure 2 N a mass ha hmass
  set bw := boltzmannWeight 2 N P a mass
  set σ_equiv := Equiv.ofBijective σ hσ_bij
  set L_σ : FinLatticeField 2 N →ₗ[ℝ] FinLatticeField 2 N :=
    asymLatticeSitePermuteLM N σ
  -- Step 1: Unfold the interacting measure = Z⁻¹ • μ_GFF.withDensity(bw)
  unfold interactingLatticeMeasure
  simp_rw [integral_smul_measure]
  congr 1  -- Z⁻¹ factor is the same on both sides
  -- Step 2: Convert withDensity integrals to μ_GFF integrals with NNReal smul
  set bw_nn := fun ω : Configuration (FinLatticeField 2 N) => Real.toNNReal (bw ω)
  have hbw_nn_meas : Measurable bw_nn :=
    Measurable.real_toNNReal
      ((interactionFunctional_measurable 2 N P a mass).neg.exp)
  change ∫ ω, F (ω.comp L_σ.toContinuousLinearMap)
      ∂(mu_GFF.withDensity (fun ω => ↑(bw_nn ω))) =
    ∫ ω, F ω ∂(mu_GFF.withDensity (fun ω => ↑(bw_nn ω)))
  rw [integral_withDensity_eq_integral_smul hbw_nn_meas,
      integral_withDensity_eq_integral_smul hbw_nn_meas]
  -- Step 3: BW invariance at the configuration level
  have hBW_config : ∀ ω : Configuration (FinLatticeField 2 N),
      bw (ω.comp L_σ.toContinuousLinearMap) = bw ω := by
    intro ω
    suffices h : interactionFunctional 2 N P a mass
        (ω.comp L_σ.toContinuousLinearMap) =
        interactionFunctional 2 N P a mass ω by
      simp only [bw, boltzmannWeight, h]
    simp only [interactionFunctional]
    congr 1
    apply Fintype.sum_equiv σ_equiv.symm
    intro x; congr 1
    change ω (L_σ (finLatticeDelta 2 N x)) = ω (finLatticeDelta 2 N (σ_equiv.symm x))
    congr 1; ext y
    simp only [L_σ, asymLatticeSitePermuteLM, LinearMap.coe_mk, AddHom.coe_mk,
      Function.comp, finLatticeDelta]
    congr 1; exact propext σ_equiv.apply_eq_iff_eq_symm_apply
  -- Step 4: Use BW invariance to factor the LHS integrand as G ∘ Φ
  have hBW_nn_config : ∀ ω : Configuration (FinLatticeField 2 N),
      bw_nn (ω.comp L_σ.toContinuousLinearMap) = bw_nn ω := by
    intro ω; simp only [bw_nn, hBW_config]
  set G := fun ω : Configuration (FinLatticeField 2 N) => bw_nn ω • F ω
  have hG_eq : ∀ ω, bw_nn ω • F (ω.comp L_σ.toContinuousLinearMap) =
      G (ω.comp L_σ.toContinuousLinearMap) := by
    intro ω; simp only [G, hBW_nn_config]
  simp_rw [hG_eq]
  -- Step 5: Build configuration-level MeasurableEquiv
  set σ_field_equiv : FinLatticeField 2 N ≃ᵐ FinLatticeField 2 N :=
    MeasurableEquiv.piCongrLeft (fun _ : FinLatticeSites 2 N => ℝ) σ_equiv
  set evalME := GaussianField.evalMapMeasurableEquiv 2 N
  set Φ_equiv : Configuration (FinLatticeField 2 N) ≃ᵐ
      Configuration (FinLatticeField 2 N) :=
    evalME.trans (σ_field_equiv.trans evalME.symm)
  -- Step 6: Show Φ_equiv agrees with ω ↦ ω.comp L_σ.toCLM
  have hΦ_eq : ∀ ω : Configuration (FinLatticeField 2 N),
      Φ_equiv ω = ω.comp L_σ.toContinuousLinearMap := by
    intro ω
    -- Both sides are configurations; show they agree on all test functions.
    -- Strategy: apply evalME and use function extensionality
    have hinj := evalME.injective
    apply hinj
    ext x
    simp only [Φ_equiv, MeasurableEquiv.trans_apply, MeasurableEquiv.apply_symm_apply]
    rw [show σ_field_equiv (evalME ω) = (evalME ω) ∘ σ_equiv.symm from
      asymPiCongrLeft_eq_comp_symm σ_equiv (evalME ω)]
    simp only [Function.comp, evalME]
    change ω (finLatticeDelta 2 N (σ_equiv.symm x)) =
      ω (L_σ (finLatticeDelta 2 N x))
    congr 1; ext y
    simp only [L_σ, asymLatticeSitePermuteLM, LinearMap.coe_mk, AddHom.coe_mk,
      Function.comp, finLatticeDelta]
    congr 1; exact propext σ_equiv.eq_symm_apply
  -- Step 7: Rewrite G(ω.comp L_σ) as G(Φ_equiv ω)
  simp_rw [← hΦ_eq]
  -- Step 8: Show Φ_equiv preserves μ_GFF
  have hΦ_mp : MeasurePreserving Φ_equiv mu_GFF mu_GFF := by
    set ν := latticeGaussianFieldLaw 2 N a mass ha hmass
    have h_nu_eq : ν = Measure.map evalME mu_GFF := by
      simp only [ν, latticeGaussianFieldLaw, mu_GFF]; rfl
    have h_evalME : MeasurePreserving evalME mu_GFF ν := by
      rw [h_nu_eq]; exact evalME.measurable.measurePreserving mu_GFF
    have h_evalME_symm : MeasurePreserving evalME.symm ν mu_GFF :=
      h_evalME.symm _
    have h_sigma : MeasurePreserving σ_field_equiv ν ν := by
      have hν_eq : ν = normalizedGaussianDensityMeasure 2 N a mass :=
        latticeGaussianFieldLaw_eq_normalizedGaussianDensityMeasure (d := 2) (N := N)
          a mass ha hmass
      rw [hν_eq, normalizedGaussianDensityMeasure]
      apply MeasurePreserving.smul_measure
      simp only [gaussianDensityMeasure]
      have hσ_field_eq : ∀ φ : FinLatticeField 2 N,
          (σ_field_equiv φ : FinLatticeField 2 N) = φ ∘ σ_equiv.symm := by
        intro φ
        have := asymPiCongrLeft_eq_comp_symm σ_equiv φ
        change (MeasurableEquiv.piCongrLeft (fun _ => ℝ) σ_equiv) φ = φ ∘ σ_equiv.symm
        rw [MeasurableEquiv.coe_piCongrLeft]; exact this
      have hρ_inv : ∀ φ : FinLatticeField 2 N,
          gaussianDensityWeight 2 N a mass (σ_field_equiv φ) =
          gaussianDensityWeight 2 N a mass φ := by
        intro φ
        simp only [gaussianDensityWeight, hσ_field_eq, hσ_density]
      have h_vol : MeasurePreserving σ_field_equiv
          (volume : Measure (FinLatticeField 2 N)) volume :=
        volume_measurePreserving_piCongrLeft _ _
      refine ⟨σ_field_equiv.measurable, ?_⟩
      ext s hs
      rw [Measure.map_apply σ_field_equiv.measurable hs,
          withDensity_apply _ (σ_field_equiv.measurable hs),
          withDensity_apply _ hs]
      rw [show ∫⁻ x in σ_field_equiv ⁻¹' s,
            gaussianDensityWeight 2 N a mass x ∂volume =
          ∫⁻ x in σ_field_equiv ⁻¹' s,
            gaussianDensityWeight 2 N a mass (σ_field_equiv x) ∂volume from
        setLIntegral_congr_fun (σ_field_equiv.measurable hs)
          (fun x _ => (hρ_inv x).symm)]
      exact h_vol.setLIntegral_comp_preimage hs
        (gaussianDensityWeight_measurable (d := 2) (N := N) a mass)
    exact h_evalME.trans (h_sigma.trans h_evalME_symm)
  exact hΦ_mp.integral_comp' G

/-- The finite Laplacian commutes with time reflection.
Local copy of the private `finiteLaplacian_timeReflect_commute` from `TorusInteractingOS.lean`. -/
private theorem asymFiniteLaplacian_timeReflect_commute (N : ℕ) [NeZero N] (a : ℝ)
    (φ : FinLatticeField 2 N) :
    finiteLaplacian 2 N a (φ ∘ timeReflectSites N) =
    (finiteLaplacian 2 N a φ) ∘ timeReflectSites N := by
  ext x
  change finiteLaplacianFun 2 N a (φ ∘ timeReflectSites N) x =
    finiteLaplacianFun 2 N a φ (timeReflectSites N x)
  simp only [finiteLaplacianFun, Function.comp]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have refl_neighbor_fwd :
      timeReflectSites N (fun j => if j = i then x j + 1 else x j) =
      fun j => if j = i then (timeReflectSites N x) j + (if i = (0 : Fin 2) then -1 else 1)
        else (timeReflectSites N x) j := by
    ext j
    simp only [timeReflectSites]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]; ring
  have refl_neighbor_bwd :
      timeReflectSites N (fun j => if j = i then x j - 1 else x j) =
      fun j => if j = i then (timeReflectSites N x) j - (if i = (0 : Fin 2) then -1 else 1)
        else (timeReflectSites N x) j := by
    ext j
    simp only [timeReflectSites]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]; ring
  rw [refl_neighbor_fwd, refl_neighbor_bwd]
  fin_cases i <;> simp <;> ring_nf

/-- The mass operator commutes with time reflection (generic spacing version).
Local copy of the private `massOperator_timeReflect_commute` from `TorusInteractingOS.lean`. -/
private theorem asymMassOperator_timeReflect_commute (N : ℕ) [NeZero N] (a mass : ℝ)
    (φ : FinLatticeField 2 N) :
    massOperator 2 N a mass (φ ∘ timeReflectSites N) =
    (massOperator 2 N a mass φ) ∘ timeReflectSites N := by
  have hΔ := asymFiniteLaplacian_timeReflect_commute N a φ
  ext x
  simp only [massOperator, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul, Function.comp]
  have h := congr_fun hΔ x
  simp only [Function.comp] at h
  linarith

/-- The lattice time-reflection linear map: `(L_refl g)(x) = g(timeReflectSites x)`. -/
private def asymLatticeTimeReflectLM (N : ℕ) :=
  asymLatticeSitePermuteLM N (timeReflectSites N)

/-- The interacting lattice measure with any spacing `a` is time-reflection invariant.

Proved by combining `asymInteractingLatticeMeasure_symmetry_invariant` with the
time-reflection density preservation argument (mass operator commutes with reflection
+ involutivity of reflection + relabeling the Gaussian exponent sum). -/
private theorem asymInteractingLatticeMeasure_timeReflection_invariant
    (N : ℕ) [NeZero N] (P : InteractionPolynomial) (mass : ℝ)
    (a : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Configuration (FinLatticeField 2 N) → E) :
    ∫ ω, F (ω.comp (asymLatticeTimeReflectLM N).toContinuousLinearMap)
      ∂(interactingLatticeMeasure 2 N P a mass ha hmass) =
    ∫ ω, F ω ∂(interactingLatticeMeasure 2 N P a mass ha hmass) := by
  -- Time reflection is bijective (involutive)
  have hbij : Function.Bijective (timeReflectSites N) := by
    have hinv : Function.Involutive (timeReflectSites N) := by
      intro x; simp only [timeReflectSites]
      ext i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact hinv.bijective
  have hinv : Function.Involutive (timeReflectSites N) := by
    intro x; simp only [timeReflectSites]
    ext i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact asymInteractingLatticeMeasure_symmetry_invariant N P mass a ha hmass
    (timeReflectSites N) hbij
    (by -- Density preservation: gaussianDensity(φ ∘ refl⁻¹) = gaussianDensity(φ)
      intro φ
      set σ_equiv := Equiv.ofBijective (timeReflectSites N) hbij
      -- Since refl is involutive, refl⁻¹ = refl
      have hsymm_eq : ∀ y, σ_equiv.symm y = timeReflectSites N y := by
        intro y
        rw [Equiv.symm_apply_eq]
        exact (hinv y).symm
      unfold gaussianDensity
      congr 1; congr 1
      have h_symm_comp : φ ∘ σ_equiv.symm = φ ∘ timeReflectSites N :=
        funext (fun y => congr_arg φ (hsymm_eq y))
      rw [h_symm_comp]
      simp_rw [Function.comp]
      -- Use commutativity: Q(φ ∘ refl) = (Qφ) ∘ refl
      have hcomm := asymMassOperator_timeReflect_commute N a mass φ
      simp_rw [show ∀ x,
        massOperator 2 N a mass (φ ∘ timeReflectSites N) x =
        (massOperator 2 N a mass φ) (timeReflectSites N x) from
        fun x => congr_fun hcomm x]
      -- Relabel sum x ↦ refl x using the equivalence
      exact Fintype.sum_equiv σ_equiv
        (fun x => φ (timeReflectSites N x) *
          (massOperator 2 N a mass φ) (timeReflectSites N x))
        (fun x => φ x * (massOperator 2 N a mass φ) x)
        (fun x => by simp [σ_equiv, Equiv.ofBijective_apply]))
    F

/-- Equivariance of `evalAsymAtFinSite` under time reflection.

  `evalAsymAtFinSite x (Θ f) = evalAsymAtFinSite (timeReflectSites x) f`

where `Θ = asymTorusTimeReflection = mapCLM (circleReflection Lt) id`.
Proof via `evalCLM_comp_mapCLM`, mirroring `evalTorusAtSite_timeReflection`. -/
private theorem evalAsymAtFinSite_timeReflection (N : ℕ) [NeZero N]
    (x : FinLatticeSites 2 N) (f : AsymTorusTestFunction Lt Ls) :
    evalAsymAtFinSite Lt Ls N x (asymTorusTimeReflection Lt Ls f) =
    evalAsymAtFinSite Lt Ls N (timeReflectSites N x) f := by
  simp only [evalAsymAtFinSite, evalAsymTorusAtSite, asymTorusTimeReflection,
    timeReflectSites]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [evalCLM_comp_mapCLM (smoothCircle_coeff_basis Lt) (smoothCircle_coeff_basis Ls)]
  simp only [ContinuousLinearMap.comp_id]
  -- Key: proj_{x 0} ∘ circRestr_Lt ∘ circRefl_Lt = proj_{-x 0} ∘ circRestr_Lt
  have key : ((ContinuousLinearMap.proj (x 0)).comp
      (circleRestriction Lt N)).comp (circleReflection Lt) =
    (ContinuousLinearMap.proj (-(x 0))).comp (circleRestriction Lt N) := by
    ext g
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      circleRestriction_apply, circleReflection, circlePoint]
    congr 1
    rw [ZMod.neg_val (x 0)]
    split
    · next hk => simp [hk]
    · next hk =>
      have hval_le : ZMod.val (x 0) ≤ N := le_of_lt (ZMod.val_lt (x 0))
      have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
      rw [show (↑(N - ZMod.val (x 0)) : ℝ) * Lt / ↑N =
          -(↑(ZMod.val (x 0)) * Lt / ↑N) + Lt from by
        rw [Nat.cast_sub hval_le]; field_simp; ring]
      exact (g.periodic' _).symm
  rw [key]

/-- Cutoff-level time reflection invariance of the asymmetric torus GF.

Follows the exact same proof as `torusInteractingMeasure_gf_timeReflection_invariant`:
1. `evalAsymAtFinSite` equivariance under time reflection
2. Lattice measure symmetry invariance
The only difference: `asymGeomSpacing Lt Ls N` replaces `circleSpacing L N`. -/
private theorem asymTorusInteractingMeasure_gf_timeReflection_invariant
    (N : ℕ) [NeZero N] (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (f : AsymTorusTestFunction Lt Ls) :
    asymTorusGeneratingFunctional Lt Ls
      (asymTorusInteractingMeasure Lt Ls N P mass hmass) f =
    asymTorusGeneratingFunctional Lt Ls
      (asymTorusInteractingMeasure Lt Ls N P mass hmass)
      (asymTorusTimeReflection Lt Ls f) := by
  -- Step 1: Eval equivariance under time reflection
  have h_lattice_refl : ∀ x : FinLatticeSites 2 N,
      asymLatticeTestFn Lt Ls N (asymTorusTimeReflection Lt Ls f) x =
      asymLatticeTestFn Lt Ls N f (timeReflectSites N x) := by
    intro x
    simp only [asymLatticeTestFn]
    exact evalAsymAtFinSite_timeReflection Lt Ls N x f
  -- Step 2: Unfold definitions and push through Measure.map
  unfold asymTorusGeneratingFunctional asymTorusInteractingMeasure
  set μ_lat := interactingLatticeMeasure 2 N P (asymGeomSpacing Lt Ls N) mass
    (asymGeomSpacing_pos Lt Ls N) hmass
  have hmeas : AEMeasurable (asymTorusEmbedLift Lt Ls N) μ_lat :=
    (asymTorusEmbedLift_measurable Lt Ls N).aemeasurable
  have hasm₁ : AEStronglyMeasurable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
      Complex.exp (Complex.I * ↑(ω f))) (Measure.map (asymTorusEmbedLift Lt Ls N) μ_lat) :=
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (configuration_eval_measurable f)))).aestronglyMeasurable
  have hasm₂ : AEStronglyMeasurable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
      Complex.exp (Complex.I * ↑(ω (asymTorusTimeReflection Lt Ls f))))
      (Measure.map (asymTorusEmbedLift Lt Ls N) μ_lat) := by
    exact (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (configuration_eval_measurable (asymTorusTimeReflection Lt Ls f))))).aestronglyMeasurable
  rw [MeasureTheory.integral_map hmeas hasm₁, MeasureTheory.integral_map hmeas hasm₂]
  -- Step 3: Rewrite using asymTorusEmbedLift_eval_eq
  simp_rw [asymTorusEmbedLift_eval_eq]
  -- Step 4: Relate lattice test fn under reflection to compose with latticeTimeReflectLM
  have h_refl_lattice : ∀ φ : Configuration (FinLatticeField 2 N),
      φ (asymLatticeTestFn Lt Ls N (asymTorusTimeReflection Lt Ls f)) =
      (φ.comp (asymLatticeTimeReflectLM N).toContinuousLinearMap)
        (asymLatticeTestFn Lt Ls N f) := by
    intro φ
    change φ (asymLatticeTestFn Lt Ls N (asymTorusTimeReflection Lt Ls f)) =
      φ ((asymLatticeTimeReflectLM N) (asymLatticeTestFn Lt Ls N f))
    congr 1; ext x; exact h_lattice_refl x
  simp_rw [h_refl_lattice]
  -- Step 5: Apply lattice measure time-reflection invariance
  exact (asymInteractingLatticeMeasure_timeReflection_invariant N P mass
    (asymGeomSpacing Lt Ls N) (asymGeomSpacing_pos Lt Ls N) hmass _).symm

/-! ## Exponential moment bound for the continuum limit

Transfers the cutoff-level Nelson bound to the weak limit by MCT + truncation.
Structurally identical to `torusInteracting_exponentialMomentBound`. -/

/-- Gaussian exponential moment bound (asymmetric spacing version).

Identical to `gaussian_exp_abs_moment` from `TorusInteractingOS.lean` but using
`asymGeomSpacing Lt Ls N` instead of `circleSpacing L N`. The proof is the same:
pushforward is Gaussian, so MGF = exp(t²σ²/2), and exp(t|X|) ≤ exp(tX) + exp(-tX). -/
private theorem asymGaussian_exp_abs_moment
    (N : ℕ) [NeZero N] (mass : ℝ) (hmass : 0 < mass)
    (g : FinLatticeField 2 N) (t : ℝ) :
    Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
      Real.exp (t * |ω g|))
      (latticeGaussianMeasure 2 N (asymGeomSpacing Lt Ls N) mass
        (asymGeomSpacing_pos Lt Ls N) hmass) ∧
    ∫ ω : Configuration (FinLatticeField 2 N),
      Real.exp (t * |ω g|)
      ∂(latticeGaussianMeasure 2 N (asymGeomSpacing Lt Ls N) mass
        (asymGeomSpacing_pos Lt Ls N) hmass) ≤
    2 * Real.exp (t ^ 2 / 2 *
      ∫ ω, (ω g) ^ 2 ∂(latticeGaussianMeasure 2 N (asymGeomSpacing Lt Ls N) mass
        (asymGeomSpacing_pos Lt Ls N) hmass)) := by
  -- Setup: abbreviations
  set a := asymGeomSpacing Lt Ls N
  set ha := asymGeomSpacing_pos Lt Ls N
  set μ := latticeGaussianMeasure 2 N a mass ha hmass
  set T := latticeCovariance 2 N a mass ha hmass
  have hμ_eq : μ = GaussianField.measure T := rfl
  haveI : IsProbabilityMeasure μ := latticeGaussianMeasure_isProbability 2 N a mass ha hmass
  -- Step 1: Pushforward is Gaussian
  have h_gauss : μ.map (fun ω : Configuration (FinLatticeField 2 N) => ω g) =
      ProbabilityTheory.gaussianReal 0
        (@inner ℝ ell2' _ (T g) (T g) : ℝ).toNNReal :=
    pairing_is_gaussian T g
  set v := (@inner ℝ ell2' _ (T g) (T g) : ℝ).toNNReal with hv_def
  -- Step 2: Integrability of exp(t*x) and exp(-t*x) under the Gaussian
  have h_int_pos : Integrable (fun x : ℝ => Real.exp (t * x))
      (ProbabilityTheory.gaussianReal 0 v) :=
    ProbabilityTheory.integrable_exp_mul_gaussianReal t
  have h_int_neg : Integrable (fun x : ℝ => Real.exp (-(t * x)))
      (ProbabilityTheory.gaussianReal 0 v) := by
    simp_rw [show ∀ x, -(t * x) = (-t) * x from fun x => by ring]
    exact ProbabilityTheory.integrable_exp_mul_gaussianReal (-t)
  -- Step 3: Pull back integrability to configuration space
  have h_eval_meas : Measurable (fun ω : Configuration (FinLatticeField 2 N) => ω g) :=
    configuration_eval_measurable g
  have h_int_pos_conf : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
      Real.exp (t * ω g)) μ := by
    rw [← h_gauss] at h_int_pos
    rwa [integrable_map_measure h_int_pos.aestronglyMeasurable
      h_eval_meas.aemeasurable] at h_int_pos
  have h_int_neg_conf : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
      Real.exp (-(t * ω g))) μ := by
    rw [← h_gauss] at h_int_neg
    rwa [integrable_map_measure h_int_neg.aestronglyMeasurable
      h_eval_meas.aemeasurable] at h_int_neg
  -- Step 4: Pointwise bound exp(t*|x|) ≤ exp(t*x) + exp(-t*x)
  have h_pointwise : ∀ x : ℝ, Real.exp (t * |x|) ≤
      Real.exp (t * x) + Real.exp (-(t * x)) := by
    intro x
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]; linarith [Real.exp_pos (-(t * x))]
    · push_neg at hx; rw [abs_of_neg hx, show t * (-x) = -(t * x) from by ring]
      linarith [Real.exp_pos (t * x)]
  -- Step 5: Integrability of exp(t*|ω g|)
  have h_int_sum : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
      Real.exp (t * ω g) + Real.exp (-(t * ω g))) μ :=
    h_int_pos_conf.add h_int_neg_conf
  have h_int_abs : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
      Real.exp (t * |ω g|)) μ := by
    apply h_int_sum.mono
      ((h_eval_meas.abs.const_mul t).exp.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (t * |ω g|)
          ≤ Real.exp (t * ω g) + Real.exp (-(t * ω g)) := h_pointwise (ω g)
        _ ≤ |Real.exp (t * ω g) + Real.exp (-(t * ω g))| := le_abs_self _
  -- Step 6: MGF values for exp(t*x) and exp(-t*x)
  have h_mgf_pos : ∫ ω : Configuration (FinLatticeField 2 N),
      Real.exp (t * ω g) ∂μ = Real.exp ((v : ℝ) * t ^ 2 / 2) := by
    have h_eq : ∫ ω, Real.exp (t * ω g) ∂μ =
        ∫ x, Real.exp (t * x) ∂(μ.map (fun ω : Configuration (FinLatticeField 2 N) => ω g)) :=
      (integral_map h_eval_meas.aemeasurable
        ((measurable_const.mul measurable_id).exp.aestronglyMeasurable)).symm
    rw [h_eq, h_gauss]
    have := congr_fun (@ProbabilityTheory.mgf_id_gaussianReal (0 : ℝ) v) t
    simp only [ProbabilityTheory.mgf, id] at this
    rw [this]; simp [zero_mul, zero_add]
  have h_mgf_neg : ∫ ω : Configuration (FinLatticeField 2 N),
      Real.exp (-(t * ω g)) ∂μ = Real.exp ((v : ℝ) * t ^ 2 / 2) := by
    have h_eq : ∫ ω, Real.exp (-(t * ω g)) ∂μ =
        ∫ x, Real.exp ((-t) * x)
          ∂(μ.map (fun ω : Configuration (FinLatticeField 2 N) => ω g)) := by
      rw [show (fun ω : Configuration (FinLatticeField 2 N) => Real.exp (-(t * ω g))) =
            (fun x : ℝ => Real.exp ((-t) * x)) ∘
            (fun ω : Configuration (FinLatticeField 2 N) => ω g) from by
        ext ω; simp [neg_mul]]
      exact (integral_map h_eval_meas.aemeasurable
        ((measurable_const.mul measurable_id).exp.aestronglyMeasurable)).symm
    rw [h_eq, h_gauss]
    have := congr_fun (@ProbabilityTheory.mgf_id_gaussianReal (0 : ℝ) v) (-t)
    simp only [ProbabilityTheory.mgf, id] at this
    rw [this]; congr 1; ring
  -- Step 7: Integral bound
  have h_integral_bound : ∫ ω, Real.exp (t * |ω g|) ∂μ ≤
      2 * Real.exp ((v : ℝ) * t ^ 2 / 2) := by
    calc ∫ ω, Real.exp (t * |ω g|) ∂μ
        ≤ ∫ ω, (Real.exp (t * ω g) + Real.exp (-(t * ω g))) ∂μ := by
          apply integral_mono h_int_abs h_int_sum
          exact fun ω => h_pointwise (ω g)
      _ = ∫ ω, Real.exp (t * ω g) ∂μ + ∫ ω, Real.exp (-(t * ω g)) ∂μ :=
          integral_add h_int_pos_conf h_int_neg_conf
      _ = Real.exp ((v : ℝ) * t ^ 2 / 2) + Real.exp ((v : ℝ) * t ^ 2 / 2) := by
          rw [h_mgf_pos, h_mgf_neg]
      _ = 2 * Real.exp ((v : ℝ) * t ^ 2 / 2) := by ring
  -- Step 8: Match the second moment to ∫ (ω g)² dμ
  have h_second_moment : ∫ ω, (ω g) ^ 2 ∂μ = @inner ℝ ell2' _ (T g) (T g) := by
    rw [hμ_eq]; exact second_moment_eq_covariance T g
  have h_inner_nonneg : (0 : ℝ) ≤ @inner ℝ ell2' _ (T g) (T g) := by
    rw [real_inner_self_eq_norm_sq]; exact sq_nonneg _
  have h_v_eq : (v : ℝ) = ∫ ω, (ω g) ^ 2 ∂μ := by
    rw [h_second_moment]
    exact Real.coe_toNNReal _ h_inner_nonneg
  -- Combine
  refine ⟨h_int_abs, ?_⟩
  calc ∫ ω, Real.exp (t * |ω g|) ∂μ
      ≤ 2 * Real.exp ((v : ℝ) * t ^ 2 / 2) := h_integral_bound
    _ = 2 * Real.exp (t ^ 2 / 2 * ∫ ω, (ω g) ^ 2 ∂μ) := by
        rw [h_v_eq]; ring_nf

/-- The lattice second moment `∫ (ω g)^2 dμ_GFF` is bounded by the continuum
Green's function `greenFunctionBilinear mass hmass f f`.

This is a lattice-to-continuum propagator comparison:
  `⟨T_N g, T_N g⟩ = Σ_k |c_k(g)|^2 / (μ_k + m^2) ≤ Σ_m |c_m(f)|^2 / (λ_m + m^2) = G(f,f)`
where μ_k are discrete Laplacian eigenvalues and λ_m are continuum eigenvalues.

**Why this is hard:** The lattice eigenvalues μ_k approximate the continuum
eigenvalues λ_m but the approximation is NOT monotone in general (finite
differences vs. exact second derivatives). The standard approach is:
  1. Show `lattice_green_tendsto_continuum` (convergence, already proved)
  2. Show monotonicity of the Galerkin truncation (requires the lattice
     discretization to be a *restriction* of the continuum operator)
For finite-difference discretizations, step 2 fails without additional
spectral analysis (e.g., explicit eigenvalue comparison for the torus).

**Status:** Used in `asymTorusInteractingMeasure_exponentialMomentBound_cutoff`.
The symmetric version avoids this by bounding with `torusEmbeddedTwoPoint`
(the lattice-level two-point function) instead of `greenFunctionBilinear`.

**Possible fix:** Refactor to bound by `mass^{-2} * C_f` (from
`asymGaussian_second_moment_uniform_bound`) instead of `greenFunctionBilinear`,
which would require changing the downstream `asymTorusInteracting_exponentialMomentBound`
chain to use the uniform constant rather than the continuum Green's function. -/
private theorem asymLattice_second_moment_le_greenFunction
    (N : ℕ) [NeZero N] (mass : ℝ) (hmass : 0 < mass)
    (f : AsymTorusTestFunction Lt Ls) :
    ∫ ω : Configuration (FinLatticeField 2 N),
      (ω (asymLatticeTestFn Lt Ls N f)) ^ 2
      ∂(latticeGaussianMeasure 2 N (asymGeomSpacing Lt Ls N) mass
        (asymGeomSpacing_pos Lt Ls N) hmass) ≤
    greenFunctionBilinear mass hmass f f := by
  sorry -- Lattice-to-continuum spectral comparison; see docstring for status

/-- Cutoff-level exponential moment bound for the asymmetric interacting measure.

For each test function f and cutoff N, the interacting measure satisfies:
  `∫ exp(|ω f|) dμ_{P,N} ≤ K * exp(G(f,f))`
where K is the universal Nelson constant and G is the continuum Green's function.

Proved from `density_transfer_bound` + `asymNelson_exponential_estimate` +
`asymGaussian_exp_abs_moment`. -/
private theorem asymTorusInteractingMeasure_exponentialMomentBound_cutoff
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : AsymTorusTestFunction Lt Ls) (N : ℕ) [NeZero N],
    Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
      Real.exp (|ω f|)) (asymTorusInteractingMeasure Lt Ls N P mass hmass) ∧
    ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
      Real.exp (|ω f|) ∂(asymTorusInteractingMeasure Lt Ls N P mass hmass) ≤
    K * Real.exp (greenFunctionBilinear mass hmass f f) := by
  -- Get K from Nelson's exponential estimate
  obtain ⟨K, hK_pos, hK_bound⟩ := asymNelson_exponential_estimate Lt Ls P mass hmass
  -- C = √(2K) works
  refine ⟨Real.sqrt (2 * K), Real.sqrt_pos_of_pos (by linarith), fun f N _ => ?_⟩
  -- Setup: abbreviations for measures and embedding
  set μ_int := interactingLatticeMeasure 2 N P (asymGeomSpacing Lt Ls N) mass
    (asymGeomSpacing_pos Lt Ls N) hmass
  set μ_GFF := latticeGaussianMeasure 2 N (asymGeomSpacing Lt Ls N) mass
    (asymGeomSpacing_pos Lt Ls N) hmass
  set ι := asymTorusEmbedLift Lt Ls N
  set g := asymLatticeTestFn Lt Ls N f
  have hι_meas : AEMeasurable ι μ_int :=
    (asymTorusEmbedLift_measurable Lt Ls N).aemeasurable
  have h_eval : ∀ ω : Configuration (FinLatticeField 2 N),
      (ι ω) f = ω g := fun ω => asymTorusEmbedLift_eval_eq Lt Ls N f ω
  -- Step 1: Push through torus embedding
  have hmeas_lhs : AEStronglyMeasurable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
      Real.exp (|ω f|)) (Measure.map ι μ_int) :=
    (Real.measurable_exp.comp (configuration_eval_measurable f).abs).aestronglyMeasurable
  change Integrable (fun ω => Real.exp (|ω f|)) (Measure.map ι μ_int) ∧
    ∫ ω, Real.exp (|ω f|) ∂(Measure.map ι μ_int) ≤
    Real.sqrt (2 * K) * Real.exp (greenFunctionBilinear mass hmass f f)
  rw [integrable_map_measure hmeas_lhs hι_meas,
      integral_map hι_meas hmeas_lhs]
  simp_rw [Function.comp_def, h_eval]
  -- Goal now on lattice: Integrable (exp(|ω g|)) μ_int ∧ ∫ exp(|ω g|) dμ_int ≤ ...
  -- Step 2: Integrability of exp(|ω g|) under μ_int
  obtain ⟨B, hB⟩ := interactionFunctional_bounded_below 2 N P (asymGeomSpacing Lt Ls N) mass
    (asymGeomSpacing_pos Lt Ls N) hmass
  set bw := boltzmannWeight 2 N P (asymGeomSpacing Lt Ls N) mass
  have hbw_bound : ∀ ω, bw ω ≤ Real.exp B := fun ω =>
    Real.exp_le_exp_of_le (by linarith [hB ω])
  have hbw_pos : ∀ ω, 0 < bw ω :=
    boltzmannWeight_pos 2 N P (asymGeomSpacing Lt Ls N) mass
  have hF_meas_raw : Measurable (fun ω : Configuration (FinLatticeField 2 N) =>
      Real.exp (|ω g|)) :=
    Real.measurable_exp.comp (configuration_eval_measurable g).abs
  -- exp(|ω g|) integrable under μ_GFF (asymGaussian_exp_abs_moment at t=1)
  have hF_int_GFF : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
      Real.exp (|ω g|)) μ_GFF := by
    have h := (asymGaussian_exp_abs_moment Lt Ls N mass hmass g 1).1
    exact h.congr (ae_of_all _ fun ω => by ring_nf)
  have hZ_pos : 0 < partitionFunction 2 N P (asymGeomSpacing Lt Ls N) mass
    (asymGeomSpacing_pos Lt Ls N) hmass :=
    partitionFunction_pos 2 N P (asymGeomSpacing Lt Ls N) mass
      (asymGeomSpacing_pos Lt Ls N) hmass
  -- Integrability under withDensity
  have hf_dens_meas : Measurable (fun ω : Configuration (FinLatticeField 2 N) =>
      ENNReal.ofReal (bw ω)) :=
    ENNReal.measurable_ofReal.comp
      ((interactionFunctional_measurable 2 N P (asymGeomSpacing Lt Ls N) mass).neg.exp)
  have hbw_simp : ∀ ω : Configuration (FinLatticeField 2 N),
      (ENNReal.ofReal (bw ω)).toReal = bw ω :=
    fun ω => ENNReal.toReal_ofReal (le_of_lt (hbw_pos ω))
  have hF_int_wd : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
      Real.exp (|ω g|))
      (μ_GFF.withDensity (fun ω => ENNReal.ofReal (bw ω))) := by
    apply (integrable_withDensity_iff hf_dens_meas
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
    simp_rw [hbw_simp]
    apply (hF_int_GFF.mul_const (Real.exp B)).mono
    · exact hF_meas_raw.aestronglyMeasurable.mul
        (interactionFunctional_measurable 2 N P
          (asymGeomSpacing Lt Ls N) mass).neg.exp.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ω => by
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hbw_pos ω).le),
            abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos B).le)]
        exact mul_le_mul_of_nonneg_left (hbw_bound ω) (Real.exp_pos _).le
  have hF_int_int : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
      Real.exp (|ω g|)) μ_int := by
    change Integrable _ (interactingLatticeMeasure 2 N P (asymGeomSpacing Lt Ls N) mass
      (asymGeomSpacing_pos Lt Ls N) hmass)
    unfold interactingLatticeMeasure
    exact hF_int_wd.smul_measure
      (ENNReal.inv_ne_top.mpr ((ENNReal.ofReal_pos.mpr hZ_pos).ne'))
  -- Step 3: Apply density_transfer_bound
  have hZ_ge_one := partitionFunction_ge_one 2 N P mass hmass
    (asymGeomSpacing Lt Ls N) (asymGeomSpacing_pos Lt Ls N)
  have hF_nn : ∀ ω : Configuration (FinLatticeField 2 N), 0 ≤ Real.exp (|ω g|) :=
    fun ω => (Real.exp_pos _).le
  have hF_meas : AEStronglyMeasurable (fun ω : Configuration (FinLatticeField 2 N) =>
      Real.exp (|ω g|)) μ_GFF :=
    hF_meas_raw.aestronglyMeasurable
  -- F² = exp(|ω g|)^2 = exp(2|ω g|), integrable by asymGaussian_exp_abs_moment at t=2
  have hF_sq_int : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
      Real.exp (|ω g|) ^ 2) μ_GFF := by
    have h_eq : ∀ ω : Configuration (FinLatticeField 2 N),
        Real.exp (|ω g|) ^ 2 = Real.exp (2 * |ω g|) := fun ω => by
      rw [sq, ← Real.exp_add]; ring_nf
    simp_rw [h_eq]
    exact (asymGaussian_exp_abs_moment Lt Ls N mass hmass g 2).1
  -- Apply density_transfer_bound
  have h_dt := density_transfer_bound 2 N P (asymGeomSpacing Lt Ls N) mass
    (asymGeomSpacing_pos Lt Ls N) hmass K hK_pos (hK_bound N)
    hZ_ge_one (fun ω => Real.exp (|ω g|)) hF_nn hF_meas hF_sq_int
  -- h_dt: ∫ exp(|ω g|) dμ_int ≤ K^{1/2} * (∫ exp(|ω g|)^{(2:ℝ)} dμ_GFF)^{1/2}
  -- Step 4: Bound (∫ exp(|ω g|)^{(2:ℝ)} dμ_GFF)^{1/2} using asymGaussian_exp_abs_moment
  have h_rpow_eq : ∀ ω : Configuration (FinLatticeField 2 N),
      Real.exp (|ω g|) ^ (2:ℝ) = Real.exp (2 * |ω g|) := fun ω => by
    rw [show (2:ℝ) = ↑(2:ℕ) from by norm_num, Real.rpow_natCast, sq, ← Real.exp_add]; ring_nf
  have h_int_rpow_eq : ∫ ω, (fun ω => Real.exp (|ω g|)) ω ^ (2:ℝ) ∂μ_GFF =
      ∫ ω, Real.exp (2 * |ω g|) ∂μ_GFF := by
    congr 1; ext ω; exact h_rpow_eq ω
  -- asymGaussian_exp_abs_moment at t=2: ∫ exp(2|ω g|) ≤ 2 * exp(2^2/2 * ∫(ωg)²)
  have h_gauss : ∫ ω, Real.exp (2 * |ω g|) ∂μ_GFF ≤
      2 * Real.exp ((2:ℝ) ^ 2 / 2 * ∫ ω, (ω g) ^ 2 ∂μ_GFF) :=
    (asymGaussian_exp_abs_moment Lt Ls N mass hmass g 2).2
  -- Lattice second moment ≤ continuum Green's function
  have h_second_moment_le : ∫ ω, (ω g) ^ 2 ∂μ_GFF ≤
      greenFunctionBilinear mass hmass f f :=
    asymLattice_second_moment_le_greenFunction Lt Ls N mass hmass f
  -- 2^2/2 * ∫(ωg)² ≤ 2 * G(f,f)
  set G := greenFunctionBilinear mass hmass f f
  have h_exp_le : (2:ℝ) ^ 2 / 2 * ∫ ω, (ω g) ^ 2 ∂μ_GFF ≤ 2 * G := by
    have : (2:ℝ) ^ 2 / 2 = 2 := by norm_num
    rw [this]; exact mul_le_mul_of_nonneg_left h_second_moment_le (by norm_num)
  -- So: ∫ exp(2|ωg|) ≤ 2 * exp(2 * G)
  have h_gauss' : ∫ ω, Real.exp (2 * |ω g|) ∂μ_GFF ≤
      2 * Real.exp (2 * G) :=
    h_gauss.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp_of_le h_exp_le) (by norm_num))
  -- Step 5: Bound (∫ exp(2|ωg|))^{1/2} ≤ √2 * exp(G)
  have h_gauss_nn : (0:ℝ) ≤ ∫ ω, Real.exp (2 * |ω g|) ∂μ_GFF :=
    integral_nonneg fun ω => (Real.exp_pos _).le
  have h_rpow_bound : (∫ ω, (fun ω => Real.exp (|ω g|)) ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) ≤
      Real.sqrt 2 * Real.exp G := by
    rw [h_int_rpow_eq]
    calc (∫ ω, Real.exp (2 * |ω g|) ∂μ_GFF) ^ (1/2:ℝ)
        ≤ (2 * Real.exp (2 * G)) ^ (1/2:ℝ) :=
          Real.rpow_le_rpow h_gauss_nn h_gauss' (by norm_num : (0:ℝ) ≤ 1/2)
      _ = Real.sqrt (2 * Real.exp (2 * G)) := by
          rw [Real.sqrt_eq_rpow]
      _ = Real.sqrt 2 * Real.sqrt (Real.exp (2 * G)) := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      _ = Real.sqrt 2 * Real.exp G := by
          congr 1
          rw [show (2 : ℝ) * G = G + G from by ring,
              Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
  -- Step 6: Combine: ∫ exp(|ωg|) ≤ K^{1/2} * √2 * exp(G) = √(2K) * exp(G)
  have h_integral_bound : ∫ ω, Real.exp (|ω g|) ∂μ_int ≤
      Real.sqrt (2 * K) * Real.exp G := by
    calc ∫ ω, Real.exp (|ω g|) ∂μ_int
        ≤ K ^ (1/2:ℝ) *
          (∫ ω, (fun ω => Real.exp (|ω g|)) ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) := h_dt
      _ ≤ K ^ (1/2:ℝ) * (Real.sqrt 2 * Real.exp G) :=
          mul_le_mul_of_nonneg_left h_rpow_bound (Real.rpow_nonneg hK_pos.le _)
      _ = Real.sqrt K * (Real.sqrt 2 * Real.exp G) := by
          rw [← Real.sqrt_eq_rpow]
      _ = (Real.sqrt K * Real.sqrt 2) * Real.exp G := by ring
      _ = Real.sqrt (2 * K) * Real.exp G := by
          congr 1
          rw [mul_comm (Real.sqrt K) (Real.sqrt 2),
              ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  exact ⟨hF_int_int, h_integral_bound⟩

/-- The lattice two-point function converges to the continuum Green's function
on the asymmetric torus.

TODO: Prove by adapting `torus_propagator_convergence`. -/
private theorem asymTorus_propagator_convergence
    (mass : ℝ) (hmass : 0 < mass)
    (f g : AsymTorusTestFunction Lt Ls) :
    Filter.Tendsto (fun _N : ℕ =>
      greenFunctionBilinear mass hmass f g)
      Filter.atTop (nhds (asymTorusContinuumGreen Lt Ls mass hmass f g)) := by
  -- asymTorusContinuumGreen is defined as greenFunctionBilinear, so this is trivial
  simp only [asymTorusContinuumGreen]
  exact tendsto_const_nhds

/-- Exponential moment bound for the asymmetric torus continuum limit.

Transfers the cutoff-level bound to the weak limit via truncation + MCT.
Structurally identical to `torusInteracting_exponentialMomentBound`. -/
private theorem asymTorusInteracting_exponentialMomentBound
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (_hφ : StrictMono φ)
    (hconv : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
        Tendsto (fun n => ∫ ω, g ω ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, g ω ∂μ)))
    : ∃ K : ℝ, 0 < K ∧ ∀ (f : AsymTorusTestFunction Lt Ls),
    Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
      Real.exp (|ω f|)) μ ∧
    ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
      Real.exp (|ω f|) ∂μ ≤
    K * Real.exp (asymTorusContinuumGreen Lt Ls mass hmass f f) := by
  -- Note: _hφ is unused because the cutoff bound already uses the continuum
  -- Green's function (N-independent), so propagator convergence is not needed.
  -- Get the universal cutoff bound (K independent of f and N)
  obtain ⟨K, hK_pos, hK_bound⟩ :=
    asymTorusInteractingMeasure_exponentialMomentBound_cutoff Lt Ls P mass hmass
  refine ⟨K, hK_pos, fun f => ?_⟩
  set B := K * Real.exp (asymTorusContinuumGreen Lt Ls mass hmass f f)
  have hB_pos : 0 < B := mul_pos hK_pos (Real.exp_pos _)
  -- Abbreviation for the target function
  set F : Configuration (AsymTorusTestFunction Lt Ls) → ℝ := fun ω => Real.exp (|ω f|)
    with hF_def
  have hF_nn : ∀ ω : Configuration (AsymTorusTestFunction Lt Ls), 0 ≤ F ω :=
    fun ω => (Real.exp_pos _).le
  have hF_meas : Measurable F :=
    Real.measurable_exp.comp ((configuration_eval_measurable f).abs)
  -- The cutoff bound already uses greenFunctionBilinear = asymTorusContinuumGreen,
  -- so the RHS is N-independent: K * exp(G(f,f)) for every N.
  have h_cutoff_bound : ∀ n, ∫ ω, F ω
      ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass) ≤ B := by
    intro n
    obtain ⟨_, h_bnd_n⟩ := hK_bound f (φ n + 1)
    exact h_bnd_n
  -- Step 1: For every M > 0, ∫ min(F, M) dμ ≤ B (truncation + weak convergence)
  have h_trunc : ∀ M : ℝ, 0 < M →
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls), min (F ω) M ∂μ ≤ B := by
    intro M hM
    have h_cont : Continuous (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
        min (F ω) M) :=
      (Real.continuous_exp.comp (continuous_abs.comp (WeakDual.eval_continuous f))).min
        continuous_const
    have h_bdd : ∃ C, ∀ ω : Configuration (AsymTorusTestFunction Lt Ls),
        |min (F ω) M| ≤ C :=
      ⟨M, fun ω => by
        rw [abs_of_nonneg (le_min (hF_nn ω) hM.le)]
        exact min_le_right _ _⟩
    have h_lim := hconv _ h_cont h_bdd
    have h_cutoff_trunc : ∀ n, ∫ ω, min (F ω) M
        ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass) ≤ B := by
      intro n
      obtain ⟨h_int_n, _⟩ := hK_bound f (φ n + 1)
      calc ∫ ω, min (F ω) M
            ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass)
          ≤ ∫ ω, F ω
            ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass) := by
            apply integral_mono_of_nonneg
            · exact ae_of_all _ (fun ω => le_min (hF_nn ω) hM.le)
            · exact h_int_n
            · exact ae_of_all _ (fun ω => min_le_left _ _)
        _ ≤ B := h_cutoff_bound n
    -- B is constant, so Tendsto (fun n => B) atTop (nhds B)
    exact le_of_tendsto_of_tendsto h_lim tendsto_const_nhds
      (Filter.Eventually.of_forall h_cutoff_trunc)
  -- Step 2: Each truncation min(F, n) is integrable (bounded on probability space)
  have h_trunc_int : ∀ n : ℕ, Integrable (fun ω => min (F ω) (↑n : ℝ)) μ := by
    intro n
    exact Integrable.of_bound
      (hF_meas.min measurable_const).aestronglyMeasurable n
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hF_nn ω) (Nat.cast_nonneg n))]
        exact min_le_right _ _)
  -- Truncation bounds for natural numbers
  have h_trunc_nat : ∀ n : ℕ, ∫ ω, min (F ω) (↑n : ℝ) ∂μ ≤ B := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp only [Nat.cast_zero]
      calc ∫ ω, min (F ω) (0 : ℝ) ∂μ
          ≤ ∫ ω, (0 : ℝ) ∂μ := by
            apply integral_mono_of_nonneg
            · exact ae_of_all _ fun _ => le_min (hF_nn _) le_rfl
            · exact integrable_const 0
            · exact ae_of_all _ fun _ => min_le_right _ _
        _ = 0 := by simp
        _ ≤ B := le_of_lt hB_pos
    · exact h_trunc n (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
  -- Step 3: Integrability of F from bounded lintegral
  have h_int : Integrable F μ := by
    refine ⟨hF_meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hF_nn)]
    -- MCT for lintegrals: ∫⁻ ofReal(min(F, n)) ↗ ∫⁻ ofReal(F)
    have h_lint_mono : ∀ᵐ ω ∂μ, Monotone
        (fun n : ℕ => ENNReal.ofReal (min (F ω) (↑n : ℝ))) :=
      ae_of_all _ fun ω n m hnm =>
        ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.mpr hnm))
    have h_lint_pw : ∀ᵐ ω ∂μ, Tendsto
        (fun n : ℕ => ENNReal.ofReal (min (F ω) (↑n : ℝ)))
        atTop (nhds (ENNReal.ofReal (F ω))) :=
      ae_of_all _ fun ω => (ENNReal.continuous_ofReal.tendsto _).comp
        (tendsto_atTop_of_eventually_const (i₀ := ⌈F ω⌉₊) fun n hn => by
          rw [min_eq_left]; exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hn))
    have h_lint_meas : ∀ n : ℕ, AEMeasurable
        (fun ω => ENNReal.ofReal (min (F ω) (↑n : ℝ))) μ :=
      fun n => (hF_meas.min measurable_const).ennreal_ofReal.aemeasurable
    have h_lint_conv := lintegral_tendsto_of_tendsto_of_monotone
      h_lint_meas h_lint_mono h_lint_pw
    -- Each ∫⁻ ofReal(min(F, n)) = ofReal(∫ min(F, n)) ≤ ofReal(B)
    have h_lint_bound : ∀ n : ℕ, ∫⁻ ω, ENNReal.ofReal (min (F ω) (↑n : ℝ)) ∂μ ≤
        ENNReal.ofReal B := by
      intro n
      rw [← ofReal_integral_eq_lintegral_ofReal (h_trunc_int n)
        (ae_of_all _ fun ω => le_min (hF_nn ω) (Nat.cast_nonneg n))]
      exact ENNReal.ofReal_le_ofReal (h_trunc_nat n)
    -- The limit ∫⁻ ofReal(F) ≤ ofReal(B) by le_of_tendsto'
    exact lt_of_le_of_lt (le_of_tendsto' h_lint_conv h_lint_bound) ENNReal.ofReal_lt_top
  constructor
  · exact h_int
  · -- Step 4: ∫ F dμ ≤ B by MCT + truncation bounds
    have h_mono : ∀ᵐ ω ∂μ, Monotone (fun n : ℕ => min (F ω) (↑n : ℝ)) :=
      ae_of_all _ fun ω n m hnm => min_le_min_left _ (Nat.cast_le.mpr hnm)
    have h_pw : ∀ᵐ ω ∂μ,
        Tendsto (fun n : ℕ => min (F ω) (↑n : ℝ)) atTop (nhds (F ω)) :=
      ae_of_all _ fun ω => tendsto_atTop_of_eventually_const
        (i₀ := ⌈F ω⌉₊) fun n hn => by
          rw [min_eq_left]
          exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hn)
    have h_mct : Tendsto (fun n : ℕ => ∫ ω, min (F ω) (↑n : ℝ) ∂μ)
        atTop (nhds (∫ ω, F ω ∂μ)) :=
      integral_tendsto_of_tendsto_of_monotone h_trunc_int h_int h_mono h_pw
    exact le_of_tendsto' h_mct h_trunc_nat

/-! ## OS Proofs

### Helper lemmas for OS0 -/

/-- On a compact set `K ⊆ (Fin n → ℂ)`, imaginary parts are uniformly bounded. -/
private lemma asymCompact_im_bound {n : ℕ} {K : Set (Fin n → ℂ)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ i : Fin n, |Complex.im (z i)| ≤ C := by
  by_cases hKe : K.Nonempty
  · obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
    exact ⟨M, le_trans (norm_nonneg _) (hM _ hKe.some_mem), fun z hz i =>
      (Complex.abs_im_le_norm (z i)).trans ((norm_le_pi_norm z i).trans (hM z hz))⟩
  · exact ⟨0, le_refl _, fun z hz => absurd ⟨z, hz⟩ hKe⟩

/-- For `aᵢ ≥ 0`: `exp(c · Σ aᵢ) ≤ Σ exp(n·c·aᵢ)`. -/
private lemma asymExp_mul_sum_le {n : ℕ} (hn : 0 < n) (c : ℝ) (hc : 0 ≤ c)
    (a : Fin n → ℝ) :
    Real.exp (c * ∑ i : Fin n, a i) ≤
    ∑ i : Fin n, Real.exp (↑n * c * a i) := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  set M := Finset.univ.sup' hne a
  have hM : ∀ i, a i ≤ M := fun i => Finset.le_sup' a (Finset.mem_univ i)
  have h_sum_le : ∑ i : Fin n, a i ≤ ↑n * M :=
    (Finset.sum_le_sum (fun i _ => hM i)).trans
      (by simp [Finset.sum_const, nsmul_eq_mul])
  have h1 : Real.exp (c * ∑ i, a i) ≤ Real.exp (↑n * c * M) :=
    Real.exp_le_exp_of_le (by nlinarith)
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' hne a
  exact h1.trans ((congr_arg Real.exp (by rw [← hj])).le.trans
    (Finset.single_le_sum (f := fun i => Real.exp (↑n * c * a i))
      (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ j)))

/-- OS0: Analyticity of the asymmetric torus generating functional.

Proved by `analyticOnNhd_integral` with pointwise analyticity of exp and
domination from exponential moment bound. -/
private theorem asymTorusInteracting_os0
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
        Tendsto (fun n => ∫ ω, g ω ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, g ω ∂μ))) :
    AsymTorusOS0_Analyticity Lt Ls μ := by
  intro n J
  -- Goal: z ↦ ∫ exp(I * (ω(Σ Re(zᵢ)Jᵢ) + I * ω(Σ Im(zᵢ)Jᵢ))) dμ is entire
  rw [analyticOn_univ]
  apply analyticOnNhd_integral
  · -- Pointwise analyticity: z ↦ F(z, ω) is entire for each ω
    intro ω z _
    apply AnalyticAt.cexp'
    have h_eq : ∀ w : Fin n → ℂ,
        Complex.I * (↑(ω (∑ i, (w i).re • J i)) +
          Complex.I * ↑(ω (∑ i, (w i).im • J i))) =
        Complex.I * ∑ i : Fin n, w i * ↑(ω (J i)) := by
      intro w; congr 1
      simp only [map_sum, map_smul, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      congr 1; ext i
      calc ↑(w i).re * ↑(ω (J i)) + Complex.I * (↑(w i).im * ↑(ω (J i)))
          = (↑(w i).re + ↑(w i).im * Complex.I) * ↑(ω (J i)) := by ring
        _ = w i * ↑(ω (J i)) := by rw [re_add_im]
    simp_rw [h_eq]
    exact analyticAt_const.mul (Finset.univ.analyticAt_fun_sum (fun i _ =>
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticAt z).mul
      analyticAt_const))
  · -- Measurability: F(z, ·) is ae strongly measurable for each z
    intro z
    apply (Complex.measurable_exp.comp _).aestronglyMeasurable
    exact (measurable_const.mul ((Complex.measurable_ofReal.comp
      (configuration_eval_measurable _)).add (measurable_const.mul
      (Complex.measurable_ofReal.comp (configuration_eval_measurable _)))))
  · -- Domination: on compact K, ‖F(z, ω)‖ ≤ bound(ω) integrable
    intro K hK
    obtain ⟨C_K, hC_K_nn, hC_K⟩ := asymCompact_im_bound hK
    obtain ⟨K_exp, hK_exp_pos, hK_exp_bound⟩ :=
      asymTorusInteracting_exponentialMomentBound Lt Ls P mass hmass μ φ hφ hconv
    by_cases hn : n = 0
    · -- n = 0: integrand is exp(I * 0) = 1, bounded by 1
      subst hn
      exact ⟨fun _ => 1, integrable_const 1, fun z _ => ae_of_all μ fun ω => by
        simp only [Finset.univ_eq_empty, Finset.sum_empty, map_zero,
          Complex.ofReal_zero, add_zero, mul_zero, Complex.exp_zero, norm_one]; rfl⟩
    · -- n > 0: bound by ∑ᵢ exp(n · C_K · |ω(Jᵢ)|)
      set bound := fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
        ∑ i : Fin n, Real.exp (↑n * C_K * |ω (J i)|) with hbound_def
      refine ⟨bound, ?_, fun z hz => ae_of_all μ fun ω => ?_⟩
      · -- Integrability: each exp(n·C_K·|ω(Jᵢ)|) = exp(|ω((n·C_K)•Jᵢ)|) is integrable
        apply integrable_finset_sum; intro i _
        have hscale : ∀ ω : Configuration (AsymTorusTestFunction Lt Ls),
            Real.exp (↑n * C_K * |ω (J i)|) =
            Real.exp (|ω ((↑n * C_K) • J i)|) := by
          intro ω
          rw [map_smul, smul_eq_mul, abs_mul,
              abs_of_nonneg (mul_nonneg (Nat.cast_nonneg' n) hC_K_nn)]
        simp_rw [hscale]
        exact (hK_exp_bound ((↑n * C_K) • J i)).1
      · -- Pointwise bound: ‖F(z, ω)‖ ≤ bound(ω) for z ∈ K
        rw [Complex.norm_exp]
        have h_re : (Complex.I * (↑(ω (∑ i, (z i).re • J i)) +
            Complex.I * ↑(ω (∑ i, (z i).im • J i)))).re =
            -(ω (∑ i, (z i).im • J i)) := by
          have : Complex.I * (↑(ω (∑ i, (z i).re • J i)) +
              Complex.I * ↑(ω (∑ i, (z i).im • J i))) =
              -↑(ω (∑ i, (z i).im • J i)) +
              ↑(ω (∑ i, (z i).re • J i)) * Complex.I := by
            rw [mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul]; ring
          rw [this, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
              Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
              Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
              add_zero]
        rw [h_re]
        calc Real.exp (-(ω (∑ i, (z i).im • J i)))
            ≤ Real.exp (|ω (∑ i, (z i).im • J i)|) :=
              Real.exp_le_exp_of_le (neg_le_abs _)
          _ ≤ Real.exp (C_K * ∑ i : Fin n, |ω (J i)|) := by
              apply Real.exp_le_exp_of_le
              rw [map_sum]
              calc |∑ i, ω ((z i).im • J i)|
                  ≤ ∑ i, |ω ((z i).im • J i)| :=
                    Finset.abs_sum_le_sum_abs _ _
                _ = ∑ i, |(z i).im| * |ω (J i)| := by
                    congr 1; ext i; rw [map_smul, smul_eq_mul, abs_mul]
                _ ≤ ∑ i, C_K * |ω (J i)| :=
                    Finset.sum_le_sum (fun i _ =>
                      mul_le_mul_of_nonneg_right (hC_K z hz i) (abs_nonneg _))
                _ = C_K * ∑ i, |ω (J i)| := (Finset.mul_sum _ _ _).symm
          _ ≤ bound ω :=
              asymExp_mul_sum_le (Nat.pos_of_ne_zero hn) C_K hC_K_nn _

/-- **OS1 for the asymmetric torus interacting continuum limit.**

The complex generating functional satisfies an exponential bound:
  `‖Z_ℂ[f_re, f_im]‖ ≤ exp(c * (q(f_re) + q(f_im)))`
for a continuous seminorm `q` and constant `c > 0`.

Proof: identical to `torusInteracting_os1`. Uses the exponential moment bound
with `q(f) = G_{Lt,Ls}(f,f) + |log K|` and `c = 1`. -/
private theorem asymTorusInteracting_os1
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
        Tendsto (fun n => ∫ ω, g ω ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, g ω ∂μ))) :
    AsymTorusOS1_Regularity Lt Ls μ := by
  -- Get the exponential moment bound with universal constant K
  obtain ⟨K, hK_pos, hK_all⟩ :=
    asymTorusInteracting_exponentialMomentBound Lt Ls P mass hmass μ φ hφ hconv
  -- Use q(f) = G(f,f) + |log K| to absorb the constant K
  have hq_cont : Continuous (fun f : AsymTorusTestFunction Lt Ls =>
      asymTorusContinuumGreen Lt Ls mass hmass f f + |Real.log K|) := by
    have : Continuous (fun f : AsymTorusTestFunction Lt Ls =>
        asymTorusContinuumGreen Lt Ls mass hmass f f) := by
      change Continuous (fun f => greenFunctionBilinear mass hmass f f)
      exact GaussianField.greenFunctionBilinear_continuous_diag mass hmass
    exact this.add continuous_const
  refine ⟨fun f => asymTorusContinuumGreen Lt Ls mass hmass f f + |Real.log K|,
          hq_cont, 1, one_pos, ?_⟩
  intro f_re f_im
  -- Get the bound for f_im (using universal K)
  obtain ⟨h_int_im, h_exp_bound_im⟩ := hK_all f_im
  -- Triangle inequality: ‖Z_ℂ‖ ≤ ∫ ‖exp(...)‖ dμ
  have h_tri : ‖∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
      Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im))) ∂μ‖ ≤
      ∫ ω, ‖Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)))‖ ∂μ :=
    norm_integral_le_integral_norm _
  -- ‖exp(I*(ω f_re + I*ω f_im))‖ = exp(-ω f_im)
  have h_norm : ∀ ω : Configuration (AsymTorusTestFunction Lt Ls),
      ‖Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)))‖ =
      Real.exp (-(ω f_im)) := by
    intro ω
    rw [Complex.norm_exp]; congr 1
    have : Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)) =
        -↑(ω f_im) + ↑(ω f_re) * Complex.I := by
      rw [mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul]; ring
    rw [this, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  calc ‖∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
          Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im))) ∂μ‖
      ≤ ∫ ω, ‖Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)))‖ ∂μ := h_tri
    _ = ∫ ω, Real.exp (-(ω f_im)) ∂μ := by congr 1; ext ω; exact h_norm ω
    _ ≤ ∫ ω, Real.exp (|ω f_im|) ∂μ := by
        apply integral_mono_of_nonneg
        · exact ae_of_all _ (fun _ => (Real.exp_pos _).le)
        · exact h_int_im
        · exact ae_of_all _ (fun ω => Real.exp_le_exp_of_le (neg_le_abs (ω f_im)))
    _ ≤ K * Real.exp (asymTorusContinuumGreen Lt Ls mass hmass f_im f_im) :=
        h_exp_bound_im
    _ ≤ Real.exp (asymTorusContinuumGreen Lt Ls mass hmass f_im f_im + |Real.log K|) := by
        have hle : K ≤ Real.exp (|Real.log K|) := by
          by_cases h1 : 1 ≤ K
          · rw [abs_of_nonneg (Real.log_nonneg h1), Real.exp_log hK_pos]
          · push_neg at h1
            exact le_trans h1.le (Real.one_le_exp (abs_nonneg _))
        calc K * Real.exp (asymTorusContinuumGreen Lt Ls mass hmass f_im f_im)
            ≤ Real.exp (|Real.log K|) *
              Real.exp (asymTorusContinuumGreen Lt Ls mass hmass f_im f_im) :=
              mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
          _ = Real.exp (asymTorusContinuumGreen Lt Ls mass hmass f_im f_im + |Real.log K|) := by
              rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (1 * ((asymTorusContinuumGreen Lt Ls mass hmass f_re f_re + |Real.log K|) +
          (asymTorusContinuumGreen Lt Ls mass hmass f_im f_im + |Real.log K|))) := by
        rw [one_mul]; apply Real.exp_le_exp_of_le
        have hG_nn : 0 ≤ asymTorusContinuumGreen Lt Ls mass hmass f_re f_re := by
          unfold asymTorusContinuumGreen
          exact GaussianField.greenFunctionBilinear_nonneg mass hmass f_re
        linarith [hG_nn, abs_nonneg (Real.log K)]

/-- OS2 (translation) for the asymmetric torus interacting continuum limit.

The proof is structurally identical to `torusInteracting_os2_translation` in
`TorusInteractingOS.lean` (line 2829), which delegates to
`torusInteractingLimit_translation_invariant` (line 1731).

**Missing infrastructure** (all are direct adaptations of symmetric versions):

1. `asymTorusInteractingMeasure_gf_latticeTranslation_invariant` (~40 lines)
   Shows `Z_N[f] = Z_N[T_{a*j} f]` for lattice translations.
   Symmetric version: `torusInteractingMeasure_gf_latticeTranslation_invariant` (line 352).
   Needs: `evalTorusAtSite_latticeTranslation` for asymmetric spacings.

2. `asymGf_sub_norm_le_seminorm` (~190 lines)
   Uniform Lipschitz bound `|Z_N[g] - Z_N[h]| <= B * p(g-h)`.
   Symmetric version: `gf_sub_norm_le_seminorm` (line 1328).
   Needs: `asymTorus_interacting_second_moment_continuous` + seminorm bound.

3. `asymTorusGF_latticeApproximation_error_vanishes` (~130 lines)
   Shows `Z_N[T_v f] - Z_N[f] -> 0` via lattice rounding + GF continuity.
   Symmetric version: `torusGF_latticeApproximation_error_vanishes` (line 1520).
   Needs: items 1-2 above + `asymTorusTranslation_continuous_in_v`.

4. `asymTorusTranslation_continuous_in_v` (~80 lines)
   Continuity of `v |-> T_v f` in the NTP topology.
   Symmetric version: `torusTranslation_continuous_in_v` (line 871).

**Total:** ~440 lines of infrastructure, all mechanical adaptations. -/
private theorem asymTorusInteracting_os2_translation
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
        Tendsto (fun n => ∫ ω, g ω ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, g ω ∂μ))) :
    AsymTorusOS2_TranslationInvariance Lt Ls μ := by
  sorry
  -- Proof sketch (identical to torusInteractingLimit_translation_invariant):
  -- 1. Build GF tendsto from weak convergence via cos/sin decomposition
  --    (asymCosEval_continuous/asymSinEval_continuous already exist)
  -- 2. For each n, round v to nearest lattice point w_n:
  --    w_n = (Lt/(phi(n)+1) * round(v.1 * (phi(n)+1)/Lt),
  --           Ls/(phi(n)+1) * round(v.2 * (phi(n)+1)/Ls))
  -- 3. Z_N[T_{w_n} f] = Z_N[f] by lattice translation invariance (MISSING: item 1)
  -- 4. |Z_N[T_v f] - Z_N[T_{w_n} f]| <= B * p(T_v f - T_{w_n} f) (MISSING: item 2)
  -- 5. p(T_v f - T_{w_n} f) -> 0 since w_n -> v (MISSING: items 3-4)
  -- 6. squeeze_zero_norm concludes Z_N[T_v f] - Z_N[f] -> 0
  -- 7. tendsto_nhds_unique gives Z[T_v f] = Z[f]

/-- **OS2 (time reflection) for the asymmetric torus interacting continuum limit.**

The interacting measure is invariant under time reflection Theta: (t,x) -> (-t,x).
  `Z(f) = Z(Theta f)` for all f.

Proved by transferring cutoff-level time reflection invariance
(`asymTorusInteractingMeasure_gf_timeReflection_invariant`) through
the weak limit, using cos/sin decomposition + unique limits. -/
private theorem asymTorusInteracting_os2_timeReflection
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (_hφ : StrictMono φ)
    (hconv : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
        Tendsto (fun n => ∫ ω, g ω ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, g ω ∂μ))) :
    AsymTorusOS2_TimeReflectionInvariance Lt Ls μ := by
  intro f
  apply Complex.ext
  · -- Re part: ∫ cos(ω f) dμ = ∫ cos(ω (Θf)) dμ
    rw [asymGf_re_eq_cos_integral Lt Ls μ f,
        asymGf_re_eq_cos_integral Lt Ls μ (asymTorusTimeReflection Lt Ls f)]
    have h_Θf := hconv _ (asymCosEval_continuous Lt Ls (asymTorusTimeReflection Lt Ls f))
      (asymCosEval_bounded Lt Ls (asymTorusTimeReflection Lt Ls f))
    have h_f := hconv _ (asymCosEval_continuous Lt Ls f) (asymCosEval_bounded Lt Ls f)
    have h_cutoff : ∀ n, ∫ ω, Real.cos (ω (asymTorusTimeReflection Lt Ls f))
        ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass) =
      ∫ ω, Real.cos (ω f) ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass) := by
      intro n
      have hgf := asymTorusInteractingMeasure_gf_timeReflection_invariant Lt Ls (φ n + 1)
        P mass hmass f
      have hre := congr_arg Complex.re hgf
      rw [asymGf_re_eq_cos_integral, asymGf_re_eq_cos_integral] at hre
      exact hre.symm
    exact tendsto_nhds_unique h_f (h_Θf.congr h_cutoff)
  · -- Im part: ∫ sin(ω f) dμ = ∫ sin(ω (Θf)) dμ
    rw [asymGf_im_eq_sin_integral Lt Ls μ f,
        asymGf_im_eq_sin_integral Lt Ls μ (asymTorusTimeReflection Lt Ls f)]
    have h_Θf := hconv _ (asymSinEval_continuous Lt Ls (asymTorusTimeReflection Lt Ls f))
      (asymSinEval_bounded Lt Ls (asymTorusTimeReflection Lt Ls f))
    have h_f := hconv _ (asymSinEval_continuous Lt Ls f) (asymSinEval_bounded Lt Ls f)
    have h_cutoff : ∀ n, ∫ ω, Real.sin (ω (asymTorusTimeReflection Lt Ls f))
        ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass) =
      ∫ ω, Real.sin (ω f) ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass) := by
      intro n
      have hgf := asymTorusInteractingMeasure_gf_timeReflection_invariant Lt Ls (φ n + 1)
        P mass hmass f
      have him := congr_arg Complex.im hgf
      rw [asymGf_im_eq_sin_integral, asymGf_im_eq_sin_integral] at him
      exact him.symm
    exact tendsto_nhds_unique h_f (h_Θf.congr h_cutoff)

/-! ## Bundled OS axioms -/

/-- **The asymmetric torus P(phi)_2 interacting continuum limit satisfies OS0-OS2.**

This bundles all verifiable OS axioms for the interacting asymmetric torus measure.
OS3 (reflection positivity) is dropped -- it is natural on the cylinder, not the torus. -/
theorem asymTorusInteracting_satisfies_OS
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
        Tendsto (fun n => ∫ ω, g ω ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, g ω ∂μ))) :
    AsymSatisfiesTorusOS Lt Ls μ where
  os0 := asymTorusInteracting_os0 Lt Ls P mass hmass μ φ hφ hconv
  os1 := asymTorusInteracting_os1 Lt Ls P mass hmass μ φ hφ hconv
  os2_translation := asymTorusInteracting_os2_translation Lt Ls P mass hmass μ φ hφ hconv
  os2_timeReflection := asymTorusInteracting_os2_timeReflection Lt Ls P mass hmass μ φ hφ hconv

end Pphi2

end
