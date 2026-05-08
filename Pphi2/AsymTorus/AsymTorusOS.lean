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
import Pphi2.GeneralResults.FunctionalAnalysis
import Pphi2.GeneralResults.ComplexAnalysis
import Pphi2.OSProofs.OS2_WardIdentity
import GaussianField.Density

noncomputable section

-- `show` is used as an in-proof claim for clarity at several points; matches
-- the style of `TorusInteractingOS.lean` from which this proof is adapted.
-- Heartbeat bumps are needed for the asymmetric-torus unification goals.
-- The unscoped form is intentional.
set_option linter.style.setOption false
set_option linter.style.show false
set_option linter.style.maxHeartbeats false
set_option linter.flexible false
set_option linter.style.emptyLine false

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
  simpa [asymTorusGeneratingFunctional] using configuration_expIntegral_re_eq_integral_cos μ g

/-- Decomposition: the generating functional's imaginary part is the sine integral. -/
private lemma asymGf_im_eq_sin_integral
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ] (g : AsymTorusTestFunction Lt Ls) :
    (asymTorusGeneratingFunctional Lt Ls μ g).im =
    ∫ ω : Configuration (AsymTorusTestFunction Lt Ls), Real.sin (ω g) ∂μ := by
  simpa [asymTorusGeneratingFunctional] using configuration_expIntegral_im_eq_integral_sin μ g

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
    simpa [evalAsymAtFinSiteGJ_apply] using
      congrArg (fun r => asymGeomSpacing Lt Ls N * r)
        (evalAsymAtFinSite_timeReflection Lt Ls N x f)
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
  set T := latticeCovarianceGJ 2 N a mass ha hmass
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
    · push Not at hx; rw [abs_of_neg hx, show t * (-x) = -(t * x) from by ring]
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

/-- Cutoff-level exponential moment bound for the asymmetric interacting measure.

For each test function f and cutoff N, the interacting measure satisfies:
  `∫ exp(|ω f|) dμ_{P,N} ≤ K * exp(σ²_N(f))`
where K is the universal Nelson constant and `σ²_N(f)` is the lattice second
moment `∫ (ω g)² dμ_{GFF,N}`. This is the N-dependent (lattice-level) bound.

The symmetric version uses `torusEmbeddedTwoPoint` for the same role.
Here we use the lattice second moment directly. The previous version
used `greenFunctionBilinear` (the continuum Green's function) at cutoff
level, which required a false lattice-to-continuum spectral comparison.

The downstream `asymTorusInteracting_exponentialMomentBound` uses
`asymGaussian_second_moment_uniform_bound` to get an N-independent bound. -/
private theorem asymTorusInteractingMeasure_exponentialMomentBound_cutoff
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : AsymTorusTestFunction Lt Ls) (N : ℕ) [NeZero N],
    Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
      Real.exp (|ω f|)) (asymTorusInteractingMeasure Lt Ls N P mass hmass) ∧
    ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
      Real.exp (|ω f|) ∂(asymTorusInteractingMeasure Lt Ls N P mass hmass) ≤
    K * Real.exp (∫ ω : Configuration (FinLatticeField 2 N),
      (ω (asymLatticeTestFn Lt Ls N f)) ^ 2
      ∂(latticeGaussianMeasure 2 N (asymGeomSpacing Lt Ls N) mass
        (asymGeomSpacing_pos Lt Ls N) hmass)) := by
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
  -- The lattice second moment σ²_N(f)
  set σ2 := ∫ ω : Configuration (FinLatticeField 2 N), (ω g) ^ 2 ∂μ_GFF
  change Integrable (fun ω => Real.exp (|ω f|)) (Measure.map ι μ_int) ∧
    ∫ ω, Real.exp (|ω f|) ∂(Measure.map ι μ_int) ≤
    Real.sqrt (2 * K) * Real.exp σ2
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
  -- 2^2/2 * ∫(ωg)² = 2 * σ2
  have h_exp_simp : (2:ℝ) ^ 2 / 2 * ∫ ω, (ω g) ^ 2 ∂μ_GFF = 2 * σ2 := by
    have h22 : (2:ℝ) ^ 2 / 2 = 2 := by norm_num
    rw [h22]
  -- So: ∫ exp(2|ωg|) ≤ 2 * exp(2 * σ2)
  have h_gauss' : ∫ ω, Real.exp (2 * |ω g|) ∂μ_GFF ≤
      2 * Real.exp (2 * σ2) := by
    rw [← h_exp_simp]; exact h_gauss
  -- Step 5: Bound (∫ exp(2|ωg|))^{1/2} ≤ √2 * exp(σ2)
  have h_gauss_nn : (0:ℝ) ≤ ∫ ω, Real.exp (2 * |ω g|) ∂μ_GFF :=
    integral_nonneg fun ω => (Real.exp_pos _).le
  have h_rpow_bound : (∫ ω, (fun ω => Real.exp (|ω g|)) ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) ≤
      Real.sqrt 2 * Real.exp σ2 := by
    rw [h_int_rpow_eq]
    calc (∫ ω, Real.exp (2 * |ω g|) ∂μ_GFF) ^ (1/2:ℝ)
        ≤ (2 * Real.exp (2 * σ2)) ^ (1/2:ℝ) :=
          Real.rpow_le_rpow h_gauss_nn h_gauss' (by norm_num : (0:ℝ) ≤ 1/2)
      _ = Real.sqrt (2 * Real.exp (2 * σ2)) := by
          rw [Real.sqrt_eq_rpow]
      _ = Real.sqrt 2 * Real.sqrt (Real.exp (2 * σ2)) := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      _ = Real.sqrt 2 * Real.exp σ2 := by
          congr 1
          rw [show (2 : ℝ) * σ2 = σ2 + σ2 from by ring,
              Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
  -- Step 6: Combine: ∫ exp(|ωg|) ≤ K^{1/2} * √2 * exp(σ2) = √(2K) * exp(σ2)
  have h_integral_bound : ∫ ω, Real.exp (|ω g|) ∂μ_int ≤
      Real.sqrt (2 * K) * Real.exp σ2 := by
    calc ∫ ω, Real.exp (|ω g|) ∂μ_int
        ≤ K ^ (1/2:ℝ) *
          (∫ ω, (fun ω => Real.exp (|ω g|)) ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) := h_dt
      _ ≤ K ^ (1/2:ℝ) * (Real.sqrt 2 * Real.exp σ2) :=
          mul_le_mul_of_nonneg_left h_rpow_bound (Real.rpow_nonneg hK_pos.le _)
      _ = Real.sqrt K * (Real.sqrt 2 * Real.exp σ2) := by
          rw [← Real.sqrt_eq_rpow]
      _ = (Real.sqrt K * Real.sqrt 2) * Real.exp σ2 := by ring
      _ = Real.sqrt (2 * K) * Real.exp σ2 := by
          congr 1
          rw [mul_comm (Real.sqrt K) (Real.sqrt 2),
              ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  exact ⟨hF_int_int, h_integral_bound⟩

/-- **AsymTorus interacting exponential moment bound on a BC-limit measure.**

NOT in the polynomial-chaos family despite being grouped with Cluster A
historically. This axiom is structurally different from the
`exp(-2 V_a)` bound discharged by `nelson_exponential_estimate_master`
(`Pphi2/NelsonEstimate/PolynomialChaosBridge.lean`):

* The polynomial-chaos master controls `∫ exp(-2 V_a) dμ_GFF` for the
  Gaussian (free) measure, with the interaction in the integrand.
* This axiom controls `∫ exp(|ω f|) dμ` for an interacting limit
  measure `μ`, with the field in the integrand and the interaction
  baked into the measure via pushforward.

The closer relative is `cylinderIR_uniform_exponential_moment`
(`Pphi2/IRLimit/UniformExponentialMoment.lean`, discharged in PR #14
via `MeasureHasGreenMomentBound`). The asym analogue would build on
`asymGf_sub_norm_le_seminorm` (the Cluster B asymmetric Lipschitz
bound, now a theorem) and lift through the BC-convergence hypothesis
`hconv` here, mirroring the cylinder IR-limit pattern. Discharge route
deferred to a follow-up Cluster B'-style refactor. -/
private axiom asymTorusInteracting_exponentialMomentBound
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (_hφ : StrictMono φ)
    (hconv : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
        Tendsto (fun n => ∫ ω, g ω ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, g ω ∂μ)))
    : ∃ (q : AsymTorusTestFunction Lt Ls → ℝ) (_ : Continuous q),
    ∀ (f : AsymTorusTestFunction Lt Ls),
    Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
      Real.exp (|ω f|)) μ ∧
    ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
      Real.exp (|ω f|) ∂μ ≤ Real.exp (q f)
/-! ## OS Proofs

### Helper lemmas for OS0 -/

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
    obtain ⟨C_K, hC_K_nn, hC_K⟩ := compact_im_bound hK
    obtain ⟨q_exp, _, hq_exp_bound⟩ :=
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
        exact (hq_exp_bound ((↑n * C_K) • J i)).1
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
              exp_mul_sum_le (Nat.pos_of_ne_zero hn) C_K hC_K_nn _

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
  -- Get the exponential moment bound with continuous bound function q
  obtain ⟨q, hq_cont, hq_bound⟩ :=
    asymTorusInteracting_exponentialMomentBound Lt Ls P mass hmass μ φ hφ hconv
  -- Use q directly as the OS1 seminorm, with c = 1
  refine ⟨q, hq_cont, 1, one_pos, ?_⟩
  intro f_re f_im
  -- Get the bound for f_im
  obtain ⟨h_int_im, h_exp_bound_im⟩ := hq_bound f_im
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
    _ ≤ Real.exp (q f_im) := h_exp_bound_im
    _ ≤ Real.exp (1 * (q f_re + q f_im)) := by
        rw [one_mul]; apply Real.exp_le_exp_of_le
        -- Need: q f_im ≤ q f_re + q f_im, i.e. 0 ≤ q f_re
        -- Proof: 1 ≤ ∫ exp(|ω f_re|) dμ ≤ exp(q f_re), so 0 ≤ q f_re
        have hq_re_nn : 0 ≤ q f_re := by
          have : (1 : ℝ) ≤ Real.exp (q f_re) :=
            le_trans (by simp :
              (1 : ℝ) = ∫ _ : Configuration (AsymTorusTestFunction Lt Ls), 1 ∂μ).le
              (le_trans (integral_mono (integrable_const 1) (hq_bound f_re).1
                (fun ω => by exact_mod_cast (Real.one_le_exp (abs_nonneg (ω f_re)))))
                (hq_bound f_re).2)
          linarith [Real.one_le_exp_iff.mp this]
        linarith

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

**Total:** ~440 lines of infrastructure, all mechanical adaptations.

Infrastructure axioms below to be proved by adapting symmetric versions. -/

-- **Lemma:** Lattice translation linear map on the asymmetric lattice.
private def asymLatticeTranslateLM (N : ℕ) (j₁ j₂ : ℤ) :=
  asymLatticeSitePermuteLM N (translateSites N j₁ j₂)

-- **Lemma:** Equivariance of evalAsymAtFinSite under lattice translation.
-- `evalAsymAtFinSite x (T_{(j₁a_t, j₂a_s)} f) = evalAsymAtFinSite (x-(j₁,j₂)) f`
-- where `a_t = Lt/N`, `a_s = Ls/N`.
private theorem evalAsymAtFinSite_latticeTranslation (N : ℕ) [NeZero N]
    (j₁ j₂ : ℤ) (x : FinLatticeSites 2 N) (f : AsymTorusTestFunction Lt Ls) :
    evalAsymAtFinSite Lt Ls N x (asymTorusTranslation Lt Ls
      (circleSpacing Lt N * j₁, circleSpacing Ls N * j₂) f) =
    evalAsymAtFinSite Lt Ls N (translateSites N j₁ j₂ x) f := by
  simp only [evalAsymAtFinSite, evalAsymTorusAtSite, asymTorusTranslation,
    translateSites]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [evalCLM_comp_mapCLM (smoothCircle_coeff_basis Lt) (smoothCircle_coeff_basis Ls)]
  -- Need: (proj_{x i} ∘ circRestr_{L_i}) ∘ T_{j_i * a_i} = (proj_{x i - j_i}) ∘ circRestr_{L_i}
  -- Helper: for period P ∈ {Lt, Ls}, (proj_k ∘ circRestr_P) ∘ T_{j*P/N} = proj_{k-j} ∘ circRestr_P
  have transl_key : ∀ (P : ℝ) [Fact (0 < P)] (k : ZMod N) (j : ℤ),
      ((ContinuousLinearMap.proj k).comp (circleRestriction P N)).comp
        (circleTranslation P (circleSpacing P N * j)) =
      (ContinuousLinearMap.proj (k - (j : ZMod N))).comp (circleRestriction P N) := by
    intro P hP k j
    ext g
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      circleRestriction_apply, circlePoint, circleSpacing]
    -- Unfold circleTranslation application
    change Real.sqrt (P / ↑N) * g (↑(ZMod.val k) * P / ↑N - P / ↑N * ↑j) =
      Real.sqrt (P / ↑N) * g (↑(ZMod.val (k - (j : ZMod N))) * P / ↑N)
    congr 1
    have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have hcong : (↑(ZMod.val k) - j : ℤ) ≡ ↑(ZMod.val (k - (j : ZMod N))) [ZMOD (N : ℤ)] := by
      rw [← ZMod.intCast_eq_intCast_iff]
      push_cast
      simp
    obtain ⟨m, hm⟩ := Int.modEq_iff_dvd.mp hcong
    have arith : ↑(ZMod.val k) * P / ↑N - P / ↑N * ↑j =
        ↑(ZMod.val (k - (j : ZMod N))) * P / ↑N + ↑(-m) * P := by
      have hm_real : (↑(ZMod.val (k - (j : ZMod N))) : ℝ) - (↑(ZMod.val k) - ↑j) =
          ↑N * ↑m := by exact_mod_cast hm
      rw [show ↑(ZMod.val k) * P / ↑N - P / ↑N * ↑j =
        (↑(ZMod.val k) - ↑j) * P / ↑N from by ring]
      rw [show (↑(ZMod.val k) - ↑j : ℝ) =
        ↑(ZMod.val (k - (j : ZMod N))) - ↑N * ↑m from by linarith]
      rw [show (↑(ZMod.val (k - (j : ZMod N))) - ↑N * ↑m) * P / ↑N =
        ↑(ZMod.val (k - (j : ZMod N))) * P / ↑N - ↑m * (↑N * P / ↑N) from by ring]
      rw [show (↑N : ℝ) * P / ↑N = P from by
        rw [mul_comm]; exact mul_div_cancel_of_imp (fun h => absurd h hN_ne)]
      push_cast
      linarith
    rw [arith]
    exact (g.periodic.int_mul (-m)) _
  rw [transl_key Lt (x 0) j₁, transl_key Ls (x 1) j₂]

-- **Lemma:** Interacting lattice measure is translation-invariant (generic spacing).
private theorem asymInteractingLatticeMeasure_translation_invariant
    (N : ℕ) [NeZero N] (P : InteractionPolynomial) (mass : ℝ)
    (a : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j₁ j₂ : ℤ) (F : Configuration (FinLatticeField 2 N) → E) :
    ∫ ω, F (ω.comp (asymLatticeTranslateLM N j₁ j₂).toContinuousLinearMap)
      ∂(interactingLatticeMeasure 2 N P a mass ha hmass) =
    ∫ ω, F ω ∂(interactingLatticeMeasure 2 N P a mass ha hmass) := by
  -- Translation x ↦ x - (j₁, j₂) on (ZMod N)² is bijective (group subtraction)
  have hbij : Function.Bijective (translateSites N j₁ j₂) := by
    set σ_inv := fun (x : FinLatticeSites 2 N) =>
      (![x 0 + (j₁ : ZMod N), x 1 + (j₂ : ZMod N)] : FinLatticeSites 2 N)
    have hleft : Function.LeftInverse σ_inv (translateSites N j₁ j₂) := by
      intro x; simp only [translateSites, σ_inv]
      ext i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hright : Function.RightInverse σ_inv (translateSites N j₁ j₂) := by
      intro x; simp only [translateSites, σ_inv]
      ext i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨hleft.injective, hright.surjective⟩
  exact asymInteractingLatticeMeasure_symmetry_invariant N P mass a ha hmass
    (translateSites N j₁ j₂) hbij
    (by -- Density preservation: gaussianDensity(φ∘σ⁻¹) = gaussianDensity(φ)
      intro φ
      set σ_equiv := Equiv.ofBijective (translateSites N j₁ j₂) hbij
      have hsymm_eq : ∀ y : FinLatticeSites 2 N,
          σ_equiv.symm y =
          (![y 0 + (j₁ : ZMod N), y 1 + (j₂ : ZMod N)] : FinLatticeSites 2 N) := by
        intro y
        rw [Equiv.symm_apply_eq]
        change y = translateSites N j₁ j₂ (![y 0 + (j₁ : ZMod N), y 1 + (j₂ : ZMod N)])
        simp only [translateSites]
        ext i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
      set v : FinLatticeSites 2 N := ![(-(j₁ : ZMod N)), (-(j₂ : ZMod N))]
      suffices h_eq : φ ∘ σ_equiv.symm = latticeTranslation 2 N v φ by
        rw [h_eq]
        exact gaussianDensity_translation_invariant 2 N a mass v φ
      funext x
      simp only [Function.comp, hsymm_eq, latticeTranslation]
      congr 1; funext i; fin_cases i <;>
        simp [v, Matrix.cons_val_zero, Matrix.cons_val_one, sub_neg_eq_add])
    F

-- **Theorem 1/4:** Lattice translation invariance of the asymmetric interacting GF.
theorem asymTorusInteractingMeasure_gf_latticeTranslation_invariant
    (N : ℕ) [NeZero N] (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (j₁ j₂ : ℤ) (f : AsymTorusTestFunction Lt Ls) :
    asymTorusGeneratingFunctional Lt Ls
      (asymTorusInteractingMeasure Lt Ls N P mass hmass) f =
    asymTorusGeneratingFunctional Lt Ls
      (asymTorusInteractingMeasure Lt Ls N P mass hmass)
      (asymTorusTranslation Lt Ls
        (circleSpacing Lt N * j₁, circleSpacing Ls N * j₂) f) := by
  -- Step 1: Show eval equivariance under lattice translation
  have h_lattice_trans : ∀ x : FinLatticeSites 2 N,
      asymLatticeTestFn Lt Ls N (asymTorusTranslation Lt Ls
        (circleSpacing Lt N * j₁, circleSpacing Ls N * j₂) f) x =
      asymLatticeTestFn Lt Ls N f (translateSites N j₁ j₂ x) := by
    intro x
    simp only [asymLatticeTestFn]
    simpa [evalAsymAtFinSiteGJ_apply] using
      congrArg (fun r => asymGeomSpacing Lt Ls N * r)
        (evalAsymAtFinSite_latticeTranslation Lt Ls N j₁ j₂ x f)
  set μ_lat := interactingLatticeMeasure 2 N P (asymGeomSpacing Lt Ls N) mass
    (asymGeomSpacing_pos Lt Ls N) hmass
  unfold asymTorusGeneratingFunctional asymTorusInteractingMeasure
  have hmeas : AEMeasurable (asymTorusEmbedLift Lt Ls N) μ_lat :=
    (asymTorusEmbedLift_measurable Lt Ls N).aemeasurable
  have hasm₁ : AEStronglyMeasurable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
      Complex.exp (Complex.I * ↑(ω f))) (Measure.map (asymTorusEmbedLift Lt Ls N) μ_lat) :=
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (configuration_eval_measurable f)))).aestronglyMeasurable
  have hasm₂ : AEStronglyMeasurable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
      Complex.exp (Complex.I * ↑(ω (asymTorusTranslation Lt Ls
        (circleSpacing Lt N * j₁, circleSpacing Ls N * j₂) f))))
      (Measure.map (asymTorusEmbedLift Lt Ls N) μ_lat) :=
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (configuration_eval_measurable _)))).aestronglyMeasurable
  rw [MeasureTheory.integral_map hmeas hasm₁, MeasureTheory.integral_map hmeas hasm₂]
  simp_rw [asymTorusEmbedLift_eval_eq]
  have h_trans_lattice : ∀ φ : Configuration (FinLatticeField 2 N),
      φ (asymLatticeTestFn Lt Ls N (asymTorusTranslation Lt Ls
        (circleSpacing Lt N * j₁, circleSpacing Ls N * j₂) f)) =
      (φ.comp (asymLatticeTranslateLM N j₁ j₂).toContinuousLinearMap)
        (asymLatticeTestFn Lt Ls N f) := by
    intro φ
    change φ (asymLatticeTestFn Lt Ls N (asymTorusTranslation Lt Ls _ f)) =
      φ ((asymLatticeTranslateLM N j₁ j₂) (asymLatticeTestFn Lt Ls N f))
    congr 1; ext x; exact h_lattice_trans x
  simp_rw [h_trans_lattice]
  exact (asymInteractingLatticeMeasure_translation_invariant N P mass
    (asymGeomSpacing Lt Ls N) (asymGeomSpacing_pos Lt Ls N) hmass j₁ j₂ _).symm


-- **Theorem 2/4:** Uniform GF Lipschitz bound for asymmetric interacting measures.
-- ‖Z_N[g] - Z_N[h]‖ ≤ B * p(g - h) with continuous p, p(0)=0.
-- Proof: Cauchy-Schwarz + Lipschitz of exp + density transfer + hypercontractivity.
-- Symmetric version at TorusInteractingOS.lean:1328.
/-- Seminorm-form Gaussian second-moment bound for the GJ-aligned asymmetric embedding. -/
private theorem asymGaussian_second_moment_le_seminorm
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ (p : AsymTorusTestFunction Lt Ls → ℝ), Continuous p ∧ p 0 = 0 ∧
    ∀ (f : AsymTorusTestFunction Lt Ls) (N : ℕ) [NeZero N],
      ∫ ω : Configuration (FinLatticeField 2 N),
        (ω (asymLatticeTestFn Lt Ls N f)) ^ 2
        ∂(latticeGaussianMeasure 2 N (asymGeomSpacing Lt Ls N) mass
          (asymGeomSpacing_pos Lt Ls N) hmass) ≤
      p f ^ 2 := by
  obtain ⟨C₀t, hC₀t_pos, hC₀t_bound⟩ :=
    SmoothMap_Circle.sobolevSeminorm_fourierBasis_le (L := Lt) 0
  have hC₀t : ∀ n, SmoothMap_Circle.sobolevSeminorm (L := Lt) 0
      (SmoothMap_Circle.fourierBasis n) ≤ C₀t := fun n => by
    specialize hC₀t_bound n
    simpa only [pow_zero, mul_one] using hC₀t_bound
  obtain ⟨C₀s, hC₀s_pos, hC₀s_bound⟩ :=
    SmoothMap_Circle.sobolevSeminorm_fourierBasis_le (L := Ls) 0
  have hC₀s : ∀ n, SmoothMap_Circle.sobolevSeminorm (L := Ls) 0
      (SmoothMap_Circle.fourierBasis n) ≤ C₀s := fun n => by
    specialize hC₀s_bound n
    simpa only [pow_zero, mul_one] using hC₀s_bound
  set A : ℝ := mass⁻¹ * Real.sqrt (Lt * Ls) * C₀t * C₀s
  refine ⟨fun f => A * RapidDecaySeq.rapidDecaySeminorm 0 f,
    ?_, ?_, ?_⟩
  · exact continuous_const.mul (RapidDecaySeq.rapidDecay_withSeminorms.continuous_seminorm 0)
  · show A * RapidDecaySeq.rapidDecaySeminorm 0 0 = 0
    rw [map_zero (RapidDecaySeq.rapidDecaySeminorm 0)]
    ring
  · intro f N _
    set p₀f := RapidDecaySeq.rapidDecaySeminorm 0 f
    set g : FinLatticeField 2 N := asymLatticeTestFn Lt Ls N f
    set a : ℝ := asymGeomSpacing Lt Ls N
    have ha_pos : 0 < a := by simpa [a] using asymGeomSpacing_pos Lt Ls N
    have ha2_ne : (a ^ 2 : ℝ) ≠ 0 := by positivity
    rw [show ∫ ω : Configuration (FinLatticeField 2 N), (ω g) ^ 2
          ∂(latticeGaussianMeasure 2 N a mass ha_pos hmass) =
        @inner ℝ ell2' _
          (latticeCovarianceGJ 2 N a mass ha_pos hmass g)
          (latticeCovarianceGJ 2 N a mass ha_pos hmass g) by
          exact second_moment_eq_covariance _ g]
    have h_GJ_bare : @inner ℝ ell2' _
          (latticeCovarianceGJ 2 N a mass ha_pos hmass g)
          (latticeCovarianceGJ 2 N a mass ha_pos hmass g) =
        (a ^ 2)⁻¹ *
          @inner ℝ ell2' _
            (latticeCovariance 2 N a mass ha_pos hmass g)
            (latticeCovariance 2 N a mass ha_pos hmass g) := by
      simpa [GaussianField.covariance] using
        latticeCovariance_GJ_eq_inv_smul_bare (d := 2) (N := N) a mass ha_pos hmass g g
    rw [h_GJ_bare]
    have h_bare : @inner ℝ ell2' _
          (latticeCovariance 2 N a mass ha_pos hmass g)
          (latticeCovariance 2 N a mass ha_pos hmass g) ≤
        mass⁻¹ ^ 2 * ∑ x : FinLatticeSites 2 N, g x ^ 2 :=
      covariance_inner_le_mass_inv_sq_norm_sq N a mass ha_pos hmass g
    have h_norm_tight : ∑ x : FinLatticeSites 2 N, g x ^ 2 ≤
        a ^ 2 * Lt * Ls * C₀t ^ 2 * C₀s ^ 2 * p₀f ^ 2 := by
      simpa [g, a, p₀f] using
        asymLatticeTestFn_norm_sq_le_tight Lt Ls
          C₀t hC₀t_pos hC₀t C₀s hC₀s_pos hC₀s f N
    have hA_sq : A ^ 2 = mass⁻¹ ^ 2 * Lt * Ls * C₀t ^ 2 * C₀s ^ 2 := by
      have hLtLs_nonneg : 0 ≤ Lt * Ls := mul_nonneg hLt.out.le hLs.out.le
      unfold A
      rw [show (mass⁻¹ * Real.sqrt (Lt * Ls) * C₀t * C₀s) ^ 2 =
          mass⁻¹ ^ 2 * (Real.sqrt (Lt * Ls)) ^ 2 * C₀t ^ 2 * C₀s ^ 2 from by ring]
      rw [Real.sq_sqrt hLtLs_nonneg]
      ring
    calc (a ^ 2)⁻¹ * @inner ℝ ell2' _
          (latticeCovariance 2 N a mass ha_pos hmass g)
          (latticeCovariance 2 N a mass ha_pos hmass g)
        ≤ (a ^ 2)⁻¹ * (mass⁻¹ ^ 2 * ∑ x : FinLatticeSites 2 N, g x ^ 2) :=
          mul_le_mul_of_nonneg_left h_bare (by positivity)
      _ ≤ (a ^ 2)⁻¹ * (mass⁻¹ ^ 2 * (a ^ 2 * Lt * Ls * C₀t ^ 2 * C₀s ^ 2 * p₀f ^ 2)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h_norm_tight (by positivity)) (by positivity)
      _ = mass⁻¹ ^ 2 * Lt * Ls * C₀t ^ 2 * C₀s ^ 2 * p₀f ^ 2 := by
          field_simp [ha2_ne]
      _ = (A * p₀f) ^ 2 := by
          rw [show (A * p₀f) ^ 2 = A ^ 2 * p₀f ^ 2 from by ring, hA_sq]
      _ = (A * RapidDecaySeq.rapidDecaySeminorm 0 f) ^ 2 := by simp [p₀f]

/-- **AsymTorus generating-functional seminorm bound**. -/
theorem asymGf_sub_norm_le_seminorm
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (B : ℝ) (p : AsymTorusTestFunction Lt Ls → ℝ),
    Continuous p ∧ p 0 = 0 ∧
    ∀ (N : ℕ) [NeZero N] (g h : AsymTorusTestFunction Lt Ls),
    ‖asymTorusGeneratingFunctional Lt Ls
        (asymTorusInteractingMeasure Lt Ls N P mass hmass) g -
     asymTorusGeneratingFunctional Lt Ls
        (asymTorusInteractingMeasure Lt Ls N P mass hmass) h‖ ≤
    B * p (g - h) := by
  obtain ⟨C, hC_pos, hC_bound⟩ :=
    asymTorus_interacting_second_moment_density_transfer Lt Ls P mass hmass
  obtain ⟨p0, hp0_cont, hp0_zero, hp0_bound⟩ :=
    asymGaussian_second_moment_le_seminorm Lt Ls mass hmass
  refine ⟨2 * Real.sqrt C, fun f => |p0 f|, hp0_cont.abs, by simp [hp0_zero], fun N _ g h => ?_⟩
  · set μ := asymTorusInteractingMeasure Lt Ls N P mass hmass
    have h_seminorm : ∫ ω : Configuration (FinLatticeField 2 N),
        (ω (asymLatticeTestFn Lt Ls N (g - h))) ^ 2
        ∂(latticeGaussianMeasure 2 N (asymGeomSpacing Lt Ls N) mass
          (asymGeomSpacing_pos Lt Ls N) hmass) ≤
        p0 (g - h) ^ 2 := hp0_bound (g - h) N
    have h_combined : ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
        (ω (g - h)) ^ 2 ∂μ ≤ C * |p0 (g - h)| ^ 2 := by
      have h_seminorm' : ∫ ω : Configuration (FinLatticeField 2 N),
          (ω (asymLatticeTestFn Lt Ls N (g - h))) ^ 2
          ∂(latticeGaussianMeasure 2 N (asymGeomSpacing Lt Ls N) mass
            (asymGeomSpacing_pos Lt Ls N) hmass) ≤
          |p0 (g - h)| ^ 2 := by
        simpa [sq_abs] using h_seminorm
      exact (hC_bound (g - h) N).trans (mul_le_mul_of_nonneg_left h_seminorm' hC_pos.le)
    set F : Configuration (AsymTorusTestFunction Lt Ls) → ℂ := fun ω =>
      Complex.exp (Complex.I * ↑(ω g)) - Complex.exp (Complex.I * ↑(ω h))
    have h_int : ∀ f : AsymTorusTestFunction Lt Ls,
        Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
          Complex.exp (Complex.I * ↑(ω f))) μ := fun f =>
      (integrable_const (1 : ℂ)).mono
        (Complex.continuous_exp.measurable.comp
          (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
            (configuration_eval_measurable f)))).aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [norm_one, mul_comm Complex.I]
          exact le_of_eq (Complex.norm_exp_ofReal_mul_I _))
    have h_gf_eq : asymTorusGeneratingFunctional Lt Ls μ g -
        asymTorusGeneratingFunctional Lt Ls μ h = ∫ ω, F ω ∂μ := by
      simp only [asymTorusGeneratingFunctional, F]
      exact (integral_sub (h_int g) (h_int h)).symm
    have hF_bd2 : ∀ ω, ‖F ω‖ ≤ 2 := fun ω => by
      exact (norm_sub_le _ _).trans (by
        rw [mul_comm Complex.I (↑(ω g) : ℂ), Complex.norm_exp_ofReal_mul_I,
            mul_comm Complex.I (↑(ω h) : ℂ), Complex.norm_exp_ofReal_mul_I]
        norm_num)
    have hF_lip : ∀ ω, ‖F ω‖ ≤ |ω (g - h)| := fun ω => by
      have : F ω = Complex.exp (Complex.I * ↑(ω h)) *
          (Complex.exp (Complex.I * ↑(ω g - ω h)) - 1) := by
        simp only [F]
        rw [mul_sub, mul_one, ← Complex.exp_add]
        congr 1
        push_cast
        ring_nf
      rw [this, norm_mul, mul_comm Complex.I (↑(ω h) : ℂ),
        Complex.norm_exp_ofReal_mul_I, one_mul]
      have h_key : ‖Complex.exp (Complex.I * ↑(ω g - ω h)) - 1‖ ≤
          |ω g - ω h| := by
        rw [Complex.norm_exp_I_mul_ofReal_sub_one]
        calc ‖2 * Real.sin ((ω g - ω h) / 2)‖
            = 2 * |Real.sin ((ω g - ω h) / 2)| := by
              rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          _ ≤ 2 * |(ω g - ω h) / 2| :=
              mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
          _ = |ω g - ω h| := by
              rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
              ring
      exact h_key.trans (by rw [map_sub])
    have hF_sq : ∀ ω, ‖F ω‖ ^ 2 ≤ (ω (g - h)) ^ 2 := fun ω =>
      (sq_le_sq' (by linarith [norm_nonneg (F ω), abs_nonneg (ω (g - h))])
        (hF_lip ω)).trans (le_of_eq (sq_abs _))
    have hF_meas : Measurable F :=
      (Complex.continuous_exp.measurable.comp
        (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
          (configuration_eval_measurable g)))).sub
      (Complex.continuous_exp.measurable.comp
        (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
          (configuration_eval_measurable h))))
    have hF_norm_int : Integrable (fun ω => ‖F ω‖) μ :=
      (integrable_const (2 : ℝ)).mono hF_meas.norm.aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          exact hF_bd2 ω)
    have hF_sq_int : Integrable (fun ω => ‖F ω‖ ^ 2) μ :=
      (integrable_const (4 : ℝ)).mono (hF_meas.norm.pow_const 2).aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ‖F ω‖ ^ 2),
              Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
          exact (sq_le_sq' (by linarith [norm_nonneg (F ω)]) (hF_bd2 ω)).trans (by norm_num))
    have hX_sq_int : Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
        (ω (g - h)) ^ 2) μ := by
      change Integrable (fun ω => (ω (g - h)) ^ 2)
        (asymTorusInteractingMeasure Lt Ls N P mass hmass)
      unfold asymTorusInteractingMeasure
      rw [integrable_map_measure
        ((configuration_eval_measurable (g - h)).pow_const 2).aestronglyMeasurable
        (asymTorusEmbedLift_measurable Lt Ls N).aemeasurable]
      have h_eq : (fun ω => (ω (g - h)) ^ 2) ∘ (asymTorusEmbedLift Lt Ls N) =
          fun ω => (ω (asymLatticeTestFn Lt Ls N (g - h))) ^ 2 := by
        ext ω
        simp [Function.comp, asymTorusEmbedLift_eval_eq Lt Ls N (g - h) ω]
      rw [h_eq]
      set g' := asymLatticeTestFn Lt Ls N (g - h)
      set μ_GFF := latticeGaussianMeasure 2 N (asymGeomSpacing Lt Ls N) mass
        (asymGeomSpacing_pos Lt Ls N) hmass
      set bw := boltzmannWeight 2 N P (asymGeomSpacing Lt Ls N) mass
      obtain ⟨B0, hB0⟩ := interactionFunctional_bounded_below 2 N P
        (asymGeomSpacing Lt Ls N) mass (asymGeomSpacing_pos Lt Ls N) hmass
      have hZ := partitionFunction_pos 2 N P (asymGeomSpacing Lt Ls N) mass
        (asymGeomSpacing_pos Lt Ls N) hmass
      suffices h : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
          (ω g') ^ 2)
          (μ_GFF.withDensity (fun ω => ENNReal.ofReal (bw ω))) by
        unfold interactingLatticeMeasure
        exact h.smul_measure (ENNReal.inv_ne_top.mpr ((ENNReal.ofReal_pos.mpr hZ).ne'))
      have hf_meas : Measurable (fun ω : Configuration (FinLatticeField 2 N) =>
          ENNReal.ofReal (bw ω)) :=
        ENNReal.measurable_ofReal.comp
          ((interactionFunctional_measurable 2 N P (asymGeomSpacing Lt Ls N) mass).neg.exp)
      apply (integrable_withDensity_iff hf_meas
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
      have hbw_simp : ∀ ω : Configuration (FinLatticeField 2 N),
          (ENNReal.ofReal (bw ω)).toReal = bw ω :=
        fun ω => ENNReal.toReal_ofReal
          (le_of_lt (boltzmannWeight_pos 2 N P (asymGeomSpacing Lt Ls N) mass ω))
      simp_rw [hbw_simp]
      have h_sq_int : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
          (ω g') ^ 2) μ_GFF :=
        (pairing_memLp (latticeCovarianceGJ 2 N (asymGeomSpacing Lt Ls N) mass
          (asymGeomSpacing_pos Lt Ls N) hmass) g' 2).integrable_sq
      apply (h_sq_int.mul_const (Real.exp B0)).mono
      · exact ((configuration_eval_measurable g').pow_const 2).aestronglyMeasurable.mul
          (Measurable.aestronglyMeasurable
            (interactionFunctional_measurable 2 N P (asymGeomSpacing Lt Ls N) mass).neg.exp)
      · exact Filter.Eventually.of_forall fun ω => by
          simp only [Real.norm_eq_abs]
          have h1 : 0 ≤ (ω g') ^ 2 := sq_nonneg _
          have h2 : 0 < bw ω :=
            boltzmannWeight_pos 2 N P (asymGeomSpacing Lt Ls N) mass ω
          have h3 : bw ω ≤ Real.exp B0 := by
            change Real.exp (-interactionFunctional 2 N P (asymGeomSpacing Lt Ls N) mass ω)
              ≤ Real.exp B0
            exact Real.exp_le_exp_of_le (by linarith [hB0 ω])
          rw [abs_of_nonneg (mul_nonneg h1 (le_of_lt h2)),
              abs_of_nonneg (mul_nonneg h1 (le_of_lt (Real.exp_pos B0)))]
          exact mul_le_mul_of_nonneg_left h3 h1
    have h_sq_bound : ‖asymTorusGeneratingFunctional Lt Ls μ g -
        asymTorusGeneratingFunctional Lt Ls μ h‖ ^ 2 ≤ C * |p0 (g - h)| ^ 2 := by
      calc ‖asymTorusGeneratingFunctional Lt Ls μ g -
              asymTorusGeneratingFunctional Lt Ls μ h‖ ^ 2
          = ‖∫ ω, F ω ∂μ‖ ^ 2 := by rw [h_gf_eq]
        _ ≤ (∫ ω, ‖F ω‖ ∂μ) ^ 2 :=
            sq_le_sq' (by
              have h1 := norm_nonneg (∫ ω, F ω ∂μ)
              have h2 : (0 : ℝ) ≤ ∫ ω, ‖F ω‖ ∂μ :=
                integral_nonneg fun ω => norm_nonneg (F ω)
              linarith)
              (norm_integral_le_integral_norm _)
        _ ≤ ∫ ω, ‖F ω‖ ^ 2 ∂μ :=
            ConvexOn.map_integral_le (Even.convexOn_pow (n := 2) even_two)
              (continuousOn_pow 2) isClosed_univ
              (ae_of_all _ fun _ => Set.mem_univ _) hF_norm_int hF_sq_int
        _ ≤ ∫ ω, (ω (g - h)) ^ 2 ∂μ :=
            integral_mono hF_sq_int hX_sq_int (fun ω => hF_sq ω)
        _ ≤ C * |p0 (g - h)| ^ 2 := h_combined
    calc ‖asymTorusGeneratingFunctional Lt Ls μ g -
            asymTorusGeneratingFunctional Lt Ls μ h‖
        ≤ Real.sqrt (C * |p0 (g - h)| ^ 2) := by
          rw [← Real.sqrt_sq (norm_nonneg _)]
          exact Real.sqrt_le_sqrt h_sq_bound
      _ = Real.sqrt C * |p0 (g - h)| := by
          rw [Real.sqrt_mul hC_pos.le, Real.sqrt_sq_eq_abs, abs_abs]
      _ ≤ 2 * Real.sqrt C * |p0 (g - h)| := by
          have h1 : 0 ≤ Real.sqrt C * |p0 (g - h)| :=
            mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
          linarith
-- **Helper:** Continuity of s ↦ T_s g for a single circle factor.
-- (The symmetric version is private in TorusInteractingOS.lean.)
private theorem circleTranslation_continuous_in_s
    {L : ℝ} [Fact (0 < L)]
    (g : GaussianField.SmoothMap_Circle L ℝ) :
    Continuous (fun s : ℝ => GaussianField.circleTranslation L s g) := by
  rw [continuous_iff_continuousAt]
  intro s₀
  rw [ContinuousAt,
      GaussianField.SmoothMap_Circle.smoothCircle_withSeminorms.tendsto_nhds
        (fun s => GaussianField.circleTranslation L s g)
        (GaussianField.circleTranslation L s₀ g)]
  intro k ε hε
  set h : ℝ → ℝ := iteratedDeriv k (⇑g) with hh_def
  have hh_cont : Continuous h := g.continuous_iteratedDeriv k
  have hh_per : Function.Periodic h L := g.periodic_iteratedDeriv k
  have hh_uc : UniformContinuous h := by
    rw [Metric.uniformContinuous_iff]
    intro ε' hε'
    have huc_cpt : UniformContinuousOn h (Set.Icc (-L) (2 * L)) :=
      isCompact_Icc.uniformContinuousOn_of_continuous hh_cont.continuousOn
    rw [Metric.uniformContinuousOn_iff] at huc_cpt
    obtain ⟨δ₀, hδ₀_pos, huc_cpt⟩ := huc_cpt ε' hε'
    have hL_pos := (inferInstance : Fact (0 < L)).out
    refine ⟨min δ₀ (L / 2), lt_min hδ₀_pos (by linarith), fun {x y} hxy => ?_⟩
    set x' := toIcoMod hL_pos 0 x
    set n := toIcoDiv hL_pos (0 : ℝ) x
    have hx_eq : x = x' + n • L :=
      (toIcoMod_add_toIcoDiv_zsmul hL_pos 0 x).symm
    have hx'_mem : x' ∈ Set.Ico (0 : ℝ) L := by
      have := toIcoMod_mem_Ico hL_pos 0 x; simp at this; exact this
    set y' := x' + (y - x)
    have hx_val : h x = h x' := by
      have : x = x' + n • L := hx_eq
      rw [this]; exact hh_per.zsmul n x'
    have hy_val : h y = h y' := by
      change h y = h (x' + (y - x))
      have heq : x' + (y - x) = y - n • L := by rw [hx_eq]; ring
      rw [heq]
      exact (hh_per.sub_zsmul_eq n).symm
    have hx'_Icc : x' ∈ Set.Icc (-L) (2 * L) := by
      exact ⟨by linarith [hx'_mem.1, hL_pos], by linarith [hx'_mem.2, hL_pos]⟩
    have hy'x' : dist y' x' < L / 2 := by
      have : dist y' x' = dist y x := by
        simp only [y', dist_eq_norm]; congr 1; ring
      rw [this, dist_comm]
      exact lt_of_lt_of_le hxy (min_le_right _ _)
    have hy'_Icc : y' ∈ Set.Icc (-L) (2 * L) := by
      rw [Real.dist_eq] at hy'x'
      constructor
      · linarith [hx'_mem.1, abs_le.mp (le_of_lt hy'x')]
      · linarith [hx'_mem.2, abs_le.mp (le_of_lt hy'x')]
    have hdist : dist x' y' < δ₀ := by
      have : dist x' y' = dist x y := by
        simp only [y', dist_eq_norm]
        congr 1
        ring
      rw [this]
      exact lt_of_lt_of_le hxy (min_le_left _ _)
    rw [hx_val, hy_val]
    exact huc_cpt x' hx'_Icc y' hy'_Icc hdist
  rw [Metric.uniformContinuous_iff] at hh_uc
  obtain ⟨δ, hδ_pos, hδ⟩ := hh_uc ε hε
  rw [Filter.Eventually, Metric.mem_nhds_iff]
  exact ⟨δ, hδ_pos, fun s hs => by
    have h_pw : ∀ x, ‖iteratedDeriv k
          (↑(GaussianField.circleTranslation L s g -
            GaussianField.circleTranslation L s₀ g)) x‖ < ε := by
      intro x
      have h_coe : ∀ y, (↑(GaussianField.circleTranslation L s g -
              GaussianField.circleTranslation L s₀ g) : ℝ → ℝ) y =
            g (y - s) - g (y - s₀) := by
        intro y; rfl
      have h_deriv : iteratedDeriv k
          (↑(GaussianField.circleTranslation L s g -
            GaussianField.circleTranslation L s₀ g)) x =
          h (x - s) - h (x - s₀) := by
        have hTs_cd : ContDiffAt ℝ k (fun y => g (y - s)) x :=
          (g.smooth.comp (contDiff_id.sub contDiff_const)).contDiffAt.of_le
            (by exact_mod_cast le_top)
        have hTs₀_cd : ContDiffAt ℝ k (fun y => g (y - s₀)) x :=
          (g.smooth.comp (contDiff_id.sub contDiff_const)).contDiffAt.of_le
            (by exact_mod_cast le_top)
        have h_coe_eq : (↑(GaussianField.circleTranslation L s g -
            GaussianField.circleTranslation L s₀ g) : ℝ → ℝ) =
            fun y => g (y - s) - g (y - s₀) := by ext y; rfl
        rw [h_coe_eq, iteratedDeriv_fun_sub hTs_cd hTs₀_cd]
        congr 1 <;> exact congr_fun (iteratedDeriv_comp_sub_const k (⇑g) _) x
      rw [h_deriv, ← dist_eq_norm]
      apply hδ
      rw [Real.dist_eq, show x - s - (x - s₀) = s₀ - s from by ring, abs_sub_comm,
          ← Real.dist_eq]
      exact Metric.mem_ball.mp hs
    change GaussianField.SmoothMap_Circle.sobolevSeminorm k
      (GaussianField.circleTranslation L s g - GaussianField.circleTranslation L s₀ g) < ε
    set d := GaussianField.circleTranslation L s g - GaussianField.circleTranslation L s₀ g
    set S := (fun x => ‖iteratedDeriv k (↑d) x‖) '' Set.Icc 0 L
    have h_ne : S.Nonempty := Set.Nonempty.image _
      GaussianField.SmoothMap_Circle.Icc_nonempty
    have h_bdd_above := d.bddAbove_norm_iteratedDeriv_image k
    obtain ⟨x₀, hx₀_mem, hx₀_max⟩ := IsCompact.exists_isMaxOn
      (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) L))
      GaussianField.SmoothMap_Circle.Icc_nonempty
      (ContinuousOn.norm (d.continuous_iteratedDeriv k).continuousOn)
    have h_max_lt : ‖iteratedDeriv k (↑d) x₀‖ < ε := h_pw x₀
    calc GaussianField.SmoothMap_Circle.sobolevSeminorm k d
        = sSup S := rfl
      _ ≤ ‖iteratedDeriv k (↑d) x₀‖ := by
          apply csSup_le h_ne
          rintro _ ⟨x, hx, rfl⟩
          exact hx₀_max hx
      _ < ε := h_max_lt⟩

-- **Theorem 3/4:** Continuity of v ↦ T_v f in the NTP topology.
-- Proof: Dynin-Mityagin expansion + Sobolev isometry + 3-epsilon argument.
-- Adapted from the symmetric version at TorusInteractingOS.lean:871.
set_option maxHeartbeats 12800000 in
theorem asymTorusTranslation_continuous_in_v
    (f : AsymTorusTestFunction Lt Ls) :
    Continuous (fun v : ℝ × ℝ => asymTorusTranslation Lt Ls v f) := by
  -- Abbreviations: E_t for the time circle, E_s for the space circle
  set E_t := GaussianField.SmoothMap_Circle Lt ℝ
  set E_s := GaussianField.SmoothMap_Circle Ls ℝ
  -- The topology on AsymTorusTestFunction is WithSeminorms rapidDecaySeminorm
  have h_ws : WithSeminorms (RapidDecaySeq.rapidDecaySeminorm :
      ℕ → Seminorm ℝ (AsymTorusTestFunction Lt Ls)) := RapidDecaySeq.rapidDecay_withSeminorms
  -- Step 1: Reduce to ContinuousAt at each v₀
  rw [continuous_iff_continuousAt]
  intro v₀
  -- Step 2: Use WithSeminorms characterization of convergence
  suffices ∀ (i : ℕ) (ε : ℝ), 0 < ε → ∀ᶠ v in nhds v₀,
      RapidDecaySeq.rapidDecaySeminorm i
        (GaussianField.asymTorusTranslation Lt Ls v f -
         GaussianField.asymTorusTranslation Lt Ls v₀ f) < ε by
    rw [ContinuousAt]
    exact (h_ws.tendsto_nhds _ _).mpr this
  intro k ε hε
  -- Step 3: Get uniform-in-v bound on mapImage seminorms
  obtain ⟨C_pure, s₁, s₂, hpure⟩ :=
    GaussianField.NuclearTensorProduct.pure_seminorm_bound (E₁ := E_t) (E₂ := E_s) k
  set ψ_t := DyninMityaginSpace.basis (E := E_t)
  set ψ_s := DyninMityaginSpace.basis (E := E_s)
  -- Sobolev isometry for translations: (s.sup p)(T_s g) ≤ (s.sup p)(g)
  have h_trans_iso₁ : ∀ (s : ℝ) (g : E_t),
      (s₁.sup DyninMityaginSpace.p) (GaussianField.circleTranslation Lt s g) ≤
      (s₁.sup DyninMityaginSpace.p) g := by
    intro s g
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro i hi
    calc DyninMityaginSpace.p i (GaussianField.circleTranslation Lt s g)
        ≤ DyninMityaginSpace.p i g :=
          GaussianField.sobolevSeminorm_affine_precomp_le 1 (-s) (by norm_num) i
            g (GaussianField.circleTranslation Lt s g)
            (fun x => by show g (x - s) = g (1 * x + -s); ring_nf)
      _ ≤ s₁.sup DyninMityaginSpace.p g :=
          Seminorm.le_finset_sup_apply hi
  have h_trans_iso₂ : ∀ (s : ℝ) (g : E_s),
      (s₂.sup DyninMityaginSpace.p) (GaussianField.circleTranslation Ls s g) ≤
      (s₂.sup DyninMityaginSpace.p) g := by
    intro s g
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro i hi
    calc DyninMityaginSpace.p i (GaussianField.circleTranslation Ls s g)
        ≤ DyninMityaginSpace.p i g :=
          GaussianField.sobolevSeminorm_affine_precomp_le 1 (-s) (by norm_num) i
            g (GaussianField.circleTranslation Ls s g)
            (fun x => by show g (x - s) = g (1 * x + -s); ring_nf)
      _ ≤ s₂.sup DyninMityaginSpace.p g :=
          Seminorm.le_finset_sup_apply hi
  -- Get polynomial growth of basis elements
  classical
  obtain ⟨D₁, hD₁, S₁, hbnd₁⟩ := GaussianField.finset_sup_poly_bound
    DyninMityaginSpace.p s₁ (DyninMityaginSpace.basis (E := E_t))
    (fun i _ => DyninMityaginSpace.basis_growth i)
  obtain ⟨D₂, hD₂, S₂, hbnd₂⟩ := GaussianField.finset_sup_poly_bound
    DyninMityaginSpace.p s₂ (DyninMityaginSpace.basis (E := E_s))
    (fun i _ => DyninMityaginSpace.basis_growth i)
  -- Uniform bound: seminorm_k(mapImage(T_v)(m)) ≤ K * (1+m)^S for ALL v
  set K := (↑C_pure + 1) * D₁ * D₂ with hK_def
  set S := S₁ + S₂ with hS_def
  have hK_pos : 0 < K := by positivity
  have h_uniform_bound : ∀ (v : ℝ × ℝ) (m : ℕ),
      RapidDecaySeq.rapidDecaySeminorm k (GaussianField.mapImage
        (GaussianField.circleTranslation Lt v.1)
        (GaussianField.circleTranslation Ls v.2) m) ≤
      K * (1 + (m : ℝ)) ^ S := by
    intro v m
    set a := (Nat.unpair m).1
    set b := (Nat.unpair m).2
    show RapidDecaySeq.rapidDecaySeminorm k
      (GaussianField.NuclearTensorProduct.pure
        (GaussianField.circleTranslation Lt v.1 (ψ_t a))
        (GaussianField.circleTranslation Ls v.2 (ψ_s b))) ≤ _
    have ha_le : (1 + (a : ℝ)) ≤ (1 + (m : ℝ)) :=
      add_le_add_right (Nat.cast_le.mpr (Nat.unpair_left_le m)) 1
    have hb_le : (1 + (b : ℝ)) ≤ (1 + (m : ℝ)) :=
      add_le_add_right (Nat.cast_le.mpr (Nat.unpair_right_le m)) 1
    calc RapidDecaySeq.rapidDecaySeminorm k
          (GaussianField.NuclearTensorProduct.pure
            (GaussianField.circleTranslation Lt v.1 (ψ_t a))
            (GaussianField.circleTranslation Ls v.2 (ψ_s b)))
        ≤ ↑C_pure * (s₁.sup DyninMityaginSpace.p)
              (GaussianField.circleTranslation Lt v.1 (ψ_t a)) *
            (s₂.sup DyninMityaginSpace.p)
              (GaussianField.circleTranslation Ls v.2 (ψ_s b)) :=
          hpure _ _
      _ ≤ ↑C_pure * (s₁.sup DyninMityaginSpace.p) (ψ_t a) *
            (s₂.sup DyninMityaginSpace.p) (ψ_s b) := by
          gcongr
          · exact h_trans_iso₁ _ _
          · exact h_trans_iso₂ _ _
      _ ≤ ↑C_pure * (D₁ * (1 + (a : ℝ)) ^ S₁) * (D₂ * (1 + (b : ℝ)) ^ S₂) := by
          gcongr
          · exact hbnd₁ a
          · exact hbnd₂ b
      _ ≤ ↑C_pure * (D₁ * (1 + (m : ℝ)) ^ S₁) * (D₂ * (1 + (m : ℝ)) ^ S₂) := by
          gcongr
      _ = ↑C_pure * D₁ * D₂ * (1 + (m : ℝ)) ^ (S₁ + S₂) := by
          rw [pow_add]; ring
      _ ≤ ((↑C_pure + 1) * D₁ * D₂) * (1 + (m : ℝ)) ^ (S₁ + S₂) := by
          gcongr; linarith [NNReal.coe_nonneg C_pure]
  -- Step 4: The 3-epsilon argument
  set g : ℕ → ℝ := fun m => |f.val m| * (2 * K) * (1 + (m : ℝ)) ^ S
  have hg_summable : Summable g := by
    have := f.rapid_decay S
    exact (this.mul_left (2 * K)).congr (fun m => by simp [g]; ring)
  -- Choose N so that Σ_{m≥N} g(m) < ε/2
  have h_tail_small : ∃ N : ℕ, ∑' m, g (m + N) < ε / 2 := by
    have h_tendsto : Filter.Tendsto (fun N => ∑' m, g (m + N)) Filter.atTop (nhds 0) :=
      tendsto_sum_nat_add g
    have h_ev := (Filter.Tendsto.eventually h_tendsto
      (Iio_mem_nhds (show (0 : ℝ) < ε / 2 by linarith)))
    rw [Filter.Eventually, Filter.mem_atTop_sets] at h_ev
    obtain ⟨N, hN⟩ := h_ev
    exact ⟨N, hN N le_rfl⟩
  obtain ⟨N, hN_tail⟩ := h_tail_small
  -- Step 5: Each v ↦ mapImage(T_{v.1}, T_{v.2})(m) is continuous in the NTP topology
  have h_mapImage_cont : ∀ m,
      Continuous (fun v : ℝ × ℝ => GaussianField.mapImage
        (GaussianField.circleTranslation Lt v.1)
        (GaussianField.circleTranslation Ls v.2) m) := by
    intro m
    show Continuous (fun v : ℝ × ℝ =>
      GaussianField.NuclearTensorProduct.pure
        (GaussianField.circleTranslation Lt v.1 (ψ_t (Nat.unpair m).1))
        (GaussianField.circleTranslation Ls v.2 (ψ_s (Nat.unpair m).2)))
    have h1 : Continuous (fun v : ℝ × ℝ =>
        GaussianField.circleTranslation Lt v.1 (ψ_t (Nat.unpair m).1)) :=
      (circleTranslation_continuous_in_s (ψ_t (Nat.unpair m).1)).comp continuous_fst
    have h2 : Continuous (fun v : ℝ × ℝ =>
        GaussianField.circleTranslation Ls v.2 (ψ_s (Nat.unpair m).2)) :=
      (circleTranslation_continuous_in_s (ψ_s (Nat.unpair m).2)).comp continuous_snd
    exact GaussianField.NuclearTensorProduct.pure_continuous.comp (h1.prodMk h2)
  -- Step 6: The seminorm of mapImage is continuous, so eventually head < ε/2
  have h_head_small : ∀ᶠ v in nhds v₀,
      ∑ m ∈ Finset.range N, |f.val m| *
        RapidDecaySeq.rapidDecaySeminorm k
          (GaussianField.mapImage
            (GaussianField.circleTranslation Lt v.1)
            (GaussianField.circleTranslation Ls v.2) m -
           GaussianField.mapImage
            (GaussianField.circleTranslation Lt v₀.1)
            (GaussianField.circleTranslation Ls v₀.2) m) < ε / 2 := by
    have h_tendsto : Filter.Tendsto (fun v =>
        ∑ m ∈ Finset.range N, |f.val m| *
          RapidDecaySeq.rapidDecaySeminorm k
            (GaussianField.mapImage
              (GaussianField.circleTranslation Lt v.1)
              (GaussianField.circleTranslation Ls v.2) m -
             GaussianField.mapImage
              (GaussianField.circleTranslation Lt v₀.1)
              (GaussianField.circleTranslation Ls v₀.2) m))
        (nhds v₀) (nhds 0) := by
      have : (0 : ℝ) = ∑ _ ∈ Finset.range N, (0 : ℝ) := by simp
      rw [this]; clear this
      apply tendsto_finset_sum
      intro m _
      have : (0 : ℝ) = |f.val m| * 0 := by simp
      rw [this]; clear this
      apply Filter.Tendsto.const_mul
      have h_cont_diff : Continuous (fun v : ℝ × ℝ =>
          GaussianField.mapImage
            (GaussianField.circleTranslation Lt v.1)
            (GaussianField.circleTranslation Ls v.2) m -
          GaussianField.mapImage
            (GaussianField.circleTranslation Lt v₀.1)
            (GaussianField.circleTranslation Ls v₀.2) m) :=
        (h_mapImage_cont m).sub continuous_const
      have h_at_v₀ : (fun v : ℝ × ℝ =>
          GaussianField.mapImage
            (GaussianField.circleTranslation Lt v.1)
            (GaussianField.circleTranslation Ls v.2) m -
          GaussianField.mapImage
            (GaussianField.circleTranslation Lt v₀.1)
            (GaussianField.circleTranslation Ls v₀.2) m) v₀ = 0 := sub_self _
      have h_comp_cont : Continuous (fun v : ℝ × ℝ =>
          RapidDecaySeq.rapidDecaySeminorm k
            (GaussianField.mapImage
              (GaussianField.circleTranslation Lt v.1)
              (GaussianField.circleTranslation Ls v.2) m -
            GaussianField.mapImage
              (GaussianField.circleTranslation Lt v₀.1)
              (GaussianField.circleTranslation Ls v₀.2) m)) :=
        (h_ws.continuous_seminorm k).comp h_cont_diff
      have h_val_at_v₀ : RapidDecaySeq.rapidDecaySeminorm k
          (GaussianField.mapImage
            (GaussianField.circleTranslation Lt v₀.1)
            (GaussianField.circleTranslation Ls v₀.2) m -
          GaussianField.mapImage
            (GaussianField.circleTranslation Lt v₀.1)
            (GaussianField.circleTranslation Ls v₀.2) m) = 0 := by
        rw [sub_self]; exact map_zero _
      rw [← h_val_at_v₀]
      exact h_comp_cont.continuousAt
    exact h_tendsto.eventually (Iio_mem_nhds (by linarith))
  -- Step 7: Bound the seminorm using CLM expansion + triangle inequality
  have h_mapCLM_basis : ∀ (T₁ : E_t →L[ℝ] E_t) (T₂ : E_s →L[ℝ] E_s) (m : ℕ),
      GaussianField.nuclearTensorProduct_mapCLM T₁ T₂ (RapidDecaySeq.basisVec m) =
      GaussianField.mapImage T₁ T₂ m := by
    intro T₁ T₂ m
    have hbv := GaussianField.NuclearTensorProduct.basisVec_eq_pure
      (DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis (E := E_t))
      (DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis (E := E_s)) m
    rw [hbv]
    exact GaussianField.nuclearTensorProduct_mapCLM_pure T₁ T₂ _ _
  -- HasSum for the CLM expansion
  have h_hasSum : ∀ (T₁ : E_t →L[ℝ] E_t) (T₂ : E_s →L[ℝ] E_s),
      HasSum (fun m => f.val m • GaussianField.mapImage T₁ T₂ m)
        (GaussianField.nuclearTensorProduct_mapCLM T₁ T₂ f) := by
    intro T₁ T₂
    have h := (RapidDecaySeq.hasSum_basisVec f).mapL
      (GaussianField.nuclearTensorProduct_mapCLM T₁ T₂)
    simp only at h
    convert h using 1
    ext1 m
    show f.val m • GaussianField.mapImage T₁ T₂ m =
      GaussianField.nuclearTensorProduct_mapCLM T₁ T₂ (f.val m • RapidDecaySeq.basisVec m)
    calc f.val m • GaussianField.mapImage T₁ T₂ m
        = f.val m • GaussianField.nuclearTensorProduct_mapCLM T₁ T₂
            (RapidDecaySeq.basisVec m) := by rw [h_mapCLM_basis]
      _ = GaussianField.nuclearTensorProduct_mapCLM T₁ T₂
            (f.val m • RapidDecaySeq.basisVec m) :=
          ((GaussianField.nuclearTensorProduct_mapCLM T₁ T₂).map_smul
            (f.val m) (RapidDecaySeq.basisVec m)).symm
  -- Define abbreviations for the CLMs at v and v₀
  set T_v := fun (v : ℝ × ℝ) => GaussianField.nuclearTensorProduct_mapCLM
    (GaussianField.circleTranslation Lt v.1)
    (GaussianField.circleTranslation Ls v.2)
  -- Difference HasSum
  have h_diff_hasSum : ∀ (v : ℝ × ℝ),
      HasSum (fun m => f.val m •
        (GaussianField.mapImage
          (GaussianField.circleTranslation Lt v.1)
          (GaussianField.circleTranslation Ls v.2) m -
         GaussianField.mapImage
          (GaussianField.circleTranslation Lt v₀.1)
          (GaussianField.circleTranslation Ls v₀.2) m))
        (GaussianField.asymTorusTranslation Lt Ls v f -
         GaussianField.asymTorusTranslation Lt Ls v₀ f) := by
    intro v
    have h1 := h_hasSum (GaussianField.circleTranslation Lt v.1)
      (GaussianField.circleTranslation Ls v.2)
    have h2 := h_hasSum (GaussianField.circleTranslation Lt v₀.1)
      (GaussianField.circleTranslation Ls v₀.2)
    convert h1.sub h2 using 1
    ext1 m; simp [smul_sub]
  -- Filter the eventually from h_head_small.
  filter_upwards [h_head_small] with v hv_head
  -- Need: seminorm_k(T_v f - T_{v₀} f) < ε
  set d := fun m => GaussianField.mapImage
    (GaussianField.circleTranslation Lt v.1)
    (GaussianField.circleTranslation Ls v.2) m -
    GaussianField.mapImage
    (GaussianField.circleTranslation Lt v₀.1)
    (GaussianField.circleTranslation Ls v₀.2) m
  -- seminorm_k(T_v f - T_{v₀} f) ≤ Σ' m, |f_m| * seminorm_k(d m)
  have h_dk_summable : Summable (fun m => |f.val m| *
      RapidDecaySeq.rapidDecaySeminorm k (d m)) :=
    hg_summable.of_nonneg_of_le
      (fun m => mul_nonneg (abs_nonneg _) (apply_nonneg _ _))
      (fun m => by
        have h_sub := map_sub_le_add (RapidDecaySeq.rapidDecaySeminorm k)
          (GaussianField.mapImage
            (GaussianField.circleTranslation Lt v.1)
            (GaussianField.circleTranslation Ls v.2) m)
          (GaussianField.mapImage
            (GaussianField.circleTranslation Lt v₀.1)
            (GaussianField.circleTranslation Ls v₀.2) m)
        calc |f.val m| * RapidDecaySeq.rapidDecaySeminorm k (d m)
            ≤ |f.val m| * (2 * K * (1 + (m : ℝ)) ^ S) :=
            mul_le_mul_of_nonneg_left
              (calc RapidDecaySeq.rapidDecaySeminorm k (d m)
                  ≤ _ := h_sub
                _ ≤ K * (1 + (m : ℝ)) ^ S + K * (1 + (m : ℝ)) ^ S :=
                  add_le_add (h_uniform_bound v m) (h_uniform_bound v₀ m)
                _ = 2 * K * (1 + (m : ℝ)) ^ S := by ring)
              (abs_nonneg _)
          _ = g m := by simp only [g]; ring)
  have h_seminorm_le : RapidDecaySeq.rapidDecaySeminorm k
      (GaussianField.asymTorusTranslation Lt Ls v f -
       GaussianField.asymTorusTranslation Lt Ls v₀ f) ≤
      ∑' m, |f.val m| * RapidDecaySeq.rapidDecaySeminorm k (d m) := by
    apply le_of_tendsto
      ((h_ws.continuous_seminorm k).continuousAt.tendsto.comp
        (h_diff_hasSum v).tendsto_sum_nat)
    rw [Filter.Eventually, Filter.mem_atTop_sets]
    refine ⟨0, fun n _ => ?_⟩
    calc (RapidDecaySeq.rapidDecaySeminorm k)
          (∑ m ∈ Finset.range n, f.val m • d m)
        ≤ ∑ m ∈ Finset.range n,
            (RapidDecaySeq.rapidDecaySeminorm k) (f.val m • d m) :=
          (Finset.range n).le_sum_of_subadditive _
            (map_zero (RapidDecaySeq.rapidDecaySeminorm k)).le
            (RapidDecaySeq.rapidDecaySeminorm k).add_le'
            (fun m => f.val m • d m)
      _ = ∑ m ∈ Finset.range n,
            |f.val m| * (RapidDecaySeq.rapidDecaySeminorm k) (d m) := by
          congr 1; ext m
          show (RapidDecaySeq.rapidDecaySeminorm k) (f.val m • d m) =
            |f.val m| * (RapidDecaySeq.rapidDecaySeminorm k) (d m)
          show ∑' n, |(f.val m • d m).val n| * (1 + (n : ℝ)) ^ k =
            |f.val m| * ∑' n, |(d m).val n| * (1 + (n : ℝ)) ^ k
          conv_lhs => arg 1; ext n; rw [show (f.val m • d m).val n = f.val m * (d m).val n from rfl,
            abs_mul, mul_assoc]
          rw [tsum_mul_left]
      _ ≤ ∑' m, |f.val m| * (RapidDecaySeq.rapidDecaySeminorm k) (d m) :=
          h_dk_summable.sum_le_tsum _
            (fun m _ => mul_nonneg (abs_nonneg _) (apply_nonneg _ _))
  -- Now split the tsum at N: head + tail
  have h_tsum_split : ∑' m, |f.val m| * RapidDecaySeq.rapidDecaySeminorm k (d m) ≤
      (∑ m ∈ Finset.range N, |f.val m| * RapidDecaySeq.rapidDecaySeminorm k (d m)) +
      ∑' m, g (m + N) := by
    have h_dk_le_g : ∀ m, |f.val m| * RapidDecaySeq.rapidDecaySeminorm k (d m) ≤ g m := by
      intro m
      calc |f.val m| * RapidDecaySeq.rapidDecaySeminorm k (d m)
          ≤ |f.val m| * (2 * K * (1 + (m : ℝ)) ^ S) :=
            mul_le_mul_of_nonneg_left
              ((map_sub_le_add (RapidDecaySeq.rapidDecaySeminorm k) _ _).trans
                ((add_le_add (h_uniform_bound v m) (h_uniform_bound v₀ m)).trans
                (by linarith)))
              (abs_nonneg _)
        _ = g m := by simp only [g]; ring
    rw [(h_dk_summable.sum_add_tsum_nat_add N).symm]
    exact add_le_add le_rfl
      (Summable.tsum_le_tsum
        (fun m => h_dk_le_g (m + N))
        (h_dk_summable.comp_injective (add_left_injective N))
        (hg_summable.comp_injective (add_left_injective N)))
  -- Combine: seminorm_k(diff) ≤ head + tail < ε/2 + ε/2 = ε
  calc RapidDecaySeq.rapidDecaySeminorm k
        (GaussianField.asymTorusTranslation Lt Ls v f -
         GaussianField.asymTorusTranslation Lt Ls v₀ f)
      ≤ ∑' m, |f.val m| * RapidDecaySeq.rapidDecaySeminorm k (d m) :=
        h_seminorm_le
    _ ≤ (∑ m ∈ Finset.range N, |f.val m| *
          RapidDecaySeq.rapidDecaySeminorm k (d m)) +
        ∑' m, g (m + N) := h_tsum_split
    _ < ε / 2 + ε / 2 := add_lt_add hv_head hN_tail
    _ = ε := by ring

-- **Theorem 4/4:** Lattice approximation error vanishes: Z_N[T_v f] - Z_N[f] → 0.
-- Proof: Round v to lattice point w_n, use axioms 1-3, squeeze_zero_norm.
-- Symmetric version at TorusInteractingOS.lean:1520.
theorem asymTorusGF_latticeApproximation_error_vanishes
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (v : ℝ × ℝ) (f : AsymTorusTestFunction Lt Ls) :
    Tendsto (fun n =>
      asymTorusGeneratingFunctional Lt Ls
        (asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass)
        (asymTorusTranslation Lt Ls v f) -
      asymTorusGeneratingFunctional Lt Ls
        (asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass) f)
    atTop (nhds 0) := by
  -- Step 1: Get the uniform GF Lipschitz bound
  obtain ⟨B, p, hp_cont, hp_zero, hp_bound⟩ :=
    asymGf_sub_norm_le_seminorm Lt Ls P mass hmass
  -- Step 2: For each n, define w_n as the nearest lattice point to v.
  -- w_n = (a_t_n * j₁_n, a_s_n * j₂_n) where a_t_n = Lt/(φ(n)+1), a_s_n = Ls/(φ(n)+1)
  set a_t : ℕ → ℝ := fun n => circleSpacing Lt (φ n + 1)
  set a_s : ℕ → ℝ := fun n => circleSpacing Ls (φ n + 1)
  set j₁ : ℕ → ℤ := fun n => round (v.1 / a_t n)
  set j₂ : ℕ → ℤ := fun n => round (v.2 / a_s n)
  set w : ℕ → ℝ × ℝ := fun n => (a_t n * j₁ n, a_s n * j₂ n)
  -- Step 3: Z_N[T_{w_n} f] = Z_N[f] by lattice translation invariance
  have h_lattice_inv : ∀ n,
      asymTorusGeneratingFunctional Lt Ls
        (asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass)
        (asymTorusTranslation Lt Ls (w n) f) =
      asymTorusGeneratingFunctional Lt Ls
        (asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass) f := by
    intro n
    exact (asymTorusInteractingMeasure_gf_latticeTranslation_invariant
      Lt Ls (φ n + 1) P mass hmass (j₁ n) (j₂ n) f).symm
  -- Step 4: Rewrite the target as Z_N[T_v f] - Z_N[T_{w_n} f]
  have h_rewrite : ∀ n,
      asymTorusGeneratingFunctional Lt Ls
        (asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass)
        (asymTorusTranslation Lt Ls v f) -
      asymTorusGeneratingFunctional Lt Ls
        (asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass) f =
      asymTorusGeneratingFunctional Lt Ls
        (asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass)
        (asymTorusTranslation Lt Ls v f) -
      asymTorusGeneratingFunctional Lt Ls
        (asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass)
        (asymTorusTranslation Lt Ls (w n) f) := by
    intro n; rw [h_lattice_inv n]
  simp_rw [h_rewrite]
  -- Step 5: Bound ‖Z_N[T_v f] - Z_N[T_{w_n} f]‖ ≤ B * p(T_v f - T_{w_n} f)
  have h_norm_bound : ∀ n,
      ‖asymTorusGeneratingFunctional Lt Ls
          (asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass)
          (asymTorusTranslation Lt Ls v f) -
        asymTorusGeneratingFunctional Lt Ls
          (asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass)
          (asymTorusTranslation Lt Ls (w n) f)‖ ≤
      B * p (asymTorusTranslation Lt Ls v f - asymTorusTranslation Lt Ls (w n) f) :=
    fun n => hp_bound _ _ _
  -- Step 6: Show B * p(T_v f - T_{w_n} f) → 0
  -- Step 6a: a_t_n → 0 and a_s_n → 0 (lattice spacings vanish)
  have h_at_tendsto : Tendsto a_t atTop (nhds 0) := by
    change Tendsto (fun n => Lt / (↑(φ n + 1) : ℝ)) atTop (nhds 0)
    have h_denom : Tendsto (fun n => (↑(φ n + 1) : ℝ)) atTop atTop := by
      exact tendsto_natCast_atTop_atTop.comp
        ((tendsto_add_atTop_nat 1).comp (hφ.tendsto_atTop))
    exact h_denom.const_div_atTop Lt
  have h_as_tendsto : Tendsto a_s atTop (nhds 0) := by
    change Tendsto (fun n => Ls / (↑(φ n + 1) : ℝ)) atTop (nhds 0)
    have h_denom : Tendsto (fun n => (↑(φ n + 1) : ℝ)) atTop atTop := by
      exact tendsto_natCast_atTop_atTop.comp
        ((tendsto_add_atTop_nat 1).comp (hφ.tendsto_atTop))
    exact h_denom.const_div_atTop Ls
  -- Step 6b: w_n → v (each component is within a_i_n/2 of v_i)
  have h_w_tendsto : Tendsto w atTop (nhds v) := by
    rw [Prod.tendsto_iff]
    have h_comp : ∀ (vi : ℝ) (ai : ℕ → ℝ) (ji : ℕ → ℤ),
        (∀ n, ji n = round (vi / ai n)) →
        Tendsto ai atTop (nhds 0) →
        (∀ n, 0 < ai n) →
        Tendsto (fun n => ai n * (ji n : ℝ)) atTop (nhds vi) := by
      intro vi ai ji hji hai hai_pos
      have h_a_half : Tendsto (fun n => ai n / 2) atTop (nhds 0) := by
        simpa using hai.div_const (2 : ℝ)
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le
        (g := fun n => vi - ai n / 2) (h := fun n => vi + ai n / 2)
      · simpa using tendsto_const_nhds.sub h_a_half
      · simpa using tendsto_const_nhds.add h_a_half
      · intro n; simp only
        have ha_pos : 0 < ai n := hai_pos n
        have h_bnd := abs_sub_round (vi / ai n)
        rw [abs_le] at h_bnd
        have h1 : vi / ai n - (1:ℝ) / 2 ≤ ↑(ji n) := by
          rw [hji]; linarith [h_bnd.1]
        have h2 : vi = ai n * (vi / ai n) := by field_simp
        linarith [mul_le_mul_of_nonneg_left h1 ha_pos.le]
      · intro n; simp only
        have ha_pos : 0 < ai n := hai_pos n
        have h_bnd := abs_sub_round (vi / ai n)
        rw [abs_le] at h_bnd
        have h1 : ↑(ji n) ≤ vi / ai n + (1:ℝ) / 2 := by
          rw [hji]; linarith [h_bnd.2]
        have h2 : vi = ai n * (vi / ai n) := by field_simp
        linarith [mul_le_mul_of_nonneg_left h1 ha_pos.le]
    constructor
    · change Tendsto (fun n => (w n).1) atTop (nhds v.1)
      change Tendsto (fun n => a_t n * (j₁ n : ℝ)) atTop (nhds v.1)
      exact h_comp v.1 a_t j₁ (fun _ => rfl) h_at_tendsto
        (fun n => circleSpacing_pos Lt (φ n + 1))
    · change Tendsto (fun n => (w n).2) atTop (nhds v.2)
      change Tendsto (fun n => a_s n * (j₂ n : ℝ)) atTop (nhds v.2)
      exact h_comp v.2 a_s j₂ (fun _ => rfl) h_as_tendsto
        (fun n => circleSpacing_pos Ls (φ n + 1))
  -- Step 6c: T_{w_n} f → T_v f (by continuity of translation)
  have h_Tw_tendsto :
      Tendsto (fun n => asymTorusTranslation Lt Ls (w n) f) atTop
        (nhds (asymTorusTranslation Lt Ls v f)) :=
    (asymTorusTranslation_continuous_in_v Lt Ls f).continuousAt.tendsto.comp
      h_w_tendsto
  -- Step 6d: p(T_v f - T_{w_n} f) → p(T_v f - T_v f) = p(0) = 0
  have h_p_tendsto :
      Tendsto (fun n => p (asymTorusTranslation Lt Ls v f -
        asymTorusTranslation Lt Ls (w n) f)) atTop (nhds 0) := by
    have h_sub_tendsto : Tendsto
        (fun n => asymTorusTranslation Lt Ls v f - asymTorusTranslation Lt Ls (w n) f)
        atTop (nhds (asymTorusTranslation Lt Ls v f - asymTorusTranslation Lt Ls v f)) :=
      Filter.Tendsto.const_sub _ h_Tw_tendsto
    rw [sub_self] at h_sub_tendsto
    rw [← hp_zero]
    exact hp_cont.continuousAt.tendsto.comp h_sub_tendsto
  -- Step 7: Conclude by squeezing
  apply squeeze_zero_norm (fun n => h_norm_bound n)
  -- Need: B * p(T_v f - T_{w_n} f) → 0
  have : Tendsto (fun n => B * p (asymTorusTranslation Lt Ls v f -
      asymTorusTranslation Lt Ls (w n) f)) atTop (nhds (B * 0)) :=
    h_p_tendsto.const_mul B
  simpa using this

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
  intro v f
  -- Step 1: GF convergence from weak convergence via cos/sin decomposition
  have hgf_tendsto : ∀ g : AsymTorusTestFunction Lt Ls, Tendsto (fun n =>
      asymTorusGeneratingFunctional Lt Ls
        (asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass) g)
      atTop (nhds (asymTorusGeneratingFunctional Lt Ls μ g)) := by
    intro g
    -- Re(Z_N[g]) = ∫ cos(ωg) → ∫ cos(ωg) = Re(Z[g])
    have h_re : Tendsto (fun n => (asymTorusGeneratingFunctional Lt Ls
        (asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass) g).re)
        atTop (nhds (asymTorusGeneratingFunctional Lt Ls μ g).re) := by
      simp_rw [asymGf_re_eq_cos_integral]
      exact hconv _ (asymCosEval_continuous Lt Ls g) (asymCosEval_bounded Lt Ls g)
    -- Im(Z_N[g]) = ∫ sin(ωg) → ∫ sin(ωg) = Im(Z[g])
    have h_im : Tendsto (fun n => (asymTorusGeneratingFunctional Lt Ls
        (asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass) g).im)
        atTop (nhds (asymTorusGeneratingFunctional Lt Ls μ g).im) := by
      simp_rw [asymGf_im_eq_sin_integral]
      exact hconv _ (asymSinEval_continuous Lt Ls g) (asymSinEval_bounded Lt Ls g)
    -- Combine Re + Im into ℂ convergence
    rw [show asymTorusGeneratingFunctional Lt Ls μ g =
      ↑(asymTorusGeneratingFunctional Lt Ls μ g).re +
      ↑(asymTorusGeneratingFunctional Lt Ls μ g).im * I from (re_add_im _).symm]
    exact (h_re.ofReal.add (h_im.ofReal.mul_const I)).congr (fun n => (re_add_im _))
  -- Step 2: The difference Z_N[T_v f] - Z_N[f] → Z[T_v f] - Z[f]
  have h_Tvf := hgf_tendsto (asymTorusTranslation Lt Ls v f)
  have h_f := hgf_tendsto f
  have h_sub : Tendsto (fun n =>
      asymTorusGeneratingFunctional Lt Ls
        (asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass)
        (asymTorusTranslation Lt Ls v f) -
      asymTorusGeneratingFunctional Lt Ls
        (asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass) f)
      atTop (nhds (asymTorusGeneratingFunctional Lt Ls μ
        (asymTorusTranslation Lt Ls v f) -
      asymTorusGeneratingFunctional Lt Ls μ f)) := h_Tvf.sub h_f
  -- Step 3: The same difference → 0 by lattice approximation error vanishing
  have h_diff := asymTorusGF_latticeApproximation_error_vanishes Lt Ls P mass hmass φ hφ v f
  -- Step 4: Uniqueness of limits gives Z[T_v f] - Z[f] = 0
  have h_eq : asymTorusGeneratingFunctional Lt Ls μ (asymTorusTranslation Lt Ls v f) -
      asymTorusGeneratingFunctional Lt Ls μ f = 0 :=
    tendsto_nhds_unique h_sub h_diff
  exact (sub_eq_zero.mp h_eq).symm

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
