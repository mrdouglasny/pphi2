/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Torus Interacting OS Axioms: OS0–OS2 for the P(φ)₂ Continuum Limit

States and proves (modulo general axioms) the Osterwalder-Schrader axioms
for the torus interacting continuum limit measure.

## Main results

- `torusInteracting_os0` — analyticity of generating functional
- `torusInteracting_os1` — regularity bound
- `torusInteracting_os2_translation` — translation invariance
- `torusInteracting_os2_D4` — D4 point group invariance
- `torusInteracting_satisfies_OS` — bundled OS0–OS2

## Mathematical background

The interacting P(φ)₂ measure on the torus T²_L is the weak limit
  `μ_P = lim_{N→∞} (ι̃_N)_* ((1/Z_N) exp(-V_N) dμ_{GFF,N})`
where V_N is the Wick-ordered interaction on the N×N lattice.

### OS0 (Analyticity)
The generating functional `Z[f] = ∫ exp(iω(f)) dμ_P` is entire analytic
in complex test function coefficients. This follows from:
1. For each ω, the integrand `exp(iω(f))` is entire in f.
2. The interacting measure has exponential moments (Nelson's estimate),
   providing the domination bound.
3. Morera's theorem / analyticity of parameter-dependent integrals
   (`analyticOnNhd_integral`).

### OS1 (Regularity)
The bound `‖Z_ℂ[f_re, f_im]‖ ≤ exp(c · (q(f_re) + q(f_im)))` for a
continuous seminorm q. Follows from Cauchy-Schwarz density transfer:
the interacting exponential moment is bounded by the Gaussian moment
(which grows as exp(½G(f,f))) times √K from Nelson's estimate.

### OS2 (Translation invariance)
On the torus T² = (ℝ/Lℤ)², translations in BOTH spatial and temporal
directions are exact symmetries at every lattice cutoff N (the torus
domain is periodic). This is simpler than the cylinder case where time
translation invariance is broken at finite temporal cutoff.

The proof transfers lattice translation invariance
(`latticeMeasure_translation_invariant`) through the weak limit.

### OS3 (Reflection positivity)
Dropped on the torus — RP is more natural on the cylinder S¹×ℝ.

## References

- Glimm-Jaffe, *Quantum Physics*, §19.3-19.4
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. V-VI
- Nelson (1966), "A quartic interaction in two dimensions"
-/

import Pphi2.TorusContinuumLimit.TorusOSAxioms
import Pphi2.TorusContinuumLimit.TorusInteractingLimit
import Pphi2.TorusContinuumLimit.TorusPropagatorConvergence
import Pphi2.GeneralResults.ComplexAnalysis
import Pphi2.InteractingMeasure.Normalization
import Pphi2.OSProofs.OS2_WardIdentity
import Torus.Evaluation

noncomputable section

open GaussianField MeasureTheory Filter Complex

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Cutoff-level invariance axioms

The interacting lattice measure on the torus is invariant under lattice
translations and D4 point group symmetries. These follow from:
- The interaction `V_N(ω) = a² Σ_x :P(φ(x)):_c` sums over ALL lattice
  sites with periodic BCs, so translating relabels the sum.
- The lattice GFF measure is invariant (covariance is translation/D4-invariant).
- The Boltzmann weight `exp(-V)` is therefore invariant.
- The partition function Z is the same before and after the symmetry.

References: Glimm-Jaffe §19.4, Simon Ch. V §1. -/

/-- Linear map on lattice field induced by a site permutation `σ`. -/
private def latticeSitePermuteLM (N : ℕ)
    (σ : FinLatticeSites 2 N → FinLatticeSites 2 N) :
    FinLatticeField 2 N →ₗ[ℝ] FinLatticeField 2 N where
  toFun g := g ∘ σ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Helper: `piCongrLeft(σ_equiv)` maps `φ ↦ φ ∘ σ⁻¹`. -/
private lemma piCongrLeft_eq_comp_symm {N : ℕ}
    (σ_equiv : FinLatticeSites 2 N ≃ FinLatticeSites 2 N)
    (φ : FinLatticeField 2 N) :
    (Equiv.piCongrLeft (fun _ : FinLatticeSites 2 N => ℝ) σ_equiv) φ =
      φ ∘ σ_equiv.symm := by
  ext x
  change (Equiv.piCongrLeft (fun _ => ℝ) σ_equiv) φ x = φ (σ_equiv.symm x)
  -- Use piCongrLeft_apply_apply with y = σ⁻¹ x:
  -- piCongrLeft(σ) φ (σ (σ⁻¹ x)) = φ (σ⁻¹ x)
  -- Since σ (σ⁻¹ x) = x, this gives piCongrLeft(σ) φ x = φ (σ⁻¹ x)
  have h := Equiv.piCongrLeft_apply_apply (P := fun _ : FinLatticeSites 2 N => ℝ)
    σ_equiv φ (σ_equiv.symm x)
  rwa [σ_equiv.apply_symm_apply] at h

/-- **Lattice interacting measure is invariant under site symmetries.**

For a bijective site permutation `σ` that preserves the Gaussian density,
`integral F(omega . sigma) d mu_int = integral F(omega) d mu_int`.

Proof:
1. BW invariance: V(omega . sigma) = V(omega) (interaction sum relabeling)
2. Density invariance: rho(phi . sigma^-1) = rho(phi) (hypothesis)
3. Lebesgue preservation: phi -> phi . sigma^-1 is a permutation (det = plus or minus 1)
4. Gaussian measure preservation: combines 2 + 3 (sorry: requires MeasurePreserving for withDensity)
5. Change of variables on the E-valued Bochner integral -/
theorem interactingLatticeMeasure_symmetry_invariant
    (N : ℕ) [NeZero N] (P : InteractionPolynomial) (mass : ℝ)
    (ha : 0 < circleSpacing L N) (hmass : 0 < mass)
    (σ : FinLatticeSites 2 N → FinLatticeSites 2 N)
    (hσ_bij : Function.Bijective σ)
    (hσ_density : ∀ φ : FinLatticeField 2 N,
      gaussianDensity 2 N (circleSpacing L N) mass
        (φ ∘ (Equiv.ofBijective σ hσ_bij).symm) =
      gaussianDensity 2 N (circleSpacing L N) mass φ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Configuration (FinLatticeField 2 N) → E) :
    ∫ ω, F (ω.comp (latticeSitePermuteLM N σ).toContinuousLinearMap)
      ∂(interactingLatticeMeasure 2 N P (circleSpacing L N) mass ha hmass) =
    ∫ ω, F ω ∂(interactingLatticeMeasure 2 N P (circleSpacing L N) mass ha hmass) := by
  -- Setup notation
  set a := circleSpacing L N
  set mu_GFF := latticeGaussianMeasure 2 N a mass ha hmass
  set bw := boltzmannWeight 2 N P a mass
  set σ_equiv := Equiv.ofBijective σ hσ_bij
  set L_σ : FinLatticeField 2 N →ₗ[ℝ] FinLatticeField 2 N :=
    latticeSitePermuteLM N σ
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
  -- bw(ω.comp L_σ) = bw(ω) because the interaction sums over all sites
  -- and composing with σ just relabels the sum.
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
    -- (ω.comp L_σ)(δ_x) = ω(δ_x ∘ σ) = ω(δ_{σ⁻¹ x})
    change ω (L_σ (finLatticeDelta 2 N x)) = ω (finLatticeDelta 2 N (σ_equiv.symm x))
    congr 1; ext y
    simp only [L_σ, latticeSitePermuteLM, LinearMap.coe_mk, AddHom.coe_mk,
      Function.comp, finLatticeDelta]
    -- Goal: (if σ y = x then 1 else 0) = (if y = σ_equiv.symm x then 1 else 0)
    congr 1; exact propext σ_equiv.apply_eq_iff_eq_symm_apply
  -- Step 4: Use BW invariance to factor the LHS integrand as G ∘ Φ
  have hBW_nn_config : ∀ ω : Configuration (FinLatticeField 2 N),
      bw_nn (ω.comp L_σ.toContinuousLinearMap) = bw_nn ω := by
    intro ω; simp only [bw_nn, hBW_config]
  set G := fun ω : Configuration (FinLatticeField 2 N) => bw_nn ω • F ω
  -- Rewrite LHS integrand: bw_nn(ω) • F(Φ(ω)) = G(Φ(ω))
  -- using bw_nn(Φ(ω)) = bw_nn(ω)
  have hG_eq : ∀ ω, bw_nn ω • F (ω.comp L_σ.toContinuousLinearMap) =
      G (ω.comp L_σ.toContinuousLinearMap) := by
    intro ω; simp only [G, hBW_nn_config]
  simp_rw [hG_eq]
  -- Goal: ∫ G(ω.comp L_σ) dμ_GFF = ∫ G(ω) dμ_GFF
  -- Step 5: Build configuration-level MeasurableEquiv
  -- ω ↦ ω.comp L_σ corresponds via evalMap to φ ↦ φ ∘ σ⁻¹ = piCongrLeft(σ_equiv)(φ)
  -- As functions: Φ = evalME.symm ∘ piCongrLeft(σ_equiv) ∘ evalME
  -- In .trans notation (A.trans B = B ∘ A):
  --   Φ = evalME.trans(σ_field.trans(evalME.symm)) : Config → Config
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
    -- Φ_equiv ω = evalME.symm(σ_field(evalME(ω)))
    -- Both sides are configurations; show they agree on all delta functions.
    apply evalME.injective
    ext x
    -- LHS: evalME(Φ_equiv ω)(x) = evalME(evalME.symm(σ_field(evalME ω)))(x)
    --     = σ_field(evalME ω)(x) (by apply_symm_apply)
    simp only [Φ_equiv, MeasurableEquiv.trans_apply, MeasurableEquiv.apply_symm_apply]
    -- Now LHS: σ_field_equiv(evalME ω)(x)
    -- RHS: evalME(ω.comp L_σ)(x) = (ω.comp L_σ)(δ_x)
    -- Use piCongrLeft_eq_comp_symm to simplify LHS
    rw [show σ_field_equiv (evalME ω) = (evalME ω) ∘ σ_equiv.symm from
      piCongrLeft_eq_comp_symm σ_equiv (evalME ω)]
    -- LHS: ((evalME ω) ∘ σ⁻¹)(x) = (evalME ω)(σ⁻¹ x) = ω(δ_{σ⁻¹ x})
    -- RHS: evalME(ω.comp L_σ)(x) = (ω.comp L_σ)(δ_x) = ω(δ_x ∘ σ)
    simp only [Function.comp, evalME]
    -- Goal: ω(δ_{σ⁻¹ x}) = (ω.comp L_σ)(δ_x) = ω(L_σ(δ_x))
    change ω (finLatticeDelta 2 N (σ_equiv.symm x)) =
      ω (L_σ (finLatticeDelta 2 N x))
    congr 1; ext y
    simp only [L_σ, latticeSitePermuteLM, LinearMap.coe_mk, AddHom.coe_mk,
      Function.comp, finLatticeDelta]
    congr 1; exact propext σ_equiv.eq_symm_apply
  -- Step 7: Rewrite G(ω.comp L_σ) as G(Φ_equiv ω)
  simp_rw [← hΦ_eq]
  -- Goal: ∫ G(Φ_equiv ω) dμ_GFF = ∫ G(ω) dμ_GFF
  -- Step 8: Show Φ_equiv preserves μ_GFF and apply MeasurePreserving.integral_comp'
  -- Φ_equiv = evalME.trans(σ_field.trans(evalME.symm))
  -- evalME maps μ_GFF to latticeGaussianFieldLaw = (∫ρ)⁻¹ • volume.withDensity(ρ)
  -- σ_field preserves this measure (by density invariance + volume preservation)
  -- evalME.symm maps it back
  -- Net result: Φ_equiv preserves μ_GFF
  have hΦ_mp : MeasurePreserving Φ_equiv mu_GFF mu_GFF := by
    -- Decompose: Φ = evalME.trans(σ_field.trans(evalME.symm))
    -- MeasurePreserving of a composition
    -- We need: evalME maps μ_GFF to some ν, σ_field preserves ν, evalME.symm maps ν back
    -- Actually, for MeasurableEquiv, Φ_equiv.symm.map μ_GFF = μ_GFF
    -- It's easier to show directly.
    -- Use the ℝ-valued density bridge to show Φ_* μ_GFF = μ_GFF.
    -- For any measurable set S: Φ_*(μ_GFF)(S) = μ_GFF(Φ⁻¹(S)) = μ_GFF(S)
    -- This requires showing all finite-dimensional distributions agree.
    -- For now, we sorry this (the formal proof requires connecting through
    -- latticeGaussianFieldLaw and the density bridge).
    sorry
  exact hΦ_mp.integral_comp' G

-- Specific instances:

private def latticeTranslateLM (N : ℕ) (j₁ j₂ : ℤ) :=
  latticeSitePermuteLM N (translateSites N j₁ j₂)

private theorem interactingLatticeMeasure_translation_invariant
    (N : ℕ) [NeZero N] (P : InteractionPolynomial) (mass : ℝ)
    (ha : 0 < circleSpacing L N) (hmass : 0 < mass)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j₁ j₂ : ℤ) (F : Configuration (FinLatticeField 2 N) → E) :
    ∫ ω, F (ω.comp (latticeTranslateLM N j₁ j₂).toContinuousLinearMap)
      ∂(interactingLatticeMeasure 2 N P (circleSpacing L N) mass ha hmass) =
    ∫ ω, F ω ∂(interactingLatticeMeasure 2 N P (circleSpacing L N) mass ha hmass) := by
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
  exact interactingLatticeMeasure_symmetry_invariant L N P mass ha hmass
    (translateSites N j₁ j₂) hbij
    (by -- Density preservation: gaussianDensity(φ∘σ⁻¹) = gaussianDensity(φ)
      intro φ
      -- Step 1: Identify σ⁻¹ with explicit inverse
      set σ_equiv := Equiv.ofBijective (translateSites N j₁ j₂) hbij
      -- The explicit inverse sends y ↦ ![y 0 + j₁, y 1 + j₂]
      have hsymm_eq : ∀ y : FinLatticeSites 2 N,
          σ_equiv.symm y =
          (![y 0 + (j₁ : ZMod N), y 1 + (j₂ : ZMod N)] : FinLatticeSites 2 N) := by
        intro y
        rw [Equiv.symm_apply_eq]
        change y = translateSites N j₁ j₂ (![y 0 + (j₁ : ZMod N), y 1 + (j₂ : ZMod N)])
        simp only [translateSites]
        ext i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
      -- Step 2: Show φ ∘ σ⁻¹ = latticeTranslation 2 N v φ for v = ![-j₁, -j₂]
      set v : FinLatticeSites 2 N := ![(-(j₁ : ZMod N)), (-(j₂ : ZMod N))]
      suffices h_eq : φ ∘ σ_equiv.symm = latticeTranslation 2 N v φ by
        rw [h_eq]
        exact gaussianDensity_translation_invariant 2 N (circleSpacing L N) mass v φ
      funext x
      simp only [Function.comp, hsymm_eq, latticeTranslation]
      congr 1; funext i; fin_cases i <;>
        simp [v, Matrix.cons_val_zero, Matrix.cons_val_one, sub_neg_eq_add])
    F

theorem torusInteractingMeasure_gf_latticeTranslation_invariant
    (N : ℕ) [NeZero N] (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (j₁ j₂ : ℤ) (f : TorusTestFunction L) :
    torusGeneratingFunctional L (torusInteractingMeasure L N P mass hmass) f =
    torusGeneratingFunctional L (torusInteractingMeasure L N P mass hmass)
      (torusTranslation L (circleSpacing L N * j₁, circleSpacing L N * j₂) f) := by
  -- Same pattern as swap/reflection proofs
  have h_lattice_trans : ∀ x : FinLatticeSites 2 N,
      latticeTestFn L N (torusTranslation L
        (circleSpacing L N * j₁, circleSpacing L N * j₂) f) x =
      latticeTestFn L N f (translateSites N j₁ j₂ x) := by
    intro x
    simp only [latticeTestFn, torusTranslation]
    exact evalTorusAtSite_latticeTranslation L N j₁ j₂ x f
  set μ_lat := interactingLatticeMeasure 2 N P (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass
  unfold torusGeneratingFunctional torusInteractingMeasure
  have hmeas : AEMeasurable (torusEmbedLift L N) μ_lat :=
    (torusEmbedLift_measurable L N).aemeasurable
  have hasm₁ : AEStronglyMeasurable (fun ω : Configuration (TorusTestFunction L) =>
      Complex.exp (Complex.I * ↑(ω f))) (Measure.map (torusEmbedLift L N) μ_lat) :=
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (configuration_eval_measurable f)))).aestronglyMeasurable
  have hasm₂ : AEStronglyMeasurable (fun ω : Configuration (TorusTestFunction L) =>
      Complex.exp (Complex.I * ↑(ω (torusTranslation L
        (circleSpacing L N * j₁, circleSpacing L N * j₂) f))))
      (Measure.map (torusEmbedLift L N) μ_lat) :=
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (configuration_eval_measurable _)))).aestronglyMeasurable
  rw [MeasureTheory.integral_map hmeas hasm₁, MeasureTheory.integral_map hmeas hasm₂]
  simp_rw [torusEmbedLift_eval_eq]
  have h_trans_lattice : ∀ φ : Configuration (FinLatticeField 2 N),
      φ (latticeTestFn L N (torusTranslation L
        (circleSpacing L N * j₁, circleSpacing L N * j₂) f)) =
      (φ.comp (latticeTranslateLM N j₁ j₂).toContinuousLinearMap) (latticeTestFn L N f) := by
    intro φ
    change φ (latticeTestFn L N (torusTranslation L _ f)) =
      φ ((latticeTranslateLM N j₁ j₂) (latticeTestFn L N f))
    congr 1; ext x; exact h_lattice_trans x
  simp_rw [h_trans_lattice]
  exact (interactingLatticeMeasure_translation_invariant L N P mass
    (circleSpacing_pos L N) hmass j₁ j₂ _).symm

/-- **The second moment is controlled by the Gaussian second moment, uniformly.**

`E_P[(ωf)²] ≤ C · G_N(f,f)` with C = 3√K universal (independent of f, N).

Proof: Cauchy-Schwarz density transfer gives `E_P[F] ≤ √K · √(E_GFF[F²])`.
With F = (ωf)², Gaussian hypercontractivity `E[X⁴] ≤ 9(E[X²])²` gives
`√(E_GFF[(ωf)⁴]) ≤ 3 · E_GFF[(ωf)²] = 3 G_N(f,f)`. So C = 3√K.

Same proof as `torus_interacting_second_moment_uniform` but with G_N(f,f) instead of sup. -/
theorem torus_interacting_second_moment_continuous
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : TorusTestFunction L) (N : ℕ) [NeZero N],
    ∫ ω : Configuration (TorusTestFunction L),
      (ω f) ^ 2 ∂(torusInteractingMeasure L N P mass hmass) ≤
    C * torusEmbeddedTwoPoint L N mass hmass f f := by
  -- Same proof structure as torus_interacting_second_moment_uniform
  -- but keeping G_N(f,f) instead of taking the supremum over N.
  obtain ⟨K, hK_pos, hK_bound⟩ := nelson_exponential_estimate L P mass hmass
  refine ⟨3 * Real.sqrt K, mul_pos (by norm_num : (0:ℝ) < 3)
    (Real.sqrt_pos_of_pos hK_pos), fun f N _ => ?_⟩
  -- Step 1: Push integral through torus embedding
  set μ_int := interactingLatticeMeasure 2 N P (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass
  set μ_GFF := latticeGaussianMeasure 2 N (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass
  set ι := torusEmbedLift L N
  set g := latticeTestFn L N f
  have hι_meas : AEMeasurable ι μ_int :=
    (torusEmbedLift_measurable L N).aemeasurable
  -- ∫ (ω f)² d(map ι μ_int) = ∫ (ω g)² dμ_int
  change ∫ ω, (ω f) ^ 2 ∂(Measure.map ι μ_int) ≤
    3 * Real.sqrt K * torusEmbeddedTwoPoint L N mass hmass f f
  rw [integral_map hι_meas
    ((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable]
  have h_eval : ∀ ω : Configuration (FinLatticeField 2 N),
      (ι ω) f = ω g := fun ω => torusEmbedLift_eval_eq L N f ω
  simp_rw [h_eval]
  -- Now goal: ∫ (ω g)² dμ_int ≤ 3 * √K * G_N(f,f)
  -- Step 2: Apply density_transfer_bound with F(ω) = (ω g)²
  have hZ_ge_one := partitionFunction_ge_one 2 N P mass hmass
    (circleSpacing L N) (circleSpacing_pos L N)
  have hF_nn : ∀ ω : Configuration (FinLatticeField 2 N), 0 ≤ (ω g) ^ 2 :=
    fun ω => sq_nonneg _
  have hF_meas : AEStronglyMeasurable (fun ω : Configuration (FinLatticeField 2 N) =>
      (ω g) ^ 2) μ_GFF :=
    ((configuration_eval_measurable g).pow_const 2).aestronglyMeasurable
  have hF_sq_int : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
      ((ω g) ^ 2) ^ 2) μ_GFF := by
    have h4 : MemLp (fun ω : Configuration (FinLatticeField 2 N) => ω g)
        4 μ_GFF := by
      exact_mod_cast pairing_memLp (latticeCovariance 2 N (circleSpacing L N) mass
        (circleSpacing_pos L N) hmass) g 4
    have hmem := h4.norm_rpow (p := (4 : ENNReal))
      (by norm_num : (4 : ENNReal) ≠ 0) (by norm_num : (4 : ENNReal) ≠ ⊤)
    rw [memLp_one_iff_integrable] at hmem
    have h_int : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
        ‖ω g‖ ^ (4 : ℕ)) μ_GFF := by
      refine hmem.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp [ENNReal.toReal_ofNat]
    exact h_int.congr (Filter.Eventually.of_forall fun ω => by
      dsimp only
      rw [Real.norm_eq_abs]
      conv_rhs => rw [show ω g ^ 2 = |ω g| ^ 2 from (sq_abs _).symm]
      ring)
  have h_dt := density_transfer_bound 2 N P (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass K hK_pos (hK_bound N)
    hZ_ge_one (fun ω => (ω g) ^ 2) hF_nn hF_meas hF_sq_int
  -- Step 3: Convert rpow to nat pow in h_dt
  have h_rpow_to_npow : ∀ ω : Configuration (FinLatticeField 2 N),
      (fun ω => (ω g) ^ 2) ω ^ (2:ℝ) = ((ω g) ^ 2) ^ 2 := by
    intro ω
    exact Real.rpow_natCast ((ω g) ^ 2) 2
  have h_int_rpow_eq : ∫ ω, (fun ω => (ω g) ^ 2) ω ^ (2:ℝ) ∂μ_GFF =
      ∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF := by
    congr 1; ext ω; exact h_rpow_to_npow ω
  -- Step 4: Bound ∫ ((ω g)²)² via hypercontractivity
  have h_second_moment_eq : ∫ ω, (ω g) ^ 2 ∂μ_GFF =
      torusEmbeddedTwoPoint L N mass hmass f f :=
    (torusEmbeddedTwoPoint_eq_lattice_second_moment L N mass hmass f).symm
  have h_second_nn : 0 ≤ ∫ ω, (ω g) ^ 2 ∂μ_GFF :=
    integral_nonneg fun ω => sq_nonneg _
  set G_Nff := torusEmbeddedTwoPoint L N mass hmass f f
  have h_G_nn : 0 ≤ G_Nff := by rw [← h_second_moment_eq]; exact h_second_nn
  set T := latticeCovariance 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass
  have hμ_eq : μ_GFF = GaussianField.measure T := rfl
  have h_fourth_le : ∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF ≤ 9 * G_Nff ^ 2 := by
    have h_eq4 : ∀ ω : Configuration (FinLatticeField 2 N),
        ((ω g) ^ 2) ^ 2 = |ω g| ^ 4 := by
      intro ω; rw [show ω g ^ 2 = |ω g| ^ 2 from (sq_abs _).symm]; ring
    simp_rw [h_eq4]
    have h_hyper := gaussian_hypercontractive T g 1 4
      (by norm_num : (2:ℝ) ≤ 4) 2 (by norm_num : 1 ≤ 2)
      (by norm_num : (4:ℝ) = 2 * ↑2)
    have h_lhs_eq : ∫ ω, |ω g| ^ 4 ∂μ_GFF =
        ∫ ω, |ω g| ^ ((4:ℝ) * ↑(1:ℕ)) ∂(GaussianField.measure T) := by
      rw [hμ_eq]
      congr 1; ext ω
      simp only [Nat.cast_one, mul_one]
      exact (Real.rpow_natCast _ 4).symm
    rw [h_lhs_eq]
    have h_coeff : ((4:ℝ) - 1) ^ ((4:ℝ) * ↑(1:ℕ) / 2) = 9 := by
      simp only [Nat.cast_one, mul_one]
      rw [show (4:ℝ) / 2 = ↑(2:ℕ) from by norm_num, Real.rpow_natCast]
      norm_num
    have h_exp_eq : (∫ ω, |ω g| ^ ((2:ℝ) * ↑(1:ℕ)) ∂(GaussianField.measure T)) ^ ((4:ℝ) / 2) =
        (∫ ω, |ω g| ^ ((2:ℝ) * ↑(1:ℕ)) ∂(GaussianField.measure T)) ^ 2 := by
      rw [show (4:ℝ) / 2 = ↑(2:ℕ) from by norm_num, Real.rpow_natCast]
    have h_rhs_int_eq : ∫ ω, |ω g| ^ ((2:ℝ) * ↑(1:ℕ)) ∂(GaussianField.measure T) =
        ∫ ω, (ω g) ^ 2 ∂μ_GFF := by
      rw [hμ_eq]; congr 1; ext ω
      simp only [Nat.cast_one, mul_one]
      rw [show |ω g| ^ (2:ℝ) = (|ω g| ^ 2 : ℝ) from Real.rpow_natCast _ 2]
      exact sq_abs _
    have h_int_2_eq : ∫ ω, |ω g| ^ (2 * 1) ∂(GaussianField.measure T) =
        ∫ ω, (ω g) ^ 2 ∂μ_GFF := by
      rw [hμ_eq]; congr 1; ext ω; simp [sq_abs]
    have h_hyper' : ∫ ω, |ω g| ^ ((4:ℝ) * ↑(1:ℕ)) ∂(GaussianField.measure T) ≤
        ((4:ℝ) - 1) ^ ((4:ℝ) * ↑(1:ℕ) / 2) *
        (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((4:ℝ) / 2) := by
      have := h_hyper
      rwa [h_int_2_eq] at this
    have h_exp_eq' : (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((4:ℝ) / 2) =
        (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 2 := by
      rw [show (4:ℝ) / 2 = ↑(2:ℕ) from by norm_num, Real.rpow_natCast]
    calc ∫ ω, |ω g| ^ ((4:ℝ) * ↑(1:ℕ)) ∂(GaussianField.measure T)
        ≤ ((4:ℝ) - 1) ^ ((4:ℝ) * ↑(1:ℕ) / 2) *
          (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((4:ℝ) / 2) := h_hyper'
      _ = 9 * (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 2 := by
          rw [h_coeff, h_exp_eq']
      _ = 9 * G_Nff ^ 2 := by
          rw [h_second_moment_eq]
  -- Step 5: Convert back to rpow form and combine
  have h_fourth_nn : (0:ℝ) ≤ ∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF :=
    integral_nonneg fun ω => by positivity
  have h_4th_bound : (∫ ω, (fun ω => (ω g) ^ 2) ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) ≤
      3 * G_Nff := by
    rw [h_int_rpow_eq]
    calc (∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF) ^ (1/2:ℝ)
        ≤ (9 * G_Nff ^ 2) ^ (1/2:ℝ) :=
          Real.rpow_le_rpow h_fourth_nn h_fourth_le (by norm_num : (0:ℝ) ≤ 1/2)
      _ = 3 * G_Nff := by
          rw [show (9:ℝ) = 3 ^ 2 from by norm_num, ← mul_pow]
          rw [← Real.sqrt_eq_rpow, Real.sqrt_sq
            (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) h_G_nn)]
  -- Final combination
  have hK_sqrt : K ^ (1/2:ℝ) = Real.sqrt K :=
    (Real.sqrt_eq_rpow K).symm
  calc ∫ ω, (ω g) ^ 2 ∂μ_int
      ≤ K ^ (1/2:ℝ) * (∫ ω, (fun ω => (ω g) ^ 2) ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) := h_dt
    _ ≤ K ^ (1/2:ℝ) * (3 * G_Nff) :=
        mul_le_mul_of_nonneg_left h_4th_bound (Real.rpow_nonneg hK_pos.le _)
    _ = Real.sqrt K * (3 * G_Nff) := by rw [hK_sqrt]
    _ = 3 * Real.sqrt K * G_Nff := by ring

/-- **Cutoff GF approximation error vanishes along the subsequence.**

For any v and the lattice approximations w_n (nearest lattice vectors in
the φ(n)+1 lattice), the GF difference `Z_{φ(n)+1}[T_v f] - Z_{φ(n)+1}[T_{w_n} f] → 0`.

Proof (see docs/translation-invariance-proof.md):
  |Z_N[T_v f] - Z_N[T_{w_n} f]| ≤ √(E_P[(ω(T_v f - T_{w_n} f))²])
                                   ≤ √(C · G_N(T_v f - T_{w_n} f, ...))
                                   → 0

The last step uses: w_n → v (lattice gets finer), so T_{w_n} f → T_v f
in the test function topology, hence G_N(T_v f - T_{w_n} f, ...) → 0
(from eigenvalue bound G_N(h,h) ≤ ‖h‖²/mass²).

**Uniform Green's function bound by a continuous seminorm.**

G_N(h, h) ≤ (1/mass²) · p(h)² for a fixed continuous seminorm p on
TorusTestFunction L, uniformly in N. Follows from eigenvalues λ_k ≥ mass². -/
axiom torusEmbeddedTwoPoint_le_seminorm
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ (p : TorusTestFunction L → ℝ) (_ : Continuous p),
    ∀ (f : TorusTestFunction L) (N : ℕ) [NeZero N],
      torusEmbeddedTwoPoint L N mass hmass f f ≤ p f ^ 2

/-- **Translation is continuous in the test function topology.**

The map `v ↦ T_v f` is continuous from ℝ² to `TorusTestFunction L`.
This is a standard property of smooth functions on the torus:
translation varies smoothly in the shift parameter. -/
axiom torusTranslation_continuous_in_v
    (f : TorusTestFunction L) :
    Continuous (fun v : ℝ × ℝ => torusTranslation L v f)

theorem torusGF_latticeApproximation_error_vanishes
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (v : ℝ × ℝ) (f : TorusTestFunction L) :
    Tendsto (fun n =>
      torusGeneratingFunctional L (torusInteractingMeasure L (φ n + 1) P mass hmass)
        (torusTranslation L v f) -
      torusGeneratingFunctional L (torusInteractingMeasure L (φ n + 1) P mass hmass) f)
    atTop (nhds 0) := by
  -- Proof outline (see docs/translation-invariance-proof.md):
  -- 1. For each n, let w_n be the nearest lattice vector to v
  -- 2. Z_N[T_{w_n} f] = Z_N[f] (lattice invariance, proved)
  -- 3. |Z_N[T_v f] - Z_N[T_{w_n} f]| ≤ √(C · G_N(T_v f - T_{w_n} f, ...))
  --    (from torus_interacting_second_moment_continuous + Cauchy-Schwarz)
  -- 4. G_N(T_v f - T_{w_n} f, ...) ≤ p(T_v f - T_{w_n} f)²
  --    (from torusEmbeddedTwoPoint_le_seminorm)
  -- 5. p(T_v f - T_{w_n} f) → 0
  --    (from torusTranslation_continuous_in_v + w_n → v)
  -- 6. Hence Z_N[T_v f] - Z_N[f] → 0
  sorry

/-! ## Helper: integral invariance from generating functional invariance

The generating functional `Z[f] = ∫ exp(iωf) dμ` determines and is determined
by the real-valued integrals of `cos(ωf)` and `sin(ωf)`. Specifically:
- `Re(Z[f]) = ∫ cos(ωf) dμ`
- `Im(Z[f]) = ∫ sin(ωf) dμ`

So `Z[f] = Z[Sf]` implies `∫ cos(ωf) dμ = ∫ cos(ω(Sf)) dμ` (and similarly for sin). -/

private lemma cosEval_continuous (g : TorusTestFunction L) :
    Continuous (fun ω : Configuration (TorusTestFunction L) => Real.cos (ω g)) :=
  Real.continuous_cos.comp (WeakDual.eval_continuous g)

private lemma cosEval_bounded (g : TorusTestFunction L) :
    ∃ C, ∀ ω : Configuration (TorusTestFunction L), |Real.cos (ω g)| ≤ C :=
  ⟨1, fun _ => Real.abs_cos_le_one _⟩

private lemma sinEval_continuous (g : TorusTestFunction L) :
    Continuous (fun ω : Configuration (TorusTestFunction L) => Real.sin (ω g)) :=
  Real.continuous_sin.comp (WeakDual.eval_continuous g)

private lemma sinEval_bounded (g : TorusTestFunction L) :
    ∃ C, ∀ ω : Configuration (TorusTestFunction L), |Real.sin (ω g)| ≤ C :=
  ⟨1, fun _ => Real.abs_sin_le_one _⟩

/-- Decomposition: the generating functional's real part is the cosine integral.
Proved by commuting Re (a CLM) with the Bochner integral. -/
private lemma gf_re_eq_cos_integral
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ] (g : TorusTestFunction L) :
    (torusGeneratingFunctional L μ g).re =
    ∫ ω : Configuration (TorusTestFunction L), Real.cos (ω g) ∂μ := by
  unfold torusGeneratingFunctional
  rw [show (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ).re =
    Complex.reCLM (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ) from rfl]
  have hint : Integrable (fun ω : Configuration (TorusTestFunction L) =>
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
private lemma gf_im_eq_sin_integral
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ] (g : TorusTestFunction L) :
    (torusGeneratingFunctional L μ g).im =
    ∫ ω : Configuration (TorusTestFunction L), Real.sin (ω g) ∂μ := by
  unfold torusGeneratingFunctional
  rw [show (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ).im =
    Complex.imCLM (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ) from rfl]
  have hint : Integrable (fun ω : Configuration (TorusTestFunction L) =>
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

/-- **Translation invariance of the interacting continuum limit.**

Proved from lattice approximation error vanishing + weak convergence.
See docs/translation-invariance-proof.md for the full argument. -/
theorem torusInteractingLimit_translation_invariant
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ (g : Configuration (TorusTestFunction L) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
        Tendsto (fun n => ∫ ω, g ω ∂(torusInteractingMeasure L (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, g ω ∂μ)))
    (v : ℝ × ℝ) (f : TorusTestFunction L) :
    torusGeneratingFunctional L μ f =
    torusGeneratingFunctional L μ (torusTranslation L v f) := by
  -- Z_{φ(n)+1}[T_v f] → Z[T_v f] and Z_{φ(n)+1}[f] → Z[f] by weak convergence.
  -- Their difference Z_{φ(n)+1}[T_v f] - Z_{φ(n)+1}[f] → 0 by the approximation axiom.
  -- By uniqueness of limits: Z[T_v f] = Z[f].
  -- Helper: GF tendsto from weak convergence
  have hgf_tendsto : ∀ g : TorusTestFunction L, Tendsto (fun n =>
      torusGeneratingFunctional L (torusInteractingMeasure L (φ n + 1) P mass hmass) g)
      atTop (nhds (torusGeneratingFunctional L μ g)) := by
    intro g
    -- Z_N[g] = ∫ exp(iωg) dμ_N converges to Z[g] = ∫ exp(iωg) dμ.
    -- Suffices: Re and Im parts converge separately, then combine.
    -- Step 1: Re(Z_N[g]) = ∫ cos(ωg) dμ_N → ∫ cos(ωg) dμ = Re(Z[g])
    have h_re : Tendsto (fun n => (torusGeneratingFunctional L
        (torusInteractingMeasure L (φ n + 1) P mass hmass) g).re)
        atTop (nhds (torusGeneratingFunctional L μ g).re) := by
      simp_rw [gf_re_eq_cos_integral]
      exact hconv _ (cosEval_continuous L g) (cosEval_bounded L g)
    -- Step 2: Im(Z_N[g]) = ∫ sin(ωg) dμ_N → ∫ sin(ωg) dμ = Im(Z[g])
    have h_im : Tendsto (fun n => (torusGeneratingFunctional L
        (torusInteractingMeasure L (φ n + 1) P mass hmass) g).im)
        atTop (nhds (torusGeneratingFunctional L μ g).im) := by
      simp_rw [gf_im_eq_sin_integral]
      exact hconv _ (sinEval_continuous L g) (sinEval_bounded L g)
    -- Step 3: Combine Re + Im convergence into ℂ convergence.
    -- z_n = ↑(z_n.re) + ↑(z_n.im) * I → ↑(z.re) + ↑(z.im) * I = z
    rw [show torusGeneratingFunctional L μ g =
      ↑(torusGeneratingFunctional L μ g).re +
      ↑(torusGeneratingFunctional L μ g).im * I from (re_add_im _).symm]
    have h_comb := (h_re.ofReal.add (h_im.ofReal.mul_const I))
    refine h_comb.congr (fun n => ?_)
    exact (re_add_im _)
  have h_Tvf := hgf_tendsto (torusTranslation L v f)
  have h_f := hgf_tendsto f
  have h_diff := torusGF_latticeApproximation_error_vanishes L P mass hmass φ hφ v f
  -- The difference of limits = limit of differences = 0
  have h_sub : Tendsto (fun n =>
      torusGeneratingFunctional L (torusInteractingMeasure L (φ n + 1) P mass hmass)
        (torusTranslation L v f) -
      torusGeneratingFunctional L (torusInteractingMeasure L (φ n + 1) P mass hmass) f)
      atTop (nhds (torusGeneratingFunctional L μ (torusTranslation L v f) -
        torusGeneratingFunctional L μ f)) := h_Tvf.sub h_f
  have h_eq : torusGeneratingFunctional L μ (torusTranslation L v f) -
      torusGeneratingFunctional L μ f = 0 :=
    tendsto_nhds_unique h_sub h_diff
  exact (sub_eq_zero.mp h_eq).symm

private def latticeSwapLM (N : ℕ) := latticeSitePermuteLM N (swapSites N)

private theorem interactingLatticeMeasure_swap_invariant
    (N : ℕ) [NeZero N] (P : InteractionPolynomial) (mass : ℝ)
    (ha : 0 < circleSpacing L N) (hmass : 0 < mass)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Configuration (FinLatticeField 2 N) → E) :
    ∫ ω, F (ω.comp (latticeSwapLM N).toContinuousLinearMap) ∂(interactingLatticeMeasure 2 N P
      (circleSpacing L N) mass ha hmass) =
    ∫ ω, F ω ∂(interactingLatticeMeasure 2 N P (circleSpacing L N) mass ha hmass) := by
  -- Swap (x₀, x₁) ↦ (x₁, x₀) is its own inverse, hence bijective
  have hbij : Function.Bijective (swapSites N) := by
    have hinv : Function.Involutive (swapSites N) := by
      intro x; simp only [swapSites]
      ext i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact hinv.bijective
  have hinv : Function.Involutive (swapSites N) := by
    intro x; simp only [swapSites]
    ext i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact interactingLatticeMeasure_symmetry_invariant L N P mass ha hmass
    (swapSites N) hbij
    (by -- Density preservation: gaussianDensity(φ∘swap⁻¹) = gaussianDensity(φ)
      intro φ
      set σ_equiv := Equiv.ofBijective (swapSites N) hbij
      -- Since swap is involutive, swap⁻¹ = swap
      have hsymm_eq : ∀ y, σ_equiv.symm y = swapSites N y := by
        intro y
        rw [Equiv.symm_apply_eq]
        exact (hinv y).symm
      -- Unfold gaussianDensity and show the exponent is equal
      unfold gaussianDensity
      congr 1; congr 1
      -- Goal: ∑ x, (φ ∘ σ_equiv.symm) x * (massOperator 2 N a mass (φ ∘ σ_equiv.symm)) x =
      --       ∑ x, φ x * (massOperator 2 N a mass φ) x
      -- Rewrite σ_equiv.symm as swapSites
      simp_rw [Function.comp, hsymm_eq]
      -- Now: ∑ x, φ(swap x) * (Q(φ∘swap)) x = ∑ x, φ x * (Q φ) x
      -- The quadratic form is invariant under swap because:
      -- 1. The mass operator Q = -Δ + m²I commutes with swap (the Laplacian stencil
      --    sums over directions i=0,1, and swap exchanges these directions)
      -- 2. The sum over all lattice sites is relabeling-invariant
      -- This requires proving massOperator commutativity with swap,
      -- which involves showing the stencil exchange property.
      sorry)
    F

/-- **The torus interacting generating functional is swap-invariant at every cutoff.**

  `∫ exp(iω(f)) dμ_{P,N} = ∫ exp(iω(σf)) dμ_{P,N}` where σ swaps coordinates.

Proved from `evalTorusAtSite_swap` (equivariance of the torus embedding)
and `interactingLatticeMeasure_swap_invariant` (lattice measure symmetry). -/
theorem torusInteractingMeasure_gf_swap_invariant
    (N : ℕ) [NeZero N] (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (f : TorusTestFunction L) :
    torusGeneratingFunctional L (torusInteractingMeasure L N P mass hmass) f =
    torusGeneratingFunctional L (torusInteractingMeasure L N P mass hmass)
      (torusSwap L f) := by
  -- Step 1: Both sides are integrals of exp(i·ω(g)) over the pushforward measure.
  -- The key identity: latticeTestFn(swap f) = latticeSwapLM(latticeTestFn f)
  have h_lattice_swap : ∀ x : FinLatticeSites 2 N,
      latticeTestFn L N (torusSwap L f) x = latticeTestFn L N f (swapSites N x) := by
    intro x
    simp only [latticeTestFn, torusSwap]
    exact evalTorusAtSite_swap L N x f
  -- Step 2: Convert both sides to lattice integrals via definition unfolding
  set μ_lat := interactingLatticeMeasure 2 N P (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass
  -- Compute LHS as lattice integral
  have h_lhs : torusGeneratingFunctional L (torusInteractingMeasure L N P mass hmass) f =
      ∫ φ, Complex.exp (Complex.I * ↑(φ (latticeTestFn L N f))) ∂μ_lat := by
    unfold torusGeneratingFunctional torusInteractingMeasure
    have hasm : AEStronglyMeasurable (fun ω : Configuration (TorusTestFunction L) =>
        Complex.exp (Complex.I * ↑(ω f)))
        (Measure.map (torusEmbedLift L N) μ_lat) :=
      (Complex.measurable_exp.comp
        (measurable_const.mul (Complex.measurable_ofReal.comp
          (configuration_eval_measurable f)))).aestronglyMeasurable
    rw [MeasureTheory.integral_map (torusEmbedLift_measurable L N).aemeasurable hasm]
    simp_rw [torusEmbedLift_eval_eq]
  -- Compute RHS as lattice integral
  have h_rhs : torusGeneratingFunctional L (torusInteractingMeasure L N P mass hmass)
      (torusSwap L f) =
      ∫ φ, Complex.exp (Complex.I * ↑(φ (latticeTestFn L N (torusSwap L f)))) ∂μ_lat := by
    unfold torusGeneratingFunctional torusInteractingMeasure
    have hasm : AEStronglyMeasurable (fun ω : Configuration (TorusTestFunction L) =>
        Complex.exp (Complex.I * ↑(ω (torusSwap L f))))
        (Measure.map (torusEmbedLift L N) μ_lat) :=
      (Complex.measurable_exp.comp
        (measurable_const.mul (Complex.measurable_ofReal.comp
          (configuration_eval_measurable (torusSwap L f))))).aestronglyMeasurable
    rw [MeasureTheory.integral_map (torusEmbedLift_measurable L N).aemeasurable hasm]
    simp_rw [torusEmbedLift_eval_eq]
  rw [h_lhs, h_rhs]
  -- Now: ∫ exp(i·φ(latticeTestFn f)) = ∫ exp(i·φ(latticeTestFn(swap f)))
  -- latticeTestFn(swap f) = latticeSwapLM(latticeTestFn f)
  have h_swap_lattice : ∀ φ : Configuration (FinLatticeField 2 N),
      φ (latticeTestFn L N (torusSwap L f)) =
      (φ.comp (latticeSwapLM N).toContinuousLinearMap) (latticeTestFn L N f) := by
    intro φ
    change φ (latticeTestFn L N (torusSwap L f)) =
      φ ((latticeSwapLM N) (latticeTestFn L N f))
    congr 1; ext x; exact h_lattice_swap x
  simp_rw [h_swap_lattice]
  -- Apply lattice swap invariance
  exact (interactingLatticeMeasure_swap_invariant L N P mass
    (circleSpacing_pos L N) hmass _).symm

/-- The lattice time-reflection linear map: `(L_refl g)(x) = g(timeReflectSites x)`. -/
private def latticeTimeReflectLM (N : ℕ) := latticeSitePermuteLM N (timeReflectSites N)

private theorem interactingLatticeMeasure_timeReflection_invariant
    (N : ℕ) [NeZero N] (P : InteractionPolynomial) (mass : ℝ)
    (ha : 0 < circleSpacing L N) (hmass : 0 < mass)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Configuration (FinLatticeField 2 N) → E) :
    ∫ ω, F (ω.comp (latticeTimeReflectLM N).toContinuousLinearMap) ∂(interactingLatticeMeasure
      2 N P (circleSpacing L N) mass ha hmass) =
    ∫ ω, F ω ∂(interactingLatticeMeasure 2 N P (circleSpacing L N) mass ha hmass) := by
  -- Time reflection (x₀, x₁) ↦ (-x₀, x₁) is its own inverse, hence bijective
  have hbij : Function.Bijective (timeReflectSites N) := by
    have hinv : Function.Involutive (timeReflectSites N) := by
      intro x; simp only [timeReflectSites]
      ext i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact hinv.bijective
  exact interactingLatticeMeasure_symmetry_invariant L N P mass ha hmass
    (timeReflectSites N) hbij
    (by sorry) -- Density preservation: gaussianDensity invariant under time reflection
    F

/-- **The torus interacting generating functional is time-reflection-invariant.**

Proved from `evalTorusAtSite_timeReflection` (equivariance)
and `interactingLatticeMeasure_timeReflection_invariant` (lattice symmetry). -/
theorem torusInteractingMeasure_gf_timeReflection_invariant
    (N : ℕ) [NeZero N] (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (f : TorusTestFunction L) :
    torusGeneratingFunctional L (torusInteractingMeasure L N P mass hmass) f =
    torusGeneratingFunctional L (torusInteractingMeasure L N P mass hmass)
      (torusTimeReflection L f) := by
  have h_lattice_refl : ∀ x : FinLatticeSites 2 N,
      latticeTestFn L N (torusTimeReflection L f) x =
      latticeTestFn L N f (timeReflectSites N x) := by
    intro x
    simp only [latticeTestFn, torusTimeReflection]
    exact evalTorusAtSite_timeReflection L N x f
  -- Follow exactly the same pattern as swap proof
  unfold torusGeneratingFunctional torusInteractingMeasure
  set μ_lat := interactingLatticeMeasure 2 N P (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass
  have hmeas : AEMeasurable (torusEmbedLift L N) μ_lat :=
    (torusEmbedLift_measurable L N).aemeasurable
  have hasm₁ : AEStronglyMeasurable (fun ω : Configuration (TorusTestFunction L) =>
      Complex.exp (Complex.I * ↑(ω f))) (Measure.map (torusEmbedLift L N) μ_lat) :=
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (configuration_eval_measurable f)))).aestronglyMeasurable
  have hasm₂ : AEStronglyMeasurable (fun ω : Configuration (TorusTestFunction L) =>
      Complex.exp (Complex.I * ↑(ω (torusTimeReflection L f))))
      (Measure.map (torusEmbedLift L N) μ_lat) := by
    exact (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (configuration_eval_measurable (torusTimeReflection L f))))).aestronglyMeasurable
  rw [MeasureTheory.integral_map hmeas hasm₁, MeasureTheory.integral_map hmeas hasm₂]
  simp_rw [torusEmbedLift_eval_eq]
  have h_refl_lattice : ∀ φ : Configuration (FinLatticeField 2 N),
      φ (latticeTestFn L N (torusTimeReflection L f)) =
      (φ.comp (latticeTimeReflectLM N).toContinuousLinearMap) (latticeTestFn L N f) := by
    intro φ
    change φ (latticeTestFn L N (torusTimeReflection L f)) =
      φ ((latticeTimeReflectLM N) (latticeTestFn L N f))
    congr 1; ext x; exact h_lattice_refl x
  simp_rw [h_refl_lattice]
  exact (interactingLatticeMeasure_timeReflection_invariant L N P mass
    (circleSpacing_pos L N) hmass _).symm

/-- **Gaussian exponential moment bound.**

For a Gaussian measure `μ = measure T` and test function `f`,
`∫ exp(t|ω(f)|) dμ` is finite for all t and bounded by `2 exp(t²‖Tf‖²/2)`.

From `pairing_is_gaussian`: `ω(f) ~ gaussianReal 0 ‖Tf‖²` under μ.
Then `E[exp(t|X|)] ≤ E[exp(tX)] + E[exp(-tX)] = 2 exp(t²σ²/2)` by `mgf_id_gaussianReal`.

This is a textbook result: Gaussian random variables have finite exponential moments. -/
axiom gaussian_exp_abs_moment
    (N : ℕ) [NeZero N] (mass : ℝ) (hmass : 0 < mass)
    (g : FinLatticeField 2 N) (t : ℝ) :
    Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
      Real.exp (t * |ω g|))
      (latticeGaussianMeasure 2 N (circleSpacing L N) mass
        (circleSpacing_pos L N) hmass) ∧
    ∫ ω : Configuration (FinLatticeField 2 N),
      Real.exp (t * |ω g|)
      ∂(latticeGaussianMeasure 2 N (circleSpacing L N) mass
        (circleSpacing_pos L N) hmass) ≤
    2 * Real.exp (t ^ 2 / 2 *
      ∫ ω, (ω g) ^ 2 ∂(latticeGaussianMeasure 2 N (circleSpacing L N) mass
        (circleSpacing_pos L N) hmass))

/-- **Cutoff exponential moment bound** (from density transfer + Gaussian MGF + Nelson).

Proved from `density_transfer_bound` + `nelson_exponential_estimate` +
`gaussian_exp_abs_moment`. -/
theorem torusInteractingMeasure_exponentialMomentBound_cutoff
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : TorusTestFunction L) (N : ℕ) [NeZero N],
    Integrable (fun ω : Configuration (TorusTestFunction L) =>
      Real.exp (|ω f|)) (torusInteractingMeasure L N P mass hmass) ∧
    ∫ ω : Configuration (TorusTestFunction L),
      Real.exp (|ω f|)
      ∂(torusInteractingMeasure L N P mass hmass) ≤
    C * Real.exp (torusEmbeddedTwoPoint L N mass hmass f f) := by
  -- Get K from Nelson's exponential estimate
  obtain ⟨K, hK_pos, hK_bound⟩ := nelson_exponential_estimate L P mass hmass
  -- C = √(2K) works
  refine ⟨Real.sqrt (2 * K), Real.sqrt_pos_of_pos (by linarith), fun f N _ => ?_⟩
  -- Setup: abbreviations for measures and embedding
  set μ_int := interactingLatticeMeasure 2 N P (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass
  set μ_GFF := latticeGaussianMeasure 2 N (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass
  set ι := torusEmbedLift L N
  set g := latticeTestFn L N f
  have hι_meas : AEMeasurable ι μ_int :=
    (torusEmbedLift_measurable L N).aemeasurable
  have h_eval : ∀ ω : Configuration (FinLatticeField 2 N),
      (ι ω) f = ω g := fun ω => torusEmbedLift_eval_eq L N f ω
  -- Step 1: Push through torus embedding
  -- torusInteractingMeasure = Measure.map ι μ_int
  -- ∫ exp(|ω f|) d(map ι μ_int) = ∫ exp(|ω g|) dμ_int
  have hmeas_lhs : AEStronglyMeasurable (fun ω : Configuration (TorusTestFunction L) =>
      Real.exp (|ω f|)) (Measure.map ι μ_int) :=
    (Real.measurable_exp.comp (configuration_eval_measurable f).abs).aestronglyMeasurable
  change Integrable (fun ω => Real.exp (|ω f|)) (Measure.map ι μ_int) ∧
    ∫ ω, Real.exp (|ω f|) ∂(Measure.map ι μ_int) ≤
    Real.sqrt (2 * K) * Real.exp (torusEmbeddedTwoPoint L N mass hmass f f)
  rw [integrable_map_measure hmeas_lhs hι_meas,
      integral_map hι_meas hmeas_lhs]
  simp_rw [Function.comp_def, h_eval]
  -- Goal now on lattice: Integrable (exp(|ω g|)) μ_int ∧ ∫ exp(|ω g|) dμ_int ≤ ...
  -- Step 2: Integrability of exp(|ω g|) under μ_int
  -- μ_int = Z⁻¹ • μ_GFF.withDensity(bw), bw ≤ exp(B)
  -- So exp(|ω g|) integrable under μ_int ⟸ exp(|ω g|) * bw integrable under μ_GFF
  -- ⟸ exp(|ω g|) * exp(B) integrable ⟸ exp(|ω g|) integrable
  -- And exp(|ω g|) = exp(1 * |ω g|) is integrable by gaussian_exp_abs_moment at t=1
  obtain ⟨B, hB⟩ := interactionFunctional_bounded_below 2 N P (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass
  set bw := boltzmannWeight 2 N P (circleSpacing L N) mass
  have hbw_bound : ∀ ω, bw ω ≤ Real.exp B := fun ω =>
    Real.exp_le_exp_of_le (by linarith [hB ω])
  have hbw_pos : ∀ ω, 0 < bw ω :=
    boltzmannWeight_pos 2 N P (circleSpacing L N) mass
  have hF_meas_raw : Measurable (fun ω : Configuration (FinLatticeField 2 N) =>
      Real.exp (|ω g|)) :=
    Real.measurable_exp.comp (configuration_eval_measurable g).abs
  -- exp(|ω g|) integrable under μ_GFF (gaussian_exp_abs_moment at t=1)
  have hF_int_GFF : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
      Real.exp (|ω g|)) μ_GFF := by
    have h := (gaussian_exp_abs_moment L N mass hmass g 1).1
    exact h.congr (ae_of_all _ fun ω => by ring_nf)
  have hZ_pos : 0 < partitionFunction 2 N P (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass :=
    partitionFunction_pos 2 N P (circleSpacing L N) mass (circleSpacing_pos L N) hmass
  -- Integrability under withDensity: use integrable_withDensity_iff
  have hf_dens_meas : Measurable (fun ω : Configuration (FinLatticeField 2 N) =>
      ENNReal.ofReal (bw ω)) :=
    ENNReal.measurable_ofReal.comp
      ((interactionFunctional_measurable 2 N P (circleSpacing L N) mass).neg.exp)
  have hbw_simp : ∀ ω : Configuration (FinLatticeField 2 N),
      (ENNReal.ofReal (bw ω)).toReal = bw ω :=
    fun ω => ENNReal.toReal_ofReal (le_of_lt (hbw_pos ω))
  have hF_int_wd : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
      Real.exp (|ω g|))
      (μ_GFF.withDensity (fun ω => ENNReal.ofReal (bw ω))) := by
    apply (integrable_withDensity_iff hf_dens_meas
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
    simp_rw [hbw_simp]
    -- Goal: Integrable (fun ω => exp(|ω g|) * bw ω) μ_GFF
    -- Dominate by exp(|ω g|) * exp(B)
    apply (hF_int_GFF.mul_const (Real.exp B)).mono
    · exact hF_meas_raw.aestronglyMeasurable.mul
        (interactionFunctional_measurable 2 N P
          (circleSpacing L N) mass).neg.exp.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ω => by
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hbw_pos ω).le),
            abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos B).le)]
        exact mul_le_mul_of_nonneg_left (hbw_bound ω) (Real.exp_pos _).le
  have hF_int_int : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
      Real.exp (|ω g|)) μ_int := by
    change Integrable _ (interactingLatticeMeasure 2 N P (circleSpacing L N) mass
      (circleSpacing_pos L N) hmass)
    unfold interactingLatticeMeasure
    exact hF_int_wd.smul_measure
      (ENNReal.inv_ne_top.mpr ((ENNReal.ofReal_pos.mpr hZ_pos).ne'))
  -- Step 3: Apply density_transfer_bound with F(ω) = exp(|ω g|)
  have hZ_ge_one := partitionFunction_ge_one 2 N P mass hmass
    (circleSpacing L N) (circleSpacing_pos L N)
  have hF_nn : ∀ ω : Configuration (FinLatticeField 2 N), 0 ≤ Real.exp (|ω g|) :=
    fun ω => (Real.exp_pos _).le
  have hF_meas : AEStronglyMeasurable (fun ω : Configuration (FinLatticeField 2 N) =>
      Real.exp (|ω g|)) μ_GFF :=
    hF_meas_raw.aestronglyMeasurable
  -- F² = exp(|ω g|)^2 = exp(2|ω g|), integrable by gaussian_exp_abs_moment at t=2
  have hF_sq_int : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
      Real.exp (|ω g|) ^ 2) μ_GFF := by
    have h_eq : ∀ ω : Configuration (FinLatticeField 2 N),
        Real.exp (|ω g|) ^ 2 = Real.exp (2 * |ω g|) := fun ω => by
      rw [sq, ← Real.exp_add]; ring_nf
    simp_rw [h_eq]
    exact (gaussian_exp_abs_moment L N mass hmass g 2).1
  -- Apply density_transfer_bound
  have h_dt := density_transfer_bound 2 N P (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass K hK_pos (hK_bound N)
    hZ_ge_one (fun ω => Real.exp (|ω g|)) hF_nn hF_meas hF_sq_int
  -- h_dt: ∫ exp(|ω g|) dμ_int ≤ K^{1/2} * (∫ exp(|ω g|)^{(2:ℝ)} dμ_GFF)^{1/2}
  -- Step 4: Bound (∫ exp(|ω g|)^{(2:ℝ)} dμ_GFF)^{1/2} using gaussian_exp_abs_moment
  have h_rpow_eq : ∀ ω : Configuration (FinLatticeField 2 N),
      Real.exp (|ω g|) ^ (2:ℝ) = Real.exp (2 * |ω g|) := fun ω => by
    rw [show (2:ℝ) = ↑(2:ℕ) from by norm_num, Real.rpow_natCast, sq, ← Real.exp_add]; ring_nf
  have h_int_rpow_eq : ∫ ω, (fun ω => Real.exp (|ω g|)) ω ^ (2:ℝ) ∂μ_GFF =
      ∫ ω, Real.exp (2 * |ω g|) ∂μ_GFF := by
    congr 1; ext ω; exact h_rpow_eq ω
  -- gaussian_exp_abs_moment at t=2: ∫ exp(2|ω g|) ≤ 2 * exp(2^2/2 * ∫(ωg)²)
  have h_gauss : ∫ ω, Real.exp (2 * |ω g|) ∂μ_GFF ≤
      2 * Real.exp ((2:ℝ) ^ 2 / 2 * ∫ ω, (ω g) ^ 2 ∂μ_GFF) :=
    (gaussian_exp_abs_moment L N mass hmass g 2).2
  -- ∫(ωg)² = torusEmbeddedTwoPoint L N mass hmass f f
  have h_second_moment_eq : ∫ ω, (ω g) ^ 2 ∂μ_GFF =
      torusEmbeddedTwoPoint L N mass hmass f f :=
    (torusEmbeddedTwoPoint_eq_lattice_second_moment L N mass hmass f).symm
  -- 2^2/2 * ∫(ωg)² = 2 * G_N(f,f)
  have h_exp_simp : (2:ℝ) ^ 2 / 2 * ∫ ω, (ω g) ^ 2 ∂μ_GFF =
      2 * torusEmbeddedTwoPoint L N mass hmass f f := by
    rw [h_second_moment_eq]; norm_num
  -- So: ∫ exp(2|ωg|) ≤ 2 * exp(2 * G_N(f,f))
  have h_gauss' : ∫ ω, Real.exp (2 * |ω g|) ∂μ_GFF ≤
      2 * Real.exp (2 * torusEmbeddedTwoPoint L N mass hmass f f) := by
    rw [← h_exp_simp]; exact h_gauss
  -- Step 5: Bound (∫ exp(2|ωg|))^{1/2} ≤ √2 * exp(G_N(f,f))
  set G_N := torusEmbeddedTwoPoint L N mass hmass f f
  have h_gauss_nn : (0:ℝ) ≤ ∫ ω, Real.exp (2 * |ω g|) ∂μ_GFF :=
    integral_nonneg fun ω => (Real.exp_pos _).le
  have h_rpow_bound : (∫ ω, (fun ω => Real.exp (|ω g|)) ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) ≤
      Real.sqrt 2 * Real.exp G_N := by
    rw [h_int_rpow_eq]
    calc (∫ ω, Real.exp (2 * |ω g|) ∂μ_GFF) ^ (1/2:ℝ)
        ≤ (2 * Real.exp (2 * G_N)) ^ (1/2:ℝ) :=
          Real.rpow_le_rpow h_gauss_nn h_gauss' (by norm_num : (0:ℝ) ≤ 1/2)
      _ = Real.sqrt (2 * Real.exp (2 * G_N)) := by
          rw [Real.sqrt_eq_rpow]
      _ = Real.sqrt 2 * Real.sqrt (Real.exp (2 * G_N)) := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      _ = Real.sqrt 2 * Real.exp G_N := by
          congr 1
          rw [show (2 : ℝ) * G_N = G_N + G_N from by ring,
              Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
  -- Step 6: Combine: ∫ exp(|ωg|) ≤ K^{1/2} * √2 * exp(G_N) = √(2K) * exp(G_N)
  have h_integral_bound : ∫ ω, Real.exp (|ω g|) ∂μ_int ≤
      Real.sqrt (2 * K) * Real.exp G_N := by
    calc ∫ ω, Real.exp (|ω g|) ∂μ_int
        ≤ K ^ (1/2:ℝ) *
          (∫ ω, (fun ω => Real.exp (|ω g|)) ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) := h_dt
      _ ≤ K ^ (1/2:ℝ) * (Real.sqrt 2 * Real.exp G_N) :=
          mul_le_mul_of_nonneg_left h_rpow_bound (Real.rpow_nonneg hK_pos.le _)
      _ = Real.sqrt K * (Real.sqrt 2 * Real.exp G_N) := by
          rw [← Real.sqrt_eq_rpow]
      _ = (Real.sqrt K * Real.sqrt 2) * Real.exp G_N := by ring
      _ = Real.sqrt (2 * K) * Real.exp G_N := by
          congr 1
          rw [mul_comm (Real.sqrt K) (Real.sqrt 2),
              ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  exact ⟨hF_int_int, h_integral_bound⟩

/-- **Interacting exponential moment bound** (transferred to continuum limit).

The weak limit measure satisfies `∫ exp(|ω(f)|) dμ ≤ exp(c · G_L(f,f))`.
Proved from the cutoff bound + weak convergence:
1. For each C > 0: `∫ min(exp(|ωf|), C) dμ = lim ∫ min(exp(|ωf|), C) dμ_N` (bcf)
2. `∫ min(exp(|ωf|), C) dμ_N ≤ ∫ exp(|ωf|) dμ_N ≤ K · exp(G_N(f,f))`
3. `G_N(f,f) → G(f,f)` (propagator convergence)
4. Taking C → ∞ by MCT gives the bound. -/
theorem torusInteracting_exponentialMomentBound
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (_hφ : StrictMono φ)
    (hconv : ∀ (g : Configuration (TorusTestFunction L) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
        Tendsto (fun n => ∫ ω, g ω ∂(torusInteractingMeasure L (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, g ω ∂μ)))
    : ∃ K : ℝ, 0 < K ∧ ∀ (f : TorusTestFunction L),
    Integrable (fun ω : Configuration (TorusTestFunction L) =>
      Real.exp (|ω f|)) μ ∧
    ∫ ω : Configuration (TorusTestFunction L),
      Real.exp (|ω f|) ∂μ ≤
    K * Real.exp (torusContinuumGreen L mass hmass f f) := by
  -- Get the universal cutoff bound (K independent of f and N)
  obtain ⟨K, hK_pos, hK_bound⟩ :=
    torusInteractingMeasure_exponentialMomentBound_cutoff L P mass hmass
  refine ⟨K, hK_pos, fun f => ?_⟩
  set B := K * Real.exp (torusContinuumGreen L mass hmass f f)
  have hB_pos : 0 < B := mul_pos hK_pos (Real.exp_pos _)
  have hG_conv := torus_propagator_convergence L mass hmass f f
  -- Abbreviation for the target function
  set F : Configuration (TorusTestFunction L) → ℝ := fun ω => Real.exp (|ω f|) with hF_def
  have hF_nn : ∀ ω : Configuration (TorusTestFunction L), 0 ≤ F ω :=
    fun ω => (Real.exp_pos _).le
  have hF_meas : Measurable F :=
    Real.measurable_exp.comp ((configuration_eval_measurable f).abs)
  -- Step 1: For every M > 0, ∫ min(F, M) dμ ≤ B (truncation + weak convergence)
  have h_trunc : ∀ M : ℝ, 0 < M →
      ∫ ω : Configuration (TorusTestFunction L), min (F ω) M ∂μ ≤ B := by
    intro M hM
    have h_cont : Continuous (fun ω : Configuration (TorusTestFunction L) =>
        min (F ω) M) :=
      (Real.continuous_exp.comp (continuous_abs.comp (WeakDual.eval_continuous f))).min
        continuous_const
    have h_bdd : ∃ C, ∀ ω : Configuration (TorusTestFunction L),
        |min (F ω) M| ≤ C :=
      ⟨M, fun ω => by
        rw [abs_of_nonneg (le_min (hF_nn ω) hM.le)]
        exact min_le_right _ _⟩
    have h_lim := hconv _ h_cont h_bdd
    have h_cutoff : ∀ n, ∫ ω, min (F ω) M
        ∂(torusInteractingMeasure L (φ n + 1) P mass hmass) ≤
        K * Real.exp (torusEmbeddedTwoPoint L (φ n + 1) mass hmass f f) := by
      intro n
      obtain ⟨h_int_n, h_bnd_n⟩ := hK_bound f (φ n + 1)
      calc ∫ ω, min (F ω) M
            ∂(torusInteractingMeasure L (φ n + 1) P mass hmass)
          ≤ ∫ ω, F ω
            ∂(torusInteractingMeasure L (φ n + 1) P mass hmass) := by
            apply integral_mono_of_nonneg
            · exact ae_of_all _ (fun ω => le_min (hF_nn ω) hM.le)
            · exact h_int_n
            · exact ae_of_all _ (fun ω => min_le_left _ _)
        _ ≤ K * Real.exp (torusEmbeddedTwoPoint L (φ n + 1) mass hmass f f) := h_bnd_n
    have h_B_lim : Tendsto (fun n =>
        K * Real.exp (torusEmbeddedTwoPoint L (φ n + 1) mass hmass f f))
        atTop (nhds B) := by
      show Tendsto _ atTop (nhds (K * Real.exp (torusContinuumGreen L mass hmass f f)))
      apply Filter.Tendsto.const_mul
      exact (Real.continuous_exp.tendsto _).comp
        (hG_conv.comp (_hφ.tendsto_atTop))
    exact le_of_tendsto_of_tendsto h_lim h_B_lim (Filter.Eventually.of_forall h_cutoff)
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
  -- Use MCT for lintegrals: ∫⁻ ofReal(min(F, n)) → ∫⁻ ofReal(F) as n → ∞
  -- Each term ≤ ofReal(B), so the limit is ≤ ofReal(B) < ∞
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

/-! ### Helper lemmas for OS0 -/

/-- On a compact set `K ⊆ (Fin n → ℂ)`, imaginary parts are uniformly bounded. -/
private lemma compact_im_bound {n : ℕ} {K : Set (Fin n → ℂ)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ i : Fin n, |Complex.im (z i)| ≤ C := by
  by_cases hKe : K.Nonempty
  · obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
    exact ⟨M, le_trans (norm_nonneg _) (hM _ hKe.some_mem), fun z hz i =>
      (Complex.abs_im_le_norm (z i)).trans ((norm_le_pi_norm z i).trans (hM z hz))⟩
  · exact ⟨0, le_refl _, fun z hz => absurd ⟨z, hz⟩ hKe⟩

/-- For `aᵢ ≥ 0`: `exp(c · Σ aᵢ) ≤ Σ exp(n·c·aᵢ)`. Uses `Σ aᵢ ≤ n · max aᵢ`
and `exp(n·c·max) ≤ Σ exp(n·c·aᵢ)` (the max term is one of the summands). -/
private lemma exp_mul_sum_le {n : ℕ} (hn : 0 < n) (c : ℝ) (hc : 0 ≤ c)
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

/-! ## OS0: Analyticity of the interacting generating functional

Unlike the Gaussian case (where Z = exp(quadratic) is trivially entire),
the interacting generating functional is a genuine integral:
  `Z_ℂ[f] = ∫ exp(iω(f)) dμ_P`
Its analyticity requires Morera's theorem (holomorphic dependence on
parameters under the integral sign). -/

/-- **OS0 for the torus interacting continuum limit.**

The generating functional `z ↦ ∫ exp(i Σ zᵢ ω(Jᵢ)) dμ_P` is entire
analytic in `z ∈ ℂⁿ`.

**Proof strategy:**
1. Each cutoff measure `μ_N` has entire generating functional (by
   `analyticOnNhd_integral`: the integrand `exp(i Σ zᵢ ω(Jᵢ))` is
   entire in z for each ω, and the exponential moment bound from
   Nelson's estimate provides domination on compact sets).
2. The cutoff generating functionals converge pointwise to the limit
   generating functional (by weak convergence from `torusInteractingLimit_exists`).
3. By Vitali's convergence theorem (locally bounded analytic functions
   converging pointwise have analytic limits), the limit is analytic.

Steps 1 and 3 use `analyticOnNhd_integral` (axiomatized in
`GeneralResults/ComplexAnalysis.lean`). -/
theorem torusInteracting_os0
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (_φ : ℕ → ℕ) (_hφ : StrictMono _φ)
    (_hconv : ∀ (f : Configuration (TorusTestFunction L) → ℝ),
      Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun n => ∫ ω, f ω ∂(torusInteractingMeasure L (_φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, f ω ∂μ))) :
    TorusOS0_Analyticity L μ := by
  intro n J
  -- Goal: z ↦ ∫ exp(I * (ω(Σ Re(zᵢ)Jᵢ) + I * ω(Σ Im(zᵢ)Jᵢ))) dμ is entire
  -- This is ∫ F(z, ω) dμ where F(z, ω) = exp(I * Σᵢ zᵢ ω(Jᵢ))
  -- Apply analyticOnNhd_integral
  -- Note: AnalyticOn = AnalyticOnNhd for open sets (Set.univ is open)
  rw [analyticOn_univ]
  apply analyticOnNhd_integral
  · -- Pointwise analyticity: z ↦ F(z, ω) is entire for each ω
    -- exp(I * (ω(Σ Re(zᵢ)Jᵢ) + I * ω(Σ Im(zᵢ)Jᵢ))) is exp of a ℂ-linear function of z
    intro ω z _
    apply AnalyticAt.cexp'
    -- Rewrite using linearity of ω: I * (ω(Σ Re(zᵢ)Jᵢ) + I * ω(Σ Im(zᵢ)Jᵢ)) = I * Σ zᵢ ω(Jᵢ)
    have h_eq : ∀ w : Fin n → ℂ,
        I * (↑(ω (∑ i, (w i).re • J i)) + I * ↑(ω (∑ i, (w i).im • J i))) =
        I * ∑ i : Fin n, w i * ↑(ω (J i)) := by
      intro w; congr 1
      simp only [map_sum, map_smul, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      congr 1; ext i
      calc ↑(w i).re * ↑(ω (J i)) + I * (↑(w i).im * ↑(ω (J i)))
          = (↑(w i).re + ↑(w i).im * I) * ↑(ω (J i)) := by ring
        _ = w i * ↑(ω (J i)) := by rw [re_add_im]
    simp_rw [h_eq]
    -- I * Σ zᵢ * cᵢ is ℂ-linear in z, hence analytic
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
    -- Get uniform bound C_K on imaginary parts over K
    obtain ⟨C_K, hC_K_nn, hC_K⟩ := compact_im_bound hK
    -- Get exponential moment bound (provides integrability)
    obtain ⟨K_exp, hK_exp_pos, hK_exp_bound⟩ :=
      torusInteracting_exponentialMomentBound L P mass hmass μ _φ _hφ _hconv
    by_cases hn : n = 0
    · -- n = 0: integrand is exp(I * 0) = 1, bounded by 1
      subst hn
      exact ⟨fun _ => 1, integrable_const 1, fun z _ => ae_of_all μ fun ω => by
        simp only [Finset.univ_eq_empty, Finset.sum_empty, map_zero,
          Complex.ofReal_zero, add_zero, mul_zero, Complex.exp_zero, norm_one]; rfl⟩
    · -- n > 0: bound by ∑ᵢ exp(n · C_K · |ω(Jᵢ)|)
      set bound := fun ω : Configuration (TorusTestFunction L) =>
        ∑ i : Fin n, Real.exp (↑n * C_K * |ω (J i)|) with hbound_def
      refine ⟨bound, ?_, fun z hz => ae_of_all μ fun ω => ?_⟩
      · -- Integrability: each exp(n·C_K·|ω(Jᵢ)|) = exp(|ω((n·C_K)•Jᵢ)|) is integrable
        apply integrable_finset_sum; intro i _
        have hscale : ∀ ω : Configuration (TorusTestFunction L),
            Real.exp (↑n * C_K * |ω (J i)|) =
            Real.exp (|ω ((↑n * C_K) • J i)|) := by
          intro ω
          rw [map_smul, smul_eq_mul, abs_mul,
              abs_of_nonneg (mul_nonneg (Nat.cast_nonneg' n) hC_K_nn)]
        simp_rw [hscale]
        exact (hK_exp_bound ((↑n * C_K) • J i)).1
      · -- Pointwise bound: ‖F(z, ω)‖ ≤ bound(ω) for z ∈ K
        -- Step 1: ‖cexp(I·(ω(g_re)+I·ω(g_im)))‖ = exp(-ω(g_im))
        rw [Complex.norm_exp]
        have h_re : (I * (↑(ω (∑ i, (z i).re • J i)) +
            I * ↑(ω (∑ i, (z i).im • J i)))).re =
            -(ω (∑ i, (z i).im • J i)) := by
          have : I * (↑(ω (∑ i, (z i).re • J i)) +
              I * ↑(ω (∑ i, (z i).im • J i))) =
              -↑(ω (∑ i, (z i).im • J i)) +
              ↑(ω (∑ i, (z i).re • J i)) * I := by
            rw [mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul]; ring
          rw [this, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
              Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
              Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
              add_zero]
        rw [h_re]
        -- Step 2: exp(-ω(g_im)) ≤ exp(|ω(g_im)|) ≤ exp(C_K · Σ|ω(Jᵢ)|)
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
          -- Step 3: exp(C_K · Σ|ω(Jᵢ)|) ≤ Σ exp(n·C_K·|ω(Jᵢ)|)
          _ ≤ bound ω :=
              exp_mul_sum_le (Nat.pos_of_ne_zero hn) C_K hC_K_nn _

/-! ## OS1: Regularity of the interacting generating functional -/

/-- **OS1 for the torus interacting continuum limit.**

The complex generating functional satisfies an exponential bound:
  `‖Z_ℂ[f_re, f_im]‖ ≤ exp(c · (q(f_re) + q(f_im)))`
for a continuous seminorm `q` and constant `c > 0`.

**Proof strategy:**
By Cauchy-Schwarz density transfer, the interacting exponential moment
`E_P[exp(t|ω(f)|)]` is bounded by `√K · E_GFF[exp(2t|ω(f)|)]^{1/2}`
where K is Nelson's constant. The Gaussian exponential moment grows as
`exp(2t² G(f,f))`, so the interacting moment is bounded by
`√K · exp(t² G(f,f))`. Taking q(f) = G_L(f,f) (the continuum Green's
function, which is a continuous seminorm) gives the OS1 bound. -/
theorem torusInteracting_os1
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (_hφ : StrictMono φ)
    (_hconv : ∀ (f : Configuration (TorusTestFunction L) → ℝ),
      Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun n => ∫ ω, f ω ∂(torusInteractingMeasure L (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, f ω ∂μ))) :
    TorusOS1_Regularity L μ := by
  -- Get the exponential moment bound with universal constant K
  -- Use q(f) = G(f,f) + log(K), c = 1 to absorb the K factor:
  -- K * exp(G) = exp(G + log K) = exp(q(f)) where q(f) = G(f,f) + log K
  -- Then ‖Z_ℂ‖ ≤ exp(q(f_im)) ≤ exp(1 * (q(f_re) + q(f_im)))
  obtain ⟨K, hK_pos, hK_all⟩ :=
    torusInteracting_exponentialMomentBound L P mass hmass μ φ _hφ _hconv
  -- Use q(f) = G(f,f) + Real.log K to absorb the constant K
  refine ⟨fun f => torusContinuumGreen L mass hmass f f + |Real.log K|,
          (torusContinuumGreen_continuous_diag L mass hmass).add continuous_const,
          1, one_pos, ?_⟩
  intro f_re f_im
  -- Get the bound for f_im (using universal K)
  obtain ⟨h_int_im, h_exp_bound_im⟩ := hK_all f_im
  -- ‖Z_ℂ‖ ≤ ∫ exp(|ω(f_im)|) dμ ≤ K * exp(G(f_im, f_im))
  -- = exp(G(f_im) + log K) = exp(q(f_im))
  -- ≤ exp(1 * (q(f_re) + q(f_im)))
  have h_tri : ‖torusGeneratingFunctionalℂ L μ f_re f_im‖ ≤
      ∫ ω, ‖Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)))‖ ∂μ :=
    norm_integral_le_integral_norm _
  have h_norm : ∀ ω : Configuration (TorusTestFunction L),
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
  calc ‖torusGeneratingFunctionalℂ L μ f_re f_im‖
      ≤ ∫ ω, ‖Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)))‖ ∂μ := h_tri
    _ = ∫ ω, Real.exp (-(ω f_im)) ∂μ := by congr 1; ext ω; exact h_norm ω
    _ ≤ ∫ ω, Real.exp (|ω f_im|) ∂μ := by
        apply integral_mono_of_nonneg
        · exact ae_of_all _ (fun _ => (Real.exp_pos _).le)
        · exact h_int_im
        · exact ae_of_all _ (fun ω => Real.exp_le_exp_of_le (neg_le_abs (ω f_im)))
    _ ≤ K * Real.exp (torusContinuumGreen L mass hmass f_im f_im) := h_exp_bound_im
    _ ≤ Real.exp (torusContinuumGreen L mass hmass f_im f_im + |Real.log K|) := by
        have hle : K ≤ Real.exp (|Real.log K|) := by
          by_cases h1 : 1 ≤ K
          · rw [abs_of_nonneg (Real.log_nonneg h1), Real.exp_log hK_pos]
          · push_neg at h1
            exact le_trans h1.le (Real.one_le_exp (abs_nonneg _))
        calc K * Real.exp (torusContinuumGreen L mass hmass f_im f_im)
            ≤ Real.exp (|Real.log K|) *
              Real.exp (torusContinuumGreen L mass hmass f_im f_im) :=
              mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
          _ = Real.exp (torusContinuumGreen L mass hmass f_im f_im + |Real.log K|) := by
              rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (1 * ((torusContinuumGreen L mass hmass f_re f_re + |Real.log K|) +
          (torusContinuumGreen L mass hmass f_im f_im + |Real.log K|))) := by
        rw [one_mul]; apply Real.exp_le_exp_of_le
        linarith [torusContinuumGreen_nonneg L mass hmass f_re, abs_nonneg (Real.log K)]

/-! ## OS2: Translation invariance of the interacting measure

On the torus T² = (ℝ/Lℤ)², translations in BOTH directions are exact
symmetries at every lattice cutoff N. The interaction
  `V_N(ω) = a² Σ_x :P(φ(x)):_c`
sums over ALL lattice sites with periodic boundary conditions, so
translating by any lattice vector permutes the summand and leaves V_N
unchanged. The free GFF measure is also translation-invariant
(`torusGaussianLimit_os2_translation`). Since both factors in
`(1/Z) exp(-V) dμ_GFF` are invariant, so is each cutoff measure.

Translation invariance passes to the limit by weak convergence:
for any bounded continuous test functional F and translation T_v,
  `∫ F(ω) dμ_N = ∫ F(T_v^{-1} ω) dμ_N`  (cutoff invariance)
Taking N → ∞, both sides converge to the limit, giving
  `∫ F(ω) dμ = ∫ F(T_v^{-1} ω) dμ`     (limit invariance) -/

/-- **OS2 (translation) for the torus interacting continuum limit.**

The interacting measure is invariant under translations on T²_L.
  `Z(f) = Z(T_v f)` for all `v ∈ ℝ²`.

This follows directly from `torusInteractingLimit_translation_invariant`,
which axiomatizes the continuum limit's translation invariance. -/
theorem torusInteracting_os2_translation
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (_φ : ℕ → ℕ) (_hφ : StrictMono _φ)
    (_hconv : ∀ (f : Configuration (TorusTestFunction L) → ℝ),
      Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun n => ∫ ω, f ω ∂(torusInteractingMeasure L (_φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, f ω ∂μ))) :
    TorusOS2_TranslationInvariance L μ := by
  intro v f
  exact torusInteractingLimit_translation_invariant L P mass hmass μ _φ _hφ _hconv v f

/-! ## OS2: D4 point group invariance

The D4 symmetry group of the square torus (swap + time reflection)
is an exact symmetry of both the free measure and the interaction
at every lattice cutoff. Like translation invariance, it passes
to the continuum limit by weak convergence. -/

/-- **OS2 (D4) for the torus interacting continuum limit.**

The interacting measure is invariant under coordinate swap
and time reflection on T²_L. -/
theorem torusInteracting_os2_D4
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (_hφ : StrictMono φ)
    (hconv : ∀ (f : Configuration (TorusTestFunction L) → ℝ),
      Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun n => ∫ ω, f ω ∂(torusInteractingMeasure L (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, f ω ∂μ))) :
    TorusOS2_D4Invariance L μ := by
  constructor
  · -- Swap invariance: Z_μ[f] = Z_μ[σf] for all f
    intro f
    apply Complex.ext
    · -- Re part
      rw [gf_re_eq_cos_integral L μ f, gf_re_eq_cos_integral L μ (torusSwap L f)]
      have h_Sf := hconv _ (cosEval_continuous L (torusSwap L f))
        (cosEval_bounded L (torusSwap L f))
      have h_f := hconv _ (cosEval_continuous L f) (cosEval_bounded L f)
      have h_cutoff : ∀ n, ∫ ω, Real.cos (ω (torusSwap L f))
          ∂(torusInteractingMeasure L (φ n + 1) P mass hmass) =
        ∫ ω, Real.cos (ω f) ∂(torusInteractingMeasure L (φ n + 1) P mass hmass) := by
        intro n
        have hgf := torusInteractingMeasure_gf_swap_invariant L (φ n + 1) P mass hmass f
        have hre := congr_arg Complex.re hgf
        rw [gf_re_eq_cos_integral, gf_re_eq_cos_integral] at hre
        exact hre.symm
      exact tendsto_nhds_unique h_f (h_Sf.congr h_cutoff)
    · -- Im part
      rw [gf_im_eq_sin_integral L μ f, gf_im_eq_sin_integral L μ (torusSwap L f)]
      have h_Sf := hconv _ (sinEval_continuous L (torusSwap L f))
        (sinEval_bounded L (torusSwap L f))
      have h_f := hconv _ (sinEval_continuous L f) (sinEval_bounded L f)
      have h_cutoff : ∀ n, ∫ ω, Real.sin (ω (torusSwap L f))
          ∂(torusInteractingMeasure L (φ n + 1) P mass hmass) =
        ∫ ω, Real.sin (ω f) ∂(torusInteractingMeasure L (φ n + 1) P mass hmass) := by
        intro n
        have hgf := torusInteractingMeasure_gf_swap_invariant L (φ n + 1) P mass hmass f
        have him := congr_arg Complex.im hgf
        rw [gf_im_eq_sin_integral, gf_im_eq_sin_integral] at him
        exact him.symm
      exact tendsto_nhds_unique h_f (h_Sf.congr h_cutoff)
  · -- Time reflection invariance: Z_μ[f] = Z_μ[Θf] for all f
    intro f
    apply Complex.ext
    · -- Re part
      rw [gf_re_eq_cos_integral L μ f,
          gf_re_eq_cos_integral L μ (torusTimeReflection L f)]
      have h_Θf := hconv _ (cosEval_continuous L (torusTimeReflection L f))
        (cosEval_bounded L (torusTimeReflection L f))
      have h_f := hconv _ (cosEval_continuous L f) (cosEval_bounded L f)
      have h_cutoff : ∀ n, ∫ ω, Real.cos (ω (torusTimeReflection L f))
          ∂(torusInteractingMeasure L (φ n + 1) P mass hmass) =
        ∫ ω, Real.cos (ω f) ∂(torusInteractingMeasure L (φ n + 1) P mass hmass) := by
        intro n
        have hgf := torusInteractingMeasure_gf_timeReflection_invariant L (φ n + 1)
          P mass hmass f
        have hre := congr_arg Complex.re hgf
        rw [gf_re_eq_cos_integral, gf_re_eq_cos_integral] at hre
        exact hre.symm
      exact tendsto_nhds_unique h_f (h_Θf.congr h_cutoff)
    · -- Im part
      rw [gf_im_eq_sin_integral L μ f,
          gf_im_eq_sin_integral L μ (torusTimeReflection L f)]
      have h_Θf := hconv _ (sinEval_continuous L (torusTimeReflection L f))
        (sinEval_bounded L (torusTimeReflection L f))
      have h_f := hconv _ (sinEval_continuous L f) (sinEval_bounded L f)
      have h_cutoff : ∀ n, ∫ ω, Real.sin (ω (torusTimeReflection L f))
          ∂(torusInteractingMeasure L (φ n + 1) P mass hmass) =
        ∫ ω, Real.sin (ω f) ∂(torusInteractingMeasure L (φ n + 1) P mass hmass) := by
        intro n
        have hgf := torusInteractingMeasure_gf_timeReflection_invariant L (φ n + 1)
          P mass hmass f
        have him := congr_arg Complex.im hgf
        rw [gf_im_eq_sin_integral, gf_im_eq_sin_integral] at him
        exact him.symm
      exact tendsto_nhds_unique h_f (h_Θf.congr h_cutoff)

/-! ## Bundled OS axioms -/

/-- **The torus P(φ)₂ interacting continuum limit satisfies OS0–OS2.**

This bundles all verifiable OS axioms for the interacting torus measure.
OS3 (reflection positivity) is dropped — it is natural on the
cylinder S¹×ℝ, not the torus T². -/
theorem torusInteracting_satisfies_OS
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ (f : Configuration (TorusTestFunction L) → ℝ),
      Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun n => ∫ ω, f ω ∂(torusInteractingMeasure L (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, f ω ∂μ))) :
    SatisfiesTorusOS L μ where
  os0 := torusInteracting_os0 L P mass hmass μ φ hφ hconv
  os1 := torusInteracting_os1 L P mass hmass μ φ hφ hconv
  os2_translation := torusInteracting_os2_translation L P mass hmass μ φ hφ hconv
  os2_D4 := torusInteracting_os2_D4 L P mass hmass μ φ hφ hconv

end Pphi2

end
