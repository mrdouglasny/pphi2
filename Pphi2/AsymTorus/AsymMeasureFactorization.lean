/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.AsymTorus.AsymEnergyFactorization
import Pphi2.AsymTorus.AsymLatticeMeasure
import GaussianField.DensityAsym

/-!
# Crux-2 steps 4–5: the measure factorization `μ_int.map sliceEquiv = pathMeasure`

The capstone of the Layer-B2 measure↔operator bridge: the interacting lattice measure, pushed
to coordinates (`evalMapAsym`) and then to time-slices (`asymSliceEquiv`), equals the periodic
path measure of `asymTransferKernel` (the abstract `TransferSystem.pathMeasure`). Once this
lands, the proved Feynman–Kac dictionary (`twoPoint_dictionary`) + the gap (`susceptibility_le`)
give the `Lt`-uniform correlator bound, and B5's `1/a` cancellation closes
`asymInteractingVariance_le_freeVariance_Lt_uniform`.

**All inputs are proved and in place** (this is gluing, no new mathematics):
1. `GaussianField.latticeGaussianFieldLawAsym_eq_normalizedQuadraticGaussianMeasure` — the free
   GFF pushed by `evalMapAsym` is the Lebesgue-density Gaussian `(Z_Q)⁻¹·exp(−(a²/2)⟨φ,Qφ⟩)·vol`.
2. `interactionFunctionalAsym` in coordinates: `V(ω) = a²·Σ_x :P:((evalMapAsym ω) x)`.
3. `energy_exponent_factorization` : `(a²/2)⟨φ,Qφ⟩ + a²Σ:P: = Σ_t (timeCoupling + a²·spatialAction)`.
4. `periodicPathDensity_asymTransferKernel_eq_exp` : `∏_t k(slices) = exp(−that)`.
5. `asymSliceEquiv` is measure-preserving for the Pi-Lebesgue volume (coordinate reindex, Jacobian 1).

## Proof strategy (the remaining gluing)

`interactingLatticeMeasureAsym = (Z_int)⁻¹ • (latticeGaussianMeasureAsym.withDensity exp(−V))`.
- Push through `evalMapAsym` (a measurable equiv, `evalMapAsymMeasurableEquiv`): `Measure.map` of a
  scaled `withDensity` through an equiv is the scaled `withDensity` of the pushforward with the
  density precomposed with the inverse (`withDensity_map_equiv`-style). Use input (1) for the free
  pushforward and input (2) for the interaction density in coordinates.
  ⟹ `= (Z_int·Z_Q)⁻¹ • volume.withDensity (exp(−((a²/2)⟨φ,Qφ⟩ + a²Σ:P:)))`.
- Rewrite the exponent by (3) and the exponential by (4): the density is `∏_t k(asymSliceEquiv φ)`.
- Push through `asymSliceEquiv` and use (5) (`volume.map asymSliceEquiv = Measure.pi (fun _ => volume)`):
  `= (Z_int·Z_Q)⁻¹ • (Measure.pi (fun _ => volume)).withDensity (∏_t k)`.
- Match `asymTransferSystem.pathMeasure Nt = (Z_path)⁻¹ • (Measure.pi (fun _ => volume)).withDensity
  (∏_t k)`. Both are probability measures with the *same* unnormalized density, so the normalizing
  constants agree (`Z_int·Z_Q = Z_path`, each `= ∫ ∏_t k`) and the measures are equal.
-/

open MeasureTheory GaussianField ReflectionPositivity
open scoped BigOperators ENNReal

namespace Pphi2

variable (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]

/-! ## Generic measure-theory helpers -/

/-- Pushing a scaled `withDensity` through a measurable equivalence:
`((μ.withDensity (g ∘ e)).map e = (μ.map e).withDensity g`. The density precomposed with the
inverse on the source becomes the bare density on the target. -/
theorem withDensity_comp_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) (e : α ≃ᵐ β) (g : β → ℝ≥0∞) :
    (μ.withDensity (fun x => g (e x))).map e = (μ.map e).withDensity g := by
  ext s hs
  rw [MeasurableEquiv.map_apply, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, e.restrict_map, MeasureTheory.lintegral_map_equiv]

/-! ## The volume-preserving slice reindexing `asymSliceEquiv`

`asymSliceEquiv` curries the time/space product index and reindexes the spatial `ZMod Ns` to
`Fin Ns`. We package it as a `MeasurableEquiv` and show it preserves the Pi-Lebesgue volume,
using `Measure.pi_eq` for the (domain) currying step and `arrowCongr'` for the spatial reindex. -/

/-- Currying preserves the Pi-Lebesgue volume `(γ × δ → ℝ) ≃ᵐ (γ → δ → ℝ)`.

`Measure.pi_eq` quantifies over all measurable slices `s g`, so the preimage of a general
`Set.pi univ s` is not a measurable box; instead we verify agreement on the box π-system `C`
(`pi_eq_generateFrom`), where each `s g` *is* a nested box, hence the preimage is a flat box. -/
theorem measurePreserving_curry (γ δ : Type*) [Fintype γ] [Fintype δ] :
    MeasurePreserving (MeasurableEquiv.curry γ δ ℝ)
      (volume : Measure (γ × δ → ℝ)) (volume : Measure (γ → δ → ℝ)) := by
  classical
  let C : Set (Set (δ → ℝ)) :=
    Set.pi Set.univ '' Set.pi Set.univ (fun _ : δ => {s : Set ℝ | MeasurableSet s})
  refine ⟨(MeasurableEquiv.curry γ δ ℝ).measurable, ?_⟩
  change Measure.map (MeasurableEquiv.curry γ δ ℝ) (volume : Measure (γ × δ → ℝ)) =
    (volume : Measure (γ → δ → ℝ))
  have hEq : Measure.pi (fun _ : γ => (volume : Measure (δ → ℝ))) =
      Measure.map (MeasurableEquiv.curry γ δ ℝ) (volume : Measure (γ × δ → ℝ)) := by
    refine Measure.pi_eq_generateFrom (μ := fun _ : γ => (volume : Measure (δ → ℝ)))
      (C := fun _ : γ => C) (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi) ?_ ?_
    · intro _
      exact Measure.FiniteSpanningSetsIn.pi
        (μ := fun _ : δ => (volume : Measure ℝ))
        (C := fun _ : δ => {s : Set ℝ | MeasurableSet s})
        (fun _ : δ => (volume : Measure ℝ).toFiniteSpanningSetsIn)
    · intro s hs
      have hs' : ∀ g : γ, ∃ t : δ → Set ℝ,
          t ∈ Set.pi Set.univ (fun _ : δ => {u : Set ℝ | MeasurableSet u}) ∧
          Set.pi Set.univ t = s g := by
        intro g
        simpa [C] using hs g
      choose t ht hst using hs'
      have ht_meas : ∀ g d, MeasurableSet (t g d) := fun g d => ht g d (Set.mem_univ d)
      have hsm : ∀ g, MeasurableSet (s g) := by
        intro g
        rw [← hst g]
        exact MeasurableSet.univ_pi (fun d => ht_meas g d)
      rw [Measure.map_apply (MeasurableEquiv.curry γ δ ℝ).measurable
        (MeasurableSet.univ_pi hsm)]
      have hpre : (MeasurableEquiv.curry γ δ ℝ) ⁻¹' Set.pi Set.univ s =
          Set.pi Set.univ (fun p : γ × δ => t p.1 p.2) := by
        ext f
        constructor
        · intro hf p _
          have hfg : Function.curry f p.1 ∈ s p.1 := hf p.1 (Set.mem_univ p.1)
          rw [← hst p.1] at hfg
          exact hfg p.2 (Set.mem_univ p.2)
        · intro hf g _
          rw [← hst g]
          intro d _
          exact hf (g, d) (Set.mem_univ (g, d))
      rw [hpre]
      calc
        (volume : Measure (γ × δ → ℝ)) (Set.pi Set.univ (fun p : γ × δ => t p.1 p.2))
            = ∏ p : γ × δ, (volume : Measure ℝ) (t p.1 p.2) := by
              change (Measure.pi (fun _ : γ × δ => (volume : Measure ℝ)))
                  (Set.pi Set.univ (fun p : γ × δ => t p.1 p.2)) = _
              rw [Measure.pi_pi]
        _ = ∏ g : γ, ∏ d : δ, (volume : Measure ℝ) (t g d) :=
              Fintype.prod_prod_type (fun p : γ × δ => (volume : Measure ℝ) (t p.1 p.2))
        _ = ∏ g : γ, (volume : Measure (δ → ℝ)) (s g) := by
              apply Finset.prod_congr rfl
              intro g _
              rw [← hst g]
              change (∏ d : δ, (volume : Measure ℝ) (t g d)) =
                (Measure.pi (fun _ : δ => (volume : Measure ℝ))) (Set.pi Set.univ (t g))
              rw [Measure.pi_pi]
  simpa using hEq.symm

/-- The per-slice spatial reindex `(ZMod Nt → ZMod Ns → ℝ) ≃ᵐ (ZMod Nt → Fin Ns → ℝ)`, applying
`ZMod.finEquiv Ns` inside each time slice. -/
noncomputable def sliceReindexMeasurableEquiv :
    (ZMod Nt → ZMod Ns → ℝ) ≃ᵐ (ZMod Nt → SpatialField Ns) :=
  MeasurableEquiv.arrowCongr' (Equiv.refl (ZMod Nt))
    (MeasurableEquiv.arrowCongr' (ZMod.finEquiv Ns).toEquiv.symm (MeasurableEquiv.refl ℝ))

/-- The slice reindex preserves the Pi-Lebesgue volume. -/
theorem measurePreserving_sliceReindex :
    MeasurePreserving (sliceReindexMeasurableEquiv Nt Ns)
      (volume : Measure (ZMod Nt → ZMod Ns → ℝ))
      (volume : Measure (ZMod Nt → SpatialField Ns)) := by
  unfold sliceReindexMeasurableEquiv
  refine volume_preserving_arrowCongr' (Equiv.refl (ZMod Nt)) _ ?_
  exact volume_preserving_arrowCongr' (ZMod.finEquiv Ns).toEquiv.symm
    (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _)

/-- The slice equivalence `asymSliceEquiv` packaged as a measurable equivalence: curry the
spacetime product index, then reindex each spatial slice `ZMod Ns → Fin Ns`. -/
noncomputable def asymSliceMeasurableEquiv :
    AsymLatticeField Nt Ns ≃ᵐ (ZMod Nt → SpatialField Ns) :=
  (MeasurableEquiv.curry (ZMod Nt) (ZMod Ns) ℝ).trans (sliceReindexMeasurableEquiv Nt Ns)

/-- The measurable-equiv packaging agrees with the linear-equiv `asymSliceEquiv`. -/
theorem asymSliceMeasurableEquiv_coe :
    ⇑(asymSliceMeasurableEquiv Nt Ns) = asymSliceEquiv Nt Ns := by
  funext φ
  funext t
  funext x
  rw [asymSliceEquiv_apply]
  rfl

/-- `asymSliceEquiv` preserves the Pi-Lebesgue volume. -/
theorem measurePreserving_asymSliceEquiv :
    MeasurePreserving (asymSliceEquiv Nt Ns)
      (volume : Measure (AsymLatticeField Nt Ns))
      (volume : Measure (ZMod Nt → SpatialField Ns)) := by
  rw [← asymSliceMeasurableEquiv_coe Nt Ns]
  exact (measurePreserving_curry (ZMod Nt) (ZMod Ns)).trans
    (measurePreserving_sliceReindex Nt Ns)

/-! ## The interaction functional in coordinates -/

/-- The interaction functional, precomposed with the coordinate inverse `evalMapAsymInv`, is the
on-site Wick interaction of the coordinate field: `V(evalMapInv φ) = a²·Σ_x :P:(φ x)`. -/
theorem interactionFunctionalAsym_evalMapAsymInv (P : InteractionPolynomial) (a mass : ℝ)
    (φ : AsymLatticeField Nt Ns) :
    interactionFunctionalAsym Nt Ns P a mass (evalMapAsymInv Nt Ns φ) =
      a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
        wickPolynomial P (wickConstantAsym Nt Ns a mass) (φ x) := by
  unfold interactionFunctionalAsym
  congr 1
  refine Finset.sum_congr rfl (fun x _ => ?_)
  congr 1
  have : evalMapAsym Nt Ns (evalMapAsymInv Nt Ns φ) x = φ x :=
    congrFun (evalMap_evalMapInvAsym Nt Ns φ) x
  simpa [evalMapAsym] using this

/-! ## The combined coordinate density equals the path density through the slices -/

/-- The product of the Gaussian density and the Boltzmann interaction weight, in coordinates,
equals the path density along the time slices: `ρ_Q(φ)·exp(−a²Σ:P:(φ)) = ∏_t k(ψ_t,ψ_{t+1})`. -/
theorem gaussianDensity_mul_boltzmann_eq_pathDensity
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (φ : AsymLatticeField Nt Ns) :
    gaussianDensityAsym Nt Ns a mass φ *
        Real.exp (-(a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
          wickPolynomial P (wickConstantAsym Nt Ns a mass) (φ x))) =
      (asymTransferSystem Nt Ns P a mass ha hmass).pathDensity Nt
        (asymSliceEquiv Nt Ns φ) := by
  show gaussianDensityAsym Nt Ns a mass φ * _ =
    periodicPathDensity (asymTransferKernel Nt Ns P a mass) Nt (asymSliceEquiv Nt Ns φ)
  rw [periodicPathDensity_asymTransferKernel_eq_exp P a mass (ne_of_gt ha) φ]
  unfold gaussianDensityAsym
  rw [← Real.exp_add]
  congr 1
  ring

/-- The Boltzmann weight is the coordinate Wick weight precomposed with `evalMapAsym`. -/
theorem boltzmannWeightAsym_eq_comp_evalMapAsym (P : InteractionPolynomial) (a mass : ℝ)
    (ω : Configuration (AsymLatticeField Nt Ns)) :
    boltzmannWeightAsym Nt Ns P a mass ω =
      Real.exp (-(a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
        wickPolynomial P (wickConstantAsym Nt Ns a mass) (evalMapAsym Nt Ns ω x))) := by
  rfl

/-- **Crux-2 steps 4–5 (measure factorization).** The interacting lattice measure, pushed to
coordinates and then to time-slices, equals the periodic path measure of `asymTransferKernel`. -/
theorem interactingLatticeMeasureAsym_slice_pushforward_eq_pathMeasure
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    (((interactingLatticeMeasureAsym Nt Ns P a mass ha hmass).map (evalMapAsym Nt Ns)).map
        (asymSliceEquiv Nt Ns)) =
      (asymTransferSystem Nt Ns P a mass ha hmass).pathMeasure Nt := by
  classical
  set Ts := asymTransferSystem Nt Ns P a mass ha hmass with hTs
  -- the two measurable equivs and their coercions to the bare maps in the goal
  have he : ⇑(evalMapAsymMeasurableEquiv Nt Ns) = evalMapAsym Nt Ns := rfl
  have hsc : ⇑(asymSliceMeasurableEquiv Nt Ns) = asymSliceEquiv Nt Ns :=
    asymSliceMeasurableEquiv_coe Nt Ns
  -- the coordinate Wick density `g φ = ofReal(exp(−a²·Σ:P:(φ)))`
  set g : AsymLatticeField Nt Ns → ℝ≥0∞ := fun φ =>
    ENNReal.ofReal (Real.exp (-(a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
      wickPolynomial P (wickConstantAsym Nt Ns a mass) (φ x)))) with hg
  have hwick_cont : Continuous (fun y : ℝ => wickPolynomial P (wickConstantAsym Nt Ns a mass) y) :=
    (wickPolynomial_continuous₂ P).comp (continuous_const.prodMk continuous_id)
  have hg_meas : Measurable g := by
    refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
    exact (measurable_const.mul
      (Finset.measurable_sum _ (fun x _ =>
        hwick_cont.measurable.comp (measurable_pi_apply x)))).neg
  -- the unnormalized path measure `ρ`
  set h : (ZMod Nt → SpatialField Ns) → ℝ≥0∞ :=
    fun ψ => ENNReal.ofReal (Ts.pathDensity Nt ψ) with hh
  have hh_meas : Measurable h :=
    ENNReal.measurable_ofReal.comp (Ts.pathDensity_measurable Nt)
  set ρ : Measure (ZMod Nt → SpatialField Ns) :=
    (Measure.pi (fun _ : ZMod Nt => (volume : Measure (SpatialField Ns)))).withDensity h with hρ
  -- abbreviations for the two scalar normalizations
  set Zint := ENNReal.ofReal (partitionFunctionAsym Nt Ns P a mass ha hmass) with hZint
  set ZQ := gaussianDensityNormConstAsym Nt Ns a mass with hZQ
  -- ## Step (b)+(c): pushforward by `evalMapAsym`, with the free GFF density bridge.
  have hstep_bc :
      (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass).map (evalMapAsym Nt Ns) =
        (Zint⁻¹ * ZQ⁻¹) •
          (volume.withDensity
            (fun φ => ENNReal.ofReal (Ts.pathDensity Nt (asymSliceEquiv Nt Ns φ)))) := by
    -- (b) push the scaled withDensity through `e = evalMapAsym`
    have hboltz : (fun ω => ENNReal.ofReal (boltzmannWeightAsym Nt Ns P a mass ω)) =
        fun ω => g (evalMapAsym Nt Ns ω) := by
      funext ω
      rw [boltzmannWeightAsym_eq_comp_evalMapAsym]
    rw [interactingLatticeMeasureAsym, Measure.map_smul, ← hZint, hboltz, ← he,
      withDensity_comp_map_measurableEquiv]
    rw [he]
    -- (c) the free GFF in coordinates is `(ZQ)⁻¹ • volume.withDensity (ofReal∘gaussianDensity)`
    have hfree : (latticeGaussianMeasureAsym Nt Ns a mass ha hmass).map (evalMapAsym Nt Ns) =
        ZQ⁻¹ • volume.withDensity (gaussianDensityWeightAsym Nt Ns a mass) := by
      show (GaussianField.measure (latticeCovarianceAsymGJ Nt Ns a mass ha hmass)).map
          (evalMapAsym Nt Ns) = _
      rw [show (GaussianField.measure (latticeCovarianceAsymGJ Nt Ns a mass ha hmass)).map
          (evalMapAsym Nt Ns)
          = latticeGaussianFieldLawAsym Nt Ns a mass ha hmass from rfl,
        latticeGaussianFieldLawAsym_eq_normalizedQuadraticGaussianMeasure,
        ← normalizedGaussianDensityMeasureAsym_eq_normalizedQuadraticGaussianMeasure]
      rfl
    have hgw : Measurable (gaussianDensityWeightAsym Nt Ns a mass) :=
      (GaussianField.gaussianDensityAsym_measurable Nt Ns a mass).ennreal_ofReal
    rw [hfree, withDensity_smul_measure, ← withDensity_mul _ hgw hg_meas]
    -- combine the two scalars and rewrite the merged density
    rw [smul_smul]
    congr 1
    apply withDensity_congr_ae
    filter_upwards with φ
    show (gaussianDensityWeightAsym Nt Ns a mass φ) * g φ = _
    rw [hg]
    show ENNReal.ofReal (gaussianDensityAsym Nt Ns a mass φ) * ENNReal.ofReal _ = _
    rw [← ENNReal.ofReal_mul (gaussianDensityAsym_nonneg Nt Ns a mass φ),
      gaussianDensity_mul_boltzmann_eq_pathDensity Nt Ns P a mass ha hmass φ]
  -- ## Step (e): push by `asymSliceEquiv`; the density is `h ∘ asymSliceEquiv`.
  have hLHS :
      ((interactingLatticeMeasureAsym Nt Ns P a mass ha hmass).map (evalMapAsym Nt Ns)).map
          (asymSliceEquiv Nt Ns) = (Zint⁻¹ * ZQ⁻¹) • ρ := by
    rw [hstep_bc, Measure.map_smul]
    congr 1
    have hdens : (fun φ => ENNReal.ofReal (Ts.pathDensity Nt (asymSliceEquiv Nt Ns φ))) =
        fun φ => h (asymSliceEquiv Nt Ns φ) := rfl
    rw [hdens, ← hsc, withDensity_comp_map_measurableEquiv, hsc,
      (measurePreserving_asymSliceEquiv Nt Ns).map_eq, hρ]
    rfl
  -- ## Step (f): match the normalizations.
  -- LHS is a probability measure (pushforward of a probability measure).
  haveI : IsProbabilityMeasure (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) :=
    interactingLatticeMeasureAsym_isProbability Nt Ns P a mass ha hmass
  haveI hprob : IsProbabilityMeasure
      (((interactingLatticeMeasureAsym Nt Ns P a mass ha hmass).map (evalMapAsym Nt Ns)).map
        (asymSliceEquiv Nt Ns)) := by
    haveI : IsProbabilityMeasure
        ((interactingLatticeMeasureAsym Nt Ns P a mass ha hmass).map (evalMapAsym Nt Ns)) :=
      Measure.isProbabilityMeasure_map (measurable_evalMapAsym Nt Ns).aemeasurable
    exact Measure.isProbabilityMeasure_map
      (measurePreserving_asymSliceEquiv Nt Ns).measurable.aemeasurable
  -- mass of LHS is 1
  have hmass_one : (Zint⁻¹ * ZQ⁻¹) * ρ Set.univ = 1 := by
    have := hprob.measure_univ
    rw [hLHS, Measure.smul_apply, smul_eq_mul] at this
    exact this
  -- ρ is a finite measure with `ρ univ = ofReal (partition Nt)`
  have hρuniv_lt : ρ Set.univ ≠ ⊤ := by
    intro htop
    rw [htop] at hmass_one
    rcases eq_or_ne (Zint⁻¹ * ZQ⁻¹) 0 with hc | hc
    · rw [hc, zero_mul] at hmass_one; exact zero_ne_one hmass_one
    · rw [ENNReal.mul_top hc] at hmass_one; exact ENNReal.top_ne_one hmass_one
  have hρuniv_ne : ρ Set.univ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmass_one
    exact one_ne_zero hmass_one.symm
  -- `pathDensity` is integrable since its `ofReal`-lintegral (= ρ univ) is finite
  have hpd_nonneg : 0 ≤ᵐ[Measure.pi (fun _ : ZMod Nt => (volume : Measure (SpatialField Ns)))]
      Ts.pathDensity Nt :=
    ae_of_all _ (fun ψ => Ts.pathDensity_nonneg Nt ψ)
  have hlint : ∫⁻ ψ, ENNReal.ofReal (Ts.pathDensity Nt ψ)
        ∂(Measure.pi (fun _ : ZMod Nt => (volume : Measure (SpatialField Ns)))) = ρ Set.univ := by
    rw [hρ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hpd_integrable : Integrable (Ts.pathDensity Nt)
      (Measure.pi (fun _ : ZMod Nt => (volume : Measure (SpatialField Ns)))) := by
    refine ⟨(Ts.pathDensity_measurable Nt).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hpd_nonneg, hlint]
    exact lt_of_le_of_ne le_top hρuniv_lt
  have hpartition : ENNReal.ofReal (Ts.partition Nt) = ρ Set.univ := by
    have hpart_eq : Ts.partition Nt =
        ∫ ψ, Ts.pathDensity Nt ψ
          ∂(Measure.pi (fun _ : ZMod Nt => (volume : Measure (SpatialField Ns)))) := rfl
    rw [hpart_eq, ofReal_integral_eq_lintegral_ofReal hpd_integrable hpd_nonneg, hlint]
  -- RHS = (ofReal (partition Nt))⁻¹ • ρ = (ρ univ)⁻¹ • ρ
  have hRHS : Ts.pathMeasure Nt = (ρ Set.univ)⁻¹ • ρ := by
    have hpm_eq : Ts.pathMeasure Nt =
        (ENNReal.ofReal (Ts.partition Nt))⁻¹ • ρ := rfl
    rw [hpm_eq, hpartition]
  -- close: both LHS and RHS equal (ρ univ)⁻¹ • ρ
  rw [hLHS, hRHS]
  congr 1
  -- `Zint⁻¹ * ZQ⁻¹ = (ρ univ)⁻¹` from `(Zint⁻¹*ZQ⁻¹) * ρ univ = 1`
  exact ENNReal.eq_inv_of_mul_eq_one_left hmass_one

end Pphi2
