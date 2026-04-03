/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nelson's Hypercontractive Estimate for the Interacting Measure

Bounds the L^p moments of the interacting measure μ_a in terms of the
free Gaussian measure μ_{GFF}:

  ∫ |ω(f)|^{pn} dμ_a ≤ C · (2p-1)^{pn/2} · (∫ |ω(f)|^{2n} dμ_{GFF})^{p/2}

The RHS is evaluated against the FREE Gaussian measure, not the interacting
measure. This is mathematically essential: the reverse transfer (from μ_{GFF}
to μ_a) would require bounding ∫ e^{+V_a} dμ_{GFF}, which diverges because
V_a ~ φ⁴ grows faster than the Gaussian e^{-φ²} suppression.

Two proof paths are provided, both decomposed into textbook axioms.

## Option A: Cauchy-Schwarz Density Transfer (3 axioms → interacting_moment_bound)

The interacting measure dμ_a = (1/Z_a) exp(-V_a) dμ_{GFF,a} is absolutely
continuous w.r.t. the Gaussian free field. The proof:

1. **Gaussian hypercontractivity** — Already proved in gaussian-field for
   the abstract Gaussian measure. Here we state the consequence for the
   lattice GFF in the continuum-embedded form.

2. **Exponential moment bound** — ∫ exp(-2V_a) dμ_{GFF} ≤ K uniformly
   in a. This is the key analytic input (Nelson's estimate / Simon §V).
   Note: only the NEGATIVE exponential exp(-sV_a) is bounded; the positive
   exponential exp(+V_a) diverges because V_a ~ φ⁴.

3. **Cauchy-Schwarz density transfer** — Cauchy-Schwarz on the density
   e^{-V_a}/Z_a gives:
     ∫ F dμ_a = (1/Z_a) ∫ F·e^{-V_a} dμ_{GFF}
              ≤ (1/Z_a)·(∫ F² dμ_{GFF})^{1/2}·(∫ e^{-2V_a} dμ_{GFF})^{1/2}
   Combined with Gaussian hypercontractivity for ∫ F² and the exponential
   moment bound, this gives the interacting moment bound with RHS in terms
   of μ_{GFF}.

Note: An earlier version used Holley-Stroock perturbation, but that requires
bounded oscillation of V_a, which is FALSE for P(φ)₂ (V_a grows like φ⁴).
A subsequent version stated the RHS in terms of the interacting measure μ_a,
but converting back from μ_{GFF} requires e^{+V_a} integrability, which fails.

## Option B: Full Gross-Rothaus-Simon framework (5 additional axioms)

Not required for the main theorem. Provides the full OU semigroup
infrastructure for extensions beyond Wick monomials.

## References

- Simon, *The P(φ)₂ Euclidean QFT*, §V (exponential moment estimates)
- Glimm-Jaffe, *Quantum Physics*, §19.4
- Nelson, "The free Markoff field," J. Funct. Anal. 12 (1973), 211–227
- Gross, "Logarithmic Sobolev inequalities," Amer. J. Math. 97 (1975), 1061–1083
-/

import Pphi2.ContinuumLimit.Embedding
import Pphi2.GeneralResults.GaussianHermiteMean
import Pphi2.GeneralResults.LatticeProductDFT
import GaussianField.Density
import GaussianField.HypercontractiveNat
import Lattice.CirculantDFT2d
import Lattice.Symmetry
import Mathlib.Analysis.Convex.Integral

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

variable (d N : ℕ) [NeZero N]

/-! # Option A: Cauchy-Schwarz Density Transfer

This is the standard approach for P(φ)₂. The interacting measure μ_a is
absolutely continuous w.r.t. the Gaussian μ_{GFF}, so we can transfer
moment bounds via Cauchy-Schwarz on the density e^{-V_a}/Z_a, paying a
cost controlled by exponential moments of the interaction V_a. The key
point is that the RHS of the bound uses the FREE Gaussian measure, not
the interacting measure. -/

/-! ## Step A1: Gaussian hypercontractivity for the continuum-embedded measure

The Gaussian free field μ_{GFF} satisfies the hypercontractive inequality
for polynomial functionals. This is already proved in gaussian-field
(`gaussian_hypercontractive`). Here we state it in the continuum-embedded
form used by the rest of the proof. -/

/- We use the generic embedding bridge from `Embedding.lean`, where
`latticeTestField` is the discretization of a continuum test function and
`latticeEmbedLift_eval_eq` identifies continuum evaluation with lattice
configuration evaluation on that test field. -/

/-- **Gaussian hypercontractivity** in continuum-embedded form.

For the continuum-embedded Gaussian measure (pushforward of μ_{GFF} under
the lattice embedding ι_a), Wick monomials satisfy:

  ∫ |ω(f)|^{pn} d(ι_a)_*μ_{GFF} ≤ (p-1)^{pn/2} · (∫ |ω(f)|^{2n} d(ι_a)_*μ_{GFF})^{p/2}

This follows from `gaussian_hypercontractive` in gaussian-field by
rewriting the pushforward integral back to the lattice Gaussian measure
via `integral_map`, then observing that `(latticeEmbedLift ω)(f) = ω(g_f)`
where `g_f` is the embedded test function, reducing to an instance of
the abstract Gaussian hypercontractive bound.

Reference: Gross (1975); gaussian-field/Hypercontractive.lean. -/
theorem gaussian_hypercontractivity_continuum
    (mass : ℝ) (hmass : 0 < mass)
    (n : ℕ) (p : ℝ) (hp : 2 ≤ p) (m : ℕ) (hm : 1 ≤ m) (hp_eq : p = 2 * ↑m)
    (f : ContinuumTestFunction d)
    (a : ℝ) (ha : 0 < a) (_ha1 : a ≤ 1) :
    ∫ ω : Configuration (ContinuumTestFunction d),
        |ω f| ^ (p * ↑n) ∂(Measure.map (latticeEmbedLift d N a ha)
          (latticeGaussianMeasure d N a mass ha hmass)) ≤
      (p - 1) ^ (p * ↑n / 2) *
      (∫ ω : Configuration (ContinuumTestFunction d),
        |ω f| ^ (2 * ↑n) ∂(Measure.map (latticeEmbedLift d N a ha)
          (latticeGaussianMeasure d N a mass ha hmass))) ^
      (p / 2) := by
  -- Step 1: Rewrite integrals using integral_map to pull back from S'(ℝ^d) to lattice
  set μ := latticeGaussianMeasure d N a mass ha hmass
  set ι := latticeEmbedLift d N a ha
  have hι : AEMeasurable ι μ := (latticeEmbedLift_measurable d N a ha).aemeasurable
  -- Measurability of the integrands (needed for integral_map)
  have hmeas_p : AEStronglyMeasurable (fun (ω : Configuration (ContinuumTestFunction d)) =>
      |ω f| ^ (p * ↑n)) (Measure.map ι μ) :=
    ((configuration_eval_measurable f).norm.pow_const _).aestronglyMeasurable
  have hmeas_2 : AEStronglyMeasurable (fun (ω : Configuration (ContinuumTestFunction d)) =>
      |ω f| ^ (2 * ↑n)) (Measure.map ι μ) :=
    ((configuration_eval_measurable f).norm.pow_const _).aestronglyMeasurable
  -- LHS: ∫ |ω f|^{pn} d(map ι μ) = ∫ |(ι ω) f|^{pn} dμ(ω)
  rw [integral_map hι hmeas_p, integral_map hι hmeas_2]
  -- Step 2: Use latticeEmbedLift_eval_eq to rewrite (ι ω) f = ω g_f
  set g_f := latticeTestField d N a f
  have h_eval : ∀ ω : Configuration (FinLatticeField d N),
      (ι ω) f = ω g_f := fun ω => latticeEmbedLift_eval_eq d N a ha f ω
  simp_rw [h_eval]
  -- Step 3: Apply gaussian_hypercontractive from gaussian-field
  -- μ = GaussianField.measure (latticeCovariance d N a mass ha hmass)
  have h_μ : μ = measure (latticeCovariance d N a mass ha hmass) := rfl
  rw [h_μ]
  exact gaussian_hypercontractive (latticeCovariance d N a mass ha hmass) g_f n p hp m hm hp_eq

/-! ## Spectral preliminaries for the Wick-constant variance identity -/

private lemma massOperator_translation_commute (a mass : ℝ) (v : FinLatticeSites d N)
    (φ : FinLatticeField d N) :
    massOperator d N a mass (latticeTranslationFun d N v φ) =
    latticeTranslationFun d N v (massOperator d N a mass φ) := by
  have hΔ := finiteLaplacian_translation_commute d N a v φ
  ext x
  simp only [massOperator, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul, latticeTranslationFun]
  exact congrArg (fun t => -t + mass ^ 2 * φ (x - v)) (congr_fun hΔ x)

private lemma gaussianDensity_translation_invariant (a mass : ℝ) (v : FinLatticeSites d N)
    (φ : FinLatticeField d N) :
    gaussianDensity d N a mass (latticeTranslationFun d N v φ) =
    gaussianDensity d N a mass φ := by
  unfold gaussianDensity
  congr 1
  congr 1
  have hcomm := massOperator_translation_commute d N a mass v φ
  simp_rw [show ∀ x, massOperator d N a mass (latticeTranslationFun d N v φ) x =
    latticeTranslationFun d N v (massOperator d N a mass φ) x from fun x => congr_fun hcomm x]
  apply Fintype.sum_equiv (Equiv.subRight v)
  intro x
  rfl

private noncomputable def latticeTranslationEquiv (v : FinLatticeSites d N) :
    FinLatticeField d N ≃ᵐ FinLatticeField d N :=
  MeasurableEquiv.piCongrLeft (fun _ : FinLatticeSites d N => ℝ) (Equiv.addRight v)

omit [NeZero N] in
private lemma latticeTranslationEquiv_eq (v : FinLatticeSites d N) (φ : FinLatticeField d N) :
    latticeTranslationEquiv d N v φ = latticeTranslationFun d N v φ := by
  ext x
  change (Equiv.piCongrLeft (fun _ => ℝ) (Equiv.addRight v)) φ x = φ (x - v)
  conv_lhs => rw [show x = (Equiv.addRight v) (x - v) from (sub_add_cancel x v).symm]
  rw [Equiv.piCongrLeft_apply_apply]

private lemma latticeTranslation_volume_preserving (v : FinLatticeSites d N) :
    MeasurePreserving (latticeTranslationEquiv d N v)
      (volume : Measure (FinLatticeField d N)) volume :=
  volume_measurePreserving_piCongrLeft _ _

private lemma latticeField_second_moment_translation_invariant
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (x v : FinLatticeSites d N) :
    ∫ ω, (ω (finLatticeDelta d N (x + v))) ^ 2 ∂(latticeGaussianMeasure d N a mass ha hmass) =
      ∫ ω, (ω (finLatticeDelta d N x)) ^ 2 ∂(latticeGaussianMeasure d N a mass ha hmass) := by
  rw [show (∫ ω, (ω (finLatticeDelta d N (x + v))) ^ 2
      ∂(latticeGaussianMeasure d N a mass ha hmass)) =
      ∫ ω, (fun φ : FinLatticeField d N => φ (x + v) ^ 2) (evalMap d N ω)
        ∂(latticeGaussianMeasure d N a mass ha hmass) by
        simp [evalMap]]
  rw [show (∫ ω, (ω (finLatticeDelta d N x)) ^ 2
      ∂(latticeGaussianMeasure d N a mass ha hmass)) =
      ∫ ω, (fun φ : FinLatticeField d N => φ x ^ 2) (evalMap d N ω)
        ∂(latticeGaussianMeasure d N a mass ha hmass) by
        simp [evalMap]]
  rw [latticeGaussianMeasure_density_integral' d N a mass ha hmass
      (fun φ : FinLatticeField d N => φ (x + v) ^ 2)]
  rw [latticeGaussianMeasure_density_integral' d N a mass ha hmass
      (fun φ : FinLatticeField d N => φ x ^ 2)]
  congr 1
  let G : FinLatticeField d N → ℝ := fun φ => φ x ^ 2
  calc
    ∫ φ, φ (x + v) ^ 2 * gaussianDensity d N a mass φ
      = ∫ φ, G (latticeTranslationEquiv d N (-v) φ) *
          gaussianDensity d N a mass (latticeTranslationEquiv d N (-v) φ) := by
            refine integral_congr_ae (ae_of_all _ fun φ => ?_)
            dsimp [G]
            rw [latticeTranslationEquiv_eq (d := d) (N := N) (-v) φ]
            simp [latticeTranslationFun, gaussianDensity_translation_invariant]
    _ = ∫ φ, G φ * gaussianDensity d N a mass φ := by
          exact (latticeTranslation_volume_preserving d N (-v)).integral_comp'
            (fun ψ => G ψ * gaussianDensity d N a mass ψ)
    _ = ∫ φ, φ x ^ 2 * gaussianDensity d N a mass φ := rfl

private lemma latticeVariance_translation_invariant
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (x v : FinLatticeSites d N) :
    @inner ℝ ell2' _
      (latticeCovariance d N a mass ha hmass (finLatticeDelta d N (x + v)))
      (latticeCovariance d N a mass ha hmass (finLatticeDelta d N (x + v))) =
    @inner ℝ ell2' _
      (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x))
      (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x)) := by
  let μ := latticeGaussianMeasure d N a mass ha hmass
  calc
    @inner ℝ ell2' _
        (latticeCovariance d N a mass ha hmass (finLatticeDelta d N (x + v)))
        (latticeCovariance d N a mass ha hmass (finLatticeDelta d N (x + v)))
      = ∫ ω : Configuration (FinLatticeField d N),
          (ω (finLatticeDelta d N (x + v))) * (ω (finLatticeDelta d N (x + v))) ∂μ := by
            symm
            simpa [μ, GaussianField.covariance, sq] using
              (lattice_cross_moment d N a mass ha hmass
                (finLatticeDelta d N (x + v)) (finLatticeDelta d N (x + v)))
    _ = ∫ ω : Configuration (FinLatticeField d N),
          (ω (finLatticeDelta d N x)) * (ω (finLatticeDelta d N x)) ∂μ := by
            simpa [μ, sq] using
              (latticeField_second_moment_translation_invariant d N a mass ha hmass x v)
    _ = @inner ℝ ell2' _
        (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x))
        (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x)) := by
            simpa [μ, GaussianField.covariance, sq] using
              (lattice_cross_moment d N a mass ha hmass
                (finLatticeDelta d N x) (finLatticeDelta d N x))

private lemma delta_massEigenvectorCoeff (a mass : ℝ)
    (k x : FinLatticeSites d N) :
    (∑ y : FinLatticeSites d N,
      (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) y *
        finLatticeDelta d N x y) =
      (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x := by
  simp [finLatticeDelta]

private lemma massEigenvectorBasis_norm_sq_eq_one (a mass : ℝ) (k : FinLatticeSites d N) :
    ∑ x : FinLatticeSites d N,
      (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x ^ 2 = 1 := by
  have h_norm1 := (massEigenvectorBasis d N a mass).orthonormal.1 k
  simp only [EuclideanSpace.norm_eq] at h_norm1
  have hsq :
      ∑ x : FinLatticeSites d N,
          (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x ^ 2 =
        ∑ x : FinLatticeSites d N,
          ‖(massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x‖ ^ 2 := by
    congr 1
    ext x
    rw [Real.norm_eq_abs, sq_abs]
  rw [hsq]
  have hnonneg :
      0 ≤ ∑ x : FinLatticeSites d N,
        ‖(massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith [Real.sq_sqrt hnonneg]

private lemma latticeVariance_sum_eq_massEigenvalue_trace
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    ∑ x : FinLatticeSites d N,
      @inner ℝ ell2' _
        (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x))
        (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x)) =
      ∑ k : FinLatticeSites d N, (massEigenvalues d N a mass k)⁻¹ := by
  calc
    ∑ x : FinLatticeSites d N,
        @inner ℝ ell2' _
          (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x))
          (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x))
      = ∑ x : FinLatticeSites d N,
          ∑ k : FinLatticeSites d N,
            (massEigenvalues d N a mass k)⁻¹ *
              (∑ y : FinLatticeSites d N,
                (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) y *
                  finLatticeDelta d N x y) ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            simpa [latticeCovariance] using
              (spectralLatticeCovariance_norm_sq (d := d) (N := N) a mass ha hmass
                (finLatticeDelta d N x))
    _ = ∑ x : FinLatticeSites d N,
          ∑ k : FinLatticeSites d N,
            (massEigenvalues d N a mass k)⁻¹ *
              ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            refine Finset.sum_congr rfl ?_
            intro k hk
            rw [delta_massEigenvectorCoeff]
    _ = ∑ k : FinLatticeSites d N,
          (massEigenvalues d N a mass k)⁻¹ *
            ∑ x : FinLatticeSites d N,
              ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) ^ 2 := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro k hk
            rw [← Finset.mul_sum]
    _ = ∑ k : FinLatticeSites d N, (massEigenvalues d N a mass k)⁻¹ := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            rw [massEigenvectorBasis_norm_sq_eq_one]
            simp

private lemma latticeVariance_eq_massEigenvalue_average
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (x : FinLatticeSites d N) :
    @inner ℝ ell2' _
      (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x))
      (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x)) =
      (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
        ∑ k : FinLatticeSites d N, (massEigenvalues d N a mass k)⁻¹ := by
  have hconst : ∀ y : FinLatticeSites d N,
      @inner ℝ ell2' _
        (latticeCovariance d N a mass ha hmass (finLatticeDelta d N y))
        (latticeCovariance d N a mass ha hmass (finLatticeDelta d N y)) =
      @inner ℝ ell2' _
        (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x))
        (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x)) := by
    intro y
    simpa [sub_add_cancel] using
      (latticeVariance_translation_invariant d N a mass ha hmass x (y - x))
  have hsum := latticeVariance_sum_eq_massEigenvalue_trace d N a mass ha hmass
  have hcard_pos : (0 : ℝ) < Fintype.card (FinLatticeSites d N) := by
    exact_mod_cast Fintype.card_pos
  have hconst_sum :
      ∑ y : FinLatticeSites d N,
        @inner ℝ ell2' _
          (latticeCovariance d N a mass ha hmass (finLatticeDelta d N y))
          (latticeCovariance d N a mass ha hmass (finLatticeDelta d N y)) =
      (Fintype.card (FinLatticeSites d N) : ℝ) *
        @inner ℝ ell2' _
          (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x))
          (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x)) := by
    calc
      ∑ y : FinLatticeSites d N,
          @inner ℝ ell2' _
            (latticeCovariance d N a mass ha hmass (finLatticeDelta d N y))
            (latticeCovariance d N a mass ha hmass (finLatticeDelta d N y))
        = ∑ _y : FinLatticeSites d N,
            @inner ℝ ell2' _
              (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x))
              (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x)) := by
              refine Finset.sum_congr rfl ?_
              intro y hy
              exact hconst y
      _ = (Fintype.card (FinLatticeSites d N) : ℝ) *
            @inner ℝ ell2' _
              (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x))
              (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x)) := by
              simp
  calc
    @inner ℝ ell2' _
        (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x))
        (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x))
      = (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
          ((Fintype.card (FinLatticeSites d N) : ℝ) *
            @inner ℝ ell2' _
              (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x))
              (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x))) := by
            field_simp [ne_of_gt hcard_pos]
    _ = (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
          ∑ k : FinLatticeSites d N, (massEigenvalues d N a mass k)⁻¹ := by
            rw [← hconst_sum, hsum]

private lemma latticeVariance_eq_latticeEigenvalue1d_family_average
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (x : FinLatticeSites d N) :
    @inner ℝ ell2' _
      (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x))
      (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x)) =
      (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
        ∑ m : (Fin d → Fin N),
          ((∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2)⁻¹ := by
  have hconst : ∀ y : FinLatticeSites d N,
      @inner ℝ ell2' _
        (latticeCovariance d N a mass ha hmass (finLatticeDelta d N y))
        (latticeCovariance d N a mass ha hmass (finLatticeDelta d N y)) =
      @inner ℝ ell2' _
        (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x))
        (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x)) := by
    intro y
    simpa [sub_add_cancel] using
      (latticeVariance_translation_invariant d N a mass ha hmass x (y - x))
  have hcov :
      ∀ y : FinLatticeSites d N,
        @inner ℝ ell2' _
          (latticeCovariance d N a mass ha hmass (finLatticeDelta d N y))
          (latticeCovariance d N a mass ha hmass (finLatticeDelta d N y)) =
        ∑ m : (Fin d → Fin N),
          (latticeFourierProductBasisFun N d m y) ^ 2 /
            (((∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2) *
              latticeFourierProductNormSq N d m) := by
    intro y
    calc
      @inner ℝ ell2' _
          (latticeCovariance d N a mass ha hmass (finLatticeDelta d N y))
          (latticeCovariance d N a mass ha hmass (finLatticeDelta d N y))
        = GaussianField.covariance
            (latticeCovariance d N a mass ha hmass)
            (finLatticeDelta d N y) (finLatticeDelta d N y) := by
              rw [GaussianField.covariance]
      _ = ∑ m : (Fin d → Fin N),
            latticeFourierProductCoeff N d (finLatticeDelta d N y) m *
              latticeFourierProductCoeff N d (finLatticeDelta d N y) m /
              (((∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2) *
                latticeFourierProductNormSq N d m) := by
                  simpa using
                    (abstract_spectral_eq_dft_spectral_family (N := N) d a mass ha hmass
                      (finLatticeDelta d N y) (finLatticeDelta d N y))
      _ = ∑ m : (Fin d → Fin N),
            (latticeFourierProductBasisFun N d m y) ^ 2 /
              (((∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2) *
                latticeFourierProductNormSq N d m) := by
                  refine Finset.sum_congr rfl ?_
                  intro m hm
                  simp [latticeFourierProductCoeff, finLatticeDelta]
                  ring
  have hsum :
      ∑ y : FinLatticeSites d N,
        @inner ℝ ell2' _
          (latticeCovariance d N a mass ha hmass (finLatticeDelta d N y))
          (latticeCovariance d N a mass ha hmass (finLatticeDelta d N y)) =
      ∑ m : (Fin d → Fin N),
        ((∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2)⁻¹ := by
    calc
      ∑ y : FinLatticeSites d N,
          @inner ℝ ell2' _
            (latticeCovariance d N a mass ha hmass (finLatticeDelta d N y))
            (latticeCovariance d N a mass ha hmass (finLatticeDelta d N y))
        = ∑ y : FinLatticeSites d N,
            ∑ m : (Fin d → Fin N),
              (latticeFourierProductBasisFun N d m y) ^ 2 /
                (((∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2) *
                  latticeFourierProductNormSq N d m) := by
                    refine Finset.sum_congr rfl ?_
                    intro y hy
                    exact hcov y
      _ = ∑ m : (Fin d → Fin N),
            ∑ y : FinLatticeSites d N,
              (latticeFourierProductBasisFun N d m y) ^ 2 /
                (((∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2) *
                  latticeFourierProductNormSq N d m) := by
                    rw [Finset.sum_comm]
      _ = ∑ m : (Fin d → Fin N),
            (((∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2) *
              latticeFourierProductNormSq N d m)⁻¹ *
              ∑ y : FinLatticeSites d N, (latticeFourierProductBasisFun N d m y) ^ 2 := by
                  refine Finset.sum_congr rfl ?_
                  intro m hm
                  calc
                    ∑ y : FinLatticeSites d N,
                        (latticeFourierProductBasisFun N d m y) ^ 2 /
                          (((∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2) *
                            latticeFourierProductNormSq N d m)
                      = ∑ y : FinLatticeSites d N,
                          ((((∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2) *
                            latticeFourierProductNormSq N d m)⁻¹ *
                            (latticeFourierProductBasisFun N d m y) ^ 2) := by
                              refine Finset.sum_congr rfl ?_
                              intro y hy
                              ring
                    _ = (((∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2) *
                          latticeFourierProductNormSq N d m)⁻¹ *
                          ∑ y : FinLatticeSites d N,
                            (latticeFourierProductBasisFun N d m y) ^ 2 := by
                              rw [← Finset.mul_sum]
      _ = ∑ m : (Fin d → Fin N),
            ((∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2)⁻¹ := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              rw [latticeFourierProductBasis_sq_sum (N := N) d m]
              have hμ_pos :
                  0 < (∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2 := by
                have hsum_nonneg : 0 ≤ ∑ i : Fin d, latticeEigenvalue1d N a (m i) :=
                  Finset.sum_nonneg (fun i _ => latticeEigenvalue1d_nonneg N a (m i))
                positivity
              have hnorm_pos : 0 < latticeFourierProductNormSq N d m :=
                latticeFourierProductNormSq_pos (N := N) d m
              field_simp [ne_of_gt hμ_pos, ne_of_gt hnorm_pos]
  have hcard_pos : (0 : ℝ) < Fintype.card (FinLatticeSites d N) := by
    exact_mod_cast Fintype.card_pos
  have hconst_sum :
      ∑ y : FinLatticeSites d N,
        @inner ℝ ell2' _
          (latticeCovariance d N a mass ha hmass (finLatticeDelta d N y))
          (latticeCovariance d N a mass ha hmass (finLatticeDelta d N y)) =
      (Fintype.card (FinLatticeSites d N) : ℝ) *
        @inner ℝ ell2' _
          (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x))
          (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x)) := by
    calc
      ∑ y : FinLatticeSites d N,
          @inner ℝ ell2' _
            (latticeCovariance d N a mass ha hmass (finLatticeDelta d N y))
            (latticeCovariance d N a mass ha hmass (finLatticeDelta d N y))
        = ∑ _y : FinLatticeSites d N,
            @inner ℝ ell2' _
              (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x))
              (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x)) := by
                refine Finset.sum_congr rfl ?_
                intro y hy
                exact hconst y
      _ = (Fintype.card (FinLatticeSites d N) : ℝ) *
            @inner ℝ ell2' _
              (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x))
              (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x)) := by
                simp
  calc
    @inner ℝ ell2' _
        (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x))
        (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x))
      = (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
          ((Fintype.card (FinLatticeSites d N) : ℝ) *
            @inner ℝ ell2' _
              (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x))
              (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x))) := by
            field_simp [ne_of_gt hcard_pos]
    _ = (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
          ∑ m : (Fin d → Fin N),
            ((∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2)⁻¹ := by
              rw [← hconst_sum, hsum]

/-- **Wick constant = GFF variance at a site.**

The Wick ordering constant `c_a = (1/|Λ|) Σ_m λ_m⁻¹` equals the variance
of the field `ω(δ_x)` under the lattice Gaussian free field:
`wickConstant = ⟨T(δ_x), T(δ_x)⟩ = E[(ω(δ_x))²]`.

This follows from the spectral decomposition of the lattice covariance
+ Parseval identity (the Fourier eigenvectors satisfy `Σ_k |e_k(x)|² = 1`)
+ translation invariance (`G(x,x)` is independent of x).

Reference: Glimm-Jaffe §1.3, Simon §I.2. -/
theorem wickConstant_eq_variance (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (x : FinLatticeSites d N) :
    (wickConstant d N a mass : ℝ) =
    @inner ℝ ell2' _
      (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x))
      (latticeCovariance d N a mass ha hmass (finLatticeDelta d N x)) := by
  rw [wickConstant_eq_latticeEigenvalue1d_family_average (d := d) (N := N) a mass]
  exact (latticeVariance_eq_latticeEigenvalue1d_family_average (d := d) (N := N)
    a mass ha hmass x).symm

private noncomputable def finLatticeSitesTwoEquivProd :
    FinLatticeSites 2 N ≃ ZMod N × ZMod N where
  toFun x := (x 0, x 1)
  invFun p := fun i => Fin.cases p.1 (fun _ => p.2) i
  left_inv x := by
    ext i
    fin_cases i <;> rfl
  right_inv p := rfl

private lemma latticeFourierBasis_sq_sum_2d (m₁ m₂ : Fin N) :
    ∑ x : FinLatticeSites 2 N,
      (latticeFourierBasisFun N m₁ (x 0) * latticeFourierBasisFun N m₂ (x 1)) ^ 2 =
      latticeFourierNormSq N m₁ * latticeFourierNormSq N m₂ := by
  calc
    ∑ x : FinLatticeSites 2 N,
        (latticeFourierBasisFun N m₁ (x 0) * latticeFourierBasisFun N m₂ (x 1)) ^ 2
      = ∑ p : ZMod N × ZMod N,
          (latticeFourierBasisFun N m₁ p.1 * latticeFourierBasisFun N m₂ p.2) ^ 2 := by
            refine Fintype.sum_equiv (finLatticeSitesTwoEquivProd (N := N))
              (fun x : FinLatticeSites 2 N =>
                (latticeFourierBasisFun N m₁ (x 0) * latticeFourierBasisFun N m₂ (x 1)) ^ 2)
              (fun p : ZMod N × ZMod N =>
                (latticeFourierBasisFun N m₁ p.1 * latticeFourierBasisFun N m₂ p.2) ^ 2) ?_
            intro x
            rfl
    _ = ∑ p : ZMod N × ZMod N,
          (latticeFourierBasisFun N m₁ p.1) ^ 2 * (latticeFourierBasisFun N m₂ p.2) ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            ring
    _ = (∑ z : ZMod N, latticeFourierBasisFun N m₁ z ^ 2) *
          ∑ z : ZMod N, latticeFourierBasisFun N m₂ z ^ 2 := by
            rw [Fintype.sum_prod_type]
            symm
            exact Fintype.sum_mul_sum _ _
    _ = latticeFourierNormSq N m₁ * latticeFourierNormSq N m₂ := by
            rw [latticeFourierNormSq, latticeFourierNormSq]

private lemma latticeVariance_eq_dft_eigenvalue_average
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (x : FinLatticeSites 2 N) :
    @inner ℝ ell2' _
      (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N x))
      (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N x)) =
      (1 / Fintype.card (FinLatticeSites 2 N) : ℝ) *
        ∑ m₁ : Fin N, ∑ m₂ : Fin N,
          (latticeEigenvalue1d N a m₁ + latticeEigenvalue1d N a m₂ + mass ^ 2)⁻¹ := by
  have hconst : ∀ y : FinLatticeSites 2 N,
      @inner ℝ ell2' _
        (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N y))
        (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N y)) =
      @inner ℝ ell2' _
        (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N x))
        (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N x)) := by
    intro y
    simpa [sub_add_cancel] using
      (latticeVariance_translation_invariant (d := 2) (N := N) a mass ha hmass x (y - x))
  have hcov :
      ∀ y : FinLatticeSites 2 N,
        @inner ℝ ell2' _
          (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N y))
          (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N y)) =
        ∑ m₁ : Fin N, ∑ m₂ : Fin N,
          ((latticeFourierBasisFun N m₁ (y 0) * latticeFourierBasisFun N m₂ (y 1)) ^ 2) /
            ((latticeEigenvalue1d N a m₁ + latticeEigenvalue1d N a m₂ + mass ^ 2) *
              latticeFourierNormSq N m₁ * latticeFourierNormSq N m₂) := by
    intro y
    calc
      @inner ℝ ell2' _
          (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N y))
          (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N y))
        = GaussianField.covariance
            (latticeCovariance 2 N a mass ha hmass)
            (finLatticeDelta 2 N y) (finLatticeDelta 2 N y) := by
              rw [GaussianField.covariance]
      _ = ∑ m₁ : Fin N, ∑ m₂ : Fin N,
            (latticeFourierBasisFun N m₁ (y 0) * latticeFourierBasisFun N m₂ (y 1)) *
              (latticeFourierBasisFun N m₁ (y 0) * latticeFourierBasisFun N m₂ (y 1)) /
              ((latticeEigenvalue1d N a m₁ + latticeEigenvalue1d N a m₂ + mass ^ 2) *
                latticeFourierNormSq N m₁ * latticeFourierNormSq N m₂) := by
                  simpa [finLatticeDelta] using
                    (abstract_spectral_eq_dft_spectral_2d (N := N) a mass ha hmass
                      (finLatticeDelta 2 N y) (finLatticeDelta 2 N y))
      _ = ∑ m₁ : Fin N, ∑ m₂ : Fin N,
            ((latticeFourierBasisFun N m₁ (y 0) * latticeFourierBasisFun N m₂ (y 1)) ^ 2) /
              ((latticeEigenvalue1d N a m₁ + latticeEigenvalue1d N a m₂ + mass ^ 2) *
                latticeFourierNormSq N m₁ * latticeFourierNormSq N m₂) := by
                  refine Finset.sum_congr rfl ?_
                  intro m₁ hm₁
                  refine Finset.sum_congr rfl ?_
                  intro m₂ hm₂
                  ring
  have hsum :
      ∑ y : FinLatticeSites 2 N,
        @inner ℝ ell2' _
          (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N y))
          (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N y)) =
      ∑ m₁ : Fin N, ∑ m₂ : Fin N,
        (latticeEigenvalue1d N a m₁ + latticeEigenvalue1d N a m₂ + mass ^ 2)⁻¹ := by
    calc
      ∑ y : FinLatticeSites 2 N,
          @inner ℝ ell2' _
            (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N y))
            (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N y))
        = ∑ y : FinLatticeSites 2 N,
            ∑ m₁ : Fin N, ∑ m₂ : Fin N,
              ((latticeFourierBasisFun N m₁ (y 0) * latticeFourierBasisFun N m₂ (y 1)) ^ 2) /
                ((latticeEigenvalue1d N a m₁ + latticeEigenvalue1d N a m₂ + mass ^ 2) *
                  latticeFourierNormSq N m₁ * latticeFourierNormSq N m₂) := by
                    refine Finset.sum_congr rfl ?_
                    intro y hy
                    exact hcov y
      _ = ∑ m₁ : Fin N, ∑ m₂ : Fin N,
            ∑ y : FinLatticeSites 2 N,
              ((latticeFourierBasisFun N m₁ (y 0) * latticeFourierBasisFun N m₂ (y 1)) ^ 2) /
                ((latticeEigenvalue1d N a m₁ + latticeEigenvalue1d N a m₂ + mass ^ 2) *
                  latticeFourierNormSq N m₁ * latticeFourierNormSq N m₂) := by
                    rw [Finset.sum_comm]
                    refine Finset.sum_congr rfl ?_
                    intro m₁ hm₁
                    rw [Finset.sum_comm]
      _ = ∑ m₁ : Fin N, ∑ m₂ : Fin N,
            ((latticeEigenvalue1d N a m₁ + latticeEigenvalue1d N a m₂ + mass ^ 2) *
              latticeFourierNormSq N m₁ * latticeFourierNormSq N m₂)⁻¹ *
              ∑ y : FinLatticeSites 2 N,
                ((latticeFourierBasisFun N m₁ (y 0) * latticeFourierBasisFun N m₂ (y 1)) ^ 2) := by
                    refine Finset.sum_congr rfl ?_
                    intro m₁ hm₁
                    refine Finset.sum_congr rfl ?_
                    intro m₂ hm₂
                    calc
                      ∑ y : FinLatticeSites 2 N,
                          ((latticeFourierBasisFun N m₁ (y 0) *
                              latticeFourierBasisFun N m₂ (y 1)) ^ 2) /
                            ((latticeEigenvalue1d N a m₁ + latticeEigenvalue1d N a m₂ + mass ^ 2) *
                              latticeFourierNormSq N m₁ * latticeFourierNormSq N m₂)
                        = ∑ y : FinLatticeSites 2 N,
                            (((latticeEigenvalue1d N a m₁ + latticeEigenvalue1d N a m₂ + mass ^ 2) *
                              latticeFourierNormSq N m₁ * latticeFourierNormSq N m₂)⁻¹ *
                              ((latticeFourierBasisFun N m₁ (y 0) *
                                latticeFourierBasisFun N m₂ (y 1)) ^ 2)) := by
                                  refine Finset.sum_congr rfl ?_
                                  intro y hy
                                  ring
                      _ = ((latticeEigenvalue1d N a m₁ + latticeEigenvalue1d N a m₂ + mass ^ 2) *
                            latticeFourierNormSq N m₁ * latticeFourierNormSq N m₂)⁻¹ *
                            ∑ y : FinLatticeSites 2 N,
                              ((latticeFourierBasisFun N m₁ (y 0) *
                                latticeFourierBasisFun N m₂ (y 1)) ^ 2) := by
                                  rw [← Finset.mul_sum]
      _ = ∑ m₁ : Fin N, ∑ m₂ : Fin N,
            (latticeEigenvalue1d N a m₁ + latticeEigenvalue1d N a m₂ + mass ^ 2)⁻¹ := by
              refine Finset.sum_congr rfl ?_
              intro m₁ hm₁
              refine Finset.sum_congr rfl ?_
              intro m₂ hm₂
              rw [latticeFourierBasis_sq_sum_2d]
              have hμ_pos :
                  0 < latticeEigenvalue1d N a m₁ + latticeEigenvalue1d N a m₂ + mass ^ 2 := by
                have hm₁_nonneg := latticeEigenvalue1d_nonneg N a m₁
                have hm₂_nonneg := latticeEigenvalue1d_nonneg N a m₂
                positivity
              have hnorm₁_pos : 0 < latticeFourierNormSq N m₁ :=
                latticeFourierNormSq_pos N m₁ m₁.isLt
              have hnorm₂_pos : 0 < latticeFourierNormSq N m₂ :=
                latticeFourierNormSq_pos N m₂ m₂.isLt
              field_simp [ne_of_gt hμ_pos, ne_of_gt hnorm₁_pos, ne_of_gt hnorm₂_pos]
  have hcard_pos : (0 : ℝ) < Fintype.card (FinLatticeSites 2 N) := by
    exact_mod_cast Fintype.card_pos
  have hconst_sum :
      ∑ y : FinLatticeSites 2 N,
        @inner ℝ ell2' _
          (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N y))
          (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N y)) =
      (Fintype.card (FinLatticeSites 2 N) : ℝ) *
        @inner ℝ ell2' _
          (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N x))
          (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N x)) := by
    calc
      ∑ y : FinLatticeSites 2 N,
          @inner ℝ ell2' _
            (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N y))
            (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N y))
        = ∑ _y : FinLatticeSites 2 N,
            @inner ℝ ell2' _
              (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N x))
              (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N x)) := by
                refine Finset.sum_congr rfl ?_
                intro y hy
                exact hconst y
      _ = (Fintype.card (FinLatticeSites 2 N) : ℝ) *
            @inner ℝ ell2' _
              (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N x))
              (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N x)) := by
                simp
  calc
    @inner ℝ ell2' _
        (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N x))
        (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N x))
      = (1 / Fintype.card (FinLatticeSites 2 N) : ℝ) *
          ((Fintype.card (FinLatticeSites 2 N) : ℝ) *
            @inner ℝ ell2' _
              (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N x))
              (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N x))) := by
            field_simp [ne_of_gt hcard_pos]
    _ = (1 / Fintype.card (FinLatticeSites 2 N) : ℝ) *
          ∑ m₁ : Fin N, ∑ m₂ : Fin N,
            (latticeEigenvalue1d N a m₁ + latticeEigenvalue1d N a m₂ + mass ^ 2)⁻¹ := by
              rw [← hconst_sum, hsum]

/-- In two dimensions, the Wick ordering constant equals the site variance of
the lattice Gaussian free field. -/
theorem wickConstant_eq_variance_two_dim
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (x : FinLatticeSites 2 N) :
    (wickConstant 2 N a mass : ℝ) =
      @inner ℝ ell2' _
        (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N x))
        (latticeCovariance 2 N a mass ha hmass (finLatticeDelta 2 N x)) := by
  rw [wickConstant_two_eq_dft_eigenvalue_average (N := N) a mass]
  exact (latticeVariance_eq_dft_eigenvalue_average (N := N) a mass ha hmass x).symm

/-! ## Textbook axioms

These axioms replace the compound axioms `exponential_moment_bound` and
`interactionFunctional_mean_nonpos` with cleaner, elementary statements. -/

/-- **Hermite orthogonality for the lattice Gaussian measure.**

Wick monomials `:x^n:_c` of order n ≥ 1 have zero mean under the Gaussian
measure with matching variance parameter c = wickConstant. This combines:
1. `wickConstant_eq_variance`: the variance of `ω(δ_x)` equals `wickConstant`
2. `pairing_is_gaussian`: the marginal of `ω(δ_x)` is `N(0, wickConstant)`
3. `gaussian_hermite_zero_mean`: Hermite orthogonality for 1D Gaussians

Also states integrability (polynomial of a Gaussian random variable).

Reference: Simon (1974), §I.3; Glimm-Jaffe (1987), §1.3. -/
theorem wickMonomial_latticeGaussian (d N : ℕ) [NeZero N]
    (n : ℕ) (hn : 1 ≤ n) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (x : FinLatticeSites d N) :
    Integrable (fun ω : Configuration (FinLatticeField d N) =>
        wickMonomial n (wickConstant d N a mass) (ω (finLatticeDelta d N x)))
      (latticeGaussianMeasure d N a mass ha hmass) ∧
    ∫ ω, wickMonomial n (wickConstant d N a mass) (ω (finLatticeDelta d N x))
      ∂(latticeGaussianMeasure d N a mass ha hmass) = 0 := by
  set μ := latticeGaussianMeasure d N a mass ha hmass
  set T := latticeCovariance d N a mass ha hmass
  set δx := finLatticeDelta d N x
  set c := wickConstant d N a mass
  have hc_pos : 0 < c := wickConstant_pos d N a mass ha hmass
  -- wickConstant = ‖T(δ_x)‖²
  have h_var := wickConstant_eq_variance d N a mass ha hmass x
  -- The marginal of ω(δ_x) under μ_GFF is N(0, wickConstant)
  have h_gauss : μ.map (fun ω : Configuration (FinLatticeField d N) => ω δx) =
      ProbabilityTheory.gaussianReal 0 (c : ℝ).toNNReal := by
    have := GaussianField.pairing_is_gaussian T δx
    rwa [show @inner ℝ ell2' _ (T δx) (T δx) = c from h_var.symm] at this
  have h_meas_eval : Measurable (fun ω : Configuration (FinLatticeField d N) => ω δx) :=
    configuration_eval_measurable δx
  -- 1D Hermite orthogonality under N(0, c)
  obtain ⟨h_int_1d, h_zero_1d⟩ := gaussian_hermite_zero_mean c hc_pos n hn
  -- Key: the composition (wickMonomial n c) ∘ (eval δx) is the integrand
  set g := fun t : ℝ => wickMonomial n c t
  have hg_comp : (fun ω : Configuration (FinLatticeField d N) =>
      wickMonomial n c (ω δx)) = g ∘ (fun ω => ω δx) := rfl
  -- g integrable under pushforward = N(0,c)
  have h_int_push : Integrable g (μ.map (fun ω => ω δx)) := h_gauss ▸ h_int_1d
  constructor
  · -- Integrability: pull back through the pushforward
    rw [hg_comp]
    exact h_int_push.comp_measurable h_meas_eval
  · -- Integral = 0: ∫ g(ω δx) dμ = ∫ g d(pushforward) = ∫ g d N(0,c) = 0
    rw [hg_comp]
    rw [show ∫ x_1, (g ∘ fun ω => ω δx) x_1 ∂μ =
      ∫ t, g t ∂(μ.map (fun ω => ω δx)) from
      (integral_map h_meas_eval.aemeasurable h_int_push.aestronglyMeasurable).symm]
    rw [h_gauss, h_zero_1d]

-- `wickPolynomial_uniform_bounded_below` is proved in WickPolynomial.lean

/-! ## Step A2: Exponential moment bound for the interaction -/

/-- **Exponential moment bound** for the Wick-ordered interaction.

The Boltzmann weight exp(-V_a) has uniformly bounded L² norm w.r.t. the
Gaussian free field measure:

  ∫ exp(-2·V_a(φ)) dμ_{GFF}(φ) ≤ K

for all a ∈ (0, 1], where K depends on the polynomial P and mass m
but not on a.

Proof: On a fixed lattice (d, N fixed), the wickConstant ≤ mass⁻², so
by `wickPolynomial_uniform_bounded_below`, V_a(ω) ≥ -(a^d · |Λ| · A).
For a ≤ 1, exp(-2V) ≤ exp(2 · |Λ| · A). Integrating over the probability
measure gives K = exp(2 · |Λ| · A).

Note: In the full continuum limit (N ~ 1/a → ∞), this simple argument
fails and one needs cluster expansions (Simon §V.1, Glimm-Jaffe §19.1).
For fixed (d, N), the bound is elementary. -/
theorem exponential_moment_bound (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ (K : ℝ), 0 < K ∧
    ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
    ∫ ω : Configuration (FinLatticeField d N),
        (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2
        ∂(latticeGaussianMeasure d N a mass ha hmass) ≤ K := by
  -- Step 1: Get uniform lower bound on wickPolynomial for c ∈ [0, mass⁻²]
  obtain ⟨A, hA_pos, hA_bound⟩ :=
    Pphi2.wickPolynomial_uniform_bounded_below P (mass⁻¹ ^ 2) (by positivity)
  -- Step 2: K = exp(2 · |Λ| · A) works uniformly
  set Λ := Fintype.card (FinLatticeSites d N)
  refine ⟨Real.exp (2 * ↑Λ * A), Real.exp_pos _, fun a ha ha1 => ?_⟩
  set μ := latticeGaussianMeasure d N a mass ha hmass
  haveI : IsProbabilityMeasure μ := latticeGaussianMeasure_isProbability d N a mass ha hmass
  -- Step 3: V(ω) ≥ -(a^d · |Λ| · A) for all ω
  have hc_nn : 0 ≤ wickConstant d N a mass :=
    le_of_lt (wickConstant_pos d N a mass ha hmass)
  have hc_le : wickConstant d N a mass ≤ mass⁻¹ ^ 2 :=
    wickConstant_le_inv_mass_sq d N a mass ha hmass
  have h_wp_bound : ∀ (ω : Configuration (FinLatticeField d N)),
      interactionFunctional d N P a mass ω ≥ -(↑Λ * A) := by
    intro ω
    unfold interactionFunctional
    have ha_pow : (0 : ℝ) ≤ a ^ d := pow_nonneg (le_of_lt ha) d
    calc a ^ d * ∑ x : FinLatticeSites d N,
          wickPolynomial P (wickConstant d N a mass) (ω (finLatticeDelta d N x))
        ≥ a ^ d * ∑ _x : FinLatticeSites d N, (-A) := by
          apply mul_le_mul_of_nonneg_left _ ha_pow
          exact Finset.sum_le_sum fun x _ => hA_bound _ hc_nn hc_le _
      _ = a ^ d * (-(↑Λ * A)) := by
          congr 1; rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
      _ ≥ -(↑Λ * A) := by
          have had : a ^ d ≤ 1 := pow_le_one₀ (le_of_lt ha) ha1
          nlinarith [mul_nonneg (Nat.cast_nonneg' Λ) (le_of_lt hA_pos)]
  -- Step 4: exp(-2V) ≤ exp(2 · |Λ| · A) pointwise
  have h_exp_bound : ∀ ω, (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2 ≤
      Real.exp (2 * ↑Λ * A) := by
    intro ω
    -- (exp x)^2 = exp(2x)
    rw [sq, ← Real.exp_add, show -interactionFunctional d N P a mass ω +
        (-interactionFunctional d N P a mass ω) =
        -2 * interactionFunctional d N P a mass ω from by ring]
    exact Real.exp_le_exp_of_le (by linarith [h_wp_bound ω])
  -- Step 5: Integrate the pointwise bound
  calc ∫ ω, (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2 ∂μ
      ≤ ∫ _ω, Real.exp (2 * ↑Λ * A) ∂μ := by
        apply integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _)
          (integrable_const _) (ae_of_all _ h_exp_bound)
    _ = Real.exp (2 * ↑Λ * A) := by
        simp [integral_const]

/-! ## Step A3: Cauchy-Schwarz density transfer -/

/-- Helper: integrability and integral computation for a single-site
Wick polynomial under the lattice Gaussian.

`∫ :P(ω(δ_x)):_c dμ_{GFF} = P.coeff₀` because all Wick monomials of
order ≥ 1 have zero Gaussian mean, and `:x^0:_c = 1`. -/
private lemma wickPolynomial_integral_eq_coeff_zero
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (x : FinLatticeSites d N) :
    Integrable (fun ω : Configuration (FinLatticeField d N) =>
        wickPolynomial P (wickConstant d N a mass) (ω (finLatticeDelta d N x)))
      (latticeGaussianMeasure d N a mass ha hmass) ∧
    ∫ ω, wickPolynomial P (wickConstant d N a mass) (ω (finLatticeDelta d N x))
      ∂(latticeGaussianMeasure d N a mass ha hmass) = P.coeff ⟨0, by have := P.hn_ge; omega⟩ := by
  set μ := latticeGaussianMeasure d N a mass ha hmass
  set c := wickConstant d N a mass
  set δx := finLatticeDelta d N x
  haveI : IsProbabilityMeasure μ := latticeGaussianMeasure_isProbability d N a mass ha hmass
  -- Integrability of each term
  have h_lead_int : Integrable (fun ω : Configuration (FinLatticeField d N) =>
      (1 / P.n : ℝ) * wickMonomial P.n c (ω δx)) μ :=
    (wickMonomial_latticeGaussian d N P.n (by have := P.hn_ge; omega)
      a mass ha hmass x).1.const_mul _
  have h_term_int : ∀ m : Fin P.n, Integrable (fun ω : Configuration (FinLatticeField d N) =>
      P.coeff m * wickMonomial (m : ℕ) c (ω δx)) μ := by
    intro m
    by_cases hm : (m : ℕ) = 0
    · have : (fun ω : Configuration (FinLatticeField d N) =>
          P.coeff m * wickMonomial (m : ℕ) c (ω δx)) = fun _ => P.coeff m := by
        ext ω; simp [hm]
      rw [this]; exact integrable_const _
    · exact ((wickMonomial_latticeGaussian d N m (by omega) a mass ha hmass x).1).const_mul _
  have h_sum_int : Integrable (fun ω : Configuration (FinLatticeField d N) =>
      ∑ m : Fin P.n, P.coeff m * wickMonomial (m : ℕ) c (ω δx)) μ :=
    integrable_finset_sum _ fun m _ => h_term_int m
  constructor
  · -- Integrability of wickPolynomial = leading + sum
    change Integrable (fun ω => (1 / P.n : ℝ) * wickMonomial P.n c (ω δx) +
      ∑ m : Fin P.n, P.coeff m * wickMonomial (m : ℕ) c (ω δx)) μ
    exact h_lead_int.add h_sum_int
  · -- Integral = P.coeff 0
    change ∫ ω, ((1 / P.n : ℝ) * wickMonomial P.n c (ω δx) +
      ∑ m : Fin P.n, P.coeff m * wickMonomial (m : ℕ) c (ω δx)) ∂μ = _
    rw [integral_add h_lead_int h_sum_int,
        integral_const_mul,
        (wickMonomial_latticeGaussian d N P.n (by have := P.hn_ge; omega)
          a mass ha hmass x).2,
        mul_zero, zero_add,
        integral_finset_sum _ (fun m _ => h_term_int m)]
    simp_rw [integral_const_mul]
    -- Each integral: ∫ wM_m = 1 if m=0, 0 if m≥1
    have h_wm_eval : ∀ m : Fin P.n,
        ∫ ω, wickMonomial (↑m) c (ω δx) ∂μ = if (m : ℕ) = 0 then 1 else 0 := by
      intro m
      by_cases hm : (m : ℕ) = 0
      · simp_rw [if_pos hm, hm, wickMonomial_zero]
        simp [integral_const]
      · rw [if_neg hm, (wickMonomial_latticeGaussian d N m (by omega) a mass ha hmass x).2]
    simp_rw [h_wm_eval, mul_ite, mul_one, mul_zero]
    -- ∑ (if m.val = 0 then coeff m else 0) = coeff ⟨0, _⟩
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    -- The filter picks out exactly ⟨0, _⟩
    have : Finset.univ.filter (fun m : Fin P.n => (m : ℕ) = 0) =
        {⟨0, by have := P.hn_ge; omega⟩} := by
      ext m; simp [Fin.ext_iff]
    rw [this, Finset.sum_singleton]

/-- **Wick ordering mean property**: the mean of the interaction functional
under the GFF is nonpositive.

`∫ V dμ_{GFF} = a^d · |Λ| · P.coeff₀ ≤ 0` since `P.coeff₀ ≤ 0`.

Proved from `wickMonomial_latticeGaussian` (Hermite orthogonality),
`wickMonomial 0 c x = 1`, and `P.coeff_zero_nonpos`.

Reference: Simon (1974), §I.3; Glimm-Jaffe (1987), §1.3. -/
theorem interactionFunctional_mean_nonpos (d N : ℕ) [NeZero N]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Integrable (interactionFunctional d N P a mass)
      (latticeGaussianMeasure d N a mass ha hmass) ∧
    ∫ ω, interactionFunctional d N P a mass ω
      ∂(latticeGaussianMeasure d N a mass ha hmass) ≤ 0 := by
  set μ := latticeGaussianMeasure d N a mass ha hmass
  haveI : IsProbabilityMeasure μ := latticeGaussianMeasure_isProbability d N a mass ha hmass
  -- Get per-site integrability and integral from helper
  have h_site : ∀ x : FinLatticeSites d N,
      Integrable (fun ω : Configuration (FinLatticeField d N) =>
        wickPolynomial P (wickConstant d N a mass) (ω (finLatticeDelta d N x))) μ ∧
      ∫ ω, wickPolynomial P (wickConstant d N a mass) (ω (finLatticeDelta d N x)) ∂μ =
        P.coeff ⟨0, by have := P.hn_ge; omega⟩ :=
    fun x => wickPolynomial_integral_eq_coeff_zero d N P a mass ha hmass x
  set c := wickConstant d N a mass
  -- Integrability of each site term
  have h_wp_int : ∀ x : FinLatticeSites d N,
      Integrable (fun ω : Configuration (FinLatticeField d N) =>
        wickPolynomial P c (ω (finLatticeDelta d N x))) μ := fun x => (h_site x).1
  constructor
  · -- Integrability of V = a^d * Σ_x wP(ω(δ_x))
    unfold interactionFunctional
    exact (integrable_finset_sum _ fun x _ => h_wp_int x).const_mul _
  · -- Mean ≤ 0: ∫ V = a^d * |Λ| * P.coeff 0 ≤ 0
    unfold interactionFunctional
    rw [integral_const_mul, integral_finset_sum _ (fun x _ => h_wp_int x)]
    simp_rw [(h_site _).2, Finset.sum_const, nsmul_eq_mul]
    apply mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (le_of_lt ha) d)
    exact mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast Fintype.card_pos.le)
      P.coeff_zero_nonpos

/-- **Partition function lower bound**: Z_a ≥ 1 for all a.

Proved from Jensen's inequality (`ConvexOn.map_integral_le`) applied to
the convex function `exp` and `f = -V`:

  Z = ∫ exp(-V) dμ_{GFF} ≥ exp(-∫ V dμ_{GFF}) ≥ exp(0) = 1

The second inequality uses `interactionFunctional_mean_nonpos`. -/
theorem partitionFunction_ge_one (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) (a : ℝ) (ha : 0 < a) :
    1 ≤ partitionFunction d N P a mass ha hmass := by
  set μ := latticeGaussianMeasure d N a mass ha hmass
  set V := interactionFunctional d N P a mass
  haveI : IsProbabilityMeasure μ := latticeGaussianMeasure_isProbability d N a mass ha hmass
  obtain ⟨hV_int, hV_mean⟩ := interactionFunctional_mean_nonpos d N P a mass ha hmass
  -- Jensen's inequality: exp(∫ -V dμ) ≤ ∫ exp(-V) dμ = Z
  have h_jensen : Real.exp (∫ ω, (-V ω) ∂μ) ≤ ∫ ω, Real.exp (-V ω) ∂μ := by
    have h_conv := convexOn_exp
    have h_cont := Real.continuous_exp.continuousOn (s := Set.univ)
    have h_closed := isClosed_univ (X := ℝ)
    have h_mem : ∀ᵐ ω ∂μ, (-V ω) ∈ Set.univ := ae_of_all _ (fun _ => Set.mem_univ _)
    have h_neg_int : Integrable (fun ω => -V ω) μ := hV_int.neg
    have h_exp_int : Integrable (fun ω => Real.exp (-V ω)) μ :=
      boltzmannWeight_integrable d N P a mass ha hmass
    exact h_conv.map_integral_le h_cont h_closed h_mem h_neg_int h_exp_int
  -- ∫ -V dμ = -(∫ V dμ) ≥ 0
  have h_neg_mean : 0 ≤ ∫ ω, (-V ω) ∂μ := by
    rw [integral_neg]; linarith
  -- Chain: 1 = exp(0) ≤ exp(∫ -V) ≤ Z
  calc (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
    _ ≤ Real.exp (∫ ω, (-V ω) ∂μ) := Real.exp_le_exp_of_le h_neg_mean
    _ ≤ ∫ ω, Real.exp (-V ω) ∂μ := h_jensen
    _ = partitionFunction d N P a mass ha hmass := rfl

/-- **Cauchy-Schwarz density transfer bound**: any nonneg integrable function F
satisfies ∫ F dμ_int ≤ K^{1/2} · (∫ F² dμ_GFF)^{1/2}, where K is the
exponential moment bound.

This combines three facts:
1. Density transfer: ∫ F dμ_int = Z⁻¹ ∫ F·bw dμ_GFF
2. Cauchy-Schwarz:   ∫ F·bw ≤ (∫ F²)^{1/2} · (∫ bw²)^{1/2}
3. Z ≥ 1 and ∫ bw² ≤ K give Z⁻¹·(∫ bw²)^{1/2} ≤ K^{1/2} -/
lemma density_transfer_bound
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (K : ℝ) (_hK_pos : 0 < K)
    (hK : ∫ ω : Configuration (FinLatticeField d N),
        (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2
        ∂(latticeGaussianMeasure d N a mass ha hmass) ≤ K)
    (hZ : 1 ≤ partitionFunction d N P a mass ha hmass)
    (F : Configuration (FinLatticeField d N) → ℝ)
    (hF_nn : ∀ ω, 0 ≤ F ω)
    (hF_meas : AEStronglyMeasurable F (latticeGaussianMeasure d N a mass ha hmass))
    (hF_sq_int : Integrable (fun ω => F ω ^ 2) (latticeGaussianMeasure d N a mass ha hmass)) :
    ∫ ω, F ω ∂(interactingLatticeMeasure d N P a mass ha hmass) ≤
    K ^ (1 / 2 : ℝ) *
    (∫ ω, F ω ^ (2 : ℝ) ∂(latticeGaussianMeasure d N a mass ha hmass)) ^ (1 / 2 : ℝ) := by
  set μ_GFF := latticeGaussianMeasure d N a mass ha hmass
  set bw := boltzmannWeight d N P a mass
  set V := interactionFunctional d N P a mass
  set Z := partitionFunction d N P a mass ha hmass
  have hZ_pos : 0 < Z := partitionFunction_pos d N P a mass ha hmass
  -- ENNReal infrastructure
  have hZ_ennreal_ne_zero : ENNReal.ofReal Z ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hZ_pos).ne'
  have hc_ne_zero : (ENNReal.ofReal Z)⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have hc_ne_top : (ENNReal.ofReal Z)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr hZ_ennreal_ne_zero
  -- Density measurability
  have hbw_meas : Measurable bw :=
    (interactionFunctional_measurable d N P a mass).neg.exp
  set bw_nn := fun ω : Configuration (FinLatticeField d N) => Real.toNNReal (bw ω)
  have hbw_nn_meas : Measurable bw_nn :=
    Measurable.real_toNNReal hbw_meas
  -- Step 1: Unfold interacting measure to weighted Gaussian integral
  -- ∫ F dμ_int = Z⁻¹ * ∫ bw * F dμ_GFF
  unfold interactingLatticeMeasure
  rw [integral_smul_measure]
  have wd_eq : ∫ ω, F ω ∂(μ_GFF.withDensity (fun ω => ENNReal.ofReal (bw ω))) =
      ∫ ω, bw ω * F ω ∂μ_GFF := by
    change ∫ ω, F ω ∂(μ_GFF.withDensity (fun ω => ↑(bw_nn ω))) =
      ∫ ω, bw ω * F ω ∂μ_GFF
    rw [integral_withDensity_eq_integral_smul hbw_nn_meas]
    congr 1; ext ω
    simp only [bw_nn, NNReal.smul_def, smul_eq_mul]
    rw [Real.coe_toNNReal _ (le_of_lt (boltzmannWeight_pos d N P a mass ω))]
  rw [wd_eq]
  have hc_real : ((ENNReal.ofReal Z)⁻¹).toReal = Z⁻¹ := by
    simp [ENNReal.toReal_inv, ENNReal.toReal_ofReal (le_of_lt hZ_pos)]
  rw [hc_real]
  -- Goal: Z⁻¹ * ∫ bw * F dμ_GFF ≤ K^{1/2} * (∫ F^2 dμ_GFF)^{1/2}
  -- Step 2: Cauchy-Schwarz + bounds
  -- ∫ bw*F ≤ (∫ bw²)^{1/2} * (∫ F²)^{1/2}   [CS]
  -- Z⁻¹ ≤ 1                                    [Z ≥ 1]
  -- (∫ bw²)^{1/2} ≤ K^{1/2}                   [exponential moment bound]
  -- Construct MemLp instances for Cauchy-Schwarz
  -- bw bounded above from interactionFunctional_bounded_below
  obtain ⟨B, hB⟩ := interactionFunctional_bounded_below d N P a mass ha hmass
  have hbw_bound : ∀ ω, bw ω ≤ Real.exp B := fun ω =>
    Real.exp_le_exp_of_le (by linarith [hB ω])
  haveI : IsProbabilityMeasure μ_GFF :=
    latticeGaussianMeasure_isProbability d N a mass ha hmass
  have hbw_sq_int : Integrable (fun ω => bw ω ^ 2) μ_GFF :=
    Integrable.of_bound (hbw_meas.pow_const 2).aestronglyMeasurable (Real.exp B ^ 2)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact sq_le_sq'
          (by linarith [boltzmannWeight_pos d N P a mass ω, Real.exp_pos B])
          (hbw_bound ω))
  have hbw_memLp : MemLp bw 2 μ_GFF :=
    (memLp_two_iff_integrable_sq hbw_meas.aestronglyMeasurable).mpr hbw_sq_int
  have hF_memLp : MemLp F 2 μ_GFF :=
    (memLp_two_iff_integrable_sq hF_meas).mpr hF_sq_int
  -- Apply Cauchy-Schwarz (Hölder with p = q = 2)
  -- integral_mul_le_Lp_mul_Lq_of_nonneg with HolderConjugate.two_two
  -- gives ∫ bw*F ≤ (∫ bw²)^{1/2} * (∫ F²)^{1/2}
  have h_cs : ∫ ω, bw ω * F ω ∂μ_GFF ≤
      (∫ ω, bw ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2 : ℝ) *
      (∫ ω, F ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2 : ℝ) := by
    -- Hölder/Cauchy-Schwarz with p = q = 2
    have h_ofReal : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by norm_num
    have hbw' : MemLp bw (ENNReal.ofReal 2) μ_GFF := h_ofReal ▸ hbw_memLp
    have hF' : MemLp F (ENNReal.ofReal 2) μ_GFF := h_ofReal ▸ hF_memLp
    exact integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (ae_of_all _ (fun ω => le_of_lt (boltzmannWeight_pos d N P a mass ω)))
      (ae_of_all _ hF_nn) hbw' hF'
  -- Chain: Z⁻¹ * ∫ bw*F ≤ Z⁻¹ * (∫ bw²)^{1/2} * (∫ F²)^{1/2}
  --                       ≤ 1 * K^{1/2} * (∫ F²)^{1/2}
  --                       = K^{1/2} * (∫ F²)^{1/2}
  have hZinv_le : Z⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hZ
  have hbw_sq_le : (∫ ω, bw ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2 : ℝ) ≤ K ^ (1/2 : ℝ) := by
    apply Real.rpow_le_rpow (integral_nonneg (fun ω =>
      Real.rpow_nonneg (le_of_lt (boltzmannWeight_pos d N P a mass ω)) _))
    · -- ∫ bw^{rpow 2} ≤ K: convert rpow to nat pow, then match by definition
      have : ∫ ω, bw ω ^ (2:ℝ) ∂μ_GFF = ∫ ω, (Real.exp (-V ω)) ^ 2 ∂μ_GFF := by
        congr 1; ext ω; exact Real.rpow_natCast _ 2
      linarith
    · linarith
  calc Z⁻¹ * ∫ ω, bw ω * F ω ∂μ_GFF
      ≤ Z⁻¹ * ((∫ ω, bw ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) * (∫ ω, F ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ)) :=
        mul_le_mul_of_nonneg_left h_cs (le_of_lt (inv_pos.mpr hZ_pos))
    _ ≤ 1 * (K ^ (1/2:ℝ) * (∫ ω, F ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ)) := by
        have hF_int_nn : 0 ≤ (∫ ω, F ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) :=
          Real.rpow_nonneg (integral_nonneg (fun ω =>
            Real.rpow_nonneg (hF_nn ω) _)) _
        have hbw_int_nn : 0 ≤ (∫ ω, bw ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) :=
          Real.rpow_nonneg (integral_nonneg (fun ω =>
            Real.rpow_nonneg (le_of_lt (boltzmannWeight_pos d N P a mass ω)) _)) _
        apply mul_le_mul hZinv_le _ (mul_nonneg hbw_int_nn hF_int_nn) (by linarith)
        exact mul_le_mul_of_nonneg_right hbw_sq_le hF_int_nn
    _ = K ^ (1/2:ℝ) * (∫ ω, F ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) := one_mul _

/-- **Interacting moment bound** via Cauchy-Schwarz density transfer.

Bounds the L^{pn} moment of the interacting measure μ_a in terms of the
FREE Gaussian measure μ_{GFF}:

  ∫ |ω(f)|^{pn} dμ_a ≤ C · (2p-1)^{pn/2} · (∫ |ω(f)|^{2n} dμ_{GFF})^{p/2}

where C = K^{1/2} is uniform in a, n, m, f and `p = 2m`.

Proof:
  ∫ |ω(f)|^{pn} dμ_a = (1/Z_a) ∫ |ω(f)|^{pn} · e^{-V_a} dμ_{GFF}
    ≤ (1/Z_a) · (∫ |ω(f)|^{2pn} dμ_{GFF})^{1/2} · (∫ e^{-2V_a} dμ_{GFF})^{1/2}
                                                                [Cauchy-Schwarz]
    ≤ (1/Z_a) · K^{1/2} · (∫ |ω(f)|^{2pn} dμ_{GFF})^{1/2}
                                                    [exponential_moment_bound]
    ≤ K^{1/2} · (2p-1)^{pn/2} · (∫ |ω(f)|^{2n} dμ_{GFF})^{p/2}
                                    [Z ≥ 1 + gaussian_hypercontractivity_continuum]

The RHS is in terms of μ_{GFF}, NOT μ_a. This is essential: converting the
RHS back to μ_a would require ∫ e^{+V_a} dμ_{GFF}, which diverges because
V_a ~ φ⁴ grows faster than the Gaussian suppression e^{-φ²}.

Reference: Simon (1974), §V.1; Glimm-Jaffe (1987), §19.4. -/
theorem interacting_moment_bound
    (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ (C : ℝ), 0 < C ∧
    ∀ (n : ℕ) (p : ℝ) (m : ℕ), 1 ≤ m → p = 2 * ↑m →
    ∀ (f : ContinuumTestFunction d) (a : ℝ) (ha : 0 < a), a ≤ 1 →
    ∫ ω : Configuration (ContinuumTestFunction d),
        |ω f| ^ (p * ↑n) ∂(continuumMeasure d N P a mass ha hmass) ≤
      C * (2 * p - 1) ^ (p * ↑n / 2) *
      (∫ ω : Configuration (ContinuumTestFunction d),
        |ω f| ^ (2 * ↑n) ∂(Measure.map (latticeEmbedLift d N a ha)
          (latticeGaussianMeasure d N a mass ha hmass))) ^
      (p / 2) := by
  -- Step A2: Get K from exponential_moment_bound
  obtain ⟨K, hK_pos, hK⟩ := exponential_moment_bound d N P mass hmass
  -- C = K^(1/2) works because Z ≥ 1 gives 1/Z ≤ 1
  refine ⟨K ^ (1 / 2 : ℝ), Real.rpow_pos_of_pos hK_pos _, ?_⟩
  intro n p m hm hp f a ha ha1
  -- Setup
  set μ_GFF := latticeGaussianMeasure d N a mass ha hmass
  set μ_int := interactingLatticeMeasure d N P a mass ha hmass
  set ι := latticeEmbedLift d N a ha
  set bw := boltzmannWeight d N P a mass
  set Z := partitionFunction d N P a mass ha hmass
  set g_f := latticeTestField d N a f
  have hZ_pos : 0 < Z := partitionFunction_pos d N P a mass ha hmass
  have hZ_ge_one : 1 ≤ Z := partitionFunction_ge_one d N P mass hmass a ha
  have hι_meas : AEMeasurable ι μ_int :=
    (latticeEmbedLift_measurable d N a ha).aemeasurable
  have hι_meas_gauss : AEMeasurable ι μ_GFF :=
    (latticeEmbedLift_measurable d N a ha).aemeasurable
  have h_eval : ∀ ω : Configuration (FinLatticeField d N),
      (ι ω) f = ω g_f := fun ω => latticeEmbedLift_eval_eq d N a ha f ω
  -- Step 1: Pull back LHS through integral_map
  -- LHS = ∫ |ω f|^{pn} d(map ι μ_int) = ∫ |(ι ω) f|^{pn} dμ_int
  have hmeas_lhs : AEStronglyMeasurable (fun (ω : Configuration (ContinuumTestFunction d)) =>
      |ω f| ^ (p * ↑n)) (Measure.map ι μ_int) :=
    ((configuration_eval_measurable f).norm.pow_const _).aestronglyMeasurable
  -- The continuum measure is the pushforward of the interacting measure
  have h_cont_eq : continuumMeasure d N P a mass ha hmass = Measure.map ι μ_int := rfl
  rw [h_cont_eq, integral_map hι_meas hmeas_lhs]
  -- Rewrite using h_eval: |(ι ω) f| = |ω g_f|
  simp_rw [h_eval]
  -- Step 2: Apply density_transfer_bound
  -- F(ω) = |ω g_f|^{pn} is nonneg, measurable, and has finite Gaussian L² norm
  have hF_meas_gauss : AEStronglyMeasurable (fun ω : Configuration (FinLatticeField d N) =>
      |ω g_f| ^ (p * ↑n)) μ_GFF :=
    ((configuration_eval_measurable g_f).norm.pow_const _).aestronglyMeasurable
  have hF_sq_int : Integrable (fun ω : Configuration (FinLatticeField d N) =>
      (|ω g_f| ^ (p * ↑n)) ^ 2) μ_GFF := by
    -- All polynomial moments of Gaussian linear functionals are finite
    -- (pairing_memLp from gaussian-field: Gaussian pairings are in L^p for all p)
    have h_μ : μ_GFF = GaussianField.measure (latticeCovariance d N a mass ha hmass) := rfl
    haveI := latticeGaussianMeasure_isProbability d N a mass ha hmass
    have hp_nn : (0 : ℝ) ≤ p := by rw [hp]; positivity
    have h_nn : (0 : ℝ) ≤ 2 * p * ↑n :=
      mul_nonneg (mul_nonneg (by norm_num) hp_nn) (Nat.cast_nonneg _)
    have h_memLp := GaussianField.pairing_memLp
      (latticeCovariance d N a mass ha hmass) g_f ⟨2 * p * ↑n, h_nn⟩
    have h_int : Integrable (fun ω : Configuration (FinLatticeField d N) =>
        ‖ω g_f‖ ^ (2 * p * ↑n)) μ_GFF := by rw [h_μ]; exact h_memLp.integrable_norm_rpow'
    exact h_int.congr (ae_of_all _ fun ω => by
      change ‖ω g_f‖ ^ (2 * p * ↑n) = (|ω g_f| ^ (p * ↑n)) ^ 2
      rw [Real.norm_eq_abs, ← Real.rpow_natCast (|ω g_f| ^ (p * ↑n)) 2,
          ← Real.rpow_mul (abs_nonneg _)]; congr 1; ring)
  have h_dt := density_transfer_bound d N P a mass ha hmass K hK_pos
    (hK a ha ha1) hZ_ge_one (fun ω => |ω g_f| ^ (p * ↑n))
    (fun ω => Real.rpow_nonneg (abs_nonneg _) _) hF_meas_gauss hF_sq_int
  -- h_dt: ∫ |ω g_f|^{pn} dμ_int ≤ K^{1/2} * (∫ (|ω g_f|^{pn})^2 dμ_GFF)^{1/2}
  -- Step 3: Bound (∫ (|ω g_f|^{pn})^2 dμ_GFF)^{1/2} using hypercontractivity
  -- (|x|^a)^{(2:ℝ)} = |x|^{2a} by rpow_mul, so F² = |ω g_f|^{2pn}
  -- Convert to continuum integral, apply hypercontractivity with parameter 2p,
  -- then simplify exponents.
  have h2p_ge : 2 ≤ 2 * p := by
    rw [hp]; have : (1 : ℝ) ≤ ↑m := Nat.one_le_cast.mpr hm; nlinarith
  have h2m_ge : 1 ≤ 2 * m := by omega
  have h2p_eq : 2 * p = 2 * ↑(2 * m) := by rw [hp]; push_cast; ring
  -- Hypercontractivity for the Gaussian measure with parameter 2p
  have h_hyper := gaussian_hypercontractivity_continuum d N mass hmass n (2 * p) h2p_ge
    (2 * m) h2m_ge h2p_eq f a ha ha1
  -- h_hyper: ∫ |σ f|^{2p·n} d(map ι μ_GFF) ≤
  --   (2p-1)^{2p·n/2} * (∫ |σ f|^{2n} d(map ι μ_GFF))^{2p/2}
  -- Key: (|x|^{pn})^{2:ℝ} = |x|^{2*p*↑n} via rpow_mul
  have h_rpow_sq : ∀ ω : Configuration (FinLatticeField d N),
      (|ω g_f| ^ (p * ↑n)) ^ (2:ℝ) = |ω g_f| ^ (2 * p * ↑n) := fun ω => by
    rw [← Real.rpow_mul (abs_nonneg _)]; congr 1; ring
  -- Lattice ↔ continuum integral for 2pn exponent
  have h_int_map_2pn : ∫ σ, |σ f| ^ (2 * p * ↑n) ∂(Measure.map ι μ_GFF) =
      ∫ ω, |ω g_f| ^ (2 * p * ↑n) ∂μ_GFF := by
    simp only [← Real.norm_eq_abs]
    rw [integral_map hι_meas_gauss
        ((configuration_eval_measurable f).norm.pow_const _).aestronglyMeasurable]
    simp_rw [h_eval]
  -- F² integral = continuum 2pn integral
  have h_F2_eq : ∫ ω, (fun ω => |ω g_f| ^ (p * ↑n)) ω ^ (2:ℝ) ∂μ_GFF =
      ∫ σ, |σ f| ^ (2 * p * ↑n) ∂(Measure.map ι μ_GFF) := by
    trans ∫ ω, |ω g_f| ^ (2 * p * ↑n) ∂μ_GFF
    · congr 1; ext ω; exact h_rpow_sq ω
    · exact h_int_map_2pn.symm
  -- Nonneg helpers for rpow arithmetic
  have h_2pm1_nn : (0:ℝ) ≤ 2 * p - 1 := by linarith
  have h_I2_nn : (0 : ℝ) ≤ ∫ σ, |σ f| ^ (2 * ↑n) ∂(Measure.map ι μ_GFF) := by
    exact integral_nonneg fun σ => by positivity
  -- Bound (∫ F²)^{1/2} using h_hyper + rpow arithmetic
  have h_F2_bound : (∫ ω, (fun ω => |ω g_f| ^ (p * ↑n)) ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) ≤
      (2*p-1) ^ (p*↑n/2) * (∫ σ, |σ f| ^ (2*↑n) ∂(Measure.map ι μ_GFF)) ^ (p/2) := by
    rw [h_F2_eq]
    calc (∫ σ, |σ f| ^ (2*p*↑n) ∂(Measure.map ι μ_GFF)) ^ (1/2:ℝ)
        ≤ ((2*p-1) ^ (2*p*↑n/2) *
           (∫ σ, |σ f| ^ (2*↑n) ∂(Measure.map ι μ_GFF)) ^ (2*p/2)) ^ (1/2:ℝ) :=
          Real.rpow_le_rpow
            (integral_nonneg (fun σ => Real.rpow_nonneg (abs_nonneg _) _))
            h_hyper (by linarith)
      _ = (2*p-1) ^ (p*↑n/2) * (∫ σ, |σ f| ^ (2*↑n) ∂(Measure.map ι μ_GFF)) ^ (p/2) := by
          rw [Real.mul_rpow (Real.rpow_nonneg h_2pm1_nn _) (Real.rpow_nonneg h_I2_nn _)]
          congr 1
          · rw [← Real.rpow_mul h_2pm1_nn]; congr 1; ring
          · rw [← Real.rpow_mul h_I2_nn]; congr 1; ring
  -- Final chain: h_dt ≤ K^{1/2} * bound
  calc ∫ x, |x g_f| ^ (p * ↑n) ∂μ_int
      ≤ K ^ (1/2:ℝ) * (∫ ω, (fun ω => |ω g_f| ^ (p * ↑n)) ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) :=
        h_dt
    _ ≤ K ^ (1/2:ℝ) * ((2*p-1) ^ (p*↑n/2) *
         (∫ σ, |σ f| ^ (2*↑n) ∂(Measure.map ι μ_GFF)) ^ (p/2)) :=
        mul_le_mul_of_nonneg_left h_F2_bound (Real.rpow_nonneg (le_of_lt hK_pos) _)
    _ = K ^ (1/2:ℝ) * (2*p-1) ^ (p*↑n/2) *
         (∫ ω, |ω f| ^ (2*↑n) ∂(Measure.map ι μ_GFF)) ^ (p/2) :=
        (mul_assoc _ _ _).symm

end Pphi2

end
