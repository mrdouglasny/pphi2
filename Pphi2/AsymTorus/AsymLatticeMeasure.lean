/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Heterogeneous isotropic lattice measures (Z_Nt × Z_Ns)

The Gaussian (and, downstream, interacting) P(φ)₂ measures on the *heterogeneous* lattice
`AsymLatticeField Nt Ns = ZMod Nt × ZMod Ns → ℝ` with a **single isotropic spacing `a`**
(`a = Lt/Nt = Ls/Ns`). This is the metric-correct replacement for the square
`FinLatticeField 2 N` + geometric-mean-spacing construction: the covariance is
`latticeCovarianceAsymGJ` from gaussian-field, whose lattice→continuum limit is the correct
rectangular-torus Green's function (`lattice_green_tendsto_continuum_asym`), so the rectangle
`Nt ≠ Ns` is carried by the boundary condition, not a distorted metric.

## Main definitions

- `latticeGaussianMeasureAsym` — centered GJ-normalized Gaussian measure on
  `Configuration (AsymLatticeField Nt Ns)`, covariance `latticeCovarianceAsymGJ`.

## Design

Mirrors gaussian-field's square `latticeGaussianMeasure`, with `FinLatticeField d N`
replaced by `AsymLatticeField Nt Ns` and the isotropic covariance. The cell area is `a²`
and the volume `Nt·Ns·a² = Lt·Ls`, so the `d = 2` Glimm–Jaffe normalisation factor is
`(a²)^{-1/2} = 1/a` (built into `latticeCovarianceAsymGJ`).
-/

import Lattice.AsymCovariance
import Lattice.AsymFiniteField
import Pphi2.InteractingMeasure.LatticeMeasure

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

/-! The `DyninMityaginSpace (AsymLatticeField)` instance now lives in GaussianField
(`Lattice.AsymFiniteField`, imported above). -/

/-- The centered Gaussian measure on the heterogeneous isotropic lattice
`ZMod Nt × ZMod Ns` (**Glimm–Jaffe-aligned normalisation**).

Constructed via `GaussianField.measure` from the GJ-aligned isotropic covariance CLM
`latticeCovarianceAsymGJ`. Has covariance kernel `a^{-2} Q⁻¹` (cell area `a²`), so the
lattice two-point function converges to the rectangular continuum Green's function on
`T_{Lt,Ls}` as `a → 0` (`Nt, Ns → ∞`, `Nt/Ns = Lt/Ls`). -/
noncomputable def latticeGaussianMeasureAsym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    @Measure (Configuration (AsymLatticeField Nt Ns)) instMeasurableSpaceConfiguration :=
  GaussianField.measure (latticeCovarianceAsymGJ Nt Ns a mass ha hmass)

/-- The heterogeneous lattice Gaussian measure is a probability measure. -/
instance latticeGaussianMeasureAsym_isProbability (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    @IsProbabilityMeasure (Configuration (AsymLatticeField Nt Ns))
      instMeasurableSpaceConfiguration
      (latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
  unfold latticeGaussianMeasureAsym
  exact GaussianField.measure_isProbability (latticeCovarianceAsymGJ Nt Ns a mass ha hmass)

/-- The two-point function of the heterogeneous lattice Gaussian measure equals the GJ-aligned
isotropic covariance bilinear form. -/
theorem latticeGaussianMeasureAsym_cross_moment (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (f g : AsymLatticeField Nt Ns) :
    ∫ ω : Configuration (AsymLatticeField Nt Ns),
      (ω f) * (ω g) ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) =
    GaussianField.covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass) f g := by
  unfold latticeGaussianMeasureAsym
  exact GaussianField.cross_moment_eq_covariance _ f g

/-! ## Wick ordering constant (heterogeneous lattice) -/

/-- The Wick ordering constant on the heterogeneous lattice (GJ-aligned diagonal of the
lattice propagator):

  `c_a = (a²)⁻¹ · (1/|Λ|) · Σ_k 1/λ_k = (a²)⁻¹ · (1/(Nt·Ns)) · Tr(Q⁻¹)`

where `λ_k` are the eigenvalues of `massOperatorAsym = -Δ_a + m²`. This is the variance of
the lattice GFF site value `ω(δ_x)` under `latticeGaussianMeasureAsym` (translation-invariant,
so the `Q⁻¹` diagonal equals `(1/|Λ|) Tr(Q⁻¹)`, which is basis-independent — hence the clean
sum over the Hermitian eigenvalues). The factor `(a²)⁻¹` is the `d = 2` GJ Riemann-sum factor. -/
def wickConstantAsym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ) : ℝ :=
  (a ^ 2 : ℝ)⁻¹ *
  ((1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) *
    ∑ k : AsymLatticeSites Nt Ns, (massEigenvaluesAsym Nt Ns a mass k)⁻¹)

/-- The heterogeneous Wick constant is positive when `mass > 0`. -/
theorem wickConstantAsym_pos (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    0 < wickConstantAsym Nt Ns a mass := by
  unfold wickConstantAsym
  refine mul_pos (inv_pos.mpr (pow_pos ha 2)) (mul_pos ?_ ?_)
  · exact div_pos one_pos (by exact_mod_cast Fintype.card_pos)
  · exact Finset.sum_pos
      (fun k _ => inv_pos.mpr (massOperatorMatrixAsym_eigenvalues_pos Nt Ns a mass ha hmass k))
      Finset.univ_nonempty

/-! ## Interaction functional (heterogeneous lattice) -/

/-- The heterogeneous lattice interaction as a function of the configuration `ω`:
`V_a(ω) = a² · Σ_{x : ZMod Nt × ZMod Ns} :P(ω(δ_x)):_{c_a}`. -/
def interactionFunctionalAsym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) :
    Configuration (AsymLatticeField Nt Ns) → ℝ :=
  fun ω => a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
    wickPolynomial P (wickConstantAsym Nt Ns a mass) (ω (asymLatticeDelta Nt Ns x))

private theorem wickMonomial_measurable_asym {α : Type*} (n : ℕ) (c : ℝ) (f : α → ℝ)
    {mα : MeasurableSpace α}
    (hf : @Measurable α ℝ mα (borel ℝ) f) :
    @Measurable α ℝ mα (borel ℝ) (fun x => wickMonomial n c (f x)) := by
  suffices h : ∀ k ≤ n, @Measurable α ℝ mα (borel ℝ) (fun x => wickMonomial k c (f x)) from
    h n le_rfl
  intro k hk
  induction k using Nat.strongRecOn with
  | ind k ih =>
    match k with
    | 0 => exact measurable_const
    | 1 => exact hf
    | k + 2 =>
      simp only [wickMonomial_succ_succ]
      exact (hf.mul (ih (k + 1) (by omega) (by omega))).sub
        (measurable_const.mul (ih k (by omega) (by omega)))

theorem interactionFunctionalAsym_measurable (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) :
    @Measurable (Configuration (AsymLatticeField Nt Ns)) ℝ
      instMeasurableSpaceConfiguration (borel ℝ)
      (interactionFunctionalAsym Nt Ns P a mass) := by
  unfold interactionFunctionalAsym
  apply Measurable.const_mul
  apply Finset.measurable_sum _ (fun x _ => ?_)
  unfold wickPolynomial
  apply Measurable.add
  · exact Measurable.const_mul
      (wickMonomial_measurable_asym P.n (wickConstantAsym Nt Ns a mass) _
        (configuration_eval_measurable _)) _
  · exact Finset.measurable_sum _ (fun m _ =>
      Measurable.const_mul
        (wickMonomial_measurable_asym m (wickConstantAsym Nt Ns a mass) _
          (configuration_eval_measurable _)) _)

/-- The heterogeneous interaction functional is bounded below. -/
theorem interactionFunctionalAsym_bounded_below (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (_hmass : 0 < mass) :
    ∃ B : ℝ, ∀ ω : Configuration (AsymLatticeField Nt Ns),
    interactionFunctionalAsym Nt Ns P a mass ω ≥ -B := by
  obtain ⟨A, _hA_pos, hA_bound⟩ := wickPolynomial_bounded_below P (wickConstantAsym Nt Ns a mass)
  refine ⟨a ^ 2 * Fintype.card (AsymLatticeSites Nt Ns) * A, fun ω => ?_⟩
  unfold interactionFunctionalAsym
  have ha_pow : (0 : ℝ) < a ^ 2 := pow_pos ha 2
  calc a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
        wickPolynomial P (wickConstantAsym Nt Ns a mass) (ω (asymLatticeDelta Nt Ns x))
      ≥ a ^ 2 * ∑ _x : AsymLatticeSites Nt Ns, (-A) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt ha_pow)
        exact Finset.sum_le_sum (fun x _ => hA_bound _)
    _ = -(a ^ 2 * Fintype.card (AsymLatticeSites Nt Ns) * A) := by
        simp [Finset.sum_const, mul_comm]; ring

/-! ## Boltzmann weight, partition function, interacting measure -/

/-- The Boltzmann weight `exp(-V_a(ω))` on the heterogeneous lattice. -/
def boltzmannWeightAsym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) :
    Configuration (AsymLatticeField Nt Ns) → ℝ :=
  fun ω => Real.exp (-(interactionFunctionalAsym Nt Ns P a mass ω))

theorem boltzmannWeightAsym_pos (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ)
    (ω : Configuration (AsymLatticeField Nt Ns)) :
    0 < boltzmannWeightAsym Nt Ns P a mass ω :=
  Real.exp_pos _

theorem boltzmannWeightAsym_integrable (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Integrable (boltzmannWeightAsym Nt Ns P a mass)
      (latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
  obtain ⟨B, hB_bound⟩ := interactionFunctionalAsym_bounded_below Nt Ns P a mass ha hmass
  apply Integrable.of_bound (C := Real.exp B)
  · exact (interactionFunctionalAsym_measurable Nt Ns P a mass).neg.exp.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro ω
    simp only [boltzmannWeightAsym, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp_of_le (by linarith [hB_bound ω])

/-- The partition function `Z_a = ∫ exp(-V_a) dμ_{GFF,a}` on the heterogeneous lattice. -/
def partitionFunctionAsym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) : ℝ :=
  ∫ ω, boltzmannWeightAsym Nt Ns P a mass ω
    ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)

theorem partitionFunctionAsym_pos (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    0 < partitionFunctionAsym Nt Ns P a mass ha hmass := by
  unfold partitionFunctionAsym
  have hinteg := boltzmannWeightAsym_integrable Nt Ns P a mass ha hmass
  rw [integral_pos_iff_support_of_nonneg
    (fun ω => le_of_lt (boltzmannWeightAsym_pos Nt Ns P a mass ω)) hinteg]
  have hsup : Function.support (boltzmannWeightAsym Nt Ns P a mass) = Set.univ := by
    ext ω; simp [Function.mem_support, ne_of_gt (boltzmannWeightAsym_pos Nt Ns P a mass ω)]
  rw [hsup]
  exact Measure.measure_univ_pos.mpr (IsProbabilityMeasure.ne_zero _)

/-- The P(φ)₂ interacting measure on the heterogeneous isotropic lattice:
`dμ_a = (1/Z_a)·exp(-V_a(ω))·dμ_{GFF,a}(ω)`. -/
def interactingLatticeMeasureAsym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    @Measure (Configuration (AsymLatticeField Nt Ns)) instMeasurableSpaceConfiguration :=
  (ENNReal.ofReal (partitionFunctionAsym Nt Ns P a mass ha hmass))⁻¹ •
    (latticeGaussianMeasureAsym Nt Ns a mass ha hmass).withDensity
      (fun ω => ENNReal.ofReal (boltzmannWeightAsym Nt Ns P a mass ω))

/-- The heterogeneous interacting lattice measure is a probability measure. -/
theorem interactingLatticeMeasureAsym_isProbability (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    @IsProbabilityMeasure (Configuration (AsymLatticeField Nt Ns))
      instMeasurableSpaceConfiguration
      (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) := by
  constructor
  have hZ := partitionFunctionAsym_pos Nt Ns P a mass ha hmass
  have hZ_ne : ENNReal.ofReal (partitionFunctionAsym Nt Ns P a mass ha hmass) ≠ 0 :=
    ENNReal.ofReal_pos.mpr hZ |>.ne'
  have hZ_ne_top : ENNReal.ofReal (partitionFunctionAsym Nt Ns P a mass ha hmass) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  unfold interactingLatticeMeasureAsym
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (boltzmannWeightAsym_integrable Nt Ns P a mass ha hmass)
    (Filter.Eventually.of_forall (fun ω => le_of_lt (boltzmannWeightAsym_pos Nt Ns P a mass ω)))]
  simp only [smul_eq_mul]
  exact ENNReal.inv_mul_cancel hZ_ne hZ_ne_top

end Pphi2

end
