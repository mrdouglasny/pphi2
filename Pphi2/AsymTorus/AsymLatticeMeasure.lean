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
import Pphi2.InteractingMeasure.LatticeMeasure

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

/-! ## DyninMityaginSpace instance for the heterogeneous lattice field

`AsymLatticeField Nt Ns ≅ ℝ^(Nt·Ns)` is trivially nuclear. Port of gaussian-field's
`finLatticeField_dyninMityaginSpace`, generic over the finite index type — only the Fintype
structure of `AsymLatticeSites Nt Ns` is used. Needed so `GaussianField.measure` /
`measure_isProbability` apply on the heterogeneous lattice. -/

/-- Enumeration of heterogeneous lattice sites via Fintype. -/
private noncomputable def asymLatticeSiteEnum (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    AsymLatticeSites Nt Ns ≃ Fin (Fintype.card (AsymLatticeSites Nt Ns)) :=
  Fintype.equivFin _

/-- The m-th basis vector: delta at the m-th site (or zero if `m ≥ |sites|`). -/
def asymLatticeBasisVec (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (m : ℕ) :
    AsymLatticeField Nt Ns :=
  if h : m < Fintype.card (AsymLatticeSites Nt Ns) then
    asymLatticeDelta Nt Ns ((asymLatticeSiteEnum Nt Ns).symm ⟨m, h⟩)
  else 0

/-- The m-th coefficient: evaluation at the m-th site (or zero if `m ≥ |sites|`). -/
def asymLatticeCoeffCLM (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (m : ℕ) :
    AsymLatticeField Nt Ns →L[ℝ] ℝ :=
  if h : m < Fintype.card (AsymLatticeSites Nt Ns) then
    { toLinearMap :=
      { toFun := fun f => f ((asymLatticeSiteEnum Nt Ns).symm ⟨m, h⟩)
        map_add' := fun _ _ => rfl
        map_smul' := fun r f => by simp [smul_eq_mul] }
      cont := continuous_apply _ }
  else 0

/-- The sup-norm seminorm on the heterogeneous lattice field. -/
def asymLatticeSeminorm (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    Seminorm ℝ (AsymLatticeField Nt Ns) where
  toFun f := Finset.univ.sup' Finset.univ_nonempty (fun x => ‖f x‖₊)
  map_zero' := by simp
  add_le' f g := by
    apply Finset.sup'_le _ _ (fun x hx => ?_)
    calc (↑‖(f + g) x‖₊ : ℝ)
        ≤ ↑‖f x‖₊ + ↑‖g x‖₊ := by exact_mod_cast nnnorm_add_le (f x) (g x)
      _ ≤ _ := add_le_add
          (Finset.le_sup' (fun y => (↑‖f y‖₊ : ℝ)) hx)
          (Finset.le_sup' (fun y => (↑‖g y‖₊ : ℝ)) hx)
  neg' f := by simp [Pi.neg_apply, nnnorm_neg]
  smul' r f := by
    simp only [Pi.smul_apply, smul_eq_mul, nnnorm_mul, NNReal.coe_mul]
    simp only [show (↑‖r‖₊ : ℝ) = ‖r‖ from rfl]
    have := Finset.comp_sup'_eq_sup'_comp (s := Finset.univ)
      Finset.univ_nonempty (f := fun x => (↑‖f x‖₊ : ℝ)) (g := (‖r‖ * ·))
      (fun _ _ => mul_max_of_nonneg _ _ (norm_nonneg r))
    simp only [Function.comp] at this
    exact this.symm

/-- The DyninMityaginSpace instance for heterogeneous lattice fields (delta basis,
point evaluations as coefficients; `f = ∑_x f(x)·δ_x`). -/
noncomputable instance asymLatticeField_dyninMityaginSpace (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    DyninMityaginSpace (AsymLatticeField Nt Ns) where
  ι := Unit
  p := fun _ => asymLatticeSeminorm Nt Ns
  h_countable := inferInstance
  h_completeSpace := by
    have heq : (IsTopologicalAddGroup.rightUniformSpace (AsymLatticeField Nt Ns)) =
        (Pi.uniformSpace (fun _ : AsymLatticeSites Nt Ns => ℝ)) :=
      IsUniformAddGroup.rightUniformSpace_eq
    exact heq ▸ inferInstance
  h_with := by
    rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf]
    simp only [iInf_const]
    have hfun : ⇑(asymLatticeSeminorm Nt Ns) = (norm : AsymLatticeField Nt Ns → ℝ) := by
      ext f; unfold asymLatticeSeminorm
      change (Finset.univ.sup' Finset.univ_nonempty fun x => (↑‖f x‖₊ : ℝ)) = ‖f‖
      rw [Pi.norm_def]
      have h1 : Finset.univ.sup' Finset.univ_nonempty
            (fun x : AsymLatticeSites Nt Ns => (↑‖f x‖₊ : ℝ)) =
          ↑(Finset.univ.sup' Finset.univ_nonempty
            (fun x : AsymLatticeSites Nt Ns => ‖f x‖₊)) :=
        (Finset.comp_sup'_eq_sup'_comp Finset.univ_nonempty
          (g := NNReal.toReal)
          (fun a b => NNReal.coe_mono.map_sup a b)).symm
      rw [h1]
      exact congrArg NNReal.toReal
        (Finset.sup'_eq_sup Finset.univ_nonempty (fun x : AsymLatticeSites Nt Ns => ‖f x‖₊))
    rw [hfun, comap_norm_nhds_zero]
  basis := asymLatticeBasisVec Nt Ns
  coeff := asymLatticeCoeffCLM Nt Ns
  expansion := fun φ f => by
    set C := Fintype.card (AsymLatticeSites Nt Ns) with hC_def
    have hvanish : ∀ m, ¬(m < C) →
        (asymLatticeCoeffCLM Nt Ns m) f * φ (asymLatticeBasisVec Nt Ns m) = 0 := by
      intro m hm
      unfold asymLatticeCoeffCLM asymLatticeBasisVec
      simp only [show ¬(m < Fintype.card (AsymLatticeSites Nt Ns)) from hm, dite_false,
        ContinuousLinearMap.zero_apply, map_zero, mul_zero]
    rw [tsum_eq_sum (s := Finset.range C) (fun m hm => by
      simp only [Finset.mem_range, not_lt] at hm
      exact hvanish m (not_lt.mpr hm))]
    have : ∀ m ∈ Finset.range C,
        (asymLatticeCoeffCLM Nt Ns m) f * φ (asymLatticeBasisVec Nt Ns m) =
        φ ((asymLatticeCoeffCLM Nt Ns m) f • asymLatticeBasisVec Nt Ns m) := by
      intro m _
      rw [map_smul, smul_eq_mul]
    rw [Finset.sum_congr rfl this, ← map_sum]
    congr 1
    ext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    obtain ⟨⟨m, hm⟩, rfl⟩ := (asymLatticeSiteEnum Nt Ns).symm.surjective x
    have hmain : (Finset.range C).sum
        (fun b => (asymLatticeCoeffCLM Nt Ns b) f *
          asymLatticeBasisVec Nt Ns b ((asymLatticeSiteEnum Nt Ns).symm ⟨m, hm⟩)) =
        (asymLatticeCoeffCLM Nt Ns m) f *
          asymLatticeBasisVec Nt Ns m ((asymLatticeSiteEnum Nt Ns).symm ⟨m, hm⟩) := by
      apply Finset.sum_eq_single
      · intro b hb hbm
        have hblt : b < Fintype.card (AsymLatticeSites Nt Ns) := Finset.mem_range.mp hb
        simp only [asymLatticeBasisVec, asymLatticeDelta, hblt, dite_true]
        rw [if_neg]
        · ring
        · intro heq
          exact hbm ((Fin.val_eq_of_eq ((asymLatticeSiteEnum Nt Ns).symm.injective heq)).symm)
      · intro hm'
        exact absurd (Finset.mem_range.mpr hm) hm'
    rw [hmain]
    have hm' : m < Nt * Ns := by
      rwa [show Fintype.card (AsymLatticeSites Nt Ns) = Nt * Ns from by simp] at hm
    simp [asymLatticeCoeffCLM, asymLatticeBasisVec, asymLatticeDelta, hm']
  basis_growth := fun _ => ⟨1, one_pos, 0, fun m => by
    simp only [pow_zero, mul_one]
    unfold asymLatticeSeminorm asymLatticeBasisVec
    by_cases h : m < Fintype.card (AsymLatticeSites Nt Ns)
    · simp only [h, dite_true]
      apply Finset.sup'_le Finset.univ_nonempty
      intro x _
      simp only [asymLatticeDelta]
      split_ifs with heq
      · simp
      · simp
    · simp only [h, dite_false]
      simp⟩
  coeff_decay := fun k => ⟨(1 + Fintype.card (AsymLatticeSites Nt Ns) : ℝ) ^ k,
    by positivity, {()}, fun f m => by
    simp only [Finset.sup_singleton]
    unfold asymLatticeCoeffCLM asymLatticeSeminorm
    by_cases h : m < Fintype.card (AsymLatticeSites Nt Ns)
    · simp only [h, dite_true, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
      set y := (asymLatticeSiteEnum Nt Ns).symm ⟨m, h⟩
      set sem := Finset.univ.sup' Finset.univ_nonempty (fun x => (↑‖f x‖₊ : ℝ)) with sem_def
      have hnorm_le : (↑‖f y‖₊ : ℝ) ≤ sem :=
        Finset.le_sup' (fun x => (↑‖f x‖₊ : ℝ)) (Finset.mem_univ y)
      have hcoeff : |f y| ≤ sem := by
        calc |f y| = ‖f y‖ := (Real.norm_eq_abs _).symm
          _ ≤ sem := by exact_mod_cast hnorm_le
      have hpow : (1 + (m : ℝ)) ^ k ≤
          (1 + (Fintype.card (AsymLatticeSites Nt Ns) : ℝ)) ^ k := by gcongr
      have hsem_nn : 0 ≤ sem := le_trans (by positivity) hnorm_le
      calc |f y| * (1 + ↑m) ^ k
          ≤ sem * (1 + ↑(Fintype.card (AsymLatticeSites Nt Ns))) ^ k :=
            mul_le_mul hcoeff hpow (by positivity) hsem_nn
        _ = (1 + ↑(Fintype.card (AsymLatticeSites Nt Ns))) ^ k * sem := by ring
    · simp only [h, dite_false, ContinuousLinearMap.zero_apply, abs_zero, zero_mul]
      positivity⟩

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
