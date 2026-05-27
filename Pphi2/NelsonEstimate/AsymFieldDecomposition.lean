/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Heterogeneous polynomial-chaos field decomposition (`Z_Nt × Z_Ns`)

The isotropic-lattice analogue of the square `CanonicalJoint` field decomposition
(`Pphi2/NelsonEstimate/FieldDecomposition.lean`): the lattice GFF is realized as the pushforward of
a product of two iid standard-Gaussian families (smooth + rough) synthesized through the rectangular
DFT modes `Fin Nt × Fin Ns` with the cutoff-split covariance weights. This is the dependency-root for
discharging `asymChaosCutoffDecomposition` (the heterogeneous Nelson chaos decomposition).

**Foundational layer (this file):** the joint space/measure, the rectangular-dispersion eigenvalue,
the smooth/rough cutoff weights, the DFT mode coefficients, and the smooth/rough/sum synthesis
functions. The deep `pushforward_eq_GFF` identity (`map (φ_S+φ_R) = latticeGaussianMeasureAsym`) is
the next target — see `docs/asym-fielddecomposition-redesign.md`.

The 1D DFT primitives (`latticeEigenvalue1d`, `latticeFourierBasisFun`, `latticeFourierNormSq`) are
the **same** functions the square uses (per direction `Nt`/`Ns`), so no new Fourier objects are
needed; the rectangular dispersion `λ_{m₁,m₂}` is exactly the eigenvalue of
`abstract_spectral_eq_dft_spectral_2d_asym` (Phase-1b).
-/

import Pphi2.AsymTorus.AsymWickVariance
import GaussianField.CramerWold
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ProductMeasure

noncomputable section

open MeasureTheory ProbabilityTheory GaussianField
open scoped BigOperators

namespace Pphi2

/-- DFT mode index for the rectangular lattice: `Fin Nt × Fin Ns` (cardinality `Nt·Ns`, matching the
site count and the mode sum of `abstract_spectral_eq_dft_spectral_2d_asym`). -/
abbrev AsymCanonicalMode (Nt Ns : ℕ) : Type := Fin Nt × Fin Ns

/-- The canonical joint space: two iid standard-Gaussian families over the DFT modes
(smooth, rough). -/
abbrev AsymCanonicalJoint (Nt Ns : ℕ) : Type :=
  (AsymCanonicalMode Nt Ns → ℝ) × (AsymCanonicalMode Nt Ns → ℝ)

/-- The joint reference measure: product of two iid standard Gaussians over the modes. -/
def asymCanonicalJointMeasure (Nt Ns : ℕ) : Measure (AsymCanonicalJoint Nt Ns) :=
  Measure.prod
    (Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1))
    (Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1))

instance asymCanonicalJointMeasure_isProbability (Nt Ns : ℕ) :
    IsProbabilityMeasure (asymCanonicalJointMeasure Nt Ns) := by
  unfold asymCanonicalJointMeasure; infer_instance

/-- Rectangular-lattice dispersion eigenvalue `λ_{m₁,m₂} = λ_1d(Nt,m₁) + λ_1d(Ns,m₂) + m²`. -/
def asymCanonicalEigenvalue (Nt Ns : ℕ) (a mass : ℝ) (m : AsymCanonicalMode Nt Ns) : ℝ :=
  latticeEigenvalue1d Nt a (m.1 : ℕ) + latticeEigenvalue1d Ns a (m.2 : ℕ) + mass ^ 2

/-- Smooth (low-frequency) part of the covariance eigenvalue `1/λ` at cutoff scale `T`. -/
def asymCanonicalSmoothWeight (Nt Ns : ℕ) (a mass T : ℝ) (m : AsymCanonicalMode Nt Ns) : ℝ :=
  Real.exp (-T * asymCanonicalEigenvalue Nt Ns a mass m) / asymCanonicalEigenvalue Nt Ns a mass m

/-- Rough (high-frequency) part of the covariance eigenvalue `1/λ` at cutoff scale `T`. -/
def asymCanonicalRoughWeight (Nt Ns : ℕ) (a mass T : ℝ) (m : AsymCanonicalMode Nt Ns) : ℝ :=
  (1 - Real.exp (-T * asymCanonicalEigenvalue Nt Ns a mass m)) /
    asymCanonicalEigenvalue Nt Ns a mass m

/-- Product DFT basis function `B_{m₁,m₂}(x) = e_{m₁}(x₁)·e_{m₂}(x₂)`. -/
def asymCanonicalBasis (Nt Ns : ℕ) (m : AsymCanonicalMode Nt Ns) (x : AsymLatticeSites Nt Ns) : ℝ :=
  latticeFourierBasisFun Nt (m.1 : ℕ) x.1 * latticeFourierBasisFun Ns (m.2 : ℕ) x.2

/-- Product DFT basis norm² `‖B_m‖² = normSq(Nt,m₁)·normSq(Ns,m₂)`. -/
def asymCanonicalNormSq (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (m : AsymCanonicalMode Nt Ns) : ℝ :=
  latticeFourierNormSq Nt (m.1 : ℕ) * latticeFourierNormSq Ns (m.2 : ℕ)

/-- Smooth synthesis coefficient: `√(smoothWeight/‖B_m‖²)·B_m(x)`. -/
def asymCanonicalSmoothModeCoeff (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (x : AsymLatticeSites Nt Ns) (m : AsymCanonicalMode Nt Ns) : ℝ :=
  Real.sqrt (asymCanonicalSmoothWeight Nt Ns a mass T m / asymCanonicalNormSq Nt Ns m) *
    asymCanonicalBasis Nt Ns m x

/-- Rough synthesis coefficient: `√(roughWeight/‖B_m‖²)·B_m(x)`. -/
def asymCanonicalRoughModeCoeff (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (x : AsymLatticeSites Nt Ns) (m : AsymCanonicalMode Nt Ns) : ℝ :=
  Real.sqrt (asymCanonicalRoughWeight Nt Ns a mass T m / asymCanonicalNormSq Nt Ns m) *
    asymCanonicalBasis Nt Ns m x

/-- The smooth field synthesized from the first (smooth) Gaussian family. The `(√(a²))⁻¹ = 1/a`
prefix is the Glimm–Jaffe `d = 2` normalization, matching
`latticeCovarianceAsymGJ = (√(a²))⁻¹ • spectral`: it makes the synthesis covariance equal the GJ
covariance (not the bare spectral one). -/
def asymCanonicalSmoothFieldFunction (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (η : AsymCanonicalJoint Nt Ns) : AsymLatticeField Nt Ns :=
  fun x => (Real.sqrt (a ^ 2))⁻¹ *
    ∑ m : AsymCanonicalMode Nt Ns, asymCanonicalSmoothModeCoeff Nt Ns a mass T x m * η.1 m

/-- The rough field synthesized from the second (rough) Gaussian family (same GJ `(√(a²))⁻¹`
prefix as the smooth part). -/
def asymCanonicalRoughFieldFunction (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (η : AsymCanonicalJoint Nt Ns) : AsymLatticeField Nt Ns :=
  fun x => (Real.sqrt (a ^ 2))⁻¹ *
    ∑ m : AsymCanonicalMode Nt Ns, asymCanonicalRoughModeCoeff Nt Ns a mass T x m * η.2 m

/-- The synthesized field `φ_S + φ_R`; its law (under `asymCanonicalJointMeasure`) is the lattice
GFF — the `pushforward_eq_GFF` identity, the next target (see the redesign doc). -/
def asymCanonicalSumFieldFunction (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (η : AsymCanonicalJoint Nt Ns) : AsymLatticeField Nt Ns :=
  fun x => asymCanonicalSmoothFieldFunction Nt Ns a mass T η x +
    asymCanonicalRoughFieldFunction Nt Ns a mass T η x

/-- The smooth + rough cutoff weights sum to the full covariance eigenvalue `1/λ_m` — the algebraic
identity underlying `pushforward_eq_GFF` (the two iid families synthesize a Gaussian field with the
GFF covariance). -/
theorem asymCanonicalSmoothWeight_add_roughWeight (Nt Ns : ℕ) (a mass T : ℝ)
    (m : AsymCanonicalMode Nt Ns) :
    asymCanonicalSmoothWeight Nt Ns a mass T m + asymCanonicalRoughWeight Nt Ns a mass T m =
      (asymCanonicalEigenvalue Nt Ns a mass m)⁻¹ := by
  unfold asymCanonicalSmoothWeight asymCanonicalRoughWeight
  rw [← add_div,
    show Real.exp (-T * asymCanonicalEigenvalue Nt Ns a mass m) +
        (1 - Real.exp (-T * asymCanonicalEigenvalue Nt Ns a mass m)) = 1 from by ring,
    one_div]

abbrev AsymCanonicalJointSumIndex (Nt Ns : ℕ) : Type :=
  AsymCanonicalMode Nt Ns ⊕ AsymCanonicalMode Nt Ns

theorem asymCanonicalJointMeasure_map_stdGaussianEuclidean (Nt Ns : ℕ) :
    (asymCanonicalJointMeasure Nt Ns).map
        (fun η =>
          WithLp.toLp 2
            (((MeasurableEquiv.sumPiEquivProdPi
              (fun _ : AsymCanonicalJointSumIndex Nt Ns => ℝ)).symm) η)) =
      ProbabilityTheory.stdGaussian
        (EuclideanSpace ℝ (AsymCanonicalJointSumIndex Nt Ns)) := by
  have h_map_map :
      Measure.map
          (fun η =>
            WithLp.toLp 2
              (((MeasurableEquiv.sumPiEquivProdPi
                (fun _ : AsymCanonicalJointSumIndex Nt Ns => ℝ)).symm) η))
          (asymCanonicalJointMeasure Nt Ns) =
        Measure.map
          (WithLp.toLp 2)
          ((asymCanonicalJointMeasure Nt Ns).map
            ((MeasurableEquiv.sumPiEquivProdPi
              (fun _ : AsymCanonicalJointSumIndex Nt Ns => ℝ)).symm)) := by
    simpa [Function.comp] using
      (Measure.map_map
        (g := WithLp.toLp 2)
        (f := (MeasurableEquiv.sumPiEquivProdPi
          (fun _ : AsymCanonicalJointSumIndex Nt Ns => ℝ)).symm)
        (μ := asymCanonicalJointMeasure Nt Ns)
        (by fun_prop)
        ((MeasurableEquiv.sumPiEquivProdPi
          (fun _ : AsymCanonicalJointSumIndex Nt Ns => ℝ)).symm.measurable)).symm
  rw [h_map_map]
  simp only [asymCanonicalJointMeasure]
  rw [measurePreserving_sumPiEquivProdPi_symm
    (fun _ : AsymCanonicalJointSumIndex Nt Ns =>
      (gaussianReal 0 1 : Measure ℝ)) |>.map_eq]
  simpa using
    (ProbabilityTheory.map_pi_eq_stdGaussian
      (ι := AsymCanonicalJointSumIndex Nt Ns))

def asymLatticeFieldToConfig (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (φ : AsymLatticeField Nt Ns) :
    Configuration (AsymLatticeField Nt Ns) :=
  { toFun := fun f => ∑ x : AsymLatticeSites Nt Ns, f x * φ x
    map_add' := fun f g => by
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    map_smul' := fun r f => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
        Finset.mul_sum, mul_assoc]
    cont := continuous_finset_sum _ (fun i _ =>
      (continuous_apply i).mul continuous_const) }

@[simp] theorem asymLatticeFieldToConfig_apply
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (φ : AsymLatticeField Nt Ns)
    (f : AsymLatticeField Nt Ns) :
    asymLatticeFieldToConfig Nt Ns φ f =
      ∑ x : AsymLatticeSites Nt Ns, f x * φ x := rfl

def asymEvalMap (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    Configuration (AsymLatticeField Nt Ns) → AsymLatticeField Nt Ns :=
  fun ω x => ω (asymLatticeDelta Nt Ns x)

theorem asymEvalMap_measurable (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    Measurable (asymEvalMap Nt Ns) := by
  rw [measurable_pi_iff]
  intro x
  simpa [asymEvalMap] using
    (configuration_eval_measurable (E := AsymLatticeField Nt Ns)
      (asymLatticeDelta Nt Ns x))

theorem asymField_basis_decomposition (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (φ : AsymLatticeField Nt Ns) :
    φ = ∑ y : AsymLatticeSites Nt Ns, φ y • asymLatticeDelta Nt Ns y := by
  ext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, asymLatticeDelta,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem asymConfig_apply_eq_sum_delta (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (ω : Configuration (AsymLatticeField Nt Ns))
    (f : AsymLatticeField Nt Ns) :
    ω f = ∑ x : AsymLatticeSites Nt Ns, f x * ω (asymLatticeDelta Nt Ns x) := by
  conv_lhs => rw [asymField_basis_decomposition Nt Ns f]
  simp [map_sum, map_smul, smul_eq_mul]

theorem asymConfig_apply_eq_sum_evalMap (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (ω : Configuration (AsymLatticeField Nt Ns))
    (f : AsymLatticeField Nt Ns) :
    ω f = ∑ x : AsymLatticeSites Nt Ns, f x * (asymEvalMap Nt Ns ω) x := by
  simpa [asymEvalMap] using asymConfig_apply_eq_sum_delta Nt Ns ω f

noncomputable def asymEvalMapInv (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (φ : AsymLatticeField Nt Ns) :
    Configuration (AsymLatticeField Nt Ns) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => ∑ x : AsymLatticeSites Nt Ns, f x * φ x
      map_add' := fun f g => by simp [Finset.sum_add_distrib, add_mul]
      map_smul' := fun c f => by
        simp only [Finset.mul_sum, smul_eq_mul, RingHom.id_apply, Pi.smul_apply]
        congr 1
        ext x
        ring }

theorem asymEvalMapInv_apply (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (φ f : AsymLatticeField Nt Ns) :
    asymEvalMapInv Nt Ns φ f =
      ∑ x : AsymLatticeSites Nt Ns, f x * φ x := by
  simp only [asymEvalMapInv]
  rfl

theorem asymEvalMap_evalMapInv (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (φ : AsymLatticeField Nt Ns) :
    asymEvalMap Nt Ns (asymEvalMapInv Nt Ns φ) = φ := by
  ext x
  simp only [asymEvalMap, asymEvalMapInv_apply, asymLatticeDelta]
  simp [Finset.mem_univ]

theorem asymEvalMapInv_evalMap (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (ω : Configuration (AsymLatticeField Nt Ns)) :
    asymEvalMapInv Nt Ns (asymEvalMap Nt Ns ω) = ω := by
  apply ContinuousLinearMap.ext
  intro f
  exact (asymConfig_apply_eq_sum_evalMap Nt Ns ω f).symm

theorem asymEvalMapInv_measurable (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    Measurable (asymEvalMapInv Nt Ns) := by
  apply configuration_measurable_of_eval_measurable (asymEvalMapInv Nt Ns)
  intro f
  simp_rw [asymEvalMapInv_apply]
  exact Finset.measurable_sum _ (fun x _ =>
    measurable_const.mul (measurable_pi_apply x))

theorem asymLatticeFieldToConfig_eq_evalMapInv
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (φ : AsymLatticeField Nt Ns) :
    asymLatticeFieldToConfig Nt Ns φ = asymEvalMapInv Nt Ns φ := by
  apply ContinuousLinearMap.ext
  intro f
  simpa [asymLatticeFieldToConfig] using
    (asymEvalMapInv_apply Nt Ns φ f).symm

def asymCanonicalSmoothFieldFunctionOfFst (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (ηS : AsymCanonicalMode Nt Ns → ℝ) :
    AsymLatticeField Nt Ns :=
  fun x => (Real.sqrt (a ^ 2))⁻¹ *
    ∑ m : AsymCanonicalMode Nt Ns, asymCanonicalSmoothModeCoeff Nt Ns a mass T x m * ηS m

def asymCanonicalRoughFieldFunctionOfSnd (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (ηR : AsymCanonicalMode Nt Ns → ℝ) :
    AsymLatticeField Nt Ns :=
  fun x => (Real.sqrt (a ^ 2))⁻¹ *
    ∑ m : AsymCanonicalMode Nt Ns, asymCanonicalRoughModeCoeff Nt Ns a mass T x m * ηR m

@[simp] theorem asymCanonicalSmoothFieldFunction_eq_of_fst
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ)
    (ηS ηR : AsymCanonicalMode Nt Ns → ℝ) (x : AsymLatticeSites Nt Ns) :
    asymCanonicalSmoothFieldFunction Nt Ns a mass T (ηS, ηR) x =
      asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS x := by
  rfl

@[simp] theorem asymCanonicalRoughFieldFunction_eq_of_snd
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ)
    (ηS ηR : AsymCanonicalMode Nt Ns → ℝ) (x : AsymLatticeSites Nt Ns) :
    asymCanonicalRoughFieldFunction Nt Ns a mass T (ηS, ηR) x =
      asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR x := by
  rfl

theorem asymCanonicalSmoothFieldFunction_add
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ)
    (η₁ η₂ : AsymCanonicalJoint Nt Ns) (x : AsymLatticeSites Nt Ns) :
    asymCanonicalSmoothFieldFunction Nt Ns a mass T (η₁ + η₂) x =
      asymCanonicalSmoothFieldFunction Nt Ns a mass T η₁ x +
        asymCanonicalSmoothFieldFunction Nt Ns a mass T η₂ x := by
  unfold asymCanonicalSmoothFieldFunction
  rw [show (η₁ + η₂).1 = η₁.1 + η₂.1 by rfl]
  simp_rw [Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib, mul_add]

theorem asymCanonicalSmoothFieldFunction_smul
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T c : ℝ)
    (η : AsymCanonicalJoint Nt Ns) (x : AsymLatticeSites Nt Ns) :
    asymCanonicalSmoothFieldFunction Nt Ns a mass T (c • η) x =
      c * asymCanonicalSmoothFieldFunction Nt Ns a mass T η x := by
  unfold asymCanonicalSmoothFieldFunction
  rw [show (c • η).1 = c • η.1 by rfl]
  simp_rw [Pi.smul_apply, smul_eq_mul]
  rw [show c * ((Real.sqrt (a ^ 2))⁻¹ *
      ∑ m : AsymCanonicalMode Nt Ns,
        asymCanonicalSmoothModeCoeff Nt Ns a mass T x m * η.1 m) =
      (Real.sqrt (a ^ 2))⁻¹ *
        (c * ∑ m : AsymCanonicalMode Nt Ns,
          asymCanonicalSmoothModeCoeff Nt Ns a mass T x m * η.1 m) by ring]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro m _
  ring

theorem asymCanonicalRoughFieldFunction_add
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ)
    (η₁ η₂ : AsymCanonicalJoint Nt Ns) (x : AsymLatticeSites Nt Ns) :
    asymCanonicalRoughFieldFunction Nt Ns a mass T (η₁ + η₂) x =
      asymCanonicalRoughFieldFunction Nt Ns a mass T η₁ x +
        asymCanonicalRoughFieldFunction Nt Ns a mass T η₂ x := by
  unfold asymCanonicalRoughFieldFunction
  rw [show (η₁ + η₂).2 = η₁.2 + η₂.2 by rfl]
  simp_rw [Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib, mul_add]

theorem asymCanonicalRoughFieldFunction_smul
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T c : ℝ)
    (η : AsymCanonicalJoint Nt Ns) (x : AsymLatticeSites Nt Ns) :
    asymCanonicalRoughFieldFunction Nt Ns a mass T (c • η) x =
      c * asymCanonicalRoughFieldFunction Nt Ns a mass T η x := by
  unfold asymCanonicalRoughFieldFunction
  rw [show (c • η).2 = c • η.2 by rfl]
  simp_rw [Pi.smul_apply, smul_eq_mul]
  rw [show c * ((Real.sqrt (a ^ 2))⁻¹ *
      ∑ m : AsymCanonicalMode Nt Ns,
        asymCanonicalRoughModeCoeff Nt Ns a mass T x m * η.2 m) =
      (Real.sqrt (a ^ 2))⁻¹ *
        (c * ∑ m : AsymCanonicalMode Nt Ns,
          asymCanonicalRoughModeCoeff Nt Ns a mass T x m * η.2 m) by ring]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro m _
  ring

theorem asymCanonicalSumFieldFunction_add
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ)
    (η₁ η₂ : AsymCanonicalJoint Nt Ns) (x : AsymLatticeSites Nt Ns) :
    asymCanonicalSumFieldFunction Nt Ns a mass T (η₁ + η₂) x =
      asymCanonicalSumFieldFunction Nt Ns a mass T η₁ x +
        asymCanonicalSumFieldFunction Nt Ns a mass T η₂ x := by
  unfold asymCanonicalSumFieldFunction
  rw [asymCanonicalSmoothFieldFunction_add, asymCanonicalRoughFieldFunction_add]
  ring

theorem asymCanonicalSumFieldFunction_smul
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T c : ℝ)
    (η : AsymCanonicalJoint Nt Ns) (x : AsymLatticeSites Nt Ns) :
    asymCanonicalSumFieldFunction Nt Ns a mass T (c • η) x =
      c * asymCanonicalSumFieldFunction Nt Ns a mass T η x := by
  unfold asymCanonicalSumFieldFunction
  rw [asymCanonicalSmoothFieldFunction_smul, asymCanonicalRoughFieldFunction_smul]
  ring

theorem asymCanonicalSmoothFieldFunction_pointwise_measurable
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ) (x : AsymLatticeSites Nt Ns) :
    Measurable (fun η : AsymCanonicalJoint Nt Ns =>
      asymCanonicalSmoothFieldFunction Nt Ns a mass T η x) := by
  unfold asymCanonicalSmoothFieldFunction
  fun_prop

theorem asymCanonicalRoughFieldFunction_pointwise_measurable
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ) (x : AsymLatticeSites Nt Ns) :
    Measurable (fun η : AsymCanonicalJoint Nt Ns =>
      asymCanonicalRoughFieldFunction Nt Ns a mass T η x) := by
  unfold asymCanonicalRoughFieldFunction
  fun_prop

theorem asymCanonicalSumFieldFunction_pointwise_measurable
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ) (x : AsymLatticeSites Nt Ns) :
    Measurable (fun η : AsymCanonicalJoint Nt Ns =>
      asymCanonicalSumFieldFunction Nt Ns a mass T η x) := by
  unfold asymCanonicalSumFieldFunction
  exact (asymCanonicalSmoothFieldFunction_pointwise_measurable Nt Ns a mass T x).add
    (asymCanonicalRoughFieldFunction_pointwise_measurable Nt Ns a mass T x)

theorem asymCanonicalSmoothFieldFunction_measurable
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ) :
    Measurable (fun η : AsymCanonicalJoint Nt Ns =>
      asymCanonicalSmoothFieldFunction Nt Ns a mass T η) := by
  apply measurable_pi_iff.mpr
  intro x
  exact asymCanonicalSmoothFieldFunction_pointwise_measurable Nt Ns a mass T x

theorem asymCanonicalRoughFieldFunction_measurable
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ) :
    Measurable (fun η : AsymCanonicalJoint Nt Ns =>
      asymCanonicalRoughFieldFunction Nt Ns a mass T η) := by
  apply measurable_pi_iff.mpr
  intro x
  exact asymCanonicalRoughFieldFunction_pointwise_measurable Nt Ns a mass T x

theorem asymCanonicalSumFieldFunction_measurable
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ) :
    Measurable (fun η : AsymCanonicalJoint Nt Ns =>
      asymCanonicalSumFieldFunction Nt Ns a mass T η) := by
  apply measurable_pi_iff.mpr
  intro x
  exact asymCanonicalSumFieldFunction_pointwise_measurable Nt Ns a mass T x

noncomputable def asymCanonicalSumConfig (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (η : AsymCanonicalJoint Nt Ns) :
    Configuration (AsymLatticeField Nt Ns) :=
  asymLatticeFieldToConfig Nt Ns (asymCanonicalSumFieldFunction Nt Ns a mass T η)

@[simp] theorem asymCanonicalSumConfig_apply_delta
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ)
    (η : AsymCanonicalJoint Nt Ns) (x : AsymLatticeSites Nt Ns) :
    asymCanonicalSumConfig Nt Ns a mass T η (asymLatticeDelta Nt Ns x) =
      asymCanonicalSumFieldFunction Nt Ns a mass T η x := by
  rw [asymCanonicalSumConfig, asymLatticeFieldToConfig_apply]
  simp [asymLatticeDelta]

theorem asymCanonicalSumConfig_measurable
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ) :
    Measurable (asymCanonicalSumConfig Nt Ns a mass T) := by
  rw [show asymCanonicalSumConfig Nt Ns a mass T =
      fun η => asymEvalMapInv Nt Ns
        (asymCanonicalSumFieldFunction Nt Ns a mass T η) from by
          funext η
          rw [asymCanonicalSumConfig, asymLatticeFieldToConfig_eq_evalMapInv]]
  exact (asymEvalMapInv_measurable Nt Ns).comp
    (asymCanonicalSumFieldFunction_measurable Nt Ns a mass T)

noncomputable def asymCanonicalStdFieldFunction (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ)
    (ξ : EuclideanSpace ℝ (AsymCanonicalJointSumIndex Nt Ns)) :
    AsymLatticeField Nt Ns :=
  fun x =>
    (Real.sqrt (a ^ 2))⁻¹ *
      ∑ m : AsymCanonicalMode Nt Ns,
        asymCanonicalSmoothModeCoeff Nt Ns a mass T x m * ξ (Sum.inl m) +
    (Real.sqrt (a ^ 2))⁻¹ *
      ∑ m : AsymCanonicalMode Nt Ns,
        asymCanonicalRoughModeCoeff Nt Ns a mass T x m * ξ (Sum.inr m)

noncomputable def asymCanonicalStdToFieldLinearMap (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) :
    EuclideanSpace ℝ (AsymCanonicalJointSumIndex Nt Ns) →ₗ[ℝ] AsymLatticeField Nt Ns where
  toFun := asymCanonicalStdFieldFunction Nt Ns a mass T
  map_add' := by
    intro ξ ζ
    funext x
    change
      (Real.sqrt (a ^ 2))⁻¹ *
          ∑ m : AsymCanonicalMode Nt Ns,
            asymCanonicalSmoothModeCoeff Nt Ns a mass T x m *
              (ξ.ofLp (Sum.inl m) + ζ.ofLp (Sum.inl m)) +
        (Real.sqrt (a ^ 2))⁻¹ *
          ∑ m : AsymCanonicalMode Nt Ns,
            asymCanonicalRoughModeCoeff Nt Ns a mass T x m *
              (ξ.ofLp (Sum.inr m) + ζ.ofLp (Sum.inr m)) =
      ((Real.sqrt (a ^ 2))⁻¹ *
          ∑ m : AsymCanonicalMode Nt Ns,
            asymCanonicalSmoothModeCoeff Nt Ns a mass T x m * ξ.ofLp (Sum.inl m) +
        (Real.sqrt (a ^ 2))⁻¹ *
          ∑ m : AsymCanonicalMode Nt Ns,
            asymCanonicalRoughModeCoeff Nt Ns a mass T x m * ξ.ofLp (Sum.inr m)) +
        ((Real.sqrt (a ^ 2))⁻¹ *
          ∑ m : AsymCanonicalMode Nt Ns,
            asymCanonicalSmoothModeCoeff Nt Ns a mass T x m * ζ.ofLp (Sum.inl m) +
          (Real.sqrt (a ^ 2))⁻¹ *
            ∑ m : AsymCanonicalMode Nt Ns,
              asymCanonicalRoughModeCoeff Nt Ns a mass T x m * ζ.ofLp (Sum.inr m))
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    ring_nf
  map_smul' := by
    intro c ξ
    funext x
    change
      (Real.sqrt (a ^ 2))⁻¹ *
          ∑ m : AsymCanonicalMode Nt Ns,
            asymCanonicalSmoothModeCoeff Nt Ns a mass T x m * (c * ξ.ofLp (Sum.inl m)) +
        (Real.sqrt (a ^ 2))⁻¹ *
          ∑ m : AsymCanonicalMode Nt Ns,
            asymCanonicalRoughModeCoeff Nt Ns a mass T x m * (c * ξ.ofLp (Sum.inr m)) =
      (RingHom.id ℝ) c *
        ((Real.sqrt (a ^ 2))⁻¹ *
            ∑ m : AsymCanonicalMode Nt Ns,
              asymCanonicalSmoothModeCoeff Nt Ns a mass T x m * ξ.ofLp (Sum.inl m) +
          (Real.sqrt (a ^ 2))⁻¹ *
            ∑ m : AsymCanonicalMode Nt Ns,
              asymCanonicalRoughModeCoeff Nt Ns a mass T x m * ξ.ofLp (Sum.inr m))
    simp only [RingHom.id_apply]
    rw [mul_add]
    have hSmooth :
        (∑ m : AsymCanonicalMode Nt Ns,
            asymCanonicalSmoothModeCoeff Nt Ns a mass T x m * (c * ξ.ofLp (Sum.inl m))) =
          c * ∑ m : AsymCanonicalMode Nt Ns,
            asymCanonicalSmoothModeCoeff Nt Ns a mass T x m * ξ.ofLp (Sum.inl m) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro m _
      ring
    have hRough :
        (∑ m : AsymCanonicalMode Nt Ns,
            asymCanonicalRoughModeCoeff Nt Ns a mass T x m * (c * ξ.ofLp (Sum.inr m))) =
          c * ∑ m : AsymCanonicalMode Nt Ns,
            asymCanonicalRoughModeCoeff Nt Ns a mass T x m * ξ.ofLp (Sum.inr m) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro m _
      ring
    rw [hSmooth, hRough]
    ring

noncomputable def asymCanonicalStdToFieldCLM (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) :
    EuclideanSpace ℝ (AsymCanonicalJointSumIndex Nt Ns) →L[ℝ] AsymLatticeField Nt Ns :=
  { toLinearMap := asymCanonicalStdToFieldLinearMap Nt Ns a mass T
    cont := (asymCanonicalStdToFieldLinearMap Nt Ns a mass T).continuous_of_finiteDimensional }

noncomputable def asymCanonicalSumFieldLaw (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) : Measure (AsymLatticeField Nt Ns) :=
  (ProbabilityTheory.stdGaussian
      (EuclideanSpace ℝ (AsymCanonicalJointSumIndex Nt Ns))).map
    (asymCanonicalStdToFieldCLM Nt Ns a mass T)

instance asymCanonicalSumFieldLaw_isGaussian (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) :
    ProbabilityTheory.IsGaussian (asymCanonicalSumFieldLaw Nt Ns a mass T) := by
  unfold asymCanonicalSumFieldLaw
  infer_instance

noncomputable def asymSitePairingCLM (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (f : AsymLatticeField Nt Ns) :
    AsymLatticeField Nt Ns →L[ℝ] ℝ :=
  { toLinearMap :=
      { toFun := fun φ => ∑ x : AsymLatticeSites Nt Ns, f x * φ x
        map_add' := by
          intro φ ψ
          simp [mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro c φ
          simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm] }
    cont := (continuous_finset_sum _ fun x _ =>
      continuous_const.mul (continuous_apply x)) }

theorem asymCanonicalStdFieldFunction_eq_asymCanonicalSumFieldFunction
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ)
    (η : AsymCanonicalJoint Nt Ns) :
    asymCanonicalStdFieldFunction Nt Ns a mass T
        (WithLp.toLp 2
          (((MeasurableEquiv.sumPiEquivProdPi
            (fun _ : AsymCanonicalJointSumIndex Nt Ns => ℝ)).symm) η)) =
      asymCanonicalSumFieldFunction Nt Ns a mass T η := by
  funext x
  unfold asymCanonicalStdFieldFunction asymCanonicalSumFieldFunction
    asymCanonicalSmoothFieldFunction asymCanonicalRoughFieldFunction
  rfl

theorem asymCanonicalSumFieldLaw_eq_map_asymCanonicalSumFieldFunction
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ) :
    asymCanonicalSumFieldLaw Nt Ns a mass T =
      (asymCanonicalJointMeasure Nt Ns).map
        (asymCanonicalSumFieldFunction Nt Ns a mass T) := by
  unfold asymCanonicalSumFieldLaw
  rw [← asymCanonicalJointMeasure_map_stdGaussianEuclidean Nt Ns]
  have h_map_map :
      Measure.map (asymCanonicalStdToFieldCLM Nt Ns a mass T)
          ((asymCanonicalJointMeasure Nt Ns).map
            (fun η =>
              WithLp.toLp 2
                (((MeasurableEquiv.sumPiEquivProdPi
                  (fun _ : AsymCanonicalJointSumIndex Nt Ns => ℝ)).symm) η))) =
        Measure.map
          (fun η =>
            asymCanonicalStdToFieldCLM Nt Ns a mass T
              (WithLp.toLp 2
                (((MeasurableEquiv.sumPiEquivProdPi
                  (fun _ : AsymCanonicalJointSumIndex Nt Ns => ℝ)).symm) η)))
          (asymCanonicalJointMeasure Nt Ns) := by
    simpa [Function.comp] using
      (Measure.map_map
        (asymCanonicalStdToFieldCLM Nt Ns a mass T).measurable
        (by fun_prop : Measurable
          (fun η =>
            WithLp.toLp 2
              (((MeasurableEquiv.sumPiEquivProdPi
                (fun _ : AsymCanonicalJointSumIndex Nt Ns => ℝ)).symm) η))))
  rw [h_map_map]
  rw [show
      (fun η =>
        asymCanonicalStdToFieldCLM Nt Ns a mass T
          (WithLp.toLp 2
            (((MeasurableEquiv.sumPiEquivProdPi
              (fun _ : AsymCanonicalJointSumIndex Nt Ns => ℝ)).symm) η))) =
        asymCanonicalSumFieldFunction Nt Ns a mass T from by
          funext η
          exact asymCanonicalStdFieldFunction_eq_asymCanonicalSumFieldFunction
            Nt Ns a mass T η]

section Variance

private lemma pi_gaussian_eval_integral_zero {I : Type*} [Fintype I] (k : I) :
    ∫ η : I → ℝ, η k
      ∂(Measure.pi (fun _ : I => gaussianReal 0 1)) = 0 := by
  rw [integral_eval]
  exact integral_id_gaussianReal

private lemma pi_gaussian_eval_integral_sq {I : Type*} [Fintype I] (k : I) :
    ∫ η : I → ℝ, (η k) ^ 2
      ∂(Measure.pi (fun _ : I => gaussianReal 0 1)) = 1 := by
  have h_meas_sq : Measurable (fun x : ℝ => x ^ 2) := by
    fun_prop
  have h_eq :
      ∫ η : I → ℝ, (η k) ^ 2
        ∂(Measure.pi (fun _ : I => gaussianReal 0 1)) =
      ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) := by
    have := integral_comp_eval (μ := fun _ : I => gaussianReal 0 1)
      (i := k) (f := fun x : ℝ => x ^ 2) h_meas_sq.aestronglyMeasurable
    convert this using 1
  rw [h_eq]
  have h_var : Var[fun x : ℝ => x; gaussianReal 0 1] = 1 := by
    simpa using variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
  have h_mean : ∫ x : ℝ, x ∂(gaussianReal 0 1) = 0 := by
    simpa using integral_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
  have h_second :
      Var[fun x : ℝ => x; gaussianReal 0 1] =
        ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) := by
    exact variance_of_integral_eq_zero aemeasurable_id h_mean
  rw [← h_second, h_var]

private lemma pi_gaussian_eval_cross_zero {I : Type*} [Fintype I]
    {k l : I} (hkl : k ≠ l) :
    ∫ η : I → ℝ, η k * η l
      ∂(Measure.pi (fun _ : I => gaussianReal 0 1)) = 0 := by
  haveI : ∀ i : I, IsProbabilityMeasure ((fun _ : I => gaussianReal 0 1) i) := by
    intro i
    infer_instance
  have h_indep_id :
      iIndepFun (fun (i : I) η => (id : ℝ → ℝ) (η i))
        (Measure.pi (fun _ : I => gaussianReal 0 1)) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have h_indep_kl :
      IndepFun (fun η : I → ℝ => η k) (fun η : I → ℝ => η l)
        (Measure.pi (fun _ : I => gaussianReal 0 1)) :=
    h_indep_id.indepFun hkl
  have h_meas_k :
      AEStronglyMeasurable (fun η : I → ℝ => η k)
        (Measure.pi (fun _ : I => gaussianReal 0 1)) :=
    (measurable_pi_apply k).aestronglyMeasurable
  have h_meas_l :
      AEStronglyMeasurable (fun η : I → ℝ => η l)
        (Measure.pi (fun _ : I => gaussianReal 0 1)) :=
    (measurable_pi_apply l).aestronglyMeasurable
  rw [h_indep_kl.integral_fun_mul_eq_mul_integral h_meas_k h_meas_l]
  rw [pi_gaussian_eval_integral_zero, pi_gaussian_eval_integral_zero]
  ring

private lemma pi_gaussian_eval_cross {I : Type*} [Fintype I] [DecidableEq I] (k l : I) :
    ∫ η : I → ℝ, η k * η l
      ∂(Measure.pi (fun _ : I => gaussianReal 0 1)) =
    (if k = l then (1 : ℝ) else 0) := by
  by_cases h : k = l
  · subst h
    simp only [if_true]
    have h_sq : (fun η : I → ℝ => η k * η k) = (fun η : I → ℝ => (η k) ^ 2) := by
      funext η
      ring
    rw [h_sq, pi_gaussian_eval_integral_sq]
  · simp only [if_neg h]
    exact pi_gaussian_eval_cross_zero h

private theorem pi_gaussian_bilinear_moment {I : Type*} [Fintype I]
    (p q : I → ℝ) :
    ∫ η : I → ℝ, (∑ k, p k * η k) * (∑ l, q l * η l)
      ∂(Measure.pi (fun _ : I => gaussianReal 0 1)) =
      ∑ k, p k * q k := by
  classical
  have h_memLp : ∀ k : I, MemLp (fun η : I → ℝ => η k) 2
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
    intro k
    have h : MemLp (id ∘ fun η : I → ℝ => η k) 2
        (Measure.pi (fun _ : I => gaussianReal 0 1)) :=
      MemLp.comp_measurePreserving IsGaussian.memLp_two_id
        (measurePreserving_eval (μ := fun _ : I => gaussianReal 0 1) k)
    exact h
  have h_distrib : ∀ η : I → ℝ,
      (∑ k, p k * η k) * (∑ l, q l * η l) =
        ∑ k, ∑ l, (p k * q l) * (η k * η l) := by
    intro η
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    ring
  simp_rw [h_distrib]
  rw [integral_finset_sum]
  swap
  · intro k _
    refine integrable_finset_sum _ (fun l _ => ?_)
    refine Integrable.const_mul ?_ _
    exact MemLp.integrable_mul (h_memLp k) (h_memLp l)
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [integral_finset_sum]
  swap
  · intro l _
    refine Integrable.const_mul ?_ _
    exact MemLp.integrable_mul (h_memLp k) (h_memLp l)
  simp_rw [integral_const_mul, pi_gaussian_eval_cross]
  rw [Finset.sum_eq_single k]
  · simp
  · intro l _ hkl
    rw [if_neg (Ne.symm hkl)]
    ring
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

private lemma asymCanonicalSmoothFieldFunction_marginal_integrable
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ) (x : AsymLatticeSites Nt Ns) :
    Integrable (fun ηS : AsymCanonicalMode Nt Ns → ℝ =>
      (Real.sqrt (a ^ 2))⁻¹ *
        ∑ m : AsymCanonicalMode Nt Ns,
          asymCanonicalSmoothModeCoeff Nt Ns a mass T x m * ηS m)
      (Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) := by
  have h_sum : Integrable (fun ηS : AsymCanonicalMode Nt Ns → ℝ =>
      ∑ m : AsymCanonicalMode Nt Ns,
        asymCanonicalSmoothModeCoeff Nt Ns a mass T x m * ηS m)
      (Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) := by
    refine integrable_finset_sum _ (fun m _ => ?_)
    have h_eval : Integrable (fun ηS : AsymCanonicalMode Nt Ns → ℝ => ηS m)
        (Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) := by
      exact integrable_eval IsGaussian.integrable_id
    convert h_eval.const_mul (asymCanonicalSmoothModeCoeff Nt Ns a mass T x m)
  exact h_sum.const_mul _

private lemma asymCanonicalRoughFieldFunction_marginal_integrable
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ) (x : AsymLatticeSites Nt Ns) :
    Integrable (fun ηR : AsymCanonicalMode Nt Ns → ℝ =>
      (Real.sqrt (a ^ 2))⁻¹ *
        ∑ m : AsymCanonicalMode Nt Ns,
          asymCanonicalRoughModeCoeff Nt Ns a mass T x m * ηR m)
      (Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) := by
  have h_sum : Integrable (fun ηR : AsymCanonicalMode Nt Ns → ℝ =>
      ∑ m : AsymCanonicalMode Nt Ns,
        asymCanonicalRoughModeCoeff Nt Ns a mass T x m * ηR m)
      (Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) := by
    refine integrable_finset_sum _ (fun m _ => ?_)
    have h_eval : Integrable (fun ηR : AsymCanonicalMode Nt Ns → ℝ => ηR m)
        (Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) := by
      exact integrable_eval IsGaussian.integrable_id
    convert h_eval.const_mul (asymCanonicalRoughModeCoeff Nt Ns a mass T x m)
  exact h_sum.const_mul _

private lemma asymCanonicalSmoothFieldFunction_marginal_integral_zero
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ) (x : AsymLatticeSites Nt Ns) :
    ∫ ηS : AsymCanonicalMode Nt Ns → ℝ,
      (Real.sqrt (a ^ 2))⁻¹ *
        ∑ m : AsymCanonicalMode Nt Ns,
          asymCanonicalSmoothModeCoeff Nt Ns a mass T x m * ηS m
      ∂(Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) = 0 := by
  have hsum :
      ∫ ηS : AsymCanonicalMode Nt Ns → ℝ,
        ∑ m : AsymCanonicalMode Nt Ns,
          asymCanonicalSmoothModeCoeff Nt Ns a mass T x m * ηS m
        ∂(Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) = 0 := by
    rw [integral_finset_sum]
    · refine Finset.sum_eq_zero ?_
      intro m _
      rw [integral_const_mul, pi_gaussian_eval_integral_zero (k := m)]
      ring
    · intro m _
      have h_eval : Integrable (fun ηS : AsymCanonicalMode Nt Ns → ℝ => ηS m)
          (Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) := by
        exact integrable_eval IsGaussian.integrable_id
      convert h_eval.const_mul (asymCanonicalSmoothModeCoeff Nt Ns a mass T x m)
  rw [integral_const_mul, hsum]
  ring

private lemma asymCanonicalRoughFieldFunction_marginal_integral_zero
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ) (x : AsymLatticeSites Nt Ns) :
    ∫ ηR : AsymCanonicalMode Nt Ns → ℝ,
      (Real.sqrt (a ^ 2))⁻¹ *
        ∑ m : AsymCanonicalMode Nt Ns,
          asymCanonicalRoughModeCoeff Nt Ns a mass T x m * ηR m
      ∂(Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) = 0 := by
  have hsum :
      ∫ ηR : AsymCanonicalMode Nt Ns → ℝ,
        ∑ m : AsymCanonicalMode Nt Ns,
          asymCanonicalRoughModeCoeff Nt Ns a mass T x m * ηR m
        ∂(Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) = 0 := by
    rw [integral_finset_sum]
    · refine Finset.sum_eq_zero ?_
      intro m _
      rw [integral_const_mul, pi_gaussian_eval_integral_zero (k := m)]
      ring
    · intro m _
      have h_eval : Integrable (fun ηR : AsymCanonicalMode Nt Ns → ℝ => ηR m)
          (Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) := by
        exact integrable_eval IsGaussian.integrable_id
      convert h_eval.const_mul (asymCanonicalRoughModeCoeff Nt Ns a mass T x m)
  rw [integral_const_mul, hsum]
  ring

theorem asymCanonicalSmoothRough_cross_moment_zero
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ)
    (x y : AsymLatticeSites Nt Ns) :
    ∫ η : AsymCanonicalJoint Nt Ns,
      asymCanonicalSmoothFieldFunction Nt Ns a mass T η x *
        asymCanonicalRoughFieldFunction Nt Ns a mass T η y
      ∂(asymCanonicalJointMeasure Nt Ns) = 0 := by
  rw [asymCanonicalJointMeasure]
  simp only [asymCanonicalSmoothFieldFunction, asymCanonicalRoughFieldFunction]
  have h_factor :
      ∫ η : AsymCanonicalJoint Nt Ns,
        ((Real.sqrt (a ^ 2))⁻¹ *
            ∑ m : AsymCanonicalMode Nt Ns,
              asymCanonicalSmoothModeCoeff Nt Ns a mass T x m * η.1 m) *
          ((Real.sqrt (a ^ 2))⁻¹ *
            ∑ m : AsymCanonicalMode Nt Ns,
              asymCanonicalRoughModeCoeff Nt Ns a mass T y m * η.2 m)
        ∂(Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)).prod
          (Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) =
      (∫ ηS : AsymCanonicalMode Nt Ns → ℝ,
        (Real.sqrt (a ^ 2))⁻¹ *
          ∑ m : AsymCanonicalMode Nt Ns,
            asymCanonicalSmoothModeCoeff Nt Ns a mass T x m * ηS m
        ∂(Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1))) *
      (∫ ηR : AsymCanonicalMode Nt Ns → ℝ,
        (Real.sqrt (a ^ 2))⁻¹ *
          ∑ m : AsymCanonicalMode Nt Ns,
            asymCanonicalRoughModeCoeff Nt Ns a mass T y m * ηR m
        ∂(Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1))) := by
    simpa [AsymCanonicalJoint] using
      (integral_prod_mul
        (μ := Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1))
        (ν := Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1))
        (f := fun ηS : AsymCanonicalMode Nt Ns → ℝ =>
          (Real.sqrt (a ^ 2))⁻¹ *
            ∑ m : AsymCanonicalMode Nt Ns,
              asymCanonicalSmoothModeCoeff Nt Ns a mass T x m * ηS m)
        (g := fun ηR : AsymCanonicalMode Nt Ns → ℝ =>
          (Real.sqrt (a ^ 2))⁻¹ *
            ∑ m : AsymCanonicalMode Nt Ns,
              asymCanonicalRoughModeCoeff Nt Ns a mass T y m * ηR m))
  rw [h_factor,
    asymCanonicalSmoothFieldFunction_marginal_integral_zero Nt Ns a mass T x,
    asymCanonicalRoughFieldFunction_marginal_integral_zero Nt Ns a mass T y]
  ring

private lemma asymCanonicalEigenvalue_pos
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (_ha : 0 < a) (hmass : 0 < mass) (m : AsymCanonicalMode Nt Ns) :
    0 < asymCanonicalEigenvalue Nt Ns a mass m := by
  unfold asymCanonicalEigenvalue
  have h1 := latticeEigenvalue1d_nonneg Nt a m.1
  have h2 := latticeEigenvalue1d_nonneg Ns a m.2
  nlinarith [sq_pos_of_pos hmass]

private lemma asymCanonicalSmoothWeight_nonneg
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (m : AsymCanonicalMode Nt Ns) :
    0 ≤ asymCanonicalSmoothWeight Nt Ns a mass T m := by
  unfold asymCanonicalSmoothWeight
  exact div_nonneg (le_of_lt (Real.exp_pos _))
    (asymCanonicalEigenvalue_pos Nt Ns a mass ha hmass m).le

private lemma asymCanonicalRoughWeight_nonneg
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T) (m : AsymCanonicalMode Nt Ns) :
    0 ≤ asymCanonicalRoughWeight Nt Ns a mass T m := by
  unfold asymCanonicalRoughWeight
  have hLam := asymCanonicalEigenvalue_pos Nt Ns a mass ha hmass m
  have h_exp_le : Real.exp (-T * asymCanonicalEigenvalue Nt Ns a mass m) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith
  have h_num : 0 ≤ 1 - Real.exp (-T * asymCanonicalEigenvalue Nt Ns a mass m) := by
    linarith
  exact div_nonneg h_num hLam.le

private lemma asymCanonicalSmoothFieldFunction_self_moment
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (_hT : 0 < T) (x y : AsymLatticeSites Nt Ns) :
    ∫ η : AsymCanonicalJoint Nt Ns,
      asymCanonicalSmoothFieldFunction Nt Ns a mass T η x *
        asymCanonicalSmoothFieldFunction Nt Ns a mass T η y
      ∂(asymCanonicalJointMeasure Nt Ns) =
    (a ^ 2 : ℝ)⁻¹ *
      ∑ m : AsymCanonicalMode Nt Ns,
        asymCanonicalSmoothWeight Nt Ns a mass T m *
          asymCanonicalBasis Nt Ns m x *
          asymCanonicalBasis Nt Ns m y /
          asymCanonicalNormSq Nt Ns m := by
  rw [asymCanonicalJointMeasure]
  simp only [asymCanonicalSmoothFieldFunction]
  have h_fst :
      ∫ z : (AsymCanonicalMode Nt Ns → ℝ) × (AsymCanonicalMode Nt Ns → ℝ),
          ((Real.sqrt (a ^ 2))⁻¹ *
              ∑ m : AsymCanonicalMode Nt Ns,
                asymCanonicalSmoothModeCoeff Nt Ns a mass T x m * z.1 m) *
            ((Real.sqrt (a ^ 2))⁻¹ *
              ∑ m : AsymCanonicalMode Nt Ns,
                asymCanonicalSmoothModeCoeff Nt Ns a mass T y m * z.1 m)
          ∂(Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)).prod
            (Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) =
        ∫ ηS : AsymCanonicalMode Nt Ns → ℝ,
          ((Real.sqrt (a ^ 2))⁻¹ *
              ∑ m : AsymCanonicalMode Nt Ns,
                asymCanonicalSmoothModeCoeff Nt Ns a mass T x m * ηS m) *
            ((Real.sqrt (a ^ 2))⁻¹ *
              ∑ m : AsymCanonicalMode Nt Ns,
                asymCanonicalSmoothModeCoeff Nt Ns a mass T y m * ηS m)
          ∂Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1) := by
    simpa using integral_fun_fst (E := ℝ)
      (μ := Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1))
      (ν := Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1))
      (f := fun ηS : AsymCanonicalMode Nt Ns → ℝ =>
        ((Real.sqrt (a ^ 2))⁻¹ *
            ∑ m : AsymCanonicalMode Nt Ns,
              asymCanonicalSmoothModeCoeff Nt Ns a mass T x m * ηS m) *
          ((Real.sqrt (a ^ 2))⁻¹ *
            ∑ m : AsymCanonicalMode Nt Ns,
              asymCanonicalSmoothModeCoeff Nt Ns a mass T y m * ηS m))
  rw [h_fst]
  have ha_sq_pos : (0 : ℝ) < a ^ 2 := pow_pos ha 2
  have hsqrt_sq : (Real.sqrt (a ^ 2))⁻¹ * (Real.sqrt (a ^ 2))⁻¹ = (a ^ 2 : ℝ)⁻¹ := by
    rw [← mul_inv, ← Real.sqrt_mul (le_of_lt ha_sq_pos),
      Real.sqrt_mul_self (le_of_lt ha_sq_pos)]
  have h_rewrite : ∀ ηS : AsymCanonicalMode Nt Ns → ℝ,
      ((Real.sqrt (a ^ 2))⁻¹ *
          ∑ m : AsymCanonicalMode Nt Ns,
            asymCanonicalSmoothModeCoeff Nt Ns a mass T x m * ηS m) *
        ((Real.sqrt (a ^ 2))⁻¹ *
          ∑ m : AsymCanonicalMode Nt Ns,
            asymCanonicalSmoothModeCoeff Nt Ns a mass T y m * ηS m) =
      (a ^ 2 : ℝ)⁻¹ *
        ((∑ m : AsymCanonicalMode Nt Ns,
            asymCanonicalSmoothModeCoeff Nt Ns a mass T x m * ηS m) *
          (∑ l : AsymCanonicalMode Nt Ns,
            asymCanonicalSmoothModeCoeff Nt Ns a mass T y l * ηS l)) := by
    intro ηS
    rw [show ∀ A B C D : ℝ, (A * B) * (C * D) = (A * C) * (B * D) by
      intro A B C D; ring, hsqrt_sq]
  simp_rw [h_rewrite, integral_const_mul]
  rw [pi_gaussian_bilinear_moment
    (p := fun m => asymCanonicalSmoothModeCoeff Nt Ns a mass T x m)
    (q := fun l => asymCanonicalSmoothModeCoeff Nt Ns a mass T y l)]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro m _
  have hC :
      0 ≤ asymCanonicalSmoothWeight Nt Ns a mass T m / asymCanonicalNormSq Nt Ns m := by
    apply div_nonneg
    · exact asymCanonicalSmoothWeight_nonneg Nt Ns a mass ha hmass T m
    · exact (mul_nonneg
        (le_of_lt (latticeFourierNormSq_pos Nt m.1 m.1.isLt))
        (le_of_lt (latticeFourierNormSq_pos Ns m.2 m.2.isLt)))
  have h_sq :
      Real.sqrt (asymCanonicalSmoothWeight Nt Ns a mass T m / asymCanonicalNormSq Nt Ns m) *
        Real.sqrt (asymCanonicalSmoothWeight Nt Ns a mass T m / asymCanonicalNormSq Nt Ns m) =
      asymCanonicalSmoothWeight Nt Ns a mass T m / asymCanonicalNormSq Nt Ns m :=
    Real.mul_self_sqrt hC
  unfold asymCanonicalSmoothModeCoeff
  calc
    Real.sqrt (asymCanonicalSmoothWeight Nt Ns a mass T m / asymCanonicalNormSq Nt Ns m) *
        asymCanonicalBasis Nt Ns m x *
        (Real.sqrt (asymCanonicalSmoothWeight Nt Ns a mass T m / asymCanonicalNormSq Nt Ns m) *
          asymCanonicalBasis Nt Ns m y)
      = (Real.sqrt (asymCanonicalSmoothWeight Nt Ns a mass T m / asymCanonicalNormSq Nt Ns m) *
          Real.sqrt (asymCanonicalSmoothWeight Nt Ns a mass T m / asymCanonicalNormSq Nt Ns m)) *
          asymCanonicalBasis Nt Ns m x *
          asymCanonicalBasis Nt Ns m y := by ring
    _ = asymCanonicalSmoothWeight Nt Ns a mass T m *
          asymCanonicalBasis Nt Ns m x *
          asymCanonicalBasis Nt Ns m y / asymCanonicalNormSq Nt Ns m := by
          rw [h_sq]
          ring

private lemma asymCanonicalRoughFieldFunction_self_moment
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T) (x y : AsymLatticeSites Nt Ns) :
    ∫ η : AsymCanonicalJoint Nt Ns,
      asymCanonicalRoughFieldFunction Nt Ns a mass T η x *
        asymCanonicalRoughFieldFunction Nt Ns a mass T η y
      ∂(asymCanonicalJointMeasure Nt Ns) =
    (a ^ 2 : ℝ)⁻¹ *
      ∑ m : AsymCanonicalMode Nt Ns,
        asymCanonicalRoughWeight Nt Ns a mass T m *
          asymCanonicalBasis Nt Ns m x *
          asymCanonicalBasis Nt Ns m y /
          asymCanonicalNormSq Nt Ns m := by
  rw [asymCanonicalJointMeasure]
  simp only [asymCanonicalRoughFieldFunction]
  have h_snd :
      ∫ z : (AsymCanonicalMode Nt Ns → ℝ) × (AsymCanonicalMode Nt Ns → ℝ),
          ((Real.sqrt (a ^ 2))⁻¹ *
              ∑ m : AsymCanonicalMode Nt Ns,
                asymCanonicalRoughModeCoeff Nt Ns a mass T x m * z.2 m) *
            ((Real.sqrt (a ^ 2))⁻¹ *
              ∑ m : AsymCanonicalMode Nt Ns,
                asymCanonicalRoughModeCoeff Nt Ns a mass T y m * z.2 m)
          ∂(Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)).prod
            (Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) =
        ∫ ηR : AsymCanonicalMode Nt Ns → ℝ,
          ((Real.sqrt (a ^ 2))⁻¹ *
              ∑ m : AsymCanonicalMode Nt Ns,
                asymCanonicalRoughModeCoeff Nt Ns a mass T x m * ηR m) *
            ((Real.sqrt (a ^ 2))⁻¹ *
              ∑ m : AsymCanonicalMode Nt Ns,
                asymCanonicalRoughModeCoeff Nt Ns a mass T y m * ηR m)
          ∂Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1) := by
    simpa using integral_fun_snd (E := ℝ)
      (μ := Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1))
      (ν := Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1))
      (f := fun ηR : AsymCanonicalMode Nt Ns → ℝ =>
        ((Real.sqrt (a ^ 2))⁻¹ *
            ∑ m : AsymCanonicalMode Nt Ns,
              asymCanonicalRoughModeCoeff Nt Ns a mass T x m * ηR m) *
          ((Real.sqrt (a ^ 2))⁻¹ *
            ∑ m : AsymCanonicalMode Nt Ns,
              asymCanonicalRoughModeCoeff Nt Ns a mass T y m * ηR m))
  rw [h_snd]
  have ha_sq_pos : (0 : ℝ) < a ^ 2 := pow_pos ha 2
  have hsqrt_sq : (Real.sqrt (a ^ 2))⁻¹ * (Real.sqrt (a ^ 2))⁻¹ = (a ^ 2 : ℝ)⁻¹ := by
    rw [← mul_inv, ← Real.sqrt_mul (le_of_lt ha_sq_pos),
      Real.sqrt_mul_self (le_of_lt ha_sq_pos)]
  have h_rewrite : ∀ ηR : AsymCanonicalMode Nt Ns → ℝ,
      ((Real.sqrt (a ^ 2))⁻¹ *
          ∑ m : AsymCanonicalMode Nt Ns,
            asymCanonicalRoughModeCoeff Nt Ns a mass T x m * ηR m) *
        ((Real.sqrt (a ^ 2))⁻¹ *
          ∑ m : AsymCanonicalMode Nt Ns,
            asymCanonicalRoughModeCoeff Nt Ns a mass T y m * ηR m) =
      (a ^ 2 : ℝ)⁻¹ *
        ((∑ m : AsymCanonicalMode Nt Ns,
            asymCanonicalRoughModeCoeff Nt Ns a mass T x m * ηR m) *
          (∑ l : AsymCanonicalMode Nt Ns,
            asymCanonicalRoughModeCoeff Nt Ns a mass T y l * ηR l)) := by
    intro ηR
    rw [show ∀ A B C D : ℝ, (A * B) * (C * D) = (A * C) * (B * D) by
      intro A B C D; ring, hsqrt_sq]
  simp_rw [h_rewrite, integral_const_mul]
  rw [pi_gaussian_bilinear_moment
    (p := fun m => asymCanonicalRoughModeCoeff Nt Ns a mass T x m)
    (q := fun l => asymCanonicalRoughModeCoeff Nt Ns a mass T y l)]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro m _
  have hC :
      0 ≤ asymCanonicalRoughWeight Nt Ns a mass T m / asymCanonicalNormSq Nt Ns m := by
    apply div_nonneg
    · exact asymCanonicalRoughWeight_nonneg Nt Ns a mass ha hmass T hT m
    · exact (mul_nonneg
        (le_of_lt (latticeFourierNormSq_pos Nt m.1 m.1.isLt))
        (le_of_lt (latticeFourierNormSq_pos Ns m.2 m.2.isLt)))
  have h_sq :
      Real.sqrt (asymCanonicalRoughWeight Nt Ns a mass T m / asymCanonicalNormSq Nt Ns m) *
        Real.sqrt (asymCanonicalRoughWeight Nt Ns a mass T m / asymCanonicalNormSq Nt Ns m) =
      asymCanonicalRoughWeight Nt Ns a mass T m / asymCanonicalNormSq Nt Ns m :=
    Real.mul_self_sqrt hC
  unfold asymCanonicalRoughModeCoeff
  calc
    Real.sqrt (asymCanonicalRoughWeight Nt Ns a mass T m / asymCanonicalNormSq Nt Ns m) *
        asymCanonicalBasis Nt Ns m x *
        (Real.sqrt (asymCanonicalRoughWeight Nt Ns a mass T m / asymCanonicalNormSq Nt Ns m) *
          asymCanonicalBasis Nt Ns m y)
      = (Real.sqrt (asymCanonicalRoughWeight Nt Ns a mass T m / asymCanonicalNormSq Nt Ns m) *
          Real.sqrt (asymCanonicalRoughWeight Nt Ns a mass T m / asymCanonicalNormSq Nt Ns m)) *
          asymCanonicalBasis Nt Ns m x *
          asymCanonicalBasis Nt Ns m y := by ring
    _ = asymCanonicalRoughWeight Nt Ns a mass T m *
          asymCanonicalBasis Nt Ns m x *
          asymCanonicalBasis Nt Ns m y / asymCanonicalNormSq Nt Ns m := by
          rw [h_sq]
          ring

private lemma asymCanonicalRoughSmooth_cross_moment_zero
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ)
    (x y : AsymLatticeSites Nt Ns) :
    ∫ η : AsymCanonicalJoint Nt Ns,
      asymCanonicalRoughFieldFunction Nt Ns a mass T η x *
        asymCanonicalSmoothFieldFunction Nt Ns a mass T η y
      ∂(asymCanonicalJointMeasure Nt Ns) = 0 := by
  have h_swap : ∀ η : AsymCanonicalJoint Nt Ns,
      asymCanonicalRoughFieldFunction Nt Ns a mass T η x *
          asymCanonicalSmoothFieldFunction Nt Ns a mass T η y =
        asymCanonicalSmoothFieldFunction Nt Ns a mass T η y *
          asymCanonicalRoughFieldFunction Nt Ns a mass T η x := by
    intro η
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall h_swap)]
  exact asymCanonicalSmoothRough_cross_moment_zero Nt Ns a mass T y x

theorem asymCanonicalSmoothFieldFunction_memLp_two
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ)
    (z : AsymLatticeSites Nt Ns) :
    MemLp (fun η : AsymCanonicalJoint Nt Ns =>
      asymCanonicalSmoothFieldFunction Nt Ns a mass T η z) 2
      (asymCanonicalJointMeasure Nt Ns) := by
  unfold asymCanonicalSmoothFieldFunction
  refine MemLp.const_mul ?_ _
  refine memLp_finset_sum _ (fun m _ => ?_)
  refine MemLp.const_mul ?_ _
  rw [asymCanonicalJointMeasure]
  have h : MemLp (fun ηS : AsymCanonicalMode Nt Ns → ℝ => ηS m) 2
      (Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) :=
    MemLp.comp_measurePreserving IsGaussian.memLp_two_id
      (measurePreserving_eval (μ := fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1) m)
  exact h.comp_measurePreserving
    (μ := (Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)).prod
      (Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)))
    measurePreserving_fst

theorem asymCanonicalRoughFieldFunction_memLp_two
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ)
    (z : AsymLatticeSites Nt Ns) :
    MemLp (fun η : AsymCanonicalJoint Nt Ns =>
      asymCanonicalRoughFieldFunction Nt Ns a mass T η z) 2
      (asymCanonicalJointMeasure Nt Ns) := by
  unfold asymCanonicalRoughFieldFunction
  refine MemLp.const_mul ?_ _
  refine memLp_finset_sum _ (fun m _ => ?_)
  refine MemLp.const_mul ?_ _
  rw [asymCanonicalJointMeasure]
  have h : MemLp (fun ηR : AsymCanonicalMode Nt Ns → ℝ => ηR m) 2
      (Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) :=
    MemLp.comp_measurePreserving IsGaussian.memLp_two_id
      (measurePreserving_eval (μ := fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1) m)
  exact h.comp_measurePreserving
    (μ := (Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)).prod
      (Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)))
    measurePreserving_snd

theorem asymCanonicalSumFieldFunction_memLp_two
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ)
    (z : AsymLatticeSites Nt Ns) :
    MemLp (fun η : AsymCanonicalJoint Nt Ns =>
      asymCanonicalSumFieldFunction Nt Ns a mass T η z) 2
      (asymCanonicalJointMeasure Nt Ns) := by
  have hs := asymCanonicalSmoothFieldFunction_memLp_two Nt Ns a mass T z
  have hr := asymCanonicalRoughFieldFunction_memLp_two Nt Ns a mass T z
  have hsum : MemLp
      ((fun η : AsymCanonicalJoint Nt Ns =>
          asymCanonicalSmoothFieldFunction Nt Ns a mass T η z) +
        (fun η : AsymCanonicalJoint Nt Ns =>
          asymCanonicalRoughFieldFunction Nt Ns a mass T η z))
      2 (asymCanonicalJointMeasure Nt Ns) := hs.add hr
  simpa [Pi.add_apply, asymCanonicalSumFieldFunction] using hsum

theorem asymCanonicalSumFieldFunction_covariance
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T) (x y : AsymLatticeSites Nt Ns) :
    ∫ η : AsymCanonicalJoint Nt Ns,
      asymCanonicalSumFieldFunction Nt Ns a mass T η x *
        asymCanonicalSumFieldFunction Nt Ns a mass T η y
      ∂(asymCanonicalJointMeasure Nt Ns) =
    (a ^ 2 : ℝ)⁻¹ *
      ∑ m : AsymCanonicalMode Nt Ns,
        asymCanonicalBasis Nt Ns m x *
          asymCanonicalBasis Nt Ns m y /
          (asymCanonicalEigenvalue Nt Ns a mass m *
            asymCanonicalNormSq Nt Ns m) := by
  have h_ss := asymCanonicalSmoothFieldFunction_self_moment Nt Ns a mass ha hmass T hT x y
  have h_rr := asymCanonicalRoughFieldFunction_self_moment Nt Ns a mass ha hmass T hT x y
  have h_sr := asymCanonicalSmoothRough_cross_moment_zero Nt Ns a mass T x y
  have h_rs := asymCanonicalRoughSmooth_cross_moment_zero Nt Ns a mass T x y
  let fss : AsymCanonicalJoint Nt Ns → ℝ := fun η =>
    asymCanonicalSmoothFieldFunction Nt Ns a mass T η x *
      asymCanonicalSmoothFieldFunction Nt Ns a mass T η y
  let fsr : AsymCanonicalJoint Nt Ns → ℝ := fun η =>
    asymCanonicalSmoothFieldFunction Nt Ns a mass T η x *
      asymCanonicalRoughFieldFunction Nt Ns a mass T η y
  let frs : AsymCanonicalJoint Nt Ns → ℝ := fun η =>
    asymCanonicalRoughFieldFunction Nt Ns a mass T η x *
      asymCanonicalSmoothFieldFunction Nt Ns a mass T η y
  let frr : AsymCanonicalJoint Nt Ns → ℝ := fun η =>
    asymCanonicalRoughFieldFunction Nt Ns a mass T η x *
      asymCanonicalRoughFieldFunction Nt Ns a mass T η y
  have h_eq : ∀ η : AsymCanonicalJoint Nt Ns,
      asymCanonicalSumFieldFunction Nt Ns a mass T η x *
        asymCanonicalSumFieldFunction Nt Ns a mass T η y =
      fss η + (fsr η + (frs η + frr η)) := by
    intro η
    simp [asymCanonicalSumFieldFunction, fss, fsr, frs, frr]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall h_eq)]
  have h_ss_int : Integrable (fun η : AsymCanonicalJoint Nt Ns =>
      asymCanonicalSmoothFieldFunction Nt Ns a mass T η x *
        asymCanonicalSmoothFieldFunction Nt Ns a mass T η y)
      (asymCanonicalJointMeasure Nt Ns) :=
    (asymCanonicalSmoothFieldFunction_memLp_two Nt Ns a mass T x).integrable_mul
      (asymCanonicalSmoothFieldFunction_memLp_two Nt Ns a mass T y)
  have h_sr_int : Integrable (fun η : AsymCanonicalJoint Nt Ns =>
      asymCanonicalSmoothFieldFunction Nt Ns a mass T η x *
        asymCanonicalRoughFieldFunction Nt Ns a mass T η y)
      (asymCanonicalJointMeasure Nt Ns) :=
    (asymCanonicalSmoothFieldFunction_memLp_two Nt Ns a mass T x).integrable_mul
      (asymCanonicalRoughFieldFunction_memLp_two Nt Ns a mass T y)
  have h_rs_int : Integrable (fun η : AsymCanonicalJoint Nt Ns =>
      asymCanonicalRoughFieldFunction Nt Ns a mass T η x *
        asymCanonicalSmoothFieldFunction Nt Ns a mass T η y)
      (asymCanonicalJointMeasure Nt Ns) :=
    (asymCanonicalRoughFieldFunction_memLp_two Nt Ns a mass T x).integrable_mul
      (asymCanonicalSmoothFieldFunction_memLp_two Nt Ns a mass T y)
  have h_rr_int : Integrable (fun η : AsymCanonicalJoint Nt Ns =>
      asymCanonicalRoughFieldFunction Nt Ns a mass T η x *
        asymCanonicalRoughFieldFunction Nt Ns a mass T η y)
      (asymCanonicalJointMeasure Nt Ns) :=
    (asymCanonicalRoughFieldFunction_memLp_two Nt Ns a mass T x).integrable_mul
      (asymCanonicalRoughFieldFunction_memLp_two Nt Ns a mass T y)
  have h_rest : Integrable (fun η : AsymCanonicalJoint Nt Ns =>
      fsr η + (frs η + frr η)) (asymCanonicalJointMeasure Nt Ns) :=
    h_sr_int.add (h_rs_int.add h_rr_int)
  calc
    ∫ η : AsymCanonicalJoint Nt Ns, fss η + (fsr η + (frs η + frr η))
        ∂(asymCanonicalJointMeasure Nt Ns)
      = (∫ η : AsymCanonicalJoint Nt Ns, fss η ∂(asymCanonicalJointMeasure Nt Ns)) +
          ∫ η : AsymCanonicalJoint Nt Ns, fsr η + (frs η + frr η)
            ∂(asymCanonicalJointMeasure Nt Ns) := by
              rw [integral_add h_ss_int h_rest]
    _ = (∫ η : AsymCanonicalJoint Nt Ns, fss η ∂(asymCanonicalJointMeasure Nt Ns)) +
          ((∫ η : AsymCanonicalJoint Nt Ns, fsr η ∂(asymCanonicalJointMeasure Nt Ns)) +
            ((∫ η : AsymCanonicalJoint Nt Ns, frs η ∂(asymCanonicalJointMeasure Nt Ns)) +
              ∫ η : AsymCanonicalJoint Nt Ns, frr η ∂(asymCanonicalJointMeasure Nt Ns))) := by
              have h_rest_split :
                  ∫ η : AsymCanonicalJoint Nt Ns, fsr η + (frs η + frr η)
                    ∂(asymCanonicalJointMeasure Nt Ns) =
                    (∫ η : AsymCanonicalJoint Nt Ns, fsr η ∂(asymCanonicalJointMeasure Nt Ns)) +
                      ((∫ η : AsymCanonicalJoint Nt Ns, frs η ∂(asymCanonicalJointMeasure Nt Ns)) +
                        ∫ η : AsymCanonicalJoint Nt Ns, frr η
                          ∂(asymCanonicalJointMeasure Nt Ns)) := by
                have h1 :
                    ∫ η : AsymCanonicalJoint Nt Ns, (fsr + (frs + frr)) η
                      ∂(asymCanonicalJointMeasure Nt Ns) =
                      (∫ η : AsymCanonicalJoint Nt Ns, fsr η ∂(asymCanonicalJointMeasure Nt Ns)) +
                        ∫ η : AsymCanonicalJoint Nt Ns, (frs + frr) η
                          ∂(asymCanonicalJointMeasure Nt Ns) := by
                  simpa using (integral_add h_sr_int (h_rs_int.add h_rr_int))
                have h2 :
                    ∫ η : AsymCanonicalJoint Nt Ns, (frs + frr) η
                      ∂(asymCanonicalJointMeasure Nt Ns) =
                      (∫ η : AsymCanonicalJoint Nt Ns, frs η ∂(asymCanonicalJointMeasure Nt Ns)) +
                        ∫ η : AsymCanonicalJoint Nt Ns, frr η
                          ∂(asymCanonicalJointMeasure Nt Ns) := by
                  simpa using (integral_add h_rs_int h_rr_int)
                calc
                  ∫ η : AsymCanonicalJoint Nt Ns, (fsr + (frs + frr)) η
                      ∂(asymCanonicalJointMeasure Nt Ns)
                    = (∫ η : AsymCanonicalJoint Nt Ns, fsr η ∂(asymCanonicalJointMeasure Nt Ns)) +
                        ∫ η : AsymCanonicalJoint Nt Ns, (frs + frr) η
                          ∂(asymCanonicalJointMeasure Nt Ns) := h1
                  _ = (∫ η : AsymCanonicalJoint Nt Ns, fsr η ∂(asymCanonicalJointMeasure Nt Ns)) +
                        ((∫ η : AsymCanonicalJoint Nt Ns, frs η
                            ∂(asymCanonicalJointMeasure Nt Ns)) +
                          ∫ η : AsymCanonicalJoint Nt Ns, frr η
                            ∂(asymCanonicalJointMeasure Nt Ns)) := by rw [h2]
              exact congrArg
                ((∫ η : AsymCanonicalJoint Nt Ns, fss η ∂(asymCanonicalJointMeasure Nt Ns)) + ·)
                h_rest_split
    _ = (a ^ 2 : ℝ)⁻¹ *
          ∑ m : AsymCanonicalMode Nt Ns,
            asymCanonicalBasis Nt Ns m x * asymCanonicalBasis Nt Ns m y /
              (asymCanonicalEigenvalue Nt Ns a mass m * asymCanonicalNormSq Nt Ns m) := by
              rw [h_ss, h_rr, h_sr, h_rs]
              set S : ℝ :=
                ∑ m : AsymCanonicalMode Nt Ns,
                  asymCanonicalSmoothWeight Nt Ns a mass T m *
                    asymCanonicalBasis Nt Ns m x *
                    asymCanonicalBasis Nt Ns m y /
                    asymCanonicalNormSq Nt Ns m
              set R : ℝ :=
                ∑ m : AsymCanonicalMode Nt Ns,
                  asymCanonicalRoughWeight Nt Ns a mass T m *
                    asymCanonicalBasis Nt Ns m x *
                    asymCanonicalBasis Nt Ns m y /
                    asymCanonicalNormSq Nt Ns m
              rw [show (a ^ 2 : ℝ)⁻¹ * S + (0 + (0 + (a ^ 2 : ℝ)⁻¹ * R)) =
                  (a ^ 2 : ℝ)⁻¹ * (S + R) by ring]
              refine congrArg ((a ^ 2 : ℝ)⁻¹ * ·) ?_
              dsimp [S, R]
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro m _
              set B :=
                asymCanonicalBasis Nt Ns m x * asymCanonicalBasis Nt Ns m y /
                  asymCanonicalNormSq Nt Ns m
              calc
                asymCanonicalSmoothWeight Nt Ns a mass T m *
                    asymCanonicalBasis Nt Ns m x * asymCanonicalBasis Nt Ns m y /
                    asymCanonicalNormSq Nt Ns m +
                  asymCanonicalRoughWeight Nt Ns a mass T m *
                    asymCanonicalBasis Nt Ns m x * asymCanonicalBasis Nt Ns m y /
                    asymCanonicalNormSq Nt Ns m
                  = (asymCanonicalSmoothWeight Nt Ns a mass T m +
                      asymCanonicalRoughWeight Nt Ns a mass T m) * B := by
                        dsimp [B]
                        ring
              _ = (asymCanonicalEigenvalue Nt Ns a mass m)⁻¹ * B := by
                    rw [asymCanonicalSmoothWeight_add_roughWeight]
              _ = asymCanonicalBasis Nt Ns m x * asymCanonicalBasis Nt Ns m y /
                    (asymCanonicalEigenvalue Nt Ns a mass m * asymCanonicalNormSq Nt Ns m) := by
                    dsimp [B]
                    field_simp

private theorem latticeCovarianceAsymGJ_eq_inv_a_sq_bare
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
  (f g : AsymLatticeField Nt Ns) :
    GaussianField.covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass) f g =
      (a ^ 2 : ℝ)⁻¹ *
        GaussianField.covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass) f g := by
  have hsqrt : Real.sqrt (a ^ 2) = a := Real.sqrt_sq ha.le
  unfold latticeCovarianceAsymGJ GaussianField.covariance
  change @inner ℝ ell2' _
      ((Real.sqrt (a ^ 2))⁻¹ • spectralLatticeCovarianceAsym Nt Ns a mass ha hmass f)
      ((Real.sqrt (a ^ 2))⁻¹ • spectralLatticeCovarianceAsym Nt Ns a mass ha hmass g) =
      (a ^ 2 : ℝ)⁻¹ *
        @inner ℝ ell2' _
          (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass f)
          (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass g)
  rw [real_inner_smul_left, real_inner_smul_right]
  field_simp [hsqrt, ne_of_gt ha]
  simp [hsqrt]

theorem asymCanonicalSumFieldFunction_covariance_eq_GJ
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T) (x y : AsymLatticeSites Nt Ns) :
    let δx : AsymLatticeField Nt Ns := fun z => if z = x then 1 else 0
    let δy : AsymLatticeField Nt Ns := fun z => if z = y then 1 else 0
    ∫ η : AsymCanonicalJoint Nt Ns,
      asymCanonicalSumFieldFunction Nt Ns a mass T η x *
        asymCanonicalSumFieldFunction Nt Ns a mass T η y
      ∂(asymCanonicalJointMeasure Nt Ns) =
    GaussianField.covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass) δx δy := by
  intro δx δy
  rw [asymCanonicalSumFieldFunction_covariance Nt Ns a mass ha hmass T hT x y]
  rw [latticeCovarianceAsymGJ_eq_inv_a_sq_bare Nt Ns a mass ha hmass]
  refine congrArg ((a ^ 2 : ℝ)⁻¹ * ·) ?_
  symm
  calc
    GaussianField.covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass) δx δy
      = ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
          (∑ z, δx z *
            (latticeFourierBasisFun Nt m₁ z.1 * latticeFourierBasisFun Ns m₂ z.2)) *
          (∑ z, δy z *
            (latticeFourierBasisFun Nt m₁ z.1 * latticeFourierBasisFun Ns m₂ z.2)) /
          ((latticeEigenvalue1d Nt a m₁ + latticeEigenvalue1d Ns a m₂ + mass ^ 2) *
            latticeFourierNormSq Nt m₁ * latticeFourierNormSq Ns m₂) := by
            simpa using
              (abstract_spectral_eq_dft_spectral_2d_asym Nt Ns a mass ha hmass δx δy)
    _ = ∑ m : AsymCanonicalMode Nt Ns,
          asymCanonicalBasis Nt Ns m x * asymCanonicalBasis Nt Ns m y /
            (asymCanonicalEigenvalue Nt Ns a mass m * asymCanonicalNormSq Nt Ns m) := by
            rw [Fintype.sum_prod_type]
            simp [asymCanonicalBasis, asymCanonicalEigenvalue,
              asymCanonicalNormSq, δx, δy, mul_assoc]

private lemma latticeCovarianceAsymGJ_eq_sum_delta_covariance
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f g : AsymLatticeField Nt Ns) :
    GaussianField.covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass) f g =
      ∑ x : AsymLatticeSites Nt Ns,
        ∑ y : AsymLatticeSites Nt Ns,
          f x * g y *
            GaussianField.covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass)
              (asymLatticeDelta Nt Ns x) (asymLatticeDelta Nt Ns y) := by
  rw [asymField_basis_decomposition Nt Ns f, asymField_basis_decomposition Nt Ns g]
  simp only [GaussianField.covariance, map_sum, map_smul, Pi.smul_apply, smul_eq_mul, sum_inner,
    inner_sum, real_inner_smul_left, real_inner_smul_right, Finset.sum_apply]
  have hsum_f : ∀ x, ∑ x₂, f x₂ * asymLatticeDelta Nt Ns x₂ x = f x := by
    intro x
    simp [asymLatticeDelta]
  have hsum_g : ∀ x, ∑ x₁, g x₁ * asymLatticeDelta Nt Ns x₁ x = g x := by
    intro x
    simp [asymLatticeDelta]
  simp_rw [hsum_f, hsum_g]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro x _
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [real_inner_comm]
  ring

private lemma asymCanonicalSmoothFieldFunction_integral_zero
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ)
    (x : AsymLatticeSites Nt Ns) :
    ∫ η : AsymCanonicalJoint Nt Ns,
      asymCanonicalSmoothFieldFunction Nt Ns a mass T η x
      ∂(asymCanonicalJointMeasure Nt Ns) = 0 := by
  rw [asymCanonicalJointMeasure]
  rw [show (fun η : AsymCanonicalJoint Nt Ns =>
      asymCanonicalSmoothFieldFunction Nt Ns a mass T η x) =
      (fun z : (AsymCanonicalMode Nt Ns → ℝ) × (AsymCanonicalMode Nt Ns → ℝ) =>
        asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T z.1 x) by
      funext η
      exact asymCanonicalSmoothFieldFunction_eq_of_fst Nt Ns a mass T η.1 η.2 x]
  rw [integral_fun_fst (E := ℝ)
    (μ := Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1))
    (ν := Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1))
    (f := fun ηS : AsymCanonicalMode Nt Ns → ℝ =>
      asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS x)]
  simpa [asymCanonicalSmoothFieldFunctionOfFst] using
    asymCanonicalSmoothFieldFunction_marginal_integral_zero Nt Ns a mass T x

private lemma asymCanonicalRoughFieldFunction_integral_zero
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ)
    (x : AsymLatticeSites Nt Ns) :
    ∫ η : AsymCanonicalJoint Nt Ns,
      asymCanonicalRoughFieldFunction Nt Ns a mass T η x
      ∂(asymCanonicalJointMeasure Nt Ns) = 0 := by
  rw [asymCanonicalJointMeasure]
  rw [show (fun η : AsymCanonicalJoint Nt Ns =>
      asymCanonicalRoughFieldFunction Nt Ns a mass T η x) =
      (fun z : (AsymCanonicalMode Nt Ns → ℝ) × (AsymCanonicalMode Nt Ns → ℝ) =>
        asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T z.2 x) by
      funext η
      exact asymCanonicalRoughFieldFunction_eq_of_snd Nt Ns a mass T η.1 η.2 x]
  rw [integral_fun_snd (E := ℝ)
    (μ := Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1))
    (ν := Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1))
    (f := fun ηR : AsymCanonicalMode Nt Ns → ℝ =>
      asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR x)]
  simpa [asymCanonicalRoughFieldFunctionOfSnd] using
    asymCanonicalRoughFieldFunction_marginal_integral_zero Nt Ns a mass T x

private lemma asymCanonicalSumFieldFunction_integral_zero
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ)
    (x : AsymLatticeSites Nt Ns) :
    ∫ η : AsymCanonicalJoint Nt Ns,
      asymCanonicalSumFieldFunction Nt Ns a mass T η x
      ∂(asymCanonicalJointMeasure Nt Ns) = 0 := by
  change ∫ η : AsymCanonicalJoint Nt Ns,
      asymCanonicalSmoothFieldFunction Nt Ns a mass T η x +
        asymCanonicalRoughFieldFunction Nt Ns a mass T η x
      ∂(asymCanonicalJointMeasure Nt Ns) = 0
  have hs_int : Integrable
      (fun η : AsymCanonicalJoint Nt Ns =>
        asymCanonicalSmoothFieldFunction Nt Ns a mass T η x)
      (asymCanonicalJointMeasure Nt Ns) :=
    (asymCanonicalSmoothFieldFunction_memLp_two Nt Ns a mass T x).integrable one_le_two
  have hr_int : Integrable
      (fun η : AsymCanonicalJoint Nt Ns =>
        asymCanonicalRoughFieldFunction Nt Ns a mass T η x)
      (asymCanonicalJointMeasure Nt Ns) :=
    (asymCanonicalRoughFieldFunction_memLp_two Nt Ns a mass T x).integrable one_le_two
  rw [integral_add hs_int hr_int,
    asymCanonicalSmoothFieldFunction_integral_zero Nt Ns a mass T x,
    asymCanonicalRoughFieldFunction_integral_zero Nt Ns a mass T x]
  ring

private lemma asymCanonicalSumFieldFunction_pairing_memLp_two
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ)
    (f : AsymLatticeField Nt Ns) :
    MemLp
      (fun η : AsymCanonicalJoint Nt Ns =>
        ∑ x : AsymLatticeSites Nt Ns, f x * asymCanonicalSumFieldFunction Nt Ns a mass T η x)
      2 (asymCanonicalJointMeasure Nt Ns) := by
  refine memLp_finset_sum _ (fun x _ => ?_)
  refine MemLp.const_mul ?_ (f x)
  exact asymCanonicalSumFieldFunction_memLp_two Nt Ns a mass T x

private lemma asymCanonicalSumFieldFunction_pairing_integral_zero
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ)
    (f : AsymLatticeField Nt Ns) :
    ∫ η : AsymCanonicalJoint Nt Ns,
      ∑ x : AsymLatticeSites Nt Ns, f x * asymCanonicalSumFieldFunction Nt Ns a mass T η x
      ∂(asymCanonicalJointMeasure Nt Ns) = 0 := by
  rw [integral_finset_sum]
  · refine Finset.sum_eq_zero ?_
    intro x _
    rw [integral_const_mul, asymCanonicalSumFieldFunction_integral_zero Nt Ns a mass T x]
    ring
  · intro x _
    refine Integrable.const_mul ?_ (f x)
    exact (asymCanonicalSumFieldFunction_memLp_two Nt Ns a mass T x).integrable one_le_two

private lemma asymCanonicalSumFieldLaw_pairing_integral_zero
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass T : ℝ)
    (f : AsymLatticeField Nt Ns) :
    ∫ φ : AsymLatticeField Nt Ns, asymSitePairingCLM Nt Ns f φ
      ∂(asymCanonicalSumFieldLaw Nt Ns a mass T) = 0 := by
  rw [asymCanonicalSumFieldLaw_eq_map_asymCanonicalSumFieldFunction Nt Ns a mass T]
  rw [integral_map
    (asymCanonicalSumFieldFunction_measurable Nt Ns a mass T).aemeasurable]
  · change ∫ η : AsymCanonicalJoint Nt Ns,
        ∑ x : AsymLatticeSites Nt Ns, f x * asymCanonicalSumFieldFunction Nt Ns a mass T η x
        ∂(asymCanonicalJointMeasure Nt Ns) = 0
    exact asymCanonicalSumFieldFunction_pairing_integral_zero Nt Ns a mass T f
  · exact (asymSitePairingCLM Nt Ns f).measurable.aestronglyMeasurable

private lemma asymCanonicalSumFieldLaw_pairing_cross_moment_eq_covariance
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T) (f g : AsymLatticeField Nt Ns) :
    ∫ φ : AsymLatticeField Nt Ns,
      asymSitePairingCLM Nt Ns f φ * asymSitePairingCLM Nt Ns g φ
      ∂(asymCanonicalSumFieldLaw Nt Ns a mass T) =
    GaussianField.covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass) f g := by
  rw [asymCanonicalSumFieldLaw_eq_map_asymCanonicalSumFieldFunction Nt Ns a mass T]
  rw [integral_map
    (asymCanonicalSumFieldFunction_measurable Nt Ns a mass T).aemeasurable]
  · change ∫ η : AsymCanonicalJoint Nt Ns,
        (∑ x : AsymLatticeSites Nt Ns, f x * asymCanonicalSumFieldFunction Nt Ns a mass T η x) *
          (∑ y : AsymLatticeSites Nt Ns, g y * asymCanonicalSumFieldFunction Nt Ns a mass T η y)
        ∂(asymCanonicalJointMeasure Nt Ns) =
      GaussianField.covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass) f g
    let μ := asymCanonicalJointMeasure Nt Ns
    let X : AsymLatticeSites Nt Ns → AsymCanonicalJoint Nt Ns → ℝ :=
      fun x η => f x * asymCanonicalSumFieldFunction Nt Ns a mass T η x
    let Y : AsymLatticeSites Nt Ns → AsymCanonicalJoint Nt Ns → ℝ :=
      fun y η => g y * asymCanonicalSumFieldFunction Nt Ns a mass T η y
    have hX : ∀ x, MemLp (X x) 2 μ := by
      intro x
      dsimp [X, μ]
      exact MemLp.const_mul (asymCanonicalSumFieldFunction_memLp_two Nt Ns a mass T x) (f x)
    have hY : ∀ y, MemLp (Y y) 2 μ := by
      intro y
      dsimp [Y, μ]
      exact MemLp.const_mul (asymCanonicalSumFieldFunction_memLp_two Nt Ns a mass T y) (g y)
    have h_pair_f : MemLp (fun η : AsymCanonicalJoint Nt Ns => ∑ x, X x η) 2 μ := by
      simpa [X, μ] using asymCanonicalSumFieldFunction_pairing_memLp_two Nt Ns a mass T f
    have h_pair_g : MemLp (fun η : AsymCanonicalJoint Nt Ns => ∑ y, Y y η) 2 μ := by
      simpa [Y, μ] using asymCanonicalSumFieldFunction_pairing_memLp_two Nt Ns a mass T g
    have h_pair_f_zero : ∫ η, ∑ x, X x η ∂μ = 0 := by
      simpa [X, μ] using asymCanonicalSumFieldFunction_pairing_integral_zero Nt Ns a mass T f
    have h_pair_g_zero : ∫ η, ∑ y, Y y η ∂μ = 0 := by
      simpa [Y, μ] using asymCanonicalSumFieldFunction_pairing_integral_zero Nt Ns a mass T g
    have h_cov_pair :
        cov[(fun η : AsymCanonicalJoint Nt Ns => ∑ x, X x η),
          (fun η : AsymCanonicalJoint Nt Ns => ∑ y, Y y η); μ] =
        ∫ η : AsymCanonicalJoint Nt Ns, (∑ x, X x η) * (∑ y, Y y η) ∂μ := by
      rw [covariance_eq_sub h_pair_f h_pair_g, h_pair_f_zero, h_pair_g_zero]
      simp
    have h_cov_sum :
        cov[(fun η : AsymCanonicalJoint Nt Ns => ∑ x, X x η),
          (fun η : AsymCanonicalJoint Nt Ns => ∑ y, Y y η); μ] =
        ∑ x, ∑ y, cov[X x, Y y; μ] := by
      exact covariance_fun_sum_fun_sum hX hY
    rw [← h_cov_pair, h_cov_sum]
    rw [latticeCovarianceAsymGJ_eq_sum_delta_covariance Nt Ns a mass ha hmass f g]
    refine Finset.sum_congr rfl ?_
    intro x _
    refine Finset.sum_congr rfl ?_
    intro y _
    have hX_zero : ∫ η, X x η ∂μ = 0 := by
      simp only [X, μ]
      rw [integral_const_mul, asymCanonicalSumFieldFunction_integral_zero Nt Ns a mass T x]
      ring
    have hY_zero : ∫ η, Y y η ∂μ = 0 := by
      simp only [Y, μ]
      rw [integral_const_mul, asymCanonicalSumFieldFunction_integral_zero Nt Ns a mass T y]
      ring
    rw [covariance_eq_sub (hX x) (hY y), hX_zero, hY_zero]
    simp only [Pi.mul_apply, mul_zero, sub_zero]
    have hxy :
        (fun η : AsymCanonicalJoint Nt Ns => X x η * Y y η) =
        (fun η : AsymCanonicalJoint Nt Ns =>
          (f x * g y) *
            (asymCanonicalSumFieldFunction Nt Ns a mass T η x *
              asymCanonicalSumFieldFunction Nt Ns a mass T η y)) := by
      funext η
      simp [X, Y]
      ring
    rw [hxy, integral_const_mul]
    rw [asymCanonicalSumFieldFunction_covariance_eq_GJ Nt Ns a mass ha hmass T hT x y]
    by_cases hfx : f x = 0
    · simp [hfx]
    · by_cases hgy : g y = 0
      · simp [hgy]
      · have hxdelta : (fun z => if z = x then 1 else 0) = asymLatticeDelta Nt Ns x := by
          ext z
          simp [asymLatticeDelta]
        have hydelta : (fun z => if z = y then 1 else 0) = asymLatticeDelta Nt Ns y := by
          ext z
          simp [asymLatticeDelta]
        rw [hxdelta, hydelta]
  · exact ((asymSitePairingCLM Nt Ns f).measurable.aestronglyMeasurable).mul
      ((asymSitePairingCLM Nt Ns g).measurable.aestronglyMeasurable)

private theorem asymCanonicalSumFieldLaw_pairing_is_gaussian
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T) (f : AsymLatticeField Nt Ns) :
    (asymCanonicalSumFieldLaw Nt Ns a mass T).map
      (fun φ : AsymLatticeField Nt Ns => ∑ x : AsymLatticeSites Nt Ns, f x * φ x) =
      gaussianReal 0
        (@inner ℝ ell2' _
          (latticeCovarianceAsymGJ Nt Ns a mass ha hmass f)
          (latticeCovarianceAsymGJ Nt Ns a mass ha hmass f)).toNNReal := by
  have h_gauss :=
    (ProbabilityTheory.IsGaussian.map_eq_gaussianReal
      (μ := asymCanonicalSumFieldLaw Nt Ns a mass T)
      (L := asymSitePairingCLM Nt Ns f))
  change Measure.map (asymSitePairingCLM Nt Ns f) (asymCanonicalSumFieldLaw Nt Ns a mass T) =
    gaussianReal 0
      (@inner ℝ ell2' _
        (latticeCovarianceAsymGJ Nt Ns a mass ha hmass f)
        (latticeCovarianceAsymGJ Nt Ns a mass ha hmass f)).toNNReal
  rw [h_gauss]
  apply (ProbabilityTheory.gaussianReal_ext_iff).2
  constructor
  · exact asymCanonicalSumFieldLaw_pairing_integral_zero Nt Ns a mass T f
  · have h_var :
        Var[asymSitePairingCLM Nt Ns f; asymCanonicalSumFieldLaw Nt Ns a mass T] =
          ∫ φ : AsymLatticeField Nt Ns, (asymSitePairingCLM Nt Ns f φ) ^ 2
            ∂(asymCanonicalSumFieldLaw Nt Ns a mass T) := by
      refine variance_of_integral_eq_zero
        (asymSitePairingCLM Nt Ns f).measurable.aemeasurable ?_
      exact asymCanonicalSumFieldLaw_pairing_integral_zero Nt Ns a mass T f
    rw [h_var, show (fun φ : AsymLatticeField Nt Ns => (asymSitePairingCLM Nt Ns f φ) ^ 2) =
        (fun φ : AsymLatticeField Nt Ns =>
          asymSitePairingCLM Nt Ns f φ * asymSitePairingCLM Nt Ns f φ) by
            funext φ; ring]
    rw [asymCanonicalSumFieldLaw_pairing_cross_moment_eq_covariance
      Nt Ns a mass ha hmass T hT f f]
    rfl

noncomputable def asymLatticeGaussianFieldLaw (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Measure (AsymLatticeField Nt Ns) :=
  (latticeGaussianMeasureAsym Nt Ns a mass ha hmass).map (asymEvalMap Nt Ns)

private theorem asymLatticeGaussianFieldLaw_pairing_is_gaussian
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : AsymLatticeField Nt Ns) :
    (asymLatticeGaussianFieldLaw Nt Ns a mass ha hmass).map
      (fun φ : AsymLatticeField Nt Ns => ∑ x : AsymLatticeSites Nt Ns, f x * φ x) =
      gaussianReal 0
        (@inner ℝ ell2' _
          (latticeCovarianceAsymGJ Nt Ns a mass ha hmass f)
          (latticeCovarianceAsymGJ Nt Ns a mass ha hmass f)).toNNReal := by
  unfold asymLatticeGaussianFieldLaw
  change Measure.map (asymSitePairingCLM Nt Ns f)
      (Measure.map (asymEvalMap Nt Ns) (latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) =
    gaussianReal 0
      (@inner ℝ ell2' _
        (latticeCovarianceAsymGJ Nt Ns a mass ha hmass f)
        (latticeCovarianceAsymGJ Nt Ns a mass ha hmass f)).toNNReal
  rw [Measure.map_map
    (g := asymSitePairingCLM Nt Ns f)
    (f := asymEvalMap Nt Ns)
    (μ := latticeGaussianMeasureAsym Nt Ns a mass ha hmass)
    (asymSitePairingCLM Nt Ns f).measurable
    (asymEvalMap_measurable Nt Ns)]
  rw [show asymSitePairingCLM Nt Ns f ∘ asymEvalMap Nt Ns =
      fun ω : Configuration (AsymLatticeField Nt Ns) => ω f from by
        funext ω
        change ∑ x : AsymLatticeSites Nt Ns, f x * asymEvalMap Nt Ns ω x = ω f
        exact (asymConfig_apply_eq_sum_evalMap Nt Ns ω f).symm]
  exact GaussianField.pairing_is_gaussian (latticeCovarianceAsymGJ Nt Ns a mass ha hmass) f

theorem asymCanonicalSumFieldLaw_eq_asymLatticeGaussianFieldLaw
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T) :
    asymCanonicalSumFieldLaw Nt Ns a mass T =
      asymLatticeGaussianFieldLaw Nt Ns a mass ha hmass := by
  letI : IsProbabilityMeasure (asymCanonicalSumFieldLaw Nt Ns a mass T) := inferInstance
  letI : IsProbabilityMeasure (asymLatticeGaussianFieldLaw Nt Ns a mass ha hmass) := by
    unfold asymLatticeGaussianFieldLaw
    exact Measure.isProbabilityMeasure_map (asymEvalMap_measurable Nt Ns).aemeasurable
  apply GaussianField.cramerWold
  intro f
  exact (asymCanonicalSumFieldLaw_pairing_is_gaussian Nt Ns a mass ha hmass T hT f).trans
    (asymLatticeGaussianFieldLaw_pairing_is_gaussian Nt Ns a mass ha hmass f).symm

theorem asymCanonicalJointMeasure_map_sumConfig (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T) :
    (asymCanonicalJointMeasure Nt Ns).map (asymCanonicalSumConfig Nt Ns a mass T) =
      latticeGaussianMeasureAsym Nt Ns a mass ha hmass := by
  rw [show asymCanonicalSumConfig Nt Ns a mass T =
      fun η => asymEvalMapInv Nt Ns
        (asymCanonicalSumFieldFunction Nt Ns a mass T η) from by
          funext η
          rw [asymCanonicalSumConfig, asymLatticeFieldToConfig_eq_evalMapInv]]
  have h_map_map :
      Measure.map
          (fun η => asymEvalMapInv Nt Ns
            (asymCanonicalSumFieldFunction Nt Ns a mass T η))
          (asymCanonicalJointMeasure Nt Ns) =
        Measure.map
          (asymEvalMapInv Nt Ns)
          ((asymCanonicalJointMeasure Nt Ns).map
            (asymCanonicalSumFieldFunction Nt Ns a mass T)) := by
    simpa [Function.comp] using
      (Measure.map_map
        (g := asymEvalMapInv Nt Ns)
        (f := asymCanonicalSumFieldFunction Nt Ns a mass T)
        (μ := asymCanonicalJointMeasure Nt Ns)
        (asymEvalMapInv_measurable Nt Ns)
        (asymCanonicalSumFieldFunction_measurable Nt Ns a mass T)).symm
  rw [h_map_map]
  rw [← asymCanonicalSumFieldLaw_eq_map_asymCanonicalSumFieldFunction Nt Ns a mass T]
  rw [asymCanonicalSumFieldLaw_eq_asymLatticeGaussianFieldLaw Nt Ns a mass ha hmass T hT]
  rw [asymLatticeGaussianFieldLaw]
  rw [Measure.map_map
    (g := asymEvalMapInv Nt Ns)
    (f := asymEvalMap Nt Ns)
    (μ := latticeGaussianMeasureAsym Nt Ns a mass ha hmass)
    (asymEvalMapInv_measurable Nt Ns)
    (asymEvalMap_measurable Nt Ns)]
  rw [show asymEvalMapInv Nt Ns ∘ asymEvalMap Nt Ns = id from by
      funext ω
      exact asymEvalMapInv_evalMap Nt Ns ω]
  simp

end Variance

end Pphi2

end
