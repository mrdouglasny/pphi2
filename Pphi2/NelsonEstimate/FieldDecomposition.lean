import Pphi2.NelsonEstimate.LatticeBridge
import Pphi2.NelsonEstimate.LatticeSetup
import Pphi2.NelsonEstimate.CovarianceSplit
import Pphi2.NelsonEstimate.HeatKernelBound
import Lattice.HeatKernel
import Lattice.LatticeFourierProduct
import Lattice.LatticeFourierIndexing
import Lattice.Symmetry
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import GaussianField.CramerWold
import GaussianField.Hypercontractive
import GaussianField.WickMultivariate
import GaussianHilbert.HermitePolynomials

noncomputable section

namespace Pphi2

open MeasureTheory GaussianField
open scoped BigOperators

variable (d N : ℕ) [NeZero N] (a mass : ℝ)

/-- Abstract field-decomposition data at cutoff scale `T`. -/
structure FieldDecomposition (T : ℝ) where
  Joint : Type
  jointMeasurable : MeasurableSpace Joint
  μ_joint : @Measure Joint jointMeasurable
  jointProbability : @IsProbabilityMeasure Joint jointMeasurable μ_joint
  φ_S : Joint → Configuration (FinLatticeField d N)
  φ_R : Joint → Configuration (FinLatticeField d N)
  φ_S_measurable :
    @Measurable Joint (Configuration (FinLatticeField d N)) jointMeasurable
      instMeasurableSpaceConfiguration φ_S
  φ_R_measurable :
    @Measurable Joint (Configuration (FinLatticeField d N)) jointMeasurable
      instMeasurableSpaceConfiguration φ_R
  pushforward_eq_GFF :
    ∀ (ha : 0 < a) (hmass : 0 < mass),
      @Measure.map Joint (Configuration (FinLatticeField d N))
          jointMeasurable instMeasurableSpaceConfiguration
          (fun ξ => φ_S ξ + φ_R ξ) μ_joint =
        latticeGaussianMeasure d N a mass ha hmass

section Canonical

abbrev CanonicalJoint (d N : ℕ) [NeZero N] : Type :=
  ((Fin d → Fin N) → ℝ) × ((Fin d → Fin N) → ℝ)

noncomputable def canonicalJointMeasure (d N : ℕ) [NeZero N] :
    Measure (CanonicalJoint d N) :=
  Measure.prod
    (Measure.pi (fun _ : Fin d → Fin N => ProbabilityTheory.gaussianReal 0 1))
    (Measure.pi (fun _ : Fin d → Fin N => ProbabilityTheory.gaussianReal 0 1))

instance canonicalJointMeasure_isProbability (d N : ℕ) [NeZero N] :
    IsProbabilityMeasure (canonicalJointMeasure d N) := by
  unfold canonicalJointMeasure
  infer_instance

abbrev CanonicalJointSumIndex (d N : ℕ) [NeZero N] :=
  (Fin d → Fin N) ⊕ (Fin d → Fin N)

noncomputable def canonicalJointStdGaussianMeasurableEquiv
    (d N : ℕ) [NeZero N] :
    CanonicalJoint d N ≃ᵐ
      (Fin (Fintype.card (CanonicalJointSumIndex d N)) → ℝ) :=
  ((MeasurableEquiv.sumPiEquivProdPi
      (fun _ : CanonicalJointSumIndex d N => ℝ)).symm).trans
    (MeasurableEquiv.piCongrLeft
      (fun _ : Fin (Fintype.card (CanonicalJointSumIndex d N)) => ℝ)
      (Fintype.equivFin (CanonicalJointSumIndex d N)))

theorem canonicalJointMeasure_map_sum_pi_gaussian
    (d N : ℕ) [NeZero N] :
    (canonicalJointMeasure d N).map
        ((MeasurableEquiv.sumPiEquivProdPi
          (fun _ : CanonicalJointSumIndex d N => ℝ)).symm) =
      Measure.pi
        (fun _ : CanonicalJointSumIndex d N =>
          ProbabilityTheory.gaussianReal 0 1) := by
  simpa [canonicalJointMeasure, CanonicalJointSumIndex]
    using
      (measurePreserving_sumPiEquivProdPi_symm
        (fun _ : CanonicalJointSumIndex d N =>
          (ProbabilityTheory.gaussianReal 0 1 : Measure ℝ))).map_eq

theorem canonicalJointMeasure_map_stdGaussian
    (d N : ℕ) [NeZero N] :
    (canonicalJointMeasure d N).map
        (canonicalJointStdGaussianMeasurableEquiv d N) =
      GaussianHilbert.stdGaussianFin
        (Fintype.card (CanonicalJointSumIndex d N)) := by
  unfold canonicalJointStdGaussianMeasurableEquiv
  simp only [MeasurableEquiv.coe_trans]
  have h_map_map :
      Measure.map
          (⇑(MeasurableEquiv.piCongrLeft
            (fun _ : Fin (Fintype.card (CanonicalJointSumIndex d N)) => ℝ)
            (Fintype.equivFin (CanonicalJointSumIndex d N))) ∘
            ⇑(MeasurableEquiv.sumPiEquivProdPi
              (fun _ : CanonicalJointSumIndex d N => ℝ)).symm)
          (canonicalJointMeasure d N) =
        Measure.map
          (MeasurableEquiv.piCongrLeft
            (fun _ : Fin (Fintype.card (CanonicalJointSumIndex d N)) => ℝ)
            (Fintype.equivFin (CanonicalJointSumIndex d N)))
          ((canonicalJointMeasure d N).map
            ((MeasurableEquiv.sumPiEquivProdPi
              (fun _ : CanonicalJointSumIndex d N => ℝ)).symm)) := by
    simpa using
      (Measure.map_map
        (g := MeasurableEquiv.piCongrLeft
          (fun _ : Fin (Fintype.card (CanonicalJointSumIndex d N)) => ℝ)
          (Fintype.equivFin (CanonicalJointSumIndex d N)))
        (f := (MeasurableEquiv.sumPiEquivProdPi
          (fun _ : CanonicalJointSumIndex d N => ℝ)).symm)
        (μ := canonicalJointMeasure d N)
        (MeasurableEquiv.piCongrLeft
          (fun _ : Fin (Fintype.card (CanonicalJointSumIndex d N)) => ℝ)
          (Fintype.equivFin (CanonicalJointSumIndex d N))).measurable
        ((MeasurableEquiv.sumPiEquivProdPi
          (fun _ : CanonicalJointSumIndex d N => ℝ)).symm.measurable)).symm
  rw [h_map_map, canonicalJointMeasure_map_sum_pi_gaussian]
  simpa [GaussianHilbert.stdGaussianFin, CanonicalJointSumIndex]
    using
      (measurePreserving_piCongrLeft
        (μ := fun _ : Fin (Fintype.card (CanonicalJointSumIndex d N)) =>
          (ProbabilityTheory.gaussianReal 0 1 : Measure ℝ))
        (α := fun _ : Fin (Fintype.card (CanonicalJointSumIndex d N)) => ℝ)
        (f := Fintype.equivFin (CanonicalJointSumIndex d N))).map_eq

theorem canonicalJointMeasure_map_stdGaussianEuclidean
    (d N : ℕ) [NeZero N] :
    (canonicalJointMeasure d N).map
        (fun η =>
          WithLp.toLp 2
            (((MeasurableEquiv.sumPiEquivProdPi
              (fun _ : CanonicalJointSumIndex d N => ℝ)).symm) η)) =
      ProbabilityTheory.stdGaussian
        (EuclideanSpace ℝ (CanonicalJointSumIndex d N)) := by
  have h_map_map :
      Measure.map
          (fun η =>
            WithLp.toLp 2
              (((MeasurableEquiv.sumPiEquivProdPi
                (fun _ : CanonicalJointSumIndex d N => ℝ)).symm) η))
          (canonicalJointMeasure d N) =
        Measure.map
          (WithLp.toLp 2)
          ((canonicalJointMeasure d N).map
            ((MeasurableEquiv.sumPiEquivProdPi
              (fun _ : CanonicalJointSumIndex d N => ℝ)).symm)) := by
    simpa [Function.comp] using
      (Measure.map_map
        (g := WithLp.toLp 2)
        (f := (MeasurableEquiv.sumPiEquivProdPi
          (fun _ : CanonicalJointSumIndex d N => ℝ)).symm)
        (μ := canonicalJointMeasure d N)
        (by fun_prop)
        ((MeasurableEquiv.sumPiEquivProdPi
          (fun _ : CanonicalJointSumIndex d N => ℝ)).symm.measurable)).symm
  rw [h_map_map, canonicalJointMeasure_map_sum_pi_gaussian]
  simpa using
    (ProbabilityTheory.map_pi_eq_stdGaussian
      (ι := CanonicalJointSumIndex d N))

def canonicalEigenvalue (d N : ℕ) [NeZero N]
    (a mass : ℝ) (m : Fin d → Fin N) : ℝ :=
  (∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2

def canonicalSmoothWeight (d N : ℕ) [NeZero N]
    (a mass T : ℝ) (m : Fin d → Fin N) : ℝ :=
  Real.exp (-T * canonicalEigenvalue d N a mass m) /
    canonicalEigenvalue d N a mass m

def canonicalRoughWeight (d N : ℕ) [NeZero N]
    (a mass T : ℝ) (m : Fin d → Fin N) : ℝ :=
  (1 - Real.exp (-T * canonicalEigenvalue d N a mass m)) /
    canonicalEigenvalue d N a mass m

private def canonicalSmoothModeCoeff (d N : ℕ) [NeZero N]
    (a mass T : ℝ) (x : FinLatticeSites d N) (m : Fin d → Fin N) : ℝ :=
  Real.sqrt
      (canonicalSmoothWeight d N a mass T m /
        latticeFourierProductNormSq N d m) *
    latticeFourierProductBasisFun N d m x

private def canonicalRoughModeCoeff (d N : ℕ) [NeZero N]
    (a mass T : ℝ) (x : FinLatticeSites d N) (m : Fin d → Fin N) : ℝ :=
  Real.sqrt
      (canonicalRoughWeight d N a mass T m /
        latticeFourierProductNormSq N d m) *
    latticeFourierProductBasisFun N d m x

noncomputable def canonicalSmoothFieldFunction (d N : ℕ) [NeZero N]
    (a mass T : ℝ) (η : CanonicalJoint d N) :
    FinLatticeSites d N → ℝ :=
  fun x =>
    (Real.sqrt (a^d))⁻¹ *
      ∑ m : Fin d → Fin N, canonicalSmoothModeCoeff d N a mass T x m * η.1 m

noncomputable def canonicalSmoothFieldFunctionOfFst (d N : ℕ) [NeZero N]
    (a mass T : ℝ) (η_S : (Fin d → Fin N) → ℝ) :
    FinLatticeSites d N → ℝ :=
  fun x =>
    (Real.sqrt (a^d))⁻¹ *
      ∑ m : Fin d → Fin N, canonicalSmoothModeCoeff d N a mass T x m * η_S m

noncomputable def canonicalRoughFieldFunction (d N : ℕ) [NeZero N]
    (a mass T : ℝ) (η : CanonicalJoint d N) :
    FinLatticeSites d N → ℝ :=
  fun x =>
    (Real.sqrt (a^d))⁻¹ *
      ∑ m : Fin d → Fin N, canonicalRoughModeCoeff d N a mass T x m * η.2 m

noncomputable def canonicalRoughFieldFunctionOfSnd (d N : ℕ) [NeZero N]
    (a mass T : ℝ) (η_R : (Fin d → Fin N) → ℝ) :
    FinLatticeSites d N → ℝ :=
  fun x =>
    (Real.sqrt (a^d))⁻¹ *
      ∑ m : Fin d → Fin N, canonicalRoughModeCoeff d N a mass T x m * η_R m

noncomputable def canonicalSumFieldFunction (d N : ℕ) [NeZero N]
    (a mass T : ℝ) (η : CanonicalJoint d N) :
    FinLatticeSites d N → ℝ :=
  fun x =>
    canonicalSmoothFieldFunction d N a mass T η x +
      canonicalRoughFieldFunction d N a mass T η x

theorem canonicalSumFieldFunction_eq_smooth_plus_rough
    (d N : ℕ) [NeZero N] (a mass T : ℝ) (η : CanonicalJoint d N)
    (x : FinLatticeSites d N) :
    canonicalSumFieldFunction d N a mass T η x =
      canonicalSmoothFieldFunction d N a mass T η x +
        canonicalRoughFieldFunction d N a mass T η x :=
  rfl

@[simp] theorem canonicalSmoothFieldFunction_eq_of_fst
    (d N : ℕ) [NeZero N] (a mass T : ℝ)
    (η_S : (Fin d → Fin N) → ℝ) (η_R : (Fin d → Fin N) → ℝ)
    (x : FinLatticeSites d N) :
    canonicalSmoothFieldFunction d N a mass T (η_S, η_R) x =
      canonicalSmoothFieldFunctionOfFst d N a mass T η_S x :=
  rfl

@[simp] theorem canonicalRoughFieldFunction_eq_of_snd
    (d N : ℕ) [NeZero N] (a mass T : ℝ)
    (η_S : (Fin d → Fin N) → ℝ) (η_R : (Fin d → Fin N) → ℝ)
    (x : FinLatticeSites d N) :
    canonicalRoughFieldFunction d N a mass T (η_S, η_R) x =
      canonicalRoughFieldFunctionOfSnd d N a mass T η_R x :=
  rfl

def latticeFieldToConfig (d N : ℕ) [NeZero N] (φ : FinLatticeField d N) :
    Configuration (FinLatticeField d N) :=
  { toFun := fun f => ∑ x : FinLatticeSites d N, f x * φ x
    map_add' := fun f g => by
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    map_smul' := fun r f => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
        Finset.mul_sum, mul_assoc]
    cont := continuous_finset_sum _ (fun i _ =>
      (continuous_apply i).mul continuous_const) }

@[simp] theorem latticeFieldToConfig_apply
    (d N : ℕ) [NeZero N] (φ : FinLatticeField d N)
    (f : FinLatticeField d N) :
    (latticeFieldToConfig d N φ) f =
      ∑ x : FinLatticeSites d N, f x * φ x := rfl

theorem latticeFieldToConfig_eq_evalMapInv
    (d N : ℕ) [NeZero N] (φ : FinLatticeField d N) :
    latticeFieldToConfig d N φ = GaussianField.evalMapInv d N φ := by
  apply ContinuousLinearMap.ext
  intro f
  simpa [latticeFieldToConfig] using
    (GaussianField.evalMapInv_apply (d := d) (N := N) φ f).symm

noncomputable def canonicalSmoothConfig (d N : ℕ) [NeZero N]
    (a mass T : ℝ) (η : CanonicalJoint d N) :
    Configuration (FinLatticeField d N) :=
  latticeFieldToConfig d N (canonicalSmoothFieldFunction d N a mass T η)

noncomputable def canonicalRoughConfig (d N : ℕ) [NeZero N]
    (a mass T : ℝ) (η : CanonicalJoint d N) :
    Configuration (FinLatticeField d N) :=
  latticeFieldToConfig d N (canonicalRoughFieldFunction d N a mass T η)

theorem canonicalSmoothFieldFunction_add
    (d N : ℕ) [NeZero N] (a mass T : ℝ)
    (η₁ η₂ : CanonicalJoint d N) (x : FinLatticeSites d N) :
    canonicalSmoothFieldFunction d N a mass T (η₁ + η₂) x =
      canonicalSmoothFieldFunction d N a mass T η₁ x +
        canonicalSmoothFieldFunction d N a mass T η₂ x := by
  unfold canonicalSmoothFieldFunction
  rw [show (η₁ + η₂).1 = η₁.1 + η₂.1 by rfl]
  simp_rw [Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib, mul_add]

theorem canonicalSmoothFieldFunction_smul
    (d N : ℕ) [NeZero N] (a mass T c : ℝ)
    (η : CanonicalJoint d N) (x : FinLatticeSites d N) :
    canonicalSmoothFieldFunction d N a mass T (c • η) x =
      c * canonicalSmoothFieldFunction d N a mass T η x := by
  unfold canonicalSmoothFieldFunction
  rw [show (c • η).1 = c • η.1 by rfl]
  simp_rw [Pi.smul_apply, smul_eq_mul]
  rw [show c * ((Real.sqrt (a^d))⁻¹ *
      ∑ m : Fin d → Fin N, canonicalSmoothModeCoeff d N a mass T x m * η.1 m) =
      (Real.sqrt (a^d))⁻¹ *
        (c * ∑ m : Fin d → Fin N, canonicalSmoothModeCoeff d N a mass T x m * η.1 m) by ring]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro m _
  ring

theorem canonicalRoughFieldFunction_add
    (d N : ℕ) [NeZero N] (a mass T : ℝ)
    (η₁ η₂ : CanonicalJoint d N) (x : FinLatticeSites d N) :
    canonicalRoughFieldFunction d N a mass T (η₁ + η₂) x =
      canonicalRoughFieldFunction d N a mass T η₁ x +
        canonicalRoughFieldFunction d N a mass T η₂ x := by
  unfold canonicalRoughFieldFunction
  rw [show (η₁ + η₂).2 = η₁.2 + η₂.2 by rfl]
  simp_rw [Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib, mul_add]

theorem canonicalRoughFieldFunction_smul
    (d N : ℕ) [NeZero N] (a mass T c : ℝ)
    (η : CanonicalJoint d N) (x : FinLatticeSites d N) :
    canonicalRoughFieldFunction d N a mass T (c • η) x =
      c * canonicalRoughFieldFunction d N a mass T η x := by
  unfold canonicalRoughFieldFunction
  rw [show (c • η).2 = c • η.2 by rfl]
  simp_rw [Pi.smul_apply, smul_eq_mul]
  rw [show c * ((Real.sqrt (a^d))⁻¹ *
      ∑ m : Fin d → Fin N, canonicalRoughModeCoeff d N a mass T x m * η.2 m) =
      (Real.sqrt (a^d))⁻¹ *
        (c * ∑ m : Fin d → Fin N, canonicalRoughModeCoeff d N a mass T x m * η.2 m) by ring]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro m _
  ring

theorem canonicalSumFieldFunction_add
    (d N : ℕ) [NeZero N] (a mass T : ℝ)
    (η₁ η₂ : CanonicalJoint d N) (x : FinLatticeSites d N) :
    canonicalSumFieldFunction d N a mass T (η₁ + η₂) x =
      canonicalSumFieldFunction d N a mass T η₁ x +
        canonicalSumFieldFunction d N a mass T η₂ x := by
  rw [canonicalSumFieldFunction_eq_smooth_plus_rough,
    canonicalSumFieldFunction_eq_smooth_plus_rough,
    canonicalSumFieldFunction_eq_smooth_plus_rough,
    canonicalSmoothFieldFunction_add, canonicalRoughFieldFunction_add]
  ring

theorem canonicalSumFieldFunction_smul
    (d N : ℕ) [NeZero N] (a mass T c : ℝ)
    (η : CanonicalJoint d N) (x : FinLatticeSites d N) :
    canonicalSumFieldFunction d N a mass T (c • η) x =
      c * canonicalSumFieldFunction d N a mass T η x := by
  rw [canonicalSumFieldFunction_eq_smooth_plus_rough,
    canonicalSumFieldFunction_eq_smooth_plus_rough,
    canonicalSmoothFieldFunction_smul, canonicalRoughFieldFunction_smul]
  ring

theorem canonicalSmoothFieldFunction_pointwise_measurable
    (d N : ℕ) [NeZero N] (a mass T : ℝ) (x : FinLatticeSites d N) :
    Measurable (fun η : CanonicalJoint d N =>
      canonicalSmoothFieldFunction d N a mass T η x) := by
  unfold canonicalSmoothFieldFunction
  fun_prop

theorem canonicalRoughFieldFunction_pointwise_measurable
    (d N : ℕ) [NeZero N] (a mass T : ℝ) (x : FinLatticeSites d N) :
    Measurable (fun η : CanonicalJoint d N =>
      canonicalRoughFieldFunction d N a mass T η x) := by
  unfold canonicalRoughFieldFunction
  fun_prop

theorem canonicalSumFieldFunction_pointwise_measurable
    (d N : ℕ) [NeZero N] (a mass T : ℝ) (x : FinLatticeSites d N) :
    Measurable (fun η : CanonicalJoint d N =>
      canonicalSumFieldFunction d N a mass T η x) := by
  unfold canonicalSumFieldFunction
  exact (canonicalSmoothFieldFunction_pointwise_measurable d N a mass T x).add
    (canonicalRoughFieldFunction_pointwise_measurable d N a mass T x)

theorem canonicalSmoothFieldFunction_measurable
    (d N : ℕ) [NeZero N] (a mass T : ℝ) :
    Measurable (fun η : CanonicalJoint d N =>
      canonicalSmoothFieldFunction d N a mass T η) := by
  apply measurable_pi_iff.mpr
  intro x
  exact canonicalSmoothFieldFunction_pointwise_measurable d N a mass T x

theorem canonicalRoughFieldFunction_measurable
    (d N : ℕ) [NeZero N] (a mass T : ℝ) :
    Measurable (fun η : CanonicalJoint d N =>
      canonicalRoughFieldFunction d N a mass T η) := by
  apply measurable_pi_iff.mpr
  intro x
  exact canonicalRoughFieldFunction_pointwise_measurable d N a mass T x

theorem canonicalSumFieldFunction_measurable
    (d N : ℕ) [NeZero N] (a mass T : ℝ) :
    Measurable (fun η : CanonicalJoint d N =>
      canonicalSumFieldFunction d N a mass T η) := by
  apply measurable_pi_iff.mpr
  intro x
  exact canonicalSumFieldFunction_pointwise_measurable d N a mass T x

noncomputable def canonicalSumConfig (d N : ℕ) [NeZero N]
    (a mass T : ℝ) (η : CanonicalJoint d N) :
    Configuration (FinLatticeField d N) :=
  latticeFieldToConfig d N (canonicalSumFieldFunction d N a mass T η)

@[simp] theorem canonicalSumConfig_apply_delta
    (d N : ℕ) [NeZero N] (a mass T : ℝ)
    (η : CanonicalJoint d N) (x : FinLatticeSites d N) :
    canonicalSumConfig d N a mass T η (finLatticeDelta d N x) =
      canonicalSumFieldFunction d N a mass T η x := by
  rw [canonicalSumConfig, latticeFieldToConfig_apply]
  simp [finLatticeDelta]

theorem canonicalSumConfig_measurable
    (d N : ℕ) [NeZero N] (a mass T : ℝ) :
    Measurable (canonicalSumConfig d N a mass T) := by
  rw [show canonicalSumConfig d N a mass T =
      fun η => GaussianField.evalMapInv d N
        (canonicalSumFieldFunction d N a mass T η) from by
          funext η
          rw [canonicalSumConfig, latticeFieldToConfig_eq_evalMapInv]]
  exact (GaussianField.evalMapInv_measurable (d := d) (N := N)).comp
    (canonicalSumFieldFunction_measurable (d := d) (N := N) (a := a) (mass := mass) T)

noncomputable def canonicalStdFieldFunction
    (d N : ℕ) [NeZero N] (a mass T : ℝ)
    (ξ : EuclideanSpace ℝ (CanonicalJointSumIndex d N)) :
    FinLatticeSites d N → ℝ :=
  fun x =>
    (Real.sqrt (a^d))⁻¹ *
      ∑ m : Fin d → Fin N, canonicalSmoothModeCoeff d N a mass T x m * ξ (Sum.inl m) +
    (Real.sqrt (a^d))⁻¹ *
      ∑ m : Fin d → Fin N, canonicalRoughModeCoeff d N a mass T x m * ξ (Sum.inr m)

noncomputable def canonicalStdToFieldLinearMap
    (d N : ℕ) [NeZero N] (a mass T : ℝ) :
    EuclideanSpace ℝ (CanonicalJointSumIndex d N) →ₗ[ℝ] FinLatticeField d N where
  toFun := canonicalStdFieldFunction d N a mass T
  map_add' := by
    intro ξ ζ
    funext x
    change
      (Real.sqrt (a ^ d))⁻¹ *
          ∑ m : Fin d → Fin N,
            canonicalSmoothModeCoeff d N a mass T x m *
              (ξ.ofLp (Sum.inl m) + ζ.ofLp (Sum.inl m)) +
        (Real.sqrt (a ^ d))⁻¹ *
          ∑ m : Fin d → Fin N,
            canonicalRoughModeCoeff d N a mass T x m *
              (ξ.ofLp (Sum.inr m) + ζ.ofLp (Sum.inr m)) =
      ((Real.sqrt (a ^ d))⁻¹ *
          ∑ m : Fin d → Fin N,
            canonicalSmoothModeCoeff d N a mass T x m * ξ.ofLp (Sum.inl m) +
        (Real.sqrt (a ^ d))⁻¹ *
          ∑ m : Fin d → Fin N,
            canonicalRoughModeCoeff d N a mass T x m * ξ.ofLp (Sum.inr m)) +
        ((Real.sqrt (a ^ d))⁻¹ *
          ∑ m : Fin d → Fin N,
            canonicalSmoothModeCoeff d N a mass T x m * ζ.ofLp (Sum.inl m) +
          (Real.sqrt (a ^ d))⁻¹ *
            ∑ m : Fin d → Fin N,
              canonicalRoughModeCoeff d N a mass T x m * ζ.ofLp (Sum.inr m))
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    ring_nf
  map_smul' := by
    intro c ξ
    funext x
    change
      (Real.sqrt (a ^ d))⁻¹ *
          ∑ m : Fin d → Fin N,
            canonicalSmoothModeCoeff d N a mass T x m * (c * ξ.ofLp (Sum.inl m)) +
        (Real.sqrt (a ^ d))⁻¹ *
          ∑ m : Fin d → Fin N,
            canonicalRoughModeCoeff d N a mass T x m * (c * ξ.ofLp (Sum.inr m)) =
      (RingHom.id ℝ) c *
        ((Real.sqrt (a ^ d))⁻¹ *
            ∑ m : Fin d → Fin N,
              canonicalSmoothModeCoeff d N a mass T x m * ξ.ofLp (Sum.inl m) +
          (Real.sqrt (a ^ d))⁻¹ *
            ∑ m : Fin d → Fin N,
              canonicalRoughModeCoeff d N a mass T x m * ξ.ofLp (Sum.inr m))
    simp only [RingHom.id_apply]
    rw [mul_add]
    have hSmooth :
        (∑ m : Fin d → Fin N,
            canonicalSmoothModeCoeff d N a mass T x m * (c * ξ.ofLp (Sum.inl m))) =
          c * ∑ m : Fin d → Fin N,
            canonicalSmoothModeCoeff d N a mass T x m * ξ.ofLp (Sum.inl m) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro m hm
      ring
    have hRough :
        (∑ m : Fin d → Fin N,
            canonicalRoughModeCoeff d N a mass T x m * (c * ξ.ofLp (Sum.inr m))) =
          c * ∑ m : Fin d → Fin N,
            canonicalRoughModeCoeff d N a mass T x m * ξ.ofLp (Sum.inr m) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro m hm
      ring
    rw [hSmooth, hRough]
    ring

noncomputable def canonicalStdToFieldCLM
    (d N : ℕ) [NeZero N] (a mass T : ℝ) :
    EuclideanSpace ℝ (CanonicalJointSumIndex d N) →L[ℝ] FinLatticeField d N :=
  { toLinearMap := canonicalStdToFieldLinearMap d N a mass T
    cont := (canonicalStdToFieldLinearMap d N a mass T).continuous_of_finiteDimensional }

/-- The canonical field law obtained by pushing the Euclidean standard Gaussian
through the smooth+rough linear field map. -/
noncomputable def canonicalSumFieldLaw
    (d N : ℕ) [NeZero N] (a mass T : ℝ) : Measure (FinLatticeField d N) :=
  (ProbabilityTheory.stdGaussian
      (EuclideanSpace ℝ (CanonicalJointSumIndex d N))).map
    (canonicalStdToFieldCLM d N a mass T)

instance canonicalSumFieldLaw_isGaussian
    (d N : ℕ) [NeZero N] (a mass T : ℝ) :
    ProbabilityTheory.IsGaussian (canonicalSumFieldLaw d N a mass T) := by
  unfold canonicalSumFieldLaw
  infer_instance

noncomputable def sitePairingCLM
    (d N : ℕ) [NeZero N] (f : FinLatticeField d N) :
    FinLatticeField d N →L[ℝ] ℝ :=
  { toLinearMap :=
      { toFun := fun φ => ∑ x : FinLatticeSites d N, f x * φ x
        map_add' := by
          intro φ ψ
          simp [mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro c φ
          simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] }
    cont := (continuous_finset_sum _ fun x _ =>
      continuous_const.mul (continuous_apply x)) }

theorem canonicalStdFieldFunction_eq_canonicalSumFieldFunction
    (d N : ℕ) [NeZero N] (a mass T : ℝ) (η : CanonicalJoint d N) :
    canonicalStdFieldFunction d N a mass T
        (WithLp.toLp 2
          (((MeasurableEquiv.sumPiEquivProdPi
            (fun _ : CanonicalJointSumIndex d N => ℝ)).symm) η)) =
      canonicalSumFieldFunction d N a mass T η := by
  funext x
  unfold canonicalStdFieldFunction canonicalSumFieldFunction
    canonicalSmoothFieldFunction canonicalRoughFieldFunction
  rfl

theorem canonicalSumFieldLaw_eq_map_canonicalSumFieldFunction
    (d N : ℕ) [NeZero N] (a mass T : ℝ) :
    canonicalSumFieldLaw d N a mass T =
      (canonicalJointMeasure d N).map
        (canonicalSumFieldFunction d N a mass T) := by
  unfold canonicalSumFieldLaw
  rw [← canonicalJointMeasure_map_stdGaussianEuclidean (d := d) (N := N)]
  have h_map_map :
      Measure.map (canonicalStdToFieldCLM d N a mass T)
          ((canonicalJointMeasure d N).map
            (fun η =>
              WithLp.toLp 2
                (((MeasurableEquiv.sumPiEquivProdPi
                  (fun _ : CanonicalJointSumIndex d N => ℝ)).symm) η))) =
        Measure.map
          (fun η =>
            canonicalStdToFieldCLM d N a mass T
              (WithLp.toLp 2
                (((MeasurableEquiv.sumPiEquivProdPi
                  (fun _ : CanonicalJointSumIndex d N => ℝ)).symm) η)))
          (canonicalJointMeasure d N) := by
    simpa [Function.comp] using
      (Measure.map_map
        (canonicalStdToFieldCLM d N a mass T).measurable
        (by fun_prop : Measurable
          (fun η =>
            WithLp.toLp 2
              (((MeasurableEquiv.sumPiEquivProdPi
                (fun _ : CanonicalJointSumIndex d N => ℝ)).symm) η))))
  rw [h_map_map]
  rw [show
      (fun η =>
        canonicalStdToFieldCLM d N a mass T
          (WithLp.toLp 2
            (((MeasurableEquiv.sumPiEquivProdPi
              (fun _ : CanonicalJointSumIndex d N => ℝ)).symm) η))) =
        canonicalSumFieldFunction d N a mass T from by
          funext η
          exact canonicalStdFieldFunction_eq_canonicalSumFieldFunction d N a mass T η]

theorem canonicalSmoothConfig_add_canonicalRoughConfig_eq_lift_sum
    (d N : ℕ) [NeZero N] (a mass T : ℝ) (η : CanonicalJoint d N) :
    canonicalSmoothConfig d N a mass T η + canonicalRoughConfig d N a mass T η =
      latticeFieldToConfig d N (canonicalSumFieldFunction d N a mass T η) := by
  apply ContinuousLinearMap.ext
  intro f
  show ∑ x : FinLatticeSites d N, f x * canonicalSmoothFieldFunction d N a mass T η x +
      ∑ x : FinLatticeSites d N, f x * canonicalRoughFieldFunction d N a mass T η x =
    ∑ x : FinLatticeSites d N, f x * canonicalSumFieldFunction d N a mass T η x
  simp [canonicalSmoothConfig, canonicalRoughConfig, latticeFieldToConfig,
    canonicalSumFieldFunction, mul_add, Finset.sum_add_distrib]

section Variance

open ProbabilityTheory MeasureTheory

variable (d N : ℕ) [NeZero N] (a mass : ℝ)

private lemma pi_gaussian_eval_integral_zero {I : Type*} [Fintype I] (k : I) :
    ∫ η : I → ℝ, η k
      ∂(Measure.pi (fun _ : I => gaussianReal 0 1)) = 0 := by
  rw [integral_eval]
  exact integral_id_gaussianReal

private lemma pi_gaussian_eval_integral_sq {I : Type*} [Fintype I] (k : I) :
    ∫ η : I → ℝ, (η k) ^ 2
      ∂(Measure.pi (fun _ : I => gaussianReal 0 1)) = 1 := by
  have h_meas_sq : Measurable (fun x : ℝ => x ^ 2) := by fun_prop
  have h_eq :
      ∫ η : I → ℝ, (η k) ^ 2
        ∂(Measure.pi (fun _ : I => gaussianReal 0 1)) =
      ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) := by
    have := integral_comp_eval (μ := fun _ : I => gaussianReal 0 1)
      (i := k) (f := fun x : ℝ => x ^ 2) h_meas_sq.aestronglyMeasurable
    convert this using 1
  rw [h_eq, integral_sq_gaussianReal 1]
  norm_num

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

theorem pi_gaussian_bilinear_moment {I : Type*} [Fintype I]
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

private lemma canonicalSmoothFieldFunction_marginal_integrable
    (T : ℝ) (x : FinLatticeSites d N) :
    Integrable (fun η_S : (Fin d → Fin N) → ℝ =>
      (Real.sqrt (a^d))⁻¹ *
        ∑ m : Fin d → Fin N, canonicalSmoothModeCoeff d N a mass T x m * η_S m)
      (Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)) := by
  have h_sum : Integrable (fun η_S : (Fin d → Fin N) → ℝ =>
      ∑ m : Fin d → Fin N, canonicalSmoothModeCoeff d N a mass T x m * η_S m)
      (Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)) := by
    refine integrable_finset_sum _ (fun m _ => ?_)
    have h_eval : Integrable (fun η_S : (Fin d → Fin N) → ℝ => η_S m)
        (Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)) := by
      exact integrable_eval IsGaussian.integrable_id
    convert h_eval.const_mul (canonicalSmoothModeCoeff d N a mass T x m)
  exact h_sum.const_mul _

private lemma canonicalRoughFieldFunction_marginal_integrable
    (T : ℝ) (x : FinLatticeSites d N) :
    Integrable (fun η_R : (Fin d → Fin N) → ℝ =>
      (Real.sqrt (a^d))⁻¹ *
        ∑ m : Fin d → Fin N, canonicalRoughModeCoeff d N a mass T x m * η_R m)
      (Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)) := by
  have h_sum : Integrable (fun η_R : (Fin d → Fin N) → ℝ =>
      ∑ m : Fin d → Fin N, canonicalRoughModeCoeff d N a mass T x m * η_R m)
      (Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)) := by
    refine integrable_finset_sum _ (fun m _ => ?_)
    have h_eval : Integrable (fun η_R : (Fin d → Fin N) → ℝ => η_R m)
        (Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)) := by
      exact integrable_eval IsGaussian.integrable_id
    convert h_eval.const_mul (canonicalRoughModeCoeff d N a mass T x m)
  exact h_sum.const_mul _

private lemma canonicalSmoothFieldFunction_marginal_integral_zero
    (T : ℝ) (x : FinLatticeSites d N) :
    ∫ η_S : (Fin d → Fin N) → ℝ,
      (Real.sqrt (a^d))⁻¹ *
        ∑ m : Fin d → Fin N, canonicalSmoothModeCoeff d N a mass T x m * η_S m
      ∂(Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)) = 0 := by
  have hsum :
      ∫ η_S : (Fin d → Fin N) → ℝ,
        ∑ m : Fin d → Fin N, canonicalSmoothModeCoeff d N a mass T x m * η_S m
        ∂(Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)) = 0 := by
    rw [integral_finset_sum]
    · refine Finset.sum_eq_zero ?_
      intro m _
      rw [integral_const_mul, pi_gaussian_eval_integral_zero (k := m)]
      ring
    · intro m _
      have h_eval : Integrable (fun η_S : (Fin d → Fin N) → ℝ => η_S m)
          (Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)) := by
        exact integrable_eval IsGaussian.integrable_id
      convert h_eval.const_mul (canonicalSmoothModeCoeff d N a mass T x m)
  rw [integral_const_mul, hsum]
  ring

private lemma canonicalRoughFieldFunction_marginal_integral_zero
    (T : ℝ) (x : FinLatticeSites d N) :
    ∫ η_R : (Fin d → Fin N) → ℝ,
      (Real.sqrt (a^d))⁻¹ *
        ∑ m : Fin d → Fin N, canonicalRoughModeCoeff d N a mass T x m * η_R m
      ∂(Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)) = 0 := by
  have hsum :
      ∫ η_R : (Fin d → Fin N) → ℝ,
        ∑ m : Fin d → Fin N, canonicalRoughModeCoeff d N a mass T x m * η_R m
        ∂(Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)) = 0 := by
    rw [integral_finset_sum]
    · refine Finset.sum_eq_zero ?_
      intro m _
      rw [integral_const_mul, pi_gaussian_eval_integral_zero (k := m)]
      ring
    · intro m _
      have h_eval : Integrable (fun η_R : (Fin d → Fin N) → ℝ => η_R m)
          (Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)) := by
        exact integrable_eval IsGaussian.integrable_id
      convert h_eval.const_mul (canonicalRoughModeCoeff d N a mass T x m)
  rw [integral_const_mul, hsum]
  ring

theorem canonicalSmoothRough_cross_moment_zero
    (T : ℝ) (x y : FinLatticeSites d N) :
    ∫ η : CanonicalJoint d N,
      canonicalSmoothFieldFunction d N a mass T η x *
        canonicalRoughFieldFunction d N a mass T η y
      ∂(canonicalJointMeasure d N) = 0 := by
  rw [canonicalJointMeasure]
  simp only [canonicalSmoothFieldFunction, canonicalRoughFieldFunction]
  have h_factor :
      ∫ η : CanonicalJoint d N,
        ((Real.sqrt (a^d))⁻¹ *
            ∑ m : Fin d → Fin N, canonicalSmoothModeCoeff d N a mass T x m * η.1 m) *
          ((Real.sqrt (a^d))⁻¹ *
            ∑ m : Fin d → Fin N, canonicalRoughModeCoeff d N a mass T y m * η.2 m)
        ∂(Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)).prod
          (Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)) =
      (∫ η_S : (Fin d → Fin N) → ℝ,
        (Real.sqrt (a^d))⁻¹ *
          ∑ m : Fin d → Fin N, canonicalSmoothModeCoeff d N a mass T x m * η_S m
        ∂(Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1))) *
      (∫ η_R : (Fin d → Fin N) → ℝ,
        (Real.sqrt (a^d))⁻¹ *
          ∑ m : Fin d → Fin N, canonicalRoughModeCoeff d N a mass T y m * η_R m
        ∂(Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1))) := by
    simpa [CanonicalJoint] using
      (integral_prod_mul
        (μ := Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1))
        (ν := Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1))
        (f := fun η_S : (Fin d → Fin N) → ℝ =>
          (Real.sqrt (a^d))⁻¹ *
            ∑ m : Fin d → Fin N, canonicalSmoothModeCoeff d N a mass T x m * η_S m)
        (g := fun η_R : (Fin d → Fin N) → ℝ =>
          (Real.sqrt (a^d))⁻¹ *
            ∑ m : Fin d → Fin N, canonicalRoughModeCoeff d N a mass T y m * η_R m))
  rw [h_factor, canonicalSmoothFieldFunction_marginal_integral_zero,
    canonicalRoughFieldFunction_marginal_integral_zero]
  ring

private lemma canonicalEigenvalue_pos
    (ha : 0 < a) (hmass : 0 < mass) (m : Fin d → Fin N) :
    0 < canonicalEigenvalue d N a mass m := by
  unfold canonicalEigenvalue
  have hsum_nonneg : 0 ≤ ∑ i : Fin d, latticeEigenvalue1d N a (m i) :=
    Finset.sum_nonneg (fun i _ => latticeEigenvalue1d_nonneg N a (m i))
  nlinarith [sq_pos_of_pos hmass]

private lemma canonicalSmoothWeight_nonneg
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (m : Fin d → Fin N) :
    0 ≤ canonicalSmoothWeight d N a mass T m := by
  unfold canonicalSmoothWeight
  exact div_nonneg (le_of_lt (Real.exp_pos _))
    (canonicalEigenvalue_pos (d := d) (N := N) (a := a) (mass := mass) ha hmass m).le

private lemma canonicalRoughWeight_nonneg
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T) (m : Fin d → Fin N) :
    0 ≤ canonicalRoughWeight d N a mass T m := by
  unfold canonicalRoughWeight
  have hLam := canonicalEigenvalue_pos (d := d) (N := N) (a := a) (mass := mass) ha hmass m
  have h_exp_le : Real.exp (-T * canonicalEigenvalue d N a mass m) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith
  have h_num : 0 ≤ 1 - Real.exp (-T * canonicalEigenvalue d N a mass m) := by
    linarith
  exact div_nonneg h_num hLam.le

private lemma canonicalEigenvalue_split
    (T : ℝ) (m : Fin d → Fin N) :
    (canonicalEigenvalue d N a mass m)⁻¹ =
      canonicalSmoothWeight d N a mass T m +
        canonicalRoughWeight d N a mass T m := by
  unfold canonicalSmoothWeight canonicalRoughWeight
  rw [inv_eq_one_div, ← add_div]
  ring

private lemma canonicalSmoothFieldFunction_self_moment
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (x y : FinLatticeSites d N) :
    ∫ η : CanonicalJoint d N,
      canonicalSmoothFieldFunction d N a mass T η x *
        canonicalSmoothFieldFunction d N a mass T η y
      ∂(canonicalJointMeasure d N) =
    (a^d : ℝ)⁻¹ *
      ∑ m : Fin d → Fin N,
        canonicalSmoothWeight d N a mass T m *
          latticeFourierProductBasisFun N d m x *
          latticeFourierProductBasisFun N d m y /
          latticeFourierProductNormSq N d m := by
  rw [canonicalJointMeasure]
  simp only [canonicalSmoothFieldFunction]
  have h_fst :=
    integral_fun_fst (E := ℝ)
      (μ := Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1))
      (ν := Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1))
      (f := fun η_S : (Fin d → Fin N) → ℝ =>
        ((Real.sqrt (a^d))⁻¹ *
            ∑ m : Fin d → Fin N, canonicalSmoothModeCoeff d N a mass T x m * η_S m) *
          ((Real.sqrt (a^d))⁻¹ *
            ∑ m : Fin d → Fin N, canonicalSmoothModeCoeff d N a mass T y m * η_S m))
  simp at h_fst
  rw [h_fst]
  have ha_d_pos : (0 : ℝ) < a^d := pow_pos ha d
  have hsqrt_sq : (Real.sqrt (a^d))⁻¹ * (Real.sqrt (a^d))⁻¹ = (a^d : ℝ)⁻¹ := by
    rw [← mul_inv, ← Real.sqrt_mul (le_of_lt ha_d_pos),
      Real.sqrt_mul_self (le_of_lt ha_d_pos)]
  have h_rewrite : ∀ η_S : (Fin d → Fin N) → ℝ,
      ((Real.sqrt (a^d))⁻¹ *
          ∑ m : Fin d → Fin N, canonicalSmoothModeCoeff d N a mass T x m * η_S m) *
        ((Real.sqrt (a^d))⁻¹ *
          ∑ m : Fin d → Fin N, canonicalSmoothModeCoeff d N a mass T y m * η_S m) =
      (a^d : ℝ)⁻¹ *
        ((∑ m : Fin d → Fin N, canonicalSmoothModeCoeff d N a mass T x m * η_S m) *
          (∑ l : Fin d → Fin N, canonicalSmoothModeCoeff d N a mass T y l * η_S l)) := by
    intro η_S
    rw [show ∀ A B C D : ℝ, (A * B) * (C * D) = (A * C) * (B * D) by intros; ring,
      hsqrt_sq]
  simp_rw [h_rewrite, integral_const_mul]
  rw [pi_gaussian_bilinear_moment
    (p := fun m => canonicalSmoothModeCoeff d N a mass T x m)
    (q := fun l => canonicalSmoothModeCoeff d N a mass T y l)]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro m _
  have hC :
      0 ≤ canonicalSmoothWeight d N a mass T m /
        latticeFourierProductNormSq N d m := by
    apply div_nonneg
    · exact canonicalSmoothWeight_nonneg
        (d := d) (N := N) (a := a) (mass := mass) ha hmass T m
    · exact (latticeFourierProductNormSq_pos (N := N) d m).le
  have h_sq :
      Real.sqrt (canonicalSmoothWeight d N a mass T m /
          latticeFourierProductNormSq N d m) *
        Real.sqrt (canonicalSmoothWeight d N a mass T m /
          latticeFourierProductNormSq N d m) =
      canonicalSmoothWeight d N a mass T m /
        latticeFourierProductNormSq N d m :=
    Real.mul_self_sqrt hC
  unfold canonicalSmoothModeCoeff
  calc
    Real.sqrt (canonicalSmoothWeight d N a mass T m / latticeFourierProductNormSq N d m) *
        latticeFourierProductBasisFun N d m x *
        (Real.sqrt (canonicalSmoothWeight d N a mass T m / latticeFourierProductNormSq N d m) *
          latticeFourierProductBasisFun N d m y)
      = (Real.sqrt (canonicalSmoothWeight d N a mass T m / latticeFourierProductNormSq N d m) *
          Real.sqrt (canonicalSmoothWeight d N a mass T m / latticeFourierProductNormSq N d m)) *
          latticeFourierProductBasisFun N d m x *
          latticeFourierProductBasisFun N d m y := by ring
    _ = canonicalSmoothWeight d N a mass T m *
          latticeFourierProductBasisFun N d m x *
          latticeFourierProductBasisFun N d m y /
          latticeFourierProductNormSq N d m := by
          rw [h_sq]
          ring

private lemma canonicalRoughFieldFunction_self_moment
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (x y : FinLatticeSites d N) :
    ∫ η : CanonicalJoint d N,
      canonicalRoughFieldFunction d N a mass T η x *
        canonicalRoughFieldFunction d N a mass T η y
      ∂(canonicalJointMeasure d N) =
    (a^d : ℝ)⁻¹ *
      ∑ m : Fin d → Fin N,
        canonicalRoughWeight d N a mass T m *
          latticeFourierProductBasisFun N d m x *
          latticeFourierProductBasisFun N d m y /
          latticeFourierProductNormSq N d m := by
  rw [canonicalJointMeasure]
  simp only [canonicalRoughFieldFunction]
  have h_snd :=
    integral_fun_snd (E := ℝ)
      (μ := Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1))
      (ν := Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1))
      (f := fun η_R : (Fin d → Fin N) → ℝ =>
        ((Real.sqrt (a^d))⁻¹ *
            ∑ m : Fin d → Fin N, canonicalRoughModeCoeff d N a mass T x m * η_R m) *
          ((Real.sqrt (a^d))⁻¹ *
            ∑ m : Fin d → Fin N, canonicalRoughModeCoeff d N a mass T y m * η_R m))
  simp at h_snd
  rw [h_snd]
  have ha_d_pos : (0 : ℝ) < a^d := pow_pos ha d
  have hsqrt_sq : (Real.sqrt (a^d))⁻¹ * (Real.sqrt (a^d))⁻¹ = (a^d : ℝ)⁻¹ := by
    rw [← mul_inv, ← Real.sqrt_mul (le_of_lt ha_d_pos),
      Real.sqrt_mul_self (le_of_lt ha_d_pos)]
  have h_rewrite : ∀ η_R : (Fin d → Fin N) → ℝ,
      ((Real.sqrt (a^d))⁻¹ *
          ∑ m : Fin d → Fin N, canonicalRoughModeCoeff d N a mass T x m * η_R m) *
        ((Real.sqrt (a^d))⁻¹ *
          ∑ m : Fin d → Fin N, canonicalRoughModeCoeff d N a mass T y m * η_R m) =
      (a^d : ℝ)⁻¹ *
        ((∑ m : Fin d → Fin N, canonicalRoughModeCoeff d N a mass T x m * η_R m) *
          (∑ l : Fin d → Fin N, canonicalRoughModeCoeff d N a mass T y l * η_R l)) := by
    intro η_R
    rw [show ∀ A B C D : ℝ, (A * B) * (C * D) = (A * C) * (B * D) by intros; ring,
      hsqrt_sq]
  simp_rw [h_rewrite, integral_const_mul]
  rw [pi_gaussian_bilinear_moment
    (p := fun m => canonicalRoughModeCoeff d N a mass T x m)
    (q := fun l => canonicalRoughModeCoeff d N a mass T y l)]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro m _
  have hC :
      0 ≤ canonicalRoughWeight d N a mass T m /
        latticeFourierProductNormSq N d m := by
    apply div_nonneg
    · exact canonicalRoughWeight_nonneg
        (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT m
    · exact (latticeFourierProductNormSq_pos (N := N) d m).le
  have h_sq :
      Real.sqrt (canonicalRoughWeight d N a mass T m /
          latticeFourierProductNormSq N d m) *
        Real.sqrt (canonicalRoughWeight d N a mass T m /
          latticeFourierProductNormSq N d m) =
      canonicalRoughWeight d N a mass T m /
        latticeFourierProductNormSq N d m :=
    Real.mul_self_sqrt hC
  unfold canonicalRoughModeCoeff
  calc
    Real.sqrt (canonicalRoughWeight d N a mass T m / latticeFourierProductNormSq N d m) *
        latticeFourierProductBasisFun N d m x *
        (Real.sqrt (canonicalRoughWeight d N a mass T m / latticeFourierProductNormSq N d m) *
          latticeFourierProductBasisFun N d m y)
      = (Real.sqrt (canonicalRoughWeight d N a mass T m / latticeFourierProductNormSq N d m) *
          Real.sqrt (canonicalRoughWeight d N a mass T m / latticeFourierProductNormSq N d m)) *
          latticeFourierProductBasisFun N d m x *
          latticeFourierProductBasisFun N d m y := by ring
    _ = canonicalRoughWeight d N a mass T m *
          latticeFourierProductBasisFun N d m x *
          latticeFourierProductBasisFun N d m y /
          latticeFourierProductNormSq N d m := by
          rw [h_sq]
          ring

private lemma canonicalRoughSmooth_cross_moment_zero
    (T : ℝ) (x y : FinLatticeSites d N) :
    ∫ η : CanonicalJoint d N,
      canonicalRoughFieldFunction d N a mass T η x *
        canonicalSmoothFieldFunction d N a mass T η y
      ∂(canonicalJointMeasure d N) = 0 := by
  have h_swap : ∀ η : CanonicalJoint d N,
      canonicalRoughFieldFunction d N a mass T η x *
          canonicalSmoothFieldFunction d N a mass T η y =
        canonicalSmoothFieldFunction d N a mass T η y *
          canonicalRoughFieldFunction d N a mass T η x := by
    intro η
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall h_swap)]
  exact canonicalSmoothRough_cross_moment_zero d N a mass T y x

theorem canonicalSmoothFieldFunction_memLp_two
    (T : ℝ) (z : FinLatticeSites d N) :
    MemLp (fun η : CanonicalJoint d N =>
      canonicalSmoothFieldFunction d N a mass T η z) 2 (canonicalJointMeasure d N) := by
  unfold canonicalSmoothFieldFunction
  refine MemLp.const_mul ?_ _
  refine memLp_finset_sum _ (fun m _ => ?_)
  refine MemLp.const_mul ?_ _
  rw [canonicalJointMeasure]
  have h : MemLp (fun η_S : (Fin d → Fin N) → ℝ => η_S m) 2
      (Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)) :=
    MemLp.comp_measurePreserving IsGaussian.memLp_two_id
      (measurePreserving_eval (μ := fun _ : Fin d → Fin N => gaussianReal 0 1) m)
  exact h.comp_measurePreserving
    (μ := (Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)).prod
      (Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)))
    measurePreserving_fst

theorem canonicalRoughFieldFunction_memLp_two
    (T : ℝ) (z : FinLatticeSites d N) :
    MemLp (fun η : CanonicalJoint d N =>
      canonicalRoughFieldFunction d N a mass T η z) 2 (canonicalJointMeasure d N) := by
  unfold canonicalRoughFieldFunction
  refine MemLp.const_mul ?_ _
  refine memLp_finset_sum _ (fun m _ => ?_)
  refine MemLp.const_mul ?_ _
  rw [canonicalJointMeasure]
  have h : MemLp (fun η_R : (Fin d → Fin N) → ℝ => η_R m) 2
      (Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)) :=
    MemLp.comp_measurePreserving IsGaussian.memLp_two_id
      (measurePreserving_eval (μ := fun _ : Fin d → Fin N => gaussianReal 0 1) m)
  exact h.comp_measurePreserving
    (μ := (Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)).prod
      (Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)))
    measurePreserving_snd

theorem canonicalSumFieldFunction_memLp_two
    (T : ℝ) (z : FinLatticeSites d N) :
    MemLp (fun η : CanonicalJoint d N =>
      canonicalSumFieldFunction d N a mass T η z) 2 (canonicalJointMeasure d N) := by
  have hs := canonicalSmoothFieldFunction_memLp_two (d := d) (N := N) (a := a) (mass := mass) T z
  have hr := canonicalRoughFieldFunction_memLp_two (d := d) (N := N) (a := a) (mass := mass) T z
  have hsum : MemLp
      ((fun η : CanonicalJoint d N =>
          canonicalSmoothFieldFunction d N a mass T η z) +
        (fun η : CanonicalJoint d N =>
          canonicalRoughFieldFunction d N a mass T η z))
      2 (canonicalJointMeasure d N) := hs.add hr
  simpa [Pi.add_apply, canonicalSumFieldFunction] using hsum

theorem canonicalSumFieldFunction_covariance
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (x y : FinLatticeSites d N) :
    ∫ η : CanonicalJoint d N,
      canonicalSumFieldFunction d N a mass T η x *
        canonicalSumFieldFunction d N a mass T η y
      ∂(canonicalJointMeasure d N) =
    (a^d : ℝ)⁻¹ *
      ∑ m : Fin d → Fin N,
        latticeFourierProductBasisFun N d m x *
          latticeFourierProductBasisFun N d m y /
          (canonicalEigenvalue d N a mass m *
            latticeFourierProductNormSq N d m) := by
  have h_ss := canonicalSmoothFieldFunction_self_moment
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x y
  have h_rr := canonicalRoughFieldFunction_self_moment
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x y
  have h_sr := canonicalSmoothRough_cross_moment_zero
    (d := d) (N := N) (a := a) (mass := mass) T x y
  have h_rs := canonicalRoughSmooth_cross_moment_zero
    (d := d) (N := N) (a := a) (mass := mass) T x y
  let fss : CanonicalJoint d N → ℝ := fun η =>
    canonicalSmoothFieldFunction d N a mass T η x *
      canonicalSmoothFieldFunction d N a mass T η y
  let fsr : CanonicalJoint d N → ℝ := fun η =>
    canonicalSmoothFieldFunction d N a mass T η x *
      canonicalRoughFieldFunction d N a mass T η y
  let frs : CanonicalJoint d N → ℝ := fun η =>
    canonicalRoughFieldFunction d N a mass T η x *
      canonicalSmoothFieldFunction d N a mass T η y
  let frr : CanonicalJoint d N → ℝ := fun η =>
    canonicalRoughFieldFunction d N a mass T η x *
      canonicalRoughFieldFunction d N a mass T η y
  have h_eq : ∀ η : CanonicalJoint d N,
      canonicalSumFieldFunction d N a mass T η x *
        canonicalSumFieldFunction d N a mass T η y =
      fss η + (fsr η + (frs η + frr η)) := by
    intro η
    simp [canonicalSumFieldFunction, fss, fsr, frs, frr]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall h_eq)]
  have h_ss_int : Integrable (fun η : CanonicalJoint d N =>
      canonicalSmoothFieldFunction d N a mass T η x *
        canonicalSmoothFieldFunction d N a mass T η y) (canonicalJointMeasure d N) :=
    MemLp.integrable_mul
      (canonicalSmoothFieldFunction_memLp_two (d := d) (N := N) (a := a) (mass := mass) T x)
      (canonicalSmoothFieldFunction_memLp_two (d := d) (N := N) (a := a) (mass := mass) T y)
  have h_sr_int : Integrable (fun η : CanonicalJoint d N =>
      canonicalSmoothFieldFunction d N a mass T η x *
        canonicalRoughFieldFunction d N a mass T η y) (canonicalJointMeasure d N) :=
    MemLp.integrable_mul
      (canonicalSmoothFieldFunction_memLp_two (d := d) (N := N) (a := a) (mass := mass) T x)
      (canonicalRoughFieldFunction_memLp_two (d := d) (N := N) (a := a) (mass := mass) T y)
  have h_rs_int : Integrable (fun η : CanonicalJoint d N =>
      canonicalRoughFieldFunction d N a mass T η x *
        canonicalSmoothFieldFunction d N a mass T η y) (canonicalJointMeasure d N) :=
    MemLp.integrable_mul
      (canonicalRoughFieldFunction_memLp_two (d := d) (N := N) (a := a) (mass := mass) T x)
      (canonicalSmoothFieldFunction_memLp_two (d := d) (N := N) (a := a) (mass := mass) T y)
  have h_rr_int : Integrable (fun η : CanonicalJoint d N =>
      canonicalRoughFieldFunction d N a mass T η x *
        canonicalRoughFieldFunction d N a mass T η y) (canonicalJointMeasure d N) :=
    MemLp.integrable_mul
      (canonicalRoughFieldFunction_memLp_two (d := d) (N := N) (a := a) (mass := mass) T x)
      (canonicalRoughFieldFunction_memLp_two (d := d) (N := N) (a := a) (mass := mass) T y)
  have h_ss_int' : Integrable fss (canonicalJointMeasure d N) := by
    simpa [fss] using h_ss_int
  have h_sr_int' : Integrable fsr (canonicalJointMeasure d N) := by
    simpa [fsr] using h_sr_int
  have h_rs_int' : Integrable frs (canonicalJointMeasure d N) := by
    simpa [frs] using h_rs_int
  have h_rr_int' : Integrable frr (canonicalJointMeasure d N) := by
    simpa [frr] using h_rr_int
  change ∫ η, (fss + (fsr + (frs + frr))) η ∂(canonicalJointMeasure d N) = _
  have hsplit1 :
      ∫ η, (fss + (fsr + (frs + frr))) η ∂(canonicalJointMeasure d N) =
        ∫ η, fss η ∂(canonicalJointMeasure d N) +
          ∫ η, (fsr + (frs + frr)) η ∂(canonicalJointMeasure d N) := by
    simpa using integral_add h_ss_int' (h_sr_int'.add (h_rs_int'.add h_rr_int'))
  have hsplit2 :
      ∫ η, (fsr + (frs + frr)) η ∂(canonicalJointMeasure d N) =
        ∫ η, fsr η ∂(canonicalJointMeasure d N) +
          ∫ η, (frs + frr) η ∂(canonicalJointMeasure d N) := by
    simpa using integral_add h_sr_int' (h_rs_int'.add h_rr_int')
  have hsplit3 :
      ∫ η, (frs + frr) η ∂(canonicalJointMeasure d N) =
        ∫ η, frs η ∂(canonicalJointMeasure d N) +
          ∫ η, frr η ∂(canonicalJointMeasure d N) := by
    simpa using integral_add h_rs_int' h_rr_int'
  rw [hsplit1, hsplit2, hsplit3]
  rw [h_ss, h_sr, h_rs, h_rr]
  rw [zero_add, zero_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro m _
  have hnormPos : 0 < latticeFourierProductNormSq N d m :=
    latticeFourierProductNormSq_pos (N := N) d m
  have hLamPos : 0 < canonicalEigenvalue d N a mass m :=
    canonicalEigenvalue_pos (d := d) (N := N) (a := a) (mass := mass) ha hmass m
  calc
    canonicalSmoothWeight d N a mass T m *
        latticeFourierProductBasisFun N d m x *
        latticeFourierProductBasisFun N d m y /
        latticeFourierProductNormSq N d m +
      canonicalRoughWeight d N a mass T m *
        latticeFourierProductBasisFun N d m x *
        latticeFourierProductBasisFun N d m y /
        latticeFourierProductNormSq N d m
      = (canonicalSmoothWeight d N a mass T m +
          canonicalRoughWeight d N a mass T m) *
          (latticeFourierProductBasisFun N d m x *
            latticeFourierProductBasisFun N d m y /
            latticeFourierProductNormSq N d m) := by
              ring
    _ = (canonicalEigenvalue d N a mass m)⁻¹ *
          (latticeFourierProductBasisFun N d m x *
            latticeFourierProductBasisFun N d m y /
            latticeFourierProductNormSq N d m) := by
              rw [← canonicalEigenvalue_split (d := d) (N := N) (a := a) (mass := mass) T m]
    _ = latticeFourierProductBasisFun N d m x *
          latticeFourierProductBasisFun N d m y /
          (canonicalEigenvalue d N a mass m *
            latticeFourierProductNormSq N d m) := by
              field_simp [ne_of_gt hLamPos, ne_of_gt hnormPos]

private lemma latticeFourierProductCoeff_delta
    (x : FinLatticeSites d N) (m : Fin d → Fin N) :
    latticeFourierProductCoeff N d (fun z : FinLatticeSites d N => if z = x then 1 else 0) m =
      latticeFourierProductBasisFun N d m x := by
  unfold latticeFourierProductCoeff
  rw [Finset.sum_eq_single x]
  · simp
  · intro z _ hzx
    simp [if_neg hzx]
  · intro hx
    exact (hx (Finset.mem_univ x)).elim

private lemma latticeHeatKernel_coeff
    (ha : a ≠ 0) (t : ℝ) (m : Fin d → Fin N) (g : FinLatticeField d N) :
    latticeFourierProductCoeff N d ((latticeHeatKernelMatrix d N a t).mulVec g) m =
      Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
        latticeFourierProductCoeff N d g m := by
  have h_symm : (latticeHeatKernelMatrix d N a t).IsHermitian :=
    latticeHeatKernelMatrix_isHermitian d N a t
  have h_eig :
      (latticeHeatKernelMatrix d N a t).mulVec (latticeFourierProductBasisFun N d m) =
        Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) •
          latticeFourierProductBasisFun N d m := by
    apply Matrix.IsHermitian.mulVec_exp_of_eigenvector
      (hM := negLaplacianMatrix_isHermitian d N a) (t := t)
    ext x
    rw [negLaplacianMatrix]
    rw [← massOperator_eq_matrix_mulVec (d := d) (N := N) (a := a) (mass := 0)
      (f := latticeFourierProductBasisFun N d m) x]
    simpa using
      (massOperator_product_eigenvector_family (N := N) d a 0 ha m x)
  unfold latticeFourierProductCoeff
  calc
    ∑ x : FinLatticeSites d N,
        ((latticeHeatKernelMatrix d N a t).mulVec g) x *
          latticeFourierProductBasisFun N d m x
      = ∑ x : FinLatticeSites d N,
          latticeFourierProductBasisFun N d m x *
            ((latticeHeatKernelMatrix d N a t).mulVec g) x := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              ring
    _ = ∑ x : FinLatticeSites d N,
          ((latticeHeatKernelMatrix d N a t).mulVec
              (latticeFourierProductBasisFun N d m)) x * g x := by
                simpa [dotProduct, mul_comm] using
                  (Matrix.IsHermitian.dotProduct_mulVec_comm h_symm
                    (latticeFourierProductBasisFun N d m) g).symm
    _ = ∑ x : FinLatticeSites d N,
          (Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
              latticeFourierProductBasisFun N d m x) * g x := by
                rw [h_eig]
                refine Finset.sum_congr rfl ?_
                intro x hx
                simp [Pi.smul_apply, smul_eq_mul]
    _ = Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
          latticeFourierProductCoeff N d g m := by
            calc
              ∑ x : FinLatticeSites d N,
                  (Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
                      latticeFourierProductBasisFun N d m x) * g x
                = ∑ x : FinLatticeSites d N,
                    Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
                      (g x * latticeFourierProductBasisFun N d m x) := by
                        refine Finset.sum_congr rfl ?_
                        intro x hx
                        ring
              _ = Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
                    ∑ x : FinLatticeSites d N, g x * latticeFourierProductBasisFun N d m x := by
                      rw [← Finset.mul_sum]
              _ = Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
                    latticeFourierProductCoeff N d g m := by
                      rfl

private lemma latticeHeatKernel_bilinear_eq_dft_spectral
    (ha : a ≠ 0) (t : ℝ) (f g : FinLatticeField d N) :
    ∑ x : FinLatticeSites d N, f x * ((latticeHeatKernelMatrix d N a t).mulVec g) x =
      ∑ m : Fin d → Fin N,
        Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
          latticeFourierProductCoeff N d f m *
          latticeFourierProductCoeff N d g m /
          latticeFourierProductNormSq N d m := by
  rw [dft_parseval_family (N := N) d f ((latticeHeatKernelMatrix d N a t).mulVec g)]
  refine Finset.sum_congr rfl ?_
  intro m hm
  rw [latticeHeatKernel_coeff (d := d) (N := N) (a := a) ha t m g]
  ring

private lemma latticeHeatKernel_diagonal_eq_dft_spectral
    (ha : a ≠ 0) (t : ℝ) (x : FinLatticeSites d N) :
    latticeHeatKernelMatrix d N a t x x =
      ∑ m : Fin d → Fin N,
        Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
          (latticeFourierProductBasisFun N d m x) ^ 2 /
          latticeFourierProductNormSq N d m := by
  let δx : FinLatticeField d N := fun z => if z = x then 1 else 0
  have hspec := latticeHeatKernel_bilinear_eq_dft_spectral
    (d := d) (N := N) (a := a) ha t δx δx
  have hcoeff :
      ∀ m : Fin d → Fin N,
        latticeFourierProductCoeff N d δx m = latticeFourierProductBasisFun N d m x := by
    intro m
    exact latticeFourierProductCoeff_delta (d := d) (N := N) x m
  calc
    latticeHeatKernelMatrix d N a t x x
      = ∑ z : FinLatticeSites d N, δx z * ((latticeHeatKernelMatrix d N a t).mulVec δx) z := by
          simp [δx, Matrix.mulVec, dotProduct]
    _ = ∑ m : Fin d → Fin N,
          Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
            latticeFourierProductCoeff N d δx m *
            latticeFourierProductCoeff N d δx m /
            latticeFourierProductNormSq N d m := hspec
    _ = ∑ m : Fin d → Fin N,
          Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
            (latticeFourierProductBasisFun N d m x) ^ 2 /
            latticeFourierProductNormSq N d m := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              rw [hcoeff m]
              ring

private lemma latticeHeatKernel_entry_eq_dft_spectral
    (ha : a ≠ 0) (t : ℝ) (x y : FinLatticeSites d N) :
    latticeHeatKernelMatrix d N a t x y =
      ∑ m : Fin d → Fin N,
        Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
          latticeFourierProductBasisFun N d m x *
          latticeFourierProductBasisFun N d m y /
          latticeFourierProductNormSq N d m := by
  let δx : FinLatticeField d N := fun z => if z = x then 1 else 0
  let δy : FinLatticeField d N := fun z => if z = y then 1 else 0
  have hspec := latticeHeatKernel_bilinear_eq_dft_spectral
    (d := d) (N := N) (a := a) ha t δx δy
  have hcoeffx :
      ∀ m : Fin d → Fin N,
        latticeFourierProductCoeff N d δx m = latticeFourierProductBasisFun N d m x := by
    intro m
    exact latticeFourierProductCoeff_delta (d := d) (N := N) x m
  have hcoeffy :
      ∀ m : Fin d → Fin N,
        latticeFourierProductCoeff N d δy m = latticeFourierProductBasisFun N d m y := by
    intro m
    exact latticeFourierProductCoeff_delta (d := d) (N := N) y m
  calc
    latticeHeatKernelMatrix d N a t x y
      = ∑ z : FinLatticeSites d N, δx z * ((latticeHeatKernelMatrix d N a t).mulVec δy) z := by
          simp [δx, δy, Matrix.mulVec, dotProduct]
    _ = ∑ m : Fin d → Fin N,
          Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
            latticeFourierProductCoeff N d δx m *
            latticeFourierProductCoeff N d δy m /
            latticeFourierProductNormSq N d m := hspec
    _ = ∑ m : Fin d → Fin N,
          Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
          latticeFourierProductBasisFun N d m x *
            latticeFourierProductBasisFun N d m y /
            latticeFourierProductNormSq N d m := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              rw [hcoeffx m, hcoeffy m]

/-- Spectral formula for an arbitrary heat-kernel entry. -/
theorem latticeHeatKernel_entry_eq_eigenvalue_average
    (ha : a ≠ 0) (t : ℝ) (x y : FinLatticeSites d N) :
    latticeHeatKernelMatrix d N a t x y =
      ∑ m : Fin d → Fin N,
        Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
          latticeFourierProductBasisFun N d m x *
          latticeFourierProductBasisFun N d m y /
          latticeFourierProductNormSq N d m :=
  latticeHeatKernel_entry_eq_dft_spectral (d := d) (N := N) (a := a) ha t x y

private lemma latticeHeatKernel_diagonal_translation_invariant
    (t : ℝ) (x y : FinLatticeSites d N) :
    latticeHeatKernelMatrix d N a t y y =
      latticeHeatKernelMatrix d N a t x x := by
  let v : FinLatticeSites d N := y - x
  have hcomm := latticeTranslation_commute_heatKernel d N a t v
  have htoeplitz :
      latticeHeatKernelMatrix d N a t (x + v) (x + v) =
        latticeHeatKernelMatrix d N a t x x := by
    have hEq := congr_fun (congr_fun hcomm.eq (x + v)) x
    simp only [Matrix.mul_apply, latticeTranslationMatrix] at hEq
    simp_rw [show ∀ z : FinLatticeSites d N, (z = (x + v) - v) ↔ z = x from
      fun z => by
        constructor <;> intro hz
        · simpa [add_sub_cancel_right] using hz
        · simpa [add_sub_cancel_right] using hz] at hEq
    simp_rw [show ∀ z : FinLatticeSites d N, (x = z - v) ↔ z = x + v from
      fun z => by
        constructor <;> intro hz
        · rw [hz, sub_add_cancel]
        · rw [hz, add_sub_cancel_right]] at hEq
    simpa using hEq.symm
  simpa [v, sub_add_cancel] using htoeplitz

private lemma latticeHeatKernel_diagonal_eq_average
    (ha : a ≠ 0) (t : ℝ) (x : FinLatticeSites d N) :
    latticeHeatKernelMatrix d N a t x x =
      (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
        ∑ m : Fin d → Fin N,
          Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) := by
  have hconst : ∀ y : FinLatticeSites d N,
      latticeHeatKernelMatrix d N a t y y =
        latticeHeatKernelMatrix d N a t x x := by
    intro y
    exact latticeHeatKernel_diagonal_translation_invariant
      (d := d) (N := N) (a := a) t x y
  have hsum_diag :
      ∑ y : FinLatticeSites d N, latticeHeatKernelMatrix d N a t y y =
        ∑ m : Fin d → Fin N,
          Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) := by
    calc
      ∑ y : FinLatticeSites d N, latticeHeatKernelMatrix d N a t y y
        = ∑ y : FinLatticeSites d N,
            ∑ m : Fin d → Fin N,
              Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
                (latticeFourierProductBasisFun N d m y) ^ 2 /
                latticeFourierProductNormSq N d m := by
                  refine Finset.sum_congr rfl ?_
                  intro y hy
                  exact latticeHeatKernel_diagonal_eq_dft_spectral
                    (d := d) (N := N) (a := a) ha t y
      _ = ∑ m : Fin d → Fin N,
            ∑ y : FinLatticeSites d N,
              Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
                (latticeFourierProductBasisFun N d m y) ^ 2 /
                latticeFourierProductNormSq N d m := by
                  rw [Finset.sum_comm]
      _ = ∑ m : Fin d → Fin N,
            Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              have hnorm_pos : 0 < latticeFourierProductNormSq N d m :=
                latticeFourierProductNormSq_pos (N := N) d m
              calc
                ∑ y : FinLatticeSites d N,
                    Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
                      (latticeFourierProductBasisFun N d m y) ^ 2 /
                      latticeFourierProductNormSq N d m
                  = ∑ y : FinLatticeSites d N,
                      Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
                        ((latticeFourierProductBasisFun N d m y) ^ 2 /
                          latticeFourierProductNormSq N d m) := by
                            refine Finset.sum_congr rfl ?_
                            intro y hy
                            ring
                _ = Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
                      ∑ y : FinLatticeSites d N,
                        (latticeFourierProductBasisFun N d m y) ^ 2 /
                        latticeFourierProductNormSq N d m := by
                          rw [← Finset.mul_sum]
                _ = Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
                      (((latticeFourierProductNormSq N d m)⁻¹) *
                        ∑ y : FinLatticeSites d N,
                          (latticeFourierProductBasisFun N d m y) ^ 2) := by
                            congr 1
                            calc
                              ∑ y : FinLatticeSites d N,
                                  (latticeFourierProductBasisFun N d m y) ^ 2 /
                                    latticeFourierProductNormSq N d m
                                = ∑ y : FinLatticeSites d N,
                                    ((latticeFourierProductNormSq N d m)⁻¹ *
                                      (latticeFourierProductBasisFun N d m y) ^ 2) := by
                                          refine Finset.sum_congr rfl ?_
                                          intro y hy
                                          field_simp [ne_of_gt hnorm_pos]
                              _ = ((latticeFourierProductNormSq N d m)⁻¹) *
                                    ∑ y : FinLatticeSites d N,
                                      (latticeFourierProductBasisFun N d m y) ^ 2 := by
                                        rw [← Finset.mul_sum]
                _ = Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) := by
                      rw [latticeFourierProductBasis_sq_sum (N := N) d m]
                      field_simp [ne_of_gt hnorm_pos]
  have hcard_pos : (0 : ℝ) < Fintype.card (FinLatticeSites d N) := by
    exact_mod_cast Fintype.card_pos
  have hconst_sum :
      ∑ y : FinLatticeSites d N, latticeHeatKernelMatrix d N a t y y =
        (Fintype.card (FinLatticeSites d N) : ℝ) *
          latticeHeatKernelMatrix d N a t x x := by
    calc
      ∑ y : FinLatticeSites d N, latticeHeatKernelMatrix d N a t y y
        = ∑ _y : FinLatticeSites d N, latticeHeatKernelMatrix d N a t x x := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            exact hconst y
      _ = (Fintype.card (FinLatticeSites d N) : ℝ) *
            latticeHeatKernelMatrix d N a t x x := by
              simp
  calc
    latticeHeatKernelMatrix d N a t x x
      = (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
          ((Fintype.card (FinLatticeSites d N) : ℝ) *
            latticeHeatKernelMatrix d N a t x x) := by
              field_simp [ne_of_gt hcard_pos]
    _ = (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
          ∑ m : Fin d → Fin N,
            Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) := by
              rw [← hconst_sum, hsum_diag]

private lemma canonicalSmoothWeight_eq_integral_Ioi
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (m : Fin d → Fin N) :
    canonicalSmoothWeight d N a mass T m =
      ∫ t in Set.Ioi T,
        Real.exp (-t * mass ^ 2) *
          Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) := by
  unfold canonicalSmoothWeight canonicalEigenvalue
  rw [schwinger_smooth_Ioi
    ((∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2)
    (canonicalEigenvalue_pos (d := d) (N := N) (a := a) (mass := mass) ha hmass m) T]
  congr with t
  rw [← Real.exp_add]
  congr 1
  ring

private lemma canonicalRoughWeight_eq_integral_Icc
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T) (m : Fin d → Fin N) :
    canonicalRoughWeight d N a mass T m =
      ∫ t in Set.Icc 0 T,
        Real.exp (-t * mass ^ 2) *
          Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) := by
  unfold canonicalRoughWeight canonicalEigenvalue
  rw [schwinger_rough
    ((∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2)
    (canonicalEigenvalue_pos (d := d) (N := N) (a := a) (mass := mass) ha hmass m)
    T hT.le]
  congr with t
  rw [← Real.exp_add]
  congr 1
  ring

private lemma smoothWeight_integrand_integrableOn_Ioi
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (m : Fin d → Fin N) :
    IntegrableOn (fun t : ℝ =>
      Real.exp (-t * mass ^ 2) *
        Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) (Set.Ioi T) := by
  have hbase :
      IntegrableOn (fun t : ℝ =>
        Real.exp (-t * canonicalEigenvalue d N a mass m)) (Set.Ioi T) := by
    have hLam := canonicalEigenvalue_pos (d := d) (N := N) (a := a) (mass := mass) ha hmass m
    have h :=
      integrableOn_exp_mul_Ioi (a := -(canonicalEigenvalue d N a mass m))
        (by linarith) T
    simpa [mul_comm] using h
  refine hbase.congr ?_
  filter_upwards with t
  unfold canonicalEigenvalue
  rw [← Real.exp_add]
  congr 1
  ring

private lemma smoothWeight_family_sum_eq_average
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (x : FinLatticeSites d N) :
    ∑ m : Fin d → Fin N,
      canonicalSmoothWeight d N a mass T m *
        (latticeFourierProductBasisFun N d m x) ^ 2 /
        latticeFourierProductNormSq N d m =
      (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
        ∑ m : Fin d → Fin N, canonicalSmoothWeight d N a mass T m := by
  have ha' : a ≠ 0 := ne_of_gt ha
  let c : (Fin d → Fin N) → ℝ := fun m =>
    (latticeFourierProductBasisFun N d m x) ^ 2 /
      latticeFourierProductNormSq N d m
  have h_int_coeff :
      ∀ m : Fin d → Fin N,
        IntegrableOn (fun t : ℝ =>
          (Real.exp (-t * mass ^ 2) *
            Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) * c m) (Set.Ioi T) := by
    intro m
    have hbase := smoothWeight_integrand_integrableOn_Ioi
      (d := d) (N := N) (a := a) (mass := mass) ha hmass T m
    simpa [c, mul_assoc, mul_comm, mul_left_comm] using hbase.mul_const (c m)
  have h_int_base :
      ∀ m : Fin d → Fin N,
        IntegrableOn (fun t : ℝ =>
          Real.exp (-t * mass ^ 2) *
            Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) (Set.Ioi T) := by
    intro m
    exact smoothWeight_integrand_integrableOn_Ioi
      (d := d) (N := N) (a := a) (mass := mass) ha hmass T m
  have hstart :
      ∑ m : Fin d → Fin N,
        canonicalSmoothWeight d N a mass T m *
          (latticeFourierProductBasisFun N d m x) ^ 2 /
          latticeFourierProductNormSq N d m =
      ∑ m : Fin d → Fin N, canonicalSmoothWeight d N a mass T m * c m := by
        refine Finset.sum_congr rfl ?_
        intro m hm
        simp [c]
        ring
  rw [hstart]
  calc
    ∑ m : Fin d → Fin N, canonicalSmoothWeight d N a mass T m * c m
      = ∑ m : Fin d → Fin N,
          ∫ t in Set.Ioi T,
            (Real.exp (-t * mass ^ 2) *
              Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) * c m := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              calc
                canonicalSmoothWeight d N a mass T m * c m
                  = c m * canonicalSmoothWeight d N a mass T m := by ring
                _ = c m *
                    ∫ t in Set.Ioi T,
                      Real.exp (-t * mass ^ 2) *
                        Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) := by
                          rw [canonicalSmoothWeight_eq_integral_Ioi
                            (d := d) (N := N) (a := a) (mass := mass) ha hmass T m]
                _ = ∫ t in Set.Ioi T,
                    c m *
                      (Real.exp (-t * mass ^ 2) *
                        Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) := by
                          rw [integral_const_mul]
                _ = ∫ t in Set.Ioi T,
                    (Real.exp (-t * mass ^ 2) *
                      Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) * c m := by
                          apply integral_congr_ae
                          filter_upwards with t
                          ring
    _ = ∫ t in Set.Ioi T,
          ∑ m : Fin d → Fin N,
            (Real.exp (-t * mass ^ 2) *
              Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) * c m := by
                rw [integral_finset_sum]
                intro m hm
                exact h_int_coeff m
    _ = ∫ t in Set.Ioi T,
          Real.exp (-t * mass ^ 2) *
            ∑ m : Fin d → Fin N,
              Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) * c m := by
                apply integral_congr_ae
                filter_upwards with t
                symm
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl ?_
                intro m hm
                ring
    _ = ∫ t in Set.Ioi T,
          Real.exp (-t * mass ^ 2) * latticeHeatKernelMatrix d N a t x x := by
                apply integral_congr_ae
                filter_upwards with t
                calc
                  Real.exp (-t * mass ^ 2) *
                      ∑ m : Fin d → Fin N,
                        Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) * c m
                    = Real.exp (-t * mass ^ 2) *
                        ∑ m : Fin d → Fin N,
                          Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
                            ((latticeFourierProductBasisFun N d m x) ^ 2 /
                              latticeFourierProductNormSq N d m) := by
                                simpa [c]
                  _ = Real.exp (-t * mass ^ 2) * latticeHeatKernelMatrix d N a t x x := by
                        have hdiag' :
                            ∑ m : Fin d → Fin N,
                              Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
                                ((latticeFourierProductBasisFun N d m x) ^ 2 /
                                  latticeFourierProductNormSq N d m) =
                            latticeHeatKernelMatrix d N a t x x := by
                              calc
                                ∑ m : Fin d → Fin N,
                                    Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
                                      ((latticeFourierProductBasisFun N d m x) ^ 2 /
                                        latticeFourierProductNormSq N d m)
                                  = ∑ m : Fin d → Fin N,
                                      Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
                                        (latticeFourierProductBasisFun N d m x) ^ 2 /
                                        latticeFourierProductNormSq N d m := by
                                          refine Finset.sum_congr rfl ?_
                                          intro m hm
                                          ring
                                _ = latticeHeatKernelMatrix d N a t x x := by
                                      rw [← latticeHeatKernel_diagonal_eq_dft_spectral
                                        (d := d) (N := N) (a := a) ha' t x]
                        rw [hdiag']
    _ = ∫ t in Set.Ioi T,
          Real.exp (-t * mass ^ 2) *
            ((1 / Fintype.card (FinLatticeSites d N) : ℝ) *
              ∑ m : Fin d → Fin N,
                Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) := by
                  apply integral_congr_ae
                  filter_upwards with t
                  rw [latticeHeatKernel_diagonal_eq_average
                    (d := d) (N := N) (a := a) ha' t x]
    _ = (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
          ∫ t in Set.Ioi T,
            Real.exp (-t * mass ^ 2) *
              ∑ m : Fin d → Fin N,
                Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) := by
                  calc
                    ∫ t in Set.Ioi T,
                        Real.exp (-t * mass ^ 2) *
                          ((1 / Fintype.card (FinLatticeSites d N) : ℝ) *
                            ∑ m : Fin d → Fin N,
                              Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)))
                      = ∫ t in Set.Ioi T,
                          (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
                            (Real.exp (-t * mass ^ 2) *
                              ∑ m : Fin d → Fin N,
                                Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) := by
                                  apply integral_congr_ae
                                  filter_upwards with t
                                  ring
                    _ = (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
                          ∫ t in Set.Ioi T,
                            Real.exp (-t * mass ^ 2) *
                              ∑ m : Fin d → Fin N,
                                Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) := by
                                  rw [integral_const_mul]
    _ = (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
          ∫ t in Set.Ioi T,
            ∑ m : Fin d → Fin N,
              Real.exp (-t * mass ^ 2) *
                Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) := by
                  apply congrArg ((1 / Fintype.card (FinLatticeSites d N) : ℝ) * ·)
                  apply integral_congr_ae
                  filter_upwards with t
                  symm
                  rw [Finset.mul_sum]
    _ = (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
          ∑ m : Fin d → Fin N,
            ∫ t in Set.Ioi T,
              Real.exp (-t * mass ^ 2) *
                Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) := by
                  rw [integral_finset_sum]
                  intro m hm
                  exact h_int_base m
    _ = (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
          ∑ m : Fin d → Fin N, canonicalSmoothWeight d N a mass T m := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro m hm
            rw [canonicalSmoothWeight_eq_integral_Ioi
              (d := d) (N := N) (a := a) (mass := mass) ha hmass T m]

private lemma roughWeight_family_sum_eq_average
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T) (x : FinLatticeSites d N) :
    ∑ m : Fin d → Fin N,
      canonicalRoughWeight d N a mass T m *
        (latticeFourierProductBasisFun N d m x) ^ 2 /
        latticeFourierProductNormSq N d m =
      (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
        ∑ m : Fin d → Fin N, canonicalRoughWeight d N a mass T m := by
  have ha' : a ≠ 0 := ne_of_gt ha
  let c : (Fin d → Fin N) → ℝ := fun m =>
    (latticeFourierProductBasisFun N d m x) ^ 2 /
      latticeFourierProductNormSq N d m
  have h_int_coeff :
      ∀ m : Fin d → Fin N,
        IntegrableOn (fun t : ℝ =>
          (Real.exp (-t * mass ^ 2) *
            Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) * c m) (Set.Icc 0 T) := by
    intro m
    have hcont : Continuous (fun t : ℝ =>
      (Real.exp (-t * mass ^ 2) *
        Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) * c m) := by
      fun_prop
    exact hcont.integrableOn_Icc
  have h_int_base :
      ∀ m : Fin d → Fin N,
        IntegrableOn (fun t : ℝ =>
          Real.exp (-t * mass ^ 2) *
            Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) (Set.Icc 0 T) := by
    intro m
    have hcont : Continuous (fun t : ℝ =>
      Real.exp (-t * mass ^ 2) *
        Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) := by
      fun_prop
    exact hcont.integrableOn_Icc
  have hstart :
      ∑ m : Fin d → Fin N,
        canonicalRoughWeight d N a mass T m *
          (latticeFourierProductBasisFun N d m x) ^ 2 /
          latticeFourierProductNormSq N d m =
      ∑ m : Fin d → Fin N, canonicalRoughWeight d N a mass T m * c m := by
        refine Finset.sum_congr rfl ?_
        intro m hm
        simp [c]
        ring
  rw [hstart]
  calc
    ∑ m : Fin d → Fin N, canonicalRoughWeight d N a mass T m * c m
      = ∑ m : Fin d → Fin N,
          ∫ t in Set.Icc 0 T,
            (Real.exp (-t * mass ^ 2) *
              Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) * c m := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              calc
                canonicalRoughWeight d N a mass T m * c m
                  = c m * canonicalRoughWeight d N a mass T m := by ring
                _ = c m *
                    ∫ t in Set.Icc 0 T,
                      Real.exp (-t * mass ^ 2) *
                        Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) := by
                          rw [canonicalRoughWeight_eq_integral_Icc
                            (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT m]
                _ = ∫ t in Set.Icc 0 T,
                    c m *
                      (Real.exp (-t * mass ^ 2) *
                        Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) := by
                          rw [integral_const_mul]
                _ = ∫ t in Set.Icc 0 T,
                    (Real.exp (-t * mass ^ 2) *
                      Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) * c m := by
                          apply integral_congr_ae
                          filter_upwards with t
                          ring
    _ = ∫ t in Set.Icc 0 T,
          ∑ m : Fin d → Fin N,
            (Real.exp (-t * mass ^ 2) *
              Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) * c m := by
                rw [integral_finset_sum]
                intro m hm
                exact h_int_coeff m
    _ = ∫ t in Set.Icc 0 T,
          Real.exp (-t * mass ^ 2) *
            ∑ m : Fin d → Fin N,
              Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) * c m := by
                apply integral_congr_ae
                filter_upwards with t
                symm
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl ?_
                intro m hm
                ring
    _ = ∫ t in Set.Icc 0 T,
          Real.exp (-t * mass ^ 2) * latticeHeatKernelMatrix d N a t x x := by
                apply integral_congr_ae
                filter_upwards with t
                calc
                  Real.exp (-t * mass ^ 2) *
                      ∑ m : Fin d → Fin N,
                        Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) * c m
                    = Real.exp (-t * mass ^ 2) *
                        ∑ m : Fin d → Fin N,
                          Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
                            ((latticeFourierProductBasisFun N d m x) ^ 2 /
                              latticeFourierProductNormSq N d m) := by
                                simpa [c]
                  _ = Real.exp (-t * mass ^ 2) * latticeHeatKernelMatrix d N a t x x := by
                        have hdiag' :
                            ∑ m : Fin d → Fin N,
                              Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
                                ((latticeFourierProductBasisFun N d m x) ^ 2 /
                                  latticeFourierProductNormSq N d m) =
                            latticeHeatKernelMatrix d N a t x x := by
                              calc
                                ∑ m : Fin d → Fin N,
                                    Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
                                      ((latticeFourierProductBasisFun N d m x) ^ 2 /
                                        latticeFourierProductNormSq N d m)
                                  = ∑ m : Fin d → Fin N,
                                      Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
                                        (latticeFourierProductBasisFun N d m x) ^ 2 /
                                        latticeFourierProductNormSq N d m := by
                                          refine Finset.sum_congr rfl ?_
                                          intro m hm
                                          ring
                                _ = latticeHeatKernelMatrix d N a t x x := by
                                      rw [← latticeHeatKernel_diagonal_eq_dft_spectral
                                        (d := d) (N := N) (a := a) ha' t x]
                        rw [hdiag']
    _ = ∫ t in Set.Icc 0 T,
          Real.exp (-t * mass ^ 2) *
            ((1 / Fintype.card (FinLatticeSites d N) : ℝ) *
              ∑ m : Fin d → Fin N,
                Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) := by
                  apply integral_congr_ae
                  filter_upwards with t
                  rw [latticeHeatKernel_diagonal_eq_average
                    (d := d) (N := N) (a := a) ha' t x]
    _ = (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
          ∫ t in Set.Icc 0 T,
            Real.exp (-t * mass ^ 2) *
              ∑ m : Fin d → Fin N,
                Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) := by
                  calc
                    ∫ t in Set.Icc 0 T,
                        Real.exp (-t * mass ^ 2) *
                          ((1 / Fintype.card (FinLatticeSites d N) : ℝ) *
                            ∑ m : Fin d → Fin N,
                              Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)))
                      = ∫ t in Set.Icc 0 T,
                          (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
                            (Real.exp (-t * mass ^ 2) *
                              ∑ m : Fin d → Fin N,
                                Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) := by
                                  apply integral_congr_ae
                                  filter_upwards with t
                                  ring
                    _ = (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
                          ∫ t in Set.Icc 0 T,
                            Real.exp (-t * mass ^ 2) *
                              ∑ m : Fin d → Fin N,
                                Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) := by
                                  rw [integral_const_mul]
    _ = (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
          ∫ t in Set.Icc 0 T,
            ∑ m : Fin d → Fin N,
              Real.exp (-t * mass ^ 2) *
                Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) := by
                  apply congrArg ((1 / Fintype.card (FinLatticeSites d N) : ℝ) * ·)
                  apply integral_congr_ae
                  filter_upwards with t
                  symm
                  rw [Finset.mul_sum]
    _ = (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
          ∑ m : Fin d → Fin N,
            ∫ t in Set.Icc 0 T,
              Real.exp (-t * mass ^ 2) *
                Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) := by
                  rw [integral_finset_sum]
                  intro m hm
                  exact h_int_base m
    _ = (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
          ∑ m : Fin d → Fin N, canonicalRoughWeight d N a mass T m := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro m hm
            rw [canonicalRoughWeight_eq_integral_Icc
              (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT m]

theorem heatKernel_diagonal_mass_weighted_eq_eigenvalue_average
    (ha : 0 < a) (mass t : ℝ) (x : FinLatticeSites d N) :
    Real.exp (-t * mass ^ 2) * latticeHeatKernelMatrix d N a t x x =
      (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
        ∑ m : Fin d → Fin N,
          Real.exp (-t * canonicalEigenvalue d N a mass m) := by
  have ha' : a ≠ 0 := ne_of_gt ha
  calc
    Real.exp (-t * mass ^ 2) * latticeHeatKernelMatrix d N a t x x
      = Real.exp (-t * mass ^ 2) *
          ((1 / Fintype.card (FinLatticeSites d N) : ℝ) *
            ∑ m : Fin d → Fin N,
              Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) := by
                rw [latticeHeatKernel_diagonal_eq_average
                  (d := d) (N := N) (a := a) ha' t x]
    _ = (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
          ∑ m : Fin d → Fin N,
            Real.exp (-t * mass ^ 2) *
              Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) := by
                calc
                  Real.exp (-t * mass ^ 2) *
                      ((1 / Fintype.card (FinLatticeSites d N) : ℝ) *
                        ∑ m : Fin d → Fin N,
                          Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)))
                    = (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
                        (Real.exp (-t * mass ^ 2) *
                          ∑ m : Fin d → Fin N,
                            Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) := by
                              ring
                  _ = (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
                        ∑ m : Fin d → Fin N,
                          Real.exp (-t * mass ^ 2) *
                            Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) := by
                              rw [Finset.mul_sum]
    _ = (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
          ∑ m : Fin d → Fin N,
            Real.exp (-t * canonicalEigenvalue d N a mass m) := by
                congr 1
                refine Finset.sum_congr rfl ?_
                intro m hm
                unfold canonicalEigenvalue
                rw [← Real.exp_add]
                congr 1
                ring

private lemma latticeFourierProductBasisFun_zero
    (x : FinLatticeSites d N) :
    latticeFourierProductBasisFun N d (0 : Fin d → Fin N) x =
      (1 / Real.sqrt (N : ℝ)) ^ d := by
  simp [latticeFourierProductBasisFun, latticeFourierBasisFun]

theorem heatKernel_row_sum_eq_one
    (ha : 0 < a) (t : ℝ) (x : FinLatticeSites d N) :
    ∑ y : FinLatticeSites d N, latticeHeatKernelMatrix d N a t x y = 1 := by
  let c : ℝ := (1 / Real.sqrt (N : ℝ)) ^ d
  have hc_pos : 0 < c := by
    have hN_pos : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
    dsimp [c]
    positivity
  have hconst :
      ∀ y : FinLatticeSites d N,
        latticeFourierProductBasisFun N d (0 : Fin d → Fin N) y = c := by
    intro y
    simp [c, latticeFourierProductBasisFun_zero]
  have hzero_mode :
      (latticeHeatKernelMatrix d N a t).mulVec
          (latticeFourierProductBasisFun N d (0 : Fin d → Fin N)) =
        latticeFourierProductBasisFun N d (0 : Fin d → Fin N) := by
    have ha' : a ≠ 0 := ne_of_gt ha
    have hspec :
        (latticeHeatKernelMatrix d N a t).mulVec
            (latticeFourierProductBasisFun N d (0 : Fin d → Fin N)) =
          Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a ((0 : Fin d → Fin N) i)) •
            latticeFourierProductBasisFun N d (0 : Fin d → Fin N) := by
      apply Matrix.IsHermitian.mulVec_exp_of_eigenvector
        (hM := negLaplacianMatrix_isHermitian d N a) (t := t)
      ext z
      rw [negLaplacianMatrix]
      rw [← massOperator_eq_matrix_mulVec (d := d) (N := N) (a := a) (mass := 0)
        (f := latticeFourierProductBasisFun N d (0 : Fin d → Fin N)) z]
      simpa using
        (massOperator_product_eigenvector_family (N := N) d a 0 ha'
          (0 : Fin d → Fin N) z)
    simpa [latticeEigenvalue1d_zero] using hspec
  have hx := congr_fun hzero_mode x
  rw [Matrix.mulVec, dotProduct] at hx
  have hsum :
      ∑ y : FinLatticeSites d N,
          latticeHeatKernelMatrix d N a t x y *
            latticeFourierProductBasisFun N d (0 : Fin d → Fin N) y =
        c * ∑ y : FinLatticeSites d N, latticeHeatKernelMatrix d N a t x y := by
    simp_rw [hconst]
    calc
      ∑ y : FinLatticeSites d N, latticeHeatKernelMatrix d N a t x y * c
        = ∑ y : FinLatticeSites d N, c * latticeHeatKernelMatrix d N a t x y := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            ring
      _ = c * ∑ y : FinLatticeSites d N, latticeHeatKernelMatrix d N a t x y := by
            rw [Finset.mul_sum]
  rw [hconst x, hsum] at hx
  have hx' : c * ∑ y : FinLatticeSites d N, latticeHeatKernelMatrix d N a t x y = c * 1 := by
    simpa using hx
  exact mul_left_cancel₀ (ne_of_gt hc_pos) hx'

theorem heatKernel_row_pairing_eq_diagonal
    (a s t : ℝ) (x : FinLatticeSites d N) :
    ∑ y : FinLatticeSites d N,
      latticeHeatKernelMatrix d N a s x y *
        latticeHeatKernelMatrix d N a t x y =
      latticeHeatKernelMatrix d N a (s + t) x x := by
  have hsymm :
      ∀ y : FinLatticeSites d N,
        latticeHeatKernelMatrix d N a t x y =
          latticeHeatKernelMatrix d N a t y x := by
    intro y
    have hT :
        Matrix.transpose (latticeHeatKernelMatrix d N a t) = latticeHeatKernelMatrix d N a t := by
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
      exact (latticeHeatKernelMatrix_isHermitian d N a t).eq
    have hentry := congr_fun (congr_fun hT y) x
    simpa [Matrix.transpose_apply] using hentry
  calc
    ∑ y : FinLatticeSites d N,
        latticeHeatKernelMatrix d N a s x y *
          latticeHeatKernelMatrix d N a t x y
      = ∑ y : FinLatticeSites d N,
          latticeHeatKernelMatrix d N a s x y *
            latticeHeatKernelMatrix d N a t y x := by
              refine Finset.sum_congr rfl ?_
              intro y hy
              rw [hsymm y]
    _ = (latticeHeatKernelMatrix d N a s * latticeHeatKernelMatrix d N a t) x x := by
          simp [Matrix.mul_apply]
    _ = latticeHeatKernelMatrix d N a (s + t) x x := by
          rw [← latticeHeatKernelMatrix_semigroup (d := d) (N := N) a s t]

private lemma smoothWickConstant_eq_family_average
    (T : ℝ) :
    smoothWickConstant d N a mass T =
      (a ^ d : ℝ)⁻¹ *
        ((1 / Fintype.card (FinLatticeSites d N) : ℝ) *
          ∑ m : Fin d → Fin N, canonicalSmoothWeight d N a mass T m) := by
  unfold smoothWickConstant canonicalSmoothWeight smoothCovEigenvalue canonicalEigenvalue
  rw [← Fin.sum_univ_eq_sum_range]
  congr 2
  exact sum_latticeEigenvalue_eq_sum_latticeEigenvalue1d_family
    (N := N) d a mass (fun t : ℝ => Real.exp (-T * t) / t)

private lemma roughWickConstant_eq_family_average
    (T : ℝ) :
    roughWickConstant d N a mass T =
      (a ^ d : ℝ)⁻¹ *
        ((1 / Fintype.card (FinLatticeSites d N) : ℝ) *
          ∑ m : Fin d → Fin N, canonicalRoughWeight d N a mass T m) := by
  unfold roughWickConstant canonicalRoughWeight roughCovEigenvalue canonicalEigenvalue
  rw [← Fin.sum_univ_eq_sum_range]
  congr 2
  exact sum_latticeEigenvalue_eq_sum_latticeEigenvalue1d_family
    (N := N) d a mass (fun t : ℝ => (1 - Real.exp (-T * t)) / t)

noncomputable def canonicalSmoothCovariance
    (T : ℝ) (x y : FinLatticeSites d N) : ℝ :=
  (a^d : ℝ)⁻¹ *
    ∑ m : Fin d → Fin N,
      canonicalSmoothWeight d N a mass T m *
        latticeFourierProductBasisFun N d m x *
        latticeFourierProductBasisFun N d m y /
        latticeFourierProductNormSq N d m

noncomputable def canonicalRoughCovariance
    (T : ℝ) (x y : FinLatticeSites d N) : ℝ :=
  (a^d : ℝ)⁻¹ *
    ∑ m : Fin d → Fin N,
      canonicalRoughWeight d N a mass T m *
        latticeFourierProductBasisFun N d m x *
        latticeFourierProductBasisFun N d m y /
        latticeFourierProductNormSq N d m

noncomputable def canonicalSmoothFieldFunction_self_moment_diag
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (x : FinLatticeSites d N) : ℝ :=
  ∫ η : CanonicalJoint d N,
    canonicalSmoothFieldFunction d N a mass T η x *
      canonicalSmoothFieldFunction d N a mass T η x
    ∂(canonicalJointMeasure d N)

noncomputable def canonicalRoughFieldFunction_self_moment_diag
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (x : FinLatticeSites d N) : ℝ :=
  ∫ η : CanonicalJoint d N,
    canonicalRoughFieldFunction d N a mass T η x *
      canonicalRoughFieldFunction d N a mass T η x
    ∂(canonicalJointMeasure d N)

theorem canonicalSmoothFieldFunction_self_moment_eq_smoothWickConstant
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (x : FinLatticeSites d N) :
    canonicalSmoothFieldFunction_self_moment_diag d N a mass ha hmass T hT x =
      smoothWickConstant d N a mass T := by
  unfold canonicalSmoothFieldFunction_self_moment_diag
  rw [canonicalSmoothFieldFunction_self_moment
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x x]
  rw [smoothWickConstant_eq_family_average (d := d) (N := N) (a := a) (mass := mass) T]
  congr 1
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
    smoothWeight_family_sum_eq_average (d := d) (N := N) (a := a) (mass := mass) ha hmass T x

theorem canonicalSmoothFieldFunction_self_moment_const
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (x : FinLatticeSites d N) :
    canonicalSmoothFieldFunction_self_moment_diag d N a mass ha hmass T hT x =
      canonicalSmoothFieldFunction_self_moment_diag d N a mass ha hmass T hT 0 := by
  rw [canonicalSmoothFieldFunction_self_moment_eq_smoothWickConstant
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x]
  rw [canonicalSmoothFieldFunction_self_moment_eq_smoothWickConstant
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT 0]

theorem canonicalRoughFieldFunction_self_moment_eq_roughWickConstant
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (x : FinLatticeSites d N) :
    canonicalRoughFieldFunction_self_moment_diag d N a mass ha hmass T hT x =
      roughWickConstant d N a mass T := by
  unfold canonicalRoughFieldFunction_self_moment_diag
  rw [canonicalRoughFieldFunction_self_moment
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x x]
  rw [roughWickConstant_eq_family_average (d := d) (N := N) (a := a) (mass := mass) T]
  congr 1
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
    roughWeight_family_sum_eq_average
      (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x

theorem canonicalRoughFieldFunction_self_moment_const
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (x : FinLatticeSites d N) :
    canonicalRoughFieldFunction_self_moment_diag d N a mass ha hmass T hT x =
      canonicalRoughFieldFunction_self_moment_diag d N a mass ha hmass T hT 0 := by
  rw [canonicalRoughFieldFunction_self_moment_eq_roughWickConstant
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x]
  rw [canonicalRoughFieldFunction_self_moment_eq_roughWickConstant
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT 0]

theorem canonicalSmoothFieldFunction_covariance_eq
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (x y : FinLatticeSites d N) :
    ∫ η : CanonicalJoint d N,
      canonicalSmoothFieldFunction d N a mass T η x *
        canonicalSmoothFieldFunction d N a mass T η y
      ∂(canonicalJointMeasure d N) =
    canonicalSmoothCovariance d N a mass T x y := by
  unfold canonicalSmoothCovariance
  exact canonicalSmoothFieldFunction_self_moment
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x y

theorem canonicalRoughFieldFunction_covariance_eq
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (x y : FinLatticeSites d N) :
    ∫ η : CanonicalJoint d N,
      canonicalRoughFieldFunction d N a mass T η x *
        canonicalRoughFieldFunction d N a mass T η y
      ∂(canonicalJointMeasure d N) =
    canonicalRoughCovariance d N a mass T x y := by
  unfold canonicalRoughCovariance
  exact canonicalRoughFieldFunction_self_moment
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x y

theorem canonicalRoughCovariance_eq_integral_Icc_heatKernel
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (x y : FinLatticeSites d N) :
    canonicalRoughCovariance d N a mass T x y =
      (a ^ d : ℝ)⁻¹ *
        ∫ t in Set.Icc 0 T,
          Real.exp (-t * mass ^ 2) *
            latticeHeatKernelMatrix d N a t x y := by
  have ha' : a ≠ 0 := ne_of_gt ha
  let c : (Fin d → Fin N) → ℝ := fun m =>
    latticeFourierProductBasisFun N d m x *
      latticeFourierProductBasisFun N d m y /
      latticeFourierProductNormSq N d m
  have h_int_coeff :
      ∀ m : Fin d → Fin N,
        IntegrableOn (fun t : ℝ =>
          (Real.exp (-t * mass ^ 2) *
            Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) * c m) (Set.Icc 0 T) := by
    intro m
    have hcont : Continuous (fun t : ℝ =>
      (Real.exp (-t * mass ^ 2) *
        Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) * c m) := by
      fun_prop
    exact hcont.integrableOn_Icc
  have h_int_base :
      ∀ m : Fin d → Fin N,
        IntegrableOn (fun t : ℝ =>
          Real.exp (-t * mass ^ 2) *
            Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) (Set.Icc 0 T) := by
    intro m
    have hcont : Continuous (fun t : ℝ =>
      Real.exp (-t * mass ^ 2) *
        Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) := by
      fun_prop
    exact hcont.integrableOn_Icc
  have hstart :
      ∑ m : Fin d → Fin N,
        canonicalRoughWeight d N a mass T m *
          latticeFourierProductBasisFun N d m x *
          latticeFourierProductBasisFun N d m y /
          latticeFourierProductNormSq N d m =
      ∑ m : Fin d → Fin N, canonicalRoughWeight d N a mass T m * c m := by
        refine Finset.sum_congr rfl ?_
        intro m hm
        simp [c]
        ring
  unfold canonicalRoughCovariance
  rw [hstart]
  calc
    (a ^ d : ℝ)⁻¹ * ∑ m : Fin d → Fin N, canonicalRoughWeight d N a mass T m * c m
      = (a ^ d : ℝ)⁻¹ *
          ∑ m : Fin d → Fin N,
            ∫ t in Set.Icc 0 T,
              (Real.exp (-t * mass ^ 2) *
                Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) * c m := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro m hm
              calc
                canonicalRoughWeight d N a mass T m * c m
                  = c m * canonicalRoughWeight d N a mass T m := by ring
                _ = c m *
                    ∫ t in Set.Icc 0 T,
                      Real.exp (-t * mass ^ 2) *
                        Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) := by
                          rw [canonicalRoughWeight_eq_integral_Icc
                            (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT m]
                _ = ∫ t in Set.Icc 0 T,
                    c m *
                      (Real.exp (-t * mass ^ 2) *
                        Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) := by
                          rw [integral_const_mul]
                _ = ∫ t in Set.Icc 0 T,
                    (Real.exp (-t * mass ^ 2) *
                      Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) * c m := by
                          apply integral_congr_ae
                          filter_upwards with t
                          ring
    _ = (a ^ d : ℝ)⁻¹ *
          ∫ t in Set.Icc 0 T,
            ∑ m : Fin d → Fin N,
              (Real.exp (-t * mass ^ 2) *
                Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) * c m := by
                congr 1
                symm
                rw [integral_finset_sum]
                intro m hm
                exact h_int_coeff m
    _ = (a ^ d : ℝ)⁻¹ *
          ∫ t in Set.Icc 0 T,
            Real.exp (-t * mass ^ 2) *
              ∑ m : Fin d → Fin N,
                Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) * c m := by
                  congr 1
                  apply integral_congr_ae
                  filter_upwards with t
                  symm
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl ?_
                  intro m hm
                  ring
    _ = (a ^ d : ℝ)⁻¹ *
          ∫ t in Set.Icc 0 T,
            Real.exp (-t * mass ^ 2) * latticeHeatKernelMatrix d N a t x y := by
                  congr 1
                  apply integral_congr_ae
                  filter_upwards with t
                  calc
                    Real.exp (-t * mass ^ 2) *
                        ∑ m : Fin d → Fin N,
                          Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) * c m
                      = Real.exp (-t * mass ^ 2) *
                          ∑ m : Fin d → Fin N,
                            Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
                              (latticeFourierProductBasisFun N d m x *
                                latticeFourierProductBasisFun N d m y /
                                latticeFourierProductNormSq N d m) := by
                                  simpa [c]
                    _ = Real.exp (-t * mass ^ 2) *
                          ∑ m : Fin d → Fin N,
                            Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
                              latticeFourierProductBasisFun N d m x *
                              latticeFourierProductBasisFun N d m y /
                              latticeFourierProductNormSq N d m := by
                                congr 1
                                refine Finset.sum_congr rfl ?_
                                intro m hm
                                ring
                    _ = Real.exp (-t * mass ^ 2) * latticeHeatKernelMatrix d N a t x y := by
                          rw [latticeHeatKernel_entry_eq_dft_spectral
                            (d := d) (N := N) (a := a) ha' t x y]

theorem canonicalRoughCovariance_sq_row_sum_eq_double_integral
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (x : FinLatticeSites d N) :
    a ^ d * ∑ y : FinLatticeSites d N,
      (canonicalRoughCovariance d N a mass T x y) ^ 2 =
      (a ^ d : ℝ)⁻¹ *
        ∫ s in Set.Icc 0 T,
          ∫ t in Set.Icc 0 T,
            Real.exp (-(s + t) * mass ^ 2) *
              latticeHeatKernelMatrix d N a (s + t) x x := by
  let I : Set ℝ := Set.Icc 0 T
  let F : FinLatticeSites d N → ℝ → ℝ := fun y s =>
    Real.exp (-s * mass ^ 2) * latticeHeatKernelMatrix d N a s x y
  have ha_d_pos : (0 : ℝ) < a ^ d := pow_pos ha d
  have hCov :
      ∀ y : FinLatticeSites d N,
        canonicalRoughCovariance d N a mass T x y =
          (a ^ d : ℝ)⁻¹ * ∫ s in I, F y s := by
    intro y
    simpa [I, F] using canonicalRoughCovariance_eq_integral_Icc_heatKernel
      (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x y
  have hprod :
      ∀ y : FinLatticeSites d N,
        (∫ s in I, F y s) * ∫ t in I, F y t =
          ∫ p in I ×ˢ I, F y p.1 * F y p.2 ∂(volume.prod volume) := by
    intro y
    symm
    simpa [I, F] using
      (MeasureTheory.setIntegral_prod_mul (μ := volume) (ν := volume) (f := F y) (g := F y) I I)
  have hF_int :
      ∀ y : FinLatticeSites d N,
        Integrable (F y) (volume.restrict I) := by
    intro y
    have ha' : a ≠ 0 := ne_of_gt ha
    let c : (Fin d → Fin N) → ℝ := fun m =>
      latticeFourierProductBasisFun N d m x *
        latticeFourierProductBasisFun N d m y /
        latticeFourierProductNormSq N d m
    have h_int_coeff :
        ∀ m : Fin d → Fin N,
          Integrable
            (fun t : ℝ =>
              (Real.exp (-t * mass ^ 2) *
                Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) * c m)
            (volume.restrict I) := by
      intro m
      have hcont : Continuous (fun t : ℝ =>
        (Real.exp (-t * mass ^ 2) *
          Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) * c m) := by
        fun_prop
      simpa [I] using hcont.integrableOn_Icc
    have hsum :
        (fun t : ℝ => F y t) =
          fun t : ℝ =>
            ∑ m : Fin d → Fin N,
              (Real.exp (-t * mass ^ 2) *
                Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) * c m := by
      funext t
      dsimp [F]
      calc
        Real.exp (-t * mass ^ 2) * latticeHeatKernelMatrix d N a t x y
          = Real.exp (-t * mass ^ 2) *
              ∑ m : Fin d → Fin N,
                Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
                  latticeFourierProductBasisFun N d m x *
                  latticeFourierProductBasisFun N d m y /
                  latticeFourierProductNormSq N d m := by
                    rw [latticeHeatKernel_entry_eq_dft_spectral
                      (d := d) (N := N) (a := a) ha' t x y]
        _ = Real.exp (-t * mass ^ 2) *
              ∑ m : Fin d → Fin N,
                Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) * c m := by
                    congr 1
                    refine Finset.sum_congr rfl ?_
                    intro m hm
                    simp [c]
                    ring
        _ = ∑ m : Fin d → Fin N,
              (Real.exp (-t * mass ^ 2) *
                Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) * c m := by
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl ?_
                    intro m hm
                    ring
    have hsum_int :
        Integrable
          (fun t : ℝ =>
            ∑ m : Fin d → Fin N,
              (Real.exp (-t * mass ^ 2) *
                Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) * c m)
          (volume.restrict I) :=
      integrable_finset_sum _ (fun m _ => h_int_coeff m)
    simpa [hsum] using hsum_int
  have hprod_int :
      ∀ y : FinLatticeSites d N,
        Integrable
          (fun p : ℝ × ℝ => F y p.1 * F y p.2)
          ((volume.restrict I).prod (volume.restrict I)) := by
    intro y
    exact (hF_int y).mul_prod (hF_int y)
  have hsum_int :
      Integrable
        (fun p : ℝ × ℝ => ∑ y : FinLatticeSites d N, F y p.1 * F y p.2)
        ((volume.restrict I).prod (volume.restrict I)) := by
    exact integrable_finset_sum _ (fun y _ => hprod_int y)
  have hcollapse :
      (fun p : ℝ × ℝ => ∑ y : FinLatticeSites d N, F y p.1 * F y p.2)
        =ᵐ[((volume.restrict I).prod (volume.restrict I))]
      (fun p : ℝ × ℝ =>
        Real.exp (-(p.1 + p.2) * mass ^ 2) *
          latticeHeatKernelMatrix d N a (p.1 + p.2) x x) := by
    filter_upwards [] with p
    calc
      ∑ y : FinLatticeSites d N, F y p.1 * F y p.2
        = ∑ y : FinLatticeSites d N,
            (Real.exp (-p.1 * mass ^ 2) * Real.exp (-p.2 * mass ^ 2)) *
              (latticeHeatKernelMatrix d N a p.1 x y *
                latticeHeatKernelMatrix d N a p.2 x y) := by
                  refine Finset.sum_congr rfl ?_
                  intro y hy
                  simp [F]
                  ring
      _ = (Real.exp (-p.1 * mass ^ 2) * Real.exp (-p.2 * mass ^ 2)) *
            ∑ y : FinLatticeSites d N,
              latticeHeatKernelMatrix d N a p.1 x y *
                latticeHeatKernelMatrix d N a p.2 x y := by
                  rw [Finset.mul_sum]
      _ = (Real.exp (-p.1 * mass ^ 2) * Real.exp (-p.2 * mass ^ 2)) *
            latticeHeatKernelMatrix d N a (p.1 + p.2) x x := by
                  rw [heatKernel_row_pairing_eq_diagonal
                    (d := d) (N := N) a p.1 p.2 x]
      _ = Real.exp (-(p.1 + p.2) * mass ^ 2) *
            latticeHeatKernelMatrix d N a (p.1 + p.2) x x := by
                  rw [← Real.exp_add]
                  congr 1
                  ring_nf
  have hdiag_int :
      Integrable
        (fun p : ℝ × ℝ =>
          Real.exp (-(p.1 + p.2) * mass ^ 2) *
            latticeHeatKernelMatrix d N a (p.1 + p.2) x x)
        ((volume.restrict I).prod (volume.restrict I)) := by
    exact hsum_int.congr hcollapse
  calc
    a ^ d * ∑ y : FinLatticeSites d N,
        (canonicalRoughCovariance d N a mass T x y) ^ 2
      = ∑ y : FinLatticeSites d N,
          a ^ d * (canonicalRoughCovariance d N a mass T x y) ^ 2 := by
            rw [Finset.mul_sum]
    _ = ∑ y : FinLatticeSites d N,
          (a ^ d : ℝ)⁻¹ * ((∫ s in I, F y s) * ∫ t in I, F y t) := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            rw [hCov y]
            field_simp [ne_of_gt ha_d_pos]
    _ = (a ^ d : ℝ)⁻¹ *
          ∑ y : FinLatticeSites d N, ((∫ s in I, F y s) * ∫ t in I, F y t) := by
            rw [← Finset.mul_sum]
    _ = (a ^ d : ℝ)⁻¹ *
          ∑ y : FinLatticeSites d N,
            ∫ p in I ×ˢ I, F y p.1 * F y p.2 ∂(volume.prod volume) := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro y hy
              rw [hprod y]
    _ = (a ^ d : ℝ)⁻¹ *
          ∫ p,
            ∑ y : FinLatticeSites d N, F y p.1 * F y p.2
          ∂((volume.restrict I).prod (volume.restrict I)) := by
              congr 1
              rw [← Measure.prod_restrict I I]
              symm
              rw [MeasureTheory.integral_finset_sum]
              intro y hy
              exact hprod_int y
    _ = (a ^ d : ℝ)⁻¹ *
          ∫ p,
            Real.exp (-(p.1 + p.2) * mass ^ 2) *
              latticeHeatKernelMatrix d N a (p.1 + p.2) x x
          ∂((volume.restrict I).prod (volume.restrict I)) := by
              congr 1
              exact MeasureTheory.integral_congr_ae hcollapse
    _ = (a ^ d : ℝ)⁻¹ *
          ∫ s in I,
            ∫ t in I,
              Real.exp (-(s + t) * mass ^ 2) *
                latticeHeatKernelMatrix d N a (s + t) x x := by
                  congr 1
                  exact MeasureTheory.integral_prod _ hdiag_int

private lemma integrable_pow_gaussianReal_one (k : ℕ) :
    MeasureTheory.Integrable (fun x : ℝ => x ^ k)
      (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)) := by
  cases k with
  | zero =>
      simp only [pow_zero]
      exact MeasureTheory.integrable_const (1 : ℝ)
  | succ k =>
      have h_mem0 :=
        ProbabilityTheory.memLp_id_gaussianReal
          (μ := (0 : ℝ)) (v := (1 : NNReal)) (p := (Nat.succ k : NNReal))
      have h_mem : MeasureTheory.MemLp (fun x : ℝ => x) (Nat.succ k)
          (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)) := by
        simpa using h_mem0
      have h_norm : MeasureTheory.Integrable (fun x : ℝ => ‖x‖ ^ Nat.succ k)
          (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)) := by
        simpa using h_mem.integrable_norm_pow'
      have h_meas :
          MeasureTheory.AEStronglyMeasurable (fun x : ℝ => x ^ Nat.succ k)
            (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)) :=
        (continuous_id.pow _).aestronglyMeasurable
      rw [← MeasureTheory.integrable_norm_iff h_meas]
      simpa [norm_pow] using h_norm

private lemma integrable_polynomial_gaussianReal_one (p : Polynomial ℝ) :
    MeasureTheory.Integrable (fun x : ℝ => p.eval x)
      (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)) := by
  have h_eval :
      (fun x : ℝ => p.eval x) =
        (fun x => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i) := by
    ext x
    rw [Polynomial.eval_eq_sum_range]
  rw [h_eval]
  exact MeasureTheory.integrable_finset_sum _ fun i hi =>
    (integrable_pow_gaussianReal_one i).const_mul (p.coeff i)

private lemma integrable_wickMonomial_mul_gaussianReal_one (m n : ℕ) :
    MeasureTheory.Integrable (fun x : ℝ => wickMonomial m 1 x * wickMonomial n 1 x)
      (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)) := by
  have h_eq :
      (fun x : ℝ => wickMonomial m 1 x * wickMonomial n 1 x) =
        fun x => ((((Polynomial.hermite m).map (Int.castRingHom ℝ)) *
          ((Polynomial.hermite n).map (Int.castRingHom ℝ))).eval x) := by
    funext x
    have hm :
        wickMonomial m 1 x =
          (((Polynomial.hermite m).map (Int.castRingHom ℝ)).eval x) := by
      simpa using (wickMonomial_eq_hermite m 1 (by norm_num : (0 : ℝ) < 1) x)
    have hn :
        wickMonomial n 1 x =
          (((Polynomial.hermite n).map (Int.castRingHom ℝ)).eval x) := by
      simpa using (wickMonomial_eq_hermite n 1 (by norm_num : (0 : ℝ) < 1) x)
    rw [hm, hn]
    simp [Polynomial.eval_mul]
  rw [h_eq]
  exact integrable_polynomial_gaussianReal_one
    (((Polynomial.hermite m).map (Int.castRingHom ℝ)) *
      ((Polynomial.hermite n).map (Int.castRingHom ℝ)))

private theorem wickMonomial_eq_root : ∀ (n : ℕ) (c x : ℝ),
    wickMonomial n c x = _root_.wickMonomial n c x
  | 0, _, _ => rfl
  | 1, _, _ => rfl
  | n + 2, c, x => by
      simp only [Pphi2.wickMonomial_succ_succ, _root_.wickMonomial_succ_succ]
      rw [wickMonomial_eq_root (n + 1), wickMonomial_eq_root n]

def canonicalSmoothGamma (d N : ℕ) [NeZero N]
    (a mass T : ℝ) (x : FinLatticeSites d N) (m : Fin d → Fin N) : ℝ :=
  (Real.sqrt (a ^ d))⁻¹ * canonicalSmoothModeCoeff d N a mass T x m

def canonicalRoughGamma (d N : ℕ) [NeZero N]
    (a mass T : ℝ) (x : FinLatticeSites d N) (m : Fin d → Fin N) : ℝ :=
  (Real.sqrt (a ^ d))⁻¹ * canonicalRoughModeCoeff d N a mass T x m

/-- The smooth field slice is the linear combination of first-factor standard
Gaussian coordinates with coefficients `canonicalSmoothGamma`. -/
theorem canonicalSmoothFieldFunctionOfFst_eq_sum_gamma
    (T : ℝ) (η_S : (Fin d → Fin N) → ℝ) (x : FinLatticeSites d N) :
    canonicalSmoothFieldFunctionOfFst d N a mass T η_S x =
      ∑ m : Fin d → Fin N, canonicalSmoothGamma d N a mass T x m * η_S m := by
  unfold canonicalSmoothFieldFunctionOfFst canonicalSmoothGamma
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro m hm
  ring

/-- The rough field slice is the linear combination of second-factor standard
Gaussian coordinates with coefficients `canonicalRoughGamma`. -/
theorem canonicalRoughFieldFunctionOfSnd_eq_sum_gamma
    (T : ℝ) (η_R : (Fin d → Fin N) → ℝ) (x : FinLatticeSites d N) :
    canonicalRoughFieldFunctionOfSnd d N a mass T η_R x =
      ∑ m : Fin d → Fin N, canonicalRoughGamma d N a mass T x m * η_R m := by
  unfold canonicalRoughFieldFunctionOfSnd canonicalRoughGamma
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro m hm
  ring

private lemma canonicalSmoothGamma_sq_sum_eq_wickConstant
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (x : FinLatticeSites d N) :
    ∑ m : Fin d → Fin N, (canonicalSmoothGamma d N a mass T x m) ^ 2 =
      smoothWickConstant d N a mass T := by
  rw [← canonicalSmoothFieldFunction_self_moment_eq_smoothWickConstant
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x]
  unfold canonicalSmoothFieldFunction_self_moment_diag
  rw [canonicalSmoothFieldFunction_self_moment
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x x]
  have ha_d_pos : (0 : ℝ) < a ^ d := pow_pos ha d
  calc
    ∑ m : Fin d → Fin N, (canonicalSmoothGamma d N a mass T x m) ^ 2
      = ∑ m : Fin d → Fin N,
          (a ^ d : ℝ)⁻¹ *
            (canonicalSmoothWeight d N a mass T m *
              latticeFourierProductBasisFun N d m x *
              latticeFourierProductBasisFun N d m x /
              latticeFourierProductNormSq N d m) := by
                refine Finset.sum_congr rfl ?_
                intro m hm
                have hC :
                    0 ≤ canonicalSmoothWeight d N a mass T m /
                      latticeFourierProductNormSq N d m := by
                  apply div_nonneg
                  · exact canonicalSmoothWeight_nonneg
                      (d := d) (N := N) (a := a) (mass := mass) ha hmass T m
                  · exact (latticeFourierProductNormSq_pos (N := N) d m).le
                have h_sq :
                    Real.sqrt
                        (canonicalSmoothWeight d N a mass T m /
                          latticeFourierProductNormSq N d m) *
                      Real.sqrt
                        (canonicalSmoothWeight d N a mass T m /
                          latticeFourierProductNormSq N d m) =
                    canonicalSmoothWeight d N a mass T m /
                      latticeFourierProductNormSq N d m :=
                  Real.mul_self_sqrt hC
                unfold canonicalSmoothGamma canonicalSmoothModeCoeff
                rw [sq]
                calc
                  ((Real.sqrt (a ^ d))⁻¹ *
                      (Real.sqrt
                          (canonicalSmoothWeight d N a mass T m /
                            latticeFourierProductNormSq N d m) *
                        latticeFourierProductBasisFun N d m x)) *
                      ((Real.sqrt (a ^ d))⁻¹ *
                        (Real.sqrt
                            (canonicalSmoothWeight d N a mass T m /
                              latticeFourierProductNormSq N d m) *
                          latticeFourierProductBasisFun N d m x))
                      =
                    ((Real.sqrt (a ^ d))⁻¹ * (Real.sqrt (a ^ d))⁻¹) *
                      (Real.sqrt
                          (canonicalSmoothWeight d N a mass T m /
                            latticeFourierProductNormSq N d m) *
                        Real.sqrt
                          (canonicalSmoothWeight d N a mass T m /
                            latticeFourierProductNormSq N d m)) *
                      (latticeFourierProductBasisFun N d m x *
                        latticeFourierProductBasisFun N d m x) := by
                          ring
                  _ = (a ^ d : ℝ)⁻¹ *
                      (canonicalSmoothWeight d N a mass T m /
                        latticeFourierProductNormSq N d m) *
                      ((latticeFourierProductBasisFun N d m x) ^ 2) := by
                        rw [← mul_inv, ← Real.sqrt_mul (le_of_lt ha_d_pos),
                          Real.sqrt_mul_self (le_of_lt ha_d_pos), h_sq]
                        ring
                  _ = (a ^ d : ℝ)⁻¹ *
                      (canonicalSmoothWeight d N a mass T m *
                        latticeFourierProductBasisFun N d m x *
                        latticeFourierProductBasisFun N d m x /
                        latticeFourierProductNormSq N d m) := by
                          ring
    _ = (a ^ d : ℝ)⁻¹ *
        ∑ m : Fin d → Fin N,
          canonicalSmoothWeight d N a mass T m *
            latticeFourierProductBasisFun N d m x *
            latticeFourierProductBasisFun N d m x /
            latticeFourierProductNormSq N d m := by
              rw [← Finset.mul_sum]

private lemma canonicalRoughGamma_sq_sum_eq_wickConstant
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (x : FinLatticeSites d N) :
    ∑ m : Fin d → Fin N, (canonicalRoughGamma d N a mass T x m) ^ 2 =
      roughWickConstant d N a mass T := by
  rw [← canonicalRoughFieldFunction_self_moment_eq_roughWickConstant
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x]
  unfold canonicalRoughFieldFunction_self_moment_diag
  rw [canonicalRoughFieldFunction_self_moment
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x x]
  have ha_d_pos : (0 : ℝ) < a ^ d := pow_pos ha d
  calc
    ∑ m : Fin d → Fin N, (canonicalRoughGamma d N a mass T x m) ^ 2
      = ∑ m : Fin d → Fin N,
          (a ^ d : ℝ)⁻¹ *
            (canonicalRoughWeight d N a mass T m *
              latticeFourierProductBasisFun N d m x *
              latticeFourierProductBasisFun N d m x /
              latticeFourierProductNormSq N d m) := by
                refine Finset.sum_congr rfl ?_
                intro m hm
                have hC :
                    0 ≤ canonicalRoughWeight d N a mass T m /
                      latticeFourierProductNormSq N d m := by
                  apply div_nonneg
                  · exact canonicalRoughWeight_nonneg
                      (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT m
                  · exact (latticeFourierProductNormSq_pos (N := N) d m).le
                have h_sq :
                    Real.sqrt
                        (canonicalRoughWeight d N a mass T m /
                          latticeFourierProductNormSq N d m) *
                      Real.sqrt
                        (canonicalRoughWeight d N a mass T m /
                          latticeFourierProductNormSq N d m) =
                    canonicalRoughWeight d N a mass T m /
                      latticeFourierProductNormSq N d m :=
                  Real.mul_self_sqrt hC
                unfold canonicalRoughGamma canonicalRoughModeCoeff
                rw [sq]
                calc
                  ((Real.sqrt (a ^ d))⁻¹ *
                      (Real.sqrt
                          (canonicalRoughWeight d N a mass T m /
                            latticeFourierProductNormSq N d m) *
                        latticeFourierProductBasisFun N d m x)) *
                      ((Real.sqrt (a ^ d))⁻¹ *
                        (Real.sqrt
                            (canonicalRoughWeight d N a mass T m /
                              latticeFourierProductNormSq N d m) *
                          latticeFourierProductBasisFun N d m x))
                      =
                    ((Real.sqrt (a ^ d))⁻¹ * (Real.sqrt (a ^ d))⁻¹) *
                      (Real.sqrt
                          (canonicalRoughWeight d N a mass T m /
                            latticeFourierProductNormSq N d m) *
                        Real.sqrt
                          (canonicalRoughWeight d N a mass T m /
                            latticeFourierProductNormSq N d m)) *
                      (latticeFourierProductBasisFun N d m x *
                        latticeFourierProductBasisFun N d m x) := by
                          ring
                  _ = (a ^ d : ℝ)⁻¹ *
                      (canonicalRoughWeight d N a mass T m /
                        latticeFourierProductNormSq N d m) *
                      ((latticeFourierProductBasisFun N d m x) ^ 2) := by
                        rw [← mul_inv, ← Real.sqrt_mul (le_of_lt ha_d_pos),
                          Real.sqrt_mul_self (le_of_lt ha_d_pos), h_sq]
                        ring
                  _ = (a ^ d : ℝ)⁻¹ *
                      (canonicalRoughWeight d N a mass T m *
                        latticeFourierProductBasisFun N d m x *
                        latticeFourierProductBasisFun N d m x /
                        latticeFourierProductNormSq N d m) := by
                          ring
    _ = (a ^ d : ℝ)⁻¹ *
        ∑ m : Fin d → Fin N,
          canonicalRoughWeight d N a mass T m *
            latticeFourierProductBasisFun N d m x *
            latticeFourierProductBasisFun N d m x /
            latticeFourierProductNormSq N d m := by
              rw [← Finset.mul_sum]

private lemma canonicalSmoothCovariance_eq_sum_gamma_mul_gamma
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (x y : FinLatticeSites d N) :
    canonicalSmoothCovariance d N a mass T x y =
      ∑ m : Fin d → Fin N,
        canonicalSmoothGamma d N a mass T x m *
          canonicalSmoothGamma d N a mass T y m := by
  have ha_d_pos : (0 : ℝ) < a ^ d := pow_pos ha d
  calc
    canonicalSmoothCovariance d N a mass T x y
      = ∑ m : Fin d → Fin N,
          (a ^ d : ℝ)⁻¹ *
            (canonicalSmoothWeight d N a mass T m *
              latticeFourierProductBasisFun N d m x *
              latticeFourierProductBasisFun N d m y /
              latticeFourierProductNormSq N d m) := by
              unfold canonicalSmoothCovariance
              rw [← Finset.mul_sum]
    _ = ∑ m : Fin d → Fin N,
          canonicalSmoothGamma d N a mass T x m *
            canonicalSmoothGamma d N a mass T y m := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              have hC :
                  0 ≤ canonicalSmoothWeight d N a mass T m /
                    latticeFourierProductNormSq N d m := by
                apply div_nonneg
                · exact canonicalSmoothWeight_nonneg
                    (d := d) (N := N) (a := a) (mass := mass) ha hmass T m
                · exact (latticeFourierProductNormSq_pos (N := N) d m).le
              have h_sq :
                  Real.sqrt
                      (canonicalSmoothWeight d N a mass T m /
                        latticeFourierProductNormSq N d m) *
                    Real.sqrt
                      (canonicalSmoothWeight d N a mass T m /
                        latticeFourierProductNormSq N d m) =
                  canonicalSmoothWeight d N a mass T m /
                      latticeFourierProductNormSq N d m :=
                Real.mul_self_sqrt hC
              unfold canonicalSmoothGamma canonicalSmoothModeCoeff
              symm
              calc
                ((Real.sqrt (a ^ d))⁻¹ *
                    (Real.sqrt
                        (canonicalSmoothWeight d N a mass T m /
                          latticeFourierProductNormSq N d m) *
                      latticeFourierProductBasisFun N d m x)) *
                    ((Real.sqrt (a ^ d))⁻¹ *
                      (Real.sqrt
                          (canonicalSmoothWeight d N a mass T m /
                            latticeFourierProductNormSq N d m) *
                        latticeFourierProductBasisFun N d m y))
                    =
                  ((Real.sqrt (a ^ d))⁻¹ * (Real.sqrt (a ^ d))⁻¹) *
                    (Real.sqrt
                        (canonicalSmoothWeight d N a mass T m /
                          latticeFourierProductNormSq N d m) *
                      Real.sqrt
                        (canonicalSmoothWeight d N a mass T m /
                          latticeFourierProductNormSq N d m)) *
                    (latticeFourierProductBasisFun N d m x *
                      latticeFourierProductBasisFun N d m y) := by
                        ring
                _ = (a ^ d : ℝ)⁻¹ *
                    (canonicalSmoothWeight d N a mass T m /
                      latticeFourierProductNormSq N d m) *
                    (latticeFourierProductBasisFun N d m x *
                      latticeFourierProductBasisFun N d m y) := by
                        rw [← mul_inv, ← Real.sqrt_mul (le_of_lt ha_d_pos),
                          Real.sqrt_mul_self (le_of_lt ha_d_pos), h_sq]
                _ = (a ^ d : ℝ)⁻¹ *
                    (canonicalSmoothWeight d N a mass T m *
                      latticeFourierProductBasisFun N d m x *
                      latticeFourierProductBasisFun N d m y /
                      latticeFourierProductNormSq N d m) := by
                        ring

theorem canonicalRoughCovariance_eq_sum_gamma_mul_gamma
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (x y : FinLatticeSites d N) :
    canonicalRoughCovariance d N a mass T x y =
      ∑ m : Fin d → Fin N,
        canonicalRoughGamma d N a mass T x m *
          canonicalRoughGamma d N a mass T y m := by
  have ha_d_pos : (0 : ℝ) < a ^ d := pow_pos ha d
  calc
    canonicalRoughCovariance d N a mass T x y
      = ∑ m : Fin d → Fin N,
          (a ^ d : ℝ)⁻¹ *
            (canonicalRoughWeight d N a mass T m *
              latticeFourierProductBasisFun N d m x *
              latticeFourierProductBasisFun N d m y /
              latticeFourierProductNormSq N d m) := by
              unfold canonicalRoughCovariance
              rw [← Finset.mul_sum]
    _ = ∑ m : Fin d → Fin N,
          canonicalRoughGamma d N a mass T x m *
            canonicalRoughGamma d N a mass T y m := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              have hC :
                  0 ≤ canonicalRoughWeight d N a mass T m /
                    latticeFourierProductNormSq N d m := by
                apply div_nonneg
                · exact canonicalRoughWeight_nonneg
                    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT m
                · exact (latticeFourierProductNormSq_pos (N := N) d m).le
              have h_sq :
                  Real.sqrt
                      (canonicalRoughWeight d N a mass T m /
                        latticeFourierProductNormSq N d m) *
                    Real.sqrt
                      (canonicalRoughWeight d N a mass T m /
                        latticeFourierProductNormSq N d m) =
                  canonicalRoughWeight d N a mass T m /
                      latticeFourierProductNormSq N d m :=
                Real.mul_self_sqrt hC
              unfold canonicalRoughGamma canonicalRoughModeCoeff
              symm
              calc
                ((Real.sqrt (a ^ d))⁻¹ *
                    (Real.sqrt
                        (canonicalRoughWeight d N a mass T m /
                          latticeFourierProductNormSq N d m) *
                      latticeFourierProductBasisFun N d m x)) *
                    ((Real.sqrt (a ^ d))⁻¹ *
                      (Real.sqrt
                          (canonicalRoughWeight d N a mass T m /
                            latticeFourierProductNormSq N d m) *
                        latticeFourierProductBasisFun N d m y))
                    =
                  ((Real.sqrt (a ^ d))⁻¹ * (Real.sqrt (a ^ d))⁻¹) *
                    (Real.sqrt
                        (canonicalRoughWeight d N a mass T m /
                          latticeFourierProductNormSq N d m) *
                      Real.sqrt
                        (canonicalRoughWeight d N a mass T m /
                          latticeFourierProductNormSq N d m)) *
                    (latticeFourierProductBasisFun N d m x *
                      latticeFourierProductBasisFun N d m y) := by
                        ring
                _ = (a ^ d : ℝ)⁻¹ *
                    (canonicalRoughWeight d N a mass T m /
                      latticeFourierProductNormSq N d m) *
                    (latticeFourierProductBasisFun N d m x *
                      latticeFourierProductBasisFun N d m y) := by
                        rw [← mul_inv, ← Real.sqrt_mul (le_of_lt ha_d_pos),
                          Real.sqrt_mul_self (le_of_lt ha_d_pos), h_sq]
                _ = (a ^ d : ℝ)⁻¹ *
                    (canonicalRoughWeight d N a mass T m *
                      latticeFourierProductBasisFun N d m x *
                      latticeFourierProductBasisFun N d m y /
                      latticeFourierProductNormSq N d m) := by
                        ring

private theorem wickPower_two_site_pi_gaussianReal_eq_zero_of_ne
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ_x γ_y : ι → ℝ) {n m : ℕ} (hnm : n ≠ m) :
    ∫ ξ : ι → ℝ,
      wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ξ j) *
        wickMonomial m (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * ξ j)
      ∂(Measure.pi (fun _ : ι => gaussianReal 0 1)) = 0 := by
  classical
  let coeff :=
    fun (k : ℕ) (γ : ι → ℝ) (α : ι → ℕ) =>
      ((k.factorial : ℝ) / ∏ j, ((α j).factorial : ℝ)) *
        ∏ j, γ j ^ α j
  let diagFac := fun (α : ι → ℕ) => ∏ j, ((α j).factorial : ℝ)
  have h_summand_int :
      ∀ α β, MeasureTheory.Integrable
        (fun ξ =>
          (coeff n γ_x α * ∏ j, wickMonomial (α j) 1 (ξ j)) *
            (coeff m γ_y β * ∏ j, wickMonomial (β j) 1 (ξ j)))
        (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
    intro α β
    have h_base : MeasureTheory.Integrable
        (fun ξ : ι → ℝ =>
          ∏ j, wickMonomial (α j) 1 (ξ j) * wickMonomial (β j) 1 (ξ j))
        (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
      simpa using
        (MeasureTheory.Integrable.fintype_prod
          (μ := fun _ : ι => gaussianReal 0 1)
          (f := fun j x => wickMonomial (α j) 1 x * wickMonomial (β j) 1 x)
          (fun j => integrable_wickMonomial_mul_gaussianReal_one (α j) (β j)))
    refine h_base.const_mul (coeff n γ_x α * coeff m γ_y β) |>.congr ?_
    filter_upwards with ξ
    rw [Finset.prod_mul_distrib]
    ring
  have h_expand :
      ∀ ξ : ι → ℝ,
        wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ξ j) *
            wickMonomial m (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * ξ j) =
          (∑ α ∈ multiIndicesOfTotalDegree ι n,
            coeff n γ_x α * ∏ j, wickMonomial (α j) 1 (ξ j)) *
          (∑ β ∈ multiIndicesOfTotalDegree ι m,
            coeff m γ_y β * ∏ j, wickMonomial (β j) 1 (ξ j)) := by
    intro ξ
    rw [wickMonomial_eq_root, wickMonomial_eq_root]
    simp_rw [wickMonomial_eq_root]
    conv_lhs =>
      rw [wickMonomial_pow_sum_expansion_of_totalDegree (γ := γ_x) (ξ := ξ) (k := n)]
      rw [wickMonomial_pow_sum_expansion_of_totalDegree (γ := γ_y) (ξ := ξ) (k := m)]
  simp_rw [h_expand]
  have h_distrib :
      ∀ ξ : ι → ℝ,
        (∑ α ∈ multiIndicesOfTotalDegree ι n,
            coeff n γ_x α * ∏ j, wickMonomial (α j) 1 (ξ j)) *
          (∑ β ∈ multiIndicesOfTotalDegree ι m,
            coeff m γ_y β * ∏ j, wickMonomial (β j) 1 (ξ j)) =
        ∑ α ∈ multiIndicesOfTotalDegree ι n,
          ∑ β ∈ multiIndicesOfTotalDegree ι m,
            (coeff n γ_x α * ∏ j, wickMonomial (α j) 1 (ξ j)) *
              (coeff m γ_y β * ∏ j, wickMonomial (β j) 1 (ξ j)) := by
    intro ξ
    rw [Finset.sum_mul_sum]
  simp_rw [h_distrib]
  rw [MeasureTheory.integral_finset_sum _ (fun α hα => by
    apply MeasureTheory.integrable_finset_sum
    intro β hβ
    exact h_summand_int α β)]
  have h_outer :
      (∑ α ∈ multiIndicesOfTotalDegree ι n,
          ∫ ξ, ∑ β ∈ multiIndicesOfTotalDegree ι m,
            (coeff n γ_x α * ∏ j, wickMonomial (α j) 1 (ξ j)) *
              (coeff m γ_y β * ∏ j, wickMonomial (β j) 1 (ξ j))
          ∂(Measure.pi (fun _ : ι => gaussianReal 0 1))) =
        ∑ α ∈ multiIndicesOfTotalDegree ι n,
          ∑ β ∈ multiIndicesOfTotalDegree ι m,
            (coeff n γ_x α * coeff m γ_y β) *
              (if α = β then diagFac α else 0) := by
    refine Finset.sum_congr rfl ?_
    intro α hα
    rw [MeasureTheory.integral_finset_sum _ (fun β hβ => h_summand_int α β)]
    refine Finset.sum_congr rfl ?_
    intro β hβ
    have h_rearr :
        (fun ξ : ι → ℝ =>
          (coeff n γ_x α * ∏ j, wickMonomial (α j) 1 (ξ j)) *
            (coeff m γ_y β * ∏ j, wickMonomial (β j) 1 (ξ j))) =
          (fun ξ : ι → ℝ =>
            (coeff n γ_x α * coeff m γ_y β) *
              ((∏ j, wickMonomial (α j) 1 (ξ j)) *
                (∏ j, wickMonomial (β j) 1 (ξ j)))) := by
      funext ξ
      ring
    rw [h_rearr]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    simpa [wickMonomial_eq_root, diagFac] using
      (multiWickMonomial_pi_gaussianReal_inner α β)
  rw [h_outer]
  apply Finset.sum_eq_zero
  intro α hα
  apply Finset.sum_eq_zero
  intro β hβ
  by_cases hαβ : α = β
  · have hdegα : ∑ j, α j = n := (Finset.mem_filter.mp hα).2
    have hdegβ : ∑ j, β j = m := (Finset.mem_filter.mp hβ).2
    have hdegα' : ∑ j, β j = n := by
      simpa [hαβ] using hdegα
    have hnm' : n = m := hdegα'.symm.trans hdegβ
    exact False.elim (hnm hnm')
  · simp [hαβ, diagFac]

private theorem wickPower_two_site_pi_gaussianReal_integrable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ_x γ_y : ι → ℝ) (n m : ℕ) :
    Integrable
      (fun ξ : ι → ℝ =>
        wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ξ j) *
          wickMonomial m (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * ξ j))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  classical
  let coeff :=
    fun (k : ℕ) (γ : ι → ℝ) (α : ι → ℕ) =>
      ((k.factorial : ℝ) / ∏ j, ((α j).factorial : ℝ)) *
        ∏ j, γ j ^ α j
  have h_summand_int :
      ∀ α β, MeasureTheory.Integrable
        (fun ξ =>
          (coeff n γ_x α * ∏ j, wickMonomial (α j) 1 (ξ j)) *
            (coeff m γ_y β * ∏ j, wickMonomial (β j) 1 (ξ j)))
        (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
    intro α β
    have h_base : MeasureTheory.Integrable
        (fun ξ : ι → ℝ =>
          ∏ j, wickMonomial (α j) 1 (ξ j) * wickMonomial (β j) 1 (ξ j))
        (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
      simpa using
        (MeasureTheory.Integrable.fintype_prod
          (μ := fun _ : ι => gaussianReal 0 1)
          (f := fun j x => wickMonomial (α j) 1 x * wickMonomial (β j) 1 x)
          (fun j => integrable_wickMonomial_mul_gaussianReal_one (α j) (β j)))
    refine h_base.const_mul (coeff n γ_x α * coeff m γ_y β) |>.congr ?_
    filter_upwards with ξ
    rw [Finset.prod_mul_distrib]
    ring
  have h_expand :
      ∀ ξ : ι → ℝ,
        wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ξ j) *
            wickMonomial m (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * ξ j) =
          (∑ α ∈ multiIndicesOfTotalDegree ι n,
            coeff n γ_x α * ∏ j, wickMonomial (α j) 1 (ξ j)) *
          (∑ β ∈ multiIndicesOfTotalDegree ι m,
            coeff m γ_y β * ∏ j, wickMonomial (β j) 1 (ξ j)) := by
    intro ξ
    rw [wickMonomial_eq_root, wickMonomial_eq_root]
    simp_rw [wickMonomial_eq_root]
    conv_lhs =>
      rw [wickMonomial_pow_sum_expansion_of_totalDegree (γ := γ_x) (ξ := ξ) (k := n)]
      rw [wickMonomial_pow_sum_expansion_of_totalDegree (γ := γ_y) (ξ := ξ) (k := m)]
  have h_distrib :
      ∀ ξ : ι → ℝ,
        (∑ α ∈ multiIndicesOfTotalDegree ι n,
            coeff n γ_x α * ∏ j, wickMonomial (α j) 1 (ξ j)) *
          (∑ β ∈ multiIndicesOfTotalDegree ι m,
            coeff m γ_y β * ∏ j, wickMonomial (β j) 1 (ξ j)) =
        ∑ α ∈ multiIndicesOfTotalDegree ι n,
          ∑ β ∈ multiIndicesOfTotalDegree ι m,
            (coeff n γ_x α * ∏ j, wickMonomial (α j) 1 (ξ j)) *
              (coeff m γ_y β * ∏ j, wickMonomial (β j) 1 (ξ j)) := by
    intro ξ
    rw [Finset.sum_mul_sum]
  have h_sum :
      Integrable
        (fun ξ : ι → ℝ =>
          ∑ α ∈ multiIndicesOfTotalDegree ι n,
            ∑ β ∈ multiIndicesOfTotalDegree ι m,
              (coeff n γ_x α * ∏ j, wickMonomial (α j) 1 (ξ j)) *
                (coeff m γ_y β * ∏ j, wickMonomial (β j) 1 (ξ j)))
        (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
    apply MeasureTheory.integrable_finset_sum
    intro α hα
    apply MeasureTheory.integrable_finset_sum
    intro β hβ
    exact h_summand_int α β
  refine h_sum.congr ?_
  filter_upwards with ξ
  rw [h_expand ξ, h_distrib ξ]

private lemma multiIndicesOfTotalDegree_eq_piAntidiag_generic
    {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) :
    multiIndicesOfTotalDegree ι n =
      Finset.piAntidiag Finset.univ n := by
  ext α
  constructor
  · intro hα
    unfold multiIndicesOfTotalDegree at hα
    simp only [Finset.mem_filter] at hα
    exact (Finset.mem_piAntidiag).2 ⟨hα.2, fun i hi => Finset.mem_univ i⟩
  · intro hα
    have hsum : ∑ j, α j = n := (Finset.mem_piAntidiag.mp hα).1
    simp only [multiIndicesOfTotalDegree, Finset.mem_filter,
      Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨?_, hsum⟩
    intro i
    have h_le : α i ≤ ∑ j, α j := by
      simpa using
        (Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) (Finset.mem_univ i))
    exact Nat.lt_succ_of_le (hsum ▸ h_le)

private lemma sum_pow_eq_sum_multiIndices_generic
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (n : ℕ) :
    (∑ j, f j) ^ n =
      ∑ α ∈ multiIndicesOfTotalDegree ι n,
        ((n.factorial : ℝ) / ∏ j, ((α j).factorial : ℝ)) *
          ∏ j, f j ^ α j := by
  rw [multiIndicesOfTotalDegree_eq_piAntidiag_generic (ι := ι) n,
    Finset.sum_pow_eq_sum_piAntidiag]
  refine Finset.sum_congr rfl ?_
  intro α hα
  have hsum : ∑ j, α j = n := (Finset.mem_piAntidiag.mp hα).1
  have hprod_pos : (0 : ℝ) < ∏ j, ((α j).factorial : ℝ) := by
    apply Finset.prod_pos
    intro j hj
    exact_mod_cast Nat.factorial_pos (α j)
  have hprod_ne : (∏ j, ((α j).factorial : ℝ)) ≠ 0 := ne_of_gt hprod_pos
  have hmult :
      (Nat.multinomial Finset.univ α : ℝ) =
        ((n.factorial : ℝ) / ∏ j, ((α j).factorial : ℝ)) := by
    apply (eq_div_iff hprod_ne).2
    calc
      (Nat.multinomial Finset.univ α : ℝ) * ∏ j, ((α j).factorial : ℝ)
          = (∏ j, ((α j).factorial : ℝ)) *
              (Nat.multinomial Finset.univ α : ℝ) := by ring
      _ = (n.factorial : ℝ) := by
        have hspec :
            (∏ j ∈ (Finset.univ : Finset ι), (α j).factorial) *
              Nat.multinomial Finset.univ α =
            (∑ j ∈ (Finset.univ : Finset ι), α j).factorial :=
          Nat.multinomial_spec Finset.univ α
        exact_mod_cast (hspec.trans (by simp [hsum]))
  simp [hmult]

private theorem wickPower_two_site_pi_gaussianReal_eq_diag
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ_x γ_y : ι → ℝ) (n : ℕ) :
    ∫ ξ : ι → ℝ,
      wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ξ j) *
        wickMonomial n (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * ξ j)
      ∂(Measure.pi (fun _ : ι => gaussianReal 0 1)) =
    (n.factorial : ℝ) * (∑ j, γ_x j * γ_y j) ^ n := by
  classical
  let coeff :=
    fun (γ : ι → ℝ) (α : ι → ℕ) =>
      ((n.factorial : ℝ) / ∏ j, ((α j).factorial : ℝ)) *
        ∏ j, γ j ^ α j
  let diagFac := fun (α : ι → ℕ) => ∏ j, ((α j).factorial : ℝ)
  have h_summand_int :
      ∀ α β, MeasureTheory.Integrable
        (fun ξ =>
          (coeff γ_x α * ∏ j, wickMonomial (α j) 1 (ξ j)) *
            (coeff γ_y β * ∏ j, wickMonomial (β j) 1 (ξ j)))
        (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
    intro α β
    have h_base : MeasureTheory.Integrable
        (fun ξ : ι → ℝ =>
          ∏ j, wickMonomial (α j) 1 (ξ j) * wickMonomial (β j) 1 (ξ j))
        (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
      simpa using
        (MeasureTheory.Integrable.fintype_prod
          (μ := fun _ : ι => gaussianReal 0 1)
          (f := fun j x => wickMonomial (α j) 1 x * wickMonomial (β j) 1 x)
          (fun j => integrable_wickMonomial_mul_gaussianReal_one (α j) (β j)))
    refine h_base.const_mul (coeff γ_x α * coeff γ_y β) |>.congr ?_
    filter_upwards with ξ
    rw [Finset.prod_mul_distrib]
    ring
  have h_expand :
      ∀ ξ : ι → ℝ,
        wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ξ j) *
            wickMonomial n (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * ξ j) =
          (∑ α ∈ multiIndicesOfTotalDegree ι n,
            coeff γ_x α * ∏ j, wickMonomial (α j) 1 (ξ j)) *
          (∑ β ∈ multiIndicesOfTotalDegree ι n,
            coeff γ_y β * ∏ j, wickMonomial (β j) 1 (ξ j)) := by
    intro ξ
    rw [wickMonomial_eq_root, wickMonomial_eq_root]
    simp_rw [wickMonomial_eq_root]
    conv_lhs =>
      rw [wickMonomial_pow_sum_expansion_of_totalDegree (γ := γ_x) (ξ := ξ) (k := n)]
      rw [wickMonomial_pow_sum_expansion_of_totalDegree (γ := γ_y) (ξ := ξ) (k := n)]
  simp_rw [h_expand]
  have h_distrib :
      ∀ ξ : ι → ℝ,
        (∑ α ∈ multiIndicesOfTotalDegree ι n,
            coeff γ_x α * ∏ j, wickMonomial (α j) 1 (ξ j)) *
          (∑ β ∈ multiIndicesOfTotalDegree ι n,
            coeff γ_y β * ∏ j, wickMonomial (β j) 1 (ξ j)) =
        ∑ α ∈ multiIndicesOfTotalDegree ι n,
          ∑ β ∈ multiIndicesOfTotalDegree ι n,
            (coeff γ_x α * ∏ j, wickMonomial (α j) 1 (ξ j)) *
              (coeff γ_y β * ∏ j, wickMonomial (β j) 1 (ξ j)) := by
    intro ξ
    rw [Finset.sum_mul_sum]
  simp_rw [h_distrib]
  rw [MeasureTheory.integral_finset_sum _ (fun α hα => by
    apply MeasureTheory.integrable_finset_sum
    intro β hβ
    exact h_summand_int α β)]
  have h_outer :
      (∑ α ∈ multiIndicesOfTotalDegree ι n,
          ∫ ξ, ∑ β ∈ multiIndicesOfTotalDegree ι n,
            (coeff γ_x α * ∏ j, wickMonomial (α j) 1 (ξ j)) *
              (coeff γ_y β * ∏ j, wickMonomial (β j) 1 (ξ j))
          ∂(Measure.pi (fun _ : ι => gaussianReal 0 1))) =
        ∑ α ∈ multiIndicesOfTotalDegree ι n,
          ∑ β ∈ multiIndicesOfTotalDegree ι n,
            (coeff γ_x α * coeff γ_y β) *
              (if α = β then diagFac α else 0) := by
    refine Finset.sum_congr rfl ?_
    intro α hα
    rw [MeasureTheory.integral_finset_sum _ (fun β hβ => h_summand_int α β)]
    refine Finset.sum_congr rfl ?_
    intro β hβ
    have h_rearr :
        (fun ξ : ι → ℝ =>
          (coeff γ_x α * ∏ j, wickMonomial (α j) 1 (ξ j)) *
            (coeff γ_y β * ∏ j, wickMonomial (β j) 1 (ξ j))) =
          (fun ξ : ι → ℝ =>
            (coeff γ_x α * coeff γ_y β) *
              ((∏ j, wickMonomial (α j) 1 (ξ j)) *
                (∏ j, wickMonomial (β j) 1 (ξ j)))) := by
      funext ξ
      ring
    rw [h_rearr, MeasureTheory.integral_const_mul]
    congr 1
    simpa [wickMonomial_eq_root, diagFac] using
      (multiWickMonomial_pi_gaussianReal_inner α β)
  rw [h_outer]
  have h_collapse :
      (∑ α ∈ multiIndicesOfTotalDegree ι n,
          ∑ β ∈ multiIndicesOfTotalDegree ι n,
            (coeff γ_x α * coeff γ_y β) * (if α = β then diagFac α else 0)) =
      ∑ α ∈ multiIndicesOfTotalDegree ι n,
        (coeff γ_x α * coeff γ_y α) * diagFac α := by
    refine Finset.sum_congr rfl ?_
    intro α hα
    rw [Finset.sum_eq_single_of_mem α hα]
    · simp [diagFac]
    · intro β hβ hβα
      have hneq : α ≠ β := by
        intro h
        exact hβα h.symm
      simp [hneq, diagFac]
  have h_diag_term :
      ∀ α, α ∈ multiIndicesOfTotalDegree ι n →
        (coeff γ_x α * coeff γ_y α) * diagFac α =
          (n.factorial : ℝ) *
            (((n.factorial : ℝ) / ∏ j, ((α j).factorial : ℝ)) *
              ∏ j, (γ_x j * γ_y j) ^ α j) := by
    intro α hα
    have hprod_mul :
        (∏ j, γ_x j ^ α j) * (∏ j, γ_y j ^ α j) =
          ∏ j, (γ_x j * γ_y j) ^ α j := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl ?_
      intro j hj
      rw [mul_pow]
    have hprod_pos : (0 : ℝ) < ∏ j, ((α j).factorial : ℝ) := by
      apply Finset.prod_pos
      intro j hj
      exact_mod_cast Nat.factorial_pos (α j)
    have hprod_ne : (∏ j, ((α j).factorial : ℝ)) ≠ 0 := ne_of_gt hprod_pos
    calc
      (coeff γ_x α * coeff γ_y α) * diagFac α
          = (n.factorial : ℝ) *
              (((n.factorial : ℝ) / ∏ j, ((α j).factorial : ℝ)) *
                ((∏ j, γ_x j ^ α j) * (∏ j, γ_y j ^ α j))) := by
            unfold coeff diagFac
            field_simp [hprod_ne]
      _ = (n.factorial : ℝ) *
            (((n.factorial : ℝ) / ∏ j, ((α j).factorial : ℝ)) *
              ∏ j, (γ_x j * γ_y j) ^ α j) := by
            simp [hprod_mul]
  calc
    (∑ α ∈ multiIndicesOfTotalDegree ι n,
        ∑ β ∈ multiIndicesOfTotalDegree ι n,
          (coeff γ_x α * coeff γ_y β) * (if α = β then diagFac α else 0))
      =
      ∑ α ∈ multiIndicesOfTotalDegree ι n,
        (coeff γ_x α * coeff γ_y α) * diagFac α := h_collapse
    _ =
      ∑ α ∈ multiIndicesOfTotalDegree ι n,
        (n.factorial : ℝ) *
          (((n.factorial : ℝ) / ∏ j, ((α j).factorial : ℝ)) *
            ∏ j, (γ_x j * γ_y j) ^ α j) := by
          refine Finset.sum_congr rfl ?_
          intro α hα
          exact h_diag_term α hα
    _ = (n.factorial : ℝ) *
        (∑ α ∈ multiIndicesOfTotalDegree ι n,
          ((n.factorial : ℝ) / ∏ j, ((α j).factorial : ℝ)) *
            ∏ j, (γ_x j * γ_y j) ^ α j) := by
        rw [← Finset.mul_sum]
    _ = (n.factorial : ℝ) * (∑ j, γ_x j * γ_y j) ^ n := by
        rw [sum_pow_eq_sum_multiIndices_generic (f := fun j => γ_x j * γ_y j) n]

theorem canonicalSmoothWickPower_two_site_marginal_integrable
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (n m : ℕ) (x y : FinLatticeSites d N) :
    Integrable
      (fun η_S : (Fin d → Fin N) → ℝ =>
        wickMonomial n (smoothWickConstant d N a mass T)
          (canonicalSmoothFieldFunctionOfFst d N a mass T η_S x) *
        wickMonomial m (smoothWickConstant d N a mass T)
          (canonicalSmoothFieldFunctionOfFst d N a mass T η_S y))
      (Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)) := by
  let γ_x : (Fin d → Fin N) → ℝ := canonicalSmoothGamma d N a mass T x
  let γ_y : (Fin d → Fin N) → ℝ := canonicalSmoothGamma d N a mass T y
  refine (wickPower_two_site_pi_gaussianReal_integrable
      (γ_x := γ_x) (γ_y := γ_y) n m).congr ?_
  filter_upwards with η_S
  calc
    wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * η_S j) *
        wickMonomial m (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * η_S j)
      =
        wickMonomial n (smoothWickConstant d N a mass T)
          (canonicalSmoothFieldFunctionOfFst d N a mass T η_S x) *
        wickMonomial m (smoothWickConstant d N a mass T)
          (canonicalSmoothFieldFunctionOfFst d N a mass T η_S y) := by
            symm
            calc
              wickMonomial n (smoothWickConstant d N a mass T)
                  (canonicalSmoothFieldFunctionOfFst d N a mass T η_S x) *
                wickMonomial m (smoothWickConstant d N a mass T)
                  (canonicalSmoothFieldFunctionOfFst d N a mass T η_S y)
                =
                  wickMonomial n (∑ j, (γ_x j) ^ 2)
                    (canonicalSmoothFieldFunctionOfFst d N a mass T η_S x) *
                  wickMonomial m (smoothWickConstant d N a mass T)
                    (canonicalSmoothFieldFunctionOfFst d N a mass T η_S y) := by
                      rw [show smoothWickConstant d N a mass T = ∑ j, (γ_x j) ^ 2 from by
                        simpa [γ_x] using
                          (canonicalSmoothGamma_sq_sum_eq_wickConstant
                            (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x).symm]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * η_S j) *
                  wickMonomial m (smoothWickConstant d N a mass T)
                    (canonicalSmoothFieldFunctionOfFst d N a mass T η_S y) := by
                      rw [show canonicalSmoothFieldFunctionOfFst d N a mass T η_S x =
                        ∑ j, γ_x j * η_S j from by
                        simpa [γ_x] using
                          canonicalSmoothFieldFunctionOfFst_eq_sum_gamma
                            (d := d) (N := N) (a := a) (mass := mass) T η_S x]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * η_S j) *
                  wickMonomial m (∑ j, (γ_y j) ^ 2)
                    (canonicalSmoothFieldFunctionOfFst d N a mass T η_S y) := by
                      rw [show smoothWickConstant d N a mass T = ∑ j, (γ_y j) ^ 2 from by
                        simpa [γ_y] using
                          (canonicalSmoothGamma_sq_sum_eq_wickConstant
                            (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT y).symm]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * η_S j) *
                  wickMonomial m (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * η_S j) := by
                      rw [show canonicalSmoothFieldFunctionOfFst d N a mass T η_S y =
                        ∑ j, γ_y j * η_S j from by
                        simpa [γ_y] using
                          canonicalSmoothFieldFunctionOfFst_eq_sum_gamma
                            (d := d) (N := N) (a := a) (mass := mass) T η_S y]

theorem canonicalRoughWickPower_two_site_marginal_integrable
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (n m : ℕ) (x y : FinLatticeSites d N) :
    Integrable
      (fun η_R : (Fin d → Fin N) → ℝ =>
        wickMonomial n (roughWickConstant d N a mass T)
          (canonicalRoughFieldFunctionOfSnd d N a mass T η_R x) *
        wickMonomial m (roughWickConstant d N a mass T)
          (canonicalRoughFieldFunctionOfSnd d N a mass T η_R y))
      (Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)) := by
  let γ_x : (Fin d → Fin N) → ℝ := canonicalRoughGamma d N a mass T x
  let γ_y : (Fin d → Fin N) → ℝ := canonicalRoughGamma d N a mass T y
  refine (wickPower_two_site_pi_gaussianReal_integrable
      (γ_x := γ_x) (γ_y := γ_y) n m).congr ?_
  filter_upwards with η_R
  calc
    wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * η_R j) *
        wickMonomial m (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * η_R j)
      =
        wickMonomial n (roughWickConstant d N a mass T)
          (canonicalRoughFieldFunctionOfSnd d N a mass T η_R x) *
        wickMonomial m (roughWickConstant d N a mass T)
          (canonicalRoughFieldFunctionOfSnd d N a mass T η_R y) := by
            symm
            calc
              wickMonomial n (roughWickConstant d N a mass T)
                  (canonicalRoughFieldFunctionOfSnd d N a mass T η_R x) *
                wickMonomial m (roughWickConstant d N a mass T)
                  (canonicalRoughFieldFunctionOfSnd d N a mass T η_R y)
                =
                  wickMonomial n (∑ j, (γ_x j) ^ 2)
                    (canonicalRoughFieldFunctionOfSnd d N a mass T η_R x) *
                  wickMonomial m (roughWickConstant d N a mass T)
                    (canonicalRoughFieldFunctionOfSnd d N a mass T η_R y) := by
                      rw [show roughWickConstant d N a mass T = ∑ j, (γ_x j) ^ 2 from by
                        simpa [γ_x] using
                          (canonicalRoughGamma_sq_sum_eq_wickConstant
                            (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x).symm]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * η_R j) *
                  wickMonomial m (roughWickConstant d N a mass T)
                    (canonicalRoughFieldFunctionOfSnd d N a mass T η_R y) := by
                      rw [show canonicalRoughFieldFunctionOfSnd d N a mass T η_R x =
                        ∑ j, γ_x j * η_R j from by
                        simpa [γ_x] using
                          canonicalRoughFieldFunctionOfSnd_eq_sum_gamma
                            (d := d) (N := N) (a := a) (mass := mass) T η_R x]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * η_R j) *
                  wickMonomial m (∑ j, (γ_y j) ^ 2)
                    (canonicalRoughFieldFunctionOfSnd d N a mass T η_R y) := by
                      rw [show roughWickConstant d N a mass T = ∑ j, (γ_y j) ^ 2 from by
                        simpa [γ_y] using
                          (canonicalRoughGamma_sq_sum_eq_wickConstant
                            (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT y).symm]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * η_R j) *
                  wickMonomial m (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * η_R j) := by
                      rw [show canonicalRoughFieldFunctionOfSnd d N a mass T η_R y =
                        ∑ j, γ_y j * η_R j from by
                        simpa [γ_y] using
                          canonicalRoughFieldFunctionOfSnd_eq_sum_gamma
                            (d := d) (N := N) (a := a) (mass := mass) T η_R y]

theorem canonicalSmoothWickPower_two_site_marginal_eq_zero_of_ne
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (n m : ℕ) (hnm : n ≠ m) (x y : FinLatticeSites d N) :
    ∫ η_S : (Fin d → Fin N) → ℝ,
      wickMonomial n (smoothWickConstant d N a mass T)
        (canonicalSmoothFieldFunctionOfFst d N a mass T η_S x) *
      wickMonomial m (smoothWickConstant d N a mass T)
        (canonicalSmoothFieldFunctionOfFst d N a mass T η_S y)
      ∂(Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)) = 0 := by
  let γ_x : (Fin d → Fin N) → ℝ := canonicalSmoothGamma d N a mass T x
  let γ_y : (Fin d → Fin N) → ℝ := canonicalSmoothGamma d N a mass T y
  calc
    ∫ η_S : (Fin d → Fin N) → ℝ,
        wickMonomial n (smoothWickConstant d N a mass T)
          (canonicalSmoothFieldFunctionOfFst d N a mass T η_S x) *
        wickMonomial m (smoothWickConstant d N a mass T)
          (canonicalSmoothFieldFunctionOfFst d N a mass T η_S y)
      ∂(Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1))
      =
        ∫ η_S : (Fin d → Fin N) → ℝ,
          wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * η_S j) *
            wickMonomial m (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * η_S j)
          ∂(Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)) := by
            apply integral_congr_ae
            filter_upwards with η_S
            calc
              wickMonomial n (smoothWickConstant d N a mass T)
                  (canonicalSmoothFieldFunctionOfFst d N a mass T η_S x) *
                wickMonomial m (smoothWickConstant d N a mass T)
                  (canonicalSmoothFieldFunctionOfFst d N a mass T η_S y)
                =
                  wickMonomial n (∑ j, (γ_x j) ^ 2)
                    (canonicalSmoothFieldFunctionOfFst d N a mass T η_S x) *
                  wickMonomial m (smoothWickConstant d N a mass T)
                    (canonicalSmoothFieldFunctionOfFst d N a mass T η_S y) := by
                      rw [show smoothWickConstant d N a mass T = ∑ j, (γ_x j) ^ 2 from by
                        simpa [γ_x] using
                          (canonicalSmoothGamma_sq_sum_eq_wickConstant
                            (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x).symm]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * η_S j) *
                  wickMonomial m (smoothWickConstant d N a mass T)
                    (canonicalSmoothFieldFunctionOfFst d N a mass T η_S y) := by
                      rw [show canonicalSmoothFieldFunctionOfFst d N a mass T η_S x =
                        ∑ j, γ_x j * η_S j from by
                        simpa [γ_x] using
                          canonicalSmoothFieldFunctionOfFst_eq_sum_gamma
                            (d := d) (N := N) (a := a) (mass := mass) T η_S x]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * η_S j) *
                  wickMonomial m (∑ j, (γ_y j) ^ 2)
                    (canonicalSmoothFieldFunctionOfFst d N a mass T η_S y) := by
                      rw [show smoothWickConstant d N a mass T = ∑ j, (γ_y j) ^ 2 from by
                        simpa [γ_y] using
                          (canonicalSmoothGamma_sq_sum_eq_wickConstant
                            (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT y).symm]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * η_S j) *
                  wickMonomial m (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * η_S j) := by
                      rw [show canonicalSmoothFieldFunctionOfFst d N a mass T η_S y =
                        ∑ j, γ_y j * η_S j from by
                        simpa [γ_y] using
                          canonicalSmoothFieldFunctionOfFst_eq_sum_gamma
                            (d := d) (N := N) (a := a) (mass := mass) T η_S y]
    _ = 0 :=
      wickPower_two_site_pi_gaussianReal_eq_zero_of_ne
        (γ_x := γ_x) (γ_y := γ_y) hnm

theorem canonicalRoughWickPower_two_site_marginal_eq_zero_of_ne
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (n m : ℕ) (hnm : n ≠ m) (x y : FinLatticeSites d N) :
    ∫ η_R : (Fin d → Fin N) → ℝ,
      wickMonomial n (roughWickConstant d N a mass T)
        (canonicalRoughFieldFunctionOfSnd d N a mass T η_R x) *
      wickMonomial m (roughWickConstant d N a mass T)
        (canonicalRoughFieldFunctionOfSnd d N a mass T η_R y)
      ∂(Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)) = 0 := by
  let γ_x : (Fin d → Fin N) → ℝ := canonicalRoughGamma d N a mass T x
  let γ_y : (Fin d → Fin N) → ℝ := canonicalRoughGamma d N a mass T y
  calc
    ∫ η_R : (Fin d → Fin N) → ℝ,
        wickMonomial n (roughWickConstant d N a mass T)
          (canonicalRoughFieldFunctionOfSnd d N a mass T η_R x) *
        wickMonomial m (roughWickConstant d N a mass T)
          (canonicalRoughFieldFunctionOfSnd d N a mass T η_R y)
      ∂(Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1))
      =
        ∫ η_R : (Fin d → Fin N) → ℝ,
          wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * η_R j) *
            wickMonomial m (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * η_R j)
          ∂(Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)) := by
            apply integral_congr_ae
            filter_upwards with η_R
            calc
              wickMonomial n (roughWickConstant d N a mass T)
                  (canonicalRoughFieldFunctionOfSnd d N a mass T η_R x) *
                wickMonomial m (roughWickConstant d N a mass T)
                  (canonicalRoughFieldFunctionOfSnd d N a mass T η_R y)
                =
                  wickMonomial n (∑ j, (γ_x j) ^ 2)
                    (canonicalRoughFieldFunctionOfSnd d N a mass T η_R x) *
                  wickMonomial m (roughWickConstant d N a mass T)
                    (canonicalRoughFieldFunctionOfSnd d N a mass T η_R y) := by
                      rw [show roughWickConstant d N a mass T = ∑ j, (γ_x j) ^ 2 from by
                        simpa [γ_x] using
                          (canonicalRoughGamma_sq_sum_eq_wickConstant
                            (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x).symm]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * η_R j) *
                  wickMonomial m (roughWickConstant d N a mass T)
                    (canonicalRoughFieldFunctionOfSnd d N a mass T η_R y) := by
                      rw [show canonicalRoughFieldFunctionOfSnd d N a mass T η_R x =
                        ∑ j, γ_x j * η_R j from by
                        simpa [γ_x] using
                          canonicalRoughFieldFunctionOfSnd_eq_sum_gamma
                            (d := d) (N := N) (a := a) (mass := mass) T η_R x]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * η_R j) *
                  wickMonomial m (∑ j, (γ_y j) ^ 2)
                    (canonicalRoughFieldFunctionOfSnd d N a mass T η_R y) := by
                      rw [show roughWickConstant d N a mass T = ∑ j, (γ_y j) ^ 2 from by
                        simpa [γ_y] using
                          (canonicalRoughGamma_sq_sum_eq_wickConstant
                            (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT y).symm]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * η_R j) *
                  wickMonomial m (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * η_R j) := by
                      rw [show canonicalRoughFieldFunctionOfSnd d N a mass T η_R y =
                        ∑ j, γ_y j * η_R j from by
                        simpa [γ_y] using
                          canonicalRoughFieldFunctionOfSnd_eq_sum_gamma
                            (d := d) (N := N) (a := a) (mass := mass) T η_R y]
    _ = 0 :=
      wickPower_two_site_pi_gaussianReal_eq_zero_of_ne
        (γ_x := γ_x) (γ_y := γ_y) hnm

theorem canonicalSmoothWickPower_two_site_marginal_eq_diag
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (n : ℕ) (x y : FinLatticeSites d N) :
    ∫ η_S : (Fin d → Fin N) → ℝ,
      wickMonomial n (smoothWickConstant d N a mass T)
        (canonicalSmoothFieldFunctionOfFst d N a mass T η_S x) *
      wickMonomial n (smoothWickConstant d N a mass T)
        (canonicalSmoothFieldFunctionOfFst d N a mass T η_S y)
      ∂(Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)) =
    (n.factorial : ℝ) * (canonicalSmoothCovariance d N a mass T x y) ^ n := by
  let γ_x : (Fin d → Fin N) → ℝ := canonicalSmoothGamma d N a mass T x
  let γ_y : (Fin d → Fin N) → ℝ := canonicalSmoothGamma d N a mass T y
  calc
    ∫ η_S : (Fin d → Fin N) → ℝ,
        wickMonomial n (smoothWickConstant d N a mass T)
          (canonicalSmoothFieldFunctionOfFst d N a mass T η_S x) *
        wickMonomial n (smoothWickConstant d N a mass T)
          (canonicalSmoothFieldFunctionOfFst d N a mass T η_S y)
      ∂(Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1))
      =
        ∫ η_S : (Fin d → Fin N) → ℝ,
          wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * η_S j) *
            wickMonomial n (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * η_S j)
          ∂(Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)) := by
            apply integral_congr_ae
            filter_upwards with η_S
            calc
              wickMonomial n (smoothWickConstant d N a mass T)
                  (canonicalSmoothFieldFunctionOfFst d N a mass T η_S x) *
                wickMonomial n (smoothWickConstant d N a mass T)
                  (canonicalSmoothFieldFunctionOfFst d N a mass T η_S y)
                =
                  wickMonomial n (∑ j, (γ_x j) ^ 2)
                    (canonicalSmoothFieldFunctionOfFst d N a mass T η_S x) *
                  wickMonomial n (smoothWickConstant d N a mass T)
                    (canonicalSmoothFieldFunctionOfFst d N a mass T η_S y) := by
                      rw [show smoothWickConstant d N a mass T = ∑ j, (γ_x j) ^ 2 from by
                        simpa [γ_x] using
                          (canonicalSmoothGamma_sq_sum_eq_wickConstant
                            (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x).symm]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * η_S j) *
                  wickMonomial n (smoothWickConstant d N a mass T)
                    (canonicalSmoothFieldFunctionOfFst d N a mass T η_S y) := by
                      rw [show canonicalSmoothFieldFunctionOfFst d N a mass T η_S x =
                        ∑ j, γ_x j * η_S j from by
                        simpa [γ_x] using
                          canonicalSmoothFieldFunctionOfFst_eq_sum_gamma
                            (d := d) (N := N) (a := a) (mass := mass) T η_S x]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * η_S j) *
                  wickMonomial n (∑ j, (γ_y j) ^ 2)
                    (canonicalSmoothFieldFunctionOfFst d N a mass T η_S y) := by
                      rw [show smoothWickConstant d N a mass T = ∑ j, (γ_y j) ^ 2 from by
                        simpa [γ_y] using
                          (canonicalSmoothGamma_sq_sum_eq_wickConstant
                            (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT y).symm]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * η_S j) *
                  wickMonomial n (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * η_S j) := by
                      rw [show canonicalSmoothFieldFunctionOfFst d N a mass T η_S y =
                        ∑ j, γ_y j * η_S j from by
                        simpa [γ_y] using
                          canonicalSmoothFieldFunctionOfFst_eq_sum_gamma
                            (d := d) (N := N) (a := a) (mass := mass) T η_S y]
    _ = (n.factorial : ℝ) * (∑ j, γ_x j * γ_y j) ^ n :=
      wickPower_two_site_pi_gaussianReal_eq_diag (γ_x := γ_x) (γ_y := γ_y) n
    _ = (n.factorial : ℝ) * (canonicalSmoothCovariance d N a mass T x y) ^ n := by
      congr 2
      symm
      simpa [γ_x, γ_y] using
        canonicalSmoothCovariance_eq_sum_gamma_mul_gamma
          (d := d) (N := N) (a := a) (mass := mass) ha hmass T x y

theorem canonicalRoughWickPower_two_site_marginal_eq_diag
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (n : ℕ) (x y : FinLatticeSites d N) :
    ∫ η_R : (Fin d → Fin N) → ℝ,
      wickMonomial n (roughWickConstant d N a mass T)
        (canonicalRoughFieldFunctionOfSnd d N a mass T η_R x) *
      wickMonomial n (roughWickConstant d N a mass T)
        (canonicalRoughFieldFunctionOfSnd d N a mass T η_R y)
      ∂(Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)) =
    (n.factorial : ℝ) * (canonicalRoughCovariance d N a mass T x y) ^ n := by
  let γ_x : (Fin d → Fin N) → ℝ := canonicalRoughGamma d N a mass T x
  let γ_y : (Fin d → Fin N) → ℝ := canonicalRoughGamma d N a mass T y
  calc
    ∫ η_R : (Fin d → Fin N) → ℝ,
        wickMonomial n (roughWickConstant d N a mass T)
          (canonicalRoughFieldFunctionOfSnd d N a mass T η_R x) *
        wickMonomial n (roughWickConstant d N a mass T)
          (canonicalRoughFieldFunctionOfSnd d N a mass T η_R y)
      ∂(Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1))
      =
        ∫ η_R : (Fin d → Fin N) → ℝ,
          wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * η_R j) *
            wickMonomial n (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * η_R j)
          ∂(Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)) := by
            apply integral_congr_ae
            filter_upwards with η_R
            calc
              wickMonomial n (roughWickConstant d N a mass T)
                  (canonicalRoughFieldFunctionOfSnd d N a mass T η_R x) *
                wickMonomial n (roughWickConstant d N a mass T)
                  (canonicalRoughFieldFunctionOfSnd d N a mass T η_R y)
                =
                  wickMonomial n (∑ j, (γ_x j) ^ 2)
                    (canonicalRoughFieldFunctionOfSnd d N a mass T η_R x) *
                  wickMonomial n (roughWickConstant d N a mass T)
                    (canonicalRoughFieldFunctionOfSnd d N a mass T η_R y) := by
                      rw [show roughWickConstant d N a mass T = ∑ j, (γ_x j) ^ 2 from by
                        simpa [γ_x] using
                          (canonicalRoughGamma_sq_sum_eq_wickConstant
                            (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x).symm]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * η_R j) *
                  wickMonomial n (roughWickConstant d N a mass T)
                    (canonicalRoughFieldFunctionOfSnd d N a mass T η_R y) := by
                      rw [show canonicalRoughFieldFunctionOfSnd d N a mass T η_R x =
                        ∑ j, γ_x j * η_R j from by
                        simpa [γ_x] using
                          canonicalRoughFieldFunctionOfSnd_eq_sum_gamma
                            (d := d) (N := N) (a := a) (mass := mass) T η_R x]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * η_R j) *
                  wickMonomial n (∑ j, (γ_y j) ^ 2)
                    (canonicalRoughFieldFunctionOfSnd d N a mass T η_R y) := by
                      rw [show roughWickConstant d N a mass T = ∑ j, (γ_y j) ^ 2 from by
                        simpa [γ_y] using
                          (canonicalRoughGamma_sq_sum_eq_wickConstant
                            (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT y).symm]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * η_R j) *
                  wickMonomial n (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * η_R j) := by
                      rw [show canonicalRoughFieldFunctionOfSnd d N a mass T η_R y =
                        ∑ j, γ_y j * η_R j from by
                        simpa [γ_y] using
                          canonicalRoughFieldFunctionOfSnd_eq_sum_gamma
                            (d := d) (N := N) (a := a) (mass := mass) T η_R y]
    _ = (n.factorial : ℝ) * (∑ j, γ_x j * γ_y j) ^ n :=
      wickPower_two_site_pi_gaussianReal_eq_diag (γ_x := γ_x) (γ_y := γ_y) n
    _ = (n.factorial : ℝ) * (canonicalRoughCovariance d N a mass T x y) ^ n := by
      congr 2
      symm
      simpa [γ_x, γ_y] using
        canonicalRoughCovariance_eq_sum_gamma_mul_gamma
          (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x y

theorem abs_canonicalSmoothCovariance_le_smoothWickConstant
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (x y : FinLatticeSites d N) :
    |canonicalSmoothCovariance d N a mass T x y| ≤ smoothWickConstant d N a mass T := by
  let γ_x : (Fin d → Fin N) → ℝ := canonicalSmoothGamma d N a mass T x
  let γ_y : (Fin d → Fin N) → ℝ := canonicalSmoothGamma d N a mass T y
  have h_cs :
      (∑ m : Fin d → Fin N, γ_x m * γ_y m) ^ 2 ≤
        (∑ m : Fin d → Fin N, (γ_x m) ^ 2) *
          ∑ m : Fin d → Fin N, (γ_y m) ^ 2 := by
    simpa [γ_x, γ_y] using
      (Finset.sum_mul_sq_le_sq_mul_sq
        (R := ℝ) (Finset.univ : Finset (Fin d → Fin N)) γ_x γ_y)
  have hx :
      ∑ m : Fin d → Fin N, (γ_x m) ^ 2 = smoothWickConstant d N a mass T := by
    simpa [γ_x] using
      canonicalSmoothGamma_sq_sum_eq_wickConstant
        (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x
  have hy :
      ∑ m : Fin d → Fin N, (γ_y m) ^ 2 = smoothWickConstant d N a mass T := by
    simpa [γ_y] using
      canonicalSmoothGamma_sq_sum_eq_wickConstant
        (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT y
  have h_nonneg : 0 ≤ smoothWickConstant d N a mass T := by
    rw [← hx]
    exact Finset.sum_nonneg fun m hm => sq_nonneg (γ_x m)
  have h_sq :
      (∑ m : Fin d → Fin N, γ_x m * γ_y m) ^ 2 ≤
        smoothWickConstant d N a mass T * smoothWickConstant d N a mass T := by
    simpa [hx, hy]
      using h_cs
  have h_abs :
      |∑ m : Fin d → Fin N, γ_x m * γ_y m| ≤
        smoothWickConstant d N a mass T := by
    have h_abs_sq :
        |∑ m : Fin d → Fin N, γ_x m * γ_y m| ^ 2 ≤
          |smoothWickConstant d N a mass T| ^ 2 := by
      simpa [sq_abs, pow_two] using h_sq
    have := (sq_le_sq).mp h_abs_sq
    simpa [abs_of_nonneg h_nonneg] using this
  rw [show canonicalSmoothCovariance d N a mass T x y =
      ∑ m : Fin d → Fin N, γ_x m * γ_y m from by
      simpa [γ_x, γ_y] using
        canonicalSmoothCovariance_eq_sum_gamma_mul_gamma
          (d := d) (N := N) (a := a) (mass := mass) ha hmass T x y]
  exact h_abs

theorem canonicalSumFieldFunction_covariance_eq_GJ
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (x y : FinLatticeSites d N) :
    let δ_x : FinLatticeField d N := fun z => if z = x then 1 else 0
    let δ_y : FinLatticeField d N := fun z => if z = y then 1 else 0
    ∫ η : CanonicalJoint d N,
      canonicalSumFieldFunction d N a mass T η x *
        canonicalSumFieldFunction d N a mass T η y
      ∂(canonicalJointMeasure d N) =
    GaussianField.covariance (latticeCovarianceGJ d N a mass ha hmass) δ_x δ_y := by
  intro δ_x δ_y
  rw [canonicalSumFieldFunction_covariance d N a mass ha hmass T hT x y]
  rw [GaussianField.latticeCovariance_GJ_eq_inv_smul_bare]
  refine congrArg ((a^d : ℝ)⁻¹ * ·) ?_
  symm
  calc
    GaussianField.covariance (latticeCovariance d N a mass ha hmass) δ_x δ_y
      = ∑ m : Fin d → Fin N,
          latticeFourierProductCoeff N d δ_x m *
            latticeFourierProductCoeff N d δ_y m /
            (canonicalEigenvalue d N a mass m *
              latticeFourierProductNormSq N d m) := by
                simpa [canonicalEigenvalue] using
                  (abstract_spectral_eq_dft_spectral_family (N := N) d a mass ha hmass δ_x δ_y)
    _ = ∑ m : Fin d → Fin N,
          latticeFourierProductBasisFun N d m x *
            latticeFourierProductBasisFun N d m y /
            (canonicalEigenvalue d N a mass m *
              latticeFourierProductNormSq N d m) := by
                refine Finset.sum_congr rfl ?_
                intro m hm
                rw [latticeFourierProductCoeff_delta (d := d) (N := N) x m,
                  latticeFourierProductCoeff_delta (d := d) (N := N) y m]

private lemma latticeCovarianceGJ_eq_sum_delta_covariance
    (ha : 0 < a) (hmass : 0 < mass)
    (f g : FinLatticeField d N) :
    GaussianField.covariance (latticeCovarianceGJ d N a mass ha hmass) f g =
      ∑ x : FinLatticeSites d N,
        ∑ y : FinLatticeSites d N,
          f x * g y *
            GaussianField.covariance (latticeCovarianceGJ d N a mass ha hmass)
              (finLatticeDelta d N x) (finLatticeDelta d N y) := by
  rw [GaussianField.field_basis_decomposition_density (d := d) (N := N) f,
    GaussianField.field_basis_decomposition_density (d := d) (N := N) g]
  simp only [GaussianField.covariance, map_sum, map_smul, Pi.smul_apply, smul_eq_mul, sum_inner,
    inner_sum, real_inner_smul_left, real_inner_smul_right, Finset.sum_apply]
  simp [finLatticeDelta]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro x hx
  refine Finset.sum_congr rfl ?_
  intro y hy
  rw [real_inner_comm]
  ring

private lemma canonicalSmoothFieldFunction_integral_zero
    (T : ℝ) (x : FinLatticeSites d N) :
    ∫ η : CanonicalJoint d N,
      canonicalSmoothFieldFunction d N a mass T η x
      ∂(canonicalJointMeasure d N) = 0 := by
  rw [canonicalJointMeasure]
  rw [show (fun η : CanonicalJoint d N =>
      canonicalSmoothFieldFunction d N a mass T η x) =
      (fun z : ((Fin d → Fin N) → ℝ) × ((Fin d → Fin N) → ℝ) =>
        canonicalSmoothFieldFunctionOfFst d N a mass T z.1 x) by
      funext η
      exact canonicalSmoothFieldFunction_eq_of_fst d N a mass T η.1 η.2 x]
  rw [integral_fun_fst (E := ℝ)
    (μ := Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1))
    (ν := Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1))
    (f := fun η_S : (Fin d → Fin N) → ℝ =>
      canonicalSmoothFieldFunctionOfFst d N a mass T η_S x)]
  simpa [canonicalSmoothFieldFunctionOfFst] using
    canonicalSmoothFieldFunction_marginal_integral_zero (d := d) (N := N) (a := a) (mass := mass) T x

private lemma canonicalRoughFieldFunction_integral_zero
    (T : ℝ) (x : FinLatticeSites d N) :
    ∫ η : CanonicalJoint d N,
      canonicalRoughFieldFunction d N a mass T η x
      ∂(canonicalJointMeasure d N) = 0 := by
  rw [canonicalJointMeasure]
  rw [show (fun η : CanonicalJoint d N =>
      canonicalRoughFieldFunction d N a mass T η x) =
      (fun z : ((Fin d → Fin N) → ℝ) × ((Fin d → Fin N) → ℝ) =>
        canonicalRoughFieldFunctionOfSnd d N a mass T z.2 x) by
      funext η
      exact canonicalRoughFieldFunction_eq_of_snd d N a mass T η.1 η.2 x]
  rw [integral_fun_snd (E := ℝ)
    (μ := Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1))
    (ν := Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1))
    (f := fun η_R : (Fin d → Fin N) → ℝ =>
      canonicalRoughFieldFunctionOfSnd d N a mass T η_R x)]
  simpa [canonicalRoughFieldFunctionOfSnd] using
    canonicalRoughFieldFunction_marginal_integral_zero (d := d) (N := N) (a := a) (mass := mass) T x

private lemma canonicalSumFieldFunction_integral_zero
    (T : ℝ) (x : FinLatticeSites d N) :
    ∫ η : CanonicalJoint d N,
      canonicalSumFieldFunction d N a mass T η x
      ∂(canonicalJointMeasure d N) = 0 := by
  change ∫ η : CanonicalJoint d N,
      canonicalSmoothFieldFunction d N a mass T η x +
        canonicalRoughFieldFunction d N a mass T η x
      ∂(canonicalJointMeasure d N) = 0
  have hs_int : Integrable
      (fun η : CanonicalJoint d N => canonicalSmoothFieldFunction d N a mass T η x)
      (canonicalJointMeasure d N) :=
    (canonicalSmoothFieldFunction_memLp_two (d := d) (N := N) (a := a) (mass := mass) T x).integrable
      one_le_two
  have hr_int : Integrable
      (fun η : CanonicalJoint d N => canonicalRoughFieldFunction d N a mass T η x)
      (canonicalJointMeasure d N) :=
    (canonicalRoughFieldFunction_memLp_two (d := d) (N := N) (a := a) (mass := mass) T x).integrable
      one_le_two
  rw [integral_add hs_int hr_int, canonicalSmoothFieldFunction_integral_zero,
    canonicalRoughFieldFunction_integral_zero]
  ring

private lemma canonicalSumFieldFunction_pairing_memLp_two
    (T : ℝ) (f : FinLatticeField d N) :
    MemLp
      (fun η : CanonicalJoint d N =>
        ∑ x : FinLatticeSites d N, f x * canonicalSumFieldFunction d N a mass T η x)
      2 (canonicalJointMeasure d N) := by
  refine memLp_finset_sum _ (fun x _ => ?_)
  refine MemLp.const_mul ?_ (f x)
  exact canonicalSumFieldFunction_memLp_two (d := d) (N := N) (a := a) (mass := mass) T x

private lemma canonicalSumFieldFunction_pairing_integral_zero
    (T : ℝ) (f : FinLatticeField d N) :
    ∫ η : CanonicalJoint d N,
      ∑ x : FinLatticeSites d N, f x * canonicalSumFieldFunction d N a mass T η x
      ∂(canonicalJointMeasure d N) = 0 := by
  rw [integral_finset_sum]
  · refine Finset.sum_eq_zero ?_
    intro x hx
    rw [integral_const_mul, canonicalSumFieldFunction_integral_zero]
    ring
  · intro x hx
    refine Integrable.const_mul ?_ (f x)
    exact (canonicalSumFieldFunction_memLp_two (d := d) (N := N) (a := a) (mass := mass) T x).integrable
      one_le_two

private lemma canonicalSumFieldLaw_pairing_integral_zero
    (T : ℝ) (f : FinLatticeField d N) :
    ∫ φ : FinLatticeField d N, sitePairingCLM d N f φ
      ∂(canonicalSumFieldLaw d N a mass T) = 0 := by
  rw [canonicalSumFieldLaw_eq_map_canonicalSumFieldFunction]
  rw [integral_map
    (canonicalSumFieldFunction_measurable d N a mass T).aemeasurable]
  ·
    change ∫ η : CanonicalJoint d N,
        ∑ x : FinLatticeSites d N, f x * canonicalSumFieldFunction d N a mass T η x
        ∂(canonicalJointMeasure d N) = 0
    exact canonicalSumFieldFunction_pairing_integral_zero
      (d := d) (N := N) (a := a) (mass := mass) T f
  ·
    exact (sitePairingCLM d N f).measurable.aestronglyMeasurable

private lemma canonicalSumFieldLaw_pairing_cross_moment_eq_covariance
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (f g : FinLatticeField d N) :
    ∫ φ : FinLatticeField d N, sitePairingCLM d N f φ * sitePairingCLM d N g φ
      ∂(canonicalSumFieldLaw d N a mass T) =
    GaussianField.covariance (latticeCovarianceGJ d N a mass ha hmass) f g := by
  rw [canonicalSumFieldLaw_eq_map_canonicalSumFieldFunction]
  rw [integral_map
    (canonicalSumFieldFunction_measurable d N a mass T).aemeasurable]
  ·
    change ∫ η : CanonicalJoint d N,
        (∑ x : FinLatticeSites d N, f x * canonicalSumFieldFunction d N a mass T η x) *
          (∑ y : FinLatticeSites d N, g y * canonicalSumFieldFunction d N a mass T η y)
        ∂(canonicalJointMeasure d N) =
      GaussianField.covariance (latticeCovarianceGJ d N a mass ha hmass) f g
    let μ := canonicalJointMeasure d N
    let X : FinLatticeSites d N → CanonicalJoint d N → ℝ :=
      fun x η => f x * canonicalSumFieldFunction d N a mass T η x
    let Y : FinLatticeSites d N → CanonicalJoint d N → ℝ :=
      fun y η => g y * canonicalSumFieldFunction d N a mass T η y
    have hX : ∀ x, MemLp (X x) 2 μ := by
      intro x
      dsimp [X, μ]
      exact MemLp.const_mul
        (canonicalSumFieldFunction_memLp_two (d := d) (N := N) (a := a) (mass := mass) T x)
        (f x)
    have hY : ∀ y, MemLp (Y y) 2 μ := by
      intro y
      dsimp [Y, μ]
      exact MemLp.const_mul
        (canonicalSumFieldFunction_memLp_two (d := d) (N := N) (a := a) (mass := mass) T y)
        (g y)
    have h_pair_f : MemLp (fun η : CanonicalJoint d N => ∑ x, X x η) 2 μ := by
      simpa [X, μ] using
        canonicalSumFieldFunction_pairing_memLp_two (d := d) (N := N) (a := a) (mass := mass) T f
    have h_pair_g : MemLp (fun η : CanonicalJoint d N => ∑ y, Y y η) 2 μ := by
      simpa [Y, μ] using
        canonicalSumFieldFunction_pairing_memLp_two (d := d) (N := N) (a := a) (mass := mass) T g
    have h_pair_f_zero : ∫ η, ∑ x, X x η ∂μ = 0 := by
      simpa [X, μ] using
        canonicalSumFieldFunction_pairing_integral_zero (d := d) (N := N) (a := a) (mass := mass) T f
    have h_pair_g_zero : ∫ η, ∑ y, Y y η ∂μ = 0 := by
      simpa [Y, μ] using
        canonicalSumFieldFunction_pairing_integral_zero (d := d) (N := N) (a := a) (mass := mass) T g
    have h_cov_pair :
        cov[(fun η : CanonicalJoint d N => ∑ x, X x η),
          (fun η : CanonicalJoint d N => ∑ y, Y y η); μ] =
        ∫ η : CanonicalJoint d N, (∑ x, X x η) * (∑ y, Y y η) ∂μ := by
      rw [covariance_eq_sub h_pair_f h_pair_g, h_pair_f_zero, h_pair_g_zero]
      simp
    have h_cov_sum :
        cov[(fun η : CanonicalJoint d N => ∑ x, X x η),
          (fun η : CanonicalJoint d N => ∑ y, Y y η); μ] =
        ∑ x, ∑ y, cov[X x, Y y; μ] := by
      exact covariance_fun_sum_fun_sum hX hY
    rw [← h_cov_pair, h_cov_sum]
    rw [latticeCovarianceGJ_eq_sum_delta_covariance (d := d) (N := N) (a := a) (mass := mass)
      ha hmass f g]
    refine Finset.sum_congr rfl ?_
    intro x hx
    refine Finset.sum_congr rfl ?_
    intro y hy
    have hX_zero : ∫ η, X x η ∂μ = 0 := by
      simp only [X, μ]
      rw [integral_const_mul, canonicalSumFieldFunction_integral_zero]
      ring
    have hY_zero : ∫ η, Y y η ∂μ = 0 := by
      simp only [Y, μ]
      rw [integral_const_mul, canonicalSumFieldFunction_integral_zero]
      ring
    rw [covariance_eq_sub (hX x) (hY y), hX_zero, hY_zero]
    simp
    have hxy :
        (fun η : CanonicalJoint d N => X x η * Y y η) =
        (fun η : CanonicalJoint d N =>
          (f x * g y) *
            (canonicalSumFieldFunction d N a mass T η x *
              canonicalSumFieldFunction d N a mass T η y)) := by
      funext η
      simp [X, Y]
      ring
    rw [hxy, integral_const_mul]
    rw [canonicalSumFieldFunction_covariance_eq_GJ
      (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x y]
    by_cases hfx : f x = 0
    · simp [hfx]
    · by_cases hgy : g y = 0
      · simp [hgy]
      · have hxdelta : (fun z => if z = x then 1 else 0) = finLatticeDelta d N x := by
          ext z
          simp [finLatticeDelta]
        have hydelta : (fun z => if z = y then 1 else 0) = finLatticeDelta d N y := by
          ext z
          simp [finLatticeDelta]
        rw [hxdelta, hydelta]
  ·
    exact ((sitePairingCLM d N f).measurable.aestronglyMeasurable).mul
      ((sitePairingCLM d N g).measurable.aestronglyMeasurable)

private theorem canonicalSumFieldLaw_pairing_is_gaussian
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (f : FinLatticeField d N) :
    (canonicalSumFieldLaw d N a mass T).map
      (fun φ : FinLatticeField d N => ∑ x : FinLatticeSites d N, f x * φ x) =
      gaussianReal 0
        (@inner ℝ ell2' _
          (latticeCovarianceGJ d N a mass ha hmass f)
          (latticeCovarianceGJ d N a mass ha hmass f)).toNNReal := by
  have h_gauss :=
    (ProbabilityTheory.IsGaussian.map_eq_gaussianReal
      (μ := canonicalSumFieldLaw d N a mass T)
      (L := sitePairingCLM d N f))
  change Measure.map (sitePairingCLM d N f) (canonicalSumFieldLaw d N a mass T) =
    gaussianReal 0
      (@inner ℝ ell2' _
        (latticeCovarianceGJ d N a mass ha hmass f)
        (latticeCovarianceGJ d N a mass ha hmass f)).toNNReal
  rw [h_gauss]
  apply (ProbabilityTheory.gaussianReal_ext_iff).2
  constructor
  · exact canonicalSumFieldLaw_pairing_integral_zero (d := d) (N := N) (a := a) (mass := mass) T f
  · have h_var :
        Var[sitePairingCLM d N f; canonicalSumFieldLaw d N a mass T] =
          ∫ φ : FinLatticeField d N, (sitePairingCLM d N f φ) ^ 2
            ∂(canonicalSumFieldLaw d N a mass T) := by
      refine variance_of_integral_eq_zero
        (sitePairingCLM d N f).measurable.aemeasurable ?_
      exact canonicalSumFieldLaw_pairing_integral_zero
        (d := d) (N := N) (a := a) (mass := mass) T f
    rw [h_var, show (fun φ : FinLatticeField d N => (sitePairingCLM d N f φ) ^ 2) =
        (fun φ : FinLatticeField d N => sitePairingCLM d N f φ * sitePairingCLM d N f φ) by
          funext φ; ring]
    rw [canonicalSumFieldLaw_pairing_cross_moment_eq_covariance
      (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT f f]
    rfl

theorem canonicalSumFieldLaw_eq_latticeGaussianFieldLaw
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T) :
    canonicalSumFieldLaw d N a mass T =
      latticeGaussianFieldLaw d N a mass ha hmass := by
  letI : IsProbabilityMeasure (canonicalSumFieldLaw d N a mass T) := inferInstance
  letI : IsProbabilityMeasure (latticeGaussianFieldLaw d N a mass ha hmass) := by
    unfold latticeGaussianFieldLaw
    exact Measure.isProbabilityMeasure_map
      (measurable_evalMap (d := d) (N := N)).aemeasurable
  apply GaussianField.cramerWold
  intro f
  exact (canonicalSumFieldLaw_pairing_is_gaussian
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT f).trans
      (latticeGaussianFieldLaw_pairing_is_gaussian
        (d := d) (N := N) a mass ha hmass f).symm

theorem canonicalJointMeasure_map_canonicalSumConfig
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T) :
    (canonicalJointMeasure d N).map (canonicalSumConfig d N a mass T) =
      latticeGaussianMeasure d N a mass ha hmass := by
  rw [show canonicalSumConfig d N a mass T =
      fun η => GaussianField.evalMapInv d N
        (canonicalSumFieldFunction d N a mass T η) from by
          funext η
          rw [canonicalSumConfig, latticeFieldToConfig_eq_evalMapInv]]
  have h_map_map :
      Measure.map
          (fun η => GaussianField.evalMapInv d N
            (canonicalSumFieldFunction d N a mass T η))
          (canonicalJointMeasure d N) =
        Measure.map
          (GaussianField.evalMapInv d N)
          ((canonicalJointMeasure d N).map
            (canonicalSumFieldFunction d N a mass T)) := by
    simpa [Function.comp] using
      (Measure.map_map
        (g := GaussianField.evalMapInv d N)
        (f := canonicalSumFieldFunction d N a mass T)
        (μ := canonicalJointMeasure d N)
        (GaussianField.evalMapInv_measurable (d := d) (N := N))
        (canonicalSumFieldFunction_measurable
          (d := d) (N := N) (a := a) (mass := mass) T)).symm
  rw [h_map_map]
  rw [← canonicalSumFieldLaw_eq_map_canonicalSumFieldFunction
    (d := d) (N := N) (a := a) (mass := mass) T]
  rw [canonicalSumFieldLaw_eq_latticeGaussianFieldLaw
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT]
  rw [latticeGaussianFieldLaw]
  rw [Measure.map_map
    (g := GaussianField.evalMapInv d N)
    (f := GaussianField.evalMap d N)
    (μ := latticeGaussianMeasure d N a mass ha hmass)
    (GaussianField.evalMapInv_measurable (d := d) (N := N))
    (GaussianField.measurable_evalMap (d := d) (N := N))]
  rw [show
      GaussianField.evalMapInv d N ∘ GaussianField.evalMap d N = id from by
          funext ω
          exact GaussianField.evalMapInv_evalMap d N ω]
  simp

theorem integral_comp_canonicalSumConfig
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (F : Configuration (FinLatticeField d N) → ℝ) (hF : Measurable F) :
    ∫ η, F (canonicalSumConfig d N a mass T η) ∂(canonicalJointMeasure d N) =
      ∫ ω, F ω ∂(latticeGaussianMeasure d N a mass ha hmass) := by
  rw [← integral_map
    (canonicalSumConfig_measurable (d := d) (N := N) (a := a) (mass := mass) T).aemeasurable
    hF.aestronglyMeasurable]
  rw [canonicalJointMeasure_map_canonicalSumConfig
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT]

end Variance

end Canonical

end Pphi2
