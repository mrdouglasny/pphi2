import Pphi2.NelsonEstimate.LatticeBridge
import Pphi2.NelsonEstimate.LatticeSetup
import Pphi2.NelsonEstimate.CovarianceSplit
import Pphi2.GeneralResults.LatticeProductDFT
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import GaussianField.Hypercontractive

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

noncomputable def canonicalRoughFieldFunction (d N : ℕ) [NeZero N]
    (a mass T : ℝ) (η : CanonicalJoint d N) :
    FinLatticeSites d N → ℝ :=
  fun x =>
    (Real.sqrt (a^d))⁻¹ *
      ∑ m : Fin d → Fin N, canonicalRoughModeCoeff d N a mass T x m * η.2 m

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
  have h_smooth_memLp : ∀ z : FinLatticeSites d N,
      MemLp (fun η : CanonicalJoint d N =>
        canonicalSmoothFieldFunction d N a mass T η z) 2 (canonicalJointMeasure d N) := by
    intro z
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
  have h_rough_memLp : ∀ z : FinLatticeSites d N,
      MemLp (fun η : CanonicalJoint d N =>
        canonicalRoughFieldFunction d N a mass T η z) 2 (canonicalJointMeasure d N) := by
    intro z
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
  have h_ss_int : Integrable (fun η : CanonicalJoint d N =>
      canonicalSmoothFieldFunction d N a mass T η x *
        canonicalSmoothFieldFunction d N a mass T η y) (canonicalJointMeasure d N) :=
    MemLp.integrable_mul (h_smooth_memLp x) (h_smooth_memLp y)
  have h_sr_int : Integrable (fun η : CanonicalJoint d N =>
      canonicalSmoothFieldFunction d N a mass T η x *
        canonicalRoughFieldFunction d N a mass T η y) (canonicalJointMeasure d N) :=
    MemLp.integrable_mul (h_smooth_memLp x) (h_rough_memLp y)
  have h_rs_int : Integrable (fun η : CanonicalJoint d N =>
      canonicalRoughFieldFunction d N a mass T η x *
        canonicalSmoothFieldFunction d N a mass T η y) (canonicalJointMeasure d N) :=
    MemLp.integrable_mul (h_rough_memLp x) (h_smooth_memLp y)
  have h_rr_int : Integrable (fun η : CanonicalJoint d N =>
      canonicalRoughFieldFunction d N a mass T η x *
        canonicalRoughFieldFunction d N a mass T η y) (canonicalJointMeasure d N) :=
    MemLp.integrable_mul (h_rough_memLp x) (h_rough_memLp y)
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

end Variance

end Canonical

end Pphi2
