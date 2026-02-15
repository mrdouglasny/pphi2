/-
  Pphi2.GaussianCylinder.Covariance
  Gaussian measures on the cylinder ℝ × S¹_L and Wick-ordered fields.

  Reference: DDJ Section 2, Definitions 2.1-2.2 and Appendix C.
  Adapted from spheres S_R to cylinders ℝ × S¹_L.
-/
import Pphi2.Basic
import Pphi2.Polynomial

noncomputable section

open MeasureTheory

/-! ## UV regularization on the cylinder -/

/-- UV regularization operator K_{L,N} = (1 - Δ_L/N²)⁻¹ on the cylinder.
    Momentum cutoff in Fourier space. -/
axiom uvRegularization (L : ℝ) (N : ℕ+) :
  TestFunctionCyl 2 L →L[ℝ] TestFunctionCyl 2 L

/-- Regularized covariance G_{L,N} = K_{L,N} G_L K_{L,N}. -/
axiom regularizedCovariance (L : ℝ) (N : ℕ+) :
  TestFunctionCyl 2 L →L[ℝ] TestFunctionCyl 2 L

/-! ## Gaussian measure on the cylinder -/

/-- The Gaussian measure ν_{L,N} on field configurations of ℝ × S¹_L
    with covariance G_{L,N}.
    DDJ Eq. (2.2), adapted to cylinder. -/
axiom gaussianMeasureCylinder (L : ℝ) (N : ℕ+) :
  ProbabilityMeasure (FieldConfigurationCyl 2 L)

/-- ν_{L,N} is concentrated on L²₁(ℝ × S¹_L) ⊂ D'(ℝ × S¹_L).
    DDJ Lemma C.1, adapted to cylinder. -/
axiom gaussianMeasure_concentrated (L : ℝ) (N : ℕ+) :
    True -- concentrated on Sobolev space

/-! ## Free field and Wick polynomials on the cylinder -/

/-- The Gaussian random variable X_L on the cylinder with covariance G_L. -/
axiom freeField (L : ℝ) : FieldConfigurationCyl 2 L

/-- The regularized free field X_{L,N} = K_{L,N} X_L. -/
axiom regularizedFreeField (L : ℝ) (N : ℕ+) : FieldConfigurationCyl 2 L

/-- Wick polynomial X_{L,N}^{:m:}(x) of order m on the cylinder.
    DDJ Definition 2.1, adapted to cylinder. -/
axiom wickPower (L : ℝ) (N : ℕ+) (m : ℕ) :
  SpaceTimeCyl 2 L → ℝ

/-- The integrated Wick polynomial X_{L,N}^{:m:}(h) = ∫ X^{:m:}(x) h(x) dx. -/
axiom wickPowerIntegrated (L : ℝ) (N : ℕ+) (m : ℕ) :
  TestFunctionCyl 2 L → ℝ

/-- Y_{L,N} = Σ_{m=0}^n a_m X_{L,N}^{:m:}(1).
    The "action" random variable on the cylinder.
    DDJ Definition 2.1, adapted. -/
axiom actionRV (P : InteractionPolynomial) (L : ℝ) (N : ℕ+) : ℝ

/-- Y^g_{L,N} = Y_{L,N} - X_{L,N}(g)ⁿ/n.
    The modified action for auxiliary measure.
    DDJ Definition 2.1. -/
axiom actionRV_g (P : InteractionPolynomial) (L : ℝ) (N : ℕ+)
    (g : TestFunctionCyl 2 L) : ℝ

/-! ## Nelson hypercontractivity -/

/-- Nelson's estimate: for X in an inhomogeneous Wiener chaos of order n,
    𝔼[|X|^p]^{1/p} ≤ √n (p-1)^{n/2} 𝔼[X²]^{1/2}.
    DDJ Lemma C.4. -/
axiom nelson_hypercontractivity :
    True -- precise statement requires Wiener chaos setup

/-! ## Moment bounds on the cylinder -/

/-- Uniform bound: 𝔼‖X_{L,N}‖²_{L¹₂(ℝ × S¹_L)} ≤ C for some C
    depending on L (but not on N).
    DDJ Lemma C.1, adapted to cylinder. -/
axiom freeField_moment_nonuniform (L : ℝ) (N : ℕ+) :
    ∃ C : ℝ, 0 < C ∧ True -- 𝔼‖X_{L,N}‖² ≤ C

/-- Uniform bound in both L and N:
    𝔼‖X_L - X_{L,N}‖²_{L^{-κ-δ}_2} ≤ C N^{-2δ}.
    DDJ Lemma C.2(B), adapted to cylinder. -/
axiom freeField_moment_uniform (κ δ : ℝ) (hκ : 0 < κ) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ) (_ : 1 ≤ L) (N : ℕ+), True -- bound

end
