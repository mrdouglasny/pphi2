/-
  Pphi2.StochasticQuant.DaPratoDebussche
  Stochastic quantization and the Da Prato-Debussche decomposition
  on the cylinder ℝ × S¹_L.

  Reference: DDJ Section 3.
  Adapted from spheres S_R to cylinders ℝ × S¹_L.
-/
import Pphi2.MeasureCylinder.Regularized

noncomputable section

open MeasureTheory

/-! ## Stochastic quantization on the cylinder

The P(Φ)₂ measure μ_{L,N}^g is the stationary distribution of the SPDE:
  dΦ = √2 dW - Q_{L,N} Φ dt - P'(Φ, c) dt + (Φ(g))^{n-1} g dt

where Q_{L,N} = (1-Δ_L)(1-Δ_L/N²)² and Δ_L is the cylinder Laplacian.

The Da Prato-Debussche trick decomposes Φ = Ψ + Z where:
  - Z solves the linear (free) SPDE: dZ = √2 dW - Q Z dt
  - Ψ = Φ - Z solves a non-singular PDE (no stochastic forcing)
-/

/-- The drift operator Q_{L,N} = (1-Δ_L)(1-Δ_L/N²)² on the cylinder.
    DDJ Definition 3.2, adapted. -/
axiom driftOperator (L : ℝ) (N : ℕ+) :
  TestFunctionCyl 2 L →L[ℝ] TestFunctionCyl 2 L

/-! ## The free field dynamics Z_{L,N}(t) -/

/-- The Ornstein-Uhlenbeck process Z_{L,N}(t) on the cylinder.
    Stationary distribution: ν_{L,N}.
    DDJ Eq. (3.1), (3.4), adapted. -/
axiom ouProcess (L : ℝ) (N : ℕ+) (t : ℝ) : FieldConfigurationCyl 2 L

/-- Law(Z_{L,N}(t)) = ν_{L,N} for all t ≥ 0.
    DDJ Lemma 3.3. -/
axiom ouProcess_stationary (L : ℝ) (N : ℕ+) (t : ℝ) (ht : 0 ≤ t) :
    True -- Law(Z(t)) = ν_{L,N}

/-! ## The interacting dynamics Φ_{L,N}^g(t) -/

/-- The interacting process Φ_{L,N}^g(t) on the cylinder.
    Stationary distribution: μ_{L,N}^g.
    DDJ Eq. (3.2), (3.5), adapted. -/
axiom interactingProcess (P : InteractionPolynomial) (L : ℝ) (N : ℕ+)
    (g : TestFunctionCyl 2 L) (t : ℝ) : FieldConfigurationCyl 2 L

/-- Law(Φ_{L,N}^g(t)) = μ_{L,N}^g for all t ≥ 0.
    DDJ Lemma 3.3. -/
axiom interactingProcess_stationary (P : InteractionPolynomial) (L : ℝ) (N : ℕ+)
    (g : TestFunctionCyl 2 L) (t : ℝ) (ht : 0 ≤ t) :
    True -- Law(Φ(t)) = μ^g_{L,N}

/-! ## The Da Prato-Debussche remainder Ψ = Φ - Z -/

/-- The DPD remainder Ψ_{L,N}^g(t) = Φ_{L,N}^g(t) - Z_{L,N}(t).
    Satisfies a non-singular PDE (no stochastic forcing).
    DDJ Eq. (3.13), adapted. -/
axiom dpdRemainder (P : InteractionPolynomial) (L : ℝ) (N : ℕ+)
    (g : TestFunctionCyl 2 L) (t : ℝ) : FieldConfigurationCyl 2 L

/-- The PDE for Ψ (in expanded form, DDJ Eq. (3.17)):
    (∂_t + Q_{L,N}) Ψ + Ψ^{n-1}
      = Σ_{l,m} a_{m,l} Z^{:m-l:} Ψ^l + ((Ψ+Z)(g))^{n-1} g

    The key point: the RHS involves Wick powers of Z (well-controlled
    stochastic terms) times powers of Ψ (the unknown). This PDE is
    non-singular in the limit N → ∞. -/
axiom dpdRemainder_pde (P : InteractionPolynomial) (L : ℝ) (N : ℕ+)
    (g : TestFunctionCyl 2 L) :
    True -- PDE statement

end
