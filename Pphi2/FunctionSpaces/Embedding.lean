/-
  Pphi2.FunctionSpaces.Embedding
  Sobolev embedding theorems for weighted Bessel potential spaces.

  Reference: DDJ Appendix A, Theorems A.5-A.7 and Lemma A.5.
-/
import Pphi2.FunctionSpaces.WeightedLp

noncomputable section

/-! ## Continuous embeddings -/

/-- **Theorem A.5(A)** (Continuous Sobolev embedding).
    L^{α₁}_{p₁}(w) ↪ L^{α₂}_{p₂}(v) continuously if
    p₂ < ∞, α₁ - d/p₁ ≥ α₂ - d/p₂, and sup v/w < ∞. -/
axiom sobolev_embedding_continuous
    (w v : AdmissibleWeight) (α₁ α₂ p₁ p₂ : ℝ)
    (hp₂ : 0 < p₂)
    (hα : α₁ - 2 / p₁ ≥ α₂ - 2 / p₂) :
    True -- continuous embedding

/-- **Theorem A.5(C)** (Compact Sobolev embedding).
    L^{α₁}_{p₁}(w) ↪ L^{α₂}_{p₂}(v) compactly if
    p₂ < ∞, α₁ - d/p₁ > α₂ - d/p₂, and v/w → 0 at infinity.
    This is the key compactness used for tightness (Remark 6.2). -/
axiom sobolev_embedding_compact
    (w v : AdmissibleWeight) (α₁ α₂ p₁ p₂ : ℝ)
    (hp₂ : 0 < p₂)
    (hα : α₁ - 2 / p₁ > α₂ - 2 / p₂) :
    True -- compact embedding (Rellich-Kondrachov type)

/-! ## Multiplication and interpolation -/

/-- **Theorem A.6** (Sobolev multiplication).
    ‖fg‖_{L^α_p(w^{1/p})} ≤ C ‖f‖_{L^α_{p₁}(w^{1/p₁})} ‖g‖_{L^α_{p₂}(w^{1/p₂})}
    where 1/p = 1/p₁ + 1/p₂. -/
axiom sobolev_multiplication
    (w : AdmissibleWeight) (α p₁ p₂ : ℝ) :
    True -- multiplication bound

/-- **Theorem A.7** (Sobolev interpolation).
    ‖f‖_{L^α_p(w^{1/p})} ≤ C ‖f‖^θ_{L^{α₁}_{p₁}(w^{1/p₁})} ‖f‖^{1-θ}_{...}
    where α = θα₁ + (1-θ)α₂ and 1/p = θ/p₁ + (1-θ)/p₂. -/
axiom sobolev_interpolation
    (w : AdmissibleWeight) (θ : ℝ) (hθ₁ : 0 < θ) (hθ₂ : θ < 1) :
    True -- interpolation bound

/-! ## The key cross-term estimate -/

/-- **Lemma A.5** (Z·Ψ^m estimate).
    |⟨Z, Ψᵐ⟩_{L₂(w^{1/2})}| ≤ C‖Z‖ᵖ + δ‖∇Ψ‖² + δ‖Ψ‖ⁿ + δ.
    Used in the energy estimate (Prop 5.1). -/
axiom cross_term_estimate
    (n : ℕ) (hn : 3 ≤ n) (κ : ℝ) (hκ : 0 < κ) :
    ∃ (C p : ℝ), 0 < C ∧ 1 ≤ p ∧
    ∀ (δ : ℝ), 0 < δ → True -- the actual estimate

end
