/-
  Pphi2.Polynomial
  The interaction polynomial P(τ) and its Wick-ordered version P(τ, c).

  Reference: DDJ Section 1, Eq. (1.1) and Eq. (2.4).
-/
import Pphi2.Basic

noncomputable section

/-! ## The interaction polynomial -/

/-- Data for a P(Φ)₂ model: an even-degree polynomial P bounded from below. -/
structure InteractionPolynomial where
  /-- Degree n ≥ 4, n even. -/
  n : ℕ
  hn_ge : 4 ≤ n
  hn_even : Even n
  /-- Coefficients a_0, ..., a_{n-1}. The leading coefficient a_n = 1/n. -/
  coeff : Fin n → ℝ

/-- Evaluate P(τ) = (1/n)τⁿ + Σ_{m<n} a_m τᵐ. -/
def InteractionPolynomial.eval (P : InteractionPolynomial) (τ : ℝ) : ℝ :=
  (1 / P.n : ℝ) * τ ^ P.n + ∑ m : Fin P.n, P.coeff m * τ ^ (m : ℕ)

/-- The Wick-ordered polynomial P(τ, c).
    P(τ, c) = Σ_{m=0}^n a_m Σ_{k=0}^{⌊m/2⌋} (-1)^k m!/(m-2k)!k!2^k c^k τ^{m-2k}.
    DDJ Eq. (2.4). -/
def InteractionPolynomial.evalWick (P : InteractionPolynomial) (τ c : ℝ) : ℝ := sorry

/-- Derivative P'(τ, c) = ∂_τ P(τ, c). -/
def InteractionPolynomial.evalWick' (P : InteractionPolynomial) (τ c : ℝ) : ℝ := sorry

/-- P(τ, c) ≥ τⁿ/(2n) - A·c^{n/2} for some constant A depending only on P.
    DDJ Lemma 2.3. -/
theorem InteractionPolynomial.polynomial_lower_bound (P : InteractionPolynomial) :
    ∃ A : ℝ, 0 < A ∧ ∀ τ c : ℝ, 1 < c →
      P.evalWick τ c ≥ -A * c ^ (P.n / 2) := by
  sorry

end
