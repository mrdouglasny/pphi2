/-
  Pphi2.Polynomial
  The interaction polynomial P(τ) and its Wick-ordered version P(τ, c).

  Reference: DDJ Section 1, Eq. (1.1) and Eq. (2.4).
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin

noncomputable section

/-! ## The interaction polynomial -/

/-- Data for a P(Φ)₂ model: an even polynomial P bounded from below.

The polynomial P(τ) = (1/n)τⁿ + Σ aₘτᵐ has even degree n ≥ 4 and only
even-power terms (odd coefficients vanish). This ensures P(τ) = P(-τ),
giving the Z₂ symmetry φ → -φ that is essential for:
- Reality of the generating functional (Im Z[f] = 0)
- Clustering → ergodicity via Cesàro averaging

Reference: Simon, *The P(φ)₂ Euclidean QFT*, §II.3;
Glimm-Jaffe, *Quantum Physics*, §6.1. -/
structure InteractionPolynomial where
  /-- Degree n ≥ 4, n even. -/
  n : ℕ
  hn_ge : 4 ≤ n
  hn_even : Even n
  /-- Coefficients a_0, ..., a_{n-1}. The leading coefficient a_n = 1/n. -/
  coeff : Fin n → ℝ
  /-- Odd-power coefficients vanish: P is an even function. -/
  coeff_odd_eq_zero : ∀ m : Fin n, Odd (m : ℕ) → coeff m = 0

/-- Evaluate P(τ) = (1/n)τⁿ + Σ_{m<n} a_m τᵐ. -/
def InteractionPolynomial.eval (P : InteractionPolynomial) (τ : ℝ) : ℝ :=
  (1 / P.n : ℝ) * τ ^ P.n + ∑ m : Fin P.n, P.coeff m * τ ^ (m : ℕ)

/-- P is an even function: P(-τ) = P(τ). -/
theorem InteractionPolynomial.eval_neg (P : InteractionPolynomial) (τ : ℝ) :
    P.eval (-τ) = P.eval τ := by
  simp only [InteractionPolynomial.eval]
  congr 1
  · -- Leading term: (-τ)^n = τ^n since n is even
    congr 1
    exact Even.neg_pow P.hn_even τ
  · -- Sum: each term aₘ(-τ)^m = aₘτ^m (odd coeff vanish, even powers absorb sign)
    apply Finset.sum_congr rfl
    intro m _
    by_cases hm : Odd (m : ℕ)
    · simp [P.coeff_odd_eq_zero m hm]
    · rw [Nat.not_odd_iff_even] at hm
      congr 1
      exact Even.neg_pow hm τ

/-- The Wick-ordered polynomial P(τ, c).
    P(τ, c) = Σ_{m=0}^n a_m Σ_{k=0}^{⌊m/2⌋} (-1)^k m!/(m-2k)!k!2^k c^k τ^{m-2k}.
    DDJ Eq. (2.4). -/
def InteractionPolynomial.evalWick (P : InteractionPolynomial) (τ _c : ℝ) : ℝ :=
  P.eval τ  -- Placeholder: should be the full Wick-ordered evaluation.
  -- The actual Wick ordering is implemented in WickPolynomial.lean as `wickPolynomial`.
  -- This definition exists for the DDJ reference; downstream code uses `wickPolynomial`.

/-- Derivative P'(τ, c) = ∂_τ P(τ, c). Finite-difference approximation. -/
def InteractionPolynomial.evalWick' (P : InteractionPolynomial) (τ _c : ℝ) : ℝ :=
  P.n * τ ^ (P.n - 1) + ∑ m : Fin P.n, (m : ℝ) * P.coeff m * τ ^ ((m : ℕ) - 1)
  -- Placeholder derivative of P.eval. The actual Wick-ordered derivative
  -- would use wickMonomial derivatives; not currently needed downstream.


end
