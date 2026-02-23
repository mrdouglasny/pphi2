/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Wick-Ordered Polynomials on the Lattice

Defines Wick ordering of polynomials with respect to a Gaussian measure with
covariance parameter `c`. Wick ordering subtracts self-contractions, making
`:φ^n:` orthogonal to lower Wick monomials in L²(μ_GFF).

## Main definitions

- `wickMonomial n c x` — the Wick-ordered monomial `:x^n:_c`
- `wickPolynomial P c x` — Wick-ordered interaction polynomial

## Mathematical background

The Wick-ordered monomial `:x^n:_c` with respect to a Gaussian of variance c
is the probabilist's Hermite polynomial scaled by c:

  `:x^n:_c = c^{n/2} · He_n(x / √c)`

where He_n is the probabilist's Hermite polynomial (Mathlib's `Polynomial.hermite`).

Equivalently, via the recursion:
  `:x^0:   = 1`
  `:x^1:   = x`
  `:x^{n+1}: = x · :x^n: - n·c · :x^{n-1}:`

The key property: `E_μ[:x^n:] = 0` for n ≥ 1 when μ = N(0, c).

## References

- Simon, *The P(φ)₂ Euclidean QFT*, §I.3 (Wick ordering)
- Glimm-Jaffe, *Quantum Physics*, §8.6
-/

import Pphi2.Polynomial
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open Real

namespace Pphi2

/-! ## Wick-ordered monomials -/

/-- The Wick-ordered monomial `:x^n:_c` with variance parameter `c`.

Defined via the recursion:
  `:x^0: = 1`, `:x^1: = x`, `:x^{n+2}: = x · :x^{n+1}: - (n+1)·c · :x^n:`

This equals `c^{n/2} · He_n(x/√c)` where He_n is the probabilist's Hermite
polynomial, but the recursive definition avoids division by zero when c = 0
and is more convenient for computation. -/
def wickMonomial : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 1
  | 1, _, x => x
  | n + 2, c, x => x * wickMonomial (n + 1) c x - (n + 1 : ℝ) * c * wickMonomial n c x

@[simp]
theorem wickMonomial_zero (c x : ℝ) : wickMonomial 0 c x = 1 := rfl

@[simp]
theorem wickMonomial_one (c x : ℝ) : wickMonomial 1 c x = x := rfl

theorem wickMonomial_succ_succ (n : ℕ) (c x : ℝ) :
    wickMonomial (n + 2) c x =
    x * wickMonomial (n + 1) c x - (n + 1 : ℝ) * c * wickMonomial n c x := rfl

/-- Wick monomials at c = 0 are just ordinary monomials. -/
theorem wickMonomial_zero_variance : ∀ (n : ℕ) (x : ℝ),
    wickMonomial n 0 x = x ^ n
  | 0, x => by simp
  | 1, x => by simp
  | n + 2, x => by
    have h1 := wickMonomial_zero_variance (n + 1) x
    have h2 := wickMonomial_zero_variance n x
    simp only [wickMonomial_succ_succ, mul_zero, zero_mul, sub_zero, h1, h2]
    ring

/-- Low-degree examples for verification:
  `:x²: = x² - c`, `:x³: = x³ - 3cx`, `:x⁴: = x⁴ - 6cx² + 3c²` -/
@[simp]
theorem wickMonomial_two (c x : ℝ) :
    wickMonomial 2 c x = x ^ 2 - c := by
  simp [wickMonomial_succ_succ]; ring

@[simp]
theorem wickMonomial_three (c x : ℝ) :
    wickMonomial 3 c x = x ^ 3 - 3 * c * x := by
  simp [wickMonomial_succ_succ, wickMonomial_two]; ring

@[simp]
theorem wickMonomial_four (c x : ℝ) :
    wickMonomial 4 c x = x ^ 4 - 6 * c * x ^ 2 + 3 * c ^ 2 := by
  simp [wickMonomial_succ_succ, wickMonomial_three]; ring

/-! ## Connection to Hermite polynomials

When c > 0, the Wick monomial equals the scaled Hermite polynomial:
  `:x^n:_c = c^{n/2} · He_n(x / √c)`

This is axiomatized; the recursive definition and the Hermite definition
agree by induction using the Hermite recurrence `He_{n+1}(t) = t·He_n(t) - n·He_{n-1}(t)`. -/

/-- Wick monomials are Hermite polynomials scaled by the variance. -/
axiom wickMonomial_eq_hermite (n : ℕ) (c : ℝ) (hc : 0 < c) (x : ℝ) :
    wickMonomial n c x =
    c ^ ((n : ℝ) / 2) * ((Polynomial.hermite n).map (Int.castRingHom ℝ)).eval
      (x / Real.sqrt c)

/-! ## Wick-ordered interaction polynomial -/

/-- The Wick-ordered interaction polynomial `:P(x):_c`.

Given `P(τ) = (1/n)τⁿ + Σ_{m<n} a_m τᵐ`, the Wick-ordered version replaces
each monomial τᵐ with `:τ^m:_c`:

  `:P(x):_c = (1/n) · :x^n:_c + Σ_{m<n} a_m · :x^m:_c`

This subtracts the self-contraction divergences. -/
def wickPolynomial (P : InteractionPolynomial) (c x : ℝ) : ℝ :=
  (1 / P.n : ℝ) * wickMonomial P.n c x +
  ∑ m : Fin P.n, P.coeff m * wickMonomial (m : ℕ) c x

/-- Wick ordering at c = 0 recovers the original polynomial. -/
theorem wickPolynomial_zero_variance (P : InteractionPolynomial) (x : ℝ) :
    wickPolynomial P 0 x = P.eval x := by
  unfold wickPolynomial InteractionPolynomial.eval
  congr 1
  · rw [wickMonomial_zero_variance]
  · apply Finset.sum_congr rfl
    intro m _
    rw [wickMonomial_zero_variance]

/-- The Wick polynomial is bounded below (crucial for measure well-definedness).

Since P has even degree n ≥ 4 with positive leading coefficient 1/n,
and Wick ordering only changes terms of degree < n, we have
`:P(x):_c = (1/n)x^n + lower order`, which is bounded below.

More precisely: `:P(x):_c ≥ -A` for some constant A depending on P and c.

Proof outline: For |x| ≥ R (large), the leading x^n term dominates.
For |x| ≤ R, the polynomial is continuous on a compact set, hence bounded below.
-/
axiom wickPolynomial_bounded_below (P : InteractionPolynomial) (c : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ,
    wickPolynomial P c x ≥ -A

end Pphi2

end
