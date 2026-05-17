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
import SchwartzNuclear.HermiteWick
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Polynomial.EraseLead

noncomputable section

open Real Polynomial

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
  simp [wickMonomial_succ_succ]; ring

@[simp]
theorem wickMonomial_four (c x : ℝ) :
    wickMonomial 4 c x = x ^ 4 - 6 * c * x ^ 2 + 3 * c ^ 2 := by
  simp [wickMonomial_succ_succ]; ring

/-! ## Connection to Hermite polynomials

When c > 0, the Wick monomial equals the scaled Hermite polynomial:
  `:x^n:_c = c^{n/2} · He_n(x / √c)`

Proved via `wick_eq_hermiteR_rpow` from gaussian-field's HermiteWick module,
which establishes this by induction using the Hermite three-term recurrence.
The bridge lemma `wickMonomial_eq_root` shows that `Pphi2.wickMonomial`
agrees with the root-level `wickMonomial` from gaussian-field. -/

/-- Pphi2's Wick monomial agrees with the gaussian-field definition. -/
private theorem wickMonomial_eq_root : ∀ (n : ℕ) (c x : ℝ),
    wickMonomial n c x = _root_.wickMonomial n c x
  | 0, _, _ => rfl
  | 1, _, _ => rfl
  | n + 2, c, x => by
    simp only [Pphi2.wickMonomial_succ_succ, _root_.wickMonomial_succ_succ]
    rw [wickMonomial_eq_root (n + 1), wickMonomial_eq_root n]

/-- Wick monomials are Hermite polynomials scaled by the variance.

Proved via the Hermite three-term recurrence (gaussian-field HermiteWick). -/
theorem wickMonomial_eq_hermite (n : ℕ) (c : ℝ) (hc : 0 < c) (x : ℝ) :
    wickMonomial n c x =
    c ^ ((n : ℝ) / 2) * ((Polynomial.hermite n).map (Int.castRingHom ℝ)).eval
      (x / Real.sqrt c) := by
  rw [wickMonomial_eq_root]
  exact wick_eq_hermiteR_rpow n c hc x

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

/-! ## Wick monomial as a formal polynomial

To prove bounded below, we represent the Wick monomial as a `Polynomial ℝ`
and use degree/leading coefficient analysis. -/

/-- The Wick-ordered monomial as a formal polynomial in one variable. -/
private def wickMonomialPoly : ℕ → ℝ → Polynomial ℝ
  | 0, _ => 1
  | 1, _ => X
  | n + 2, c => X * wickMonomialPoly (n + 1) c -
                 C ((n + 1 : ℝ) * c) * wickMonomialPoly n c

/-- The formal polynomial evaluates to the Wick monomial. -/
private theorem wickMonomialPoly_eval : ∀ (n : ℕ) (c x : ℝ),
    (wickMonomialPoly n c).eval x = wickMonomial n c x
  | 0, _, x => by simp [wickMonomialPoly]
  | 1, _, x => by simp [wickMonomialPoly]
  | n + 2, c, x => by
    simp only [wickMonomialPoly, wickMonomial_succ_succ,
      eval_X, eval_C, eval_mul, eval_sub,
      wickMonomialPoly_eval (n + 1) c x, wickMonomialPoly_eval n c x]

/-- wickMonomialPoly n c is monic of degree n. Proved by joint induction. -/
private theorem wickMonomialPoly_monic_deg : ∀ (n : ℕ) (c : ℝ),
    (wickMonomialPoly n c).Monic ∧ (wickMonomialPoly n c).natDegree = n
  | 0, _ => ⟨monic_one, by simp [wickMonomialPoly, natDegree_one]⟩
  | 1, _ => ⟨monic_X, by simp [wickMonomialPoly, natDegree_X]⟩
  | n + 2, c => by
    obtain ⟨hm1, hd1⟩ := wickMonomialPoly_monic_deg (n + 1) c
    obtain ⟨hm0, hd0⟩ := wickMonomialPoly_monic_deg n c
    simp only [wickMonomialPoly]
    -- After simp, the cast (n+1 : ℝ) normalizes to (↑n + 1)
    have hm_xp : (X * wickMonomialPoly (n + 1) c).Monic := monic_X.mul hm1
    have hd_xp : (X * wickMonomialPoly (n + 1) c).natDegree = n + 2 := by
      rw [natDegree_X_mul hm1.ne_zero, hd1]
    have hd_cp : (C (((n : ℝ) + 1) * c) * wickMonomialPoly n c).natDegree ≤ n := by
      calc _ ≤ (C _).natDegree + (wickMonomialPoly n c).natDegree := natDegree_mul_le
        _ = 0 + n := by rw [natDegree_C, hd0]
        _ = n := zero_add n
    have hlt_nat : (C (((n : ℝ) + 1) * c) * wickMonomialPoly n c).natDegree <
        (X * wickMonomialPoly (n + 1) c).natDegree := by
      rw [hd_xp]; omega
    constructor
    · -- Monic: subtraction preserves monicity when subtrahend has smaller degree
      rw [sub_eq_add_neg]
      apply hm_xp.add_of_left
      rw [degree_neg]
      calc degree (C (((n : ℝ) + 1) * c) * wickMonomialPoly n c)
          ≤ ↑(C (((n : ℝ) + 1) * c) * wickMonomialPoly n c).natDegree := degree_le_natDegree
        _ ≤ ↑n := by exact_mod_cast hd_cp
        _ < ↑(n + 2) := by exact_mod_cast (show n < n + 2 by omega)
        _ = degree (X * wickMonomialPoly (n + 1) c) := by
            rw [degree_eq_natDegree hm_xp.ne_zero, hd_xp]
    · -- natDegree: subtraction preserves degree when subtrahend has smaller degree
      rw [natDegree_sub_eq_left_of_natDegree_lt hlt_nat, hd_xp]

private theorem wickMonomialPoly_monic (n : ℕ) (c : ℝ) :
    (wickMonomialPoly n c).Monic :=
  (wickMonomialPoly_monic_deg n c).1

private theorem wickMonomialPoly_natDegree (n : ℕ) (c : ℝ) :
    (wickMonomialPoly n c).natDegree = n :=
  (wickMonomialPoly_monic_deg n c).2

/-! ## Wick polynomial as a formal polynomial -/

/-- The Wick-ordered interaction polynomial as a formal polynomial. -/
private def wickPolynomialPoly (P : InteractionPolynomial) (c : ℝ) : Polynomial ℝ :=
  C (1 / P.n : ℝ) * wickMonomialPoly P.n c +
  ∑ m : Fin P.n, C (P.coeff m) * wickMonomialPoly (m : ℕ) c

/-- The formal polynomial evaluates to the Wick polynomial. -/
private theorem wickPolynomialPoly_eval (P : InteractionPolynomial) (c x : ℝ) :
    (wickPolynomialPoly P c).eval x = wickPolynomial P c x := by
  simp only [wickPolynomialPoly, wickPolynomial, eval_add, eval_mul,
    eval_C, eval_finset_sum, wickMonomialPoly_eval]

/-! ### Properties of wickPolynomialPoly needed for bounded below -/

private theorem wickPolynomialPoly_leading_natDegree (P : InteractionPolynomial) (c : ℝ) :
    (C (1 / P.n : ℝ) * wickMonomialPoly P.n c).natDegree = P.n := by
  have h1n : (1 / (P.n : ℝ)) ≠ 0 := by
    apply div_ne_zero one_ne_zero
    exact_mod_cast (show P.n ≠ 0 by have := P.hn_ge; omega)
  rw [natDegree_C_mul h1n, wickMonomialPoly_natDegree]

private theorem wickPolynomialPoly_leading_ne_zero (P : InteractionPolynomial) (c : ℝ) :
    C (1 / P.n : ℝ) * wickMonomialPoly P.n c ≠ 0 := by
  intro h
  have := wickPolynomialPoly_leading_natDegree P c
  rw [h, natDegree_zero] at this
  have := P.hn_ge; omega

private theorem wickPolynomialPoly_sum_natDegree_lt (P : InteractionPolynomial) (c : ℝ) :
    (∑ m : Fin P.n, C (P.coeff m) * wickMonomialPoly (m : ℕ) c).natDegree < P.n := by
  have hn_pos : 0 < P.n := by have := P.hn_ge; omega
  suffices h : (∑ m : Fin P.n, C (P.coeff m) * wickMonomialPoly (m : ℕ) c).natDegree
      ≤ P.n - 1 by omega
  apply le_trans (natDegree_sum_le _ _)
  apply Finset.sup_le
  intro m _
  calc (C (P.coeff m) * wickMonomialPoly (m : ℕ) c).natDegree
      ≤ (C (P.coeff m)).natDegree + (wickMonomialPoly (m : ℕ) c).natDegree := natDegree_mul_le
    _ = 0 + (m : ℕ) := by rw [natDegree_C, wickMonomialPoly_natDegree]
    _ = (m : ℕ) := zero_add _
    _ ≤ P.n - 1 := by have := m.is_lt; omega

private theorem wickPolynomialPoly_natDegree (P : InteractionPolynomial) (c : ℝ) :
    (wickPolynomialPoly P c).natDegree = P.n := by
  unfold wickPolynomialPoly
  have h_lead := wickPolynomialPoly_leading_natDegree P c
  have h_sum := wickPolynomialPoly_sum_natDegree_lt P c
  have hlt : (∑ m : Fin P.n, C (P.coeff m) * wickMonomialPoly (↑m) c).natDegree <
      (C (1 / (P.n : ℝ)) * wickMonomialPoly P.n c).natDegree := by rw [h_lead]; exact h_sum
  rw [natDegree_add_eq_left_of_natDegree_lt hlt, h_lead]

private theorem wickPolynomialPoly_leadingCoeff (P : InteractionPolynomial) (c : ℝ) :
    (wickPolynomialPoly P c).leadingCoeff = 1 / P.n := by
  unfold wickPolynomialPoly
  have hne := wickPolynomialPoly_leading_ne_zero P c
  have h_lead := wickPolynomialPoly_leading_natDegree P c
  have h_sum := wickPolynomialPoly_sum_natDegree_lt P c
  rw [leadingCoeff_add_of_degree_lt']
  · rw [leadingCoeff_mul, leadingCoeff_C, (wickMonomialPoly_monic P.n c).leadingCoeff, mul_one]
  · -- degree of sum < degree of leading term
    calc degree (∑ m : Fin P.n, C (P.coeff m) * wickMonomialPoly (m : ℕ) c)
        ≤ ↑(∑ m : Fin P.n, C (P.coeff m) * wickMonomialPoly (m : ℕ) c).natDegree :=
          degree_le_natDegree
      _ < ↑P.n := by exact_mod_cast h_sum
      _ = ↑(C (1 / ↑P.n : ℝ) * wickMonomialPoly P.n c).natDegree := by rw [h_lead]
      _ = degree (C (1 / ↑P.n : ℝ) * wickMonomialPoly P.n c) := by
          rw [degree_eq_natDegree hne]

/-! ## Bounded below: the main result

Strategy: The wickPolynomial is a polynomial function of x with even degree ≥ 4
and positive leading coefficient 1/n. For large |x|, the leading term dominates.
On bounded intervals, continuity gives a finite minimum. -/

/-- A polynomial with even degree ≥ 2 and positive leading coefficient
is bounded below.

Proof: Combine ‖p.eval‖ → ∞ (from `tendsto_norm_atTop`) with
"eventually nonneg" (even degree + positive leading coeff) to get
p.eval → +∞ on cocompact, then `Continuous.exists_forall_le` gives
the global minimum. -/
theorem poly_even_degree_bounded_below (p : ℝ[X])
    (hd_pos : 0 < p.natDegree) (hd_even : Even p.natDegree)
    (hlc : 0 < p.leadingCoeff) :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, p.eval x ≥ -A := by
  have hp_ne : p ≠ 0 := by intro h; rw [h, natDegree_zero] at hd_pos; omega
  have hdeg : (0 : WithBot ℕ) < p.degree := by
    rw [degree_eq_natDegree hp_ne]; exact_mod_cast hd_pos
  -- Step 1: Global minimum exists from continuity + signed tendency
  suffices htend : Filter.Tendsto (fun x : ℝ => p.eval x) (Filter.cocompact ℝ) Filter.atTop by
    obtain ⟨x₀, hx₀⟩ := p.continuous.exists_forall_le htend
    exact ⟨|p.eval x₀| + 1, by positivity, fun x => by
      have := hx₀ x; linarith [neg_abs_le (p.eval x₀)]⟩
  -- Step 2: ‖p.eval‖ → ∞ on cocompact (from Mathlib)
  have hnorm : Filter.Tendsto (fun x : ℝ => ‖p.eval x‖) (Filter.cocompact ℝ) Filter.atTop :=
    p.tendsto_norm_atTop hdeg tendsto_norm_cocompact_atTop
  -- Step 3: p.eval x ≥ 0 for large |x| (even degree + positive leading coeff)
  have hpos : ∀ᶠ x in Filter.cocompact ℝ, (0 : ℝ) ≤ p.eval x := by
    set n := p.natDegree
    set lc := p.leadingCoeff
    -- R is chosen so that for |x| ≥ R, the leading term dominates
    let C : ℝ := (Finset.range n).sum (fun i => |p.coeff i|)
    let R : ℝ := max 1 (C / lc + 1)
    have hclaim : ∀ x : ℝ, R ≤ |x| → 0 ≤ p.eval x := by
      intro x hxR
      have hx1 : 1 ≤ |x| := le_trans (le_max_left 1 _) hxR
      -- Decompose: p.eval x = lc * x^n + Σ_{i<n} p.coeff i * x^i
      have hp_eq : p.eval x = lc * x ^ n +
          (Finset.range n).sum (fun i => p.coeff i * x ^ i) := by
        simp only [eval_eq_sum_range, Finset.sum_range_succ]
        change _ = p.leadingCoeff * x ^ p.natDegree + _
        rw [Polynomial.leadingCoeff]; ring
      -- x^n = |x|^n (even degree)
      have hxn_eq : x ^ n = |x| ^ n := (hd_even.pow_abs x).symm
      -- Bound: |Σ_{i<n} p.coeff i * x^i| ≤ C * |x|^(n-1)
      have hrest_bound : |(Finset.range n).sum (fun i => p.coeff i * x ^ i)|
          ≤ C * |x| ^ (n - 1) := by
        calc |(Finset.range n).sum fun i => p.coeff i * x ^ i|
            ≤ (Finset.range n).sum fun i => |p.coeff i * x ^ i| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = (Finset.range n).sum fun i => |p.coeff i| * |x| ^ i := by
              congr 1; ext i; rw [abs_mul, abs_pow]
          _ ≤ (Finset.range n).sum fun i => |p.coeff i| * |x| ^ (n - 1) := by
              apply Finset.sum_le_sum; intro i hi
              exact mul_le_mul_of_nonneg_left
                (pow_le_pow_right₀ hx1 (by have := Finset.mem_range.mp hi; omega))
                (abs_nonneg _)
          _ = C * |x| ^ (n - 1) := by
              change _ = (Finset.range n).sum (fun i => |p.coeff i|) * _
              rw [← Finset.sum_mul]
      -- lc * |x|^n = (lc * |x|) * |x|^(n-1)
      have hlead_split : lc * |x| ^ n = (lc * |x|) * |x| ^ (n - 1) := by
        have : |x| ^ n = |x| ^ (n - 1) * |x| := by
          conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
        rw [this]; ring
      -- lc * R > C, so lc * |x| ≥ lc * R > C
      have hR_bound : C < lc * R := by
        have hCR : C / lc < R := lt_of_lt_of_le (by linarith) (le_max_right 1 _)
        rwa [div_lt_iff₀ hlc, mul_comm] at hCR
      have hlcx_bound : C ≤ lc * |x| :=
        le_of_lt (lt_of_lt_of_le hR_bound (mul_le_mul_of_nonneg_left hxR (le_of_lt hlc)))
      -- Combine: p.eval x ≥ lc*|x|^n - C*|x|^(n-1) = (lc*|x| - C)*|x|^(n-1) ≥ 0
      rw [hp_eq, hxn_eq, hlead_split]
      have hxn1 : 0 ≤ |x| ^ (n - 1) := pow_nonneg (abs_nonneg x) _
      have hrest_lower : -(C * |x| ^ (n - 1)) ≤
          (Finset.range n).sum (fun i => p.coeff i * x ^ i) :=
        neg_le_of_abs_le hrest_bound
      nlinarith [mul_le_mul_of_nonneg_right hlcx_bound hxn1]
    -- Convert to Eventually on cocompact
    rw [Filter.Eventually, Filter.mem_cocompact']
    refine ⟨Metric.closedBall 0 R, isCompact_closedBall 0 R, fun x hx => ?_⟩
    -- hx : x ∈ {x | 0 ≤ p.eval x}ᶜ, i.e., ¬(0 ≤ p.eval x)
    -- Need to show x ∈ closedBall 0 R, i.e., |x| ≤ R
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hx
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    by_contra hx_far
    push Not at hx_far
    exact hx (hclaim x (le_of_lt hx_far))
  -- Step 4: Combine norm → ∞ with eventually nonneg to get signed tendency
  rw [Filter.tendsto_atTop]
  intro M
  exact ((hnorm.eventually (Filter.eventually_ge_atTop (max M 0))).and hpos).mono
    fun x ⟨hx_norm, hx_pos⟩ => by
      rw [Real.norm_eq_abs, abs_of_nonneg hx_pos] at hx_norm
      exact le_trans (le_max_left M 0) hx_norm

/-- The Wick polynomial is bounded below (crucial for measure well-definedness).

Since P has even degree n ≥ 4 with positive leading coefficient 1/n,
and Wick ordering only changes terms of degree < n, the Wick polynomial
`:P(x):_c = (1/n)x^n + lower order` is bounded below.

The proof converts wickPolynomial to a formal `Polynomial ℝ`, verifies its
degree and leading coefficient, then applies `poly_even_degree_bounded_below`. -/
theorem wickPolynomial_bounded_below (P : InteractionPolynomial) (c : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ,
    wickPolynomial P c x ≥ -A := by
  suffices h : ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, (wickPolynomialPoly P c).eval x ≥ -A by
    obtain ⟨A, hA, hbound⟩ := h
    exact ⟨A, hA, fun x => by rw [← wickPolynomialPoly_eval]; exact hbound x⟩
  apply poly_even_degree_bounded_below
  · -- natDegree > 0
    rw [wickPolynomialPoly_natDegree]; have := P.hn_ge; omega
  · -- natDegree is even
    rw [wickPolynomialPoly_natDegree]; exact P.hn_even
  · -- leading coeff > 0
    rw [wickPolynomialPoly_leadingCoeff]
    apply div_pos one_pos
    exact_mod_cast (show (0 : ℕ) < P.n by have := P.hn_ge; omega)

/-! ## Joint continuity in (c, x) -/

/-- Wick monomials are jointly continuous in (c, x). -/
theorem wickMonomial_continuous₂ : ∀ (n : ℕ),
    Continuous (fun p : ℝ × ℝ => wickMonomial n p.1 p.2)
  | 0 => by simp only [wickMonomial]; exact continuous_const
  | 1 => by simp only [wickMonomial]; exact continuous_snd
  | n + 2 => by
    change Continuous (fun p : ℝ × ℝ =>
      p.2 * wickMonomial (n + 1) p.1 p.2 -
      (↑n + 1) * p.1 * wickMonomial n p.1 p.2)
    exact (continuous_snd.mul (wickMonomial_continuous₂ (n + 1))).sub
      ((continuous_const.mul continuous_fst).mul (wickMonomial_continuous₂ n))

/-- Wick polynomial is jointly continuous in (c, x). -/
theorem wickPolynomial_continuous₂ (P : InteractionPolynomial) :
    Continuous (fun p : ℝ × ℝ => wickPolynomial P p.1 p.2) := by
  unfold wickPolynomial
  apply Continuous.add
  · exact continuous_const.mul (wickMonomial_continuous₂ P.n)
  · apply continuous_finset_sum; intro m _
    exact continuous_const.mul (wickMonomial_continuous₂ m)

/-! ## Coefficient continuity -/

/-- Each coefficient of `wickMonomialPoly n c` is continuous in `c`.
This is because the recurrence involves only polynomial operations in `c`. -/
private theorem wickMonomialPoly_coeff_continuous : ∀ (n i : ℕ),
    Continuous (fun c : ℝ => (wickMonomialPoly n c).coeff i)
  | 0, i => by simp only [wickMonomialPoly]; exact continuous_const
  | 1, i => by simp only [wickMonomialPoly]; exact continuous_const
  | n + 2, i => by
    simp only [wickMonomialPoly, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    apply Continuous.sub
    · -- coeff i (X * wickMonomialPoly (n+1) c)
      cases i with
      | zero =>
        simp only [Polynomial.coeff_X_mul_zero]
        exact continuous_const
      | succ j =>
        simp only [Polynomial.coeff_X_mul]
        exact wickMonomialPoly_coeff_continuous (n + 1) j
    · -- ((n+1) * c) * coeff i (wickMonomialPoly n c)
      exact (continuous_const.mul continuous_id).mul
        (wickMonomialPoly_coeff_continuous n i)

/-- Each coefficient of `wickPolynomialPoly P c` is continuous in `c`. -/
private theorem wickPolynomialPoly_coeff_continuous (P : InteractionPolynomial)
    (i : ℕ) : Continuous (fun c : ℝ => (wickPolynomialPoly P c).coeff i) := by
  -- Extract the coefficient as an explicit expression
  have h_eq : ∀ c, (wickPolynomialPoly P c).coeff i =
      (1 / P.n : ℝ) * (wickMonomialPoly P.n c).coeff i +
      ∑ m : Fin P.n, P.coeff m * (wickMonomialPoly (↑m) c).coeff i := by
    intro c; unfold wickPolynomialPoly
    simp [Polynomial.coeff_add, Polynomial.coeff_C_mul]
  simp_rw [h_eq]
  apply Continuous.add
  · exact continuous_const.mul (wickMonomialPoly_coeff_continuous P.n i)
  · apply continuous_finset_sum; intro m _
    exact continuous_const.mul (wickMonomialPoly_coeff_continuous m i)

/-! ## Uniform bounded below -/

/-- The Wick polynomial is uniformly bounded below for c in a bounded interval.

For large |x|, the leading term (1/n)x^n dominates regardless of c (the
sub-leading coefficients are bounded on [0,C] by coefficient continuity).
On the compact remainder [0,C] × [-R,R], joint continuity gives a finite
minimum. -/
theorem wickPolynomial_uniform_bounded_below
    (P : InteractionPolynomial) (C : ℝ) (hC : 0 ≤ C) :
    ∃ A : ℝ, 0 < A ∧ ∀ (c : ℝ), 0 ≤ c → c ≤ C → ∀ x : ℝ,
    wickPolynomial P c x ≥ -A := by
  set n := P.n with hn_def
  have hn_ge : 4 ≤ n := P.hn_ge
  have hn_even : Even n := P.hn_even
  have hn_pos : 0 < n := by omega
  set lc : ℝ := 1 / n
  have hlc_pos : 0 < lc := div_pos one_pos (by exact_mod_cast hn_pos)
  -- Step 1: Uniform bound on sub-leading coefficient sum
  have hcoeff_sum_cont : Continuous (fun c : ℝ =>
      (Finset.range n).sum (fun i => |(wickPolynomialPoly P c).coeff i|)) :=
    continuous_finset_sum _ fun i _ =>
      (wickPolynomialPoly_coeff_continuous P i).abs
  obtain ⟨c₀, hc₀_mem, hc₀_max⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr hC) hcoeff_sum_cont.continuousOn
  set Mcoeff : ℝ :=
    (Finset.range n).sum (fun i => |(wickPolynomialPoly P c₀).coeff i|)
  have hM_bound : ∀ c ∈ Set.Icc 0 C,
      (Finset.range n).sum (fun i => |(wickPolynomialPoly P c).coeff i|) ≤
        Mcoeff :=
    fun c hc => hc₀_max hc
  have hM_nonneg : 0 ≤ Mcoeff := Finset.sum_nonneg fun i _ => abs_nonneg _
  -- Step 2: For |x| ≥ R, wickPolynomial P c x ≥ 0 (uniformly in c ∈ [0, C])
  set R : ℝ := max 1 (Mcoeff / lc + 1)
  have hR_ge1 : 1 ≤ R := le_max_left 1 _
  have hR_pos : 0 < R := lt_of_lt_of_le one_pos hR_ge1
  have hMR : Mcoeff < lc * R := by
    have : Mcoeff / lc < R :=
      lt_of_lt_of_le (by linarith) (le_max_right 1 _)
    rwa [div_lt_iff₀ hlc_pos, mul_comm] at this
  have hclaim : ∀ c ∈ Set.Icc 0 C, ∀ x : ℝ, R ≤ |x| →
      0 ≤ wickPolynomial P c x := by
    intro c hc x hxR
    have hx1 : 1 ≤ |x| := le_trans hR_ge1 hxR
    rw [← wickPolynomialPoly_eval]
    set p := wickPolynomialPoly P c
    -- Decompose p.eval x = lc * x^n + Σ_{i<n} p.coeff i * x^i
    have hp_deg : p.natDegree = n := wickPolynomialPoly_natDegree P c
    have hp_lc : p.leadingCoeff = lc := wickPolynomialPoly_leadingCoeff P c
    have hcn : p.coeff n = lc := by
      rw [show n = p.natDegree from hp_deg.symm]; exact hp_lc
    have hp_eq : p.eval x = lc * x ^ n +
        (Finset.range n).sum (fun i => p.coeff i * x ^ i) := by
      simp only [eval_eq_sum_range, Finset.sum_range_succ, hp_deg]
      rw [hcn]; ring
    have hxn_eq : x ^ n = |x| ^ n := (hn_even.pow_abs x).symm
    -- |Σ rest| ≤ Mcoeff * |x|^(n-1)
    have hrest_bound : |(Finset.range n).sum (fun i => p.coeff i * x ^ i)|
        ≤ Mcoeff * |x| ^ (n - 1) := by
      calc |(Finset.range n).sum fun i => p.coeff i * x ^ i|
          ≤ (Finset.range n).sum fun i => |p.coeff i| * |x| ^ i := by
            calc _ ≤ (Finset.range n).sum fun i => |p.coeff i * x ^ i| :=
                  Finset.abs_sum_le_sum_abs _ _
              _ = _ := by congr 1; ext i; rw [abs_mul, abs_pow]
        _ ≤ (Finset.range n).sum fun i => |p.coeff i| * |x| ^ (n - 1) := by
            apply Finset.sum_le_sum; intro i hi
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ hx1 (by
                have := Finset.mem_range.mp hi; omega))
              (abs_nonneg _)
        _ = ((Finset.range n).sum fun i => |p.coeff i|) * |x| ^ (n - 1) :=
            (Finset.sum_mul ..).symm
        _ ≤ Mcoeff * |x| ^ (n - 1) :=
            mul_le_mul_of_nonneg_right (hM_bound c hc)
              (pow_nonneg (abs_nonneg x) _)
    -- lc * |x|^n = (lc * |x|) * |x|^(n-1)
    have hlead_split : lc * |x| ^ n = (lc * |x|) * |x| ^ (n - 1) := by
      have : |x| ^ n = |x| ^ (n - 1) * |x| := by
        conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
      rw [this]; ring
    have hlcx_bound : Mcoeff ≤ lc * |x| :=
      le_of_lt (lt_of_lt_of_le hMR
        (mul_le_mul_of_nonneg_left hxR (le_of_lt hlc_pos)))
    -- Combine
    have hxn1 : 0 ≤ |x| ^ (n - 1) := pow_nonneg (abs_nonneg x) _
    have hrest_lower : -(Mcoeff * |x| ^ (n - 1)) ≤
        (Finset.range n).sum (fun i => p.coeff i * x ^ i) :=
      neg_le_of_abs_le hrest_bound
    rw [hp_eq, hxn_eq, hlead_split]
    nlinarith [mul_le_mul_of_nonneg_right hlcx_bound hxn1]
  -- Step 3: On [0,C] × [-R,R], use compactness for a finite minimum
  set K := Set.Icc 0 C ×ˢ Set.Icc (-R) R
  have hK_compact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hK_ne : K.Nonempty :=
    ⟨⟨0, 0⟩, Set.mk_mem_prod (Set.left_mem_Icc.mpr hC)
      ⟨by linarith, by linarith⟩⟩
  set f : ℝ × ℝ → ℝ := fun p => wickPolynomial P p.1 p.2
  have hf_cont : Continuous f := wickPolynomial_continuous₂ P
  obtain ⟨p₀, hp₀_mem, hp₀_min⟩ := hK_compact.exists_isMinOn hK_ne
    hf_cont.continuousOn
  -- Take A = |f(p₀)| + 1
  refine ⟨|f p₀| + 1, by positivity, fun c hc0 hcC x => ?_⟩
  by_cases hx : R ≤ |x|
  · -- Large |x|: wickPolynomial ≥ 0 ≥ -A
    have := hclaim c ⟨hc0, hcC⟩ x hx
    linarith [abs_nonneg (f p₀)]
  · -- Bounded |x|: wickPolynomial ≥ f(p₀) ≥ -|f(p₀)| ≥ -A
    push Not at hx
    have hx_bound : x ∈ Set.Icc (-R) R := by
      rw [Set.mem_Icc]; constructor
      · linarith [(abs_lt.mp hx).1]
      · linarith [(abs_lt.mp hx).2]
    have hmem : (c, x) ∈ K := Set.mk_mem_prod ⟨hc0, hcC⟩ hx_bound
    have h_min : f p₀ ≤ f (c, x) := hp₀_min hmem
    -- f (c, x) = wickPolynomial P c x
    change wickPolynomial P p₀.1 p₀.2 ≤ wickPolynomial P c x at h_min
    linarith [neg_abs_le (f p₀)]

/-! ## General lower bound with explicit `c`-growth -/

/-- A rescaled unit-variance polynomial family that appears after factoring
`c ^ (P.n / 2)` out of `wickPolynomial P c x` for `c > 0`. The parameter
`s = 1 / √c` ranges over `[0, 1]` when `c ≥ 1`. -/
private def normalizedWickPolynomialPoly (P : InteractionPolynomial) (s : ℝ) : Polynomial ℝ :=
  C (1 / P.n : ℝ) * wickMonomialPoly P.n 1 +
  ∑ m : Fin P.n, C (P.coeff m * s ^ (P.n - (m : ℕ))) * wickMonomialPoly (m : ℕ) 1

private theorem normalizedWickPolynomialPoly_eval
    (P : InteractionPolynomial) (s x : ℝ) :
    (normalizedWickPolynomialPoly P s).eval x =
      (1 / P.n : ℝ) * wickMonomial P.n 1 x +
      ∑ m : Fin P.n, P.coeff m * s ^ (P.n - (m : ℕ)) * wickMonomial (m : ℕ) 1 x := by
  unfold normalizedWickPolynomialPoly
  simp only [eval_add, eval_mul, eval_C, eval_finset_sum, wickMonomialPoly_eval]

private theorem normalizedWickPolynomialPoly_leading_natDegree
    (P : InteractionPolynomial) (_ : ℝ) :
    (C (1 / P.n : ℝ) * wickMonomialPoly P.n 1).natDegree = P.n := by
  have h1n : (1 / P.n : ℝ) ≠ 0 := by
    have hP : (0 : ℕ) < P.n := by
      have := P.hn_ge
      omega
    positivity
  rw [natDegree_C_mul h1n, wickMonomialPoly_natDegree]

private theorem normalizedWickPolynomialPoly_leading_ne_zero
    (P : InteractionPolynomial) (s : ℝ) :
    C (1 / P.n : ℝ) * wickMonomialPoly P.n 1 ≠ 0 := by
  intro h
  have hdeg := normalizedWickPolynomialPoly_leading_natDegree P s
  rw [h, natDegree_zero] at hdeg
  have hzero : P.n = 0 := by simpa using hdeg.symm
  have := P.hn_ge
  omega

private theorem normalizedWickPolynomialPoly_sum_natDegree_lt
    (P : InteractionPolynomial) (s : ℝ) :
    (∑ m : Fin P.n, C (P.coeff m * s ^ (P.n - (m : ℕ))) * wickMonomialPoly (m : ℕ) 1).natDegree <
      P.n := by
  have hn_pos : 0 < P.n := by
    have := P.hn_ge
    omega
  suffices h :
      (∑ m : Fin P.n, C (P.coeff m * s ^ (P.n - (m : ℕ))) * wickMonomialPoly (m : ℕ) 1).natDegree
        ≤ P.n - 1 by
    omega
  apply le_trans (natDegree_sum_le _ _)
  apply Finset.sup_le
  intro m hm
  calc
    (C (P.coeff m * s ^ (P.n - (m : ℕ))) * wickMonomialPoly (m : ℕ) 1).natDegree
        ≤
          (C (P.coeff m * s ^ (P.n - (m : ℕ)))).natDegree +
            (wickMonomialPoly (m : ℕ) 1).natDegree :=
          natDegree_mul_le
    _ = 0 + (m : ℕ) := by rw [natDegree_C, wickMonomialPoly_natDegree]
    _ = (m : ℕ) := zero_add _
    _ ≤ P.n - 1 := by
      have := m.is_lt
      omega

private theorem normalizedWickPolynomialPoly_natDegree
    (P : InteractionPolynomial) (s : ℝ) :
    (normalizedWickPolynomialPoly P s).natDegree = P.n := by
  unfold normalizedWickPolynomialPoly
  have h_lead := normalizedWickPolynomialPoly_leading_natDegree P s
  have h_sum := normalizedWickPolynomialPoly_sum_natDegree_lt P s
  have hlt :
      (∑ m : Fin P.n, C (P.coeff m * s ^ (P.n - (m : ℕ))) * wickMonomialPoly (↑m) 1).natDegree <
        (C (1 / (P.n : ℝ)) * wickMonomialPoly P.n 1).natDegree := by
    rw [h_lead]
    exact h_sum
  rw [natDegree_add_eq_left_of_natDegree_lt hlt, h_lead]

private theorem normalizedWickPolynomialPoly_leadingCoeff
    (P : InteractionPolynomial) (s : ℝ) :
    (normalizedWickPolynomialPoly P s).leadingCoeff = 1 / P.n := by
  unfold normalizedWickPolynomialPoly
  have hne := normalizedWickPolynomialPoly_leading_ne_zero P s
  have h_lead := normalizedWickPolynomialPoly_leading_natDegree P s
  have h_sum := normalizedWickPolynomialPoly_sum_natDegree_lt P s
  rw [leadingCoeff_add_of_degree_lt']
  · rw [leadingCoeff_mul, leadingCoeff_C, (wickMonomialPoly_monic P.n 1).leadingCoeff, mul_one]
  · calc
      degree (∑ m : Fin P.n, C (P.coeff m * s ^ (P.n - (m : ℕ))) * wickMonomialPoly (m : ℕ) 1)
          ≤
            ↑(∑ m : Fin P.n,
                C (P.coeff m * s ^ (P.n - (m : ℕ))) * wickMonomialPoly (m : ℕ) 1).natDegree :=
            degree_le_natDegree
      _ < ↑P.n := by exact_mod_cast h_sum
      _ = ↑(C (1 / ↑P.n : ℝ) * wickMonomialPoly P.n 1).natDegree := by rw [h_lead]
      _ = degree (C (1 / ↑P.n : ℝ) * wickMonomialPoly P.n 1) := by
            rw [degree_eq_natDegree hne]

private theorem normalizedWickPolynomialPoly_coeff_continuous
    (P : InteractionPolynomial) (i : ℕ) :
    Continuous (fun s : ℝ => (normalizedWickPolynomialPoly P s).coeff i) := by
  have h_eq : ∀ s, (normalizedWickPolynomialPoly P s).coeff i =
      (1 / P.n : ℝ) * (wickMonomialPoly P.n 1).coeff i +
      ∑ m : Fin P.n,
        (P.coeff m * s ^ (P.n - (m : ℕ))) * (wickMonomialPoly (m : ℕ) 1).coeff i := by
    intro s
    unfold normalizedWickPolynomialPoly
    rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.finset_sum_coeff]
    apply congrArg (fun t => (1 / P.n : ℝ) * (wickMonomialPoly P.n 1).coeff i + t)
    apply Finset.sum_congr rfl
    intro m hm
    rw [mul_assoc, Polynomial.coeff_C_mul]
    simp [mul_assoc, mul_left_comm, mul_comm]
  simp_rw [h_eq]
  apply Continuous.add
  · exact continuous_const
  · apply continuous_finset_sum
    intro m _
    exact (continuous_const.mul (continuous_id.pow _)).mul continuous_const

/-- Uniform lower bound for the normalized unit-variance family obtained by
factoring out the highest `c`-power from `wickPolynomial P c x`. -/
private theorem normalizedWickPolynomialPoly_uniform_bounded_below
    (P : InteractionPolynomial) :
    ∃ A : ℝ, 0 < A ∧ ∀ (s : ℝ), 0 ≤ s → s ≤ 1 → ∀ x : ℝ,
      (normalizedWickPolynomialPoly P s).eval x ≥ -A := by
  set n := P.n with hn_def
  have hn_ge : 4 ≤ n := P.hn_ge
  have hn_even : Even n := P.hn_even
  have hn_pos : 0 < n := by omega
  set lc : ℝ := 1 / n
  have hlc_pos : 0 < lc := div_pos one_pos (by exact_mod_cast hn_pos)
  have hcoeff_sum_cont : Continuous (fun s : ℝ =>
      (Finset.range n).sum (fun i => |(normalizedWickPolynomialPoly P s).coeff i|)) :=
    continuous_finset_sum _ fun i _ =>
      (normalizedWickPolynomialPoly_coeff_continuous P i).abs
  obtain ⟨s₀, hs₀_mem, hs₀_max⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr zero_le_one) hcoeff_sum_cont.continuousOn
  set Mcoeff : ℝ :=
    (Finset.range n).sum (fun i => |(normalizedWickPolynomialPoly P s₀).coeff i|)
  have hM_bound : ∀ s ∈ Set.Icc 0 1,
      (Finset.range n).sum (fun i => |(normalizedWickPolynomialPoly P s).coeff i|) ≤ Mcoeff :=
    fun s hs => hs₀_max hs
  have hM_nonneg : 0 ≤ Mcoeff := Finset.sum_nonneg fun i _ => abs_nonneg _
  set R : ℝ := max 1 (Mcoeff / lc + 1)
  have hR_ge1 : 1 ≤ R := le_max_left 1 _
  have hR_pos : 0 < R := lt_of_lt_of_le one_pos hR_ge1
  have hMR : Mcoeff < lc * R := by
    have : Mcoeff / lc < R :=
      lt_of_lt_of_le (by linarith) (le_max_right 1 _)
    rwa [div_lt_iff₀ hlc_pos, mul_comm] at this
  have hclaim : ∀ s ∈ Set.Icc 0 1, ∀ x : ℝ, R ≤ |x| →
      0 ≤ (normalizedWickPolynomialPoly P s).eval x := by
    intro s hs x hxR
    have hx1 : 1 ≤ |x| := le_trans hR_ge1 hxR
    set p := normalizedWickPolynomialPoly P s
    have hp_deg : p.natDegree = n := normalizedWickPolynomialPoly_natDegree P s
    have hp_lc : p.leadingCoeff = lc := by
      simpa [lc, hn_def] using normalizedWickPolynomialPoly_leadingCoeff P s
    have hcn : p.coeff n = lc := by
      rw [show n = p.natDegree from hp_deg.symm]
      exact hp_lc
    have hp_eq : p.eval x = lc * x ^ n +
        (Finset.range n).sum (fun i => p.coeff i * x ^ i) := by
      simp only [eval_eq_sum_range, Finset.sum_range_succ, hp_deg]
      rw [hcn]
      ring
    have hxn_eq : x ^ n = |x| ^ n := (hn_even.pow_abs x).symm
    have hrest_bound : |(Finset.range n).sum (fun i => p.coeff i * x ^ i)|
        ≤ Mcoeff * |x| ^ (n - 1) := by
      calc
        |(Finset.range n).sum fun i => p.coeff i * x ^ i|
            ≤ (Finset.range n).sum fun i => |p.coeff i| * |x| ^ i := by
              calc
                _ ≤ (Finset.range n).sum fun i => |p.coeff i * x ^ i| :=
                      Finset.abs_sum_le_sum_abs _ _
                _ = _ := by congr 1; ext i; rw [abs_mul, abs_pow]
        _ ≤ (Finset.range n).sum fun i => |p.coeff i| * |x| ^ (n - 1) := by
              apply Finset.sum_le_sum
              intro i hi
              exact mul_le_mul_of_nonneg_left
                (pow_le_pow_right₀ hx1 (by
                  have := Finset.mem_range.mp hi
                  omega))
                (abs_nonneg _)
        _ = ((Finset.range n).sum fun i => |p.coeff i|) * |x| ^ (n - 1) :=
              (Finset.sum_mul ..).symm
        _ ≤ Mcoeff * |x| ^ (n - 1) :=
              mul_le_mul_of_nonneg_right (hM_bound s hs)
                (pow_nonneg (abs_nonneg x) _)
    have hlead_split : lc * |x| ^ n = (lc * |x|) * |x| ^ (n - 1) := by
      have : |x| ^ n = |x| ^ (n - 1) * |x| := by
        conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
      rw [this]
      ring
    have hlcx_bound : Mcoeff ≤ lc * |x| :=
      le_of_lt (lt_of_lt_of_le hMR
        (mul_le_mul_of_nonneg_left hxR (le_of_lt hlc_pos)))
    have hxn1 : 0 ≤ |x| ^ (n - 1) := pow_nonneg (abs_nonneg x) _
    have hrest_lower : -(Mcoeff * |x| ^ (n - 1)) ≤
        (Finset.range n).sum (fun i => p.coeff i * x ^ i) :=
      neg_le_of_abs_le hrest_bound
    rw [hp_eq, hxn_eq, hlead_split]
    nlinarith [mul_le_mul_of_nonneg_right hlcx_bound hxn1]
  set K := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-R) R
  have hK_compact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hK_ne : K.Nonempty :=
    ⟨⟨0, 0⟩, by
      refine Set.mk_mem_prod ?_ ?_
      · exact Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩
      · exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩⟩
  set f : ℝ × ℝ → ℝ := fun p => (normalizedWickPolynomialPoly P p.1).eval p.2
  have hf_cont : Continuous f := by
    change Continuous (fun p : ℝ × ℝ => (normalizedWickPolynomialPoly P p.1).eval p.2)
    rw [show (fun p : ℝ × ℝ => (normalizedWickPolynomialPoly P p.1).eval p.2) =
        (fun p : ℝ × ℝ =>
          (1 / P.n : ℝ) * wickMonomial P.n 1 p.2 +
            ∑ m : Fin P.n,
              P.coeff m * p.1 ^ (P.n - (m : ℕ)) * wickMonomial (m : ℕ) 1 p.2) by
          funext p
          rw [normalizedWickPolynomialPoly_eval]]
    apply Continuous.add
    · exact continuous_const.mul
        ((wickMonomial_continuous₂ n).comp (continuous_const.prodMk continuous_snd))
    · apply continuous_finset_sum
      intro m _
      exact ((continuous_const.mul (continuous_fst.pow _)).mul
        ((wickMonomial_continuous₂ m).comp (continuous_const.prodMk continuous_snd)))
  obtain ⟨p₀, hp₀_mem, hp₀_min⟩ := hK_compact.exists_isMinOn hK_ne hf_cont.continuousOn
  refine ⟨|f p₀| + 1, by positivity, fun s hs0 hs1 x => ?_⟩
  by_cases hx : R ≤ |x|
  · have := hclaim s ⟨hs0, hs1⟩ x hx
    linarith [abs_nonneg (f p₀)]
  · push Not at hx
    have hx_bound : x ∈ Set.Icc (-R) R := by
      rw [Set.mem_Icc]
      constructor
      · linarith [(abs_lt.mp hx).1]
      · linarith [(abs_lt.mp hx).2]
    have hmem : (s, x) ∈ K := Set.mk_mem_prod ⟨hs0, hs1⟩ hx_bound
    have h_min : f p₀ ≤ f (s, x) := hp₀_min hmem
    change (normalizedWickPolynomialPoly P p₀.1).eval p₀.2 ≤
      (normalizedWickPolynomialPoly P s).eval x at h_min
    linarith [neg_abs_le (f p₀)]

private theorem wickMonomial_rescale_to_unit
    (n : ℕ) {c : ℝ} (hc : 0 < c) (x : ℝ) :
    wickMonomial n c x =
      Real.sqrt c ^ n * wickMonomial n 1 (x / Real.sqrt c) := by
  have h := wickMonomial_homogeneity n (Real.sqrt c) 1 (x / Real.sqrt c)
  have hsqrt_ne : Real.sqrt c ≠ 0 := by positivity
  have hx : Real.sqrt c * (x / Real.sqrt c) = x := by
    field_simp [hsqrt_ne]
  rw [wickMonomial_eq_root, wickMonomial_eq_root]
  simpa [Real.sq_sqrt hc.le, one_mul, hx] using h

private theorem wickPolynomial_eq_normalized_scale
    (P : InteractionPolynomial) {c : ℝ} (hc : 0 < c) (x : ℝ) :
    wickPolynomial P c x =
      Real.sqrt c ^ P.n *
        (normalizedWickPolynomialPoly P ((Real.sqrt c)⁻¹)).eval (x / Real.sqrt c) := by
  let y : ℝ := x / Real.sqrt c
  let γ : ℝ := Real.sqrt c
  have hγ_ne : γ ≠ 0 := by
    dsimp [γ]
    positivity
  have hterm :
      ∀ m : ℕ,
        wickMonomial m c x = γ ^ m * wickMonomial m 1 y := by
    intro m
    simpa [γ, y] using wickMonomial_rescale_to_unit m hc x
  unfold wickPolynomial
  rw [normalizedWickPolynomialPoly_eval]
  simp_rw [hterm]
  have hlead :
      (1 / P.n : ℝ) * (γ ^ P.n * wickMonomial P.n 1 y) =
        γ ^ P.n * ((1 / P.n : ℝ) * wickMonomial P.n 1 y) := by
    ring
  rw [hlead]
  have hsum :
      ∑ m : Fin P.n, P.coeff m * (γ ^ (m : ℕ) * wickMonomial (m : ℕ) 1 y) =
        γ ^ P.n *
          ∑ m : Fin P.n,
            P.coeff m * γ⁻¹ ^ (P.n - (m : ℕ)) * wickMonomial (m : ℕ) 1 y := by
    calc
      ∑ m : Fin P.n, P.coeff m * (γ ^ (m : ℕ) * wickMonomial (m : ℕ) 1 y)
          = ∑ m : Fin P.n,
              γ ^ P.n * (P.coeff m * γ⁻¹ ^ (P.n - (m : ℕ)) * wickMonomial (m : ℕ) 1 y) := by
                apply Finset.sum_congr rfl
                intro m hm
                have hpow :
                    γ ^ P.n * γ⁻¹ ^ (P.n - (m : ℕ)) = γ ^ (m : ℕ) := by
                  have hm_le : (m : ℕ) ≤ P.n := Nat.le_of_lt m.2
                  have hsplit : γ ^ P.n = γ ^ (P.n - (m : ℕ)) * γ ^ (m : ℕ) := by
                    calc
                      γ ^ P.n = γ ^ ((P.n - (m : ℕ)) + (m : ℕ)) := by
                        exact congrArg (fun t : ℕ => γ ^ t) (Nat.sub_add_cancel hm_le).symm
                      _ = γ ^ (P.n - (m : ℕ)) * γ ^ (m : ℕ) := by
                        rw [pow_add]
                  calc
                    γ ^ P.n * γ⁻¹ ^ (P.n - (m : ℕ))
                        = (γ ^ (P.n - (m : ℕ)) * γ ^ (m : ℕ)) *
                            γ⁻¹ ^ (P.n - (m : ℕ)) := by rw [hsplit]
                    _ = γ ^ (m : ℕ) := by
                          rw [inv_pow]
                          field_simp [hγ_ne]
                calc
                  P.coeff m * (γ ^ (m : ℕ) * wickMonomial (m : ℕ) 1 y)
                      = P.coeff m * ((γ ^ P.n * γ⁻¹ ^ (P.n - (m : ℕ))) *
                          wickMonomial (m : ℕ) 1 y) := by rw [hpow]
                  _ = γ ^ P.n *
                      (P.coeff m * γ⁻¹ ^ (P.n - (m : ℕ)) *
                        wickMonomial (m : ℕ) 1 y) := by ring
      _ = γ ^ P.n *
            ∑ m : Fin P.n,
              P.coeff m * γ⁻¹ ^ (P.n - (m : ℕ)) * wickMonomial (m : ℕ) 1 y := by
                rw [Finset.mul_sum]
  rw [hsum]
  ring

/-- General sitewise lower bound for the Wick polynomial, with the growth in
the Wick constant controlled by the top degree `P.n / 2`. This is the smooth-side
estimate needed for the bounded-volume Nelson bridge for general even `P`. -/
theorem wickPolynomial_lower_bound_general (P : InteractionPolynomial) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (c x : ℝ), 0 ≤ c →
        wickPolynomial P c x ≥ -A * (1 + c ^ (P.n / 2)) := by
  obtain ⟨A_small, hA_small_pos, hsmall⟩ :=
    wickPolynomial_uniform_bounded_below P 1 zero_le_one
  obtain ⟨A_large, hA_large_pos, hlarge⟩ :=
    normalizedWickPolynomialPoly_uniform_bounded_below P
  let A : ℝ := max A_small A_large
  refine ⟨A, le_of_lt (lt_of_lt_of_le hA_small_pos (le_max_left _ _)), ?_⟩
  intro c x hc
  by_cases hc1 : c ≤ 1
  · have hbase : wickPolynomial P c x ≥ -A_small := hsmall c hc hc1 x
    have hfactor : 1 ≤ 1 + c ^ (P.n / 2) := by
      have hpow_nonneg : 0 ≤ c ^ (P.n / 2) := pow_nonneg hc _
      linarith
    have hbound : -A * (1 + c ^ (P.n / 2)) ≤ -A_small := by
      have h1 : -A ≤ -A_small := by
        have hA_small_le_A : A_small ≤ A := le_max_left _ _
        linarith
      have h2 : -A * (1 + c ^ (P.n / 2)) ≤ -A * 1 := by
        have hnegA : -A ≤ 0 := by
          have hA_nonneg : 0 ≤ A := le_trans (le_of_lt hA_small_pos) (le_max_left _ _)
          linarith
        simpa using mul_le_mul_of_nonpos_left hfactor hnegA
      linarith
    exact le_trans hbound hbase
  · have hc_gt_one : 1 < c := lt_of_not_ge hc1
    have hc_pos : 0 < c := lt_trans zero_lt_one hc_gt_one
    have hs_nonneg : 0 ≤ (Real.sqrt c)⁻¹ := by positivity
    have hs_le_one : (Real.sqrt c)⁻¹ ≤ 1 := by
      have hsqrt_ge_one : 1 ≤ Real.sqrt c := by
        rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
        exact Real.sqrt_le_sqrt hc_gt_one.le
      have hsqrt_pos : 0 < Real.sqrt c := by positivity
      rwa [inv_le_one₀ hsqrt_pos]
    have hnorm :
        (normalizedWickPolynomialPoly P ((Real.sqrt c)⁻¹)).eval (x / Real.sqrt c) ≥ -A_large :=
      hlarge ((Real.sqrt c)⁻¹) hs_nonneg hs_le_one (x / Real.sqrt c)
    have hsqrt_pow_nonneg : 0 ≤ Real.sqrt c ^ P.n := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hnorm hsqrt_pow_nonneg
    have hsqrt_even :
        Real.sqrt c ^ P.n = c ^ (P.n / 2) := by
      obtain ⟨k, hk⟩ := P.hn_even
      rw [hk]
      rw [show (k + k) / 2 = k by omega]
      rw [show k + k = 2 * k by omega, pow_mul]
      have hsq : Real.sqrt c ^ 2 = c := by
        nlinarith [Real.sq_sqrt hc]
      rw [hsq]
    have hpoly_eq := wickPolynomial_eq_normalized_scale P hc_pos x
    have hscaled' : -(A_large * c ^ (P.n / 2)) ≤ wickPolynomial P c x := by
      calc
        -(A_large * c ^ (P.n / 2))
            = Real.sqrt c ^ P.n * (-A_large) := by
                rw [hsqrt_even]
                ring
        _ ≤ Real.sqrt c ^ P.n *
              (normalizedWickPolynomialPoly P ((Real.sqrt c)⁻¹)).eval (x / Real.sqrt c) :=
              hscaled
        _ = wickPolynomial P c x := hpoly_eq.symm
    have hA_ge_large : A_large ≤ A := le_max_right _ _
    have hbound : -A * (1 + c ^ (P.n / 2)) ≤ -(A_large * c ^ (P.n / 2)) := by
      have hA_nonneg : 0 ≤ A := le_trans (le_of_lt hA_small_pos) (le_max_left _ _)
      have hpow_nonneg : 0 ≤ c ^ (P.n / 2) := pow_nonneg hc (P.n / 2)
      have hmul : A_large * c ^ (P.n / 2) ≤ A * (1 + c ^ (P.n / 2)) := by
        calc
          A_large * c ^ (P.n / 2) ≤ A * c ^ (P.n / 2) :=
            mul_le_mul_of_nonneg_right hA_ge_large hpow_nonneg
          _ ≤ A * (1 + c ^ (P.n / 2)) :=
            mul_le_mul_of_nonneg_left (by linarith) hA_nonneg
      linarith
    exact le_trans hbound hscaled'

end Pphi2

end
