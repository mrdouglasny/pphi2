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
    push_neg at hx_far
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

end Pphi2

end
