/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Wick Binomial Theorem

The Wick binomial theorem for sums of independent Gaussian variables:
`:( x + y )^n :_{c₁+c₂} = Σ_{k=0}^{n} C(n,k) · :x^k:_{c₁} · :y^{n-k}:_{c₂}`

This is the key algebraic identity needed for the Nelson estimate's
covariance splitting argument.

## Main results

- `wickMonomial_add_binomial` — the Wick binomial expansion
- `wickMonomial_four_add_binomial` — explicit expansion for n = 4

## References

- Simon, *P(φ)₂ Euclidean QFT*, Chapter V (Wick product properties)
- Janson, *Gaussian Hilbert Spaces*, Proposition 3.27
-/

import Pphi2.WickOrdering.WickPolynomial

noncomputable section

open Finset Nat
open scoped BigOperators

namespace Pphi2

/-! ## Wick Binomial Theorem

The Wick binomial theorem states that for the probabilist's Hermite polynomials
(= Wick monomials), we have the addition formula:

  :( x + y )^n :_{c₁+c₂} = Σ_{k=0}^{n} C(n,k) · :x^k:_{c₁} · :y^{n-k}:_{c₂}

This is equivalent to the linearization formula for Hermite polynomials,
and holds as a purely algebraic identity. -/

/-! ### Helper lemmas for the recurrence proof -/

/-- The binomial sum Σ_k C(n,k) W_k(c₁,x) W_{n-k}(c₂,y) -/
private def wickBinomialSum (n : ℕ) (c₁ c₂ x y : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1),
    (n.choose k : ℝ) * wickMonomial k c₁ x * wickMonomial (n - k) c₂ y

/-- Reverse Wick recurrence: x * W(n, c, x) = W(n+1, c, x) + n*c*W(n-1, c, x)
    Uniform version that works for all n (including n=0). -/
private theorem wickMonomial_mul_left : ∀ (n : ℕ) (c x : ℝ),
    x * wickMonomial n c x = wickMonomial (n + 1) c x + (n : ℝ) * c * wickMonomial (n - 1) c x
  | 0, c, x => by simp [wickMonomial_zero, wickMonomial_one]
  | n + 1, c, x => by
    simp only [Nat.succ_sub_one, Nat.cast_succ]
    linarith [wickMonomial_succ_succ n c x]

/-- Reverse Wick recurrence for the y variable (second Wick monomial). -/
private theorem wickMonomial_mul_right : ∀ (m : ℕ) (c y : ℝ),
    y * wickMonomial m c y = wickMonomial (m + 1) c y + (m : ℝ) * c * wickMonomial (m - 1) c y :=
  wickMonomial_mul_left

/-- Key binomial coefficient identity: (k+1) * C(n+1, k+1) = (n+1) * C(n, k) -/
private theorem choose_mul_succ (n k : ℕ) :
    (k + 1 : ℝ) * ((n + 1).choose (k + 1) : ℝ) = (n + 1 : ℝ) * (n.choose k : ℝ) := by
  have h := Nat.add_one_mul_choose_eq n k
  -- h : (n + 1) * n.choose k = (n + 1).choose (k + 1) * (k + 1)
  -- Need: (k+1) * C(n+1, k+1) = (n+1) * C(n, k)
  -- which is h rewritten as multiplication commuted
  have h' : (k + 1) * (n + 1).choose (k + 1) = (n + 1) * n.choose k := by linarith [h]
  exact_mod_cast h'

/-- Key binomial coefficient identity: (n+1-k) * C(n+1, k) = (n+1) * C(n, k) for k ≤ n -/
private theorem choose_mul_complement (n k : ℕ) (hk : k ≤ n) :
    ((n + 1 - k : ℕ) : ℝ) * ((n + 1).choose k : ℝ) = (n + 1 : ℝ) * (n.choose k : ℝ) := by
  have h := Nat.add_one_mul_choose_eq n (n - k)
  -- h : (n+1) * C(n, n-k) = C(n+1, n-k+1) * (n-k+1)
  have hk' : n - k + 1 = n + 1 - k := by omega
  have hchoose1 : n.choose (n - k) = n.choose k := Nat.choose_symm hk
  have hchoose2 : (n + 1).choose (n - k + 1) = (n + 1).choose k := by
    rw [hk']
    exact Nat.choose_symm (by omega)
  have h' : (n + 1 - k) * (n + 1).choose k = (n + 1) * n.choose k := by
    rw [← hk', ← hchoose2, ← hchoose1]
    linarith [h]
  exact_mod_cast h'

/-- **Wick Binomial Theorem**: The Wick monomial of a sum decomposes as a
binomial sum of Wick monomials with split variances.

For all n, c₁, c₂ ≥ 0, x, y ∈ ℝ:
  wickMonomial n (c₁ + c₂) (x + y) =
    Σ_{k ∈ range (n+1)} C(n, k) • wickMonomial k c₁ x • wickMonomial (n-k) c₂ y -/
theorem wickMonomial_add_binomial (n : ℕ) (c₁ c₂ x y : ℝ) :
    wickMonomial n (c₁ + c₂) (x + y) =
    ∑ k ∈ range (n + 1),
      (n.choose k : ℝ) * wickMonomial k c₁ x * wickMonomial (n - k) c₂ y := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [wickMonomial_zero]
    | 1 =>
      simp [Finset.sum_range_succ, wickMonomial_one, wickMonomial_zero]
      ring
    | n + 2 =>
      rw [wickMonomial_succ_succ, ih (n + 1) (by omega), ih n (by omega)]
      -- Goal: (x+y) * S₁ - (n+1)(c₁+c₂) * S₂ = Σ C(n+2,k) W_k(x) W_{n+2-k}(y)
      -- where S₁ = Σ_{i=0}^{n+1} C(n+1,i) W_i(x) W_{n+1-i}(y)
      --       S₂ = Σ_{i=0}^{n} C(n,i) W_i(x) W_{n-i}(y)
      -- We use wickMonomial_mul_left on the x-part of each term,
      -- and wickMonomial_mul_right on the y-part.
      -- After reindexing and cancellation, we get the RHS via Pascal's rule.

      -- Distribute (x+y) and (n+1)(c₁+c₂) into sums
      simp only [Finset.mul_sum]
      -- Convert to: Σ (x+y)*term_i - Σ (n+1)(c₁+c₂)*term_j = Σ result_k
      -- Use sub_eq_iff_eq_add or work with individual terms

      -- Apply Wick recurrences within sums using conv + sum_congr
      -- First: (x+y) * (C * W_i * W_{n+1-i}) = C * (x*W_i) * W_{n+1-i} + C * W_i * (y*W_{n+1-i})
      -- Then: x*W_i = W_{i+1} + i*c₁*W_{i-1} and y*W_m = W_{m+1} + m*c₂*W_{m-1}
      -- Replace each summand using the Wick recurrence
      have key : ∀ i ∈ range (n + 1 + 1),
          (x + y) * (↑((n + 1).choose i) * wickMonomial i c₁ x * wickMonomial (n + 1 - i) c₂ y) =
          ↑((n + 1).choose i) * (wickMonomial (i + 1) c₁ x + ↑i * c₁ * wickMonomial (i - 1) c₁ x) *
            wickMonomial (n + 1 - i) c₂ y +
          ↑((n + 1).choose i) * wickMonomial i c₁ x *
            (wickMonomial (n + 1 - i + 1) c₂ y +
             ↑(n + 1 - i) * c₂ * wickMonomial (n + 1 - i - 1) c₂ y) := by
        intro i _
        rw [show (x + y) * (↑((n + 1).choose i) * wickMonomial i c₁ x * wickMonomial (n + 1 - i) c₂ y) =
              ↑((n + 1).choose i) * (x * wickMonomial i c₁ x) * wickMonomial (n + 1 - i) c₂ y +
              ↑((n + 1).choose i) * wickMonomial i c₁ x * (y * wickMonomial (n + 1 - i) c₂ y) from by ring]
        rw [wickMonomial_mul_left i, wickMonomial_mul_left (n + 1 - i)]
      rw [Finset.sum_congr rfl key]; clear key ih
      -- After applying the Wick recurrence to each term, we have 4 sub-sums:
      -- A = Σ C(n+1,i) W_{i+1}(x) W_{n+1-i}(y)
      -- B = Σ C(n+1,i) * i*c₁ * W_{i-1}(x) * W_{n+1-i}(y)
      -- C = Σ C(n+1,i) W_i(x) W_{n+2-i}(y)
      -- D = Σ C(n+1,i) * (n+1-i)*c₂ * W_i(x) * W_{n-i}(y)
      -- plus the subtracted -(n+1)(c₁+c₂) * S₂.
      -- Key: B = (n+1)c₁ * S₂, D = (n+1)c₂ * S₂, so B+D cancels exactly.
      -- Then A + C = RHS via Pascal's rule.

      -- We'll prove: LHS = A + C, and A + C = RHS
      -- First split into A + B + C + D
      simp only [mul_add, add_mul, Finset.sum_add_distrib]

      -- Now prove B = (n+1)c₁ * S₂ by reindexing
      -- B = Σ_{i∈range(n+2)} C(n+1,i) * i*c₁ * W_{i-1}(x) * W_{n+1-i}(y)
      -- Define shorthand for the sums
      -- We need to show: A + B + (C + D) - ((n+1)c₁ S₂ + c₁ S₂ + (n+1)c₂ S₂ + c₂ S₂) = RHS
      -- i.e., A + B + C + D - (n+1)c₁ S₂ - c₁ S₂ - (n+1)c₂ S₂ - c₂ S₂ = RHS
      -- where we'll show B = (n+1)c₁ S₂ + c₁ S₂ and D = (n+1)c₂ S₂ + c₂ S₂
      -- Actually: the negative terms are  n*c₁*S₂ + c₁*S₂ + n*c₂*S₂ + c₂*S₂ = (n+1)(c₁+c₂)*S₂

      -- Prove B = Σ (n*c₁ + c₁) * C(n,i) * W_i(x) * W_{n-i}(y)
      -- i.e., B = (n+1)*c₁ * S₂
      have hB : ∑ i ∈ range (n + 1 + 1),
          ↑((n + 1).choose i) * (↑i * c₁ * wickMonomial (i - 1) c₁ x) *
            wickMonomial (n + 1 - i) c₂ y =
        ∑ i ∈ range (n + 1),
          (↑n + 1) * c₁ * (↑(n.choose i) * wickMonomial i c₁ x * wickMonomial (n - i) c₂ y) := by
        -- The i=0 term vanishes (factor i=0)
        rw [Finset.sum_range_succ']
        simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
        apply Finset.sum_congr rfl
        intro i hi
        have him : i < n + 1 := Finset.mem_range.mp hi
        -- After reindexing: i+1 term has C(n+1,i+1)*(i+1)*c₁*W_i(x)*W_{n-i}(y)
        -- Use (i+1)*C(n+1,i+1) = (n+1)*C(n,i)
        have hcoeff : (↑(i + 1) : ℝ) * ↑((n + 1).choose (i + 1)) = (↑n + 1) * ↑(n.choose i) := by
          push_cast; exact choose_mul_succ n i
        have hsub : n + 1 - (i + 1) = n - i := by omega
        simp only [Nat.succ_sub_one, hsub]
        -- Goal: C(n+1,i+1) * ((i+1)*c₁*W_i(x)) * W_{n-i}(y) = (n+1)*c₁*(C(n,i)*W_i(x)*W_{n-i}(y))
        -- Use (i+1)*C(n+1,i+1) = (n+1)*C(n,i)
        have hkey : ↑((n + 1).choose (i + 1)) * (↑(i + 1) : ℝ) = (↑n + 1) * ↑(n.choose i) := by
          linarith [hcoeff]
        -- Both sides are just hkey * c₁ * W_i(x) * W_{n-i}(y)
        linear_combination (c₁ * wickMonomial i c₁ x * wickMonomial (n - i) c₂ y) * hkey
      -- Prove D = (n+1)*c₂ * S₂
      -- D = Σ_{i∈range(n+2)} C(n+1,i) * W_i(x) * (n+1-i)*c₂*W_{n-i}(y)
      -- The i=n+1 term vanishes ((n+1-i)=0). For i≤n, use (n+1-i)*C(n+1,i)=(n+1)*C(n,i)
      have hD : ∑ i ∈ range (n + 1 + 1),
          ↑((n + 1).choose i) * wickMonomial i c₁ x *
            (↑(n + 1 - i) * c₂ * wickMonomial (n + 1 - i - 1) c₂ y) =
        ∑ i ∈ range (n + 1),
          (↑n + 1) * c₂ * (↑(n.choose i) * wickMonomial i c₁ x * wickMonomial (n - i) c₂ y) := by
        -- The last term (i=n+1) vanishes since n+1-(n+1)=0
        rw [Finset.sum_range_succ]
        simp only [Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero, add_zero]
        apply Finset.sum_congr rfl
        intro i hi
        have him : i < n + 1 := Finset.mem_range.mp hi
        have hi_le : i ≤ n := by omega
        have hsub1 : n + 1 - i - 1 = n - i := by omega
        have hsub2 : (n + 1 - i : ℕ) = n + 1 - i := rfl
        simp only [hsub1]
        -- Need: C(n+1,i) * (n+1-i) = (n+1) * C(n,i)
        have hcoeff : ((n + 1 - i : ℕ) : ℝ) * ↑((n + 1).choose i) = (↑n + 1) * ↑(n.choose i) :=
          choose_mul_complement n i hi_le
        have hkey : ↑((n + 1).choose i) * (↑(n + 1 - i) : ℝ) = (↑n + 1) * ↑(n.choose i) := by
          linarith [hcoeff]
        linear_combination (c₂ * wickMonomial i c₁ x * wickMonomial (n - i) c₂ y) * hkey
      -- Now use hB and hD to cancel the c₁ and c₂ terms
      rw [hB, hD]
      -- After rw, positive terms include (n+1)c₁ S₂ and (n+1)c₂ S₂
      -- Negative terms are nc₁ S₂ + c₁ S₂ + nc₂ S₂ + c₂ S₂ = (n+1)(c₁+c₂) S₂
      -- These cancel, leaving A + C = RHS

      -- Let's just suffice A + C = RHS
      suffices h : ∑ x_1 ∈ range (n + 1 + 1),
            ↑((n + 1).choose x_1) * wickMonomial (x_1 + 1) c₁ x * wickMonomial (n + 1 - x_1) c₂ y +
          ∑ x_1 ∈ range (n + 1 + 1),
            ↑((n + 1).choose x_1) * wickMonomial x_1 c₁ x * wickMonomial (n + 1 - x_1 + 1) c₂ y =
          ∑ k ∈ range (n + 2 + 1),
            ↑((n + 2).choose k) * wickMonomial k c₁ x * wickMonomial (n + 2 - k) c₂ y by
        -- Cancel B+D with the negative terms, reducing to h
        -- All the c₁*S₂ and c₂*S₂ terms cancel
        -- LHS = A + (n+1)c₁S₂ + (C + (n+1)c₂S₂) - (nc₁S₂ + c₁S₂ + nc₂S₂ + c₂S₂)
        --     = A + C + [(n+1)c₁S₂ + (n+1)c₂S₂ - nc₁S₂ - c₁S₂ - nc₂S₂ - c₂S₂]
        --     = A + C + 0 = A + C
        have hcancel :
          ∑ i ∈ range (n + 1), (↑n + 1) * c₁ * (↑(n.choose i) * wickMonomial i c₁ x * wickMonomial (n - i) c₂ y) +
          ∑ i ∈ range (n + 1), (↑n + 1) * c₂ * (↑(n.choose i) * wickMonomial i c₁ x * wickMonomial (n - i) c₂ y) =
          ∑ x_1 ∈ range (n + 1), ↑n * c₁ * (↑(n.choose x_1) * wickMonomial x_1 c₁ x * wickMonomial (n - x_1) c₂ y) +
            ∑ x_1 ∈ range (n + 1), 1 * c₁ * (↑(n.choose x_1) * wickMonomial x_1 c₁ x * wickMonomial (n - x_1) c₂ y) +
          (∑ x_1 ∈ range (n + 1), ↑n * c₂ * (↑(n.choose x_1) * wickMonomial x_1 c₁ x * wickMonomial (n - x_1) c₂ y) +
            ∑ x_1 ∈ range (n + 1), 1 * c₂ * (↑(n.choose x_1) * wickMonomial x_1 c₁ x * wickMonomial (n - x_1) c₂ y)) := by
          simp only [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro i _; ring
        linarith [h, hcancel]
      -- Prove A + C = RHS via antidiagonal sums and Pascal's rule
      -- Convert range sums to antidiagonal sums
      rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => ↑((n + 1).choose i) * wickMonomial (i + 1) c₁ x * wickMonomial j c₂ y),
          ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => ↑((n + 1).choose i) * wickMonomial i c₁ x * wickMonomial (j + 1) c₂ y),
          ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => ↑((n + 2).choose i) * wickMonomial i c₁ x * wickMonomial j c₂ y)]
      -- Convert ↑choose * a * b to choose • (a * b) for sum_antidiagonal_choose_succ_nsmul
      -- nsmul_eq_mul: n • x = ↑n * x, so ↑n * (a * b) = n • (a * b)
      simp_rw [show ∀ (a b c : ℝ), a * b * c = a * (b * c) from fun a b c => mul_assoc a b c]
      simp_rw [← nsmul_eq_mul]
      -- Now match with sum_antidiagonal_choose_succ_nsmul
      rw [show n + 2 = n + 1 + 1 from rfl]
      rw [Finset.sum_antidiagonal_choose_succ_nsmul
            (fun i j => wickMonomial i c₁ x * wickMonomial j c₂ y) (n + 1)]
      -- RHS: Σ C(n+1,i) • f(i, j+1) + Σ C(n+1,j) • f(i+1, j)
      -- LHS: A + C where
      --   A = Σ C(n+1,i) • (W_{i+1} * W_j)  -- f(i+1, j) with C(n+1,i)
      --   C = Σ C(n+1,i) • (W_i * W_{j+1})  -- f(i, j+1) with C(n+1,i)
      -- RHS first sum matches C ✓
      -- RHS second sum has C(n+1,j), need to convert to C(n+1,i) for A
      rw [add_comm]
      congr 1
      -- Goal: Σ C(n+1,i) • (W_{i+1} * W_j) = Σ C(n+1,j) • (W_{i+1} * W_j) on antidiag(n+1)
      apply Finset.sum_congr rfl
      intro ij hij
      have hmem := Finset.mem_antidiagonal.mp hij
      -- hmem : ij.1 + ij.2 = n + 1
      have hsymm : (n + 1).choose ij.2 = (n + 1).choose ij.1 := by
        have h2 : ij.2 = n + 1 - ij.1 := by omega
        rw [h2]
        exact Nat.choose_symm (by omega)
      rw [hsymm]

/-! ## Explicit cases -/

/-- Wick binomial for n = 2:
:(x+y)²:_{c₁+c₂} = :x²:_{c₁} + 2xy + :y²:_{c₂} -/
theorem wickMonomial_two_add (c₁ c₂ x y : ℝ) :
    wickMonomial 2 (c₁ + c₂) (x + y) =
    wickMonomial 2 c₁ x + 2 * x * y + wickMonomial 2 c₂ y := by
  simp [wickMonomial_succ_succ, wickMonomial_one, wickMonomial_zero]
  ring

/-- Wick binomial for n = 4 (the φ⁴ case):
:(x+y)⁴:_{c₁+c₂} = :x⁴:_{c₁} + 4·:x³:_{c₁}·y + 6·:x²:_{c₁}·:y²:_{c₂}
                    + 4·x·:y³:_{c₂} + :y⁴:_{c₂} -/
theorem wickMonomial_four_add (c₁ c₂ x y : ℝ) :
    wickMonomial 4 (c₁ + c₂) (x + y) =
    wickMonomial 4 c₁ x +
    4 * wickMonomial 3 c₁ x * y +
    6 * wickMonomial 2 c₁ x * wickMonomial 2 c₂ y +
    4 * x * wickMonomial 3 c₂ y +
    wickMonomial 4 c₂ y := by
  rw [wickMonomial_four, wickMonomial_four, wickMonomial_four,
      wickMonomial_three, wickMonomial_three,
      wickMonomial_two, wickMonomial_two]
  ring

/-! ## Lower bound for the smooth part

The smooth Wick polynomial :x⁴:_{c_S} = x⁴ - 6c_S·x² + 3c_S² has minimum value -3c_S².
(Completing the square: x⁴ - 6c·x² + 3c² = (x² - 3c)² - 6c² ≥ -6c².)

Wait, let's compute: min of f(t) = t² - 6c·t + 3c² where t = x²:
f'(t) = 2t - 6c = 0 → t = 3c → f(3c) = 9c² - 18c² + 3c² = -6c².
So :x⁴:_c ≥ -6c² for all x. -/

/-- The Wick-ordered fourth power has a universal lower bound:
`:x⁴:_c ≥ -6c²` for all x and c ≥ 0. -/
theorem wickMonomial_four_lower_bound (c : ℝ) (_hc : 0 ≤ c) (x : ℝ) :
    -6 * c ^ 2 ≤ wickMonomial 4 c x := by
  -- wickMonomial 4 c x = x⁴ - 6c·x² + 3c²
  -- = (x² - 3c)² - 6c²
  -- ≥ -6c²
  have h4 := wickMonomial_four c x
  -- wickMonomial 4 c x = x⁴ - 6c·x² + 3c²
  -- This equals (x² - 3c)² - 6c² ≥ -6c²
  linarith [sq_nonneg (x ^ 2 - 3 * c), h4]

end Pphi2

end
