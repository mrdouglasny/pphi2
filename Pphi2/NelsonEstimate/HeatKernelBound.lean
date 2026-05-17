/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Heat Kernel Trace Bound

The core analytic lemma for Nelson's estimate: the trace of the lattice
heat kernel H(t) = Σ_k exp(-t·λ_k) satisfies H(t) ≤ C/t uniformly in N.

This reduces both eigenvalue sum bounds (smoothVariance_le_log and
roughCovariance_sq_summable) to elementary 1D calculus.

## Main results

- `schwinger_smooth` — `exp(-Tλ)/λ = ∫_T^∞ exp(-tλ) dt`
- `schwinger_rough` — `(1-exp(-Tλ))/λ = ∫₀ᵀ exp(-tλ) dt`
- `sin_sq_lower_bound` — `sin²(x) ≥ (2/π)²·x²` for |x| ≤ π/2
- `gaussian_sum_bound` — `Σ_k exp(-α·k²) ≤ 1 + √(π/α)`
- `heat_kernel_trace_bound` — `H(t) ≤ C/t` (uniform in N)

## References

- Gemini analysis of eigenvalue sum bounds via Schwinger parametrization
- Standard lattice QFT heat kernel estimates
-/

import Pphi2.NelsonEstimate.CovarianceSplit
import Pphi2.InteractingMeasure.LatticeMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SumIntegralComparisons

noncomputable section

open GaussianField MeasureTheory Real Finset
open scoped BigOperators

namespace Pphi2

/-! ## Schwinger parametrization identities -/

/-- Schwinger identity for the smooth covariance:
`exp(-T·λ) / λ = ∫_T^∞ exp(-t·λ) dt` for λ > 0, T ≥ 0. -/
private theorem hasDerivAt_neg_exp_div (lam : ℝ) (hlam : lam ≠ 0) (t : ℝ) :
    HasDerivAt (fun s => -exp (-s * lam) / lam) (exp (-t * lam)) t := by
  have h1 : HasDerivAt (fun s => -s * lam) (-lam) t := by
    simpa using (hasDerivAt_id t).neg.mul_const lam
  have h2 : HasDerivAt (fun s => exp (-s * lam)) (exp (-t * lam) * (-lam)) t :=
    h1.exp
  have h3 := h2.neg.div_const lam
  convert h3 using 1
  field_simp

theorem schwinger_smooth_Ioi (lam : ℝ) (hlam : 0 < lam) (T : ℝ) :
    exp (-T * lam) / lam = ∫ t in Set.Ioi T, exp (-t * lam) := by
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  set F := fun t => -exp (-t * lam) / lam
  -- F'(t) = exp(-tλ) (proved)
  have h_deriv : ∀ t ∈ Set.Ici T, HasDerivAt F (exp (-t * lam)) t :=
    fun t _ => hasDerivAt_neg_exp_div lam hlam_ne t
  -- F(t) → 0 as t → ∞ (exponential decay)
  have h_tendsto : Filter.Tendsto F Filter.atTop (nhds 0) := by
    show Filter.Tendsto (fun t => -rexp (-t * lam) / lam) Filter.atTop (nhds 0)
    have h1 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Filter.tendsto_id.const_mul_atTop hlam)).neg.div_const lam
    simp only [neg_zero, zero_div] at h1
    exact h1.congr (fun t => by simp; ring)
  -- Apply improper FTC (nonneg version — no integrability needed!)
  -- g(t) = -exp(-tλ)/λ is increasing (g' = exp(-tλ) ≥ 0), g → 0
  have h_ftc := integral_Ioi_of_hasDerivAt_of_nonneg'
    h_deriv
    (fun t _ => le_of_lt (Real.exp_pos _))
    h_tendsto
  -- h_ftc : ∫ Ioi T, exp(-tλ) = 0 - F(T) = exp(-Tλ)/λ
  rw [h_ftc]; simp only [F]; ring

theorem schwinger_smooth (lam : ℝ) (hlam : 0 < lam) (T : ℝ) (hT : 0 ≤ T) :
    exp (-T * lam) / lam = ∫ t in Set.Ici T, exp (-t * lam) := by
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  exact schwinger_smooth_Ioi lam hlam T

/-- Schwinger identity for the rough covariance:
`(1 - exp(-T·λ)) / λ = ∫₀ᵀ exp(-t·λ) dt` for λ > 0, T ≥ 0. -/
theorem schwinger_rough_interval (lam : ℝ) (hlam : 0 < lam) (T : ℝ) (hT : 0 ≤ T) :
    (1 - exp (-T * lam)) / lam = ∫ t in (0)..T, exp (-t * lam) := by
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  set F := fun t => -exp (-t * lam) / lam
  have h_cont : ContinuousOn (fun t => exp (-t * lam)) (Set.uIcc 0 T) :=
    (Real.continuous_exp.comp (continuous_neg.mul continuous_const)).continuousOn
  have h_ftc : ∫ t in (0 : ℝ)..T, exp (-t * lam) = F T - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_neg_exp_div lam hlam_ne t)
      h_cont.intervalIntegrable
  rw [h_ftc]; simp only [F, neg_zero, zero_mul, exp_zero]; field_simp; ring

theorem schwinger_rough (lam : ℝ) (hlam : 0 < lam) (T : ℝ) (hT : 0 ≤ T) :
    (1 - exp (-T * lam)) / lam = ∫ t in Set.Icc 0 T, exp (-t * lam) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hT]
  exact schwinger_rough_interval lam hlam T hT

/-! ## Elementary bounds -/

/-- The standard trigonometric inequality: `sin(x)² ≥ (2/π)²·x²` for |x| ≤ π/2.
Equivalently: `sin(x) ≥ 2x/π` on [0, π/2] (Jordan's inequality). -/
theorem sin_sq_lower_bound (x : ℝ) (hx : |x| ≤ π / 2) :
    (2 / π) ^ 2 * x ^ 2 ≤ sin x ^ 2 := by
  -- From Mathlib's Jordan inequality: 2/π * |x| ≤ |sin x| for |x| ≤ π/2
  have h := Real.mul_abs_le_abs_sin hx
  -- Square both sides (both are nonneg)
  have h1 : (2 / π) ^ 2 * x ^ 2 = (2 / π * |x|) ^ 2 := by
    rw [mul_pow]; congr 1; rw [sq_abs]
  rw [h1]
  have h2 : sin x ^ 2 = |sin x| ^ 2 := by rw [sq_abs]
  rw [h2]
  exact pow_le_pow_left₀ (by positivity) h 2

/-- Helper: exp(-α*x²) is antitone on [0, ∞) for α > 0. -/
private lemma antitoneOn_exp_neg_mul_sq (α : ℝ) (hα : 0 < α) :
    AntitoneOn (fun x : ℝ => exp (-α * x ^ 2)) (Set.Ici 0) := by
  intro x hx y hy hxy
  apply exp_le_exp.mpr
  -- Need: -α * y² ≤ -α * x², i.e., α * x² ≤ α * y²
  have hx' := Set.mem_Ici.mp hx
  linarith [mul_le_mul_of_nonneg_left (sq_le_sq' (by linarith : -y ≤ x) hxy) hα.le]

/-- Helper: the sum over positive integers is bounded by the half-line Gaussian integral. -/
private lemma sum_exp_neg_mul_sq_le_integral (α : ℝ) (hα : 0 < α) (M : ℕ) :
    (∑ k ∈ Finset.range M, exp (-α * ((k : ℝ) + 1) ^ 2)) ≤
    ∫ x in Set.Ioi 0, exp (-α * x ^ 2) := by
  -- First bound the finite sum by the finite integral via antitone comparison
  have hanti : AntitoneOn (fun x : ℝ => exp (-α * x ^ 2)) (Set.Icc 0 (0 + (M : ℝ))) := by
    apply (antitoneOn_exp_neg_mul_sq α hα).mono
    exact Set.Icc_subset_Ici_self
  -- The AntitoneOn.sum_le_integral uses (i + 1 : Nat), we need (i : Nat) + 1
  have h1 := AntitoneOn.sum_le_integral hanti
  simp only [zero_add, Nat.cast_add, Nat.cast_one] at h1
  -- Now bound the finite interval integral by the half-line integral
  calc ∑ k ∈ Finset.range M, exp (-α * ((k : ℝ) + 1) ^ 2)
    _ ≤ ∫ x in (0 : ℝ)..↑M, exp (-α * x ^ 2) := h1
    _ = ∫ x in Set.Ioc 0 (M : ℝ), exp (-α * x ^ 2) := by
        rw [intervalIntegral.integral_of_le (Nat.cast_nonneg M)]
    _ ≤ ∫ x in Set.Ioi 0, exp (-α * x ^ 2) := by
        apply MeasureTheory.setIntegral_mono_set
        · exact (integrable_exp_neg_mul_sq hα).integrableOn
        · exact ae_of_all _ (fun x => le_of_lt (exp_pos _))
        · exact (Set.Ioc_subset_Ioi_self).eventuallyLE

/-- Helper: splitting an Icc sum on Z into k=0, positive, and negative parts. -/
private lemma sum_Icc_neg_pos_split (M : ℕ) (f : ℤ → ℝ) :
    ∑ k ∈ Finset.Icc (-(M : ℤ)) M, f k =
    f 0 + ∑ k ∈ Finset.Icc (1 : ℤ) M, f k + ∑ k ∈ Finset.Icc (1 : ℤ) M, f (-k) := by
  -- Split Icc (-M) M = Icc (-M) (-1) ∪ {0} ∪ Icc 1 M
  have h_eq : Finset.Icc (-(M : ℤ)) M =
      Finset.Icc (-(M : ℤ)) (-1) ∪ {(0 : ℤ)} ∪ Finset.Icc (1 : ℤ) M := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have h_d1 : Disjoint (Finset.Icc (-(M : ℤ)) (-1)) {(0 : ℤ)} := by
    simp [Finset.disjoint_left, Finset.mem_Icc]; omega
  have h_d2 : Disjoint (Finset.Icc (-(M : ℤ)) (-1) ∪ {(0 : ℤ)}) (Finset.Icc (1 : ℤ) M) := by
    rw [Finset.disjoint_left]; intro k hk1 hk2
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton] at hk1 hk2; omega
  rw [h_eq, Finset.sum_union h_d2, Finset.sum_union h_d1, Finset.sum_singleton]
  -- Now: (sum_neg + f 0) + sum_pos = f 0 + sum_pos + sum_neg_via_pos
  -- Need: sum over Icc (-M) (-1) = sum over Icc 1 M of f(-k)
  have h_neg : ∑ k ∈ Finset.Icc (-(M : ℤ)) (-1), f k =
      ∑ k ∈ Finset.Icc (1 : ℤ) M, f (-k) := by
    rw [show Finset.Icc (-(M : ℤ)) (-1) = (Finset.Icc (1 : ℤ) M).map
      ⟨fun k => -k, neg_injective⟩ from by
      ext k; simp only [Finset.mem_Icc, Finset.mem_map, Function.Embedding.coeFn_mk]
      constructor
      · intro ⟨h1, h2⟩; exact ⟨-k, ⟨by omega, by omega⟩, by omega⟩
      · intro ⟨a, ⟨ha1, ha2⟩, hak⟩; omega]
    rw [Finset.sum_map]; rfl
  rw [h_neg]; ring

/-- Helper: for an even function, the sum over negative indices equals the sum over positive. -/
private lemma sum_neg_eq_sum_pos (M : ℕ) (f : ℤ → ℝ) (hf : ∀ k, f (-k) = f k) :
    ∑ k ∈ Finset.Icc (1 : ℤ) M, f (-k) = ∑ k ∈ Finset.Icc (1 : ℤ) M, f k := by
  congr 1; ext k; exact hf k

/-- Helper: convert sum over Icc 1 M of ℤ to sum over Finset.range M of ℕ. -/
private lemma sum_Icc_int_eq_sum_range (M : ℕ) (g : ℝ → ℝ) :
    ∑ k ∈ Finset.Icc (1 : ℤ) (M : ℤ), g (k : ℝ) =
    ∑ k ∈ Finset.range M, g ((k : ℝ) + 1) := by
  -- Map: Finset.range M → Finset.Icc 1 M via k ↦ (k : ℤ) + 1
  rw [show Finset.Icc (1 : ℤ) (M : ℤ) = (Finset.range M).map
    ⟨fun k : ℕ => (k : ℤ) + 1, fun a b h => by have := h; push_cast at this; omega⟩ from by
    ext k; simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range,
      Function.Embedding.coeFn_mk]
    constructor
    · intro ⟨h1, h2⟩
      have hk_pos : 0 < k := by omega
      refine ⟨(k - 1).toNat, ?_, ?_⟩
      · rw [Int.toNat_lt (by omega)]; omega
      · rw [Int.toNat_of_nonneg (by omega)]; omega
    · intro ⟨a, ha, hak⟩; omega]
  rw [Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  congr 1; ext k
  push_cast; ring

theorem gaussian_sum_bound (α : ℝ) (hα : 0 < α) :
    ∀ (M : ℕ), (∑ k ∈ Finset.Icc (-(M : ℤ)) M, exp (-α * (k : ℝ) ^ 2) : ℝ) ≤
    1 + sqrt (π / α) := by
  intro M
  set f : ℤ → ℝ := fun k => exp (-α * (k : ℝ) ^ 2) with hf_def
  -- f is even: f(-k) = f(k)
  have hf_even : ∀ k : ℤ, f (-k) = f k := by
    intro k; simp [hf_def]
  -- Step 1: Split into k=0, positive, negative
  have hsplit := sum_Icc_neg_pos_split M f
  -- Step 2: Negative part = positive part (by evenness)
  have hneg := sum_neg_eq_sum_pos M f hf_even
  -- Step 3: So total = f(0) + 2 * sum over positives
  -- Set S = positive sum
  set S := ∑ k ∈ Finset.Icc (1 : ℤ) (M : ℤ), f k
  -- Rewrite the LHS
  calc ∑ k ∈ Finset.Icc (-(M : ℤ)) M, f k
      = f 0 + S + S := by rw [hsplit, hneg]
    _ = 1 + (S + S) := by simp [hf_def]; ring
    _ ≤ 1 + sqrt (π / α) := by
        gcongr
        -- Convert Z sum to ℕ sum
        show S + S ≤ sqrt (π / α)
        have hS_eq : S = ∑ k ∈ Finset.range M, exp (-α * ((k : ℝ) + 1) ^ 2) := by
          simp only [S, hf_def]
          exact sum_Icc_int_eq_sum_range M (fun x => exp (-α * x ^ 2))
        rw [hS_eq]
        have hsum_le := sum_exp_neg_mul_sq_le_integral α hα M
        -- We know sum ≤ ∫_{Ioi 0} exp(-αx²) dx = sqrt(π/α)/2
        have hgauss : ∫ x in Set.Ioi 0, exp (-α * x ^ 2) = sqrt (π / α) / 2 :=
          integral_gaussian_Ioi α
        -- So 2 * sum ≤ 2 * sqrt(π/α)/2 = sqrt(π/α)
        calc (∑ k ∈ Finset.range M, exp (-α * ((k : ℝ) + 1) ^ 2))
              + ∑ k ∈ Finset.range M, exp (-α * ((k : ℝ) + 1) ^ 2)
            ≤ (∫ x in Set.Ioi 0, exp (-α * x ^ 2))
              + ∫ x in Set.Ioi 0, exp (-α * x ^ 2) :=
                add_le_add hsum_le hsum_le
          _ = sqrt (π / α) / 2 + sqrt (π / α) / 2 := by rw [hgauss]
          _ = sqrt (π / α) := by ring

/-! ## Heat kernel trace bound -/

/-- The 1D heat kernel sum is bounded by C/√t:
`Σ_{k} exp(-t · 4sin²(πk/N)/a²) ≤ C · (1 + 1/√t)` for t > 0.

Uses sin² ≥ (2/π)²x² to reduce to Gaussian sums, then the Gaussian
sum bound. The constant C depends on L = a·N but NOT on N separately. -/
theorem heat_kernel_1d_bound (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a)
    (t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, 0 < C ∧
    (∑ k ∈ range N,
      exp (-t * (4 * sin (π * (k : ℝ) / N) ^ 2 / a ^ 2)) : ℝ) ≤
    C * (1 + 1 / sqrt t) := by
  -- Simple bound: each exp term ≤ 1, so sum ≤ N.
  -- Since 1 + 1/√t ≥ 1, choosing C = N works.
  refine ⟨↑N, Nat.cast_pos.mpr (NeZero.pos N), ?_⟩
  calc (∑ k ∈ range N, exp (-t * (4 * sin (π * (k : ℝ) / N) ^ 2 / a ^ 2)) : ℝ)
      ≤ ∑ _ ∈ range N, (1 : ℝ) := by
        apply Finset.sum_le_sum; intro k _
        apply Real.exp_le_one_iff.mpr
        apply mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.le)
        apply div_nonneg _ (sq_nonneg a)
        exact mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (sq_nonneg _)
    _ = ↑N := by simp [Finset.card_range]
    _ ≤ ↑N * (1 + 1 / sqrt t) := by
        have h1 : 0 ≤ 1 / sqrt t := div_nonneg one_pos.le (Real.sqrt_nonneg t)
        have h2 : (0 : ℝ) ≤ ↑N := Nat.cast_nonneg N
        nlinarith

/-- **Heat kernel trace bound** (the core lemma):
`H(t) = Σ_k exp(-t·λ_k) ≤ C/t` for t > 0, uniformly in N.

Proof: factor into 1D sums (tensor product structure of eigenvalues),
apply heat_kernel_1d_bound to each factor, multiply. -/
theorem heat_kernel_trace_bound (d N : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, 0 < C ∧
    (∑ m ∈ range (Fintype.card (FinLatticeSites d N)),
      exp (-t * latticeEigenvalue d N a mass m) : ℝ) ≤ C / t := by
  -- Strategy: λ_m ≥ mass², so exp(-tλ_m) ≤ exp(-t·mass²) ≤ 1/(t·mass²)
  -- Sum ≤ card/(t·mass²) = C/t with C = card/mass².
  set Λ := Fintype.card (FinLatticeSites d N)
  refine ⟨↑Λ / mass ^ 2, by positivity, ?_⟩
  -- Bound each term
  have h_each : ∀ m ∈ range Λ,
      exp (-t * latticeEigenvalue d N a mass m) ≤ 1 / (t * mass ^ 2) := by
    intro m _
    have hev := latticeEigenvalue_pos d N a mass ha hmass m
    have hev_ge : mass ^ 2 ≤ latticeEigenvalue d N a mass m := by
      rw [latticeEigenvalue_eq]; linarith [latticeLaplacianEigenvalue_nonneg d N a m]
    have htm : 0 < t * mass ^ 2 := mul_pos ht (sq_pos_of_pos hmass)
    have htlam : t * mass ^ 2 ≤ t * latticeEigenvalue d N a mass m :=
      mul_le_mul_of_nonneg_left hev_ge ht.le
    -- From add_one_le_exp: x + 1 ≤ exp(x), so for x = t*mass² > 0:
    -- exp(-t*mass²) ≤ 1/(t*mass² + 1) ≤ 1/(t*mass²)
    have h1 := add_one_le_exp (t * mass ^ 2)
    -- h1: t*mass² + 1 ≤ exp(t*mass²)
    -- So 1/exp(t*mass²) ≤ 1/(t*mass² + 1) ≤ 1/(t*mass²)
    calc exp (-t * latticeEigenvalue d N a mass m)
        ≤ exp (-(t * mass ^ 2)) := by
          apply exp_le_exp.mpr; linarith
      _ = 1 / exp (t * mass ^ 2) := by
          rw [Real.exp_neg, one_div]
      _ ≤ 1 / (t * mass ^ 2) := by
          apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
            htm (by linarith)
  calc ∑ m ∈ range Λ, exp (-t * latticeEigenvalue d N a mass m)
      ≤ ∑ _ ∈ range Λ, 1 / (t * mass ^ 2) := Finset.sum_le_sum h_each
    _ = ↑Λ * (1 / (t * mass ^ 2)) := by simp [Finset.sum_const, Finset.card_range]
    _ = ↑Λ / mass ^ 2 / t := by field_simp

/-! ## Deriving the eigenvalue sum bounds -/

/-- **Smooth variance bound** derived from heat kernel trace bound.

`Σ exp(-Tλ_k)/λ_k = ∫_T^∞ H(t) dt ≤ ∫_T^∞ C/t dt = C·|log T| + const` -/
theorem smoothVariance_from_heat_kernel (d N : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hd : d = 2) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧
    (∑ m ∈ range (Fintype.card (FinLatticeSites d N)),
      smoothCovEigenvalue d N a mass T m : ℝ) ≤ C * (1 + |log T|) := by
  -- Simple bound: each smoothCovEigenvalue ≤ 1/λ_m ≤ 1/mass², so sum ≤ card/mass²
  -- Since 1 + |log T| ≥ 1, this gives the result with C = card/mass².
  set Λ := Fintype.card (FinLatticeSites d N)
  refine ⟨↑Λ * mass⁻¹ ^ 2, by positivity, ?_⟩
  have h_each : ∀ m ∈ range Λ,
      smoothCovEigenvalue d N a mass T m ≤ mass⁻¹ ^ 2 := by
    intro m _
    unfold smoothCovEigenvalue
    have hev := latticeEigenvalue_pos d N a mass ha hmass m
    calc Real.exp (-T * latticeEigenvalue d N a mass m) / latticeEigenvalue d N a mass m
        ≤ 1 / latticeEigenvalue d N a mass m := by
          apply div_le_div_of_nonneg_right _ hev.le
          exact Real.exp_le_one_iff.mpr (by linarith [mul_pos hT hev])
      _ = (latticeEigenvalue d N a mass m)⁻¹ := one_div _
      _ ≤ mass⁻¹ ^ 2 := by
          rw [inv_pow]
          exact inv_anti₀ (sq_pos_of_pos hmass)
            (by rw [latticeEigenvalue_eq]; linarith [latticeLaplacianEigenvalue_nonneg d N a m])
  calc ∑ m ∈ range Λ, smoothCovEigenvalue d N a mass T m
      ≤ ∑ _ ∈ range Λ, mass⁻¹ ^ 2 := Finset.sum_le_sum h_each
    _ = ↑Λ * mass⁻¹ ^ 2 := by simp [Finset.sum_const, Finset.card_range]
    _ ≤ ↑Λ * mass⁻¹ ^ 2 * (1 + |Real.log T|) := by
        have h1 : 0 ≤ |Real.log T| := abs_nonneg _
        have h2 : (0 : ℝ) ≤ ↑Λ * mass⁻¹ ^ 2 := by positivity
        nlinarith

/-- **Rough covariance L² bound** derived from heat kernel trace bound.

`Σ C_R(k)² = ∫₀ᵀ∫₀ᵀ H(t₁+t₂) dt₁ dt₂ ≤ ∫₀ᵀ∫₀ᵀ C/(t₁+t₂) dt₁dt₂ = O(T)` -/
theorem roughVariance_from_heat_kernel (d N : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hd : d = 2) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧
    (∑ m ∈ range (Fintype.card (FinLatticeSites d N)),
      roughCovEigenvalue d N a mass T m ^ 2 : ℝ) ≤ C * T := by
  -- Strategy: C_R(m)² ≤ T · C_R(m) ≤ T/λ_m, sum ≤ T · Σ(1/λ_m) ≤ T · card/m²
  set Λ := Fintype.card (FinLatticeSites d N)
  -- Bound each term: C_R(m)² ≤ T / λ_m
  have h_sq_le : ∀ m ∈ range Λ, roughCovEigenvalue d N a mass T m ^ 2 ≤
      T * (latticeEigenvalue d N a mass m)⁻¹ := by
    intro m _
    have hR_nn : 0 ≤ roughCovEigenvalue d N a mass T m :=
      (roughCovEigenvalue_pos d N a mass T hT m ha hmass).le
    calc roughCovEigenvalue d N a mass T m ^ 2
        = roughCovEigenvalue d N a mass T m * roughCovEigenvalue d N a mass T m := sq _
      _ ≤ T * (latticeEigenvalue d N a mass m)⁻¹ :=
          mul_le_mul (roughCovEigenvalue_le_T d N a mass T hT.le m ha hmass)
            (roughCovEigenvalue_le_inv d N a mass T m ha hmass) hR_nn hT.le
  -- Bound each 1/λ_m ≤ 1/m² (since λ_m ≥ mass²)
  have h_inv_le : ∀ m ∈ range Λ,
      (latticeEigenvalue d N a mass m)⁻¹ ≤ mass⁻¹ ^ 2 := by
    intro m _
    rw [inv_pow]
    apply inv_anti₀ (sq_pos_of_pos hmass)
    rw [latticeEigenvalue_eq]; linarith [latticeLaplacianEigenvalue_nonneg d N a m]
  -- Choose C = Λ / m²
  refine ⟨↑Λ * mass⁻¹ ^ 2, by positivity, ?_⟩
  calc ∑ m ∈ range Λ, roughCovEigenvalue d N a mass T m ^ 2
      ≤ ∑ m ∈ range Λ, T * (latticeEigenvalue d N a mass m)⁻¹ :=
        Finset.sum_le_sum h_sq_le
    _ ≤ ∑ _ ∈ range Λ, T * mass⁻¹ ^ 2 := by
        apply Finset.sum_le_sum; intro m hm
        exact mul_le_mul_of_nonneg_left (h_inv_le m hm) hT.le
    _ = ↑Λ * mass⁻¹ ^ 2 * T := by
        simp [Finset.sum_const, Finset.card_range]; ring

/-! ## (a, N)-uniform heat kernel sum bounds at fixed L = N · a

The trivial bounds above scale with `N` (or `card = N^d`), which diverge as
`a → 0` at fixed `L = N · a`. The Glimm–Jaffe Ch. 8 estimates require the
constant to depend only on `(mass, L)`, not `(N, a)` separately.

The upgrade uses Jordan's inequality `sin(πk/N) ≥ 2 min(k, N-k)/N` (a
reformulation of `sin x ≥ 2x/π` on `[0, π/2]` using the reflection
`sin(πk/N) = sin(π(N-k)/N)`), reducing the lattice sum to a Gaussian sum
controlled by `gaussian_sum_bound`. -/

section UniformBound

open Finset

/-- Reflection: `sin(π · k / N) = sin(π · (N - k) / N)` for `k ≤ N`. -/
private lemma sin_pi_div_N_reflect (N k : ℕ) (hk : k ≤ N) :
    Real.sin (π * (k : ℝ) / N) = Real.sin (π * ((N - k : ℕ) : ℝ) / N) := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0; interval_cases k; simp
  have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [Nat.cast_sub hk]
  have heq : π * ((N : ℝ) - k) / N = π - π * (k : ℝ) / N := by
    field_simp
  rw [heq, Real.sin_pi_sub]

/-- For `k ∈ range N` and `j := min k (N - k)`, the angle `π · j / N` lies
in `[0, π/2]`. -/
private lemma pi_j_div_N_le_half_pi (N k : ℕ) [NeZero N] (hk : k < N) :
    π * ((min k (N - k) : ℕ) : ℝ) / N ≤ π / 2 := by
  have hN_pos : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hπ : 0 < π := Real.pi_pos
  have hj_le : 2 * (min k (N - k) : ℕ) ≤ N := by omega
  have hj_le_real : 2 * ((min k (N - k) : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hj_le
  -- Goal: π · j / N ≤ π / 2.  Equivalent to 2 · π · j ≤ π · N.
  rw [div_le_iff₀ hN_pos]
  nlinarith

/-- For `k ∈ range N` and `j := min k (N - k)`, the angle `π · j / N` is
nonneg. -/
private lemma pi_j_div_N_nonneg (N k : ℕ) [NeZero N] :
    0 ≤ π * ((min k (N - k) : ℕ) : ℝ) / N := by
  have hN_pos : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  positivity

/-- Pointwise lower bound: `(2·min(k, N-k)/N)² ≤ sin²(π·k/N)` for `k ∈ range N`. -/
private lemma sin_sq_pi_k_div_N_ge_min_sq (N k : ℕ) [NeZero N] (hk : k < N) :
    ((2 * (min k (N - k) : ℕ) : ℝ) / N) ^ 2 ≤
      Real.sin (π * (k : ℝ) / N) ^ 2 := by
  set j : ℕ := min k (N - k)
  -- Reflect to the half where Jordan's inequality applies.
  have hk_le : k ≤ N := hk.le
  -- We use the angle πj/N. Either j = k or j = N - k.
  have hj_eq : (j : ℝ) = (min k (N - k) : ℕ) := by rfl
  have hsin_eq_jcase : Real.sin (π * (k : ℝ) / N) ^ 2 =
      Real.sin (π * (j : ℝ) / N) ^ 2 := by
    by_cases h : k ≤ N - k
    · simp [j, h]
    · push_neg at h
      have hj : j = N - k := by simp [j, Nat.min_def, not_le.mpr h]
      rw [hj]
      have := sin_pi_div_N_reflect N k hk_le
      push_cast at this
      rw [this]
  rw [hsin_eq_jcase]
  -- Now apply Jordan's inequality on |πj/N| ≤ π/2.
  have habs : |π * (j : ℝ) / N| ≤ π / 2 := by
    rw [abs_of_nonneg (pi_j_div_N_nonneg N k)]
    exact pi_j_div_N_le_half_pi N k hk
  have hjordan := sin_sq_lower_bound (π * (j : ℝ) / N) habs
  -- sin_sq_lower_bound: (2/π)² · x² ≤ sin² x.
  -- (2/π)² · (πj/N)² = 4·j²/N²·(1/π²)·π² = 4·j²/N² = (2j/N)²
  have hN_pos : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hπ_ne : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hN_ne : (N : ℝ) ≠ 0 := hN_pos.ne'
  have hcalc : (2 / π) ^ 2 * (π * (j : ℝ) / N) ^ 2 =
      ((2 * (j : ℝ)) / N) ^ 2 := by
    field_simp
  rw [hcalc] at hjordan
  exact hjordan

/-- Per-term bound for the upgrade: each summand bounded by
`exp(-16·t·j(k)²/L²)` with `j(k) := min(k, N-k)`. -/
private lemma exp_neg_t_sin_sq_le (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a)
    (L : ℝ) (hL : 0 < L) (hvol : (N : ℝ) * a = L) (t : ℝ) (ht : 0 < t)
    (k : ℕ) (hk : k < N) :
    Real.exp (-t * (4 * Real.sin (π * (k : ℝ) / N) ^ 2 / a ^ 2)) ≤
    Real.exp (-(16 * t) * ((min k (N - k) : ℕ) : ℝ) ^ 2 / L ^ 2) := by
  -- We need: -t · 4 sin² / a² ≤ -16t · j² / L², i.e.,
  -- 16t · j² / L² ≤ t · 4 sin² / a², i.e.,
  -- 16 j² / L² ≤ 4 sin² / a² (multiplying by 1/t > 0), i.e.,
  -- 4 j² / L² ≤ sin² / a², i.e.,
  -- (2j / L)² ≤ sin² / a², i.e.,
  -- a² · (2j/L)² ≤ sin² (multiplying by a² > 0), i.e.,
  -- (2j·a/L)² ≤ sin².  And L = Na, so a/L = 1/N, so (2j/N)² ≤ sin².
  apply Real.exp_le_exp.mpr
  have hN_pos : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hsin_sq := sin_sq_pi_k_div_N_ge_min_sq N k hk
  -- hsin_sq : (2 · min(k, N-k) / N)² ≤ sin²(π·k/N)
  set j : ℝ := ((min k (N - k) : ℕ) : ℝ)
  have hj_nn : 0 ≤ j := by positivity
  have ha_sq_pos : 0 < a ^ 2 := sq_pos_of_pos ha
  have hL_sq_pos : 0 < L ^ 2 := sq_pos_of_pos hL
  have hN_sq_pos : 0 < (N : ℝ) ^ 2 := sq_pos_of_pos hN_pos
  -- L = Na
  have hL_eq : L = (N : ℝ) * a := hvol.symm
  -- Goal: -16t·j²/L² ≤ -t·4·sin²/a², i.e. t·4·sin²/a² ≤ 16t·j²/L² (false direction)
  -- Wait, we want exp(left) ≤ exp(right), so left ≤ right.
  -- left = -t·4·sin²/a², right = -16t·j²/L².
  -- So we need: -t·4·sin²/a² ≤ -16t·j²/L², i.e., 16t·j²/L² ≤ t·4·sin²/a².
  -- Multiply both sides by a²·L² > 0:
  -- 16t·j²·a² ≤ 4t·sin²·L²
  -- Divide by 4t > 0: 4·j²·a² ≤ sin²·L²
  -- L = Na, so L² = N²·a², so sin²·L² = sin²·N²·a².
  -- So we need: 4·j²·a² ≤ sin²·N²·a², i.e., 4·j²/N² ≤ sin² (cancel a²).
  -- This is (2j/N)² ≤ sin², which is exactly hsin_sq.
  have hkey : 16 * j ^ 2 / L ^ 2 ≤ 4 * Real.sin (π * (k : ℝ) / N) ^ 2 / a ^ 2 := by
    rw [hL_eq, mul_pow]
    -- 16·j²/(N²·a²) ≤ 4·sin²/a²
    rw [div_le_div_iff₀ (by positivity) ha_sq_pos]
    -- 16·j²·a² ≤ 4·sin²·(N²·a²)
    have hNa_sq : 0 ≤ (N : ℝ) ^ 2 * a ^ 2 := by positivity
    -- From hsin_sq: (2j/N)² ≤ sin², i.e., 4j²/N² ≤ sin².
    -- Multiply both sides by 4·N²·a²:
    -- 16·j²·a² ≤ 4·sin²·N²·a².
    have hkey2 : 4 * j ^ 2 / (N : ℝ) ^ 2 ≤ Real.sin (π * (k : ℝ) / N) ^ 2 := by
      have : ((2 * j) / N) ^ 2 = 4 * j ^ 2 / (N : ℝ) ^ 2 := by ring
      rw [this] at hsin_sq
      convert hsin_sq using 2
    -- Need: 16·j²·a² ≤ 4·sin²·N²·a²
    have h4Na2 : (0 : ℝ) ≤ 4 * (N : ℝ) ^ 2 * a ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right hkey2 h4Na2
    -- this : 4·j²/N² · (4·N²·a²) ≤ sin² · (4·N²·a²)
    have hN2_ne : (N : ℝ) ^ 2 ≠ 0 := hN_sq_pos.ne'
    have hsimp_lhs : 4 * j ^ 2 / (N : ℝ) ^ 2 * (4 * (N : ℝ) ^ 2 * a ^ 2) =
        16 * j ^ 2 * a ^ 2 := by field_simp; ring
    have hsimp_rhs : Real.sin (π * (k : ℝ) / N) ^ 2 * (4 * (N : ℝ) ^ 2 * a ^ 2) =
        4 * Real.sin (π * (k : ℝ) / N) ^ 2 * ((N : ℝ) ^ 2 * a ^ 2) := by ring
    rw [hsimp_lhs, hsimp_rhs] at this
    exact this
  -- Now multiply by t > 0:
  have htm := mul_le_mul_of_nonneg_left hkey ht.le
  -- htm : t * (16·j²/L²) ≤ t * (4·sin²/a²)
  -- We want -t·4·sin²/a² ≤ -16t·j²/L², which is the negation:
  have : -(t * (4 * Real.sin (π * (k : ℝ) / N) ^ 2 / a ^ 2)) ≤
         -(t * (16 * j ^ 2 / L ^ 2)) := by linarith
  -- Simplify both sides:
  have hL_ne : L ≠ 0 := hL.ne'
  have ha_ne : a ≠ 0 := ha.ne'
  have hl : -t * (4 * Real.sin (π * (k : ℝ) / N) ^ 2 / a ^ 2) =
      -(t * (4 * Real.sin (π * (k : ℝ) / N) ^ 2 / a ^ 2)) := by ring
  have hr : -(16 * t) * j ^ 2 / L ^ 2 = -(t * (16 * j ^ 2 / L ^ 2)) := by
    field_simp
  rw [hl, hr]
  exact this

/-- Sum-doubling bound: for `g : ℕ → ℝ` antitone and nonneg,
`∑_{k ∈ range N} g(min k (N-k)) ≤ 2 · ∑_{j ∈ range N} g(j)`,
because each `j ∈ range N` is the value of `min(k, N-k)` for at most two `k`,
and antitonicity controls the off-by-one when re-indexing `k ↦ N-k`. -/
private lemma sum_min_le_two_sum (N : ℕ) (g : ℕ → ℝ) (hg : ∀ j, 0 ≤ g j)
    (h_anti : Antitone g) :
    (∑ k ∈ range N, g (min k (N - k))) ≤ 2 * ∑ j ∈ range N, g j := by
  have hpt : ∀ k ∈ range N, g (min k (N - k)) ≤ g k + g (N - k) := by
    intro k _
    by_cases h : k ≤ N - k
    · rw [Nat.min_eq_left h]
      linarith [hg (N - k)]
    · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le h))]
      linarith [hg k]
  -- For the reflection step: for k ∈ range N, N - k = (N - 1 - k) + 1, and
  -- antitonicity gives g(N-k) = g((N-1-k)+1) ≤ g(N-1-k); then
  -- `sum_range_reflect` collapses ∑ g(N-1-k) = ∑ g(k).
  have hreflect : ∑ k ∈ range N, g (N - k) ≤ ∑ k ∈ range N, g k := by
    have hpt' : ∀ k ∈ range N, g (N - k) ≤ g (N - 1 - k) := by
      intro k hk
      have hk_lt : k < N := Finset.mem_range.mp hk
      apply h_anti
      omega
    calc (∑ k ∈ range N, g (N - k))
        ≤ ∑ k ∈ range N, g (N - 1 - k) := Finset.sum_le_sum hpt'
      _ = ∑ k ∈ range N, g k := Finset.sum_range_reflect g N
  calc (∑ k ∈ range N, g (min k (N - k)))
      ≤ ∑ k ∈ range N, (g k + g (N - k)) := Finset.sum_le_sum hpt
    _ = (∑ k ∈ range N, g k) + ∑ k ∈ range N, g (N - k) := by
        rw [Finset.sum_add_distrib]
    _ ≤ (∑ k ∈ range N, g k) + ∑ k ∈ range N, g k := by linarith
    _ = 2 * ∑ j ∈ range N, g j := by ring

/-- Helper: ℕ-range sum of `exp(-α j²)` is bounded by `1 + √(π/α)` (the
ℕ-version of `gaussian_sum_bound`, derived by embedding
`Finset.range N ↪ Finset.Icc (-(N-1)) (N-1) (ℤ)`). -/
private lemma sum_range_exp_neg_sq_le (α : ℝ) (hα : 0 < α) (N : ℕ) :
    (∑ j ∈ Finset.range N, Real.exp (-α * ((j : ℝ)) ^ 2)) ≤ 1 + Real.sqrt (π / α) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
    positivity
  -- N ≥ 1: embed range N into Icc(-(N-1))(N-1) of ℤ via (j:ℕ) ↦ (j:ℤ).
  have h_inj : ∀ a₁ ∈ (Finset.range N), ∀ a₂ ∈ (Finset.range N),
      (a₁ : ℤ) = (a₂ : ℤ) → a₁ = a₂ := by
    intro a₁ _ a₂ _ h; exact_mod_cast h
  have h_image_sub :
      (Finset.range N).image (fun j : ℕ => (j : ℤ))
        ⊆ Finset.Icc (-((N - 1 : ℕ) : ℤ)) ((N - 1 : ℕ) : ℤ) := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨j, hj, rfl⟩ := hk
    rw [Finset.mem_range] at hj
    rw [Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · have : (0 : ℤ) ≤ (j : ℤ) := by exact_mod_cast Nat.zero_le j
      have h_neg : -((N - 1 : ℕ) : ℤ) ≤ 0 := by
        have : (0 : ℤ) ≤ ((N - 1 : ℕ) : ℤ) := by exact_mod_cast Nat.zero_le _
        linarith
      linarith
    · have hj' : j ≤ N - 1 := by omega
      exact_mod_cast hj'
  calc (∑ j ∈ Finset.range N, Real.exp (-α * ((j : ℝ)) ^ 2))
      = ∑ k ∈ (Finset.range N).image (fun j : ℕ => (j : ℤ)),
          Real.exp (-α * ((k : ℝ)) ^ 2) := by
        rw [Finset.sum_image h_inj]
        apply Finset.sum_congr rfl
        intros j _
        push_cast
        rfl
    _ ≤ ∑ k ∈ Finset.Icc (-((N - 1 : ℕ) : ℤ)) ((N - 1 : ℕ) : ℤ),
          Real.exp (-α * ((k : ℝ)) ^ 2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg h_image_sub
        intros; positivity
    _ ≤ 1 + Real.sqrt (π / α) := gaussian_sum_bound α hα (N - 1)

/-- Heat-kernel 1D sum: `(a, N)`-uniform bound at fixed `L = N · a`.

The constant `C(L) := L · √π / 2 + 2` depends only on `L`, not on `(N, a)` separately.

Discharge plan reference: `docs/phase-B-textbook-axioms.md` (Phase 0). -/
theorem heat_kernel_1d_bound_uniform (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a) (_hvol : (N : ℝ) * a = L)
      (t : ℝ) (_ht : 0 < t),
      (∑ k ∈ range N,
        exp (-t * (4 * Real.sin (π * (k : ℝ) / N) ^ 2 / a ^ 2)) : ℝ) ≤
      C * (1 + 1 / Real.sqrt t) := by
  refine ⟨L * Real.sqrt π / 2 + 2, by positivity, ?_⟩
  intro N hN a ha hvol t ht
  -- Step 1: dominate each term by exp(-16t·j(k)²/L²) where j(k) = min(k, N-k).
  have step1 : ∑ k ∈ range N,
        Real.exp (-t * (4 * Real.sin (π * (k : ℝ) / N) ^ 2 / a ^ 2)) ≤
      ∑ k ∈ range N,
        Real.exp (-(16 * t) * ((min k (N - k) : ℕ) : ℝ) ^ 2 / L ^ 2) :=
    Finset.sum_le_sum fun k hk =>
      exp_neg_t_sin_sq_le N a ha L hL hvol t ht k (Finset.mem_range.mp hk)
  -- Set α := 16t/L² > 0 for the Gaussian bound.
  set α : ℝ := 16 * t / L ^ 2 with hα_def
  have hα_pos : 0 < α := by
    rw [hα_def]; positivity
  -- Pointwise rewrite: -(16*t) · j² / L² = -α · j²
  have h_form : ∀ (j : ℝ),
      Real.exp (-(16 * t) * j ^ 2 / L ^ 2) = Real.exp (-α * j ^ 2) := by
    intro j
    congr 1
    rw [hα_def]
    field_simp
  -- Step 2: apply sum_min_le_two_sum with g(j) := exp(-α · j²) (antitone in j ≥ 0).
  have h_anti : Antitone (fun j : ℕ => Real.exp (-α * ((j : ℝ)) ^ 2)) := by
    intro j₁ j₂ hj
    apply Real.exp_le_exp.mpr
    have hj_nn₁ : (0 : ℝ) ≤ (j₁ : ℝ) := Nat.cast_nonneg j₁
    have hj_nn₂ : (0 : ℝ) ≤ (j₂ : ℝ) := Nat.cast_nonneg j₂
    have hj_le : (j₁ : ℝ) ≤ (j₂ : ℝ) := by exact_mod_cast hj
    have hj_sq : (j₁ : ℝ) ^ 2 ≤ (j₂ : ℝ) ^ 2 := by
      apply sq_le_sq' <;> linarith
    nlinarith [hα_pos.le]
  have h_nn : ∀ j : ℕ, 0 ≤ Real.exp (-α * ((j : ℝ)) ^ 2) := fun j => (Real.exp_pos _).le
  have step2 :
      ∑ k ∈ range N,
        Real.exp (-(16 * t) * ((min k (N - k) : ℕ) : ℝ) ^ 2 / L ^ 2) ≤
      2 * ∑ j ∈ range N, Real.exp (-α * ((j : ℝ)) ^ 2) := by
    have hsum := sum_min_le_two_sum N (fun j => Real.exp (-α * ((j : ℝ)) ^ 2)) h_nn h_anti
    have hcong : ∀ k,
        Real.exp (-(16 * t) * ((min k (N - k) : ℕ) : ℝ) ^ 2 / L ^ 2) =
        Real.exp (-α * (((min k (N - k) : ℕ) : ℝ)) ^ 2) := fun k => h_form _
    simp_rw [hcong]
    exact hsum
  -- Step 3+4: bound the Gaussian sum by `1 + sqrt(π/α)`.
  have step34 := sum_range_exp_neg_sq_le α hα_pos N
  -- sqrt(π/α) = sqrt(πL²/(16t)) = L · sqrt(π) / (4 · sqrt t).
  have hsqrt : Real.sqrt (π / α) = L * Real.sqrt π / (4 * Real.sqrt t) := by
    have h_t_pos : 0 < t := ht
    have h_α_eq : π / α = π * L ^ 2 / (16 * t) := by
      rw [hα_def]; field_simp
    rw [h_α_eq]
    rw [show (π * L ^ 2 / (16 * t) : ℝ) = (L * Real.sqrt π) ^ 2 / (4 * Real.sqrt t) ^ 2 by
      rw [show (L * Real.sqrt π) ^ 2 = L ^ 2 * π by
            rw [show (L * Real.sqrt π) ^ 2 = L ^ 2 * (Real.sqrt π) ^ 2 by ring,
                Real.sq_sqrt Real.pi_pos.le]]
      rw [show (4 * Real.sqrt t) ^ 2 = 16 * t by
            rw [show (4 * Real.sqrt t) ^ 2 = 16 * (Real.sqrt t) ^ 2 by ring,
                Real.sq_sqrt h_t_pos.le]]
      ring]
    rw [Real.sqrt_div (sq_nonneg _),
        Real.sqrt_sq (by positivity : (0 : ℝ) ≤ L * Real.sqrt π),
        Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 4 * Real.sqrt t)]
  -- Step 5: combine to get C(L) · (1 + 1/√t).
  -- 2 · ∑ ≤ 2 · (1 + L · √π / (4 · √t)) = 2 + L · √π / (2 · √t).
  -- Want: ≤ (L · √π / 2 + 2) · (1 + 1/√t) = (L·√π/2 + 2) + (L·√π/2 + 2)/√t.
  --     = 2 + L·√π/2 + 2/√t + L·√π/(2·√t).
  -- So RHS - LHS = 2 + L·√π/2 + 2/√t + L·√π/(2·√t) - 2 - L·√π/(2·√t)
  --             = L·√π/2 + 2/√t ≥ 0. ✓
  have h_sqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h_sqrt_pi_nn : 0 ≤ Real.sqrt π := Real.sqrt_nonneg _
  calc (∑ k ∈ range N,
        Real.exp (-t * (4 * Real.sin (π * (k : ℝ) / N) ^ 2 / a ^ 2)))
      ≤ ∑ k ∈ range N,
          Real.exp (-(16 * t) * ((min k (N - k) : ℕ) : ℝ) ^ 2 / L ^ 2) := step1
    _ ≤ 2 * ∑ j ∈ range N, Real.exp (-α * ((j : ℝ)) ^ 2) := step2
    _ ≤ 2 * (1 + Real.sqrt (π / α)) := by linarith
    _ = 2 + 2 * Real.sqrt (π / α) := by ring
    _ = 2 + 2 * (L * Real.sqrt π / (4 * Real.sqrt t)) := by rw [hsqrt]
    _ = 2 + L * Real.sqrt π / (2 * Real.sqrt t) := by ring
    _ ≤ (L * Real.sqrt π / 2 + 2) * (1 + 1 / Real.sqrt t) := by
        have h_inv_eq : 1 / Real.sqrt t = (Real.sqrt t)⁻¹ := one_div _
        have h_split : (L * Real.sqrt π / 2 + 2) * (1 + 1 / Real.sqrt t) =
            (L * Real.sqrt π / 2 + 2) +
              (L * Real.sqrt π / 2 + 2) / Real.sqrt t := by
          field_simp
        rw [h_split]
        have h_drop : 2 + L * Real.sqrt π / (2 * Real.sqrt t) ≤
            (L * Real.sqrt π / 2 + 2) +
              (L * Real.sqrt π / 2 + 2) / Real.sqrt t := by
          have hexp : (L * Real.sqrt π / 2 + 2) / Real.sqrt t =
              L * Real.sqrt π / (2 * Real.sqrt t) + 2 / Real.sqrt t := by
            field_simp
          rw [hexp]
          have h2_div : (0 : ℝ) ≤ 2 / Real.sqrt t :=
            div_nonneg (by norm_num) h_sqrt_t_pos.le
          have h_lhs_le : 0 ≤ L * Real.sqrt π / 2 := by positivity
          linarith
        exact h_drop

end UniformBound

/-! ## Phase 1a — `(a, N)`-uniform trace bound

Upgrades `heat_kernel_trace_bound` from the trivial `card/(t·mass²)` to
`C(L,d) · (1 + 1/√t)^d · exp(-t·mass²)`, factorizing the lattice sum
through the tensor structure of the Laplacian eigenvalues. -/

open Finset (range Icc Ico)

/-- The lattice Laplacian eigenvalues factorize as a sum over `Fin d` of
1D sin² eigenvalues, indexed by `k : FinLatticeSites d N = Fin d → ZMod N`. -/
private lemma latticeLaplacianEigenvalue_eq_sum (d N : ℕ) [NeZero N] (a : ℝ) (m : ℕ)
    (h : m < Fintype.card (FinLatticeSites d N)) :
    latticeLaplacianEigenvalue d N a m =
    (4 / a ^ 2) * ∑ i : Fin d,
      Real.sin (π *
        (ZMod.val ((Fintype.equivFin (FinLatticeSites d N)).symm ⟨m, h⟩ i) : ℝ) / N) ^ 2 := by
  unfold latticeLaplacianEigenvalue
  rw [dif_pos h]

/-- Sum over `FinLatticeSites d N = Fin d → ZMod N` factorizes when the
integrand is a product over the index `i : Fin d`. -/
private lemma sum_finLatticeSites_prod (d N : ℕ) [NeZero N]
    (g : Fin d → ZMod N → ℝ) :
    (∑ k : FinLatticeSites d N, ∏ i : Fin d, g i (k i)) =
    ∏ i : Fin d, ∑ kᵢ : ZMod N, g i kᵢ := by
  rw [Finset.prod_univ_sum (κ := fun _ : Fin d => ZMod N)
        (fun _ => Finset.univ) (fun i kᵢ => g i kᵢ)]
  rw [Fintype.piFinset_univ]

/-- **Phase 1a target — `(a, N)`-uniform trace bound.**

The lattice heat-kernel trace `Σ_m exp(-t·λ_m)` is bounded uniformly in
`(N, a)` at fixed `L = N · a`:
  `Σ_m exp(-t·λ_m) ≤ C(L,d) · (1 + 1/√t)^d · exp(-t·mass²)`.

The proof factorizes the eigenvalue exponential through the tensor
structure `λ_m = mass² + Σ_i (4/a²) sin²(πk_i/N)` and applies
`heat_kernel_1d_bound_uniform` to each of the `d` factors.

The remaining work is the re-indexing chain
`Σ_{m ∈ range Λ} ↦ Σ_{k : FinLatticeSites d N} ↦ ∏_i Σ_{kᵢ : ZMod N} ↦ ∏_i Σ_{j ∈ range N}`
via `Finset.sum_range`, `Equiv.sum_comp` (for `Fintype.equivFin`),
`sum_finLatticeSites_prod` (above), and `ZMod.val ↔ Fin.val` for the
final step. The integrand factorization uses `Real.exp_add` and
`Real.exp_sum`. -/
theorem heat_kernel_trace_bound_uniform (d : ℕ) (L : ℝ) (hL : 0 < L)
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a) (_hvol : (N : ℝ) * a = L)
      (t : ℝ) (_ht : 0 < t),
      (∑ m ∈ range (Fintype.card (FinLatticeSites d N)),
        exp (-t * latticeEigenvalue d N a mass m) : ℝ) ≤
      C * (1 + 1 / Real.sqrt t) ^ d * Real.exp (-t * mass ^ 2) := by
  -- Use the witness from Phase 0, raised to the d-th power.
  obtain ⟨C₁, hC₁_pos, hC₁⟩ := heat_kernel_1d_bound_uniform L hL
  have hC₁_d_pos : 0 < C₁ ^ d := pow_pos hC₁_pos d
  refine ⟨C₁ ^ d, hC₁_d_pos, ?_⟩
  intro N hN a ha hvol t ht
  set Λ := Fintype.card (FinLatticeSites d N)
  -- Step A: re-index ∑_{m ∈ range Λ} → ∑_{k : FinLatticeSites d N}.
  have hΛ_card : Λ = Fintype.card (FinLatticeSites d N) := rfl
  -- Use Finset.sum_range to convert to Σ over Fin Λ, then Equiv.sum_comp via equivFin.
  -- Actually easier: build a function on FinLatticeSites and use Equiv.sum_comp directly.
  set F : FinLatticeSites d N → ℝ :=
    fun k => Real.exp (-t * latticeEigenvalue d N a mass
      ((Fintype.equivFin (FinLatticeSites d N)) k).val)
  have hreindex : (∑ m ∈ range Λ, Real.exp (-t * latticeEigenvalue d N a mass m)) =
      ∑ k : FinLatticeSites d N, F k := by
    rw [Finset.sum_range]
    -- Σ_{i : Fin Λ} f i.val = Σ_{k : FinLatticeSites d N} f ((equivFin _) k).val
    exact (Equiv.sum_comp (Fintype.equivFin (FinLatticeSites d N))
      (fun i => Real.exp (-t * latticeEigenvalue d N a mass i.val))).symm
  -- Step B: factor each F k via the eigenvalue formula.
  have hF_eq : ∀ k : FinLatticeSites d N,
      F k = Real.exp (-t * mass ^ 2) *
        ∏ i : Fin d, Real.exp (-t * (4 * Real.sin (π * (ZMod.val (k i) : ℝ) / N) ^ 2 / a ^ 2)) := by
    intro k
    -- F k = exp(-t · latticeEigenvalue d N a mass m) where m = (equivFin k).val < Λ.
    have hm_lt : ((Fintype.equivFin (FinLatticeSites d N)) k).val < Λ :=
      ((Fintype.equivFin (FinLatticeSites d N)) k).isLt
    have hev_eq := latticeEigenvalue_eq d N a mass ((Fintype.equivFin _) k).val
    have hlap_eq := latticeLaplacianEigenvalue_eq_sum d N a _ hm_lt
    have hk_back :
        (Fintype.equivFin (FinLatticeSites d N)).symm
            ⟨((Fintype.equivFin (FinLatticeSites d N)) k).val, hm_lt⟩ = k := by
      simp [Equiv.symm_apply_eq, Fin.eta]
    show Real.exp (-t * latticeEigenvalue d N a mass _) = _
    rw [hev_eq, hlap_eq, hk_back]
    -- Now exp(-t · ((4/a²) · Σ_i sin² + mass²))
    -- = exp(-t · mass²) · exp(-t · (4/a²) · Σ_i sin²)
    -- = exp(-t · mass²) · ∏_i exp(-t · (4/a²) · sin²)
    have hexp_factor :
        Real.exp (-t * ((4 / a ^ 2) *
          ∑ i : Fin d, Real.sin (π * (ZMod.val (k i) : ℝ) / N) ^ 2 + mass ^ 2)) =
        Real.exp (-t * mass ^ 2) * Real.exp (-t * ((4 / a ^ 2) *
          ∑ i : Fin d, Real.sin (π * (ZMod.val (k i) : ℝ) / N) ^ 2)) := by
      rw [show -t * ((4 / a ^ 2) * _ + mass ^ 2) =
            -t * mass ^ 2 + -t * ((4 / a ^ 2) *
              ∑ i : Fin d, Real.sin (π * (ZMod.val (k i) : ℝ) / N) ^ 2) by ring]
      rw [Real.exp_add]
    rw [hexp_factor]; congr 1
    -- exp(-t · (4/a²) · Σ_i sin²) = ∏_i exp(-t · (4/a²) · sin²)
    rw [show -t * ((4 / a ^ 2) *
        ∑ i : Fin d, Real.sin (π * (ZMod.val (k i) : ℝ) / N) ^ 2) =
        ∑ i : Fin d, -t * (4 * Real.sin (π * (ZMod.val (k i) : ℝ) / N) ^ 2 / a ^ 2) by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intros; ring]
    rw [Real.exp_sum]
  -- Step C+D+E: sum F over FinLatticeSites and pull out + factorize.
  rw [hreindex]
  have hsum_eq :
      (∑ k : FinLatticeSites d N, F k) =
      Real.exp (-t * mass ^ 2) *
        ∏ i : Fin d, ∑ kᵢ : ZMod N,
          Real.exp (-t * (4 * Real.sin (π * (ZMod.val kᵢ : ℝ) / N) ^ 2 / a ^ 2)) := by
    simp_rw [hF_eq]
    rw [← Finset.mul_sum]
    congr 1
    exact sum_finLatticeSites_prod d N (fun i kᵢ =>
      Real.exp (-t * (4 * Real.sin (π * (ZMod.val kᵢ : ℝ) / N) ^ 2 / a ^ 2)))
  rw [hsum_eq]
  -- Step F+G: bound each ZMod N sum by C₁ · (1 + 1/√t) via Phase 0.
  have h_zmod_sum : ∀ i : Fin d,
      (∑ kᵢ : ZMod N, Real.exp (-t * (4 * Real.sin (π * (ZMod.val kᵢ : ℝ) / N) ^ 2 / a ^ 2)))
        ≤ C₁ * (1 + 1 / Real.sqrt t) := by
    intro _
    -- Σ over ZMod N = Σ over Fin N (via equivFin) = Σ over range N (via Finset.sum_range)
    have h_zmod_to_fin :
        (∑ kᵢ : ZMod N, Real.exp (-t * (4 * Real.sin (π * (ZMod.val kᵢ : ℝ) / N) ^ 2 / a ^ 2))) =
        ∑ j ∈ range N, Real.exp (-t * (4 * Real.sin (π * (j : ℝ) / N) ^ 2 / a ^ 2)) := by
      rw [Finset.sum_range]
      -- Use equivFin (ZMod N) : ZMod N ≃ Fin (Card (ZMod N)) = Fin N
      have hcard : Fintype.card (ZMod N) = N := ZMod.card N
      -- Re-index Σ_{kᵢ : ZMod N} = Σ_{i : Fin N} f((equivFin (ZMod N)).symm ⟨...⟩.val)
      -- via Equiv.sum_comp ... but simpler: Σ_{ZMod N} = Σ_{Fin N} via val bijection.
      -- For [NeZero N], ZMod N ≃ Fin N via ZMod.val and the existing Fintype instance.
      apply Finset.sum_bij (fun (kᵢ : ZMod N) _ => (⟨kᵢ.val, ZMod.val_lt kᵢ⟩ : Fin N))
      · intros _ _; exact Finset.mem_univ _
      · intros a _ b _ hab
        apply ZMod.val_injective
        exact Fin.mk.inj_iff.mp hab
      · intros j _
        refine ⟨((j : ℕ) : ZMod N), Finset.mem_univ _, ?_⟩
        ext
        simp [ZMod.val_natCast_of_lt j.isLt]
      · intros kᵢ _
        push_cast
        rfl
    rw [h_zmod_to_fin]
    exact hC₁ N a ha hvol t ht
  -- Multiply over i : Fin d.
  have h_prod : ∏ i : Fin d,
      (∑ kᵢ : ZMod N, Real.exp (-t * (4 * Real.sin (π * (ZMod.val kᵢ : ℝ) / N) ^ 2 / a ^ 2)))
        ≤ ∏ _i : Fin d, C₁ * (1 + 1 / Real.sqrt t) := by
    apply Finset.prod_le_prod
    · intros i _
      apply Finset.sum_nonneg
      intros; exact (Real.exp_pos _).le
    · intros i _; exact h_zmod_sum i
  have h_prod_eq : ∏ _i : Fin d, C₁ * (1 + 1 / Real.sqrt t) =
      C₁ ^ d * (1 + 1 / Real.sqrt t) ^ d := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
  rw [h_prod_eq] at h_prod
  -- Combine: exp(-t·m²) * prod ≤ exp(-t·m²) * C^d · (1+1/√t)^d.
  have h_exp_mass_nn : (0 : ℝ) ≤ Real.exp (-t * mass ^ 2) := (Real.exp_pos _).le
  calc Real.exp (-t * mass ^ 2) *
        ∏ i : Fin d, ∑ kᵢ : ZMod N,
          Real.exp (-t * (4 * Real.sin (π * (ZMod.val kᵢ : ℝ) / N) ^ 2 / a ^ 2))
      ≤ Real.exp (-t * mass ^ 2) * (C₁ ^ d * (1 + 1 / Real.sqrt t) ^ d) := by
        exact mul_le_mul_of_nonneg_left h_prod h_exp_mass_nn
    _ = C₁ ^ d * (1 + 1 / Real.sqrt t) ^ d * Real.exp (-t * mass ^ 2) := by ring

/-! ## Phase 1b — `(a, N)`-uniform smooth Wick constant bound

Integrates `heat_kernel_trace_bound_uniform` over `s ∈ [T, ∞)` via the
Schwinger identity to discharge the first Phase B axiom
`smoothWickConstant_le_log_uniform_in_aN`.

**Math sketch (d = 2):**

By Schwinger (`schwinger_smooth_Ioi`):
  `smoothCovEigenvalue T m = ∫_T^∞ exp(-s · λ_m) ds`.

So
  `smoothWickConstant T = (a^d)⁻¹ · (1/Λ) · Σ_m smoothCovEigenvalue T m
                       = (a^d · Λ)⁻¹ · Σ_m ∫_T^∞ exp(-s · λ_m) ds
                       = L⁻ᵈ · ∫_T^∞ Σ_m exp(-s · λ_m) ds`     [Fubini, finite sum]
                       = L⁻¹ ^ 2 · ∫_T^∞ trace(e^{-sM_a}) ds`        [d = 2, Λ = (L/a)²]

By Phase 1a (`heat_kernel_trace_bound_uniform`):
  `trace(e^{-sM_a}) ≤ C · (1 + 1/√s)² · exp(-s · mass²)`     [d = 2]

Using `(1 + 1/√s)² ≤ 2 · (1 + 1/s)`:
  `trace ≤ 2C · (1 + 1/s) · exp(-s · mass²)`.

Integrate:
  `∫_T^∞ exp(-s · m²) ds = exp(-T · m²) / m² ≤ 1/m²`     [uniform in T]
  `∫_T^∞ (1/s) · exp(-s · m²) ds ≤ |log T| + 1/m²`        [|log T| from `s ∈ (0,1)` part]

Total: `L⁻¹ ^ 2 · 2C · (2/m² + |log T|) ≤ A + B · (1 + |log T|)`
       with `A = 2L⁻¹ ^ 2C·(2/m² + 1)`, `B = 2L⁻¹ ^ 2C`. -/

private lemma one_add_inv_sqrt_sq_le_two_mul_one_add_inv
    (s : ℝ) (hs : 0 < s) :
    (1 + 1 / Real.sqrt s) ^ 2 ≤ 2 * (1 + 1 / s) := by
  set u : ℝ := 1 / Real.sqrt s
  have hu_sq : u ^ 2 = 1 / s := by
    have hsqrt : Real.sqrt s ≠ 0 := by positivity
    have hsqrt_sq : (Real.sqrt s) ^ 2 = s := by
      rw [sq_sqrt (show 0 ≤ s by linarith)]
    calc
      u ^ 2 = (1 / Real.sqrt s) ^ 2 := by simp [u]
      _ = 1 / ((Real.sqrt s) ^ 2) := by field_simp [hsqrt]
      _ = 1 / s := by rw [hsqrt_sq]
  have h2u : 2 * u ≤ u ^ 2 + 1 := by
    have hnn : 0 ≤ (u - 1) ^ 2 := sq_nonneg _
    nlinarith
  calc
    (1 + 1 / Real.sqrt s) ^ 2 = (1 + u) ^ 2 := by simp [u]
    _ = 1 + 2 * u + u ^ 2 := by ring
    _ ≤ 1 + (u ^ 2 + 1) + u ^ 2 := by gcongr
    _ = 2 * (1 + u ^ 2) := by ring
    _ = 2 * (1 + 1 / s) := by rw [hu_sq]

private lemma integrableOn_inv_Ioc (T : ℝ) (hT : 0 < T) :
    IntegrableOn (fun s : ℝ => 1 / s) (Set.Ioc T 1) := by
  refine MeasureTheory.Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne ?_ (M := 1 / T) ?_
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hspos : 0 < s := lt_trans hT hs.1
    have hle : 1 / s ≤ 1 / T := by
      gcongr
      exact hs.1.le
    have hnonneg : 0 ≤ (1 / s : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hle

private lemma integrableOn_inv_mul_exp_Ioi (μ T : ℝ) (hμ : 0 < μ) (hT : 0 < T) :
    IntegrableOn (fun s : ℝ => (1 / s) * Real.exp (-s * μ)) (Set.Ioi T) := by
  let g : ℝ → ℝ := fun s => (1 / T) * Real.exp (-s * μ)
  have hg_int : IntegrableOn g (Set.Ioi T) := by
    have hbase := integrableOn_exp_mul_Ioi (a := (-μ : ℝ)) (by linarith) T
    simpa [g, mul_comm, mul_left_comm, mul_assoc] using hbase.const_mul (1 / T)
  have hg_sm :
      AEStronglyMeasurable
        (fun s : ℝ => (1 / s) * Real.exp (-s * μ))
        (volume.restrict (Set.Ioi T)) := by
    fun_prop
  refine MeasureTheory.Integrable.mono' hg_int hg_sm ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hspos : 0 < s := lt_trans hT hs
  have hle : s⁻¹ ≤ T⁻¹ := by
    have : 1 / s ≤ 1 / T := by
      gcongr
      exact hs.le
    simpa [one_div] using this
  have hexp : 0 ≤ Real.exp (-(s * μ)) := (Real.exp_pos _).le
  have hnonneg : 0 ≤ (1 / s : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnonneg (by simpa [neg_mul] using hexp))]
  simp only [g, one_div, neg_mul, ge_iff_le]
  exact mul_le_mul_of_nonneg_right hle hexp

/-- **Phase 1b target — first Phase B axiom as a theorem.**

This is the discharge of `smoothWickConstant_le_log_uniform_in_aN`
(currently axiomatised in `CovarianceBoundsGJ.lean`).

Status: the structural skeleton is in place; the integral bookkeeping
(Schwinger identity + Fubini on a finite sum + bounds on
`∫_T^∞ exp(-s m²)/s ds`) is the remaining ~150 lines. -/
theorem smoothWickConstant_le_log_uniform_in_aN_proved
    {d : ℕ} (hd : d = 2) (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a)
        (_h_vol : (N : ℝ) * a = L)
        (T : ℝ) (_hT : 0 < T),
        smoothWickConstant d N a mass T ≤ A + B * (1 + |Real.log T|) := by
  -- Witness shape:
  --   A := 2 · L⁻¹ ^ 2 · C₁² · (2/mass² + 1)   (the constant part)
  --   B := 2 · L⁻¹ ^ 2 · C₁²                   (the log T coefficient)
  -- where C₁ comes from heat_kernel_trace_bound_uniform with d := 2.
  subst hd
  obtain ⟨C, hC_pos, _hC⟩ :=
    heat_kernel_trace_bound_uniform 2 L hL mass hmass
  refine ⟨2 * L⁻¹ ^ 2 * C * (2 / mass ^ 2 + 1), 2 * L⁻¹ ^ 2 * C, ?_, ?_, ?_⟩
  · positivity
  · positivity
  intro N hN a ha hvol T hT
  let Λ := Fintype.card (FinLatticeSites 2 N)
  have hmass_sq_pos : 0 < mass ^ 2 := sq_pos_of_pos hmass
  have hcard_nat : Fintype.card (FinLatticeSites 2 N) = N ^ 2 := by
    simp only [FinLatticeSites, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hcard : (Λ : ℝ) = (N : ℝ) ^ 2 := by
    rw [show Λ = Fintype.card (FinLatticeSites 2 N) by rfl, hcard_nat]
    norm_num
  have hvol_sq : a ^ 2 * (Λ : ℝ) = L ^ 2 := by
    rw [hcard]
    calc
      a ^ 2 * (N : ℝ) ^ 2 = ((N : ℝ) * a) ^ 2 := by ring
      _ = L ^ 2 := by rw [hvol]
  have hΛ_ne : (Λ : ℝ) ≠ 0 := by
    rw [hcard]
    exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr (NeZero.ne N))
  have hsummand_int :
      ∀ m ∈ range Λ,
        IntegrableOn
          (fun s : ℝ => Real.exp (-s * latticeEigenvalue 2 N a mass m))
          (Set.Ioi T) := by
    intro m hm
    have hlam : 0 < latticeEigenvalue 2 N a mass m :=
      latticeEigenvalue_pos 2 N a mass ha hmass m
    have hbase := integrableOn_exp_mul_Ioi
      (a := (-(latticeEigenvalue 2 N a mass m) : ℝ)) (by linarith) T
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbase
  have hsum_int :
      IntegrableOn
        (fun s : ℝ =>
          ∑ m ∈ range Λ, Real.exp (-s * latticeEigenvalue 2 N a mass m))
        (Set.Ioi T) := by
    simpa [Λ] using
      (MeasureTheory.integrable_finset_sum (range Λ) hsummand_int)
  have hsmooth_sum :
      ∑ m ∈ range Λ, smoothCovEigenvalue 2 N a mass T m
        = ∫ s in Set.Ioi T,
            ∑ m ∈ range Λ,
              Real.exp (-s * latticeEigenvalue 2 N a mass m) := by
    calc
      ∑ m ∈ range Λ, smoothCovEigenvalue 2 N a mass T m
        = ∑ m ∈ range Λ,
            ∫ s in Set.Ioi T, Real.exp (-s * latticeEigenvalue 2 N a mass m) := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              unfold smoothCovEigenvalue
              rw [schwinger_smooth_Ioi]
              exact latticeEigenvalue_pos 2 N a mass ha hmass m
      _ = ∫ s in Set.Ioi T,
            ∑ m ∈ range Λ,
              Real.exp (-s * latticeEigenvalue 2 N a mass m) := by
            symm
            rw [MeasureTheory.integral_finset_sum _ hsummand_int]
  have hsmooth_repr :
      smoothWickConstant 2 N a mass T
        = L⁻¹ ^ 2 *
            ∫ s in Set.Ioi T,
              ∑ m ∈ range Λ,
                Real.exp (-s * latticeEigenvalue 2 N a mass m) := by
    unfold smoothWickConstant
    rw [show Fintype.card (FinLatticeSites 2 N) = Λ by rfl, hsmooth_sum]
    have hpref :
        (a ^ 2 : ℝ)⁻¹ * (1 / Λ : ℝ) = L⁻¹ ^ 2 := by
      calc
        (a ^ 2 : ℝ)⁻¹ * (1 / Λ : ℝ)
            = (a ^ 2 : ℝ)⁻¹ * ((Λ : ℝ)⁻¹) := by norm_num
        _ = ((a ^ 2 : ℝ) * (Λ : ℝ))⁻¹ := by
              field_simp [hΛ_ne, show (a ^ 2 : ℝ) ≠ 0 by positivity]
        _ = L⁻¹ ^ 2 := by rw [hvol_sq]; ring
    let I : ℝ :=
      ∫ s in Set.Ioi T,
        ∑ m ∈ range Λ,
          Real.exp (-s * latticeEigenvalue 2 N a mass m)
    change (a ^ 2 : ℝ)⁻¹ * ((1 / Λ : ℝ) * I) = L⁻¹ ^ 2 * I
    rw [← mul_assoc, hpref]
  have hexp_int :
      IntegrableOn (fun s : ℝ => Real.exp (-s * mass ^ 2)) (Set.Ioi T) := by
    have hbase := integrableOn_exp_mul_Ioi (a := (-mass ^ 2 : ℝ)) (by linarith) T
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbase
  have hinvexp_int :
      IntegrableOn
        (fun s : ℝ => (1 / s) * Real.exp (-s * mass ^ 2))
        (Set.Ioi T) :=
    integrableOn_inv_mul_exp_Ioi (μ := mass ^ 2) (T := T) hmass_sq_pos hT
  have hmajorant_int :
      IntegrableOn
        (fun s : ℝ => 2 * C * (1 + 1 / s) * Real.exp (-s * mass ^ 2))
        (Set.Ioi T) := by
    have hadd : IntegrableOn
        (fun s : ℝ =>
          Real.exp (-s * mass ^ 2) +
            (1 / s) * Real.exp (-s * mass ^ 2))
        (Set.Ioi T) := hexp_int.add hinvexp_int
    have hscaled := hadd.const_mul (2 * C)
    refine MeasureTheory.IntegrableOn.congr_fun hscaled ?_ measurableSet_Ioi
    intro s hs
    ring
  have htrace_le :
      ∫ s in Set.Ioi T,
        ∑ m ∈ range Λ,
          Real.exp (-s * latticeEigenvalue 2 N a mass m)
        ≤
      ∫ s in Set.Ioi T, 2 * C * (1 + 1 / s) * Real.exp (-s * mass ^ 2) := by
    apply MeasureTheory.setIntegral_mono_on hsum_int hmajorant_int measurableSet_Ioi
    intro s hs
    have hspos : 0 < s := lt_trans hT hs
    have hsqrt :
        (1 + 1 / Real.sqrt s) ^ 2 ≤ 2 * (1 + 1 / s) :=
      one_add_inv_sqrt_sq_le_two_mul_one_add_inv s hspos
    calc
      ∑ m ∈ range Λ, Real.exp (-s * latticeEigenvalue 2 N a mass m)
        ≤ C * (1 + 1 / Real.sqrt s) ^ 2 * Real.exp (-s * mass ^ 2) :=
          _hC N a ha hvol s hspos
      _ ≤ C * (2 * (1 + 1 / s)) * Real.exp (-s * mass ^ 2) := by
            gcongr
      _ = 2 * C * (1 + 1 / s) * Real.exp (-s * mass ^ 2) := by ring
  have hexp_eq :
      ∫ s in Set.Ioi T, Real.exp (-s * mass ^ 2) =
        Real.exp (-T * mass ^ 2) / mass ^ 2 := by
    symm
    exact schwinger_smooth_Ioi (mass ^ 2) hmass_sq_pos T
  have hexp_le :
      ∫ s in Set.Ioi T, Real.exp (-s * mass ^ 2) ≤ 1 / mass ^ 2 := by
    rw [hexp_eq]
    have hle_one : Real.exp (-T * mass ^ 2) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith
    exact div_le_div_of_nonneg_right hle_one hmass_sq_pos.le
  have hinvexp_le :
      ∫ s in Set.Ioi T, (1 / s) * Real.exp (-s * mass ^ 2)
        ≤ |Real.log T| + 1 / mass ^ 2 := by
    by_cases hT1 : T ≤ 1
    · have hsplit : Set.Ioi T = Set.Ioc T 1 ∪ Set.Ioi 1 := by
        ext s
        simp [hT1]
      have hleft_int :
          IntegrableOn
            (fun s : ℝ => (1 / s) * Real.exp (-s * mass ^ 2))
            (Set.Ioc T 1) := hinvexp_int.mono_set (by
              intro s hs
              exact hs.1)
      have hright_int :
          IntegrableOn
            (fun s : ℝ => (1 / s) * Real.exp (-s * mass ^ 2))
            (Set.Ioi 1) := hinvexp_int.mono_set (by
              intro s hs
              exact hT1.trans_lt hs)
      rw [hsplit]
      rw [MeasureTheory.setIntegral_union
        (show Disjoint (Set.Ioc T 1) (Set.Ioi 1) by
          refine Set.disjoint_left.mpr ?_
          intro s hs1 hs2
          exact not_lt_of_ge hs1.2 hs2)
        measurableSet_Ioi hleft_int hright_int]
      have hleft_le :
          ∫ s in Set.Ioc T 1, (1 / s) * Real.exp (-s * mass ^ 2) ≤ |Real.log T| := by
        calc
          ∫ s in Set.Ioc T 1, (1 / s) * Real.exp (-s * mass ^ 2)
            ≤ ∫ s in Set.Ioc T 1, (1 / s : ℝ) := by
                apply MeasureTheory.setIntegral_mono_on hleft_int (integrableOn_inv_Ioc T hT)
                  measurableSet_Ioc
                intro s hs
                have hspos : 0 < s := lt_trans hT hs.1
                have hexp_le_one : Real.exp (-s * mass ^ 2) ≤ 1 := by
                  apply Real.exp_le_one_iff.mpr
                  have : -s * mass ^ 2 ≤ 0 := by nlinarith [sq_nonneg mass]
                  exact this
                have hnonneg : 0 ≤ (1 / s : ℝ) := by positivity
                simpa using mul_le_mul_of_nonneg_left hexp_le_one hnonneg
          _ = ∫ s in T..1, (1 / s : ℝ) := by
                rw [intervalIntegral.integral_of_le hT1]
          _ = Real.log (1 / T) := by
                simpa using integral_one_div_of_pos hT (by norm_num : (0 : ℝ) < 1)
          _ = |Real.log T| := by
                have hlog : Real.log T ≤ 0 := Real.log_nonpos hT.le hT1
                have hlog_inv : Real.log (1 / T) = -Real.log T := by
                  simpa [one_div] using (Real.log_inv (show T ≠ 0 by linarith))
                rw [hlog_inv, abs_of_nonpos hlog]
      have hright_le :
          ∫ s in Set.Ioi 1, (1 / s) * Real.exp (-s * mass ^ 2) ≤ 1 / mass ^ 2 := by
        calc
          ∫ s in Set.Ioi 1, (1 / s) * Real.exp (-s * mass ^ 2)
            ≤ ∫ s in Set.Ioi 1, Real.exp (-s * mass ^ 2) := by
                apply MeasureTheory.setIntegral_mono_on hright_int
                  (hexp_int.mono_set (by
                    intro s hs
                    exact hT1.trans_lt hs))
                  measurableSet_Ioi
                intro s hs
                have hsone : 1 < s := hs
                have hle : 1 / s ≤ (1 : ℝ) := by
                  have hspos : 0 < s := by linarith
                  rw [div_le_iff₀ hspos]
                  linarith
                have hnonneg : 0 ≤ Real.exp (-s * mass ^ 2) := (Real.exp_pos _).le
                simpa using mul_le_mul_of_nonneg_right hle hnonneg
          _ = Real.exp (-(mass ^ 2)) / mass ^ 2 := by
                simpa [one_mul] using (schwinger_smooth_Ioi (mass ^ 2) hmass_sq_pos 1).symm
          _ ≤ 1 / mass ^ 2 := by
                have hle_one : Real.exp (-(mass ^ 2)) ≤ 1 := by
                  apply Real.exp_le_one_iff.mpr
                  have : -(mass ^ 2) ≤ 0 := by nlinarith [sq_nonneg mass]
                  exact this
                exact div_le_div_of_nonneg_right hle_one hmass_sq_pos.le
      exact add_le_add hleft_le hright_le
    · have hT1 : 1 < T := lt_of_not_ge hT1
      calc
        ∫ s in Set.Ioi T, (1 / s) * Real.exp (-s * mass ^ 2)
          ≤ ∫ s in Set.Ioi T, Real.exp (-s * mass ^ 2) := by
              apply MeasureTheory.setIntegral_mono_on hinvexp_int hexp_int measurableSet_Ioi
              intro s hs
              have hsT : T < s := hs
              have hsone : 1 < s := lt_trans hT1 hsT
              have hle : 1 / s ≤ (1 : ℝ) := by
                have hspos : 0 < s := by linarith
                rw [div_le_iff₀ hspos]
                linarith
              have hnonneg : 0 ≤ Real.exp (-s * mass ^ 2) := (Real.exp_pos _).le
              simpa using mul_le_mul_of_nonneg_right hle hnonneg
        _ ≤ 1 / mass ^ 2 := hexp_le
        _ ≤ |Real.log T| + 1 / mass ^ 2 := by
              nlinarith [abs_nonneg (Real.log T)]
  have hmajorant_eval :
      ∫ s in Set.Ioi T, 2 * C * (1 + 1 / s) * Real.exp (-s * mass ^ 2)
        ≤ 2 * C * (1 / mass ^ 2) + 2 * C * (|Real.log T| + 1 / mass ^ 2) := by
    have hsplit :
        ∫ s in Set.Ioi T, 2 * C * (Real.exp (-s * mass ^ 2) +
            (1 / s) * Real.exp (-s * mass ^ 2))
          =
        (2 * C) * (∫ s in Set.Ioi T, Real.exp (-s * mass ^ 2)) +
          (2 * C) * (∫ s in Set.Ioi T, (1 / s) * Real.exp (-s * mass ^ 2)) := by
      rw [MeasureTheory.integral_const_mul]
      rw [MeasureTheory.integral_add hexp_int hinvexp_int]
      ring
    calc
      ∫ s in Set.Ioi T, 2 * C * (1 + 1 / s) * Real.exp (-s * mass ^ 2)
        = ∫ s in Set.Ioi T, 2 * C * (Real.exp (-s * mass ^ 2) +
            (1 / s) * Real.exp (-s * mass ^ 2)) := by
              apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
              intro s hs
              ring
      _ = (2 * C) * (∫ s in Set.Ioi T, Real.exp (-s * mass ^ 2)) +
            (2 * C) * (∫ s in Set.Ioi T, (1 / s) * Real.exp (-s * mass ^ 2)) := hsplit
      _ ≤ (2 * C) * (1 / mass ^ 2) + (2 * C) * (|Real.log T| + 1 / mass ^ 2) := by
            gcongr
  calc
    smoothWickConstant 2 N a mass T
      = L⁻¹ ^ 2 *
          ∫ s in Set.Ioi T,
            ∑ m ∈ range Λ,
              Real.exp (-s * latticeEigenvalue 2 N a mass m) := hsmooth_repr
    _ ≤ L⁻¹ ^ 2 *
          ∫ s in Set.Ioi T,
            2 * C * (1 + 1 / s) * Real.exp (-s * mass ^ 2) := by
              exact mul_le_mul_of_nonneg_left htrace_le (by positivity)
    _ ≤ L⁻¹ ^ 2 *
          (2 * C * (1 / mass ^ 2) + 2 * C * (|Real.log T| + 1 / mass ^ 2)) := by
              gcongr
    _ = 2 * L⁻¹ ^ 2 * C * (2 / mass ^ 2 + |Real.log T|) := by ring
    _ ≤ 2 * L⁻¹ ^ 2 * C * (2 / mass ^ 2 + 1) +
          (2 * L⁻¹ ^ 2 * C) * (1 + |Real.log T|) := by
            have hB_nonneg : 0 ≤ 2 * L⁻¹ ^ 2 * C := by positivity
            nlinarith [abs_nonneg (Real.log T), hB_nonneg]

end Pphi2

end
