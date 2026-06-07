/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.NelsonEstimate.RoughErrorBound
import Pphi2.NelsonEstimate.CovarianceBoundsGJ
import Pphi2.InteractingMeasure.UniformBounds
import Pphi2.InteractingMeasure.InteractionL2

/-!
# Uniform `L²` bound on the interaction (uniform-discharge brick L1) — smooth side

Toward `∫ V² dμ_GFF ≤ C(m,L)` uniform in `N` (`planning/L1-plan.md`). The bridge
`integral_interaction_sq_eq_canonicalJoint` and the rough variance `rough_error_variance` are done;
this file builds the **smooth** summability input (`M1`): the smooth covariance, being pointwise
bounded by `smoothWickConstant`, gives a trivial double-sum bound via `a^d·#sites = L^d` (no
row-sums needed, unlike the rough side).
-/

namespace Pphi2

open MeasureTheory GaussianField

/-- **M1 — smooth covariance double-sum bound.** Since `|C_smooth(x,y)| ≤ smoothWickConstant` (a
uniform `A + B(1+|log T|)`), the full double sum is controlled by the lattice volume squared:
`a^{2d} ∑_{x,y} |C_smooth(x,y)|^m ≤ C·(1+|log T|)^m`, uniform in `N` at fixed `L`. This is the
smooth-side summability input for the smooth interaction variance (M2). -/
theorem canonicalSmoothCovariance_pow_double_sum_le {d : ℕ} (hd : d = 2) (mass L : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a) (_hvol : (N : ℝ) * a = L)
      (T : ℝ) (_hT : 0 < T),
      a ^ d * a ^ d * ∑ x : FinLatticeSites d N, ∑ y : FinLatticeSites d N,
        |canonicalSmoothCovariance d N a mass T x y| ^ m ≤ C * (1 + |Real.log T|) ^ m := by
  obtain ⟨A, B, hA, hB, hbd⟩ := smoothWickConstant_le_log_uniform_in_aN hd mass L hL hmass
  refine ⟨L ^ (2 * d) * (A + B) ^ m + 1, by positivity, ?_⟩
  intro N _ a ha hvol T hT
  set u := |Real.log T| with hudef
  have hu : 0 ≤ u := abs_nonneg _
  set S := smoothWickConstant d N a mass T with hSdef
  have hSbd : S ≤ A + B * (1 + u) := hbd N a ha hvol T hT
  have hSnn : 0 ≤ S :=
    le_trans (abs_nonneg _) (abs_canonicalSmoothCovariance_le_smoothWickConstant d N a mass ha hmass
      T hT (Classical.arbitrary _) (Classical.arbitrary _))
  -- termwise `|C_smooth x y|^m ≤ S^m`
  have hsum : ∑ x : FinLatticeSites d N, ∑ y : FinLatticeSites d N,
        |canonicalSmoothCovariance d N a mass T x y| ^ m
      ≤ ∑ _x : FinLatticeSites d N, ∑ _y : FinLatticeSites d N, S ^ m := by
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
    exact pow_le_pow_left₀ (abs_nonneg _)
      (abs_canonicalSmoothCovariance_le_smoothWickConstant d N a mass ha hmass T hT x y) m
  -- collapse the constant double sum to `card² · S^m` and use `a^d·card = L^d`
  have hcard : ∑ _x : FinLatticeSites d N, ∑ _y : FinLatticeSites d N, S ^ m
      = ((Fintype.card (FinLatticeSites d N) : ℝ)) ^ 2 * S ^ m := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hvold : a ^ d * (Fintype.card (FinLatticeSites d N) : ℝ) = L ^ d := by
    rw [lattice_volume_eq d N a]; congr 1; rw [mul_comm]; exact hvol
  -- `S^m ≤ (A+B(1+u))^m ≤ (A+B)^m (1+u)^m`
  have hSpow : S ^ m ≤ (A + B) ^ m * (1 + u) ^ m := by
    calc S ^ m ≤ (A + B * (1 + u)) ^ m := pow_le_pow_left₀ hSnn hSbd m
      _ ≤ ((A + B) * (1 + u)) ^ m := by
          refine pow_le_pow_left₀ (by positivity) ?_ m
          nlinarith [mul_nonneg hA hu, hu, hA, hB]
      _ = (A + B) ^ m * (1 + u) ^ m := mul_pow _ _ _
  have hsum2 : ∑ x : FinLatticeSites d N, ∑ y : FinLatticeSites d N,
        |canonicalSmoothCovariance d N a mass T x y| ^ m
      ≤ (Fintype.card (FinLatticeSites d N) : ℝ) ^ 2 * S ^ m := hsum.trans (le_of_eq hcard)
  calc a ^ d * a ^ d * ∑ x : FinLatticeSites d N, ∑ y : FinLatticeSites d N,
          |canonicalSmoothCovariance d N a mass T x y| ^ m
      ≤ a ^ d * a ^ d * ((Fintype.card (FinLatticeSites d N) : ℝ) ^ 2 * S ^ m) :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
    _ = (L ^ d) ^ 2 * S ^ m := by
        rw [show a ^ d * a ^ d * ((Fintype.card (FinLatticeSites d N) : ℝ) ^ 2 * S ^ m)
          = (a ^ d * (Fintype.card (FinLatticeSites d N) : ℝ)) ^ 2 * S ^ m from by ring, hvold]
    _ ≤ (L ^ d) ^ 2 * ((A + B) ^ m * (1 + u) ^ m) :=
        mul_le_mul_of_nonneg_left hSpow (by positivity)
    _ ≤ (L ^ (2 * d) * (A + B) ^ m + 1) * (1 + u) ^ m := by
        have hLd : (L ^ d) ^ 2 = L ^ (2 * d) := by rw [← pow_mul, mul_comm]
        rw [hLd, add_mul, one_mul, ← mul_assoc]
        exact le_add_of_nonneg_right (by positivity)

/-- **M2a — smooth interaction as a sum of diagonal cross-terms.** The smooth interaction is the
`j=k` (pure-smooth) part of the Wick expansion: `V_smooth = (1/P.n)·crossTerm(P.n,P.n) +
∑_m P.coeff m · crossTerm(m,m)`, where `canonicalCrossTerm k k = a^d ∑_x :φ_S(x)^k:` (the rough
factor `:φ_R^0: = 1`). Mirrors `canonicalRoughError_eq_sum_over_cross_terms` (excludes `j=k`). -/
lemma canonicalSmoothInteraction_eq_sum_crossTerm_diag (d N : ℕ) [NeZero N] (a mass : ℝ)
    (T : ℝ) (P : InteractionPolynomial) (η : CanonicalJoint d N) :
    canonicalSmoothInteraction d N a mass T P η =
    (1 / P.n : ℝ) * canonicalCrossTerm d N a mass T η P.n P.n
    + ∑ m : Fin P.n, P.coeff m * canonicalCrossTerm d N a mass T η (m : ℕ) (m : ℕ) := by
  unfold canonicalSmoothInteraction canonicalCrossTerm
  simp only [Nat.sub_self, wickMonomial_zero, mul_one, wickPolynomial]
  rw [Finset.sum_add_distrib, mul_add]
  refine congr_arg₂ (· + ·) ?_ ?_
  · rw [← Finset.mul_sum]; ring
  · simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [mul_assoc, ← Finset.mul_sum]
    ring

/-- **M2c — per-term diagonal cross-term L² bound.** `∫ (crossTerm(k,k))² ≤ k!·C·(1+|log T|)^k`
uniform in `N`: the cross-term L² equals `(a^d)²·k!·∑_{x,y} C_smooth(x,y)^k`
(`canonicalCrossTerm_l2_sq_eq_covSum` at `j=k`, the rough factor being `C_rough^0 = 1`), and the
smooth double sum is bounded by M1. -/
theorem canonicalCrossTerm_diag_l2_sq_le {d : ℕ} (hd : d = 2) (mass L : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a) (_hvol : (N : ℝ) * a = L)
      (T : ℝ) (_hT : 0 < T),
      ∫ η, (canonicalCrossTerm d N a mass T η k k) ^ 2 ∂(canonicalJointMeasure d N)
        ≤ (k.factorial : ℝ) * C * (1 + |Real.log T|) ^ k := by
  obtain ⟨C1, hC1, hM1⟩ := canonicalSmoothCovariance_pow_double_sum_le hd mass L hL hmass k
  refine ⟨C1, hC1, ?_⟩
  intro N _ a ha hvol T hT
  rw [canonicalCrossTerm_l2_sq_eq_covSum d N a mass ha hmass T hT k k]
  simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one, pow_zero]
  -- goal: a^d * a^d * k! * ∑_{x,y} C_smooth^k ≤ k! * C1 * (1+u)^k
  have habs : ∑ x : FinLatticeSites d N, ∑ y : FinLatticeSites d N,
        canonicalSmoothCovariance d N a mass T x y ^ k
      ≤ ∑ x : FinLatticeSites d N, ∑ y : FinLatticeSites d N,
        |canonicalSmoothCovariance d N a mass T x y| ^ k := by
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
    rw [← abs_pow]; exact le_abs_self _
  have hkfac : (0 : ℝ) ≤ (k.factorial : ℝ) := by positivity
  have hann : (0 : ℝ) ≤ a ^ d * a ^ d := by positivity
  calc a ^ d * a ^ d * (k.factorial : ℝ)
          * ∑ x : FinLatticeSites d N, ∑ y : FinLatticeSites d N,
            canonicalSmoothCovariance d N a mass T x y ^ k
      ≤ a ^ d * a ^ d * (k.factorial : ℝ)
          * ∑ x : FinLatticeSites d N, ∑ y : FinLatticeSites d N,
            |canonicalSmoothCovariance d N a mass T x y| ^ k :=
        mul_le_mul_of_nonneg_left habs (by positivity)
    _ = (k.factorial : ℝ) * (a ^ d * a ^ d * ∑ x : FinLatticeSites d N,
            ∑ y : FinLatticeSites d N, |canonicalSmoothCovariance d N a mass T x y| ^ k) := by ring
    _ ≤ (k.factorial : ℝ) * (C1 * (1 + |Real.log T|) ^ k) :=
        mul_le_mul_of_nonneg_left (hM1 N a ha hvol T hT) hkfac
    _ = (k.factorial : ℝ) * C1 * (1 + |Real.log T|) ^ k := by ring

/-- **M2 — smooth interaction variance, uniform.** `∫ (canonicalSmoothInteraction)² dμ_joint ≤
C·(1+|log T|)^{P.n}` uniform in `N`. Via M2a (`V_s = (1/P.n)·crossTerm(P.n,P.n) + ∑_m coeff_m·
crossTerm(m,m)`), pointwise `(a+b)² ≤ 2a²+2b²` and Cauchy–Schwarz `(∑cᵢgᵢ)² ≤ (∑cᵢ²)(∑gᵢ²)`, then
the per-term bound M2c. No orthogonality needed. -/
theorem canonicalSmoothInteraction_variance_le {d : ℕ} (hd : d = 2) (mass L : ℝ)
    (hL : 0 < L) (hmass : 0 < mass) (P : InteractionPolynomial) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a) (_hvol : (N : ℝ) * a = L)
      (T : ℝ) (_hT : 0 < T),
      ∫ η, (canonicalSmoothInteraction d N a mass T P η) ^ 2 ∂(canonicalJointMeasure d N)
        ≤ C * (1 + |Real.log T|) ^ P.n := by
  obtain ⟨CL, hCLpos, hCLbd⟩ := canonicalCrossTerm_diag_l2_sq_le hd mass L hL hmass P.n
  choose Cm hCmpos hCmbd using fun m : Fin P.n =>
    canonicalCrossTerm_diag_l2_sq_le hd mass L hL hmass (m : ℕ)
  have hsumCm : (0 : ℝ) ≤ ∑ m : Fin P.n, ((m : ℕ).factorial : ℝ) * Cm m :=
    Finset.sum_nonneg fun m _ => mul_nonneg (by positivity) (hCmpos m).le
  refine ⟨2 * (1 / P.n : ℝ) ^ 2 * ((P.n).factorial : ℝ) * CL
      + 2 * (∑ m : Fin P.n, P.coeff m ^ 2) * (∑ m : Fin P.n, ((m : ℕ).factorial : ℝ) * Cm m) + 1,
      ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 2 * (1 / P.n : ℝ) ^ 2 * ((P.n).factorial : ℝ) * CL := by positivity
    have h2 : (0 : ℝ) ≤ 2 * (∑ m : Fin P.n, P.coeff m ^ 2)
        * (∑ m : Fin P.n, ((m : ℕ).factorial : ℝ) * Cm m) :=
      mul_nonneg (by positivity) hsumCm
    linarith
  intro N _ a ha hvol T hT
  set μ := canonicalJointMeasure d N with hμ
  set CT : ℕ → CanonicalJoint d N → ℝ := fun k η => canonicalCrossTerm d N a mass T η k k with hCT
  set u := (1 + |Real.log T|) with hudef
  have hu1 : (1 : ℝ) ≤ u := by rw [hudef]; nlinarith [abs_nonneg (Real.log T)]
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have hCTsq_int : ∀ k, Integrable (fun η => (CT k η) ^ 2) μ := fun k => by
    have h := canonicalCrossTerm_pair_integrable d N a mass ha hmass T hT k k k k
    simpa [hCT, pow_two] using h
  have hbound_int : Integrable (fun η => 2 * (1 / P.n : ℝ) ^ 2 * (CT P.n η) ^ 2
      + 2 * (∑ m : Fin P.n, P.coeff m ^ 2) * ∑ m : Fin P.n, (CT (m : ℕ) η) ^ 2) μ := by
    apply Integrable.add
    · exact (hCTsq_int P.n).const_mul _
    · exact (integrable_finset_sum Finset.univ
        (fun (m : Fin P.n) _ => hCTsq_int (m : ℕ))).const_mul _
  have hptwise : ∀ η, (canonicalSmoothInteraction d N a mass T P η) ^ 2
      ≤ 2 * (1 / P.n : ℝ) ^ 2 * (CT P.n η) ^ 2
        + 2 * (∑ m : Fin P.n, P.coeff m ^ 2) * ∑ m : Fin P.n, (CT (m : ℕ) η) ^ 2 := by
    intro η
    rw [canonicalSmoothInteraction_eq_sum_crossTerm_diag d N a mass T P η]
    have hCS : (∑ m : Fin P.n, P.coeff m * CT (m : ℕ) η) ^ 2
        ≤ (∑ m : Fin P.n, P.coeff m ^ 2) * ∑ m : Fin P.n, (CT (m : ℕ) η) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun m => P.coeff m) (fun m => CT (m : ℕ) η)
    have hsplit : ((1 / P.n : ℝ) * CT P.n η + ∑ m : Fin P.n, P.coeff m * CT (m : ℕ) η) ^ 2
        ≤ 2 * ((1 / P.n : ℝ) * CT P.n η) ^ 2
          + 2 * (∑ m : Fin P.n, P.coeff m * CT (m : ℕ) η) ^ 2 := by
      nlinarith [sq_nonneg ((1 / P.n : ℝ) * CT P.n η - ∑ m : Fin P.n, P.coeff m * CT (m : ℕ) η)]
    have h2 : (2 : ℝ) * (∑ m : Fin P.n, P.coeff m * CT (m : ℕ) η) ^ 2
        ≤ 2 * ((∑ m : Fin P.n, P.coeff m ^ 2) * ∑ m : Fin P.n, (CT (m : ℕ) η) ^ 2) :=
      by linarith [mul_le_mul_of_nonneg_left hCS (by norm_num : (0 : ℝ) ≤ 2)]
    calc ((1 / P.n : ℝ) * CT P.n η + ∑ m : Fin P.n, P.coeff m * CT (m : ℕ) η) ^ 2
        ≤ 2 * ((1 / P.n : ℝ) * CT P.n η) ^ 2
            + 2 * (∑ m : Fin P.n, P.coeff m * CT (m : ℕ) η) ^ 2 := hsplit
      _ ≤ 2 * (1 / P.n : ℝ) ^ 2 * (CT P.n η) ^ 2
            + 2 * ((∑ m : Fin P.n, P.coeff m ^ 2) * ∑ m : Fin P.n, (CT (m : ℕ) η) ^ 2) := by
          have : 2 * ((1 / P.n : ℝ) * CT P.n η) ^ 2 = 2 * (1 / P.n : ℝ) ^ 2 * (CT P.n η) ^ 2 := by
            ring
          linarith [this, h2]
      _ = _ := by ring
  -- integrate the pointwise bound
  have hmono : ∫ η, (canonicalSmoothInteraction d N a mass T P η) ^ 2 ∂μ
      ≤ ∫ η, (2 * (1 / P.n : ℝ) ^ 2 * (CT P.n η) ^ 2
          + 2 * (∑ m : Fin P.n, P.coeff m ^ 2) * ∑ m : Fin P.n, (CT (m : ℕ) η) ^ 2) ∂μ :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _) hbound_int
      (Filter.Eventually.of_forall hptwise)
  have hsplit_int : ∫ η, (2 * (1 / P.n : ℝ) ^ 2 * (CT P.n η) ^ 2
        + 2 * (∑ m : Fin P.n, P.coeff m ^ 2) * ∑ m : Fin P.n, (CT (m : ℕ) η) ^ 2) ∂μ
      = 2 * (1 / P.n : ℝ) ^ 2 * (∫ η, (CT P.n η) ^ 2 ∂μ)
        + 2 * (∑ m : Fin P.n, P.coeff m ^ 2) * ∑ m : Fin P.n, ∫ η, (CT (m : ℕ) η) ^ 2 ∂μ := by
    rw [integral_add ((hCTsq_int P.n).const_mul _)
      ((integrable_finset_sum Finset.univ
        (fun (m : Fin P.n) _ => hCTsq_int (m : ℕ))).const_mul _),
      integral_const_mul, integral_const_mul,
      integral_finset_sum Finset.univ (fun (m : Fin P.n) _ => hCTsq_int (m : ℕ))]
  rw [hsplit_int] at hmono
  refine hmono.trans ?_
  -- bound each integral via M2c and u^k ≤ u^{P.n}
  have hleadbd : ∫ η, (CT P.n η) ^ 2 ∂μ ≤ ((P.n).factorial : ℝ) * CL * u ^ P.n :=
    hCLbd N a ha hvol T hT
  have hmbd : ∀ m : Fin P.n, ∫ η, (CT (m : ℕ) η) ^ 2 ∂μ
      ≤ ((m : ℕ).factorial : ℝ) * Cm m * u ^ P.n := by
    intro m
    refine (hCmbd m N a ha hvol T hT).trans ?_
    have hpow : u ^ (m : ℕ) ≤ u ^ P.n := pow_le_pow_right₀ hu1 (le_of_lt m.2)
    have : (0 : ℝ) ≤ ((m : ℕ).factorial : ℝ) * Cm m :=
      mul_nonneg (by positivity) (hCmpos m).le
    nlinarith [mul_le_mul_of_nonneg_left hpow this]
  have hsum_m : (∑ m : Fin P.n, ∫ η, (CT (m : ℕ) η) ^ 2 ∂μ)
      ≤ (∑ m : Fin P.n, ((m : ℕ).factorial : ℝ) * Cm m) * u ^ P.n := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun m _ => hmbd m
  have hcoeff_nn : (0 : ℝ) ≤ 2 * (∑ m : Fin P.n, P.coeff m ^ 2) := by positivity
  have hupn : (0 : ℝ) ≤ u ^ P.n := by positivity
  calc 2 * (1 / P.n : ℝ) ^ 2 * (∫ η, (CT P.n η) ^ 2 ∂μ)
        + 2 * (∑ m : Fin P.n, P.coeff m ^ 2) * ∑ m : Fin P.n, ∫ η, (CT (m : ℕ) η) ^ 2 ∂μ
      ≤ 2 * (1 / P.n : ℝ) ^ 2 * (((P.n).factorial : ℝ) * CL * u ^ P.n)
        + 2 * (∑ m : Fin P.n, P.coeff m ^ 2)
            * ((∑ m : Fin P.n, ((m : ℕ).factorial : ℝ) * Cm m) * u ^ P.n) := by
        gcongr
    _ = (2 * (1 / P.n : ℝ) ^ 2 * ((P.n).factorial : ℝ) * CL
          + 2 * (∑ m : Fin P.n, P.coeff m ^ 2)
              * (∑ m : Fin P.n, ((m : ℕ).factorial : ℝ) * Cm m)) * u ^ P.n := by ring
    _ ≤ (2 * (1 / P.n : ℝ) ^ 2 * ((P.n).factorial : ℝ) * CL
          + 2 * (∑ m : Fin P.n, P.coeff m ^ 2)
              * (∑ m : Fin P.n, ((m : ℕ).factorial : ℝ) * Cm m) + 1) * u ^ P.n := by
        nlinarith [hupn]

/-- **`(canonicalSmoothInteraction)²` is integrable** on the joint measure: dominated by the M2b
bound `2(1/P.n)²·CT(P.n,P.n)² + 2(∑coeff²)·∑_m CT(m,m)²` (integrable via
`canonicalCrossTerm_pair_integrable`), with measurability from `canonicalSmoothFieldFunction`. -/
theorem canonicalSmoothInteraction_sq_integrable (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T) (P : InteractionPolynomial) :
    Integrable (fun η => (canonicalSmoothInteraction d N a mass T P η) ^ 2)
      (canonicalJointMeasure d N) := by
  set μ := canonicalJointMeasure d N with hμ
  set CT : ℕ → CanonicalJoint d N → ℝ := fun k η => canonicalCrossTerm d N a mass T η k k with hCT
  have hCTsq_int : ∀ k, Integrable (fun η => (CT k η) ^ 2) μ := fun k => by
    have h := canonicalCrossTerm_pair_integrable d N a mass ha hmass T hT k k k k
    simpa [hCT, pow_two] using h
  have hbound_int : Integrable (fun η => 2 * (1 / P.n : ℝ) ^ 2 * (CT P.n η) ^ 2
      + 2 * (∑ m : Fin P.n, P.coeff m ^ 2) * ∑ m : Fin P.n, (CT (m : ℕ) η) ^ 2) μ := by
    apply Integrable.add
    · exact (hCTsq_int P.n).const_mul _
    · exact (integrable_finset_sum Finset.univ
        (fun (m : Fin P.n) _ => hCTsq_int (m : ℕ))).const_mul _
  have hVs_meas : Measurable (fun η => canonicalSmoothInteraction d N a mass T P η) := by
    unfold canonicalSmoothInteraction
    refine measurable_const.mul (Finset.measurable_sum _ fun x _ => ?_)
    exact ((wickPolynomial_continuous₂ P).comp
      (continuous_const.prodMk continuous_id)).measurable.comp
      (canonicalSmoothFieldFunction_pointwise_measurable d N a mass T x)
  refine Integrable.mono' hbound_int (hVs_meas.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun η => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    canonicalSmoothInteraction_eq_sum_crossTerm_diag d N a mass T P η]
  have hCS : (∑ m : Fin P.n, P.coeff m * CT (m : ℕ) η) ^ 2
      ≤ (∑ m : Fin P.n, P.coeff m ^ 2) * ∑ m : Fin P.n, (CT (m : ℕ) η) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun m => P.coeff m) (fun m => CT (m : ℕ) η)
  nlinarith [sq_nonneg ((1 / P.n : ℝ) * CT P.n η - ∑ m : Fin P.n, P.coeff m * CT (m : ℕ) η),
    mul_le_mul_of_nonneg_left hCS (by norm_num : (0 : ℝ) ≤ 2)]

/-- **L1 — uniform `∫ V² dμ_GFF ≤ C`.** The K-leaf analytic core, uniform in `N` on the torus
(`a = L/N`). Via the bridge `∫V² dμ_GFF = ∫V_full² dμ_joint` (at `T=1`),
`V_full = V_smooth + V_rough`, the pointwise `(a+b)² ≤ 2a²+2b²`, and the smooth
(`canonicalSmoothInteraction_variance_le`) and rough (`rough_error_variance`) variance bounds —
the `(1+|log 1|)` factors vanish at `T=1`. No orthogonality needed. -/
theorem interaction_variance_le (L mass : ℝ) [Fact (0 < L)] (hmass : 0 < mass)
    (P : InteractionPolynomial) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N],
      ∫ ω, (interactionFunctional 2 N P (circleSpacing L N) mass ω) ^ 2
          ∂(latticeGaussianMeasure 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass)
        ≤ C := by
  have hL : (0 : ℝ) < L := Fact.out
  obtain ⟨Cs, hCspos, hCsbd⟩ :=
    canonicalSmoothInteraction_variance_le (d := 2) rfl mass L hL hmass P
  obtain ⟨Cr, hCrpos, hCrbd⟩ := rough_error_variance (d := 2) rfl P L mass hL hmass
  refine ⟨2 * Cs + 2 * Cr, by positivity, ?_⟩
  intro N _
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hvol : (N : ℝ) * circleSpacing L N = L := by rw [circleSpacing_eq]; field_simp
  have hVs2 := canonicalSmoothInteraction_sq_integrable 2 N (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass 1 one_pos P
  have hVr2 := canonicalRoughError_sq_integrable (d := 2) (N := N)
    (a := circleSpacing L N) (mass := mass) (circleSpacing_pos L N) hmass 1 one_pos P
  rw [integral_interaction_sq_eq_canonicalJoint 2 N (circleSpacing L N) mass P
    (circleSpacing_pos L N) hmass 1 one_pos]
  have hptwise : ∀ η, (canonicalFullInteractionJoint 2 N (circleSpacing L N) mass 1 P η) ^ 2
      ≤ 2 * (canonicalSmoothInteraction 2 N (circleSpacing L N) mass 1 P η) ^ 2
        + 2 * (canonicalRoughError 2 N (circleSpacing L N) mass 1 P η) ^ 2 := by
    intro η
    have hfe : canonicalFullInteractionJoint 2 N (circleSpacing L N) mass 1 P η
        = canonicalSmoothInteraction 2 N (circleSpacing L N) mass 1 P η
          + canonicalRoughError 2 N (circleSpacing L N) mass 1 P η := by
      unfold canonicalRoughError; ring
    rw [hfe]
    nlinarith [sq_nonneg (canonicalSmoothInteraction 2 N (circleSpacing L N) mass 1 P η
      - canonicalRoughError 2 N (circleSpacing L N) mass 1 P η)]
  calc ∫ η, (canonicalFullInteractionJoint 2 N (circleSpacing L N) mass 1 P η) ^ 2
          ∂(canonicalJointMeasure 2 N)
      ≤ ∫ η, (2 * (canonicalSmoothInteraction 2 N (circleSpacing L N) mass 1 P η) ^ 2
          + 2 * (canonicalRoughError 2 N (circleSpacing L N) mass 1 P η) ^ 2)
          ∂(canonicalJointMeasure 2 N) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _)
          ((hVs2.const_mul 2).add (hVr2.const_mul 2)) (Filter.Eventually.of_forall hptwise)
    _ = 2 * (∫ η, (canonicalSmoothInteraction 2 N (circleSpacing L N) mass 1 P η) ^ 2
          ∂(canonicalJointMeasure 2 N))
        + 2 * (∫ η, (canonicalRoughError 2 N (circleSpacing L N) mass 1 P η) ^ 2
          ∂(canonicalJointMeasure 2 N)) := by
        rw [integral_add (hVs2.const_mul 2) (hVr2.const_mul 2), integral_const_mul,
          integral_const_mul]
    _ ≤ 2 * Cs + 2 * Cr := by
        have h1 := hCsbd N (circleSpacing L N) (circleSpacing_pos L N) hvol 1 one_pos
        have h2 := hCrbd N (circleSpacing L N) (circleSpacing_pos L N) hvol 1 one_pos
        simp only [Real.log_one, abs_zero, add_zero, one_pow, mul_one] at h1 h2
        linarith

/-- **L2-for-V — uniform even-moment bound.** `∃ K, ∀ N, ∫ V^{2m} dμ_GFF ≤ K` uniform on the torus
(`m ≥ 1`). Via the bridge `∫V^{2m}dμ_GFF = ∫V_full^{2m}dμ_joint`, the full-interaction Bonami–Nelson
moment bound `canonicalFullInteractionJoint_moment_le`, the `T=1` `∫V_full² = ∫V²dμ_GFF` bridge, and
L1 (`interaction_variance_le`, `∫V² ≤ C`). This is what L3's Cauchy–Schwarz consumes. -/
theorem interaction_moment_le (L mass : ℝ) [Fact (0 < L)] (hmass : 0 < mass)
    (P : InteractionPolynomial) (m : ℕ) (hm : 1 ≤ m) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) [NeZero N],
      ∫ ω, (interactionFunctional 2 N P (circleSpacing L N) mass ω) ^ (2 * m)
          ∂(latticeGaussianMeasure 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass)
        ≤ K := by
  have hL : (0 : ℝ) < L := Fact.out
  obtain ⟨C2, hC2pos, hC2⟩ := interaction_variance_le L mass hmass P
  set q : ℝ := ((2 * m : ℕ) : ℝ) with hq
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hq2 : (2 : ℝ) ≤ q := by rw [hq]; push_cast; nlinarith [hm']
  have hq1 : (1 : ℝ) ≤ q - 1 := by linarith
  set Cb : ℝ := ((P.n : ℝ) + 1) * (q - 1) ^ ((P.n : ℝ) / 2) with hCb
  have hCbpos : 0 < Cb := by rw [hCb]; positivity
  refine ⟨Cb ^ q * C2 ^ m, mul_pos (Real.rpow_pos_of_pos hCbpos _) (pow_pos hC2pos m), ?_⟩
  intro N _
  have ha : 0 < circleSpacing L N := circleSpacing_pos L N
  have hbridge :
      ∫ ω, (interactionFunctional 2 N P (circleSpacing L N) mass ω) ^ (2 * m)
          ∂(latticeGaussianMeasure 2 N (circleSpacing L N) mass ha hmass)
        = ∫ η, (canonicalFullInteractionJoint 2 N (circleSpacing L N) mass 1 P η) ^ (2 * m)
            ∂(canonicalJointMeasure 2 N) := by
    rw [← integral_comp_canonicalSumConfig (d := 2) (N := N) (a := circleSpacing L N)
      (mass := mass) ha hmass 1 one_pos
      (F := fun ω => (interactionFunctional 2 N P (circleSpacing L N) mass ω) ^ (2 * m))
      ((interactionFunctional_measurable 2 N P (circleSpacing L N) mass).pow_const (2 * m))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    simp only [canonicalFullInteractionJoint_eq_interactionFunctional]
  have heqpow :
      (fun η => (canonicalFullInteractionJoint 2 N (circleSpacing L N) mass 1 P η) ^ (2 * m))
        = (fun η => |canonicalFullInteractionJoint 2 N (circleSpacing L N) mass 1 P η| ^ q) := by
    funext η; rw [hq, Real.rpow_natCast, (even_two_mul m).pow_abs]
  rw [hbridge, heqpow]
  have hmom := canonicalFullInteractionJoint_moment_le 2 N (circleSpacing L N) mass ha hmass
    1 one_pos P q hq2
  have hvar :
      ∫ η, |canonicalFullInteractionJoint 2 N (circleSpacing L N) mass 1 P η| ^ (2 : ℝ)
          ∂(canonicalJointMeasure 2 N) ≤ C2 := by
    have heq2 :
        (fun η => |canonicalFullInteractionJoint 2 N (circleSpacing L N) mass 1 P η| ^ (2 : ℝ))
          = (fun η => (canonicalFullInteractionJoint 2 N (circleSpacing L N) mass 1 P η) ^ 2) := by
      funext η; rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    rw [heq2,
      ← integral_interaction_sq_eq_canonicalJoint 2 N (circleSpacing L N) mass P ha hmass 1 one_pos]
    exact hC2 N
  have hvar_nn :
      0 ≤ ∫ η, |canonicalFullInteractionJoint 2 N (circleSpacing L N) mass 1 P η| ^ (2 : ℝ)
        ∂(canonicalJointMeasure 2 N) := integral_nonneg fun η => Real.rpow_nonneg (abs_nonneg _) _
  refine hmom.trans ?_
  rw [← hCb, show q / 2 = (m : ℝ) by rw [hq]; push_cast; ring]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hCbpos.le q)
  rw [← Real.rpow_natCast C2 m]
  exact Real.rpow_le_rpow hvar_nn hvar (by positivity)

/-- **L3b — free even-moment hypercontractivity.** For any lattice test function `f` and `m ≥ 1`,
the GFF even moment is controlled by the variance:
`∫(ωf)^{2m} dμ_GFF ≤ (2m-1)^m·(∫(ωf)² dμ_GFF)^m`. Direct from `gaussian_hypercontractive`
(`n=1, p=2m`). Combined with a uniform variance bound it yields the uniform field moment consumed
by the L3 Cauchy–Schwarz. -/
theorem field_pow_le_second_pow {d N : ℕ} [NeZero N] (a mass : ℝ) (ha : 0 < a)
    (hmass : 0 < mass)
    (f : FinLatticeField d N) (m : ℕ) (hm : 1 ≤ m) :
    ∫ ω, (ω f) ^ (2 * m) ∂(latticeGaussianMeasure d N a mass ha hmass)
      ≤ ((2 * m : ℝ) - 1) ^ m
        * (∫ ω, (ω f) ^ 2 ∂(latticeGaussianMeasure d N a mass ha hmass)) ^ m := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  set T := latticeCovarianceGJ d N a mass ha hmass with hT
  have hμ : latticeGaussianMeasure d N a mass ha hmass = GaussianField.measure T := rfl
  have hp : (2 : ℝ) ≤ 2 * (m : ℝ) := by linarith
  have h_hyper := gaussian_hypercontractive T f 1 (2 * (m : ℝ)) hp m hm (by push_cast; ring)
  simp only [Nat.cast_one, mul_one] at h_hyper
  rw [show (2 * (m : ℝ)) / 2 = (m : ℝ) by ring] at h_hyper
  rw [hμ]
  -- Convert the goal's `npow`/`(ωf)` integrands into the `rpow`/`|ωf|` form of `h_hyper`.
  have key1 : ∫ ω, (ω f) ^ (2 * m) ∂(GaussianField.measure T)
      = ∫ ω, |ω f| ^ (2 * (m : ℝ)) ∂(GaussianField.measure T) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show (ω f) ^ (2 * m) = |ω f| ^ (2 * (m : ℝ))
    rw [show (2 * (m : ℝ)) = ((2 * m : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
      (even_two_mul m).pow_abs]
  have key2 : ∫ ω, (ω f) ^ 2 ∂(GaussianField.measure T)
      = ∫ ω, |ω f| ^ (2 : ℕ) ∂(GaussianField.measure T) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show (ω f) ^ 2 = |ω f| ^ (2 : ℕ)
    rw [sq_abs]
  rw [key1, key2, ← Real.rpow_natCast ((2 : ℝ) * (m : ℝ) - 1) m,
    ← Real.rpow_natCast (∫ ω, |ω f| ^ (2 : ℕ) ∂(GaussianField.measure T)) m]
  exact h_hyper

/-- **L3a — `V ∈ Lᵖ` on the GFF** (`p ≥ 2`, per `N`). Transfers
`canonicalFullInteractionJoint_memLp` from the joint measure to the lattice GFF via
`canonicalJointMeasure_map_canonicalSumConfig` and
`canonicalFullInteractionJoint_eq_interactionFunctional`. In particular `V^{2k} ∈ L²` (so the L3
Cauchy–Schwarz applies). -/
theorem interaction_memLp (N : ℕ) [NeZero N] (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (p : ℝ) (hp : 2 ≤ p) :
    MeasureTheory.MemLp (fun ω => interactionFunctional 2 N P a mass ω)
      (ENNReal.ofReal p)
      (latticeGaussianMeasure 2 N a mass ha hmass) := by
  have hVfull := canonicalFullInteractionJoint_memLp 2 N a mass ha hmass 1 one_pos P p hp
  rw [show latticeGaussianMeasure 2 N a mass ha hmass
      = (canonicalJointMeasure 2 N).map (canonicalSumConfig 2 N a mass 1)
      from (canonicalJointMeasure_map_canonicalSumConfig 2 N a mass ha hmass 1 one_pos).symm,
    memLp_map_measure_iff
      (interactionFunctional_measurable 2 N P a mass).aestronglyMeasurable
      (canonicalSumConfig_measurable 2 N a mass 1).aemeasurable]
  refine hVfull.ae_eq ?_
  filter_upwards with η
  simp only [Function.comp_apply, canonicalFullInteractionJoint_eq_interactionFunctional]

/-- **Per-`N` integrability of `Vᵐ` powers** on the lattice GFF (`m ≥ 2`): since `V ∈ Lᵐ` for all
`m ≥ 2`, the even power `V^{2k}` is `L²` (`k ≥ 1`) and `Vⁿ` is integrable (`n ≥ 2`). Direct from
`interaction_memLp`. -/
theorem interactionFunctional_pow_integrable (N : ℕ) [NeZero N] (a mass : ℝ) (ha : 0 < a)
    (hmass : 0 < mass) (P : InteractionPolynomial) (n : ℕ) (hn : 2 ≤ n) :
    MeasureTheory.Integrable (fun ω => (interactionFunctional 2 N P a mass ω) ^ n)
      (latticeGaussianMeasure 2 N a mass ha hmass) := by
  have hmem : MemLp (fun ω => interactionFunctional 2 N P a mass ω) (n : ENNReal)
      (latticeGaussianMeasure 2 N a mass ha hmass) := by
    have h := interaction_memLp N a mass ha hmass P (n : ℝ) (by exact_mod_cast hn)
    rwa [ENNReal.ofReal_natCast] at h
  have h := hmem.norm_rpow (p := (n : ENNReal)) (by exact_mod_cast (by omega : n ≠ 0)) (by simp)
  rw [memLp_one_iff_integrable] at h
  have hint_abs : Integrable (fun ω => |interactionFunctional 2 N P a mass ω| ^ n)
      (latticeGaussianMeasure 2 N a mass ha hmass) :=
    h.congr (Filter.Eventually.of_forall fun ω => by
      simp [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs])
  exact hint_abs.mono'
    ((interactionFunctional_measurable 2 N P a mass).pow_const n).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => le_of_eq (by rw [Real.norm_eq_abs, abs_pow]))

/-- **L3c — Cauchy–Schwarz split of the free product moment.** For `k ≥ 1`,
`∫(ωf)^{2n}·V^{2k} dμ_GFF ≤ (∫(ωf)^{4n})^{1/2}·(∫V^{4k})^{1/2}` (Hölder with conjugate `2,2`). The
field factor `(ωf)^{2n} ∈ L²` (`pairing_memLp`) and the interaction factor `V^{2k} ∈ L²`
(`interaction_memLp`). Combined with `field_pow_le_second_pow` (field) and `interaction_moment_le`
(`V`), this yields the uniform free moment `⟨φ^{2n}V^{2k}⟩₀ ≤ K₀` that L4 consumes. -/
theorem free_product_moment_cauchy_schwarz {N : ℕ} [NeZero N] (P : InteractionPolynomial)
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (f : FinLatticeField 2 N) (n k : ℕ) (hk : 1 ≤ k) :
    ∫ ω, (ω f) ^ (2 * n) * (interactionFunctional 2 N P a mass ω) ^ (2 * k)
        ∂(latticeGaussianMeasure 2 N a mass ha hmass)
      ≤ (∫ ω, (ω f) ^ (4 * n) ∂(latticeGaussianMeasure 2 N a mass ha hmass)) ^ (1 / 2 : ℝ)
        * (∫ ω, (interactionFunctional 2 N P a mass ω) ^ (4 * k)
            ∂(latticeGaussianMeasure 2 N a mass ha hmass)) ^ (1 / 2 : ℝ) := by
  set μ := latticeGaussianMeasure 2 N a mass ha hmass with hμ
  have hf_mem : MemLp (fun ω => (ω f) ^ (2 * n)) 2 μ := by
    rw [memLp_two_iff_integrable_sq
      ((configuration_eval_measurable f).pow_const (2 * n)).aestronglyMeasurable]
    refine (integrable_pow_pairing 2 N a mass ha hmass f (4 * n)).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    show (ω f) ^ (4 * n) = ((ω f) ^ (2 * n)) ^ 2
    rw [← pow_mul]; congr 1; ring
  have hg_mem : MemLp (fun ω => (interactionFunctional 2 N P a mass ω) ^ (2 * k)) 2 μ := by
    rw [memLp_two_iff_integrable_sq
      ((interactionFunctional_measurable 2 N P a mass).pow_const (2 * k)).aestronglyMeasurable]
    refine (interactionFunctional_pow_integrable N a mass ha hmass P (4 * k) (by omega)).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    show (interactionFunctional 2 N P a mass ω) ^ (4 * k)
      = ((interactionFunctional 2 N P a mass ω) ^ (2 * k)) ^ 2
    rw [← pow_mul]; congr 1; ring
  have key := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    (f := fun ω => (ω f) ^ (2 * n)) (g := fun ω => (interactionFunctional 2 N P a mass ω) ^ (2 * k))
    (Filter.Eventually.of_forall fun ω => (even_two_mul n).pow_nonneg _)
    (Filter.Eventually.of_forall fun ω => (even_two_mul k).pow_nonneg _)
    (by rw [ENNReal.ofReal_ofNat]; exact hf_mem) (by rw [ENNReal.ofReal_ofNat]; exact hg_mem)
  refine le_trans key (le_of_eq ?_)
  congr 1
  · congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show ((ω f) ^ (2 * n)) ^ (2 : ℝ) = (ω f) ^ (4 * n)
    rw [Real.rpow_two, ← pow_mul]; congr 1; ring
  · congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show ((interactionFunctional 2 N P a mass ω) ^ (2 * k)) ^ (2 : ℝ)
      = (interactionFunctional 2 N P a mass ω) ^ (4 * k)
    rw [Real.rpow_two, ← pow_mul]; congr 1; ring

end Pphi2
