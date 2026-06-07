/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.InteractingMeasure.InteractionFourPoint
import GaussianField.Properties

/-!
# Moment integrability foundations (u₄ step 2c, step 1)

Integrability of raw pairing powers `(ω f)ⁿ` and their products with the interaction `V` under the
lattice GFF — the domination inputs for differentiating the Gibbs family `g ↦ ∫ (ω f)ⁿ e^{−gV} dμ_GFF`
under the integral sign.

Key facts: `latticeGaussianMeasure = GaussianField.measure (latticeCovarianceGJ …)` (definitionally),
so `pairing_memLp` gives `ω f ∈ Lᵖ` for every `p`; the `‖·‖^n` route (mirroring
`TorusInteractingMoments`) then gives integrability of the raw powers.
-/

namespace Pphi2

open MeasureTheory GaussianField
open scoped NNReal ENNReal

variable (d N : ℕ) [NeZero N]

/-- The pairing `ω ↦ ω f` lies in every `Lᵖ` of the lattice GFF. (Repackages `pairing_memLp` for the
`latticeGaussianMeasure` form, which is `GaussianField.measure (latticeCovarianceGJ …)` by `rfl`.) -/
theorem pairing_memLp_lattice (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : FinLatticeField d N) (p : ℝ≥0) :
    MemLp (fun ω : Configuration (FinLatticeField d N) => ω f) (p : ℝ≥0∞)
      (latticeGaussianMeasure d N a mass ha hmass) :=
  pairing_memLp (latticeCovarianceGJ d N a mass ha hmass) f p

/-- **Raw moment integrability.** `(ω f)ⁿ` is integrable under the lattice GFF (the `n`-th moment of
the pairing is finite, since `ω f ∈ Lⁿ`). -/
theorem integrable_pow_pairing (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : FinLatticeField d N) (n : ℕ) :
    Integrable (fun ω => (ω f) ^ n) (latticeGaussianMeasure d N a mass ha hmass) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [pow_zero]
    exact integrable_const (1 : ℝ)
  · have hmem : MemLp (fun ω : Configuration (FinLatticeField d N) => ω f) (n : ℝ≥0∞)
        (latticeGaussianMeasure d N a mass ha hmass) := by
      exact_mod_cast pairing_memLp_lattice d N a mass ha hmass f n
    have h := hmem.norm_rpow (p := (n : ℝ≥0∞)) (by exact_mod_cast hn.ne') (by simp)
    rw [memLp_one_iff_integrable] at h
    have hint_abs : Integrable (fun ω => |ω f| ^ n)
        (latticeGaussianMeasure d N a mass ha hmass) := by
      refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs]
    exact hint_abs.mono'
      ((configuration_eval_measurable f).pow_const n).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => le_of_eq (by rw [Real.norm_eq_abs, abs_pow]))

/-- **Product of two raw pairing moments is integrable.** `(ω f)ⁿ · (ω g)ᵐ` is integrable under the
lattice GFF — by AM–GM domination `|XY| ≤ ½(X²+Y²)` with `X=(ω f)ⁿ`, `Y=(ω g)ᵐ` and the raw-moment
integrability of `(ω f)²ⁿ`, `(ω g)²ᵐ`. -/
theorem integrable_pow_pairing_mul (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f g : FinLatticeField d N) (n m : ℕ) :
    Integrable (fun ω => (ω f) ^ n * (ω g) ^ m) (latticeGaussianMeasure d N a mass ha hmass) := by
  have hf := integrable_pow_pairing d N a mass ha hmass f (2 * n)
  have hg := integrable_pow_pairing d N a mass ha hmass g (2 * m)
  have hG : Integrable (fun ω => (1 / 2 : ℝ) * ((ω f) ^ (2 * n) + (ω g) ^ (2 * m)))
      (latticeGaussianMeasure d N a mass ha hmass) := (hf.add hg).const_mul _
  refine hG.mono'
    (((configuration_eval_measurable f).pow_const n).mul
      ((configuration_eval_measurable g).pow_const m)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  have hx : (ω f) ^ (2 * n) = ((ω f) ^ n) ^ 2 := by rw [mul_comm, pow_mul]
  have hy : (ω g) ^ (2 * m) = ((ω g) ^ m) ^ 2 := by rw [mul_comm, pow_mul]
  rw [Real.norm_eq_abs, abs_mul, hx, hy]
  nlinarith [two_mul_le_add_sq |(ω f) ^ n| |(ω g) ^ m|, sq_abs ((ω f) ^ n), sq_abs ((ω g) ^ m),
    abs_nonneg ((ω f) ^ n), abs_nonneg ((ω g) ^ m)]

/-- `(ω f)ⁿ · (ω δ_z)ˡ · wickMonomial k c (ω δ_z)` is integrable, for all `k, n, l`. Proved by strong
induction on the Wick degree `k` (the recursion `:xᵏ⁺²: = x:xᵏ⁺¹: − (k+1)c:xᵏ:`), with the extra
`(ω δ_z)ˡ` factor carrying the `x·` of the recursion. The `l = 0` case gives integrability of
`(ω f)ⁿ · wickMonomial k c (ω δ_z)` — the building block for `(ω f)ⁿ · wickPolynomial`. -/
theorem integrable_powMul_wickMonomial (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : FinLatticeField d N) (z : FinLatticeSites d N) (c : ℝ) :
    ∀ (k n l : ℕ), Integrable (fun ω => (ω f) ^ n * (ω (Pi.single z 1)) ^ l *
      wickMonomial k c (ω (Pi.single z 1))) (latticeGaussianMeasure d N a mass ha hmass)
  | 0, n, l => by
      simp only [wickMonomial_zero, mul_one]
      exact integrable_pow_pairing_mul d N a mass ha hmass f (Pi.single z 1) n l
  | 1, n, l => by
      simp only [wickMonomial_one, mul_assoc, ← pow_succ]
      exact integrable_pow_pairing_mul d N a mass ha hmass f (Pi.single z 1) n (l + 1)
  | (k + 2), n, l => by
      have IH1 := integrable_powMul_wickMonomial a mass ha hmass f z c (k + 1) n (l + 1)
      have IH2 := integrable_powMul_wickMonomial a mass ha hmass f z c k n l
      have heq : (fun ω : Configuration (FinLatticeField d N) => (ω f) ^ n *
            (ω (Pi.single z 1)) ^ l * wickMonomial (k + 2) c (ω (Pi.single z 1))) =
          (fun ω : Configuration (FinLatticeField d N) => (ω f) ^ n *
            (ω (Pi.single z 1)) ^ (l + 1) * wickMonomial (k + 1) c (ω (Pi.single z 1)))
          - (fun ω : Configuration (FinLatticeField d N) => ((k : ℝ) + 1) * c *
            ((ω f) ^ n * (ω (Pi.single z 1)) ^ l * wickMonomial k c (ω (Pi.single z 1)))) := by
        funext ω
        simp only [Pi.sub_apply, wickMonomial_succ_succ, pow_succ]
        ring
      rw [heq]
      exact IH1.sub (IH2.const_mul _)

/-- `(ω f)ⁿ · wickMonomial k c (ω δ_z)` is integrable (the `l = 0` case). -/
theorem integrable_powMul_wickMonomial' (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : FinLatticeField d N) (z : FinLatticeSites d N) (c : ℝ) (k n : ℕ) :
    Integrable (fun ω => (ω f) ^ n * wickMonomial k c (ω (Pi.single z 1)))
      (latticeGaussianMeasure d N a mass ha hmass) := by
  have h := integrable_powMul_wickMonomial d N a mass ha hmass f z c k n 0
  simpa using h

/-- `(ω f)ⁿ · wickPolynomial P c (ω δ_z)` is integrable: a finite linear combination of the
`(ω f)ⁿ · wickMonomial m c (ω δ_z)`. -/
theorem integrable_powMul_wickPolynomial (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (f : FinLatticeField d N) (z : FinLatticeSites d N) (c : ℝ)
    (n : ℕ) :
    Integrable (fun ω => (ω f) ^ n * wickPolynomial P c (ω (Pi.single z 1)))
      (latticeGaussianMeasure d N a mass ha hmass) := by
  have hdist : (fun ω : Configuration (FinLatticeField d N) =>
        (ω f) ^ n * wickPolynomial P c (ω (Pi.single z 1))) =
      (fun ω : Configuration (FinLatticeField d N) => (1 / (P.n : ℝ)) *
          ((ω f) ^ n * wickMonomial P.n c (ω (Pi.single z 1)))
        + ∑ m : Fin P.n, P.coeff m *
            ((ω f) ^ n * wickMonomial (m : ℕ) c (ω (Pi.single z 1)))) := by
    funext ω
    rw [wickPolynomial, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun m _ => by ring
  rw [hdist]
  exact ((integrable_powMul_wickMonomial' d N a mass ha hmass f z c P.n n).const_mul _).add
    (integrable_finset_sum _ (fun (m : Fin P.n) _ =>
      (integrable_powMul_wickMonomial' d N a mass ha hmass f z c (m : ℕ) n).const_mul (P.coeff m)))

/-- **Domination integrability for (2c).** `(ω f)ⁿ · V` is integrable, where
`V = a^d ∑_z wickPolynomial P (wickConstant) (φ_z)` is the lattice interaction — the `g=0`
integrand whose dominated derivative drives the differentiation of the Gibbs family. -/
theorem integrable_powMul_interaction (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (f : FinLatticeField d N) (n : ℕ) :
    Integrable (fun ω => (ω f) ^ n *
        (a ^ d * ∑ z, wickPolynomial P (wickConstant d N a mass) (ω (Pi.single z 1))))
      (latticeGaussianMeasure d N a mass ha hmass) := by
  have hc : (fun ω : Configuration (FinLatticeField d N) => (ω f) ^ n *
        (a ^ d * ∑ z, wickPolynomial P (wickConstant d N a mass) (ω (Pi.single z 1)))) =
      (fun ω : Configuration (FinLatticeField d N) => a ^ d *
        ∑ z, ((ω f) ^ n * wickPolynomial P (wickConstant d N a mass) (ω (Pi.single z 1)))) := by
    funext ω
    rw [show (ω f) ^ n * (a ^ d * ∑ z, wickPolynomial P (wickConstant d N a mass) (ω (Pi.single z 1)))
          = a ^ d * ((ω f) ^ n *
            ∑ z, wickPolynomial P (wickConstant d N a mass) (ω (Pi.single z 1))) from by ring,
      Finset.mul_sum]
  rw [hc]
  exact (integrable_finset_sum _ (fun z _ =>
    integrable_powMul_wickPolynomial d N a mass ha hmass P f z (wickConstant d N a mass) n)).const_mul _

/-- `(ω f)ⁿ · (ω δ_z)ˡ · wickMonomial k₁ c (ω δ_z) · wickMonomial k₂ c (ω δ_z)` is integrable
(both Wick factors at the **same** site `z`), for all `k₂, n, l`. Strong induction on the second
degree `k₂` via the recursion `:xᵏ⁺²: = x:xᵏ⁺¹: − (k+1)c:xᵏ:`, with the first Wick factor
`wickMonomial k₁` riding along inertly and the recursion's `x·` absorbed into `(ω δ_z)ˡ`. The base
cases reduce to `integrable_powMul_wickMonomial`. -/
theorem integrable_powMul_wickMonomial_mul (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : FinLatticeField d N) (z : FinLatticeSites d N) (c : ℝ) (k₁ : ℕ) :
    ∀ (k₂ n l : ℕ), Integrable (fun ω => (ω f) ^ n * (ω (Pi.single z 1)) ^ l *
      wickMonomial k₁ c (ω (Pi.single z 1)) * wickMonomial k₂ c (ω (Pi.single z 1)))
      (latticeGaussianMeasure d N a mass ha hmass)
  | 0, n, l => by
      have h := integrable_powMul_wickMonomial d N a mass ha hmass f z c k₁ n l
      have heq : (fun ω : Configuration (FinLatticeField d N) => (ω f) ^ n *
            (ω (Pi.single z 1)) ^ l * wickMonomial k₁ c (ω (Pi.single z 1)) *
            wickMonomial 0 c (ω (Pi.single z 1))) =
          (fun ω : Configuration (FinLatticeField d N) => (ω f) ^ n *
            (ω (Pi.single z 1)) ^ l * wickMonomial k₁ c (ω (Pi.single z 1))) := by
        funext ω; simp only [wickMonomial_zero, mul_one]
      rwa [heq]
  | 1, n, l => by
      have h := integrable_powMul_wickMonomial d N a mass ha hmass f z c k₁ n (l + 1)
      have heq : (fun ω : Configuration (FinLatticeField d N) => (ω f) ^ n *
            (ω (Pi.single z 1)) ^ (l + 1) * wickMonomial k₁ c (ω (Pi.single z 1))) =
          (fun ω : Configuration (FinLatticeField d N) => (ω f) ^ n *
            (ω (Pi.single z 1)) ^ l * wickMonomial k₁ c (ω (Pi.single z 1)) *
            wickMonomial 1 c (ω (Pi.single z 1))) := by
        funext ω; simp only [wickMonomial_one, pow_succ]; ring
      rwa [heq] at h
  | (k₂ + 2), n, l => by
      have IH1 := integrable_powMul_wickMonomial_mul a mass ha hmass f z c k₁ (k₂ + 1) n (l + 1)
      have IH2 := integrable_powMul_wickMonomial_mul a mass ha hmass f z c k₁ k₂ n l
      have heq : (fun ω : Configuration (FinLatticeField d N) => (ω f) ^ n *
            (ω (Pi.single z 1)) ^ l * wickMonomial k₁ c (ω (Pi.single z 1)) *
            wickMonomial (k₂ + 2) c (ω (Pi.single z 1))) =
          (fun ω : Configuration (FinLatticeField d N) => (ω f) ^ n *
            (ω (Pi.single z 1)) ^ (l + 1) * wickMonomial k₁ c (ω (Pi.single z 1)) *
            wickMonomial (k₂ + 1) c (ω (Pi.single z 1)))
          - (fun ω : Configuration (FinLatticeField d N) => ((k₂ : ℝ) + 1) * c *
            ((ω f) ^ n * (ω (Pi.single z 1)) ^ l * wickMonomial k₁ c (ω (Pi.single z 1)) *
              wickMonomial k₂ c (ω (Pi.single z 1)))) := by
        funext ω
        simp only [Pi.sub_apply, wickMonomial_succ_succ, pow_succ]
        ring
      rw [heq]
      exact IH1.sub (IH2.const_mul _)

/-- `(ω f)ⁿ · (ω δ_z)ˡ · wickMonomial k₁ c (ω δ_z) · wickPolynomial P c (ω δ_z)` is integrable
(same site): a finite linear combination of `integrable_powMul_wickMonomial_mul` over the Wick
expansion of the second factor. -/
theorem integrable_powMul_wickMonomial_mulWickPoly (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (f : FinLatticeField d N) (z : FinLatticeSites d N) (c : ℝ)
    (k₁ n l : ℕ) :
    Integrable (fun ω => (ω f) ^ n * (ω (Pi.single z 1)) ^ l *
        wickMonomial k₁ c (ω (Pi.single z 1)) * wickPolynomial P c (ω (Pi.single z 1)))
      (latticeGaussianMeasure d N a mass ha hmass) := by
  have hdist : (fun ω : Configuration (FinLatticeField d N) => (ω f) ^ n *
        (ω (Pi.single z 1)) ^ l * wickMonomial k₁ c (ω (Pi.single z 1)) *
        wickPolynomial P c (ω (Pi.single z 1))) =
      (fun ω : Configuration (FinLatticeField d N) => (1 / (P.n : ℝ)) *
          ((ω f) ^ n * (ω (Pi.single z 1)) ^ l * wickMonomial k₁ c (ω (Pi.single z 1)) *
            wickMonomial P.n c (ω (Pi.single z 1)))
        + ∑ m : Fin P.n, P.coeff m *
            ((ω f) ^ n * (ω (Pi.single z 1)) ^ l * wickMonomial k₁ c (ω (Pi.single z 1)) *
              wickMonomial (m : ℕ) c (ω (Pi.single z 1)))) := by
    funext ω
    rw [wickPolynomial, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun m _ => by ring
  rw [hdist]
  exact ((integrable_powMul_wickMonomial_mul d N a mass ha hmass f z c k₁ P.n n l).const_mul _).add
    (integrable_finset_sum _ (fun m _ =>
      (integrable_powMul_wickMonomial_mul d N a mass ha hmass f z c k₁ (m : ℕ) n l).const_mul
        (P.coeff m)))

/-- `(ω f)ⁿ · (ω δ_z)ˡ · wickPolynomial P c (ω δ_z) · wickPolynomial P c (ω δ_z)` is integrable
(same site): expand the first `wickPolynomial` factor and sum `integrable_powMul_wickMonomial_mulWickPoly`. -/
theorem integrable_powMul_wickPolynomial_mul_self (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (f : FinLatticeField d N) (z : FinLatticeSites d N) (c : ℝ)
    (n l : ℕ) :
    Integrable (fun ω => (ω f) ^ n * (ω (Pi.single z 1)) ^ l *
        wickPolynomial P c (ω (Pi.single z 1)) * wickPolynomial P c (ω (Pi.single z 1)))
      (latticeGaussianMeasure d N a mass ha hmass) := by
  have hdist : (fun ω : Configuration (FinLatticeField d N) => (ω f) ^ n *
        (ω (Pi.single z 1)) ^ l * wickPolynomial P c (ω (Pi.single z 1)) *
        wickPolynomial P c (ω (Pi.single z 1))) =
      (fun ω : Configuration (FinLatticeField d N) => (1 / (P.n : ℝ)) *
          ((ω f) ^ n * (ω (Pi.single z 1)) ^ l * wickMonomial P.n c (ω (Pi.single z 1)) *
            wickPolynomial P c (ω (Pi.single z 1)))
        + ∑ m : Fin P.n, P.coeff m *
            ((ω f) ^ n * (ω (Pi.single z 1)) ^ l * wickMonomial (m : ℕ) c (ω (Pi.single z 1)) *
              wickPolynomial P c (ω (Pi.single z 1)))) := by
    funext ω
    nth_rewrite 1 [wickPolynomial]
    rw [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun m _ => by ring
  rw [hdist]
  exact
    ((integrable_powMul_wickMonomial_mulWickPoly d N a mass ha hmass P f z c P.n n l).const_mul _).add
      (integrable_finset_sum _ (fun m _ =>
        (integrable_powMul_wickMonomial_mulWickPoly d N a mass ha hmass P f z c (m : ℕ) n l).const_mul
          (P.coeff m)))

/-- `(ω f)ⁿ · (wickPolynomial P c (ω δ_z))²` is integrable (the `l = 0` square). -/
theorem integrable_powMul_wickPolynomial_sq (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (f : FinLatticeField d N) (z : FinLatticeSites d N) (c : ℝ)
    (n : ℕ) :
    Integrable (fun ω => (ω f) ^ n * (wickPolynomial P c (ω (Pi.single z 1))) ^ 2)
      (latticeGaussianMeasure d N a mass ha hmass) := by
  have h := integrable_powMul_wickPolynomial_mul_self d N a mass ha hmass P f z c n 0
  have heq : (fun ω : Configuration (FinLatticeField d N) => (ω f) ^ n *
        (ω (Pi.single z 1)) ^ 0 * wickPolynomial P c (ω (Pi.single z 1)) *
        wickPolynomial P c (ω (Pi.single z 1))) =
      (fun ω : Configuration (FinLatticeField d N) => (ω f) ^ n *
        (wickPolynomial P c (ω (Pi.single z 1))) ^ 2) := by
    funext ω; rw [pow_zero, mul_one, sq]; ring
  rwa [heq] at h

end Pphi2
