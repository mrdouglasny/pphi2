/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.InteractingMeasure.SmearedWickVertex
import Pphi2.InteractingMeasure.WickConstantBridge
import Pphi2.WickOrdering.WickPolynomial
import Pphi2.NelsonEstimate.RoughErrorBound

/-!
# Connected four-point against the interaction polynomial (u₄ step 2b)

Evaluates `∫ :φ(f)⁴: · wickPolynomial P (wickConstant) (φ_z) dμ_GFF` — the per-vertex contribution to
the first-order connected four-point `u₄'(0) = −⟨:φ(f)⁴:·V⟩_free`. By Wick orthogonality only the
degree-4 Wick monomial of the interaction polynomial contributes, so the result is the degree-4 weight
of `P` times `4!·(C_a f)(z)⁴ = 24·(∑_x f(x)C(x,z))⁴`.

For the **pure quartic** `P.n = 4` this collapses to `6·(C_a f)(z)⁴` (the `1/4` leading coefficient
times `24`), giving `κ = 6`.

Note: `wickPolynomial` is built from `Pphi2.wickMonomial`, while the smeared Wick kernel uses
GaussianField's `_root_.wickMonomial`; the two agree by `wickMonomial_eq_root_local`.
-/

namespace Pphi2

open MeasureTheory GaussianField

variable (d N : ℕ) [NeZero N]

/-- **Per-vertex connected four-point against the interaction polynomial.**
`∫ :φ(f)⁴: · wickPolynomial P (wickConstant) (φ_z) dμ_GFF` equals the degree-4 weight of `P` times
`24·(C_a f)(z)⁴`: only the degree-4 Wick monomial survives the orthogonality with `:φ(f)⁴:`. -/
theorem wickFourth_wickPolynomial_inner (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (f : FinLatticeField d N) (z : FinLatticeSites d N) :
    ∫ ω, _root_.wickMonomial 4 (gffSmearedCovariance d N a mass f f) (ω f) *
          wickPolynomial P (wickConstant d N a mass) (ω (Pi.single z 1))
        ∂(latticeGaussianMeasure d N a mass ha hmass) =
    (1 / (P.n : ℝ)) *
        (if 4 = P.n then 24 * (∑ x, f x * gffPositionCovariance d N a mass x z) ^ 4 else 0)
      + ∑ m : Fin P.n, P.coeff m *
          (if 4 = (m : ℕ) then
            24 * (∑ x, f x * gffPositionCovariance d N a mass x z) ^ 4 else 0) := by
  -- Rewrite the interaction Wick constant into the eigenbasis site covariance the kernel uses.
  rw [← gffSmearedCovariance_single_single_eq_wickConstant d N a mass ha hmass z]
  -- Integrability of `:φ(f)⁴: · :φ(δ_z)ᵏ:` for every degree `k`.
  have hInt : ∀ k : ℕ, Integrable
      (fun ω => _root_.wickMonomial 4 (gffSmearedCovariance d N a mass f f) (ω f) *
        _root_.wickMonomial k (gffSmearedCovariance d N a mass (Pi.single z 1) (Pi.single z 1))
          (ω (Pi.single z 1)))
      (latticeGaussianMeasure d N a mass ha hmass) := by
    intro k
    rw [gffSmearedCovariance_self d N a mass f,
        gffSmearedCovariance_self d N a mass (Pi.single z 1)]
    exact integrable_wickMonomial_smeared_mul d N a mass ha hmass 4 k f (Pi.single z 1)
  -- Per-term evaluation via the smeared kernel.
  have hterm : ∀ k : ℕ,
      ∫ ω, _root_.wickMonomial 4 (gffSmearedCovariance d N a mass f f) (ω f) *
        _root_.wickMonomial k (gffSmearedCovariance d N a mass (Pi.single z 1) (Pi.single z 1))
          (ω (Pi.single z 1))
        ∂(latticeGaussianMeasure d N a mass ha hmass) =
      if 4 = k then 24 * (∑ x, f x * gffPositionCovariance d N a mass x z) ^ 4 else 0 :=
    fun k => wickFourth_smeared_site_inner d N a mass ha hmass k f z
  -- Distribute `:φ(f)⁴:` across the interaction polynomial's Wick monomials (bridging the two
  -- `wickMonomial` namespaces via `wickMonomial_eq_root_local`).
  have hdist : (fun ω : Configuration (FinLatticeField d N) =>
        _root_.wickMonomial 4 (gffSmearedCovariance d N a mass f f) (ω f) *
        wickPolynomial P (gffSmearedCovariance d N a mass (Pi.single z 1) (Pi.single z 1))
          (ω (Pi.single z 1))) =
      (fun ω : Configuration (FinLatticeField d N) => (1 / (P.n : ℝ)) *
          (_root_.wickMonomial 4 (gffSmearedCovariance d N a mass f f) (ω f) *
            _root_.wickMonomial P.n
              (gffSmearedCovariance d N a mass (Pi.single z 1) (Pi.single z 1)) (ω (Pi.single z 1)))
        + ∑ m : Fin P.n, P.coeff m *
            (_root_.wickMonomial 4 (gffSmearedCovariance d N a mass f f) (ω f) *
              _root_.wickMonomial (m : ℕ)
                (gffSmearedCovariance d N a mass (Pi.single z 1) (Pi.single z 1))
                (ω (Pi.single z 1)))) := by
    funext ω
    rw [wickPolynomial]
    simp only [wickMonomial_eq_root_local]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun m _ => by ring
  rw [hdist,
      integral_add ((hInt P.n).const_mul (1 / (P.n : ℝ)))
        (integrable_finset_sum _ (fun (m : Fin P.n) _ => (hInt (m : ℕ)).const_mul (P.coeff m))),
      integral_const_mul,
      integral_finset_sum _ (fun (m : Fin P.n) _ => (hInt (m : ℕ)).const_mul (P.coeff m))]
  simp_rw [integral_const_mul, hterm]

/-- **Pure-quartic per-vertex connected four-point.** For `P.n = 4` (the `φ⁴` interaction), the
per-vertex contribution is `6·(C_a f)(z)⁴`: the leading `1/4` Wick coefficient times `4! = 24`, and
all lower Wick monomials vanish by orthogonality. This is `κ = 6`. -/
theorem wickFourth_wickPolynomial_inner_quartic (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (hP : P.n = 4) (f : FinLatticeField d N) (z : FinLatticeSites d N) :
    ∫ ω, _root_.wickMonomial 4 (gffSmearedCovariance d N a mass f f) (ω f) *
          wickPolynomial P (wickConstant d N a mass) (ω (Pi.single z 1))
        ∂(latticeGaussianMeasure d N a mass ha hmass) =
    6 * (∑ x, f x * gffPositionCovariance d N a mass x z) ^ 4 := by
  rw [wickFourth_wickPolynomial_inner d N a mass ha hmass P f z]
  have hsum : (∑ m : Fin P.n, P.coeff m *
      (if 4 = (m : ℕ) then
        24 * (∑ x, f x * gffPositionCovariance d N a mass x z) ^ 4 else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro m _
    rw [if_neg (by have := m.isLt; omega), mul_zero]
  rw [hsum, add_zero, if_pos hP.symm, hP]
  push_cast
  ring

/-- Integrability of `:φ(f)⁴: · wickPolynomial P (wickConstant) (φ_z)` under the lattice GFF — needed
to pull the site integral through the interaction's sum over vertices. -/
theorem integrable_wickFourth_wickPolynomial (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (f : FinLatticeField d N) (z : FinLatticeSites d N) :
    Integrable (fun ω => _root_.wickMonomial 4 (gffSmearedCovariance d N a mass f f) (ω f) *
      wickPolynomial P (wickConstant d N a mass) (ω (Pi.single z 1)))
      (latticeGaussianMeasure d N a mass ha hmass) := by
  rw [← gffSmearedCovariance_single_single_eq_wickConstant d N a mass ha hmass z]
  have hInt : ∀ k : ℕ, Integrable
      (fun ω => _root_.wickMonomial 4 (gffSmearedCovariance d N a mass f f) (ω f) *
        _root_.wickMonomial k (gffSmearedCovariance d N a mass (Pi.single z 1) (Pi.single z 1))
          (ω (Pi.single z 1)))
      (latticeGaussianMeasure d N a mass ha hmass) := by
    intro k
    rw [gffSmearedCovariance_self d N a mass f,
        gffSmearedCovariance_self d N a mass (Pi.single z 1)]
    exact integrable_wickMonomial_smeared_mul d N a mass ha hmass 4 k f (Pi.single z 1)
  have hdist : (fun ω : Configuration (FinLatticeField d N) =>
        _root_.wickMonomial 4 (gffSmearedCovariance d N a mass f f) (ω f) *
        wickPolynomial P (gffSmearedCovariance d N a mass (Pi.single z 1) (Pi.single z 1))
          (ω (Pi.single z 1))) =
      (fun ω : Configuration (FinLatticeField d N) => (1 / (P.n : ℝ)) *
          (_root_.wickMonomial 4 (gffSmearedCovariance d N a mass f f) (ω f) *
            _root_.wickMonomial P.n
              (gffSmearedCovariance d N a mass (Pi.single z 1) (Pi.single z 1)) (ω (Pi.single z 1)))
        + ∑ m : Fin P.n, P.coeff m *
            (_root_.wickMonomial 4 (gffSmearedCovariance d N a mass f f) (ω f) *
              _root_.wickMonomial (m : ℕ)
                (gffSmearedCovariance d N a mass (Pi.single z 1) (Pi.single z 1))
                (ω (Pi.single z 1)))) := by
    funext ω
    rw [wickPolynomial]
    simp only [wickMonomial_eq_root_local]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun m _ => by ring
  rw [hdist]
  exact ((hInt P.n).const_mul _).add
    (integrable_finset_sum _ (fun (m : Fin P.n) _ => (hInt (m : ℕ)).const_mul (P.coeff m)))

/-- **Pure-quartic connected four-point against the full interaction sum (u₄ step 2b).**
`∫ :φ(f)⁴: · (a^d ∑_z wickPolynomial P (wickConstant) (φ_z)) dμ_GFF = 6·a^d·∑_z (C_a f)(z)⁴` for the
`φ⁴` interaction (`P.n = 4`). This is `⟨:φ(f)⁴: · V⟩_free` with `V` the lattice interaction — the
first-order coefficient `−u₄'(0) = 6∫(C_a f)⁴` of the weak-coupling four-point. -/
theorem wickFourth_interaction_inner_quartic (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (hP : P.n = 4) (f : FinLatticeField d N) :
    ∫ ω, _root_.wickMonomial 4 (gffSmearedCovariance d N a mass f f) (ω f) *
          (a ^ d * ∑ z, wickPolynomial P (wickConstant d N a mass) (ω (Pi.single z 1)))
        ∂(latticeGaussianMeasure d N a mass ha hmass) =
    6 * a ^ d * ∑ z, (∑ x, f x * gffPositionCovariance d N a mass x z) ^ 4 := by
  have hcongr : (fun ω : Configuration (FinLatticeField d N) =>
        _root_.wickMonomial 4 (gffSmearedCovariance d N a mass f f) (ω f) *
          (a ^ d * ∑ z, wickPolynomial P (wickConstant d N a mass) (ω (Pi.single z 1)))) =
      (fun ω : Configuration (FinLatticeField d N) => a ^ d *
        ∑ z, (_root_.wickMonomial 4 (gffSmearedCovariance d N a mass f f) (ω f) *
          wickPolynomial P (wickConstant d N a mass) (ω (Pi.single z 1)))) := by
    funext ω
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => by ring
  rw [hcongr, integral_const_mul,
      integral_finset_sum _
        (fun z _ => integrable_wickFourth_wickPolynomial d N a mass ha hmass P f z)]
  simp_rw [wickFourth_wickPolynomial_inner_quartic d N a mass ha hmass P hP f]
  rw [← Finset.mul_sum]
  ring

end Pphi2
