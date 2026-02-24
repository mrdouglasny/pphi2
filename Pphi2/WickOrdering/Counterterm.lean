/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Wick Ordering Counterterm

The Wick ordering constant `c_a = G_a(0,0)` — the diagonal of the lattice
Green's function. This is the variance parameter for Wick ordering on the
lattice, and the ONLY UV counterterm needed for P(Φ)₂ (super-renormalizability).

## Main definitions

- `wickConstant d N a mass` — the self-contraction `c_a = (1/|Λ|) Σ_k 1/λ_k`

## Mathematical background

The lattice propagator (Green's function) at coinciding points is:
  `G_a(x,x) = (1/|Λ_a|) Σ_k 1/λ_k`

where `λ_k = (4/a²) Σᵢ sin²(πkᵢ/N) + m²` are the eigenvalues of `-Δ_a + m²`.

This is independent of x by translation invariance of the periodic lattice.

As `a → 0` (with N = L/a → ∞):
  `c_a ~ (1/2π) log(1/a) + O(1)`

This logarithmic divergence is the UV divergence that Wick ordering removes.

## References

- Simon, *The P(φ)₂ Euclidean QFT*, §I.4 (Wick ordering counterterm)
- Glimm-Jaffe, *Quantum Physics*, §8.6
-/

import Lattice.Covariance
import Pphi2.WickOrdering.WickPolynomial

noncomputable section

open GaussianField Real

namespace Pphi2

variable (d N : ℕ) [NeZero N]

/-! ## The Wick ordering constant -/

/-- The Wick ordering constant (self-contraction / lattice propagator diagonal):

  `c_a = (1/|Λ|) Σ_{m=0}^{|Λ|-1} 1 / λ_m`

where `|Λ| = N^d` is the number of lattice sites and `λ_m` are the eigenvalues
of the mass operator `-Δ_a + m²`.

This equals `G_a(x,x)` (the Green's function at coinciding points), which is
independent of x by translation invariance. -/
def wickConstant (a mass : ℝ) : ℝ :=
  (1 / Fintype.card (FinLatticeSites d N) : ℝ) *
  ∑ m ∈ Finset.range (Fintype.card (FinLatticeSites d N)),
    (latticeEigenvalue d N a mass m)⁻¹

/-- The Wick constant is positive when mass > 0.
Proof: it's a sum of positive terms (1/λ_m with λ_m > 0). -/
theorem wickConstant_pos (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    0 < wickConstant d N a mass := by
  unfold wickConstant
  apply mul_pos
  · apply div_pos one_pos
    exact_mod_cast Fintype.card_pos
  · apply Finset.sum_pos
    · intro m hm
      exact inv_pos.mpr (latticeEigenvalue_pos d N a mass ha hmass m)
    · exact Finset.nonempty_range_iff.mpr (Fintype.card_pos.ne')

/-- Upper bound on the Wick constant: `c_a ≤ 1/m²`.

Each eigenvalue satisfies `λ_m ≥ m²`, so `1/λ_m ≤ 1/m²`, and the average
of |Λ| terms each bounded by 1/m² gives c_a ≤ 1/m². -/
theorem wickConstant_le_inv_mass_sq (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    wickConstant d N a mass ≤ mass⁻¹ ^ 2 := by
  unfold wickConstant
  have hcard_pos : (0 : ℝ) < Fintype.card (FinLatticeSites d N) :=
    by exact_mod_cast Fintype.card_pos
  -- Each eigenvalue ≥ mass², so each inverse ≤ (mass²)⁻¹ = mass⁻¹²
  have h_each : ∀ m ∈ Finset.range (Fintype.card (FinLatticeSites d N)),
      (latticeEigenvalue d N a mass m)⁻¹ ≤ mass⁻¹ ^ 2 := by
    intro m _
    rw [inv_pow]
    apply inv_anti₀ (sq_pos_of_pos hmass)
    unfold latticeEigenvalue
    split_ifs with h
    · have h_sin_nonneg : (0 : ℝ) ≤ ∑ i : Fin d,
          sin (π * ↑((Fintype.equivFin (FinLatticeSites d N)).symm ⟨m, h⟩ i) / ↑N) ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      linarith [mul_nonneg (div_nonneg (by norm_num : (0:ℝ) ≤ 4) (sq_nonneg a)) h_sin_nonneg]
    · exact le_refl _
  -- Sum of |Λ| terms each ≤ C gives sum ≤ |Λ| * C
  have h_sum : ∑ m ∈ Finset.range (Fintype.card (FinLatticeSites d N)),
      (latticeEigenvalue d N a mass m)⁻¹ ≤
      ↑(Fintype.card (FinLatticeSites d N)) * (mass⁻¹ ^ 2) := by
    have := Finset.sum_le_card_nsmul _ _ _ h_each
    rwa [Finset.card_range, nsmul_eq_mul] at this
  -- (1/|Λ|) * (|Λ| * C) = C
  calc (1 / ↑(Fintype.card (FinLatticeSites d N))) *
      ∑ m ∈ Finset.range (Fintype.card (FinLatticeSites d N)),
        (latticeEigenvalue d N a mass m)⁻¹
    ≤ (1 / ↑(Fintype.card (FinLatticeSites d N))) *
      (↑(Fintype.card (FinLatticeSites d N)) * (mass⁻¹ ^ 2)) :=
      mul_le_mul_of_nonneg_left h_sum (by positivity)
    _ = mass⁻¹ ^ 2 := by field_simp

/-- The Wick constant is monotone decreasing in mass: larger mass means
smaller self-contraction. -/
theorem wickConstant_antitone_mass (a : ℝ) (ha : 0 < a)
    (m₁ m₂ : ℝ) (hm₁ : 0 < m₁) (hm₂ : m₁ ≤ m₂) :
    wickConstant d N a m₂ ≤ wickConstant d N a m₁ := by
  unfold wickConstant
  -- Same prefactor (1/|Λ|), so suffices to show sum decreases
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro m _
  -- Eigenvalue is monotone in mass, so inverse is antitone
  apply inv_anti₀ (latticeEigenvalue_pos d N a m₁ ha hm₁ m)
  unfold latticeEigenvalue
  split_ifs with h
  · -- (4/a²) Σ sin² + m₁² ≤ (4/a²) Σ sin² + m₂²
    linarith [pow_le_pow_left₀ (le_of_lt hm₁) hm₂ 2]
  · -- m₁² ≤ m₂²
    exact pow_le_pow_left₀ (le_of_lt hm₁) hm₂ 2

/-! ## Asymptotics

As a → 0 with N = L/a, the Wick constant diverges logarithmically.
This is the ONLY UV divergence in P(Φ)₂ (super-renormalizability). -/

/-- The Wick constant diverges as `(1/2π) log(1/a)` in d=2.

More precisely, for d = 2 and N = ⌊L/a⌋:
  `c_a = (1/2π) log(1/a) + O(1)`

The proof uses Euler-Maclaurin summation to compare the lattice sum
`Σ_k 1/(k² + m²)` with the integral `∫ dk/(k² + m²) = (1/2π) log(Λ²/m²)`.

This is axiomatized for now; the upper bound `wickConstant_le_inv_mass_sq`
already provides a (crude) uniform bound. -/
axiom wickConstant_log_divergence (mass : ℝ) (hmass : 0 < mass) :
    ∃ C : ℝ, ∀ (N : ℕ) [NeZero N] (a : ℝ), 0 < a → a ≤ 1 →
    |wickConstant 2 N a mass - (1 / (2 * π)) * Real.log (1 / a)| ≤ C

end Pphi2

end
