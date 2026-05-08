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
import Pphi2.GeneralResults.LatticeFourierIndexing
import Pphi2.WickOrdering.WickPolynomial

noncomputable section

open GaussianField Real

namespace Pphi2

variable (d N : ℕ) [NeZero N]

/-! ## The Wick ordering constant -/

/-- The Wick ordering constant (**Glimm–Jaffe-aligned**, self-contraction
/ lattice propagator diagonal):

  `c_a = (1/(a^d |Λ|)) Σ_{m=0}^{|Λ|-1} 1 / λ_m  =  (1/L^d) Σ_m 1/λ_m`

where `|Λ| = N^d` is the number of lattice sites, `L = aN` is the
physical box size, and `λ_m` are the eigenvalues of the mass operator
`-Δ_a + m²`.

This equals the GJ-aligned `G_a(x,x) = (a^d Q)^{-1}_{xx}` (the
Glimm–Jaffe-normalised Green's function at coinciding points), which is
the variance of the lattice GFF site value `ω(δ_x)` under the new
`latticeGaussianMeasure`. The `(a^d)⁻¹` Riemann-sum factor is what
distinguishes this from the bare counting-inner-product self-contraction.

In `d = 2` and small `a`, `c_a ≈ (1/(2π)) log(1/(am))` (textbook
log-divergence — the UV divergence Wick ordering removes). -/
def wickConstant (a mass : ℝ) : ℝ :=
  (a^d : ℝ)⁻¹ *
  ((1 / Fintype.card (FinLatticeSites d N) : ℝ) *
    ∑ m ∈ Finset.range (Fintype.card (FinLatticeSites d N)),
      (latticeEigenvalue d N a mass m)⁻¹)

/-- The Wick constant is positive when mass > 0.
Proof: positive `(a^d)⁻¹` factor times an average of positive terms
(`1/λ_m` with `λ_m > 0`). -/
theorem wickConstant_pos (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    0 < wickConstant d N a mass := by
  unfold wickConstant
  have ha_d_pos : (0 : ℝ) < a^d := pow_pos ha d
  refine mul_pos (inv_pos.mpr ha_d_pos) ?_
  apply mul_pos
  · apply div_pos one_pos
    exact_mod_cast Fintype.card_pos
  · apply Finset.sum_pos
    · intro m hm
      exact inv_pos.mpr (latticeEigenvalue_pos d N a mass ha hmass m)
    · exact Finset.nonempty_range_iff.mpr (Fintype.card_pos.ne')

/-- Upper bound on the Wick constant: `c_a ≤ (a^d)⁻¹ · 1/m²`.

Each eigenvalue satisfies `λ_m ≥ m²`, so `1/λ_m ≤ 1/m²`, and the average
of `|Λ|` terms each bounded by `1/m²` gives `(1/|Λ|) Σ ≤ 1/m²`. The
outer `(a^d)⁻¹` factor in the GJ-aligned definition gives the final bound.

**Note**: this bound is *not* uniform in N (since `(a^d)⁻¹ → ∞` as
`a → 0` with `L = aN` fixed). The textbook continuum-limit asymptotic is
the log-divergent `c_∞ ≈ (1/(2π)) log(1/(am))` in 2D. The lemma is
useful for fixed-`a` `MemLp` plumbing where uniformity in N is not needed. -/
theorem wickConstant_le_inv_mass_sq (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    wickConstant d N a mass ≤ (a^d : ℝ)⁻¹ * mass⁻¹ ^ 2 := by
  unfold wickConstant
  have hcard_pos : (0 : ℝ) < Fintype.card (FinLatticeSites d N) :=
    by exact_mod_cast Fintype.card_pos
  have ha_d_pos : (0 : ℝ) < a^d := pow_pos ha d
  -- Each eigenvalue ≥ mass², so each inverse ≤ (mass²)⁻¹ = mass⁻¹²
  have h_each : ∀ m ∈ Finset.range (Fintype.card (FinLatticeSites d N)),
      (latticeEigenvalue d N a mass m)⁻¹ ≤ mass⁻¹ ^ 2 := by
    intro m _
    rw [inv_pow]
    apply inv_anti₀ (sq_pos_of_pos hmass)
    unfold latticeEigenvalue latticeLaplacianEigenvalue
    split_ifs with h
    · have h_sin_nonneg : (0 : ℝ) ≤ ∑ i : Fin d,
          sin (π * ↑(ZMod.val ((Fintype.equivFin (FinLatticeSites d N)).symm ⟨m, h⟩ i)) / ↑N) ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      linarith [mul_nonneg (div_nonneg (by norm_num : (0:ℝ) ≤ 4) (sq_nonneg a)) h_sin_nonneg]
    · linarith
  -- Sum of |Λ| terms each ≤ C gives sum ≤ |Λ| * C
  have h_sum : ∑ m ∈ Finset.range (Fintype.card (FinLatticeSites d N)),
      (latticeEigenvalue d N a mass m)⁻¹ ≤
      ↑(Fintype.card (FinLatticeSites d N)) * (mass⁻¹ ^ 2) := by
    have := Finset.sum_le_card_nsmul _ _ _ h_each
    rwa [Finset.card_range, nsmul_eq_mul] at this
  -- (a^d)⁻¹ · (1/|Λ|) * (|Λ| * C) = (a^d)⁻¹ · C
  have h_inner :
      (1 / ↑(Fintype.card (FinLatticeSites d N))) *
        ∑ m ∈ Finset.range (Fintype.card (FinLatticeSites d N)),
          (latticeEigenvalue d N a mass m)⁻¹
        ≤ mass⁻¹ ^ 2 := by
    calc (1 / ↑(Fintype.card (FinLatticeSites d N))) *
        ∑ m ∈ Finset.range (Fintype.card (FinLatticeSites d N)),
          (latticeEigenvalue d N a mass m)⁻¹
      ≤ (1 / ↑(Fintype.card (FinLatticeSites d N))) *
        (↑(Fintype.card (FinLatticeSites d N)) * (mass⁻¹ ^ 2)) :=
        mul_le_mul_of_nonneg_left h_sum (by positivity)
      _ = mass⁻¹ ^ 2 := by field_simp
  exact mul_le_mul_of_nonneg_left h_inner (le_of_lt (inv_pos.mpr ha_d_pos))

/-- The Wick constant is monotone decreasing in mass: larger mass means
smaller self-contraction. -/
theorem wickConstant_antitone_mass (a : ℝ) (ha : 0 < a)
    (m₁ m₂ : ℝ) (hm₁ : 0 < m₁) (hm₂ : m₁ ≤ m₂) :
    wickConstant d N a m₂ ≤ wickConstant d N a m₁ := by
  unfold wickConstant
  have ha_d_pos : (0 : ℝ) < a^d := pow_pos ha d
  -- Outer (a^d)⁻¹ same on both sides; inner factor (1/|Λ|) Σ also nonneg-monotone
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (inv_pos.mpr ha_d_pos))
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro m _
  -- Eigenvalue is monotone in mass, so inverse is antitone
  apply inv_anti₀ (latticeEigenvalue_pos d N a m₁ ha hm₁ m)
  unfold latticeEigenvalue latticeLaplacianEigenvalue
  split_ifs with h
  · linarith [pow_le_pow_left₀ (le_of_lt hm₁) hm₂ 2]
  · linarith [pow_le_pow_left₀ (le_of_lt hm₁) hm₂ 2]

/-- The Wick constant can be reindexed as an `(a^d)⁻¹`-rescaled average
over coordinatewise 1D Fourier modes in any dimension. -/
theorem wickConstant_eq_latticeEigenvalue1d_family_average (a mass : ℝ) :
    (wickConstant d N a mass : ℝ) =
      (a^d : ℝ)⁻¹ *
        ((1 / Fintype.card (FinLatticeSites d N) : ℝ) *
          ∑ k : (Fin d → Fin N),
            ((∑ i : Fin d, latticeEigenvalue1d N a (k i)) + mass ^ 2)⁻¹) := by
  unfold wickConstant
  rw [← Fin.sum_univ_eq_sum_range]
  congr 2
  exact sum_latticeEigenvalue_eq_sum_latticeEigenvalue1d_family
    (N := N) (d := d) (a := a) (mass := mass) (F := fun t => t⁻¹)

/-- In two dimensions, the Wick constant is `(a^2)⁻¹` times the average of
the product DFT eigenvalue formula coming from the 1D lattice modes. -/
theorem wickConstant_two_eq_dft_eigenvalue_average (a mass : ℝ) :
    (wickConstant 2 N a mass : ℝ) =
      (a^2 : ℝ)⁻¹ *
        ((1 / Fintype.card (FinLatticeSites 2 N) : ℝ) *
          ∑ m₁ : Fin N, ∑ m₂ : Fin N,
            (latticeEigenvalue1d N a m₁ + latticeEigenvalue1d N a m₂ + mass ^ 2)⁻¹) := by
  unfold wickConstant
  rw [← Fin.sum_univ_eq_sum_range]
  congr 2
  exact sum_latticeEigenvalue_two_eq_sum_latticeEigenvalue1d_pair (N := N) (a := a)
    (mass := mass) (F := fun t => t⁻¹)

end Pphi2

end
