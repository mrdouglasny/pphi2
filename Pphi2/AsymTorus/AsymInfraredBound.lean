/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# FSS infrared bound and the high-branch variance comparison (B2 S1)

The Fröhlich–Simon–Spencer infrared bound in integrated quadratic form (`planning/
b2-route-a-statements.md`, §S1), together with its first consumer: the fully proved
high-branch comparison `asymHighModes_variance_le_freeVariance`, bounding the interacting
variance of a spectrally-high mode projection by `(1 + m²/κ²)` times its free variance.

## Main statements

- `fss_infrared_quadratic` (**axiom**, vetted) — on the zero-mode complement the interacting
  second moment is dominated by the massless free quadratic form, uniformly in `(a, Nt, Ns)`
  for quartic `P`.
- `asymHighModes_variance_le_freeVariance` (**theorem**) — for a mode set `S` with
  `mass² + κ² ≤ λ_k` on `S`, the interacting variance of `asymModeProj S G` is at most
  `(1 + mass²/κ²)` times its free variance.

## Supporting proved lemmas

- `massOperatorAsym_const` — the lattice Laplacian stencil kills constants, so constants are
  `mass²`-eigenvectors of `massOperatorAsym`.
- `sum_massEigenvectorBasisAsym_eq_zero_of_ne` — eigenvectors with eigenvalue `≠ mass²` sum
  to zero over the lattice (self-adjointness pairing against the constant field).
- `sum_asymModeProj_eq_zero` — spectrally-high mode projections lie in the zero-mode
  complement, unlocking `fss_infrared_quadratic` for the high branch.
-/

import Pphi2.AsymTorus.AsymFreeSpectral

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

/-! ## Constants are mass-squared eigenvectors -/

/-- The nearest-neighbor Laplacian stencil kills constant fields, so the constant field is a
`mass²`-eigenvector of the mass operator: `(-Δ_a + m²)(c·1) = m²·(c·1)`. -/
theorem massOperatorAsym_const (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass c : ℝ) :
    massOperatorAsym Nt Ns a mass (fun _ => c) = fun _ => mass ^ 2 * c := by
  funext x
  simp only [massOperatorAsym, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul]
  have hlap : (finiteLaplacianAsym Nt Ns a fun _ => c) x = 0 := by
    change finiteLaplacianAsymFun Nt Ns a (fun _ => c) x = 0
    simp only [finiteLaplacianAsymFun]
    ring
  rw [hlap]
  ring

/-! ## Nonconstant eigenvectors sum to zero -/

/-- An eigenvector of the asymmetric mass operator whose eigenvalue differs from `mass²` sums
to zero over the lattice. Pairing the eigencoefficient identity against the constant field `1`
(a `mass²`-eigenvector by `massOperatorAsym_const`) gives `(λ_k - mass²)·∑_x e_k(x) = 0`. -/
theorem sum_massEigenvectorBasisAsym_eq_zero_of_ne (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (k : AsymLatticeSites Nt Ns)
    (hk : massEigenvaluesAsym Nt Ns a mass k ≠ mass ^ 2) :
    ∑ x : AsymLatticeSites Nt Ns,
      (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x = 0 := by
  have h := massOperatorAsym_eigenCoeff_eq_eigenvalues_mul_eigenCoeff Nt Ns a mass
    (fun _ => (1 : ℝ)) k
  rw [massOperatorAsym_const Nt Ns a mass 1] at h
  simp only [mul_one] at h
  rw [← Finset.sum_mul] at h
  have hfactor : (massEigenvaluesAsym Nt Ns a mass k - mass ^ 2) *
      ∑ x : AsymLatticeSites Nt Ns,
        (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x = 0 := by
    rw [sub_mul, sub_eq_zero, ← h]
    ring
  exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hk)

/-- **Zero-mode complement**: the spectral projection onto a set of modes whose eigenvalues
are uniformly above `mass²` sums to zero over the lattice, hence lies in the domain of the
integrated infrared bound. -/
theorem sum_asymModeProj_eq_zero (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass κ : ℝ) (hκ : 0 < κ) (S : Finset (AsymLatticeSites Nt Ns))
    (hS : ∀ k ∈ S, mass ^ 2 + κ ^ 2 ≤ massEigenvaluesAsym Nt Ns a mass k)
    (G : AsymLatticeField Nt Ns) :
    ∑ x : AsymLatticeSites Nt Ns, asymModeProj Nt Ns a mass S G x = 0 := by
  unfold asymModeProj
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [← Finset.mul_sum,
    sum_massEigenvectorBasisAsym_eq_zero_of_ne Nt Ns a mass k ?_, mul_zero]
  have hgap := hS k hk
  have : mass ^ 2 < massEigenvaluesAsym Nt Ns a mass k :=
    lt_of_lt_of_le (by nlinarith) hgap
  exact ne_of_gt this

/-! ## The FSS infrared bound (axiom) -/

/-- **Fröhlich–Simon–Spencer infrared bound / Gaussian domination, integrated form.**

On the zero-mode complement (`∑ x, h x = 0`), the interacting second moment is dominated by
the massless free quadratic form, uniformly in `(a, Nt, Ns)` for quartic `P`. The
massless symbol is written `massEigenvaluesAsym … k − mass²` from the mass-`m` eigendata
(the operators differ by `mass² • 1`, so the eigenbasis is shared); the `if` guard makes the
zero mode's exclusion explicit rather than relying on `(0 : ℝ)⁻¹ = 0`.

    Reference: Fröhlich–Simon–Spencer, Comm. Math. Phys. 50 (1976) 79–95; Simon *P(φ)₂*;
    Glimm–Jaffe. Vetted: Gemini 3.1-pro 2026-07-12 — `c₀ = 1` exact in this GJ normalization
    (kinetic action `½⟨φ,(−Δ_unscaled)φ⟩`, β = ½; mass and Wick terms live in the single-site
    factor and never enter the denominator). See planning/b2-route-a-statements.md §S1.
    Strategy: Gaussian domination `Z[h] ≤ Z[0]·exp(½⟨h,(−Δ)⁻¹h⟩)` via lattice RP over the
    kinetic bonds, then the `t²`-expansion at the Z₂-even measure. (NOT VERIFIED — vetted
    statement; discharge shares the Griffiths–Simon machinery with Layer A.) -/
axiom fss_infrared_quadratic
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (hP : P.n = 4)
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (h : AsymLatticeField Nt Ns) (hzero : ∑ x, h x = 0) :
    ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω h) ^ 2 ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ≤
      (a ^ 2)⁻¹ * ∑ k, (if mass ^ 2 < massEigenvaluesAsym Nt Ns a mass k
        then (massEigenvaluesAsym Nt Ns a mass k - mass ^ 2)⁻¹ *
          asymModeCoeff Nt Ns a mass k h ^ 2
        else 0)

/-! ## The high-branch comparison (S1's consumer) -/

/-- Denominator comparison for the high branch: if `mass² + κ² ≤ lam` then the massless
inverse symbol is controlled by the massive one, `(lam - mass²)⁻¹ ≤ (1 + mass²/κ²)·lam⁻¹`. -/
theorem inv_sub_le_one_add_div_mul_inv {lam mass κ : ℝ} (hκ : 0 < κ)
    (hgap : mass ^ 2 + κ ^ 2 ≤ lam) :
    (lam - mass ^ 2)⁻¹ ≤ (1 + mass ^ 2 / κ ^ 2) * lam⁻¹ := by
  have hκ2 : 0 < κ ^ 2 := by positivity
  have hsub : 0 < lam - mass ^ 2 := by nlinarith [sq_nonneg mass]
  have hlam : 0 < lam := by nlinarith [sq_nonneg mass]
  have expand : (1 + mass ^ 2 / κ ^ 2) * lam⁻¹ = (κ ^ 2 + mass ^ 2) / (κ ^ 2 * lam) := by
    field_simp
  rw [expand, inv_eq_one_div, div_le_div_iff₀ hsub (by positivity)]
  nlinarith [mul_nonneg (sq_nonneg mass) (sub_nonneg.mpr hgap)]

/-- **High-branch variance comparison.** For a mode set `S` with all eigenvalues uniformly
above `mass² + κ²`, the interacting variance of the spectral projection `asymModeProj S G`
is at most `(1 + mass²/κ²)` times its free variance. Consumes `fss_infrared_quadratic` at
`P.n = 4` and `h = asymModeProj S G` (in the zero-mode complement by
`sum_asymModeProj_eq_zero`), restricts
the massless mode sum to `S` via `asymModeCoeff_proj`, applies the denominator comparison
mode-by-mode, and identifies the free side by `asymFreeVariance_eq_sum_modeCoeff_sq`. -/
theorem asymHighModes_variance_le_freeVariance
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (hP : P.n = 4)
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (κ : ℝ) (hκ : 0 < κ)
    (S : Finset (AsymLatticeSites Nt Ns))
    (hS : ∀ k ∈ S, mass ^ 2 + κ ^ 2 ≤ massEigenvaluesAsym Nt Ns a mass k)
    (G : AsymLatticeField Nt Ns) :
    ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω (asymModeProj Nt Ns a mass S G)) ^ 2
        ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ≤
      (1 + mass ^ 2 / κ ^ 2) *
        ∫ ω : Configuration (AsymLatticeField Nt Ns),
          (ω (asymModeProj Nt Ns a mass S G)) ^ 2
          ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
  set h : AsymLatticeField Nt Ns := asymModeProj Nt Ns a mass S G with hh
  have hzero : ∑ x, h x = 0 := sum_asymModeProj_eq_zero Nt Ns a mass κ hκ S hS G
  have hfss := fss_infrared_quadratic Nt Ns P hP a mass ha hmass h hzero
  have ha2 : (0 : ℝ) ≤ (a ^ 2)⁻¹ := by positivity
  have hC : (0 : ℝ) ≤ 1 + mass ^ 2 / κ ^ 2 := by positivity
  -- Mode-by-mode comparison of the massless sum against the massive (free) sum.
  have hsum : ∑ k, (if mass ^ 2 < massEigenvaluesAsym Nt Ns a mass k
        then (massEigenvaluesAsym Nt Ns a mass k - mass ^ 2)⁻¹ *
          asymModeCoeff Nt Ns a mass k h ^ 2
        else 0) ≤
      (1 + mass ^ 2 / κ ^ 2) * ∑ k, (massEigenvaluesAsym Nt Ns a mass k)⁻¹ *
        asymModeCoeff Nt Ns a mass k h ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [hh, asymModeCoeff_proj]
    by_cases hkS : k ∈ S
    · simp only [hkS, if_true]
      have hgap := hS k hkS
      have hlt : mass ^ 2 < massEigenvaluesAsym Nt Ns a mass k := by nlinarith
      rw [if_pos hlt, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (inv_sub_le_one_add_div_mul_inv hκ hgap) (sq_nonneg _)
    · simp [hkS]
  calc
    ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω h) ^ 2 ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass)
      ≤ (a ^ 2)⁻¹ * ∑ k, (if mass ^ 2 < massEigenvaluesAsym Nt Ns a mass k
          then (massEigenvaluesAsym Nt Ns a mass k - mass ^ 2)⁻¹ *
            asymModeCoeff Nt Ns a mass k h ^ 2
          else 0) := hfss
    _ ≤ (a ^ 2)⁻¹ * ((1 + mass ^ 2 / κ ^ 2) * ∑ k, (massEigenvaluesAsym Nt Ns a mass k)⁻¹ *
          asymModeCoeff Nt Ns a mass k h ^ 2) := mul_le_mul_of_nonneg_left hsum ha2
    _ = (1 + mass ^ 2 / κ ^ 2) * ((a ^ 2)⁻¹ * ∑ k, (massEigenvaluesAsym Nt Ns a mass k)⁻¹ *
          asymModeCoeff Nt Ns a mass k h ^ 2) := by ring
    _ = (1 + mass ^ 2 / κ ^ 2) *
          ∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω h) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
        rw [asymFreeVariance_eq_sum_modeCoeff_sq Nt Ns a mass ha hmass h]

end Pphi2

end
