/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Wick L² inner-product identity for asym smooth/rough cross terms

Discharge of the per-cross-term L² bound `asymCanonicalCrossTerm_l2_sq_le`
(`AsymRoughErrorVariance.lean:144`) — the only remaining documented sorry
on the `cylinder-isotropic-lattice` branch toward `asymChaosCutoffDecomposition`.

The genuine analytical content is the Wick L² identity

  ∫ (CrossTerm_{k,j})² dη
    = (a²)² · j! · (k−j)! · Σ_{x,y} C_S(x,y)^j · C_R(x,y)^(k−j)

where C_S, C_R are the smooth/rough covariances. This sits on top of three
fully proved upstream identities:

  * `wickPower_two_site_pi_gaussianReal_eq_diag` (FieldDecomposition.lean:3236,
    made public in this session) — the index-polymorphic Wick L² identity over
    a standard-Gaussian product measure.
  * `gaussian-hilbert/HermitePolynomials.hermiteMulti_orthogonality` — the
    bedrock multivariate Hermite orthogonality.
  * The asym FieldDecomposition pushforward identity `pushforward_eq_GFF`.

All asym-side work is mechanical translation that plugs the asym mode
index `Fin Nt × Fin Ns` into the index-polymorphic helpers.

## Structure

  * §1 `asymCanonical{Smooth,Rough}Gamma` defs — linear coefficients such
       that `φ_S(η, x) = Σ_m γ_x(m) · η(m)`.
  * §2 Site-variance identity `Σ_m γ_x(m)² = asymSmoothWickConstant` via
       translation invariance of the smooth diagonal (mirrors the proved
       `wickConstantAsym_eq_variance`).
  * §3 `asymCanonicalSmoothCovariance` def and the cross-pair identity
       `Σ_m γ_x(m) · γ_y(m) = asymCanonicalSmoothCovariance(x, y)`.
  * §4 The 6 `_two_site_marginal_*` lemmas (thin wrappers around the public
       generic helpers).
  * §5 The cross-term L² covSum identity.
  * §6 `|asymCanonicalSmoothCovariance| ≤ asymSmoothWickConstant`.
  * §7 Unified rough-covariance row-sum (case-split p = 1, 2, ≥ 3).
  * §8 Discharge `asymCanonicalCrossTerm_l2_sq_le`.
-/

import Pphi2.NelsonEstimate.AsymRoughCovarianceHigherP
import Pphi2.AsymTorus.AsymWickVariance
import Pphi2.NelsonEstimate.WickBinomial

noncomputable section

open GaussianField MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Pphi2

/-! ## §1 Asym gamma coefficients

`γ_x(m) = (√(a²))⁻¹ · asymCanonicalSmoothModeCoeff(x, m)` (smooth side),
and the rough analog. This is exactly the coefficient pulled out of the
linear `φ_S(η_S, x) = Σ_m γ_x(m) · η_S(m)` form. -/

/-- Smooth gamma coefficient on the rectangular lattice. -/
def asymCanonicalSmoothGamma (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (x : AsymLatticeSites Nt Ns)
    (m : AsymCanonicalMode Nt Ns) : ℝ :=
  (Real.sqrt (a ^ 2))⁻¹ * asymCanonicalSmoothModeCoeff Nt Ns a mass T x m

/-- Rough gamma coefficient on the rectangular lattice. -/
def asymCanonicalRoughGamma (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (x : AsymLatticeSites Nt Ns)
    (m : AsymCanonicalMode Nt Ns) : ℝ :=
  (Real.sqrt (a ^ 2))⁻¹ * asymCanonicalRoughModeCoeff Nt Ns a mass T x m

/-- The smooth field slice as a linear combination of the first-factor std
Gaussian coordinates, with coefficients `asymCanonicalSmoothGamma`. -/
theorem asymCanonicalSmoothFieldFunctionOfFst_eq_sum_gamma
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (ηS : AsymCanonicalMode Nt Ns → ℝ)
    (x : AsymLatticeSites Nt Ns) :
    asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS x =
      ∑ m : AsymCanonicalMode Nt Ns,
        asymCanonicalSmoothGamma Nt Ns a mass T x m * ηS m := by
  unfold asymCanonicalSmoothFieldFunctionOfFst asymCanonicalSmoothGamma
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro m hm
  ring

/-- The rough field slice as a linear combination of the second-factor std
Gaussian coordinates, with coefficients `asymCanonicalRoughGamma`. -/
theorem asymCanonicalRoughFieldFunctionOfSnd_eq_sum_gamma
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (ηR : AsymCanonicalMode Nt Ns → ℝ)
    (x : AsymLatticeSites Nt Ns) :
    asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR x =
      ∑ m : AsymCanonicalMode Nt Ns,
        asymCanonicalRoughGamma Nt Ns a mass T x m * ηR m := by
  unfold asymCanonicalRoughFieldFunctionOfSnd asymCanonicalRoughGamma
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro m hm
  ring

end Pphi2

end
