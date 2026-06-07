/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.TorusContinuumLimit.TorusPropagatorConvergence
import Pphi2.InteractingMeasure.LeadingTerm

/-!
# Pointwise covariance mass decay (uniform-discharge leaf `L6F`, Route 1)

`|gffPositionCovariance x y| ≤ (a^d)⁻¹·mass⁻²`: the lattice propagator decays like `mass⁻²`
uniformly in the sites. From the diagonal bound (`lattice_second_moment_le_mass_inv` at `δ_z`,
`∑(δ_z)² = 1`, identifying `∫(ωδ_z)² = ⟨Tδ_z,Tδ_z⟩`) and Cauchy–Schwarz
`|⟨Tδ_x,Tδ_y⟩| ≤ ‖Tδ_x‖‖Tδ_y‖` (AM–GM). The pointwise input for mass-grading the interaction
variance `∫V²` (a covariance double-sum), which in turn grades all `∫V^{2m}` and hence the
`u₄''` bound `K(mass)` — see `planning/L6F-mass-coupling-plan.md`.
-/

namespace Pphi2

open MeasureTheory GaussianField

/-- **Pointwise covariance mass decay** `|gffPositionCovariance x y| ≤ (a²)⁻¹·mass⁻²`. -/
theorem gffPositionCovariance_abs_le_mass_inv (N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (x y : FinLatticeSites 2 N) :
    |gffPositionCovariance 2 N a mass x y| ≤ (a ^ 2)⁻¹ * mass⁻¹ ^ 2 := by
  have hdiag : ∀ z : FinLatticeSites 2 N,
      @inner ℝ _ _ (latticeCovarianceGJ 2 N a mass ha hmass (Pi.single z (1:ℝ) : FinLatticeField 2 N))
        (latticeCovarianceGJ 2 N a mass ha hmass (Pi.single z (1:ℝ) : FinLatticeField 2 N)) ≤ (a ^ 2)⁻¹ * mass⁻¹ ^ 2 := by
    intro z
    have h := lattice_second_moment_le_mass_inv N a mass ha hmass (Pi.single z (1:ℝ) : FinLatticeField 2 N)
    have hsum : ∑ w : FinLatticeSites 2 N, (Pi.single z (1:ℝ) : FinLatticeField 2 N) w ^ 2 = 1 := by
      simp [Pi.single_apply, Finset.sum_ite_eq']
    rw [hsum, mul_one] at h
    rw [← second_moment_eq_covariance (latticeCovarianceGJ 2 N a mass ha hmass) (Pi.single z (1:ℝ))]
    exact h
  rw [gffPositionCovariance_eq_covarianceGJ 2 N a mass ha hmass x y]
  show |@inner ℝ _ _ (latticeCovarianceGJ 2 N a mass ha hmass (Pi.single x (1:ℝ) : FinLatticeField 2 N))
      (latticeCovarianceGJ 2 N a mass ha hmass (Pi.single y (1:ℝ) : FinLatticeField 2 N))| ≤ (a ^ 2)⁻¹ * mass⁻¹ ^ 2
  refine le_trans (abs_real_inner_le_norm _ _) ?_
  have hx := hdiag x
  have hy := hdiag y
  rw [real_inner_self_eq_norm_sq] at hx hy
  nlinarith [norm_nonneg (latticeCovarianceGJ 2 N a mass ha hmass (Pi.single x (1:ℝ) : FinLatticeField 2 N)),
    norm_nonneg (latticeCovarianceGJ 2 N a mass ha hmass (Pi.single y (1:ℝ) : FinLatticeField 2 N)), hx, hy,
    sq_nonneg (‖latticeCovarianceGJ 2 N a mass ha hmass (Pi.single x (1:ℝ) : FinLatticeField 2 N)‖
      - ‖latticeCovarianceGJ 2 N a mass ha hmass (Pi.single y (1:ℝ) : FinLatticeField 2 N)‖)]

end Pphi2
