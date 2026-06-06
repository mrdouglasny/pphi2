/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.ContinuumLimit.Hypercontractivity
import GaussianField.WickMultivariate

/-!
# `wickConstant` ↔ eigenbasis position covariance

Bridges pphi2's interaction Wick constant `wickConstant` (the operator-form lattice variance, equal to
`⟨T_GJ δ_x, T_GJ δ_x⟩` by `wickConstant_eq_variance`) to GaussianField's eigenbasis position covariance
`gffPositionCovariance x x` that the smeared Wick kernel is stated in. Both equal `Var ω(δ_x)`; the
identification is `GaussianField.gffPositionCovariance_eq_covarianceGJ` plus
`finLatticeDelta x = Pi.single x 1`.

This is step (2a) of the `u₄` weak-coupling discharge: it lets the per-vertex atom
`wickFourth_smeared_vertex_inner` (stated in the eigenbasis) plug into the actual interaction `V`,
whose site Wick monomials `:φ(δ_z)⁴:` use `wickConstant`.
-/

namespace Pphi2

open GaussianField

variable (d N : ℕ) [NeZero N]

/-- `finLatticeDelta x = Pi.single x 1` (both are the indicator at site `x`). -/
lemma finLatticeDelta_eq_single (x : FinLatticeSites d N) :
    finLatticeDelta d N x = Pi.single x (1 : ℝ) := by
  funext y
  simp [finLatticeDelta, Pi.single_apply]

/-- **The interaction Wick constant equals the eigenbasis site variance.**
`wickConstant = gffPositionCovariance x x` for every site `x` — both are `Var ω(δ_x)`. Connects the
operator-form Wick constant used by the interaction `V` to the eigenbasis covariance of the smeared
Wick kernel. -/
theorem wickConstant_eq_gffPositionCovariance (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (x : FinLatticeSites d N) :
    wickConstant d N a mass = gffPositionCovariance d N a mass x x := by
  rw [gffPositionCovariance_eq_covarianceGJ d N a mass ha hmass x x,
      wickConstant_eq_variance d N a mass ha hmass x,
      finLatticeDelta_eq_single d N x]
  rfl

/-- The diagonal smeared covariance at a single site is the position covariance:
`gffSmearedCovariance (δ_z) (δ_z) = gffPositionCovariance z z`. -/
lemma gffSmearedCovariance_single_single (a mass : ℝ) (z : FinLatticeSites d N) :
    gffSmearedCovariance d N a mass (Pi.single z (1 : ℝ)) (Pi.single z (1 : ℝ)) =
    gffPositionCovariance d N a mass z z := by
  rw [gffSmearedCovariance_single_right d N a mass (Pi.single z 1) z]
  simp [Pi.single_apply, ite_mul, Finset.sum_ite_eq']

/-- **The site Wick monomial's constant matches the kernel's site covariance.**
`gffSmearedCovariance (δ_z)(δ_z) = wickConstant` — so the interaction `V`'s site Wick monomials
`:φ(δ_z)ᵐ:_{wickConstant}` are exactly the site factors in the per-vertex inner product
`wickFourth_smeared_site_inner`. -/
theorem gffSmearedCovariance_single_single_eq_wickConstant
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (z : FinLatticeSites d N) :
    gffSmearedCovariance d N a mass (Pi.single z (1 : ℝ)) (Pi.single z (1 : ℝ)) =
    wickConstant d N a mass := by
  rw [gffSmearedCovariance_single_single d N a mass z,
    ← wickConstant_eq_gffPositionCovariance d N a mass ha hmass z]

end Pphi2
