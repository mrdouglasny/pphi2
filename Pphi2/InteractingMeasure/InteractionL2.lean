/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.NelsonEstimate.RoughErrorBound

/-!
# Uniform `L²` bound on the interaction (uniform-discharge brick L1)

Toward `⟨V²⟩_{μ_GFF} ≤ C` uniform in the lattice size `N` (`V = interactionFunctional`), which feeds
the `N`-uniform `u₄` remainder (`planning/L1-handoff.md`). The route reuses the Nelson smooth/rough
decomposition rather than computing `a⁴∑_{z,w}C^m` from scratch:

* **bridge** (this file): `∫ V² dμ_GFF = ∫ V_full² dμ_joint`, where `V_full = canonicalFullInteractionJoint`
  is `V` evaluated on the canonical sum field `φ_S + φ_R` — the `F = (·)²` analogue of
  `integral_exp_neg_interaction_sq_eq_canonicalJoint`.

Then `V_full = V_smooth + V_rough` (`canonicalRoughError = full − smooth`), and
`‖V‖_{L²} ≤ ‖V_smooth‖_{L²} + ‖V_rough‖_{L²}`: the rough part is citable
(`canonicalRoughError_leading_l2_sq`, uniform at fixed cutoff `T`), the smooth part needs a
smooth-covariance summability bound (the remaining build).
-/

namespace Pphi2

open MeasureTheory GaussianField

variable (d N : ℕ) [NeZero N] (a mass : ℝ)

/-- **L1 bridge.** The free `L²`-norm² of the interaction equals the joint integral of the full
canonical interaction squared: `∫ V² dμ_GFF = ∫ V_full² dμ_joint`. (The `F = (·)²` analogue of
`integral_exp_neg_interaction_sq_eq_canonicalJoint`; `V_full = canonicalFullInteractionJoint`.) -/
theorem integral_interaction_sq_eq_canonicalJoint
    (P : InteractionPolynomial) (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T) :
    ∫ ω : Configuration (FinLatticeField d N),
        (interactionFunctional d N P a mass ω) ^ 2
        ∂(latticeGaussianMeasure d N a mass ha hmass) =
      ∫ η : CanonicalJoint d N,
        (canonicalFullInteractionJoint d N a mass T P η) ^ 2
        ∂(canonicalJointMeasure d N) := by
  symm
  simpa [canonicalFullInteractionJoint_eq_interactionFunctional
    (d := d) (N := N) (a := a) (mass := mass) T P] using
    (integral_comp_canonicalSumConfig
      (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT
      (F := fun ω : Configuration (FinLatticeField d N) =>
        (interactionFunctional d N P a mass ω) ^ 2)
      ((interactionFunctional_measurable d N P a mass).pow_const 2))

end Pphi2
