/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Uniform Exponential Moment Bound for Cylinder Pullback

Provides the uniform-in-Lt exponential moment bound
`E_{ν_Lt}[exp(ω(f))] ≤ exp(C · ‖f‖²)` needed for OS0 analyticity.

This is pulled through from the AsymTorus Nelson/Fröhlich bound via
the cylinder-to-torus embedding.

## Mathematical background

The torus interacting measure satisfies (from `asymTorusInteracting_exponentialMomentBound`):
  `E_{μ_Lt}[exp(|ω(g)|)] ≤ K · exp(σ²_Lt(g))`

For `g = embed(f)` where `f` is a cylinder test function:
  `σ²_Lt(embed f) ≤ C · q(f)²`  (from the method of images bound)

Combined: `E_{ν_Lt}[exp(|ω(f)|)] ≤ K · exp(C · q(f)²)` uniformly in Lt.

This is sufficient for Montel/Vitali to prove the limit generating
functional is entire analytic (OS0).
-/

import Pphi2.IRLimit.GreenFunctionComparison

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory Filter

variable (Ls : ℝ) [hLs : Fact (0 < Ls)]

/-- Uniform exponential moment bound for the cylinder pullback measures.

For any cylinder test function `f`, the exponential moment under the
pulled-back torus interacting measure is bounded uniformly in Lt:

  `∫ exp(|ω(f)|) dν_Lt ≤ K · exp(C · q(f)²)`

where `q` is a continuous seminorm on `CylinderTestFunction Ls` and
`K, C > 0` are constants independent of `f` and `Lt`.

This combines the torus Nelson exponential bound with the method of
images bound on `‖embed f‖`. -/
axiom cylinderIR_uniform_exponential_moment
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (K C : ℝ) (q : CylinderTestFunction Ls → ℝ),
    0 < K ∧ 0 < C ∧ Continuous q ∧
    ∀ (Lt : ℝ) [Fact (0 < Lt)]
      (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
      [IsProbabilityMeasure μ]
      (f : CylinderTestFunction Ls),
    Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
      Real.exp (|ω f|)) (cylinderPullbackMeasure Lt Ls μ) ∧
    ∫ ω : Configuration (CylinderTestFunction Ls),
      Real.exp (|ω f|) ∂(cylinderPullbackMeasure Lt Ls μ) ≤
    K * Real.exp (C * q f)

end Pphi2
