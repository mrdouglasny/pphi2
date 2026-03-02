/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Embedded Covariance for the Gaussian Free Field

Defines the continuum-embedded Gaussian measure (pushforward of the lattice GFF
under `latticeEmbedLift`) and the two-point functions that connect lattice
and continuum covariance structures.

## Main definitions

- `gaussianContinuumMeasure` — pushforward of `latticeGaussianMeasure` to S'(ℝ^d)
- `embeddedTwoPoint` — two-point function `∫ ω(f)·ω(g) dν_{GFF,a}`
- `continuumGreenBilinear` — continuum Green's function `∫ f̂(k) ĝ(k) / (|k|²+m²) dk/(2π)^d`

## Mathematical background

The lattice GFF has covariance `(-Δ_a + m²)⁻¹`. When embedded into S'(ℝ^d)
via the Riemann sum embedding `ι_a`, the two-point function becomes:

  `E[Φ_a(f) · Φ_a(g)] = a^{2d} Σ_{x,y} C_a(x,y) f(ax) g(ay)`

This is a Riemann sum that converges to the continuum Green's function
bilinear form `∫ f̂(k) ĝ(k) / (|k|² + m²) dk/(2π)^d`.

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1 (Green's functions)
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I (Free field)
-/

import Pphi2.ContinuumLimit.Embedding

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

variable (d N : ℕ) [NeZero N]

/-! ## Gaussian continuum measure -/

/-- The continuum-embedded Gaussian free field measure.

Pushforward of the lattice GFF `μ_{GFF,a}` under the lattice-to-continuum
embedding `latticeEmbedLift`. This is the free-field analogue of
`continuumMeasure`, which uses the interacting measure.

  `ν_{GFF,a} = (ι̃_a)_* μ_{GFF,a}` -/
def gaussianContinuumMeasure (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Measure (Configuration (ContinuumTestFunction d)) :=
  Measure.map (latticeEmbedLift d N a ha)
    (latticeGaussianMeasure d N a mass ha hmass)

/-- The Gaussian continuum measure is a probability measure. -/
instance gaussianContinuumMeasure_isProbability (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    IsProbabilityMeasure (gaussianContinuumMeasure d N a mass ha hmass) := by
  unfold gaussianContinuumMeasure
  exact Measure.isProbabilityMeasure_map
    (latticeEmbedLift_measurable d N a ha).aemeasurable

/-! ## Two-point functions -/

/-- The embedded two-point function of the lattice GFF.

  `⟨Φ_a(f) · Φ_a(g)⟩_{GFF} = ∫ ω(f) · ω(g) d(ν_{GFF,a})`

This is the covariance of the Gaussian continuum measure evaluated on
test functions f, g ∈ S(ℝ^d). -/
def embeddedTwoPoint (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f g : ContinuumTestFunction d) : ℝ :=
  ∫ ω : Configuration (ContinuumTestFunction d),
    ω f * ω g ∂(gaussianContinuumMeasure d N a mass ha hmass)

/-- The continuum Green's function bilinear form.

  `G(f, g) = ∫ f̂(k) · ĝ(k) / (|k|² + m²) dk / (2π)^d`

This is the two-point function of the continuum massive free field.
It is the inner product in the Sobolev space H⁻¹(ℝ^d), i.e., the
quadratic form of the operator `(-Δ + m²)⁻¹`.

The definition uses the Fourier-space representation, which makes
positivity manifest (the integrand is nonneg). -/
def continuumGreenBilinear (mass : ℝ)
    (f g : ContinuumTestFunction d) : ℝ :=
  (2 * Real.pi) ^ (-(d : ℤ)) *
  ∫ k : EuclideanSpace ℝ (Fin d),
    f.toFun k * g.toFun k / (‖k‖ ^ 2 + mass ^ 2)

/-! ## Algebraic identities connecting the two-point functions -/

/-- The embedded two-point function unfolds to a lattice Riemann sum.

  `⟨Φ_a(f) · Φ_a(g)⟩_{GFF} = a^{2d} Σ_{x,y} C_a(x,y) f(ax) g(ay)`

where `C_a(x,y)` is the lattice Green's function `(-Δ_a + m²)⁻¹(x,y)`.

Proof sketch:
1. Unfold the pushforward integral: `∫ F d(map ι μ) = ∫ F∘ι dμ`.
2. The evaluation `(ι_a φ)(f) = a^d Σ_x φ(x) f(ax)` gives a bilinear
   form in φ.
3. Gaussian integration `∫ φ(x)φ(y) dμ_{GFF} = C_a(x,y)` yields the
   lattice sum. -/
theorem embeddedTwoPoint_eq_latticeSum (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f g : ContinuumTestFunction d) :
    embeddedTwoPoint d N a mass ha hmass f g =
    a ^ (2 * d) * ∑ x : FinLatticeSites d N, ∑ y : FinLatticeSites d N,
      GaussianField.covariance (latticeCovariance d N a mass ha hmass)
        (Pi.single x 1) (Pi.single y 1) *
      evalAtSite d N a f x * evalAtSite d N a g y := by
  -- The pushforward integral unfolds as ∫ (F ∘ ι) dμ_GFF
  -- where F(ω) = ω(f) * ω(g) and ι = latticeEmbedLift.
  -- Then ι(ω)(f) = a^d Σ_x ω(e_x) f(ax), so the product gives the double sum.
  -- The Gaussian integration ∫ ω(e_x) ω(e_y) = C(e_x, e_y) finishes.
  sorry

/-- The embedded two-point function connects to the lattice Gaussian integral.

Rewrites the pushforward integral as an integral over lattice field
configurations, connecting to the spectral covariance. -/
theorem embeddedTwoPoint_eq_covariance (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f g : ContinuumTestFunction d) :
    embeddedTwoPoint d N a mass ha hmass f g =
    ∫ ω : Configuration (FinLatticeField d N),
      (latticeEmbed d N a ha (fun x => ω (Pi.single x 1))) f *
      (latticeEmbed d N a ha (fun x => ω (Pi.single x 1))) g
      ∂(latticeGaussianMeasure d N a mass ha hmass) := by
  unfold embeddedTwoPoint gaussianContinuumMeasure
  rw [integral_map (latticeEmbedLift_measurable d N a ha).aemeasurable
    ((configuration_eval_measurable f).mul (configuration_eval_measurable g)
      |>.aestronglyMeasurable)]
  rfl

end Pphi2

end
