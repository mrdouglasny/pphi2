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

/-- The lattice Green bilinear form evaluated on the discretizations of
continuum test functions. This is the spectral representation of the embedded
two-point function. -/
def latticeGreenBilinear (a mass : ℝ)
    (f g : ContinuumTestFunction d) : ℝ :=
  ∑ k : FinLatticeSites d N,
    (massEigenvalues d N a mass k)⁻¹ *
    (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
      latticeTestField d N a f x) *
    (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
      latticeTestField d N a g x)

/-! ## Algebraic identities connecting the two-point functions -/

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

/-- The embedded two-point function is the lattice Gaussian cross moment of the
induced lattice test fields. -/
theorem embeddedTwoPoint_eq_lattice_cross_moment (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f g : ContinuumTestFunction d) :
    embeddedTwoPoint d N a mass ha hmass f g =
    ∫ ω : Configuration (FinLatticeField d N),
      ω (latticeTestField d N a f) * ω (latticeTestField d N a g)
      ∂(latticeGaussianMeasure d N a mass ha hmass) := by
  unfold embeddedTwoPoint gaussianContinuumMeasure
  rw [integral_map (latticeEmbedLift_measurable d N a ha).aemeasurable
    (((configuration_eval_measurable f).mul
      (configuration_eval_measurable g)).aestronglyMeasurable)]
  congr 1
  ext ω
  rw [latticeEmbedLift_eval_eq d N a ha f ω, latticeEmbedLift_eval_eq d N a ha g ω]

theorem embeddedTwoPoint_eq_latticeSum (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f g : ContinuumTestFunction d) :
    embeddedTwoPoint d N a mass ha hmass f g =
    a ^ (2 * d) * ∑ x : FinLatticeSites d N, ∑ y : FinLatticeSites d N,
      GaussianField.covariance (latticeCovariance d N a mass ha hmass)
        (Pi.single x 1) (Pi.single y 1) *
      evalAtSite d N a f x * evalAtSite d N a g y := by
  -- Step 1: Rewrite as integral over lattice configurations
  rw [embeddedTwoPoint_eq_covariance]
  -- Step 2: Unfold latticeEmbed to latticeEmbedEval
  simp only [latticeEmbed_eval, latticeEmbedEval]
  -- Step 3: Rewrite integrand to factor out a^{2d} and expand product of sums
  set μ := latticeGaussianMeasure d N a mass ha hmass
  set T := latticeCovariance d N a mass ha hmass
  -- Abbreviate: each factor is a^d * Σ_x ω(e_x) * f(ax)
  -- Their product = a^{2d} * (Σ_x ω(e_x) f(ax)) * (Σ_y ω(e_y) g(ay))
  --              = a^{2d} * Σ_x Σ_y ω(e_x) ω(e_y) f(ax) g(ay)
  have hrewrite : ∀ ω : Configuration (FinLatticeField d N),
      (a ^ d * ∑ x, ω (Pi.single x 1) * evalAtSite d N a f x) *
      (a ^ d * ∑ y, ω (Pi.single y 1) * evalAtSite d N a g y) =
      a ^ (2 * d) * ∑ x, ∑ y,
        ω (Pi.single x 1) * ω (Pi.single y 1) *
        evalAtSite d N a f x * evalAtSite d N a g y := by
    intro ω
    -- (a^d * Σf) * (a^d * Σg) = a^{2d} * (Σf) * (Σg) = a^{2d} * Σ_{x,y} f_x * g_y
    have hpow : a ^ d * a ^ d = a ^ (2 * d) := by rw [← pow_add]; ring_nf
    rw [show (a ^ d * ∑ x, ω (Pi.single x 1) * evalAtSite d N a f x) *
        (a ^ d * ∑ y, ω (Pi.single y 1) * evalAtSite d N a g y) =
        a ^ d * a ^ d *
        ((∑ x, ω (Pi.single x 1) * evalAtSite d N a f x) *
         (∑ y, ω (Pi.single y 1) * evalAtSite d N a g y))
      from by ring]
    rw [hpow, Finset.sum_mul_sum]
    congr 1
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _
    ring
  simp_rw [hrewrite]
  -- Step 4: Pull constant a^{2d} and finite sums out of the integral
  rw [integral_const_mul]
  congr 1
  -- Now need: ∫ Σ_x Σ_y ... = Σ_x Σ_y ∫ ...
  -- Integrability of each summand
  have hint : ∀ (x y : FinLatticeSites d N),
      Integrable (fun ω : Configuration (FinLatticeField d N) =>
        ω (Pi.single x 1) * ω (Pi.single y 1) *
        evalAtSite d N a f x * evalAtSite d N a g y) μ := by
    intro x y
    have h1 := pairing_product_integrable T (Pi.single x 1) (Pi.single y 1)
    exact (h1.mul_const _).mul_const _
  -- Swap integral and outer sum
  rw [integral_finset_sum _ (fun x _ =>
    integrable_finset_sum _ (fun y _ => hint x y))]
  congr 1; ext x
  -- Swap integral and inner sum
  rw [integral_finset_sum _ (fun y _ => hint x y)]
  congr 1; ext y
  -- Step 5: Factor out constants and apply Gaussian cross moment
  have : (fun ω : Configuration (FinLatticeField d N) =>
      ω (Pi.single x 1) * ω (Pi.single y 1) *
      evalAtSite d N a f x * evalAtSite d N a g y) =
      fun ω => (ω (Pi.single x 1) * ω (Pi.single y 1)) *
      (evalAtSite d N a f x * evalAtSite d N a g y) := by
    ext ω; ring
  rw [this, integral_mul_const, lattice_cross_moment d N a mass ha hmass]; ring

/-- The embedded two-point function equals the lattice Green bilinear form. -/
theorem embeddedTwoPoint_eq_latticeGreenBilinear (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f g : ContinuumTestFunction d) :
    embeddedTwoPoint d N a mass ha hmass f g =
    latticeGreenBilinear d N a mass f g := by
  rw [embeddedTwoPoint_eq_lattice_cross_moment, lattice_cross_moment]
  rw [lattice_covariance_eq_spectral]
  rfl

/-- The embedded two-point function equals the lattice spectral sum. -/
theorem embeddedTwoPoint_eq_spectral_sum (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f g : ContinuumTestFunction d) :
    embeddedTwoPoint d N a mass ha hmass f g =
    latticeGreenBilinear d N a mass f g := by
  simpa using embeddedTwoPoint_eq_latticeGreenBilinear
    (d := d) (N := N) (a := a) (mass := mass) (ha := ha) (hmass := hmass) f g

end Pphi2

end
