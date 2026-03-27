/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michael R. Douglas

# Covariance Convergence: Torus → Cylinder as Lt → ∞

States and proves (modulo known axioms) that the torus Green's function
of embedded cylinder test functions converges to the cylinder Green's
function as the temporal period Lt → ∞.

## Mathematical content

On the asymmetric torus T_{Lt,Ls}, the Green's function in the
mixed spectral representation (Fourier in x, position in t) is:

  `G_{Lt,Ls}((t,x),(t',x')) = (1/Ls) Σ_n e^{2πin(x-x')/Ls}
      · cosh(ω_n(Lt/2 - |t-t'|)) / (2ω_n sinh(ω_n Lt/2))`

where `ω_n = √((2πn/Ls)² + m²)` is the dispersion relation.

As Lt → ∞, `coth(ω_n Lt/2) → 1`, so each mode's 1D Green's function
converges:

  `cosh(ω_n(Lt/2 - |t|)) / (2ω_n sinh(ω_n Lt/2)) → e^{-ω_n|t|} / (2ω_n)`

The convergence is exponentially fast: the error is O(e^{-m Lt})
since `ω_n ≥ m > 0` for all n (mass gap).

At the level of test functions (bilinear forms), this gives:

  `asymTorusContinuumGreen Lt Ls mass (embed f) (embed g)
    → cylinderGreen Ls mass f g`

as Lt → ∞, where `embed = cylinderToTorusEmbed Lt Ls`.

## Main results

- `asymTorusGreen_tendsto_cylinderGreen` — covariance convergence (axiom)
- `cylinderIRLimit_covariance_eq` — the IR limit measure has the correct
  cylinder covariance
- `cylinderPullbackGFF_secondMoment_eq_torus` — pullback second moment equals
  torus second moment on `cylinderToTorusEmbed` (via `cylinderPullbackMeasure_integral_sq`)
- Scalar 1D periodic/free kernel comparison — `Pphi2.GeneralResults.PeriodicResolvent1D`
  (definitions `periodicKernel`, `freeKernel`; this file keeps expanded `Pphi2.periodicResolvent_*` aliases)

## References

- Glimm-Jaffe, *Quantum Physics*, §19.1 (infinite volume limit)
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. VIII
-/

import Pphi2.IRLimit.CylinderOS
import Pphi2.AsymTorus.AsymTorusEmbedding
import Pphi2.GeneralResults.PeriodicResolvent1D

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory Filter PeriodicResolvent1D

variable (Ls : ℝ) [hLs : Fact (0 < Ls)]

/-! ## Green's function convergence

The key analytical fact: the asymmetric torus Green's function of
embedded cylinder test functions converges to the cylinder Green's
function as the temporal period Lt → ∞.

### Proof sketch (not yet formalized)

For pure tensors `f = g ⊗ h` where `g ∈ C∞(S¹_{Ls})` and `h ∈ 𝓢(ℝ)`:

1. `cylinderToTorusEmbed` maps `g ⊗ h ↦ (periodize h) ⊗ g` (periodize
   temporal factor, swap order).

2. The torus Green's function in the spatial Fourier basis is:
     `G_{Lt,Ls}(f,f) = (1/Ls) Σ_n |ĉ_n(g)|² · ∫∫ h̃_n(t) h̃_n(t')
        · cosh(ω_n(Lt/2-|t-t'|)) / (2ω_n sinh(ω_n Lt/2)) dt dt'`
   where `h̃_n` is the periodization of h restricted to mode n.

3. As Lt → ∞, `periodize(h)` converges to `h` on any compact set
   (the wrap-around terms decay like `e^{-m Lt}`), and the 1D periodic
   Green's function converges to the non-periodic one:
     `cosh(ω(Lt/2-|t|))/(2ω sinh(ωLt/2)) → e^{-ω|t|}/(2ω)`

4. Dominated convergence: the uniform bound from `torusGreen_uniform_bound`
   provides the dominating function. The series over spatial modes n
   converges uniformly because `ω_n → ∞` and Schwartz coefficients
   decay rapidly.

5. The limit equals `cylinderGreen Ls mass f g` by the spectral
   representation of the cylinder covariance. -/

/-- **Torus Green's function converges to cylinder Green's function.**

For any cylinder test functions f, g ∈ C∞(S¹_{Ls}) ⊗̂ 𝓢(ℝ), the
asymmetric torus Green's function of the embedded test functions
converges to the cylinder Green's function as Lt → ∞.

  `G_{Lt,Ls}(embed f, embed g) → G_cyl(f, g)` as `Lt → ∞`

This is the covariance analogue of `torus_propagator_convergence`
(lattice → torus, as N → ∞). Here the convergence is from finite
temporal volume to infinite temporal volume.

**Convergence mechanism**: For each spatial mode n, the 1D periodic
resolvent kernel on [0, Lt] converges to the infinite-line kernel:
  `cosh(ω_n(Lt/2 - |t|)) / (2ω_n sinh(ω_n Lt/2)) → e^{-ω_n|t|} / (2ω_n)`
Convergence is exponentially fast: error ≤ C · e^{-m·Lt} where m is the
mass (gap), since `ω_n ≥ m` for all n.

**Axiom justification**: This requires connecting the abstract `cylinderGreen`
(defined via the axiomatized `cylinderMassOperator`) to the explicit
resolvent kernel. The content is that `cylinderMassOperator` correctly
implements the spectral decomposition
  `(Tf)_n(p) = ĉ_n(g) · ĥ(p) / √(p² + ω_n²)`
in spatial Fourier mode n, temporal Fourier variable p. -/
axiom asymTorusGreen_tendsto_cylinderGreen
    (mass : ℝ) (hmass : 0 < mass)
    (f g : CylinderTestFunction Ls)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop) :
    Tendsto (fun n =>
      @asymTorusContinuumGreen (Lt n) Ls (hLt n) _ mass hmass
        (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _ f)
        (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _ g))
      atTop (nhds (cylinderGreen Ls mass hmass f g))

/-- Second moments for the pulled-back cylinder GFF equal torus second moments on embedded
test functions (`Pphi2.IRLimit.CylinderEmbedding.cylinderPullbackMeasure_integral_sq`). -/
theorem cylinderPullbackGFF_secondMoment_eq_torus
    (Lt : ℝ) [hLt : Fact (0 < Lt)]
    (mass : ℝ) (hmass : 0 < mass)
    (f : CylinderTestFunction Ls) :
    ∫ ω, (ω f) ^ 2 ∂(cylinderPullbackMeasure Lt Ls
        (GaussianField.measure (GaussianField.cylinderMassOperator Ls mass hmass))) =
    ∫ ω, (ω (cylinderToTorusEmbed Lt Ls f)) ^ 2 ∂
        (GaussianField.measure (GaussianField.cylinderMassOperator Ls mass hmass)) :=
  cylinderPullbackMeasure_integral_sq Lt Ls _ f

/-! ## Covariance of the IR limit

The main payoff: combining the Green's function convergence with the
weak convergence of measures to identify the covariance of the IR limit. -/

/-- **The IR limit measure has the correct cylinder covariance.**

If the sequence of pulled-back torus measures `ν_{Lt_n}` converges
weakly to a measure ν on cylinder configurations, and each torus
measure is Gaussian with the correct torus covariance, then ν has
covariance equal to `cylinderGreen`.

**Proof strategy** (characteristic function method, same as
`torusLimit_covariance_eq`):
0. `cylinderPullbackGFF_secondMoment_eq_torus`: along the approximating sequence,
   cylinder second moments equal torus second moments on `cylinderToTorusEmbed f`.
1. Each torus measure is Gaussian: `E[e^{iω(g)}] = exp(-½ ⟨Tg,Tg⟩)` with
   `T = cylinderMassOperator`, and `⟨Tg,Tg⟩ = G_{Lt}(g,g)` for `g = embed f`
   (`second_moment_eq_covariance` + covariance = `greenFunctionBilinear`).
2. The Green's function converges: `G_{Lt}(embed f, embed f) → G_cyl(f,f)`
   (`asymTorusGreen_tendsto_cylinderGreen`).
3. Weak convergence: `∫ cos(ω(f)) dν_{Lt} → ∫ cos(ω(f)) dν`
4. Combining: `exp(-½ ∫(ωf)² dν) = exp(-½ G_cyl(f,f))`
5. By injectivity of exp: `∫ (ωf)² dν = G_cyl(f,f)` -/
axiom cylinderIRLimit_covariance_eq
    (mass : ℝ) (hmass : 0 < mass)
    (ν : Measure (Configuration (CylinderTestFunction Ls)))
    [IsProbabilityMeasure ν]
    -- ν is a weak limit of pulled-back Gaussian torus measures
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ (f : CylinderTestFunction Ls),
      Tendsto (fun n =>
        ∫ ω, Complex.exp (Complex.I * ↑(ω f))
          ∂(cylinderPullbackMeasure (Lt (φ n)) Ls
            (GaussianField.measure
              (@GaussianField.cylinderMassOperator Ls _ mass hmass))))
        atTop (nhds (∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν)))
    (f : CylinderTestFunction Ls) :
    ∫ ω : Configuration (CylinderTestFunction Ls), (ω f) ^ 2 ∂ν =
    cylinderGreen Ls mass hmass f f

/-! ## Exponential convergence rate

The mass gap `m > 0` gives exponential convergence of the periodic Green's
function to the non-periodic one. The scalar 1D estimates live in
`PeriodicResolvent1D` (`periodicKernel`, `freeKernel`, and lemmas such as
`PeriodicResolvent1D.abs_sub_free_le`).

The `Pphi2.periodicResolvent_*` theorems below restate the same bounds in
expanded form for compatibility with the mixed spectral representation
`cosh(ω(Lt/2-|t|))/(2ω sinh(ωLt/2))` used in the torus Green's function. -/

/-- The 1D periodic resolvent converges exponentially to the free resolvent.

For ω > 0:
  `|cosh(ω(Lt/2 - |t|))/(2ω sinh(ωLt/2)) - e^{-ω|t|}/(2ω)|
    ≤ e^{-ω(Lt - |t|)} / (ω(1 - e^{-ω Lt}))`

See `PeriodicResolvent1D.abs_sub_free_le`. -/
theorem periodicResolvent_convergence_rate
    (ω : ℝ) (hω : 0 < ω)
    (t : ℝ) (Lt : ℝ) (hLt : 0 < Lt) :
    |Real.cosh (ω * (Lt / 2 - |t|)) / (2 * ω * Real.sinh (ω * Lt / 2)) -
     Real.exp (-ω * |t|) / (2 * ω)| ≤
    Real.exp (-ω * (Lt - |t|)) /
      (ω * (1 - Real.exp (-ω * Lt))) := by
  simpa [periodicKernel, freeKernel] using abs_sub_free_le ω hω t Lt hLt

/-- Uniform half-period decay; see `PeriodicResolvent1D.abs_sub_free_le_on_halfPeriodStrip`. -/
theorem periodicResolvent_convergence_rate_uniform
    (ω : ℝ) (hω : 0 < ω)
    (t : ℝ) (Lt : ℝ) (hLt : 0 < Lt) (ht : |t| < Lt / 2) :
    |Real.cosh (ω * (Lt / 2 - |t|)) / (2 * ω * Real.sinh (ω * Lt / 2)) -
      Real.exp (-ω * |t|) / (2 * ω)| ≤
    Real.exp (-ω * Lt / 2) /
      (ω * (1 - Real.exp (-ω * Lt))) := by
  simpa [periodicKernel, freeKernel] using
    abs_sub_free_le_on_halfPeriodStrip ω hω t Lt hLt ht

/-- Uniform mass-gap control; see `PeriodicResolvent1D.abs_sub_free_le_uniform_mass_gap`. -/
theorem periodicResolvent_convergence_rate_uniform_mass_gap
    (ω mass : ℝ) (hmass : 0 < mass) (hω : mass ≤ ω)
    (t : ℝ) (Lt : ℝ) (hLt : 0 < Lt) (ht : |t| < Lt / 2) :
    |Real.cosh (ω * (Lt / 2 - |t|)) / (2 * ω * Real.sinh (ω * Lt / 2)) -
      Real.exp (-ω * |t|) / (2 * ω)| ≤
    Real.exp (-mass * Lt / 2) /
      (mass * (1 - Real.exp (-mass * Lt))) := by
  simpa [periodicKernel, freeKernel] using
    abs_sub_free_le_uniform_mass_gap ω mass hmass hω t Lt hLt ht

omit hLs in
/-- Specialization of the uniform mass-gap bound to cylinder frequencies
`ω_n = resolventFreq Ls mass n`. -/
theorem periodicResolvent_resolventFreq_convergence_rate_uniform
    (mass : ℝ) (hmass : 0 < mass) (n : ℕ)
    (t : ℝ) (Lt : ℝ) (hLt : 0 < Lt) (ht : |t| < Lt / 2) :
    |Real.cosh (resolventFreq Ls mass n * (Lt / 2 - |t|)) /
        (2 * resolventFreq Ls mass n * Real.sinh (resolventFreq Ls mass n * Lt / 2)) -
      Real.exp (-resolventFreq Ls mass n * |t|) / (2 * resolventFreq Ls mass n)| ≤
    Real.exp (-mass * Lt / 2) /
      (mass * (1 - Real.exp (-mass * Lt))) := by
  simpa [periodicKernel, freeKernel] using
    abs_sub_free_le_uniform_mass_gap
      (ω := resolventFreq Ls mass n) (mass := mass) hmass
      (resolventFreq_mass_le Ls mass hmass.le n) t Lt hLt ht

/-- For fixed `ω > 0` and `t`, the periodic 1D resolvent kernel converges to the free resolvent
kernel as `Lt → ∞`. See `PeriodicResolvent1D.tendsto_periodicKernel_freeKernel`. -/
theorem periodicResolvent_tendsto_free
    (ω : ℝ) (hω : 0 < ω) (t : ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop) :
    Tendsto
      (fun n =>
        Real.cosh (ω * (Lt n / 2 - |t|)) /
          (2 * ω * Real.sinh (ω * Lt n / 2)))
      atTop (nhds (Real.exp (-ω * |t|) / (2 * ω))) := by
  simpa [periodicKernel, freeKernel] using
    tendsto_periodicKernel_freeKernel ω hω t Lt hLt hLt_tend

end Pphi2

end
