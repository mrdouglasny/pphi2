/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

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

## References

- Glimm-Jaffe, *Quantum Physics*, §19.1 (infinite volume limit)
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. VIII
-/

import Pphi2.IRLimit.CylinderOS
import Pphi2.AsymTorus.AsymTorusEmbedding

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory Filter

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
1. Each lattice measure is Gaussian: `E[e^{iω(f)}] = exp(-½ G_{Lt}(f,f))`
2. The Green's function converges: `G_{Lt}(embed f, embed f) → G_cyl(f,f)`
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

The mass gap m > 0 gives exponential convergence of the periodic
Green's function to the non-periodic one. This is useful for
quantitative control and is the mechanism behind `torusGreen_uniform_bound`
in `Cylinder/MethodOfImages.lean`. -/

/-- The 1D periodic resolvent converges exponentially to the free resolvent.

For ω > 0 and |t| < Lt/2:
  |cosh(ω(Lt/2 - |t|))/(2ω sinh(ωLt/2)) - e^{-ω|t|}/(2ω)|
    ≤ e^{-ω(Lt - |t|)} / (ω(1 - e^{-ω Lt}))

This is the standard wrap-around contribution from the method of images:
the nearest nontrivial image sits at temporal distance `Lt - |t|`.

In particular, on any fixed compact time interval the error is `O(e^{-ω Lt})`
as `Lt → ∞`, and under the hypothesis `|t| < Lt / 2` it is uniformly
`O(e^{-ω Lt / 2})`. -/
theorem periodicResolvent_convergence_rate
    (ω : ℝ) (hω : 0 < ω)
    (t : ℝ) (Lt : ℝ) (hLt : 0 < Lt) (_ht : |t| < Lt / 2) :
    |Real.cosh (ω * (Lt / 2 - |t|)) / (2 * ω * Real.sinh (ω * Lt / 2)) -
     Real.exp (-ω * |t|) / (2 * ω)| ≤
    Real.exp (-ω * (Lt - |t|)) /
      (ω * (1 - Real.exp (-ω * Lt))) := by
  set a : ℝ := ω * Lt / 2
  set b : ℝ := ω * |t|
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    positivity
  have hsinh_pos : 0 < Real.sinh a := by
    rw [Real.sinh_eq]
    have hnum_pos : 0 < Real.exp a - Real.exp (-a) := by
      exact sub_pos.mpr <| (Real.exp_lt_exp).2 (by linarith [ha_pos])
    nlinarith
  have hsinh_ne : Real.sinh a ≠ 0 := ne_of_gt hsinh_pos
  have hω_ne : ω ≠ 0 := ne_of_gt hω
  have hLt_exp_lt : Real.exp (-ω * Lt) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hone_pos : 0 < 1 - Real.exp (-ω * Lt) := sub_pos.mpr hLt_exp_lt
  have hone_ne : 1 - Real.exp (-ω * Lt) ≠ 0 := ne_of_gt hone_pos
  have hsplit : Real.cosh (a - b) =
      Real.sinh a * Real.exp (-b) + Real.exp (-a) * Real.cosh b := by
    have hcosh_a : Real.cosh a = Real.sinh a + Real.exp (-a) := by
      linarith [Real.cosh_sub_sinh a]
    calc
      Real.cosh (a - b)
          = Real.cosh a * Real.cosh b - Real.sinh a * Real.sinh b := by
              rw [Real.cosh_sub]
      _ = (Real.sinh a + Real.exp (-a)) * Real.cosh b - Real.sinh a * Real.sinh b := by
            rw [hcosh_a]
      _ = Real.sinh a * (Real.cosh b - Real.sinh b) + Real.exp (-a) * Real.cosh b := by
            ring
      _ = Real.sinh a * Real.exp (-b) + Real.exp (-a) * Real.cosh b := by
            rw [Real.cosh_sub_sinh]
  have hdiff :
      Real.cosh (ω * (Lt / 2 - |t|)) / (2 * ω * Real.sinh (ω * Lt / 2)) -
          Real.exp (-ω * |t|) / (2 * ω) =
        Real.exp (-a) * Real.cosh b / (2 * ω * Real.sinh a) := by
    have harg : ω * (Lt / 2 - |t|) = a - b := by
      dsimp [a, b]
      ring
    rw [harg, show ω * Lt / 2 = a by rfl, hsplit]
    field_simp [hω_ne, hsinh_ne]
    ring
  have habs :
      |Real.cosh (ω * (Lt / 2 - |t|)) / (2 * ω * Real.sinh (ω * Lt / 2)) -
        Real.exp (-ω * |t|) / (2 * ω)| =
      Real.exp (-a) * Real.cosh b / (2 * ω * Real.sinh a) := by
    rw [hdiff, abs_of_nonneg]
    positivity
  have hsinh_exp : 2 * Real.sinh a = Real.exp a - Real.exp (-a) := by
    rw [Real.sinh_eq]
    ring
  have hratio :
      Real.exp (-a) / (2 * Real.sinh a) =
        Real.exp (-ω * Lt) / (1 - Real.exp (-ω * Lt)) := by
    rw [hsinh_exp, Real.exp_neg]
    set u : ℝ := Real.exp a
    have hu_ne : u ≠ 0 := by
      dsimp [u]
      exact ne_of_gt (Real.exp_pos a)
    have hratio_u :
        u⁻¹ / (u - u⁻¹) = (u * u)⁻¹ / (1 - (u * u)⁻¹) := by
      field_simp [hu_ne]
    have hu_sq : Real.exp (-ω * Lt) = (u * u)⁻¹ := by
      rw [show -ω * Lt = -(a + a) by
        dsimp [a]
        ring, Real.exp_neg, Real.exp_add, show Real.exp a = u by rfl]
    rw [hu_sq]
    simpa [u] using hratio_u
  have hcosh_le : Real.cosh b ≤ Real.exp b := by
    rw [Real.cosh_eq]
    have hle : Real.exp (-b) ≤ Real.exp b := by
      exact (Real.exp_le_exp).2 (by linarith [hb_nonneg])
    linarith
  have hfactor_nonneg :
      0 ≤ Real.exp (-ω * Lt) / (ω * (1 - Real.exp (-ω * Lt))) := by
    apply div_nonneg
    · exact le_of_lt (Real.exp_pos _)
    · exact le_of_lt (mul_pos hω hone_pos)
  rw [habs]
  calc
    Real.exp (-a) * Real.cosh b / (2 * ω * Real.sinh a)
        = Real.cosh b * (Real.exp (-ω * Lt) / (ω * (1 - Real.exp (-ω * Lt)))) := by
            have hωhone_ne : ω * (1 - Real.exp (-ω * Lt)) ≠ 0 :=
              mul_ne_zero hω_ne hone_ne
            calc
              Real.exp (-a) * Real.cosh b / (2 * ω * Real.sinh a)
                  = Real.cosh b * (Real.exp (-a) / (2 * Real.sinh a)) / ω := by
                      field_simp [hω_ne, hsinh_ne]
              _ = Real.cosh b * (Real.exp (-ω * Lt) / (1 - Real.exp (-ω * Lt))) / ω := by
                    rw [hratio]
              _ = Real.cosh b * (Real.exp (-ω * Lt) / (ω * (1 - Real.exp (-ω * Lt)))) := by
                    field_simp [hω_ne, hone_ne]
    _ ≤ Real.exp b * (Real.exp (-ω * Lt) / (ω * (1 - Real.exp (-ω * Lt)))) := by
          gcongr
    _ = Real.exp (-ω * (Lt - |t|)) / (ω * (1 - Real.exp (-ω * Lt))) := by
          have hcombine : Real.exp b * Real.exp (-ω * Lt) =
              Real.exp (-ω * (Lt - |t|)) := by
            rw [show b = ω * |t| by rfl, ← Real.exp_add]
            congr 1
            ring
          calc
            Real.exp b * (Real.exp (-ω * Lt) / (ω * (1 - Real.exp (-ω * Lt))))
                = (Real.exp b * Real.exp (-ω * Lt)) / (ω * (1 - Real.exp (-ω * Lt))) := by
                    rw [div_eq_mul_inv]
                    ring
            _ = Real.exp (-ω * (Lt - |t|)) / (ω * (1 - Real.exp (-ω * Lt))) := by
                    rw [hcombine]

end Pphi2

end
