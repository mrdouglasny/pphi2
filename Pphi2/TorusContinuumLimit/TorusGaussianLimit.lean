/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gaussian Identification of the Torus Continuum Limit

Identifies the weak limit from `torusGaussianLimit_exists` as a Gaussian
measure with the correct covariance (the torus continuum Green's function).

## Main results

- `torusGaussianLimit_isGaussian` — (axiom) weak limits of Gaussians are Gaussian
- `IsTorusGaussianContinuumLimit` — predicate for the Gaussian continuum limit on torus

## Mathematical background

### Gaussianity of the limit

The characteristic functional of ν_{GFF,N} is:

  `E[e^{iω(f)}] = exp(-½ · torusEmbeddedTwoPoint_N(f, f))`

By `torus_propagator_convergence`, the exponent converges to `-½ G_L(f, f)`.
Weak convergence implies pointwise convergence of characteristic functionals.
Hence the limit has Gaussian characteristic functional, and by Bochner-Minlos
on the torus it is a Gaussian measure.

This is the same mathematical content as `gaussianLimit_isGaussian` from
the S'(ℝ^d) approach, but on the torus configuration space.

## References

- Fernique (1975), §III.4
- Simon, *The P(φ)₂ Euclidean QFT* Ch. I
-/

import Pphi2.TorusContinuumLimit.TorusConvergence
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

noncomputable section

open GaussianField MeasureTheory Filter

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Gaussianity of the torus limit -/

/-- **Weak limits of Gaussian measures on the torus are Gaussian.**

If {μ_n} is a sequence of centered Gaussian measures on Configuration(TorusTestFunction L)
that converges weakly to μ, then μ is also a centered Gaussian measure.

The characteristic functional of μ_n is `exp(-½ σ²_n(f))` where σ²_n(f)
is the variance. Weak convergence implies pointwise convergence of
characteristic functionals to `exp(-½ σ²(f))`, which is Gaussian by
the Bochner-Minlos theorem on the nuclear Fréchet space C∞(T²_L).

Reference: Fernique (1975), §III.4; Simon, *The P(φ)₂ Euclidean QFT* Ch. I. -/
axiom torusGaussianLimit_isGaussian
    (μ_seq : ℕ → Measure (Configuration (TorusTestFunction L)))
    (hμ_prob : ∀ n, IsProbabilityMeasure (μ_seq n))
    -- Each μ_n is Gaussian
    (hμ_gauss : ∀ n (f : TorusTestFunction L),
      ∫ ω : Configuration (TorusTestFunction L),
        Real.exp (ω f) ∂(μ_seq n) =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂(μ_seq n)))
    -- Weak convergence to μ
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (hconv : ∀ (g : Configuration (TorusTestFunction L) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Tendsto (fun n => ∫ ω, g ω ∂(μ_seq n)) atTop (nhds (∫ ω, g ω ∂μ))) :
    -- The limit is Gaussian
    ∀ (f : TorusTestFunction L),
      ∫ ω : Configuration (TorusTestFunction L),
        Real.exp (ω f) ∂μ =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂μ)

/-! ## Gaussian continuum limit predicate -/

/-- **Predicate for the torus Gaussian continuum limit measure.**

A probability measure μ on Configuration(TorusTestFunction L) is a
Gaussian continuum limit if:
1. It is a probability measure.
2. It is Gaussian (characteristic functional has exp(-½σ²) form).
3. Its covariance equals the torus continuum Green's function.
4. It is Z₂-symmetric: `μ ∘ (-) = μ`. -/
structure IsTorusGaussianContinuumLimit
    (μ : Measure (Configuration (TorusTestFunction L)))
    (mass : ℝ) (hmass : 0 < mass) : Prop where
  /-- μ is a probability measure -/
  isProbability : IsProbabilityMeasure μ
  /-- Gaussian: characteristic functional has exp(-½σ²) form -/
  isGaussian : ∀ (f : TorusTestFunction L),
    ∫ ω : Configuration (TorusTestFunction L),
      Real.exp (ω f) ∂μ =
    Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂μ)
  /-- Covariance = torus continuum Green's function -/
  covariance_eq : ∀ (f : TorusTestFunction L),
    ∫ ω : Configuration (TorusTestFunction L), (ω f) ^ 2 ∂μ =
    torusContinuumGreen L mass hmass f f
  /-- Z₂ symmetry: μ is invariant under field negation -/
  z2_symmetric : Measure.map
    (Neg.neg : Configuration (TorusTestFunction L) →
      Configuration (TorusTestFunction L)) μ = μ

/-! ## Lattice GFF is Gaussian -/

/-- **The lattice GFF continuum measure is Gaussian.**

The lattice GFF `μ_{GFF,N}` is a centered Gaussian measure, so its pushforward
under the linear embedding `ι̃_N` is also centered Gaussian. The moment
generating function satisfies `E[e^{ω(f)}] = exp(½ E[ω(f)²])`.

Mathematically: `ν_{GFF,N}` is the pushforward of a Gaussian measure under
a linear map, hence Gaussian. The MGF formula follows from the standard
Gaussian identity `E[e^{tX}] = exp(½t²σ²)` at t=1. -/
axiom torusGaussianMeasure_isGaussian (N : ℕ) [NeZero N]
    (mass : ℝ) (hmass : 0 < mass)
    (f : TorusTestFunction L) :
    ∫ ω : Configuration (TorusTestFunction L),
      Real.exp (ω f) ∂(torusContinuumMeasure L N mass hmass) =
    Real.exp ((1 / 2) * torusEmbeddedTwoPoint L N mass hmass f f)

/-! ## Covariance of the limit -/

/-- **Weak convergence transfers second moments to the limit.**

If `ν_N → μ` weakly and `E_N[ω(f)²] → G(f,f)`, then `E_μ[ω(f)²] = G(f,f)`.

This requires uniform integrability of `ω ↦ ω(f)²`, which follows from the
uniform bound `E_N[ω(f)²] ≤ C` (from `torusEmbeddedTwoPoint_uniform_bound`).
Bounded second moments + weak convergence → convergence of second moments. -/
axiom torusLimit_covariance_eq
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ (g : Configuration (TorusTestFunction L) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Tendsto (fun n => ∫ ω, g ω ∂(torusContinuumMeasure L (φ n + 1) mass hmass))
        atTop (nhds (∫ ω, g ω ∂μ)))
    (f : TorusTestFunction L) :
    ∫ ω : Configuration (TorusTestFunction L), (ω f) ^ 2 ∂μ =
    torusContinuumGreen L mass hmass f f

/-! ## Gaussian uniqueness -/

/-- **A Gaussian measure on a nuclear space is determined by its covariance.**

Two centered Gaussian probability measures on Configuration(TorusTestFunction L)
with the same covariance bilinear form are equal.

This follows from the Bochner-Minlos theorem: a Gaussian measure on the dual
of a nuclear space is uniquely determined by its characteristic functional
`exp(-½ C(f,f))`, which depends only on the covariance. -/
axiom gaussian_measure_unique_of_covariance
    (μ₁ μ₂ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    -- Both are Gaussian
    (hμ₁_gauss : ∀ (f : TorusTestFunction L),
      ∫ ω : Configuration (TorusTestFunction L),
        Real.exp (ω f) ∂μ₁ =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂μ₁))
    (hμ₂_gauss : ∀ (f : TorusTestFunction L),
      ∫ ω : Configuration (TorusTestFunction L),
        Real.exp (ω f) ∂μ₂ =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂μ₂))
    -- Same covariance
    (hcov : ∀ (f : TorusTestFunction L),
      ∫ ω : Configuration (TorusTestFunction L), (ω f) ^ 2 ∂μ₁ =
      ∫ ω : Configuration (TorusTestFunction L), (ω f) ^ 2 ∂μ₂) :
    μ₁ = μ₂

/-! ## Z₂ symmetry helpers -/

/-- Negation on Configuration is measurable w.r.t. the cylindrical σ-algebra.

Each evaluation `ω ↦ (-ω)(f) = -(ω f)` is measurable since `ω ↦ ω f` is
measurable and negation on ℝ is measurable. -/
theorem configuration_neg_measurable :
    @Measurable _ _ instMeasurableSpaceConfiguration instMeasurableSpaceConfiguration
      (Neg.neg : Configuration (TorusTestFunction L) →
        Configuration (TorusTestFunction L)) := by
  apply configuration_measurable_of_eval_measurable
  intro f
  -- (-ω)(f) = -(ω f), and ω ↦ ω f is measurable, negation is measurable
  change @Measurable _ _ instMeasurableSpaceConfiguration _ (fun ω => (-ω) f)
  have h_eq : (fun ω : Configuration (TorusTestFunction L) => (-ω) f) =
      (fun ω => -(ω f)) := by
    ext ω; exact ContinuousLinearMap.neg_apply ω f
  rw [h_eq]
  exact (configuration_eval_measurable f).neg

/-- Negation on `(-ω)(f) = -(ω f)` for configurations. -/
theorem configuration_neg_apply (ω : Configuration (TorusTestFunction L))
    (f : TorusTestFunction L) : (-ω) f = -(ω f) :=
  ContinuousLinearMap.neg_apply ω f

/-! ## Z₂ symmetry of lattice GFF -/

/-- **The lattice GFF continuum measure is Z₂-symmetric.**

The lattice GFF μ_{GFF,N} is a centered Gaussian, hence Z₂-symmetric
(invariant under φ ↦ -φ). The pushforward ν_{GFF,N} = (ι̃_N)_* μ_{GFF,N}
inherits this symmetry since the embedding is linear.

**Proof strategy:** Both `neg_* ν` and `ν` are Gaussian probability measures
with the same covariance (since `((-ω)f)² = (ω f)²`), hence equal by
`gaussian_measure_unique_of_covariance`. -/
theorem torusGaussianMeasure_z2_symmetric (N : ℕ) [NeZero N]
    (mass : ℝ) (hmass : 0 < mass) :
    Measure.map (Neg.neg : Configuration (TorusTestFunction L) →
      Configuration (TorusTestFunction L))
      (torusContinuumMeasure L N mass hmass) =
    torusContinuumMeasure L N mass hmass := by
  set ν := torusContinuumMeasure L N mass hmass
  set ν' := Measure.map (Neg.neg : Configuration (TorusTestFunction L) →
    Configuration (TorusTestFunction L)) ν
  have hneg_meas := configuration_neg_measurable L
  -- ν' is a probability measure
  haveI hν_prob : IsProbabilityMeasure ν := torusContinuumMeasure_isProbability L N mass hmass
  haveI hν'_prob : IsProbabilityMeasure ν' :=
    Measure.isProbabilityMeasure_map hneg_meas.aemeasurable
  -- Helper: (-ω)(f) = -(ω f)
  have neg_eval : ∀ (ω : Configuration (TorusTestFunction L)) (f : TorusTestFunction L),
      (-ω) f = -(ω f) := fun ω f => ContinuousLinearMap.neg_apply ω f
  -- Helper: ∫ g(ω) d(neg_* ν) = ∫ g(-ω) dν for measurable g
  -- We use integral_map_of_stronglyMeasurable which requires StronglyMeasurable g.
  -- For the specific integrands we need (exp and pow of evaluation), we prove
  -- measurability from composition with configuration_eval_measurable.
  -- Helper for measurability: ω ↦ (ω f)^2 is strongly measurable
  have eval_sq_sm : ∀ (f : TorusTestFunction L),
      StronglyMeasurable (fun ω : Configuration (TorusTestFunction L) => (ω f) ^ 2) := by
    intro f
    exact ((configuration_eval_measurable f).pow_const 2).stronglyMeasurable
  -- Helper for measurability: ω ↦ exp(ω f) is strongly measurable
  have eval_exp_sm : ∀ (f : TorusTestFunction L),
      StronglyMeasurable (fun ω : Configuration (TorusTestFunction L) => Real.exp (ω f)) := by
    intro f
    exact (Real.measurable_exp.comp (configuration_eval_measurable f)).stronglyMeasurable
  -- Covariance of ν': ∫ (ω f)² dν' = ∫ (ω f)² dν
  have hν'_cov : ∀ (f : TorusTestFunction L),
      ∫ ω : Configuration (TorusTestFunction L), (ω f) ^ 2 ∂ν' =
      ∫ ω : Configuration (TorusTestFunction L), (ω f) ^ 2 ∂ν := by
    intro f
    rw [integral_map_of_stronglyMeasurable hneg_meas (eval_sq_sm f)]
    congr 1; funext ω; rw [neg_eval]; ring
  -- ν' is Gaussian: ∫ exp(ω f) dν' = exp(½ ∫ (ω f)² dν')
  have hν'_gauss : ∀ (f : TorusTestFunction L),
      ∫ ω : Configuration (TorusTestFunction L),
        Real.exp (ω f) ∂ν' =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂ν') := by
    intro f
    -- ∫ exp(ω f) dν' = ∫ exp((-ω) f) dν  (change of variables)
    rw [integral_map_of_stronglyMeasurable hneg_meas (eval_exp_sm f)]
    -- Rewrite the integrand: exp((-ω) f) = exp(-(ω f)) = exp(ω(-f))
    have h_eq : (fun ω : Configuration (TorusTestFunction L) =>
        Real.exp ((-ω) f)) = (fun ω => Real.exp (ω (-f))) := by
      funext ω; congr 1; rw [neg_eval]; simp [map_neg]
    rw [h_eq]
    -- Apply Gaussianity at -f: ∫ exp(ω(-f)) dν = exp(½ · twoPoint(-f,-f))
    rw [torusGaussianMeasure_isGaussian L N mass hmass (-f)]
    congr 1; congr 1
    -- twoPoint(-f,-f) = ∫ (ω f)² dν'
    simp only [torusEmbeddedTwoPoint]
    have h1 : (fun ω : Configuration (TorusTestFunction L) =>
        ω (-f) * ω (-f)) = (fun ω => (ω f) ^ 2) := by
      funext ω; simp [map_neg]; ring
    rw [integral_congr_ae (ae_of_all _ (fun ω => congr_fun h1 ω))]
    exact (hν'_cov f).symm
  -- Gaussianity of ν in the right form
  have hν_gauss : ∀ (f : TorusTestFunction L),
      ∫ ω : Configuration (TorusTestFunction L),
        Real.exp (ω f) ∂ν =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂ν) := by
    intro f
    rw [torusGaussianMeasure_isGaussian L N mass hmass f]
    congr 1; congr 1
    simp only [torusEmbeddedTwoPoint]
    congr 1; funext ω; ring
  -- Apply Gaussian uniqueness: same Gaussianity + same covariance → equal
  exact gaussian_measure_unique_of_covariance L ν' ν hν'_gauss hν_gauss hν'_cov

/-- **Z₂ symmetry is preserved under weak limits.**

If each μ_n is Z₂-symmetric (invariant under negation) and μ_n → μ weakly,
then μ is Z₂-symmetric. This follows because negation is a homeomorphism,
so weak convergence of μ_n implies weak convergence of (neg)_* μ_n,
and both limits must agree. -/
theorem z2_symmetric_of_weakLimit
    (μ_seq : ℕ → Measure (Configuration (TorusTestFunction L)))
    (hμ_symm : ∀ n, Measure.map
      (Neg.neg : Configuration (TorusTestFunction L) →
        Configuration (TorusTestFunction L)) (μ_seq n) = μ_seq n)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (hconv : ∀ (g : Configuration (TorusTestFunction L) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Tendsto (fun n => ∫ ω, g ω ∂(μ_seq n)) atTop (nhds (∫ ω, g ω ∂μ))) :
    Measure.map (Neg.neg : Configuration (TorusTestFunction L) →
      Configuration (TorusTestFunction L)) μ = μ := by
  -- We use the measure extensionality theorem for finite Borel measures.
  haveI := configuration_torus_borelSpace L
  haveI := configuration_torus_polish L
  have hneg_meas := configuration_neg_measurable L
  haveI : IsProbabilityMeasure (Measure.map
      (Neg.neg : Configuration (TorusTestFunction L) →
        Configuration (TorusTestFunction L)) μ) :=
    Measure.isProbabilityMeasure_map hneg_meas.aemeasurable
  -- It suffices to show integrals agree on all bounded continuous functions
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  -- ∫ f d(neg_* μ) = ∫ (f ∘ neg) dμ  (change of variables)
  -- With BorelSpace, continuous functions are AEStronglyMeasurable
  have hf_aesm : ∀ (ν : Measure (Configuration (TorusTestFunction L))),
      AEStronglyMeasurable (fun ω => (f : Configuration (TorusTestFunction L) → ℝ) ω) ν :=
    fun ν => f.continuous.aestronglyMeasurable
  rw [integral_map hneg_meas.aemeasurable (hf_aesm _)]
  -- Need to show: ∫ f(-ω) dμ = ∫ f(ω) dμ
  -- g := ω ↦ f(-ω) is bounded continuous
  set g : Configuration (TorusTestFunction L) → ℝ :=
    fun ω => (f : Configuration (TorusTestFunction L) → ℝ) (-ω) with hg_def
  have hg_cont : Continuous g := f.continuous.comp continuous_neg
  have hbnd : ∀ x : Configuration (TorusTestFunction L),
      |(f : Configuration (TorusTestFunction L) → ℝ) x| ≤ ‖f‖ := by
    intro x; rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm x
  have hg_bdd : ∃ C, ∀ x, |g x| ≤ C := ⟨‖f‖, fun x => hbnd (-x)⟩
  have hf_bdd : ∃ C, ∀ x,
      |(f : Configuration (TorusTestFunction L) → ℝ) x| ≤ C := ⟨‖f‖, hbnd⟩
  -- ∫ g dμ_n → ∫ g dμ  (weak convergence)
  have hconv_g := hconv g hg_cont hg_bdd
  -- ∫ f dμ_n → ∫ f dμ  (weak convergence)
  have hconv_f := hconv _ f.continuous hf_bdd
  -- But ∫ g dμ_n = ∫ f(-ω) dμ_n = ∫ f(ω) d(neg_* μ_n) = ∫ f(ω) dμ_n
  have h_eq_n : (fun n => ∫ ω, g ω ∂(μ_seq n)) =
      (fun n => ∫ ω, (f : Configuration (TorusTestFunction L) → ℝ) ω ∂(μ_seq n)) := by
    funext n
    show ∫ ω, (f : Configuration (TorusTestFunction L) → ℝ) (-ω) ∂(μ_seq n) =
        ∫ ω, (f : Configuration (TorusTestFunction L) → ℝ) ω ∂(μ_seq n)
    rw [← integral_map hneg_meas.aemeasurable (hf_aesm _), hμ_symm n]
  -- Since the sequences are equal, their limits are equal
  exact tendsto_nhds_unique (h_eq_n ▸ hconv_g) hconv_f

/-! ## Full convergence from Gaussian uniqueness -/

/-- **Full sequence convergence of torus Gaussian measures.**

Combines three ingredients:
1. Tightness (`torusContinuumMeasures_tight`): any subsequence has a
   further weakly convergent subsequence (Prokhorov).
2. Gaussianity (`torusGaussianLimit_isGaussian`): any such limit is Gaussian.
3. Uniqueness (`gaussian_measure_unique_of_covariance`): a Gaussian on a
   nuclear space is determined by its covariance.

Together: every subsequential limit is the unique Gaussian with covariance
`torusContinuumGreen`, so the full sequence converges.

This is the standard "subsequential compactness + unique limit ⇒ convergence"
argument from point-set topology. -/
axiom torusGaussianLimit_fullConvergence
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (hμ_gauss : ∀ (f : TorusTestFunction L),
      ∫ ω : Configuration (TorusTestFunction L),
        Real.exp (ω f) ∂μ =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂μ))
    (hcov : ∀ (f : TorusTestFunction L),
      ∫ ω : Configuration (TorusTestFunction L), (ω f) ^ 2 ∂μ =
      torusContinuumGreen L mass hmass f f) :
    ∀ (g : Configuration (TorusTestFunction L) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Tendsto (fun N => ∫ ω, g ω ∂(torusContinuumMeasure L (N + 1) mass hmass))
        atTop (nhds (∫ ω, g ω ∂μ))

/-! ## Full sequence convergence -/

/-- **The full sequence of torus Gaussian measures converges.**

Unlike `torusGaussianLimit_exists` which only gives a subsequential limit,
this theorem shows the **full sequence** `{ν_{GFF,N}}` converges weakly.

The proof:
1. By `torusGaussianLimit_exists`, every subsequence has a further subsequence
   converging to some limit μ.
2. By `torusGaussianLimit_isGaussian`, μ is Gaussian.
3. By `torusLimit_covariance_eq`, the covariance of μ is `torusContinuumGreen`.
4. By `gaussian_measure_unique_of_covariance`, all such limits are the same.
5. Since every subsequence has a further subsequence converging to the **same**
   limit, the full sequence converges.

**This theorem is PROVED** from the axioms. -/
theorem torusGaussianLimit_converges
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ (μ : Measure (Configuration (TorusTestFunction L))),
      IsProbabilityMeasure μ ∧
      IsTorusGaussianContinuumLimit L μ mass hmass ∧
      ∀ (g : Configuration (TorusTestFunction L) → ℝ),
        Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
        Tendsto (fun N => ∫ ω, g ω ∂(torusContinuumMeasure L (N + 1) mass hmass))
          atTop (nhds (∫ ω, g ω ∂μ)) := by
  -- Step 1: Get a subsequential limit
  obtain ⟨φ, μ, hφ_mono, hμ_prob, hconv⟩ := torusGaussianLimit_exists L mass hmass
  haveI := hμ_prob
  -- Step 2: The limit is Gaussian
  have hμ_gauss : ∀ f : TorusTestFunction L,
      ∫ ω : Configuration (TorusTestFunction L),
        Real.exp (ω f) ∂μ =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂μ) := by
    exact torusGaussianLimit_isGaussian L
      (fun n => torusContinuumMeasure L (φ n + 1) mass hmass)
      (fun n => torusContinuumMeasure_isProbability L (φ n + 1) mass hmass)
      (fun n f => by
        rw [torusGaussianMeasure_isGaussian L (φ n + 1) mass hmass f]
        congr 1
        simp only [torusEmbeddedTwoPoint]
        congr 1
        congr 1
        funext ω
        ring)
      μ hconv
  -- Step 3: Covariance equals continuum Green's function
  have hcov : ∀ f : TorusTestFunction L,
      ∫ ω : Configuration (TorusTestFunction L), (ω f) ^ 2 ∂μ =
      torusContinuumGreen L mass hmass f f :=
    fun f => torusLimit_covariance_eq L mass hmass μ φ hφ_mono hconv f
  -- Step 4: The limit satisfies IsTorusGaussianContinuumLimit
  have hGCL : IsTorusGaussianContinuumLimit L μ mass hmass := {
    isProbability := hμ_prob
    isGaussian := hμ_gauss
    covariance_eq := hcov
    z2_symmetric := by
      exact z2_symmetric_of_weakLimit L
        (fun n => torusContinuumMeasure L (φ n + 1) mass hmass)
        (fun n => torusGaussianMeasure_z2_symmetric L (φ n + 1) mass hmass)
        μ hconv
  }
  -- Step 5: Full sequence convergence
  -- Every subsequential limit is the unique Gaussian with this covariance.
  -- Standard topology argument: if every subsequence has a further subsequence
  -- converging to the same point, then the full sequence converges.
  exact ⟨μ, hμ_prob, hGCL,
    torusGaussianLimit_fullConvergence L mass hmass μ hμ_gauss hcov⟩

/-! ## Nontriviality -/

/-- **Nontriviality of the torus Gaussian continuum limit.**

For any nonzero test function f, the two-point function is strictly positive. -/
theorem torusGaussianLimit_nontrivial
    (mass : ℝ) (hmass : 0 < mass)
    (f : TorusTestFunction L) (hf : f ≠ 0)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (h2pt : ∫ ω : Configuration (TorusTestFunction L),
        (ω f) ^ 2 ∂μ = torusContinuumGreen L mass hmass f f) :
    0 < ∫ ω : Configuration (TorusTestFunction L), (ω f) ^ 2 ∂μ := by
  rw [h2pt]
  exact torusContinuumGreen_pos L mass hmass f hf

end Pphi2

end
