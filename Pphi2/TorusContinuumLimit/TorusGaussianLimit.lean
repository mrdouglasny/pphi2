/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gaussian Identification of the Torus Continuum Limit

Identifies the weak limit from `torusGaussianLimit_exists` as a Gaussian
measure with the correct covariance (the torus continuum Green's function).

## Main results

- `torusGaussianLimit_isGaussian` — (theorem) weak limits of Gaussians are Gaussian
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
import Mathlib.Probability.Distributions.Gaussian.Real

noncomputable section

open GaussianField MeasureTheory Filter ProbabilityTheory
open scoped NNReal

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Gaussianity of the torus limit -/

/-- **Each 1D pushforward of a Gaussian measure is a real Gaussian.**

From the MGF identity `∫ exp(ω f) dμ = exp(½ ∫ (ω f)² dμ)` for all test functions f,
substituting `t • f` gives `mgf (eval_f) μ t = exp(σ² t² / 2)`, which matches the MGF
of `gaussianReal 0 σ²`. By complex MGF extension (`eqOn_complexMGF_of_mgf`) and
measure uniqueness (`ext_of_complexMGF_eq`), the pushforward equals `gaussianReal 0 σ²`. -/
private theorem pushforward_eval_gaussianReal
    (μ_seq : ℕ → Measure (Configuration (TorusTestFunction L)))
    (hμ_prob : ∀ n, IsProbabilityMeasure (μ_seq n))
    (hμ_gauss : ∀ n (f : TorusTestFunction L),
      ∫ ω : Configuration (TorusTestFunction L),
        Real.exp (ω f) ∂(μ_seq n) =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂(μ_seq n)))
    (f : TorusTestFunction L) (n : ℕ) :
    (μ_seq n).map (fun ω : Configuration (TorusTestFunction L) => ω f) =
    gaussianReal 0 (∫ ω, (ω f) ^ 2 ∂(μ_seq n)).toNNReal := by
  haveI := hμ_prob n
  set eval_f := fun ω : Configuration (TorusTestFunction L) => ω f
  set σ_sq := ∫ ω, (ω f) ^ 2 ∂(μ_seq n)
  set v := σ_sq.toNNReal
  have h_σ_nonneg : 0 ≤ σ_sq := integral_nonneg (fun ω => sq_nonneg _)
  have h_σ_cast : (v : ℝ) = σ_sq := Real.coe_toNNReal _ h_σ_nonneg
  -- Step 1: The exp(t * ω f) integrand is integrable for all t
  have h_integrable : ∀ t, Integrable (fun ω => Real.exp (t * eval_f ω)) (μ_seq n) := by
    intro t
    by_contra h_not_int
    have h_zero := integral_undef h_not_int
    have h := hμ_gauss n (t • f)
    simp only [show ∀ ω : Configuration (TorusTestFunction L), ω (t • f) = t * ω f
      from fun ω => ContinuousLinearMap.map_smul_of_tower ω t f] at h
    linarith [Real.exp_pos ((1 / 2) * ∫ ω, (t * ω f) ^ 2 ∂(μ_seq n))]
  -- Step 2: Match MGFs
  have h_mgf_eq : mgf eval_f (μ_seq n) = mgf id (gaussianReal 0 v) := by
    funext t
    -- Both sides equal exp(σ_sq * t² / 2)
    -- LHS from hypothesis:
    have h_lhs : mgf eval_f (μ_seq n) t = Real.exp (σ_sq * t ^ 2 / 2) := by
      simp only [mgf]
      have h := hμ_gauss n (t • f)
      simp only [show ∀ ω : Configuration (TorusTestFunction L), ω (t • f) = t * ω f
        from fun ω => ContinuousLinearMap.map_smul_of_tower ω t f] at h
      simp_rw [show ∀ ω : Configuration (TorusTestFunction L),
        (t * ω f) ^ 2 = t ^ 2 * (ω f) ^ 2 from fun ω => by ring,
        integral_const_mul] at h
      rw [h]; congr 1; ring
    -- RHS from Gaussian MGF:
    have h_rhs : mgf id (gaussianReal 0 v) t = Real.exp (σ_sq * t ^ 2 / 2) := by
      rw [congr_fun mgf_id_gaussianReal t]
      congr 1; simp only [zero_mul, zero_add]; rw [h_σ_cast]
    rw [h_lhs, h_rhs]
  -- Step 3: integrableExpSet is all of ℝ
  have h_exp_set : integrableExpSet eval_f (μ_seq n) = Set.univ := by
    ext t; simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact h_integrable t
  -- Step 4: complexMGF equality (from mgf equality + full strip)
  have h_cmgf_eq : complexMGF eval_f (μ_seq n) = complexMGF id (gaussianReal 0 v) := by
    have h_eqon := eqOn_complexMGF_of_mgf h_mgf_eq
    rw [h_exp_set, interior_univ] at h_eqon
    funext z
    exact h_eqon (Set.mem_univ z)
  -- Step 5: Measure equality
  have h_map_eq := Measure.ext_of_complexMGF_eq
    (configuration_eval_measurable f).aemeasurable aemeasurable_id h_cmgf_eq
  rwa [Measure.map_id] at h_map_eq

/-- **Weak limits of centered Gaussians on ℝ are centered Gaussian.**

If `ν_n = gaussianReal 0 v_n` and `ν_n → ν` weakly, then `ν = gaussianReal 0 v` for some v.

Proof: characteristic functions converge pointwise (cos/sin are bounded continuous).
The CF of N(0, v_n) at t is exp(-v_n t²/2). By dominated convergence, the CF of ν
is continuous at 0 with CF(0) = 1, so the limit can't be 0, forcing v_n → v.
By `ext_of_charFun`, the limit measure is identified. -/
axiom weakLimit_centered_gaussianReal
    (ν_seq : ℕ → Measure ℝ) (v_seq : ℕ → ℝ≥0)
    (hν_prob : ∀ n, IsProbabilityMeasure (ν_seq n))
    (hν_gauss : ∀ n, ν_seq n = gaussianReal 0 (v_seq n))
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hconv : ∀ (g : ℝ → ℝ), Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Tendsto (fun n => ∫ x, g x ∂(ν_seq n)) atTop (nhds (∫ x, g x ∂ν))) :
    ∃ v : ℝ≥0, ν = gaussianReal 0 v

/-- **Weak limits of Gaussian measures on the torus are Gaussian.**

If {μ_n} is a sequence of centered Gaussian measures on Configuration(TorusTestFunction L)
that converges weakly to μ, then μ is also a centered Gaussian measure.

Proof: For each test function f, the 1D pushforward `μ_n.map (ω ↦ ω f)` is
`gaussianReal 0 σ_n²` (by `pushforward_eval_gaussianReal`). Weak convergence
transfers to pushforwards (ω ↦ ω f is continuous). By `weakLimit_centered_gaussianReal`,
the limit pushforward is Gaussian. The MGF identity follows from Gaussian properties.

Reference: Fernique (1975), §III.4; Simon, *The P(φ)₂ Euclidean QFT* Ch. I. -/
theorem torusGaussianLimit_isGaussian
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
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂μ) := by
  intro f
  set eval_f := fun ω : Configuration (TorusTestFunction L) => ω f
  have h_eval_meas : Measurable eval_f := configuration_eval_measurable f
  -- Step 1: Each pushforward (μ_seq n).map eval_f is gaussianReal 0 (σ_n²)
  have h_push_gauss : ∀ n, (μ_seq n).map eval_f =
      gaussianReal 0 (∫ ω, (ω f) ^ 2 ∂(μ_seq n)).toNNReal :=
    fun n => pushforward_eval_gaussianReal L μ_seq hμ_prob hμ_gauss f n
  -- Step 2: Weak convergence of pushforwards on ℝ
  have h_push_conv : ∀ (g : ℝ → ℝ), Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Tendsto (fun n => ∫ x, g x ∂((μ_seq n).map eval_f))
        atTop (nhds (∫ x, g x ∂(μ.map eval_f))) := by
    intro g hg_cont hg_bdd
    simp_rw [integral_map h_eval_meas.aemeasurable hg_cont.measurable.aestronglyMeasurable]
    exact hconv (g ∘ eval_f)
      (hg_cont.comp (WeakDual.eval_continuous f))
      (by obtain ⟨C, hC⟩ := hg_bdd; exact ⟨C, fun x => hC (x f)⟩)
  -- Step 3: Limit pushforward is Gaussian
  haveI : IsProbabilityMeasure (μ.map eval_f) :=
    Measure.isProbabilityMeasure_map h_eval_meas.aemeasurable
  obtain ⟨v, hv⟩ := weakLimit_centered_gaussianReal
    (fun n => (μ_seq n).map eval_f)
    (fun n => (∫ ω, (ω f) ^ 2 ∂(μ_seq n)).toNNReal)
    (fun n => by dsimp; rw [h_push_gauss n]; infer_instance)
    h_push_gauss (μ.map eval_f) h_push_conv
  -- Step 4: Extract the identity
  -- ∫ exp(ω f) dμ = ∫ exp(x) d(gaussianReal 0 v)
  have h_integral_exp : ∫ ω, Real.exp (eval_f ω) ∂μ =
      ∫ x, Real.exp x ∂(gaussianReal 0 v) := by
    rw [← integral_map h_eval_meas.aemeasurable
        Real.measurable_exp.aestronglyMeasurable, hv]
  -- ∫ exp(x) d(gaussianReal 0 v) = exp(v/2)
  have h_exp_val : ∫ x, Real.exp x ∂(gaussianReal 0 v) = Real.exp (↑v / 2) := by
    have := congr_fun (mgf_id_gaussianReal (μ := 0) (v := v)) 1
    simp only [mgf, one_mul, zero_add, one_pow, mul_one, id] at this
    exact this
  -- ∫ (ω f)² dμ = v
  have h_second_moment : ∫ ω, (eval_f ω) ^ 2 ∂μ = ↑v := by
    have h1 : ∫ ω, (eval_f ω) ^ 2 ∂μ = ∫ x, x ^ 2 ∂(μ.map eval_f) :=
      (integral_map h_eval_meas.aemeasurable
        (continuous_pow 2).aestronglyMeasurable).symm
    rw [h1, hv]
    have h_mean : ∫ x, x ∂(gaussianReal (0 : ℝ) v) = 0 := integral_id_gaussianReal
    have h_var := variance_of_integral_eq_zero
      (measurable_id.aemeasurable (μ := gaussianReal (0 : ℝ) v)) h_mean
    -- h_var : Var[id; gaussianReal 0 v] = ∫ x, id x ^ 2 d(gaussianReal 0 v)
    simp only [id] at h_var
    -- h_var : Var[fun x ↦ x; ...] = ∫ x, x ^ 2 d(...)
    rw [← h_var]
    exact variance_fun_id_gaussianReal
  -- Combine: exp(½ ∫ (ω f)² dμ) = exp(½ v) = exp(v/2)
  rw [h_integral_exp, h_exp_val, h_second_moment]
  congr 1; ring

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
theorem torusGaussianMeasure_isGaussian (N : ℕ) [NeZero N]
    (mass : ℝ) (hmass : 0 < mass)
    (f : TorusTestFunction L) :
    ∫ ω : Configuration (TorusTestFunction L),
      Real.exp (ω f) ∂(torusContinuumMeasure L N mass hmass) =
    Real.exp ((1 / 2) * torusEmbeddedTwoPoint L N mass hmass f f) := by
  -- Abbreviations
  set a := circleSpacing L N
  set ha := circleSpacing_pos L N
  set T := latticeCovariance 2 N a mass ha hmass
  set μ_lat := latticeGaussianMeasure 2 N a mass ha hmass
  set g := latticeTestFn L N f
  -- Step 1: Unfold torusContinuumMeasure as pushforward and apply integral_map
  -- torusContinuumMeasure = Measure.map (torusEmbedLift L N) μ_lat
  change ∫ ω, Real.exp (ω f) ∂(Measure.map (torusEmbedLift L N) μ_lat) =
    Real.exp ((1 / 2) * torusEmbeddedTwoPoint L N mass hmass f f)
  have h_meas := torusEmbedLift_measurable L N
  rw [integral_map h_meas.aemeasurable]
  · -- Step 2: Rewrite integrand using torusEmbedLift_eval_eq
    -- ∫ φ, exp((torusEmbedLift φ) f) dμ_lat = ∫ φ, exp(φ g) dμ_lat
    have h_eval : ∀ φ : Configuration (FinLatticeField 2 N),
        (torusEmbedLift L N φ) f = φ g :=
      fun φ => torusEmbedLift_eval_eq L N f φ
    simp_rw [h_eval]
    -- Step 3: Relate to MGF
    -- ∫ φ, exp(φ g) dμ_lat = mgf (fun φ => φ g) μ_lat 1
    have h_mgf : ∫ φ : Configuration (FinLatticeField 2 N),
        Real.exp (φ g) ∂μ_lat =
        ProbabilityTheory.mgf (fun φ : Configuration (FinLatticeField 2 N) => φ g) μ_lat 1 := by
      simp only [ProbabilityTheory.mgf, one_mul]
    rw [h_mgf]
    -- Step 4: Apply mgf_gaussianReal using pairing_is_gaussian
    have h_gauss : μ_lat.map (fun φ : Configuration (FinLatticeField 2 N) => φ g) =
        ProbabilityTheory.gaussianReal 0 (@inner ℝ ell2' _ (T g) (T g) : ℝ).toNNReal :=
      GaussianField.pairing_is_gaussian T g
    rw [ProbabilityTheory.mgf_gaussianReal h_gauss]
    -- Now goal: exp(0 * 1 + ⟨Tg,Tg⟩.toNNReal * 1^2 / 2) = exp(1/2 * twoPoint f f)
    simp only [zero_add, one_pow, mul_one]
    -- Step 5: Match the RHS
    -- torusEmbeddedTwoPoint f f = ∫ (ω f)*(ω f) d(torusContinuumMeasure)
    --   = ∫ (φ g)^2 dμ_lat  (by torusEmbeddedTwoPoint_eq_lattice_second_moment)
    --   = ⟨Tg, Tg⟩  (by lattice_second_moment_eq_inner)
    have h_two_pt : torusEmbeddedTwoPoint L N mass hmass f f =
        @inner ℝ ell2' _ (T g) (T g) := by
      rw [torusEmbeddedTwoPoint_eq_lattice_second_moment L N mass hmass f,
          lattice_second_moment_eq_inner L N mass hmass g]
    rw [h_two_pt]
    congr 1
    rw [Real.coe_toNNReal _ real_inner_self_nonneg]
    ring
  · -- Measurability of ω ↦ exp(ω f)
    exact (Real.measurable_exp.comp (configuration_eval_measurable f)).aestronglyMeasurable

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
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
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
private theorem torus_configuration_neg_measurable :
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
  have hneg_meas := torus_configuration_neg_measurable L
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
  have hneg_meas := torus_configuration_neg_measurable L
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
    change ∫ ω, (f : Configuration (TorusTestFunction L) → ℝ) (-ω) ∂(μ_seq n) =
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
theorem torusGaussianLimit_fullConvergence
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
        atTop (nhds (∫ ω, g ω ∂μ)) := by
  intro g hg_cont hg_bdd
  -- Use the "unique subsequential limit ⟹ convergence" theorem.
  -- For any reindexing ns : ℕ → ℕ with ns → ∞, we extract a further
  -- subsequence converging to ∫ g dμ, using Prokhorov + Gaussian uniqueness.
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  -- Apply Prokhorov to the reindexed measures ν_{ns(n)+1}
  haveI : PolishSpace (Configuration (TorusTestFunction L)) :=
    configuration_torus_polish L
  haveI : BorelSpace (Configuration (TorusTestFunction L)) :=
    configuration_torus_borelSpace L
  obtain ⟨ψ, ν', hψ_mono, hν'_prob, hν'_conv⟩ := prokhorov_sequential
    (fun n => torusContinuumMeasure L (ns n + 1) mass hmass)
    (fun n => torusContinuumMeasure_isProbability L (ns n + 1) mass hmass)
    (fun ε hε => by
      obtain ⟨K, hK_compact, hK_bound⟩ :=
        torusContinuumMeasures_tight L mass hmass ε hε
      exact ⟨K, hK_compact, fun n => hK_bound (ns n + 1)⟩)
  haveI := hν'_prob
  -- The subsequential limit ν' is Gaussian
  have hν'_gauss : ∀ f : TorusTestFunction L,
      ∫ ω : Configuration (TorusTestFunction L),
        Real.exp (ω f) ∂ν' =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂ν') :=
    torusGaussianLimit_isGaussian L
      (fun n => torusContinuumMeasure L (ns (ψ n) + 1) mass hmass)
      (fun n => torusContinuumMeasure_isProbability L (ns (ψ n) + 1) mass hmass)
      (fun n f => by
        rw [torusGaussianMeasure_isGaussian L (ns (ψ n) + 1) mass hmass f]
        congr 1; congr 1; simp only [torusEmbeddedTwoPoint]
        congr 1; funext ω; ring)
      ν' hν'_conv
  -- The covariance of ν' equals the continuum Green's function
  have hν'_cov : ∀ f : TorusTestFunction L,
      ∫ ω : Configuration (TorusTestFunction L), (ω f) ^ 2 ∂ν' =
      torusContinuumGreen L mass hmass f f :=
    fun f => torusLimit_covariance_eq L mass hmass ν'
      (fun n => ns (ψ n))
      (hns.comp hψ_mono.tendsto_atTop)
      hν'_conv f
  -- By Gaussian uniqueness: ν' = μ
  have hν'_eq_μ : ν' = μ :=
    gaussian_measure_unique_of_covariance L ν' μ hν'_gauss hμ_gauss
      (fun f => by rw [hν'_cov f, hcov f])
  -- The integrals converge along ψ
  exact ⟨ψ, by rw [← hν'_eq_μ]; exact hν'_conv g hg_cont hg_bdd⟩

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
    fun f => torusLimit_covariance_eq L mass hmass μ φ hφ_mono.tendsto_atTop hconv f
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
