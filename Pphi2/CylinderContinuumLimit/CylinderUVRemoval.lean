/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cylinder UV Removal: Λ → ∞

Removes the UV cutoff Λ from the cylinder interacting measure,
constructing the UV limit measure μ_T for each fixed temporal extent T.

## Main results

- `cylinderUVLimitMeasure` — the limit measure as Λ → ∞
- `cylinderUVLimitMeasure_isProbability` — it is a probability measure
- `cylinderUVLimit_weakLimit` — it is the weak limit of μ_{Λ,T}

## Mathematical background

The UV limit exists because Wick ordering removes the logarithmic
divergence of the bare interaction. Concretely:

1. V_{Λ,T} converges in L²(μ_free) as Λ → ∞ because the Wick-ordered
   integrand :P(φ_Λ):_{c_Λ} has controlled differences: the variance
   of V_{Λ',T} - V_{Λ,T} involves only spatial modes |k| ∈ (Λ, Λ'],
   which are independent under μ_free and whose Wick-ordered contribution
   vanishes by the renormalization cancellation.

2. L² convergence of V implies L¹ convergence of exp(-V) (by dominated
   convergence + uniform lower bound), hence weak convergence of measures.

This is the cylinder analogue of the lattice continuum limit (a → 0),
but simpler: the UV cutoff Λ is a Fourier mode truncation, not a
lattice spacing, so no embedding map is needed.

## References

- Simon, *The P(φ)₂ Euclidean QFT*, Ch. VIII (UV cutoff removal)
- Glimm-Jaffe, *Quantum Physics*, §19.2
-/

import Pphi2.CylinderContinuumLimit.CylinderHypercontractivity

open GaussianField MeasureTheory

noncomputable section

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-- **Integrability of (ω f)^2 under the cutoff interacting measure.**

Since the interacting measure μ_{Λ,T} = (1/Z)·exp(-V)·dμ_free has density bounded
by exp(B)/Z ≤ exp(B) w.r.t. the free Gaussian measure (where V ≥ -B), and (ω f)^2 is
integrable under μ_free (by Gaussian all-moments / pairing_memLp at p = 2), the function
(ω f)^2 is also integrable under μ_{Λ,T}.

This is used in the truncation argument for `cylinderUVLimit_second_moment_finite`. -/
theorem cylinderInteracting_sq_integrable
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    (f : CylinderTestFunction L) :
    Integrable (fun ω : Configuration (CylinderTestFunction L) => (ω f) ^ 2)
      (cylinderInteractingMeasure L P Λ T mass hT hmass) := by
  -- Setup: abbreviations for the key objects
  set V := cylinderV L P Λ T mass hT hmass with hV_def
  set μ := cylinderFreeMeasure L mass hmass with hμ_def
  set bw := interactingBoltzmannWeight V with hbw_def
  set Z := interactingPartitionFunction V μ with hZ_def
  -- Key properties of V
  have hV_meas : Measurable V :=
    cylinderInteractionFunctional_measurable L P Λ T mass hT hmass
  have hV_below : ∃ B : ℝ, ∀ ω, V ω ≥ -B :=
    cylinderInteractionFunctional_bounded_below L P Λ T mass hT hmass
  -- Z > 0
  have hZ_pos : 0 < Z := interactingPartitionFunction_pos V μ hV_meas hV_below
  -- Step 1: Reduce from interacting measure = (Z⁻¹) • μ.withDensity(bw) to withDensity
  -- The interacting measure is (ENNReal.ofReal Z)⁻¹ • μ.withDensity(ENNReal.ofReal ∘ bw)
  suffices h : Integrable (fun ω : Configuration (CylinderTestFunction L) => (ω f) ^ 2)
      (μ.withDensity (fun ω => ENNReal.ofReal (bw ω))) by
    change Integrable _ (interactingMeasure V μ)
    simp only [interactingMeasure]
    exact h.smul_measure (ENNReal.inv_ne_top.mpr ((ENNReal.ofReal_pos.mpr hZ_pos).ne'))
  -- Step 2: Reduce withDensity to multiplicative weight under free Gaussian
  -- Using integrable_withDensity_iff
  have hbw_meas : Measurable (fun ω : Configuration (CylinderTestFunction L) =>
      ENNReal.ofReal (bw ω)) :=
    interactingBoltzmannWeight_ennreal_measurable V hV_meas
  apply (integrable_withDensity_iff hbw_meas
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  -- Simplify toReal ∘ ofReal since bw > 0
  have hbw_simp : ∀ ω : Configuration (CylinderTestFunction L),
      (ENNReal.ofReal (bw ω)).toReal = bw ω :=
    fun ω => ENNReal.toReal_ofReal (le_of_lt (interactingBoltzmannWeight_pos V ω))
  simp_rw [hbw_simp]
  -- Goal: Integrable (fun ω => (ω f)^2 * bw ω) μ
  -- Step 3: Get Gaussian integrability of (ω f)²
  -- From pairing_memLp at p = 2: ω f ∈ L²(μ_free), so (ω f)² is integrable
  have h_sq_int : Integrable (fun ω : Configuration (CylinderTestFunction L) =>
      (ω f) ^ 2) μ := by
    have h2 : MemLp (fun ω : Configuration (CylinderTestFunction L) => ω f)
        2 μ := by
      exact_mod_cast pairing_memLp (cylinderMassOperator L mass hmass) f 2
    exact h2.integrable_sq
  -- Step 4: Dominate (ω f)² * bw ω by (ω f)² * exp(B) pointwise
  -- Since V ≥ -B, we have bw ω = exp(-V ω) ≤ exp(B)
  obtain ⟨B, hB⟩ := hV_below
  apply (h_sq_int.mul_const (Real.exp B)).mono
  · -- AEStronglyMeasurable of (ω f)² * bw ω
    exact ((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable.mul
      hV_meas.neg.exp.aestronglyMeasurable
  · -- Pointwise norm bound: ‖(ω f)² * bw ω‖ ≤ ‖(ω f)² * exp(B)‖
    exact Filter.Eventually.of_forall fun ω => by
      simp only [Real.norm_eq_abs]
      have h1 : 0 ≤ (ω f) ^ 2 := sq_nonneg _
      have h2 : 0 < bw ω := interactingBoltzmannWeight_pos V ω
      have h3 : bw ω ≤ Real.exp B := by
        change Real.exp (-(V ω)) ≤ Real.exp B
        exact Real.exp_le_exp_of_le (by linarith [hB ω])
      rw [abs_of_nonneg (mul_nonneg h1 (le_of_lt h2)),
          abs_of_nonneg (mul_nonneg h1 (le_of_lt (Real.exp_pos B)))]
      exact mul_le_mul_of_nonneg_left h3 h1

/-! ## UV limit measure

The UV limit measure μ_T is the weak limit of the cutoff measures μ_{Λ,T}
as Λ → ∞. Its existence follows from:
- Uniform second moment bounds (from `cylinderInteracting_second_moment_bound`)
- Tightness via Mitoma criterion (nuclear test function space)
- Prokhorov's theorem on the Polish configuration space -/

/-- **UV limit measure** on the cylinder for fixed temporal extent T.

This is the P(φ)₂ interacting measure with UV cutoff removed:
  `μ_T = lim_{Λ→ ∞} (1/Z_{Λ,T}) exp(-V_{Λ,T}) dμ_free`

The limit exists because:
1. Uniform moment bounds (from hypercontractivity + density transfer)
   give tightness of {μ_{Λ,T}}_Λ
2. Prokhorov on the Polish configuration space extracts a convergent
   subsequence
3. The limit is independent of subsequence (by L² convergence of V_{Λ,T}) -/
axiom cylinderUVLimitMeasure
    (P : InteractionPolynomial) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    @Measure (Configuration (CylinderTestFunction L)) instMeasurableSpaceConfiguration

/-- The UV limit measure is a probability measure. -/
axiom cylinderUVLimitMeasure_isProbability
    (P : InteractionPolynomial) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    @IsProbabilityMeasure (Configuration (CylinderTestFunction L))
      instMeasurableSpaceConfiguration
      (cylinderUVLimitMeasure L P T mass hT hmass)

/-- The UV limit measure is the weak limit of the cutoff measures.

For all bounded continuous functions g on Configuration(CylinderTestFunction L):
  `∫ g dμ_{Λ,T} → ∫ g dμ_T` as Λ → ∞ -/
axiom cylinderUVLimit_weakLimit
    (P : InteractionPolynomial) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    (g : Configuration (CylinderTestFunction L) → ℝ)
    (hg_cont : Continuous g) (hg_bound : ∃ M, ∀ ω, |g ω| ≤ M) :
    Filter.Tendsto (fun Λ =>
      ∫ ω, g ω ∂(cylinderInteractingMeasure L P Λ T mass hT hmass))
    Filter.atTop
    (nhds (∫ ω, g ω ∂(cylinderUVLimitMeasure L P T mass hT hmass)))

/-! ## Properties of the UV limit -/

/-- **Absolute continuity of the UV limit measure** w.r.t. the free measure.

Each cutoff measure μ_{Λ,T} = (1/Z_{Λ,T}) exp(-V_{Λ,T}) dμ_free is absolutely
continuous w.r.t. μ_free by construction. However, absolute continuity is NOT
preserved under weak limits in general (counterexample: point masses weakly
converging to a point mass at a different location).

For P(φ)₂, the limit μ_T is absolutely continuous because:
1. The Wick-ordered densities exp(-V_{Λ,T})/Z_{Λ,T} converge in L²(μ_free)
   (by hypercontractivity + Wick renormalization cancellation)
2. L² convergence implies the limit has an L² density w.r.t. μ_free
3. Having an L² density implies absolute continuity

This is a deep analytical fact requiring L² convergence of densities
(not just weak convergence of measures), so we take it as an axiom.

**References:**
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. VIII, Theorem VIII.5
- Glimm-Jaffe, *Quantum Physics*, §19.2, density convergence -/
axiom cylinderUVLimitMeasure_absolutelyContinuous
    (P : InteractionPolynomial) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    cylinderUVLimitMeasure L P T mass hT hmass ≪
    cylinderFreeMeasure L mass hmass

/-- **Finite second moments** under the UV limit measure.

The proof uses weak convergence + truncation + monotone convergence:
1. For each M > 0, let g_M(ω) = min((ω f)², M). This is bounded and continuous.
2. By `cylinderUVLimit_weakLimit`: ∫ g_M dμ_T = lim_Λ ∫ g_M dμ_{Λ,T}
3. Since g_M ≤ (ω f)², we have ∫ g_M dμ_{Λ,T} ≤ ∫ (ω f)² dμ_{Λ,T} ≤ C
   by `cylinderInteracting_second_moment_bound`
4. Therefore ∫ g_M dμ_T ≤ C for all M
5. By monotone convergence (g_M ↑ (ω f)²), we get ∫ (ω f)² dμ_T ≤ C

**Key inputs:** `cylinderInteracting_second_moment_bound`, `cylinderUVLimit_weakLimit`
**References:** Simon, *P(φ)₂*, Ch. VIII; see also Billingsley, *Convergence of
Probability Measures*, Theorem 5.4 (Fatou for weak convergence) -/
theorem cylinderUVLimit_second_moment_finite
    (P : InteractionPolynomial) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    (f : CylinderTestFunction L) :
    ∃ C : ℝ, ∫ ω, (ω f) ^ 2
      ∂(cylinderUVLimitMeasure L P T mass hT hmass) ≤ C := by
  -- Abbreviations
  set μ_T := cylinderUVLimitMeasure L P T mass hT hmass with hμ_T_def
  set μ_Λ := fun Λ => cylinderInteractingMeasure L P Λ T mass hT hmass with hμ_Λ_def
  -- μ_T is a probability measure
  have hprob : IsProbabilityMeasure μ_T :=
    cylinderUVLimitMeasure_isProbability L P T mass hT hmass
  -- Step 1: Get uniform bound C₀ on second moments under cutoff measures
  obtain ⟨C₀, hC₀⟩ := cylinderInteracting_second_moment_bound L P T mass hT hmass f
  -- Use max C₀ 0 to ensure nonneg bound
  set C := max C₀ 0 with hC_def
  have hC_nn : (0 : ℝ) ≤ C := le_max_right _ _
  refine ⟨C, ?_⟩
  -- Step 2: Continuity of evaluation and squaring
  have heval_cont : Continuous (fun ω : Configuration (CylinderTestFunction L) => ω f) :=
    WeakDual.eval_continuous f
  have hsq_cont : Continuous (fun ω : Configuration (CylinderTestFunction L) => (ω f) ^ 2) :=
    heval_cont.pow 2
  -- Step 3: For each M : ℕ, g_M(ω) = min((ω f)², ↑M) is bounded continuous.
  -- Its integral under the UV limit measure is ≤ C.
  have htrunc_bound : ∀ M : ℕ,
      ∫ ω, min ((ω f) ^ 2) (↑M) ∂μ_T ≤ C := by
    intro M
    -- g_M is continuous and bounded
    have hgM_cont : Continuous (fun ω : Configuration (CylinderTestFunction L) =>
        min ((ω f) ^ 2) (↑M : ℝ)) := hsq_cont.min continuous_const
    have hgM_nn : ∀ ω : Configuration (CylinderTestFunction L),
        0 ≤ min ((ω f) ^ 2) (↑M : ℝ) :=
      fun ω => le_min (sq_nonneg _) (Nat.cast_nonneg M)
    have hgM_bound : ∃ B : ℝ, ∀ ω : Configuration (CylinderTestFunction L),
        |min ((ω f) ^ 2) (↑M : ℝ)| ≤ B :=
      ⟨M, fun ω => by rw [abs_of_nonneg (hgM_nn ω)]; exact min_le_right _ _⟩
    -- By weak convergence: ∫ g_M dμ_{Λ,T} → ∫ g_M dμ_T as Λ → ∞
    have hconv := cylinderUVLimit_weakLimit L P T mass hT hmass
      (fun ω => min ((ω f) ^ 2) (↑M : ℝ)) hgM_cont hgM_bound
    -- Each ∫ g_M dμ_{Λ,T} ≤ C: since 0 ≤ g_M ≤ (ω f)² pointwise, and
    -- (ω f)² is integrable under μ_{Λ,T} (by cylinderInteracting_sq_integrable),
    -- integral_mono_of_nonneg gives ∫ g_M ≤ ∫ (ω f)² ≤ C₀ ≤ C.
    have hterms_le : ∀ Λ : ℕ,
        ∫ ω, min ((ω f) ^ 2) (↑M : ℝ) ∂(μ_Λ Λ) ≤ C := fun Λ =>
      calc ∫ ω, min ((ω f) ^ 2) (↑M : ℝ) ∂(μ_Λ Λ)
          ≤ ∫ ω, (ω f) ^ 2 ∂(μ_Λ Λ) := by
            exact integral_mono_of_nonneg
              (Filter.Eventually.of_forall hgM_nn)
              (cylinderInteracting_sq_integrable L P Λ T mass hT hmass f)
              (Filter.Eventually.of_forall fun ω => min_le_left _ _)
        _ ≤ C₀ := hC₀ Λ
        _ ≤ C := le_max_left _ _
    -- By le_of_tendsto': the limit of a convergent sequence ≤ C is itself ≤ C
    exact le_of_tendsto' hconv hterms_le
  -- Step 4: Conclude from truncation bounds.
  -- If (ω f)² is not integrable, ∫ (ω f)² dμ_T = 0 by Lean convention, and 0 ≤ C.
  -- If integrable, use monotone convergence: min((ω f)², M) ↑ (ω f)² gives
  --   ∫ (ω f)² dμ_T = lim_M ∫ min((ω f)², M) dμ_T ≤ C.
  by_cases hint : Integrable (fun ω => (ω f) ^ 2) μ_T
  · -- Integrable case: monotone convergence for truncation
    have hmono_conv : Filter.Tendsto
        (fun M : ℕ => ∫ ω, min ((ω f) ^ 2) (↑M : ℝ) ∂μ_T)
        Filter.atTop (nhds (∫ ω, (ω f) ^ 2 ∂μ_T)) := by
      apply integral_tendsto_of_tendsto_of_monotone
      · -- Each g_M is integrable (bounded on probability space)
        intro n
        -- Measurability: (ω f)^2 is measurable (cylindrical σ-algebra), and min with
        -- a constant preserves measurability.
        have hgn_meas : Measurable (fun ω : Configuration (CylinderTestFunction L) =>
            min ((ω f) ^ 2) (↑n : ℝ)) :=
          (configuration_eval_measurable f).pow_const 2 |>.min measurable_const
        exact Integrable.of_bound hgn_meas.aestronglyMeasurable n
          (Filter.Eventually.of_forall fun ω => by
            rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sq_nonneg _) (Nat.cast_nonneg n))]
            exact min_le_right _ _)
      · exact hint
      · -- Monotonicity: min(x², n) ≤ min(x², m) when n ≤ m
        exact Filter.Eventually.of_forall fun ω =>
          fun n m (hnm : n ≤ m) => min_le_min_left _ (Nat.cast_le.mpr hnm)
      · -- Pointwise convergence: min(x², n) → x² as n → ∞
        -- For large enough n, n ≥ (ω f)², so min((ω f)², n) = (ω f)².
        exact Filter.Eventually.of_forall fun ω =>
          tendsto_atTop_of_eventually_const (i₀ := ⌈(ω f) ^ 2⌉₊) fun n hn => by
            rw [min_eq_left]
            exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hn)
    exact le_of_tendsto' hmono_conv htrunc_bound
  · -- Non-integrable case: Bochner integral is 0
    rw [integral_undef hint]
    exact hC_nn

/-- **Convergence of two-point Schwinger functions** as Λ → ∞.

Since `cylinderSchwinger2 L P Λ T mass hT hmass f g = ∫ ω f * ω g dμ_{Λ,T}` and
ω ↦ ω(f) · ω(g) is continuous but NOT bounded, the weak convergence axiom
`cylinderUVLimit_weakLimit` does not apply directly.

The proof requires **uniform integrability** of {ω ↦ ω(f)·ω(g)} under {μ_{Λ,T}}:
1. By Cauchy-Schwarz: |∫ ω f · ω g dμ| ≤ (∫ (ω f)² dμ)^{1/2} · (∫ (ω g)² dμ)^{1/2}
2. `cylinderInteracting_second_moment_bound` gives ∫ (ω f)² dμ_{Λ,T} ≤ C uniformly
3. Actually need: for all ε > 0, there exists M s.t. ∫_{|ω f · ω g| > M} |ω f · ω g| dμ_{Λ,T} < ε
   uniformly in Λ. This follows from uniform L² bounds via Markov/truncation.
4. Uniform integrability + weak convergence of measures implies convergence of integrals
   (Vitali convergence theorem for weak limits)

This is standard but requires Vitali's convergence theorem infrastructure.

**Key inputs:** `cylinderInteracting_second_moment_bound`, `cylinderUVLimit_weakLimit`
**References:** Billingsley, *Convergence of Probability Measures*, Theorem 5.4;
Simon, *P(φ)₂*, Ch. VIII -/
axiom cylinderUVLimit_schwinger2
    (P : InteractionPolynomial) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    (f g : CylinderTestFunction L) :
    Filter.Tendsto (fun Λ =>
      cylinderSchwinger2 L P Λ T mass hT hmass f g)
    Filter.atTop
    (nhds (∫ ω, ω f * ω g
      ∂(cylinderUVLimitMeasure L P T mass hT hmass)))

end Pphi2

end
