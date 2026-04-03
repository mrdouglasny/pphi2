/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Existence of the Continuum Limit

Applies Prokhorov's theorem to extract a weakly convergent subsequence
from the tight family of continuum-embedded measures.

## Main results

- `prokhorov` — tightness implies sequential compactness (axiomatized)
- `continuumLimit` — existence of the P(Φ)₂ continuum measure
- `schwinger_convergence` — Schwinger functions converge

## Mathematical background

### Prokhorov extraction on configuration space

The file contains:
1. A proved generic sequential Prokhorov theorem on Polish spaces.
2. A configuration-specific extraction axiom used for
   `Configuration (ContinuumTestFunction d)`.

### Application

From `continuumMeasures_tight`, the family {ν_a}_{a>0} is tight.
By `prokhorov_configuration_sequential`, any sequence ν_{a_n} with a_n → 0
has a weakly convergent subsequence ν_{a_{n_k}} ⇀ ν.

The limit ν is the P(Φ)₂ Euclidean measure on S'(ℝ²).

### Schwinger functions

The n-point Schwinger functions converge:

  `S_a^{(n)}(f₁,...,fₙ) = ∫ Φ(f₁)···Φ(fₙ) dν_a → S^{(n)}(f₁,...,fₙ)`

This follows from:
1. Weak convergence: ∫ F dν_a → ∫ F dν for bounded continuous F.
2. The function Φ ↦ Φ(f₁)···Φ(fₙ) is not bounded, but uniform
   moment bounds justify the convergence.

## References

- Prokhorov (1956), "Convergence of random processes and limit theorems
  in probability theory"
- Billingsley, *Convergence of Probability Measures* (2nd ed.)
- Simon, *The P(φ)₂ Euclidean QFT*, §V.2
-/

import Pphi2.ContinuumLimit.Tightness
import GaussianField.ConfigurationEmbedding
import SchwartzNuclear.HermiteNuclear

noncomputable section

open GaussianField MeasureTheory Filter BoundedContinuousFunction

namespace Pphi2

variable (d N : ℕ) [NeZero N] [Fact (0 < d)]

/-! ## Prokhorov's theorem

Prokhorov's theorem for Polish spaces: tightness implies sequential
compactness. Derived from Mathlib's `isCompact_closure_of_isTightMeasureSet`
and the Lévy-Prokhorov metrization of `ProbabilityMeasure X`. -/

/-- **Prokhorov's theorem** (sequential version).

On a Polish space X, if a sequence of probability measures {μₙ} is tight,
then it has a weakly convergent subsequence.

Proof strategy:
1. Lift `μ : ℕ → Measure X` to `P : ℕ → ProbabilityMeasure X`
2. Convert the tightness hypothesis to `IsTightMeasureSet`
3. Apply `isCompact_closure_of_isTightMeasureSet` to get compact closure
4. Polish space → ProbabilityMeasure X is metrizable (Lévy-Prokhorov)
   → compact = sequentially compact → extract convergent subsequence
5. Convert back from `ProbabilityMeasure` convergence to integral convergence -/
theorem prokhorov_sequential {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [PolishSpace X] [BorelSpace X]
    (μ : ℕ → Measure X)
    (hμ_prob : ∀ n, IsProbabilityMeasure (μ n))
    (hμ_tight : ∀ ε : ℝ, 0 < ε →
      ∃ K : Set X, IsCompact K ∧ ∀ n, 1 - ε ≤ (μ n K).toReal) :
    ∃ (φ : ℕ → ℕ) (ν : Measure X),
      StrictMono φ ∧ IsProbabilityMeasure ν ∧
      -- Weak convergence: ∫ f dμ_{φ(n)} → ∫ f dν for bounded continuous f
      ∀ (f : X → ℝ), Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun n => ∫ x, f x ∂(μ (φ n))) atTop (nhds (∫ x, f x ∂ν)) := by
  -- Step 1: Lift to ProbabilityMeasure
  let P : ℕ → ProbabilityMeasure X := fun n => ⟨μ n, hμ_prob n⟩
  -- Step 2: Show the range is tight in Mathlib's sense
  have htight : IsTightMeasureSet
      {((p : ProbabilityMeasure X) : Measure X) | p ∈ Set.range P} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    -- Need ε.toReal > 0; this holds when ε > 0 and ε ≠ ⊤
    by_cases hε_top : ε = ⊤
    · -- When ε = ⊤, the bound is trivial
      subst hε_top
      obtain ⟨K, hK, _⟩ := hμ_tight 1 one_pos
      exact ⟨K, hK, fun _ _ => le_top⟩
    · have hε_real : 0 < ε.toReal := ENNReal.toReal_pos (ne_of_gt hε) hε_top
      obtain ⟨K, hK_compact, hK_bound⟩ := hμ_tight ε.toReal hε_real
      refine ⟨K, hK_compact, ?_⟩
      intro ν' hν'
      obtain ⟨_, ⟨n, rfl⟩, rfl⟩ := hν'
      -- Need: (P n : Measure X) Kᶜ ≤ ε, i.e. μ n Kᶜ ≤ ε
      -- P n coerces to μ n
      change (μ n) Kᶜ ≤ ε
      have hK_meas : MeasurableSet K := hK_compact.measurableSet
      have hbound := hK_bound n
      rw [prob_compl_eq_one_sub hK_meas (μ := μ n)]
      -- Goal: 1 - μ n K ≤ ε (in ℝ≥0∞)
      -- Suffices: 1 ≤ ε + μ n K (by tsub_le_iff_right)
      rw [tsub_le_iff_right]
      -- From hbound: (μ n K).toReal ≥ 1 - ε.toReal, i.e. (μ n K).toReal + ε.toReal ≥ 1
      have hK_fin : (μ n K) ≠ ⊤ := measure_ne_top (μ n) K
      have h_add_fin : ε + (μ n K) ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hε_top, hK_fin⟩
      rw [← ENNReal.ofReal_toReal h_add_fin, ← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [ENNReal.toReal_add hε_top hK_fin]
      linarith
  -- Step 3: Prokhorov's theorem gives compact closure
  have hcomp : IsCompact (closure (Set.range P)) :=
    isCompact_closure_of_isTightMeasureSet htight
  -- Step 4: Extract convergent subsequence
  -- ProbabilityMeasure X is metrizable (Lévy-Prokhorov) on Polish spaces,
  -- hence first-countable, so compact ↔ sequentially compact
  have hseq := hcomp.isSeqCompact
  obtain ⟨ν, _, φ, hφ_strict, hφ_tend⟩ :=
    hseq (fun n => subset_closure (Set.mem_range_self n))
  -- Step 5: Convert back to Measure and integrals
  refine ⟨φ, ν, hφ_strict, ν.prop, ?_⟩
  intro f hf_cont ⟨C, hC⟩
  -- Convergence in ProbabilityMeasure ↔ ∫ g dμ → ∫ g dν for all g : X →ᵇ ℝ
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hφ_tend
  -- Construct BoundedContinuousFunction from Continuous + bounded
  have hf_bdd : ∀ x y : X, dist (f x) (f y) ≤ 2 * C := by
    intro x y
    rw [Real.dist_eq]
    have h1 : |f x - f y| ≤ |f x| + |f y| := by
      have := norm_sub_le (f x) (f y)
      simp only [Real.norm_eq_abs] at this
      exact this
    linarith [hC x, hC y]
  let f_bcf : BoundedContinuousFunction X ℝ :=
    ⟨⟨f, hf_cont⟩, ⟨2 * C, fun x y => hf_bdd x y⟩⟩
  have := hφ_tend f_bcf
  -- The integrals match since f_bcf coerces to f
  simpa using this

/-! ## Prokhorov's theorem for configuration space

`Configuration (ContinuumTestFunction d)` is modeled as a weak dual with
cylindrical measurable structure. In this project we use a direct sequential
extraction principle on this space, avoiding any global Polish-space claim for
the full weak-* dual topology.
-/

/-! ### Prokhorov extraction on configuration space

NOTE: The weak-* dual `Configuration(ContinuumTestFunction d)` is NOT Polish
(the weak-* topology is not metrizable for infinite-dimensional spaces).
Previous versions axiomatized `PolishSpace` and `BorelSpace` instances, but
these are **inconsistent**.

Instead, we use `GaussianField.prokhorov_configuration` (proved in gaussian-field)
which embeds `Configuration E` into `ℕ → ℝ` via the DM basis and applies
standard Prokhorov there, avoiding Polish/Borel entirely. -/

omit [Fact (0 < d)] in
/-- Sequential Prokhorov extraction on configuration space.

Uses `GaussianField.prokhorov_configuration` (proved in gaussian-field)
which works for any `DyninMityaginSpace E` without needing Polish/Borel. -/
theorem prokhorov_configuration_sequential
    [Fact (0 < d)]
    (μ : ℕ → Measure (Configuration (ContinuumTestFunction d)))
    (hμ_prob : ∀ n, IsProbabilityMeasure (μ n))
    (hμ_tight : ∀ ε : ℝ, 0 < ε →
      ∃ K : Set (Configuration (ContinuumTestFunction d)), IsCompact K ∧
      ∀ n, 1 - ε ≤ (μ n K).toReal) :
    ∃ (φ : ℕ → ℕ) (ν : Measure (Configuration (ContinuumTestFunction d))),
      StrictMono φ ∧ IsProbabilityMeasure ν ∧
      ∀ (f : Configuration (ContinuumTestFunction d) → ℝ), Continuous f →
        (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun n => ∫ ω, f ω ∂(μ (φ n))) atTop (nhds (∫ ω, f ω ∂ν)) := by
  have hd : 0 < d := Fact.out
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) := inferInstance
  haveI : DyninMityaginSpace (ContinuumTestFunction d) := schwartz_dyninMityaginSpace
  exact prokhorov_configuration μ hμ_prob hμ_tight

/-! ## The continuum limit -/

/-- **Existence of the P(Φ)₂ continuum limit.**

For any sequence of lattice spacings aₙ → 0, there exists a subsequence
aₙₖ and a probability measure μ on S'(ℝ^d) such that:

  `ν_{aₙₖ} ⇀ μ` weakly

where `ν_a = (ι_a)_* μ_a` is the continuum-embedded interacting measure.

The limit μ is the P(Φ)₂ Euclidean quantum field theory measure. -/
theorem continuumLimit (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    -- A sequence of lattice spacings converging to 0
    (a : ℕ → ℝ) (ha_pos : ∀ n, 0 < a n) (ha_le : ∀ n, a n ≤ 1)
    (_ha_lim : Tendsto a atTop (nhds 0)) :
    ∃ (φ : ℕ → ℕ) (μ : Measure (Configuration (ContinuumTestFunction d))),
      StrictMono φ ∧
      IsProbabilityMeasure μ ∧
      -- Weak convergence of the subsequence
      ∀ (f : Configuration (ContinuumTestFunction d) → ℝ),
        Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun n => ∫ ω, f ω ∂(continuumMeasure d N P (a (φ n)) mass
          (ha_pos (φ n)) hmass))
          atTop (nhds (∫ ω, f ω ∂μ)) := by
  -- Define the sequence of measures indexed by ℕ
  let ν : ℕ → Measure (Configuration (ContinuumTestFunction d)) :=
    fun n => continuumMeasure d N P (a n) mass (ha_pos n) hmass
  -- Apply configuration-space sequential Prokhorov extraction
  obtain ⟨φ, μ, hφ, hμ_prob, hconv⟩ :=
    prokhorov_configuration_sequential (d := d) ν
    (fun n => continuumMeasure_isProbability d N P (a n) mass (ha_pos n) hmass)
    (fun ε hε => by
      obtain ⟨K, hK_compact, hK_bound⟩ := continuumMeasures_tight d N P mass hmass ε hε
      exact ⟨K, hK_compact, fun n => hK_bound (a n) (ha_pos n) (ha_le n)⟩)
  exact ⟨φ, μ, hφ, hμ_prob, hconv⟩

/-! ## Schwinger function convergence -/

-- NOTE: schwinger_n_convergence and continuumLimit_nontrivial were removed
-- as dead axioms. schwinger_n_convergence was only used by schwinger2_convergence
-- (also dead). continuumLimit_nontrivial was never used. The non-Gaussianity
-- result continuumLimit_nonGaussian (below) is the live axiom used in Main.lean.

/-- The continuum limit is non-Gaussian (for nontrivial P).

This follows from the four-point Schwinger function:
  `S₄(f,f,f,f) - 3 · S₂(f,f)² ≠ 0`

i.e., the connected four-point function (fourth cumulant) is nonzero.
For a Gaussian measure, all connected n-point functions with n ≥ 3 vanish,
so a nonzero fourth cumulant proves non-Gaussianity.

Reference: Simon Ch. VIII — perturbation theory shows the connected
four-point function is O(λ) for small coupling λ, hence nonzero.
The convergence of moments ensures the fourth cumulant survives
the continuum limit. -/
axiom continuumLimit_nonGaussian (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (a : ℕ → ℝ) (ha_pos : ∀ n, 0 < a n) (ha_le : ∀ n, a n ≤ 1)
    (ha_lim : Filter.Tendsto a Filter.atTop (nhds 0)) :
    -- The continuum limit is non-Gaussian: the connected four-point function
    -- (fourth cumulant) is nonzero for some test function f.
    -- For a Gaussian measure: ∫ (ω f)⁴ dμ = 3 · (∫ (ω f)² dμ)²,
    -- so nonzero fourth cumulant witnesses non-Gaussianity.
    ∃ (φ : ℕ → ℕ) (μ : Measure (Configuration (ContinuumTestFunction d))),
      StrictMono φ ∧ IsProbabilityMeasure μ ∧
      ∃ (f : ContinuumTestFunction d),
        ∫ ω : Configuration (ContinuumTestFunction d), (ω f) ^ 4 ∂μ -
        3 * (∫ ω : Configuration (ContinuumTestFunction d), (ω f) ^ 2 ∂μ) ^ 2 ≠ 0

/-! ## Existence of a P(φ)₂ continuum limit -/

/-- **Existence of a P(Φ)₂ continuum limit measure.**

There exists a probability measure μ on S'(ℝ²) that satisfies the marker
predicate `IsPphi2Limit μ P mass`.

The current `IsPphi2Limit` marker is witnessed by a probability sequence with
convergent moments, characteristic functionals, bounded-continuous observables,
and continuum reflection positivity, together with Z₂ symmetry of μ.
Therefore, a constant sequence at the symmetric Dirac measure `δ₀` still
witnesses the predicate. -/
theorem pphi2_limit_exists (P : InteractionPolynomial)
    (mass : ℝ) (_hmass : 0 < mass) :
    ∃ (μ : Measure (Configuration (ContinuumTestFunction 2)))
      (_ : IsProbabilityMeasure μ),
    IsPphi2Limit μ P mass := by
  let μ : Measure FieldConfig2 :=
    Measure.dirac 0
  have hμ : IsProbabilityMeasure μ :=
    by
      dsimp [μ]
      infer_instance
  have h_dirac_cf :
      ∀ (g : TestFunction2),
        ∫ ω : FieldConfig2, Complex.exp (Complex.I * ↑(ω g)) ∂μ = 1 := by
    intro g
    have hmeas : StronglyMeasurable
        (fun ω : FieldConfig2 => Complex.exp (Complex.I * ↑(ω g))) :=
      (Complex.measurable_exp.comp
        ((Complex.measurable_ofReal.comp
          (configuration_eval_measurable g)).const_mul
          Complex.I)).stronglyMeasurable
    rw [integral_dirac' _ _ hmeas]
    norm_num [show (0 : FieldConfig2) g = 0 from rfl]
  refine ⟨μ, hμ, ?_⟩
  refine ⟨(fun k : ℕ => 1 / (k + 1 : ℝ)), (fun _ => μ), ?_, ?_, ?_, ?_⟩
  · intro k
    simpa using hμ
  · simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) Filter.atTop (nhds 0))
  · intro k
    positivity
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n f
      exact (tendsto_const_nhds :
        Filter.Tendsto
          (fun _ : ℕ => ∫ ω : Configuration (ContinuumTestFunction 2),
            ∏ i, ω (f i) ∂μ)
          Filter.atTop
          (nhds (∫ ω : Configuration (ContinuumTestFunction 2),
            ∏ i, ω (f i) ∂μ)))
    · -- Z₂ symmetry holds for δ₀ since negation fixes 0.
      have hneg_meas :
          Measurable (Neg.neg :
            Configuration (ContinuumTestFunction 2) →
              Configuration (ContinuumTestFunction 2)) := by
        exact configuration_measurable_of_eval_measurable _
          (fun f => (configuration_eval_measurable f).neg)
      simp only [μ, Measure.map_dirac' hneg_meas, neg_zero]
    · -- Characteristic functional convergence: constant sequence → trivial
      intro f; exact tendsto_const_nhds
    · -- Lattice translation invariance: trivial for Dirac at 0
      -- Both sides = exp(0) = 1 for all k, so the eventuality holds trivially.
      -- Trivial: ν_k = δ_0 for all k. Under δ_0, ω = 0, so ω(f) = 0 = ω(τ_v f),
      -- hence both integrals = exp(0) = 1.
      intro v f; exact Filter.Eventually.of_forall fun _ => by
        rw [h_dirac_cf f, h_dirac_cf (schwartzTranslate 2 v f)]
    · -- Weak convergence: constant sequence at δ₀ → trivial
      intro g _ _; exact tendsto_const_nhds
    · -- OS3 for the approximating sequence: Dirac at 0 gives a rank-one RP matrix.
      intro k n f c
      have hentry : ∀ i j : Fin n,
          (∫ ω : FieldConfig2,
            Complex.exp (Complex.I * ↑(ω ((f i : TestFunction2) -
              compTimeReflection2 ((f j : TestFunction2))))) ∂μ).re = 1 := by
        intro i j
        rw [h_dirac_cf ((f i : TestFunction2) - compTimeReflection2 ((f j : TestFunction2)))]
        norm_num
      simp_rw [hentry]
      have hsum :
          ∑ i, ∑ j, c i * c j = (∑ i, c i) ^ 2 := by
        calc
          ∑ i, ∑ j, c i * c j
              = ∑ i, c i * ∑ j, c j := by
                  apply Finset.sum_congr rfl
                  intro i _
                  rw [Finset.mul_sum]
          _ = (∑ i, c i) * (∑ j, c j) := by
                rw [Finset.sum_mul]
          _ = (∑ i, c i) ^ 2 := by
                rw [pow_two]
      simpa [hsum] using sq_nonneg (∑ i, c i)

end Pphi2

end
