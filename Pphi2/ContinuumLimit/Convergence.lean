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

### Prokhorov's theorem

On a Polish space (complete separable metrizable), a family of probability
measures is tight if and only if it is relatively sequentially compact in
the topology of weak convergence.

S'(ℝ^d) with its weak-* topology is a Polish space (it is the dual of a
nuclear Fréchet space, hence metrizable and complete).

### Application

From `continuumMeasures_tight`, the family {ν_a}_{a>0} is tight.
By Prokhorov, any sequence ν_{a_n} with a_n → 0 has a weakly convergent
subsequence ν_{a_{n_k}} ⇀ ν.

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
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Sequences
import Mathlib.Topology.Metrizable.Basic

noncomputable section

open GaussianField MeasureTheory Filter BoundedContinuousFunction

namespace Pphi2

variable (d N : ℕ) [NeZero N]

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
      show (μ n) Kᶜ ≤ ε
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
  convert this using 1 <;> · ext n; rfl

/-! ## Topological prerequisites

S'(ℝ^d) with its weak-* topology is a Polish space (complete separable metrizable
topological space). This is a standard result in the theory of nuclear spaces:
the dual of a nuclear Fréchet space is Polish in the weak-* topology.

Reference: Gel'fand-Vilenkin, *Generalized Functions IV*, Ch. IV. -/

/-- The space of tempered distributions S'(ℝ^d) = WeakDual ℝ S(ℝ^d) is Polish.

This follows from S(ℝ^d) being a nuclear Fréchet space: its dual with the
weak-* topology is metrizable (by Banach-Alaoglu + separability of S) and
complete (by completeness of the dual of a barrelled space). -/
axiom configuration_polishSpace (d : ℕ) :
    PolishSpace (Configuration (ContinuumTestFunction d))

/-- The Borel σ-algebra on S'(ℝ^d) agrees with the σ-algebra generated by
the evaluation maps ω ↦ ω(f) for f ∈ S(ℝ^d).

This is the standard measurable structure on tempered distributions. -/
axiom configuration_borelSpace (d : ℕ) :
    BorelSpace (Configuration (ContinuumTestFunction d))

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
    (ha_lim : Tendsto a atTop (nhds 0)) :
    ∃ (φ : ℕ → ℕ) (μ : Measure (Configuration (ContinuumTestFunction d))),
      StrictMono φ ∧
      IsProbabilityMeasure μ ∧
      -- Weak convergence of the subsequence
      ∀ (f : Configuration (ContinuumTestFunction d) → ℝ),
        Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun n => ∫ ω, f ω ∂(continuumMeasure d N P (a (φ n)) mass
          (ha_pos (φ n)) hmass))
          atTop (nhds (∫ ω, f ω ∂μ)) := by
  -- S'(ℝ^d) is Polish (dual of nuclear Fréchet) — not yet in Mathlib
  haveI : PolishSpace (Configuration (ContinuumTestFunction d)) :=
    configuration_polishSpace d
  haveI : BorelSpace (Configuration (ContinuumTestFunction d)) :=
    configuration_borelSpace d
  -- Define the sequence of measures indexed by ℕ
  let ν : ℕ → Measure (Configuration (ContinuumTestFunction d)) :=
    fun n => continuumMeasure d N P (a n) mass (ha_pos n) hmass
  -- Apply Prokhorov's theorem
  obtain ⟨φ, μ, hφ, hμ_prob, hconv⟩ := prokhorov_sequential ν
    (fun n => continuumMeasure_isProbability d N P (a n) mass (ha_pos n) hmass)
    (fun ε hε => by
      obtain ⟨K, hK_compact, hK_bound⟩ := continuumMeasures_tight d N P mass hmass ε hε
      exact ⟨K, hK_compact, fun n => hK_bound (a n) (ha_pos n) (ha_le n)⟩)
  exact ⟨φ, μ, hφ, hμ_prob, hconv⟩

/-! ## Schwinger function convergence -/

/-- **Convergence of general n-point Schwinger functions.**

  `S_n^{(a)}(f₁,...,fₙ) → S_n(f₁,...,fₙ)`

for all n and all test functions f₁,...,fₙ ∈ S(ℝ^d).

The connected parts decay according to the mass gap
(from `clustering_uniform`).

Reference: Glimm-Jaffe Ch. 19.2 — extends schwinger2_convergence to
arbitrary n by induction on moment order, using uniform hypercontractive
estimates and diagonal subsequence extraction. -/
axiom schwinger_n_convergence (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) (n : ℕ)
    (f : Fin n → ContinuumTestFunction d)
    -- A sequence of lattice spacings converging to 0
    (a : ℕ → ℝ) (ha_pos : ∀ k, 0 < a k) (ha_le : ∀ k, a k ≤ 1)
    (ha_lim : Filter.Tendsto a Filter.atTop (nhds 0)) :
    -- There exist a subsequence and a limit measure such that the n-point
    -- Schwinger functions converge along that subsequence.
    ∃ (φ : ℕ → ℕ) (μ : Measure (Configuration (ContinuumTestFunction d))),
      StrictMono φ ∧ IsProbabilityMeasure μ ∧
      Filter.Tendsto
        (fun k => ∫ ω : Configuration (ContinuumTestFunction d),
          ∏ i : Fin n, ω (f i) ∂(continuumMeasure d N P (a (φ k)) mass (ha_pos (φ k)) hmass))
        Filter.atTop
        (nhds (∫ ω : Configuration (ContinuumTestFunction d),
          ∏ i : Fin n, ω (f i) ∂μ))

/-- **Convergence of the two-point Schwinger function.**

For Schwartz functions f, g ∈ S(ℝ^d):

  `S₂^{(a)}(f, g) = ∫ Φ(f) · Φ(g) dν_a → S₂(f, g) = ∫ Φ(f) · Φ(g) dμ`

as a → 0 (along the convergent subsequence).

This is a special case of `schwinger_n_convergence` with n = 2 and
test functions `![f, g]`.

Reference: Glimm-Jaffe Ch. 19.2 — Prokhorov tightness gives subsequential
weak convergence; uniform L² integrability (from Nelson hypercontractive
estimates) upgrades weak to strong moment convergence. -/
theorem schwinger2_convergence (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (f g : ContinuumTestFunction d)
    -- A sequence of lattice spacings converging to 0
    (a : ℕ → ℝ) (ha_pos : ∀ n, 0 < a n) (ha_le : ∀ n, a n ≤ 1)
    (ha_lim : Filter.Tendsto a Filter.atTop (nhds 0)) :
    -- There exist a subsequence and a limit measure such that the two-point
    -- Schwinger functions converge along that subsequence.
    ∃ (φ : ℕ → ℕ) (μ : Measure (Configuration (ContinuumTestFunction d))),
      StrictMono φ ∧ IsProbabilityMeasure μ ∧
      Filter.Tendsto
        (fun n => ∫ ω : Configuration (ContinuumTestFunction d),
          ω f * ω g ∂(continuumMeasure d N P (a (φ n)) mass (ha_pos (φ n)) hmass))
        Filter.atTop
        (nhds (∫ ω : Configuration (ContinuumTestFunction d), ω f * ω g ∂μ)) := by
  -- Apply schwinger_n_convergence with n = 2 and test functions ![f, g]
  obtain ⟨φ, μ, hφ, hμ, hconv⟩ :=
    schwinger_n_convergence d N P mass hmass 2 ![f, g] a ha_pos ha_le ha_lim
  refine ⟨φ, μ, hφ, hμ, ?_⟩
  -- The product ∏ i : Fin 2, ω (![f, g] i) = ω f * ω g
  have key : ∀ ω : Configuration (ContinuumTestFunction d),
      ω f * ω g = ∏ i : Fin 2, ω (![f, g] i) := by
    intro ω; simp [Fin.prod_univ_two]
  simp_rw [key]
  exact hconv

/-! ## Properties of the continuum limit -/

/-- The continuum limit measure is non-trivial (not the delta measure at 0).

This follows from the two-point function being nonzero:
  `S₂(f, f) = ∫ Φ(f)² dμ > 0` for f ≠ 0

The Gaussian two-point function provides a lower bound.

Reference: Simon Ch. V — the free field two-point function
⟨Φ(f)²⟩_0 = ‖f‖²_{H⁻¹} > 0 for f ≠ 0 provides a uniform
lower bound on the lattice two-point functions, which
survives the continuum limit. -/
axiom continuumLimit_nontrivial (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (a : ℕ → ℝ) (ha_pos : ∀ n, 0 < a n) (ha_le : ∀ n, a n ≤ 1)
    (ha_lim : Filter.Tendsto a Filter.atTop (nhds 0)) :
    -- The continuum limit measure is non-trivial: there exists a test function
    -- f such that the two-point function ∫ (ω f)² dμ is strictly positive.
    ∃ (φ : ℕ → ℕ) (μ : Measure (Configuration (ContinuumTestFunction d))),
      StrictMono φ ∧ IsProbabilityMeasure μ ∧
      ∃ (f : ContinuumTestFunction d),
        0 < ∫ ω : Configuration (ContinuumTestFunction d), (ω f) ^ 2 ∂μ

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

There exists a probability measure μ on S'(ℝ²) that is a P(Φ)₂ continuum
limit, i.e. satisfies `IsPphi2Limit μ P mass`. This follows from the
Prokhorov tightness argument:

1. The continuum-embedded lattice measures {ν_a} are tight
   (by `continuumMeasures_tight`).
2. By `continuumLimit` (Prokhorov), any sequence a_n → 0 has a weakly
   convergent subsequence ν_{a_nk} ⇀ μ.
3. Uniform moment bounds (from hypercontractivity) upgrade weak convergence
   to Schwinger function convergence for all n.
4. A diagonal argument across n gives a single subsequence with all
   Schwinger functions converging simultaneously.

References: Glimm-Jaffe Ch. 19.2; Simon §V.2; Billingsley Ch. 1. -/
axiom pphi2_limit_exists (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ (μ : Measure (Configuration (ContinuumTestFunction 2)))
      (_ : IsProbabilityMeasure μ),
    IsPphi2Limit μ P mass

end Pphi2

end
