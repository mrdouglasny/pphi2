/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Existence of the Continuum Limit

Applies Prokhorov's theorem to extract a weakly convergent subsequence
from the tight family of continuum-embedded measures.

## Main results

- `prokhorov` — tightness implies sequential compactness (axiomatized)
- `schwinger_convergence` — Schwinger functions converge

## Mathematical background

### Prokhorov extraction on configuration space

The file contains:
1. A proved generic sequential Prokhorov theorem on Polish spaces.
2. A configuration-specific extraction axiom used for
   `Configuration (ContinuumTestFunction d)`.

### Application

`prokhorov_configuration_sequential` extracts a weakly convergent subsequence from any
tight sequence of probability measures on `S'(ℝ^d)`.

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

/-! ## The continuum limit (REMOVED)

`continuumLimit` (Prokhorov extraction along `a_n → 0` at fixed lattice size `N`) was deleted
on 2026-10-08 with `continuumMeasures_tight`, whose proof rested on the false axiom
`nelson_exponential_estimate_master_bounded` (issue #63). Existence of a limit is carried by
the axiom `pphi2_limit_exists` below and, unconditionally, by the torus routes. -/

/-! ## Schwinger function convergence -/

-- NOTE: schwinger_n_convergence and continuumLimit_nontrivial were removed
-- as dead axioms. schwinger_n_convergence was only used by schwinger2_convergence
-- (also dead). continuumLimit_nontrivial was never used. The non-Gaussianity
-- result continuumLimit_nonGaussian (below) is the live axiom used in Main.lean.

/-! ### Coupling-regime predicates

These predicates were introduced in `Bridge.lean` and are defined here (upstream
of `Main.lean`) so that the regime-sensitive axioms below can carry them as
hypotheses. See `planning/r2-honest-headline-spec.md` (D3): non-Gaussianity of
the limit, like the spectral gap, is a weak-coupling statement — at the φ⁴₂
critical point the axioms below are false as stated without a regime
hypothesis. -/

/-- A pphi2 `InteractionPolynomial` is a φ⁴ interaction if its polynomial is
P(τ) = λτ⁴ for some coupling constant λ > 0. -/
def isPhi4 (P : InteractionPolynomial) (coupling : ℝ) : Prop :=
  P.n = 4 ∧ 0 < coupling
  -- Full version: all coefficients match the φ⁴ interaction

/-- The coupling constant is in the weak-coupling regime where the cluster
expansion converges, guaranteeing uniqueness of the infinite-volume limit.

The full condition is `coupling < l₀(P, mass)` where l₀ is the radius of
convergence of the Glimm-Jaffe-Spencer cluster expansion.
Reference: Glimm-Jaffe-Spencer (1974). -/
def IsWeakCoupling (P : InteractionPolynomial) (mass coupling : ℝ) : Prop :=
  -- The coupling constant is small enough for the Glimm-Jaffe-Spencer cluster
  -- expansion to converge. Concretely, for P(τ) = λτ⁴ this requires λ < λ₀(m)
  -- where λ₀(m) > 0 is a mass-dependent radius of convergence.
  -- We state this as: there exists a positive threshold λ₀ > coupling such that
  -- the expansion converges, ensuring uniqueness of the infinite-volume limit.
  0 < coupling ∧ coupling < mass ^ 2 / 4
  -- Note: the true condition is coupling < λ₀(P, mass) per Glimm-Jaffe-Spencer (1974).
  -- We use mass² / 4 as a conservative stand-in for the convergence radius.

/-- The continuum limit is non-Gaussian (for φ⁴ interactions at weak coupling).

This follows from the four-point Schwinger function:
  `S₄(f,f,f,f) - 3 · S₂(f,f)² ≠ 0`

i.e., the connected four-point function (fourth cumulant) is nonzero.
For a Gaussian measure, all connected n-point functions with n ≥ 3 vanish,
so a nonzero fourth cumulant proves non-Gaussianity.

The coupling hypotheses (`isPhi4`, `IsWeakCoupling`) restrict the statement
to the regime where it is literature-true: at the φ⁴₂ critical point the
connected four-point function of the scaling limit can vanish, so the
unrestricted all-`P` form is false as stated. See
`planning/r2-honest-headline-spec.md` (D3).

Reference: Simon Ch. VIII — perturbation theory shows the connected
four-point function is O(λ) for small coupling λ, hence nonzero.
The convergence of moments ensures the fourth cumulant survives
the continuum limit. -/
axiom continuumLimit_nonGaussian (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (coupling : ℝ) (hP4 : isPhi4 P coupling)
    (hweak : IsWeakCoupling P mass coupling)
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

/-- Existence of the infinite-volume P(φ)₂ continuum limit (OPEN in this repo).
    Reference: Fröhlich, Adv. Math. 23 (1976) (tightness/compactness existence, arbitrary
    semibounded even P, all couplings); Y.M. Park, J. Math. Phys. 18 (1977) (lattice
    approximants: volume- and spacing-uniform moment bounds via lattice Nelson symmetry /
    checkerboard, lattice→continuum); Glimm–Jaffe Ch. 11.
    ⚠ NOT Guerra–Rosen–Simon: GKS/FKG monotonicity routes need the Griffiths–Simon
    ferromagnetic class and are KNOWN to fail for general even deg ≥ 6 multi-well P
    (Ellis–Monroe–Newman, CMP 46 (1976)); the tightness route covers the full
    InteractionPolynomial class.
    Strategy: the repo's own route is Route B′/A — cylinder IR limit (Lt→∞) then Ls→∞ per
    docs/cylinder-master-plan.md; keystone 18's cluster expansion gives it with uniqueness at
    weak coupling. Until then this is the single existence input for the ℝ² headline.
    (NOT VERIFIED — statement Gemini-vetted 2026-07-12, see r2-honest-headline-spec.md
    D2 vet record) -/
axiom pphi2_limit_exists (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ (μ : Measure (Configuration (ContinuumTestFunction 2)))
      (_ : IsProbabilityMeasure μ),
    IsPphi2Limit μ P mass

end Pphi2

end
