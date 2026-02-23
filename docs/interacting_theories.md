# Interacting Theories — P(Φ)₂ Construction Plan

## Context

We have formalized Gaussian measures (the free field) in Lean 4. The next
major goal is to construct interacting QFT measures, starting with P(Φ)₂
(polynomial interactions in 2 spacetime dimensions).

The interacting measure is defined via a Radon-Nikodym derivative:

    dμ_Λ = (1/Z_Λ) exp(-∫_Λ :P(φ): dx) dμ₀

where μ₀ is the Gaussian free field measure, :P(φ): denotes a Wick-ordered
polynomial, and Λ is a finite volume cutoff.

## Existing Lean 4 Formalizations

### Directly Relevant

**Gaussian LSI** — [lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory)
([arXiv:2602.02285](https://arxiv.org/abs/2602.02285))
- Gaussian logarithmic Sobolev inequality (`gaussian_logSobolev_W12_pi`):
  Ent(f²) ≤ 2 E[‖∇f(X)‖₂²] for X standard Gaussian
- Also: Efron-Stein inequality, Gaussian Poincaré, Bernoulli LSI,
  Gaussian Lipschitz concentration
- ~30k lines, no sorry, built on Mathlib
- Limitation: LSI is in entropy-gradient form, NOT the operator-theoretic
  form. Gross's theorem (LSI ⟹ hypercontractivity) and Nelson's
  hypercontractivity (O-U semigroup Lp→Lq) are NOT formalized.

**Harris-Kleitman Inequality** — Mathlib
([docs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SetFamily/HarrisKleitman.html))
- `Mathlib.Combinatorics.SetFamily.HarrisKleitman`
- Proves: for upper (or lower) sets 𝒜, ℬ on a finite Boolean lattice,
  𝒜.card * ℬ.card ≤ 2^n * (𝒜 ∩ ℬ).card
- Harris-Kleitman is a special case of FKG. Starting point for formalizing
  the full FKG inequality needed for the infinite-volume limit.

**Gagliardo-Nirenberg-Sobolev Inequality** — Mathlib (van Doorn & Macbeth)
([ITP 2024](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2024.37))
- Main file: `Mathlib.Analysis.FunctionalSpaces.SobolevInequality`
  ([docs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.html))
- Key theorems: `eLpNorm_le_eLpNorm_fderiv` (Lp norm bounded by Lq norm
  of derivative for compactly supported C¹ functions between
  finite-dimensional spaces)
- Marginal construction: `Mathlib.MeasureTheory.Integral.Marginal`
  (iterated integration infrastructure, dimension induction)
- Establishes Sobolev-type function space infrastructure in Lean 4

**Gaussian Measures** — our gaussian-field project
- DyninMityaginSpace typeclass (nuclear Fréchet spaces)
- Gaussian measure construction on dual of nuclear spaces
- Schwartz space infrastructure

### Partially Relevant

**HALF Project** — Harmonic Analysis with Lean Formalization (Bonn, ERC)
- 6-year, €6.4M ERC Synergy Grant (Thiele & van Doorn, Bonn)
- Already completed: [Carleson's theorem](https://github.com/fpvandoorn/carleson)
- Will develop: Littlewood-Paley theory, singular integrals, function spaces
- Long-term relevance: infrastructure could eventually support stochastic
  quantization approach. Near-term: Sobolev/function space tools benefit us.

**PhysLean — Wick's Theorem** ([GitHub](https://github.com/HEPLean/PhysLean),
[arXiv:2505.07939](https://arxiv.org/abs/2505.07939))
- Perturbative QFT Wick's theorem: combinatorial, normal-ordering in
  operator algebra (`WickAlgebra`)
- NOT the same as our needs: we need probabilistic Wick ordering (:φⁿ:
  as L² projections in Wiener chaos), not algebraic normal ordering.
  Same name, different mathematical objects.

**LeanMillenniumPrizeProblems — Yang-Mills**
([GitHub](https://github.com/lean-dojo/LeanMillenniumPrizeProblems))
- Wightman-style axiom statement bundled as `QuantumYangMillsTheory`
- States the problem, does not solve it. Worth comparing their Wightman
  axiom formulation with our OS axiom formulation.

### Not Found in Lean 4

- Hermite polynomials / orthogonal polynomials
- Wiener chaos / Itô-Wiener isometry
- Full FKG inequality (only Harris-Kleitman special case exists)
- Hypercontractivity / Ornstein-Uhlenbeck semigroup
- Gross's theorem (LSI ⟹ hypercontractivity)
- Nuclear/Fréchet spaces (our gaussian-field project has this, not in Mathlib)
- Krylov-Bogoliubov theorem
- Fractional Sobolev/Besov spaces

## Two Approaches

### Approach 1: Euclidean QFT (Glimm-Jaffe / Nelson) — Recommended

This approach works directly with the functional integral and measure theory.
It is well-suited to Lean 4 because Mathlib has robust libraries for measure
theory, Bochner integration, and Lp spaces.

**Key advantage**: Cluster expansions are NOT needed for constructing the
measure if we restrict to even polynomials (e.g., aφ⁴ + bφ²) and use
correlation inequalities (FKG, Griffiths, Nelson's monotonicity) instead.
With Dirichlet boundary conditions, Schwinger functions are monotonically
increasing with volume Λ, giving weak convergence as Λ → ℝ².

Cluster expansions are only needed later for:
- Proving the mass gap / exponential decay of correlations
- Handling general (non-even) polynomials

#### Formalization Plan

**Step 1: Wick Ordering (Free Field)**
- Define Wick powers :φ(x)ⁿ: via the Itô-Wiener isometry
- Formalize orthogonal projections in L²(dμ₀) using Hermite polynomials
- Make :φ(f)ⁿ: a rigorously defined random variable
- No existing Lean formalization of Hermite polynomials found

**Step 2: Nelson's Estimate (Hypercontractivity)**
- Prove the interaction V_Λ = ∫_Λ :P(φ(x)): dx satisfies exp(-V_Λ) ∈ L¹(dμ₀)
- This is the hardest analytic step
- Uses the Gaussian LSI to prove hypercontractivity of the
  Ornstein-Uhlenbeck semigroup (Lp → Lq bounds)
- Gaussian LSI is formalized (lean-stat-learning-theory), but in
  entropy-gradient form. Still need:
  (a) Gross's theorem: LSI ⟹ hypercontractivity
  (b) Nelson's hypercontractivity bound for the O-U semigroup

**Step 3: Finite-Volume Measure**
- Define the interacting measure dμ_Λ over compact domain Λ
- Use Mathlib's Measure.withDensity and Lp machinery
- This alone would be a significant formalization achievement

**Step 4: Lattice Approximation and FKG Inequality**
- Approximate the continuum Gaussian measure with a finite lattice
- Prove the FKG inequality (combinatorial property of positive measures
  on lattices)
- Harris-Kleitman in Mathlib is a starting point (special case of FKG)
- This provides the monotonicity needed for the infinite-volume limit

**Step 5: Infinite-Volume Limit**
- Push FKG to the continuum
- Use monotonicity to show finite-volume measures converge weakly
  as Λ → ℝ² via monotone convergence
- This cleanly bypasses cluster expansions

#### Lean 4 / Mathlib Requirements

| Requirement | Status |
|---|---|
| Measure theory, Bochner integration | Available in Mathlib |
| Lp spaces | Available in Mathlib |
| Gaussian measures | Available (our gaussian-field project) |
| Hermite polynomials / orthogonal polynomials | NOT available — need to build |
| Gaussian LSI (entropy form) | Formalized: [lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory) |
| Gross's theorem (LSI ⟹ hypercontractivity) | NOT formalized — needed |
| Nelson's hypercontractivity (O-U semigroup Lp→Lq) | NOT formalized — needed |
| Measure.withDensity (Radon-Nikodym) | Available in Mathlib |
| Harris-Kleitman inequality | Available in Mathlib (special case of FKG) |
| Full FKG inequality | NOT formalized — need to generalize Harris-Kleitman |
| Weak convergence of measures | Available in Mathlib |
| Gagliardo-Nirenberg-Sobolev inequality | Available: `Mathlib.Analysis.FunctionalSpaces.SobolevInequality` |

### Approach 2: Stochastic Quantization (Da Prato-Debussche) — Not Recommended

This approach defines the P(φ)₂ measure as the invariant measure of a
singular SPDE:

    ∂_t Φ = (Δ - m²)Φ - :P'(Φ): + ξ

where ξ is spacetime white noise.

**Key obstacle**: Φ in 2D is a distribution, requiring the Da Prato-Debussche
trick — solving a deterministic parabolic PDE with rough distributional
coefficients in fractional function spaces. This requires heavy harmonic
analysis infrastructure absent from Lean 4.

Note: The HALF project (Bonn) will develop Littlewood-Paley and related
infrastructure over the next 6 years, which could eventually make this
approach feasible.

#### Formalization Plan (for reference)

**Step 1: Linear SPDE**
- Solve ∂_t X = (Δ - m²)X + ξ
- Prove stochastic convolution X(t) is a continuous path in C^{-ε}

**Step 2: Wick Powers of X**
- Construct :Xᵏ: probabilistically (purely Gaussian, isolates renormalization)
- Prove :Xᵏ: converges in L²(Ω; C^{-ε})

**Step 3: Da Prato-Debussche Trick**
- Write Φ = X + v, noise cancels, leaving deterministic PDE for v:
  ∂_t v = (Δ - m²)v - Σ_k (n choose k) :Xᵏ: v^{n-k}

**Step 4: Pathwise Contraction**
- Since X ∈ C^{-ε} and v ∈ C^{2-ε}, the product :Xᵏ: · v^{n-k} is defined
- Banach fixed-point in C^{2-ε} using Schauder estimates

**Step 5: Invariant Measure**
- Define Markov transition semigroup for Φ
- Prove tightness, extract invariant measure via Krylov-Bogoliubov

#### Lean 4 / Mathlib Requirements

| Requirement | Status |
|---|---|
| Fractional function spaces (Hölder-Zygmund C^α, Besov) | NOT available |
| Littlewood-Paley theory, dyadic partitions of unity | NOT available (HALF project future) |
| Fractional Schauder estimates (C^α → C^{α+2}) | NOT available |
| Stochastic convolution in negative regularity spaces | NOT available |
| Krylov-Bogoliubov theorem | NOT available |

## Recommendation

Pursue the Glimm-Jaffe / Nelson approach. The main dependencies (measure
theory, Lp spaces, Gaussian measures) are already available. The critical
missing pieces, roughly in order of difficulty:

1. **Wick ordering** via Hermite polynomials / Wiener chaos — no Lean
   precedent, but mathematically straightforward
2. **FKG inequality** — extend Harris-Kleitman already in Mathlib,
   combinatorial and well-suited to formalization
3. **Finite-volume interacting measure** — Radon-Nikodym with respect
   to μ₀, uses existing Mathlib infrastructure
4. **Hypercontractivity** — Gaussian LSI exists, need Gross's theorem
   and Nelson's estimate. Hardest analytic step.

## References

### Textbooks
- Glimm and Jaffe, *Quantum Physics*, Ch. 6, 8, 19
- Simon, *The P(Φ)₂ Euclidean (Quantum) Field Theory*

### Original Papers
- Nelson, *Construction of quantum fields from Markoff fields* (1973)
- Gross, *Logarithmic Sobolev inequalities* (1975)
- Osterwalder and Schrader, *Axioms for Euclidean Green's functions* I & II
- Da Prato and Debussche, *Strong solutions to the 2D stochastic quantization equation* (2003)

### Lean 4 Formalizations
- Zhang et al., *Statistical Learning Theory in Lean 4* ([arXiv:2602.02285](https://arxiv.org/abs/2602.02285)) — Gaussian LSI
- van Doorn and Macbeth, *Integrals Within Integrals* ([ITP 2024](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2024.37)) — GNS inequality
- Tooby-Smith, *Digitalizing Wick's theorem* ([arXiv:2505.07939](https://arxiv.org/abs/2505.07939)) — perturbative Wick (PhysLean)
- Mathlib: `Combinatorics.SetFamily.HarrisKleitman` — Harris-Kleitman inequality
- HALF Project, Bonn ([Carleson formalization](https://github.com/fpvandoorn/carleson)) — harmonic analysis infrastructure
