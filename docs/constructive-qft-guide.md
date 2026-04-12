# Constructive Quantum Field Theory: A Guide for Physicists Using AI-Math Tools

> For physicists who want to understand how rigorous QFT constructions
> work, and how to formalize them using tools like Lean 4 + Mathlib.

## What is constructive QFT?

Constructive QFT builds quantum field theories as rigorously defined
mathematical objects — probability measures on spaces of distributions —
rather than formal perturbation series. The key results:

- **P(φ)₂** (2D scalar field): Fully constructed (Glimm-Jaffe-Spencer 1970s)
- **φ⁴₃** (3D scalar field): Constructed via stochastic quantization (Hairer 2014, Gubinelli-Hofmanova 2018, Barashkov-Gubinelli 2020)
- **φ⁴₄** (4D scalar field): Proved trivial (Aizenman-Duminil-Copin 2021)
- **Yang-Mills₄**: Open — this is the Clay Millennium Problem

## The construction pipeline

Every constructive QFT follows the same template:

```
Free field (Gaussian measure μ₀)
    ↓  perturb by exp(-V)
Regularized interacting measure μ_κ = (1/Z_κ) exp(-V_κ) dμ₀
    ↓  remove cutoff (κ → ∞)
Continuum interacting measure μ
    ↓  verify axioms
OS axioms → Wightman QFT (via reconstruction)
```

### Step 1: The Gaussian free field

The starting point is always a Gaussian measure μ₀ on S'(M) (distributions
on spacetime M), with covariance operator C = (-Δ + m²)⁻¹. This is the
free field — a well-defined probability measure on distributions.

Key property: μ₀ satisfies the **log-Sobolev inequality** (Gross 1975),
which gives **hypercontractivity** of the associated OU semigroup.

### Step 2: The interaction and Wick ordering

The interaction V(φ) = ∫ :P(φ(x)): dx involves:
- A semibounded polynomial P (e.g., P(t) = λt⁴ + lower order)
- **Wick ordering** :·: to subtract divergent expectations
- **Renormalization** (mass counterterm) to absorb cutoff-dependent divergences

After Wick ordering: V_κ lives in a finite sum of Wiener chaoses.

### Step 3: Integrability of exp(-V)

**Problem:** V is unbounded below, so exp(-V) is unbounded above.

**Solution (Nelson's estimate):** Since V_κ is in a finite sum of Wiener
chaoses, and Gaussian hypercontractivity controls moments of Wiener chaos
variables, we get exp(-sV_κ) ∈ L¹(μ₀) for all s > 0, uniformly in κ.

Two approaches to the moment bound:
- **Direct:** Gaussian moments + double factorial bounds (fully proved in gaussian-field)
- **Via Cauchy-Schwarz:** ∫F dμ_a ≤ (∫F² dμ_GFF)^{1/2} · (∫e^{-2V} dμ_GFF)^{1/2}

### Step 4: Continuum limit (tightness)

Remove the UV cutoff. Need: the family {μ_κ} has a convergent subsequence.

**Tool:** Prokhorov's theorem on S' — tightness ⟹ sequential compactness.

**Tightness criterion (Mitoma):** For measures on S', tightness reduces to
uniform second moment bounds: sup_κ E_{μ_κ}[|Φ(f)|²] < ∞ for all test f.

**Two approaches:**
- **Hypercontractivity route** (pphi2): Nelson bounds give uniform moments
  directly, no correlation inequalities needed
- **Correlation inequality route** (Simon, Glimm-Jaffe): Use GHS, FKG, etc.
  for the infinite-volume limit. More classical, harder to formalize.

### Step 5: Osterwalder-Schrader axioms

The continuum measure must satisfy OS0–OS4:
- **OS0** (Analyticity): Schwinger functions are real-analytic
- **OS1** (Regularity): Distributional regularity / tempered growth
- **OS2** (Euclidean invariance): Translation + rotation symmetry
- **OS3** (Reflection positivity): The crucial positivity condition
- **OS4** (Clustering / mass gap): Exponential decay of correlations

OS3 (reflection positivity) is the deepest — it's what makes the
reconstruction theorem work, producing a positive-definite Hilbert space.

### Step 6: Reconstruction

The **Osterwalder-Schrader reconstruction theorem** converts a Euclidean
QFT satisfying OS0–OS4 into a Wightman QFT (Hilbert space + vacuum +
field operators satisfying the Wightman axioms).

## What we've formalized

### pphi2 (P(φ)₂ on the 2D torus and ℝ²)
- Three construction routes: lattice→ℝ², lattice→T², direct on S¹×ℝ
- Gaussian hypercontractivity: **fully proved** (0 sorry)
- Nelson estimate: **proved**
- Tightness (torus): **proved**
- OS axioms: OS1–OS4 proved for Route A (25 axioms for analytical infrastructure)
- Main theorem `pphi2_exists`: P(φ)₂ QFT exists satisfying Wightman axioms

### gaussian-field (Gaussian measures on nuclear spaces)
- Gaussian hypercontractivity: **fully proved** (0 sorry, 0 axioms)
- Tightness: **proved** via uniform second moments
- Measure uniqueness: **proved** via covariance characterization

### markov-semigroups (functional inequalities)
- Brascamp-Lieb inequality: **proved** from 2 analytical axioms
- Poincaré inequality from BL: **proved**
- Bakry-Émery framework: axiomatized (BGL textbook results)
- Gross equivalence (LSI ↔ hypercontractivity): axiomatized

### OSreconstruction (OS → Wightman)
- Paley-Wiener-Schwartz theorem: 0 sorry, 1 private axiom
- Boundary value convergence: **proved**
- Reconstruction theorem: in progress

## References

### Overviews and surveys

- Simon, "Euclidean quantum mechanics and field theory: a 50 year love affair"
  (2020, arXiv:2011.12335) — **Best single starting point.**
- Kawahigashi-Tanimoto, "Constructive quantum field theory"
  (2024, arXiv:2403.01886) — Recent broad survey.
- Jaffe, "Quantum theory and relativity" (1999, hep-th/9907095) — Concise
  overview by a founder of the field.

### Classic textbooks

- Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory* (1974) —
  Most accessible complete treatment. **Read this first.**
- Glimm-Jaffe, *Quantum Physics: A Functional Integral Point of View*
  (1987, 2nd ed.) — Encyclopedic reference for classic CQFT.
- Streater-Wightman, *PCT, Spin and Statistics, and All That* (1964) —
  The Wightman axioms (target of reconstruction).
- Simon, *Functional Integration and Quantum Physics* (2005, 2nd ed.) —
  Rigorous path integrals / Wiener measure.
- Rivasseau, *From Perturbative to Constructive Renormalization* (1991) —
  Bridges perturbative and constructive methods.

### Modern approaches (stochastic quantization)

- Hairer, "Singular SPDEs" (2016, arXiv:1612.08133) — Pedagogical
  introduction to regularity structures and φ⁴₃.
- Chandra-Chevyrev-Hairer-Shen, "Lecture notes on stochastic quantization"
  (2018, arXiv:1801.06730) — Covers φ⁴₃ and Yang-Mills via SPDEs.
- Gubinelli, lecture notes (2025) — Modern treatment.
- Barashkov-Gubinelli (2020, arXiv:2112.05562) — Variational approach to φ⁴₃.
- Gubinelli-Hofmanova (2018, arXiv:1810.01700) — Global solutions for φ⁴₃.

### The frontier

- Chandra-Chevyrev-Hairer-Shen, "Stochastic quantisation of Yang-Mills-Higgs
  in 3D" (2022, arXiv:2211.05436) — State of the art for gauge theories.
- Aizenman-Duminil-Copin, "Triviality of φ⁴₄" (2021, arXiv:1912.07979) —
  Why simple scalar theories can't be interacting in 4D.
- Duch-Dybalski-Jahandideh (2023, arXiv:2311.04137) — Recent OS-related work.

### Reconstruction and axiomatics

- Osterwalder-Schrader, "Axioms for Euclidean Green's functions" (1973, 1975) —
  The original papers.
- Jäkel, "The Osterwalder-Schrader theorem" (2005, math-ph/0504049) —
  Clear pedagogical review.
- Haag, *Local Quantum Physics* (1996, 2nd ed.) — Algebraic QFT perspective.

### Functional inequalities (foundation for hypercontractivity)

- Gross, "Logarithmic Sobolev inequalities" (1975) — The LSI ↔ hypercontractivity
  equivalence.
- Bakry-Gentil-Ledoux, *Analysis and Geometry of Markov Diffusion Operators*
  (2014) — The modern reference for Bakry-Émery theory.
- Brascamp-Lieb, "On extensions of the Brunn-Minkowski and Prékopa-Leindler
  theorems" (1976) — The variance bound for log-concave measures.

### For the Gaussian free field specifically

- Sheffield, "Gaussian free field for mathematicians" (2007, math/0312099) —
  Definitive modern introduction.
- Nelson, "The free Markoff field" (1973) — Original construction + hypercontractivity.
