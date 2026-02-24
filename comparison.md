# Comparison: pphi2 vs Phi4

Both projects formalize the construction of an interacting scalar quantum field
theory in 2 Euclidean dimensions in Lean 4, ultimately verifying the
Osterwalder-Schrader axioms and (via reconstruction) the Wightman axioms.
They share the gaussian-field library as a common dependency but differ
significantly in their construction strategy.

## Scope

| | pphi2 | Phi4 |
|---|---|---|
| **Interaction** | General even P(φ), deg ≥ 4, bounded below | φ⁴ only (λφ⁴, coupling λ > 0) |
| **Parameters** | `InteractionPolynomial`, mass m > 0 | `Phi4Params` (mass m > 0, coupling λ > 0) |
| **Target axioms** | OS0–OS4 (all five) | OS0–OS3 + E0' (E4 for weak coupling only) |
| **Extra dependency** | — | OSreconstruction (Wightman axioms, analytic continuation) |
| **Main theorem** | `pphi2_main`, `pphi2_existence` | `phi4_wightman_exists` |

## Construction strategy

### pphi2 — Lattice → Continuum (Glimm-Jaffe/Nelson)

1. **Lattice measure.** Start on the finite periodic lattice (ℤ/Nℤ)² with
   spacing a. The free field is the lattice GFF (`latticeGaussianMeasure`
   from gaussian-field). The interacting measure is
   `dμ_a = Z_a⁻¹ exp(−V_a) dμ_{GFF,a}`, where
   `V_a = a² Σ_x :P(φ(x)):_a` uses Wick ordering with the lattice
   propagator diagonal `c_a = G_a(0,0)` as counterterm.

2. **Transfer matrix.** Decompose the lattice action across time slices.
   The transfer operator T is self-adjoint, positive, trace-class on
   L²(ℝ^{N_s}). This yields **OS3 (reflection positivity)** directly.

3. **Spectral gap.** Perron-Frobenius (strictly positive kernel → simple
   leading eigenvalue) gives `λ₀ > λ₁`, hence a mass gap
   `m_phys = −(1/a) log(λ₁/λ₀) > 0`. This implies **OS4 (clustering)**.

4. **Continuum limit.** Embed lattice fields into S'(ℝ²) via
   `(ι_a φ)(f) = a² Σ_x φ(x) f(ax)`. Prove tightness of the pushforward
   family {ν_a} using Mitoma's criterion + Nelson's hypercontractive
   estimate. Extract a convergent subsequence by Prokhorov's theorem.
   OS0, OS1, OS3, OS4 transfer to the limit.

5. **Euclidean invariance.** The lattice breaks E(2) to the discrete group.
   A Ward identity argument shows the rotation-breaking anomaly has scaling
   dimension 4 > d = 2, so it is RG-irrelevant and vanishes as O(a²).
   Super-renormalizability prevents logarithmic corrections. This gives
   **OS2**.

### Phi4 — Continuum regularization (Glimm-Jaffe Part II)

1. **Free field.** Construct the centered Gaussian measure dφ_C on S'(ℝ²)
   with covariance C = (−Δ + m²)⁻¹, using spectral CLM via the harmonic
   oscillator (Hermite) basis. This lives directly in the continuum.

2. **UV regularization + Wick ordering.** Smooth the field: φ_κ = δ_κ ∗ φ
   (convolution with approximate delta of width 1/κ). The Wick-ordered
   quartic is `:φ_κ⁴: = He₄(φ_κ, c_κ)` where c_κ ∼ (2π)⁻¹ ln κ.

3. **Finite-volume measure.** For a rectangle Λ ⊂ ℝ², define
   `V_Λ = λ ∫_Λ :φ⁴: dx` (UV limit of V_{Λ,κ} in L²). The key estimate
   is `e^{−V_Λ} ∈ Lᵖ(dφ_C)` for all p < ∞ (Theorem 8.6.2). Then
   `dμ_Λ = Z_Λ⁻¹ e^{−V_Λ} dφ_C`.

4. **Correlation inequalities.** GKS-I/II, FKG, and Lebowitz inequalities
   give monotonicity of Schwinger functions in the volume: S_n^{Λ₁} ≤
   S_n^{Λ₂} for Λ₁ ⊂ Λ₂ (with Dirichlet BC and non-negative test
   functions).

5. **Infinite-volume limit.** Monotone + uniformly bounded (from chessboard /
   multiple reflection estimates) ⟹ convergent. The limit defines the
   infinite-volume Schwinger functions and the measure on S'(ℝ²).

6. **Reflection positivity.** Proved directly in the continuum using the
   positivity of the free covariance under time reflection, then inherited
   by the interacting measure. Multiple reflections give chessboard bounds.

7. **Reconstruction.** OS0–OS3 + linear growth E0' are fed into the
   OSreconstruction library's `os_to_wightman` theorem to produce Wightman
   distributions, field operators, locality, and Lorentz covariance. OS4
   (clustering) is proved separately for weak coupling via cluster expansion.

## Key differences

| Aspect | pphi2 | Phi4 |
|---|---|---|
| **Regularization** | Lattice (spacing a) | Continuum UV cutoff κ + volume cutoff Λ |
| **Free field** | Lattice GFF on (ℤ/Nℒ)² | Gaussian on S'(ℝ²) via Hermite CLM |
| **Wick counterterm** | `c_a = G_a(0,0)` (propagator diagonal) | `c_κ ∼ (2π)⁻¹ ln κ` (regularized covariance) |
| **Infinite-volume route** | Prokhorov (tightness + weak compactness) | Monotone convergence (GKS + chessboard bounds) |
| **Reflection positivity** | Transfer matrix positivity on lattice → inherited | Direct continuum argument + multiple reflections |
| **Clustering / mass gap** | Perron-Frobenius spectral gap for transfer matrix | Cluster expansion (weak coupling only) |
| **Euclidean invariance** | Ward identity restoration (non-trivial!) | Built in (continuum from the start) |
| **Boundary conditions** | Periodic (torus) | Dirichlet |
| **Wightman reconstruction** | Axiomatized (`os_reconstruction`) | Uses OSreconstruction library (`os_to_wightman`) |

## Shared infrastructure (from gaussian-field)

- `GaussianField.measure T` — Gaussian probability measure on WeakDual ℝ E
- `GaussianField.covariance` — bilinear covariance form
- `GaussianField.pairing_memLp` — all finite moments (Fernique)
- `latticeGaussianMeasure` — GFF on finite lattice (used by pphi2)
- Nuclear space infrastructure (Dynin-Mityagin, Schwartz space)
- Wick's theorem and moment bounds

## Proof status

| | pphi2 | Phi4 |
|---|---|---|
| **Axioms** | 65 | ~14 (fewer explicit axioms) |
| **Sorries** | 28 | ~82 |
| **Proven theorems** | Many structural + some core | ~11 |
| **Prokhorov** | Partly proved (tightness → sequential compactness) | N/A (uses monotone convergence) |
| **Builds cleanly** | Yes (3067 jobs) | Yes |

## Complementary strengths

**pphi2** handles the general P(φ) case and has a more complete logical
structure (all six phases wired together with explicit axiom inheritance),
plus a partly-proved Prokhorov theorem. Its main weakness is the Ward
identity argument for rotation invariance, which is subtle.

**Phi4** is closer to the textbook continuum treatment (Glimm-Jaffe Part II),
has an explicit Wightman reconstruction via the OSreconstruction library,
Feynman diagram machinery, and the full suite of correlation inequalities
(GKS, FKG, Lebowitz). Its main weakness is that OS4 is only proved for weak
coupling.

The two approaches are genuinely complementary and, if they can be shown to
produce the same continuum measure (see [same_measure.md](same_measure.md)),
they validate each other and allow transferring results between frameworks.
