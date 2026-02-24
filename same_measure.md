# Proving the Two Constructions Yield the Same Continuum Measure

The pphi2 project (lattice → continuum) and the Phi4 project (continuum UV
cutoff → infinite volume) both produce a probability measure on S'(ℝ²).
This document outlines strategies for proving these measures coincide,
at least for the common case P(φ) = λφ⁴.

## Primary motivation: cherry-picking the easiest proof of each OS axiom

The two projects handle different OS axioms with very different levels of
difficulty. Proving measure equality lets us transfer proofs between them,
using the simplest available argument for each axiom:

| Axiom | Easiest in | Why | Hard in the other |
|---|---|---|---|
| **OS2** (Euclidean invariance) | **Phi4** | Manifest: (−Δ+m²)⁻¹ and ∫:φ⁴:dx are E(2)-invariant. Only translation invariance needs restoration (infinite-volume limit). | **pphi2**: Requires Ward identity argument — anomaly has dim 4 > d=2, must show it's RG-irrelevant with no log corrections |
| **OS3** (Reflection positivity) | **pphi2** | Transfer matrix T is positive ⟹ action decomposes as S⁺ + S⁺∘Θ ⟹ perfect square ⟹ RP on lattice. Then RP is closed under weak limits (proved). | **Phi4**: Needs Dirichlet/Neumann covariance bracketing, checkerboard decomposition, multiple reflection bounds, determinant estimates |

The bridging theorem is:

```
μ_latt = μ_cont                     (same_continuum_measure)

OS2(μ_cont)  — from Phi4            (manifest Euclidean invariance)
OS3(μ_latt)  — from pphi2           (transfer matrix → RP → weak limit)

∴ OS2(μ_latt) by rewrite            (eliminates Ward identity argument)
∴ OS3(μ_cont) by rewrite            (eliminates multiple reflections)
```

This eliminates the two hardest arguments in the entire formalization:
- **pphi2 Phase 5** (Ward identity anomaly irrelevance) — the most subtle
  part of the lattice construction
- **Phi4 multiple reflections** (chessboard bounds) — requires Dirichlet-
  Neumann covariance comparison and determinant estimates

The bridging code is in `Pphi2/Bridge.lean`.

## The two measures

**pphi2 measure (μ_latt):**
Lattice GFF on (ℤ/Nℤ)² with spacing a, Wick-ordered interaction
V_a = a² Σ_x :P(φ(x)):_a, interacting measure μ_a, embedded into S'(ℝ²)
as ν_a = (ι_a)_* μ_a, then Prokhorov subsequential limit ν_{a_n} ⇀ μ_latt.

**Phi4 measure (μ_cont):**
Continuum Gaussian dφ_C on S'(ℝ²), UV-regularized interaction
V_{Λ,κ} = λ ∫_Λ :φ_κ⁴: dx, UV limit V_Λ, finite-volume measure
dμ_Λ = Z_Λ⁻¹ e^{−V_Λ} dφ_C, infinite-volume limit μ_Λ → μ_cont via
monotone convergence with Dirichlet BC.

## Why the measures should be the same

Both constructions implement the same heuristic path integral
```
  dμ = Z⁻¹ exp(−λ ∫ :φ⁴: dx) dφ_C
```
with the same mass m, the same coupling λ, and the same Wick ordering
(subtracting the coincident-point divergence). The only differences are
in the regularization scheme (lattice vs. continuum UV cutoff) and the
order of limits (a → 0 vs. Λ ↗ ℝ²).

The standard physics argument is universality: the P(φ)₂ theory is
super-renormalizable, so the only counterterm needed is a mass
renormalization (absorbed into the Wick ordering). Different regularization
schemes that implement the same Wick subtraction should flow to the same
continuum theory.

## Strategy 1: Schwinger function comparison (most promising)

### Idea
Show that the n-point Schwinger functions of both measures agree. Since
a measure on S'(ℝ²) is determined by its moments (the Schwinger functions)
— at least when a moment bound holds — equality of all Schwinger functions
implies equality of the measures.

### Steps

**Step 1. Moment determinacy.**
Both measures satisfy the exponential moment bound
`∫ exp(c‖Φ‖_{−s}²) dμ < ∞` for some c > 0, s > 0
(Fernique-type bound). This implies the measure is determined by its
moments (Schwinger functions). In Lean, this would require:
```
theorem measure_determined_by_moments
    (μ ν : Measure (Configuration TestFun2D))
    (hμ : IsProbabilityMeasure μ) (hν : IsProbabilityMeasure ν)
    (h_exp_moment : (* both have finite exponential moments *))
    (h_moments : ∀ n (f : Fin n → TestFun2D),
      ∫ ω, ∏ i, ω (f i) ∂μ = ∫ ω, ∏ i, ω (f i) ∂ν) :
    μ = ν
```

**Step 2. Schwinger functions as a double limit.**
The Schwinger functions of both measures can be expressed as limits of the
same doubly-regularized object. Define:
```
  S_n^{a,Λ}(f₁,...,fₙ) = ∫ Φ(f₁)⋯Φ(fₙ) dν_{a,Λ}
```
where ν_{a,Λ} is the measure with BOTH lattice spacing a AND volume cutoff Λ.

- pphi2 takes a → 0 first (continuum limit), then Λ → ∞ is automatic
  (the lattice is a torus, so volume = (N·a)² → ∞ as N → ∞ with Na fixed
  — actually the lattice size grows with 1/a).
- Phi4 takes Λ → ∞ first (infinite-volume limit), then κ → ∞ removes the
  UV cutoff.

If the double limit commutes, both procedures give the same answer.

**Step 3. Interchange of limits.**
The key technical result: for super-renormalizable theories in d = 2,
the double limit (a → 0, Λ → ∞) of the Schwinger functions exists and is
independent of the order. This follows from:

(a) **Uniform bounds:** The Nelson hypercontractive estimate and the
chessboard bounds provide uniform control of the Schwinger functions
in both parameters simultaneously.

(b) **Uniqueness of the limit:** For P(φ)₂ with P = λφ⁴ at weak coupling
(λ < λ₀), the cluster expansion shows that the infinite-volume limit is
unique (no phase transitions). Combined with (a), any subsequential limit
must agree.

(c) **Wick ordering equivalence:** The lattice Wick constant
c_a = G_a(0,0) and the continuum Wick constant c_κ with κ ∼ 1/a both
diverge as (2π)⁻¹ log(1/a), and their difference is bounded:
```
  |c_a − c_{1/a}| ≤ C  (uniformly in a)
```
The re-Wick-ordering formula `:φ⁴:_{c₁} = :φ⁴:_{c₂} + 6δc :φ²:_{c₂} + 3(δc)²`
shows that the bounded difference δc = c_a − c_{1/a} produces only a bounded
shift in the interaction, which vanishes in the renormalized limit.

## Strategy 2: Coupling both to a common intermediate

### Idea
Introduce a "doubly-regularized" measure that uses BOTH a lattice AND a
volume cutoff, then show each project's measure is the limit of this common
object.

### The intermediate measure
On a lattice (ℤ/Nℤ)² with spacing a, restrict the volume to a rectangle
Λ ⊂ aℤ² (Dirichlet BC on ∂Λ). This gives a finite-dimensional Gaussian
with Dirichlet covariance C_{a,Λ}, and the interacting measure
```
  dμ_{a,Λ} = Z_{a,Λ}⁻¹ exp(−V_{a,Λ}) dφ_{C_{a,Λ}}
```

Then:
- **pphi2 route:** Fix Λ = full torus, take a → 0 (continuum limit)
- **Phi4 route:** Fix a → 0 first (continuum limit of the lattice GFF →
  continuum GFF with Dirichlet BC on Λ), then take Λ → ∞

The key lemma: the lattice GFF with Dirichlet BC converges weakly to the
continuum GFF with Dirichlet BC as a → 0. This is a standard result in
probability theory (invariance principle for Gaussian fields).

## Strategy 3: Characteristic functional comparison

### Idea
The characteristic functional (generating functional)
```
  Z[f] = ∫ exp(iΦ(f)) dμ
```
determines the measure uniquely by the Bochner-Minlos theorem (since S'(ℝ²)
is the dual of a nuclear space). Show both constructions give the same Z[f].

### Advantage
The characteristic functional is bounded (|Z[f]| ≤ 1), so weak convergence
automatically implies convergence of Z[f]. No moment determinacy argument
needed.

### Steps
1. Show Z_latt[f] := lim_{a→0} ∫ exp(iΦ(f)) dν_a exists and equals the
   pphi2 characteristic functional.
2. Show Z_cont[f] := ∫ exp(iΦ(f)) dμ_cont is the Phi4 characteristic
   functional.
3. Prove Z_latt[f] = Z_cont[f] for all f ∈ S(ℝ²), using the double-limit
   interchange argument from Strategy 1.

## Strategy 4: Uniqueness from the OS axioms (weakest, but simplest)

### Idea
If both measures satisfy OS0–OS4 (including clustering), and if the OS axioms
plus the mass and coupling parameters uniquely determine the measure, then
equality follows without comparing constructions at all.

### Caveat
OS uniqueness is **not automatic**. The OS axioms define a convex set of
measures, and extremal decomposition is needed to identify pure phases.
For φ⁴₂ at weak coupling, uniqueness does hold (by the cluster expansion).
For strong coupling near the critical point, there can be multiple phases
(spontaneous symmetry breaking for Z₂-even P), and additional information
(e.g., which phase is selected) is needed.

### When this works
- Weak coupling: λ < λ₀ (some threshold). Both constructions give the
  unique cluster-expansion phase.
- Away from phase transitions more generally.
- If both constructions select the same phase (e.g., the ℤ₂-even phase for
  even P with no external field).

## Recommended approach

**Strategy 1 (Schwinger function comparison)** is the most promising for
formalization because:

1. Both projects already define and compute Schwinger functions.
2. The moment determinacy argument is clean and well-suited to Lean.
3. The Wick constant comparison (Step 3c) is a concrete, provable estimate.
4. The uniqueness argument at weak coupling is already partly formalized
   in Phi4 (cluster expansion for OS4).

The main new ingredients needed:
- `measure_determined_by_schwinger` (standard measure theory)
- `wick_constant_comparison` (lattice analysis — comparing G_a(0,0) with
  the regularized continuum propagator)
- `lattice_schwinger_equals_continuum_schwinger` (the core technical result,
  using the interchange of limits)

**Estimated difficulty:** The measure determinacy theorem and the Wick
constant comparison are each medium-difficulty formalizations. The
interchange of limits is the hardest part, but can be axiomatized with a
detailed proof sketch and filled in incrementally.

## References

- Glimm-Jaffe, *Quantum Physics*, Chapter 8 (Wick ordering, UV estimates),
  Chapter 11 (infinite volume), Chapter 18 (cluster expansion)
- Simon, *The P(φ)₂ Euclidean QFT*, Chapter V (continuum limit)
- Guerra-Rosen-Simon, "The P(φ)₂ Euclidean quantum field theory as
  classical statistical mechanics" (1975) — universality of regularization
- Brydges-Fröhlich-Sokal, "The random walk representation of classical
  spin systems and correlation inequalities" — lattice/continuum comparison
- Dimock-Glimm, "Measures on Schwartz distribution space and applications
  to P(φ)₂ field theories" (1974) — measure determinacy on S'
