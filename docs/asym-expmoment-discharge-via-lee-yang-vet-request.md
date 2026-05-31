# Pphi2 discharge plan for `asymInteracting_expMoment_volume_uniform` via the proposed `lee-yang` repo — vet request

*Standalone vet packet. Reader assumed to have working knowledge of
constructive P(φ)₂, Lee-Yang theory, transfer-matrix spectral theory,
and Lean 4 / Mathlib formalization practice. No project-internal jargon
required.*

**VETTED 2026-05-31** (deep-think). Architecture confirmed as correct;
four recalibrations applied:

1. `IsLeeYang` is multivariate with a projection lemma to univariate
   marginals (was univariate + multivariate-as-add-on).
2. `iteratedAsano` lives over `SimpleGraph V` with edge weighting,
   not specialized to rectangular lattices.
3. `evenPolynomialWick` takes an explicit variance parameter (was
   hardcoded unit variance).
4. Pphi2-side adapter scope bumped from ~50-150 lines to **~200-400
   lines** — the global covariance representation
   (`GaussianField.measure (latticeCovarianceAsymGJ ...)`) does NOT
   admit a one-step disintegration into the site-wise product
   measure that Griffiths-Simon consumes. The adapter needs a
   substantive density-vs-flat-Lebesgue rewriting + nearest-neighbour
   coupling extraction. See "Question 3 answered" section below.

The four planned files (`Polynomial/RealZeros.lean`,
`Polynomial/Asano.lean`, `Measure/Newman.lean`,
`Measure/GriffithsSimon.lean`) stand; their content has been refined
in `lee-yang/PLAN.md` accordingly. Phase 1 total scope bumped to
**~1600-2700 lines** (was ~1500-2500) due to the multivariate IsLeeYang
+ projection lemma in `Measure/Newman.lean`.

Risks flagged: Mathlib Hurwitz-theorem API state (recon needed before
`GriffithsSimon.lean`); Cayley-Möbius bookkeeping (mitigated by
leading with `NewmanClass` as primary definition rather than
Lee-Yang circle).

---

## Vet response — Question 3 answered

**Gemini's question**: "How do you currently represent the global
lattice covariance in pphi2, and does it easily admit a disintegration
into the site-wise product measure required by lee-yang?"

**Answer**: pphi2's representation is:

```lean
def latticeGaussianMeasureAsym ... :=
  GaussianField.measure (latticeCovarianceAsymGJ Nt Ns a mass ha hmass)

def interactingLatticeMeasureAsym ... :=
  (1/Z) • (latticeGaussianMeasureAsym).withDensity (exp(-V))
```

It does **not** currently admit a direct disintegration. The Gaussian
factor is built abstractly via `GaussianField.measure` parameterized
by a covariance CLM (`latticeCovarianceAsymGJ` — encoding `−Δ_a + m²`);
the interaction is layered on as a `withDensity`.

To bridge to Griffiths-Simon's
`(∏_x evenPolynomialWick) × (∏_⟨xy⟩ coupling)` form, the pphi2 adapter
file needs (in order):

1. **GFF density rewriting**:
   `latticeGaussianMeasureAsym = (1/Z_G) · exp(−½⟨ω, Q ω⟩) · ∏_x dω_x`
   with `Q = −Δ_a + m²`. Substantive theorem — moves from the abstract
   `GaussianField.measure` form to an explicit Lebesgue-density form.
2. **Quadratic-form decomposition**:
   `exp(−½⟨ω, Q ω⟩) = ∏_x exp(−D_x ω_x²/2) · ∏_⟨xy⟩ exp(J_xy ω_x ω_y)`
   with `D_x` the on-site (kinetic + mass) coefficients and `J_xy =
   −1/a²` the nearest-neighbour ferromagnetic couplings.
3. **Site-wise combination**:
   Fold each `exp(−D_x ω_x²/2) · dω_x` together with `exp(−a²:P(ω_x):)`
   from the interaction; recognize as `evenPolynomialWick c_x a P` with
   `c_x = wickConstantAsym Nt Ns a mass` (variance parameter matches
   exactly with the design change above).
4. **Asano application**: apply `iteratedAsano` (generic graph version)
   to the resulting Newman-class single-site factors over the asym
   lattice's edge structure with the ferromagnetic `J_xy` weights.

The Asano application (Step 4) is short — topology-independent. The
cost lives in Steps 1-3, especially Step 1 (density rewriting).
Realistic adapter line count: **200-400 lines**, not 50-150.

---

## 0. What this document is

We have a P(φ)₂ Euclidean QFT formalization (pphi2) that constructs
the **cylinder** measure on `S¹(Ls) × ℝ` — fixed spatial period `Ls`,
time period `Lt → ∞`. The construction is **fully unconditional in
its UV step** and reduces the cylinder OS0/OS1/OS2/OS3 axiomatic
content to one remaining project-introduced axiom plus three textbook
upstream/independent inputs.

This document:

1. States the remaining axiom precisely.
2. States our proposed 4-layer discharge architecture (vetted by you on
   2026-05-31 in a prior pass — recapitulated for context).
3. States the **dependency split** between pphi2 and a proposed new
   Mathlib-only repo `lee-yang` that would carry the polynomial /
   measure / MGF infrastructure.
4. Asks specific questions about whether the split is correct, the
   lee-yang content is sufficient, and the pphi2-side instantiation
   is short.

## 1. The axiom

`Pphi2/AsymTorus/AsymContinuumLimit.lean:601` (informal):

> For any even-degree `InteractionPolynomial P` with positive leading
> coefficient and mass `m > 0`, there exist constants `K, C > 0` such
> that for every time-period `L`, every refinement `(Nt, Ns, a)` with
> `Nt · a = L`, `Ns · a = Ls`, and every test function
> `f : AsymTorusTestFunction L Ls`,
>
> `∫ exp(|ωf|) dμ_int_{Nt,Ns,a,L,Ls} ≤ K · exp(C · σ²_free(f))`,
>
> where `μ_int` is the asymmetric-torus interacting measure (Wick-ordered
> `:P(φ):` action with nearest-neighbour Gaussian coupling), and
> `σ²_free(f) = ∫ (ωg)² dμ_GFF` with `g` the asym lattice embedding of
> `f`.

Setting: rectangular discrete lattice `Z_{Nt} × Z_{Ns}` with single
spacing `a`; `Ls` fixed; `Lt → ∞`. The bound is uniform in
`(L, Nt, Ns, a)`.

The `∃ K, C` (not `K, C = 1, 1`) is essential: in infinite volume,
the interacting susceptibility can exceed `2/m²`, so the `(K = 1, C = 1)`
form is false. The `∃ K, C` form is the standard constructive-QFT
input (Glimm-Jaffe Ch. 18-19; Simon Ch. V, VIII; Newman 1975).

## 2. Proposed 4-layer discharge

| Layer | Statement (informal) | What discharges it |
|---|---|---|
| **A** | `E[e^{tS}]_int ≤ exp(t² · Var_int(S) / 2)` for the joint Wick-ordered lattice measure (the Newman MGF Gaussian-domination) | Joint measure is in the Lee-Yang class ⟹ Newman's inequality |
| **B1** | At fixed `a, Ns`: `Var_int(ωf) ≤ C(a, Ns) · Var_free(ωf)`, via cylinder transfer matrix `T = e^{-aH_{Ns}}` having a positive isolated mass gap (compact + positivity-improving ⟹ Jentzsch) | Lattice Källén-Lehmann sum rule applied to TM spectral decomposition |
| **B2** | `C(a, Ns)` stays bounded as `a → 0`, `Ns → ∞` | Quasi-1D chessboard / Fröhlich-Simon-Spencer (Ls fixed ⟹ no full 2D cluster expansion needed) |
| **C** | Combine A + B2 ⟹ axiom with `K = 2`, `C = (sup_a C(a, Ns))/2` | Pure assembly (~50 lines) |

The cylinder advantage over the full-2D square case: `Ls` fixed makes
`L → ∞` a 1D thermodynamic limit, so the cylinder mass gap is
unconditional (no full 2D cluster expansion), and `B2` reduces to
chessboard rather than Glimm-Jaffe-Spencer.

In the proposed split:

* **A** is an axiom on the lee-yang side once the joint measure's
  Lee-Yang class is established. *Or* it's a theorem in lee-yang and an
  axiom-discharge in pphi2 — depending on which way the split goes (see
  questions below).
* **B1, B2** are pphi2 axioms (or proved later — out of scope here).
* **C** is a proved theorem in pphi2 (~50 lines).

This document focuses on **Layer A**. Layers B1 and B2 do not depend
on lee-yang and have a separate discharge path (shared with the
square's own `spectral_gap_uniform`, which is also still an open
axiom).

## 3. Why Layer A factors through lee-yang

Layer A's target is the Newman MGF inequality applied to the
**interacting** lattice measure `μ_int`. The inequality holds for any
measure in the Lee-Yang class. So Layer A reduces to:

> **(LY)**: `μ_int` is in the Lee-Yang class.

`μ_int` factors structurally as:

* A product of single-site **Wick-ordered weight factors**:
  `dν_a,P(φ_x) = Z_x⁻¹ exp(-a²:P(φ_x):) dφ_x` for each site `x`.
* A product of nearest-neighbour **coupling factors**:
  `exp(β · φ_x φ_y)` for each lattice edge `⟨x, y⟩`.
* Normalization by the lattice partition function `Z`.

For `(LY)` to follow we need:

* **(LY1)**: Each single-site Wick weight `ν_a,P` is Lee-Yang.
* **(LY2)**: The Lee-Yang class is closed under finite products of
  independent factors (with possibly different parameters).
* **(LY3)**: Each nearest-neighbour coupling factor, integrated
  out, preserves the Lee-Yang property of the remaining marginal.
  Standard tool: **Asano contractions** on the multivariate
  partition function viewed as a polynomial in single-site fugacities.

`(LY1)` is the Griffiths-Simon theorem: approximate `ν_a,P` weakly by
Asano-rescaled Ising measures, each of which is manifestly Lee-Yang
(single-site Ising = bilinear in a binary fugacity), and pass to the
limit via Hurwitz's theorem (zero localization is stable under locally
uniform convergence of entire functions on compacta).

`(LY2)` is the convolution / product closure of the Lee-Yang class
(characteristic functions multiply; the product of two functions in
Newman's class is in Newman's class via Hadamard factorization).

`(LY3)` is iterated Asano (Asano 1970; Ruelle 1971; Lieb-Sokal 1981);
this is the same machinery that proves the original Lee-Yang theorem
for the Ising partition function.

Then `(LY) := (LY1) + (LY2) + (LY3)`, and Layer A follows from `(LY)`
plus the Newman MGF inequality.

## 4. Proposed dependency split

### 4a. What goes in `lee-yang` (new Mathlib-only repo)

Initial release (Phase 1):

| File | Content |
|---|---|
| `LeeYang/Polynomial/RealZeros.lean` | `Polynomial.LeeYangCircle`, `Polynomial.NewmanClass` (∼ Hurwitz after Cayley) definitions; closure under multiplication, scaling, complex conjugation, derivative; connection lemmas Lee-Yang ↔ Newman ↔ Hurwitz via Cayley-Möbius. |
| `LeeYang/Polynomial/Asano.lean` | `Polynomial.asanoContract` operation; `Polynomial.asanoContract_preserves_zeroRegion` (Asano's main lemma); `Polynomial.iteratedAsano` for application over a finite graph. |
| `LeeYang/Measure/Newman.lean` | `MeasureTheory.Measure.IsLeeYang` predicate (characteristic function extends to entire in Newman's class); `IsLeeYang.mgf_le_gaussian` (Newman 1975 Thm 3); `IsLeeYang.mgf_abs_le` (`K = 2` variant); closure under independent product / convolution. |
| `LeeYang/Measure/GriffithsSimon.lean` | `MeasureTheory.Measure.evenPolynomialWick a P` definition; `evenPolynomialWick_isLeeYang` main theorem via Asano-rescaled Ising approximation + Hurwitz. |

Estimated Phase 1 scope: ~1500-2500 lines.

### 4b. What stays in pphi2

Layer A becomes a short adapter file `Pphi2/AsymTorus/AsymInteractingLeeYang.lean`
(new), ~50-150 lines, with three theorems:

| Theorem | Cites from lee-yang |
|---|---|
| `asymWickSiteMeasure_isLeeYang` (single-site `(LY1)` for the asym lattice) | `Measure.evenPolynomialWick_isLeeYang` |
| `asymInteractingMeasure_isLeeYang` (joint `(LY)`) | `Polynomial.iteratedAsano` over the asym lattice graph |
| `asymInteracting_mgf_gaussianDominated` (Layer A bound) | `Measure.IsLeeYang.mgf_abs_le` |

These hook the lee-yang general results to the pphi2 types
(`AsymLatticeField`, `interactingLatticeMeasureAsym`, etc.). They are
mechanical instantiations.

### 4c. What changes in the discharge of the axiom itself

After Layers A + B1 + B2 + C land, the file
`Pphi2/AsymTorus/AsymContinuumLimit.lean` converts the
`axiom asymInteracting_expMoment_volume_uniform` to a `theorem` whose
proof is just the Layer-C assembly (~50 lines), referencing Layer A
(from `AsymInteractingLeeYang.lean`) and Layers B1 + B2 (from the
transfer-matrix / chessboard workstream).

## 5. Things we are *not* asking about in this packet

* The provability or formalizability of Layers B1 / B2 (transfer-matrix
  mass gap + chessboard). Those are a separate workstream, share their
  discharge path with the square's open `spectral_gap_uniform` axiom,
  and are not on the lee-yang critical path.
* The detailed Lean implementation of any specific lemma.
* The reusability of lee-yang for non-pphi2 downstream consumers
  (gibbs-variational, lgt, etc.). We've already concluded that the
  reuse case is real and justifies a standalone repo.

## 6. Questions for vetting

**(Q1) Correctness of the Layer A factorization.** Does Layer A truly
reduce to `(LY) := (LY1) + (LY2) + (LY3)` plus the Newman MGF inequality?
Specifically:

* Is the factorization of `μ_int` as `single-site Wick × nearest-neighbour
  couplings / Z` the correct algebraic shape for invoking iterated Asano?
  Or do we need to keep the action in a different normal form (e.g.,
  high-temperature expansion, polymer representation) for Asano to apply
  cleanly?
* Does Asano contraction on the nearest-neighbour-coupling polynomial
  on the spin variables actually produce a Lee-Yang reduction in the
  way we claim — or does the rectangular `Nt × Ns` topology with
  periodic boundary conditions cause issues (e.g., long cycles)? The
  original Lee-Yang theorem was for ferromagnetic Ising on arbitrary
  graphs; does the (continuous-spin, Wick-ordered, finite-volume)
  asym lattice fall within the standard hypotheses?

**(Q2) Sufficiency of the lee-yang Phase 1 content.** Are the four
files listed in §4a sufficient for Layer A on the pphi2 side? In
particular:

* `Measure/Newman.lean` is stated for measures on `ℝ` (single-variable
  MGF). The pphi2 application needs the bound for the linear functional
  `S = ⟨ω, f⟩` under the joint multivariate measure. Is the right
  abstraction (a) "marginal is Lee-Yang ⟹ MGF bound", relying on `(LY)`
  for the joint measure plus a marginal projection lemma; or (b) a
  genuinely multivariate IsLeeYang predicate? If (b), should it be in
  Phase 1?
* For `(LY2)`, is "product of independent Lee-Yang measures is
  Lee-Yang" stated correctly as a closure for the `IsLeeYang` predicate,
  or does it need to be stated more carefully (e.g., assuming each
  marginal satisfies a Newman-class CF, the joint Fourier transform of
  the product satisfies a multivariate analogue)?
* For `(LY3)`, do we need `Polynomial.iteratedAsano` to live at a
  graph-theoretic level of abstraction (over an arbitrary finite simple
  graph with edge weights), or is a less general version (specialized
  to the rectangular lattice) cheaper?

**(Q3) Pphi2-side scope realism.** Is the ~50-150 line estimate for
the pphi2 adapter file (§4b) realistic? Are there friction points we
should anticipate:

* Bridging pphi2's existing Wick-polynomial infrastructure
  (`Pphi2/WickOrdering/*`, defined for the multivariate joint
  Gaussian) to lee-yang's single-site Wick measure
  `evenPolynomialWick`?
* Does the `InteractionPolynomial` type (which encodes
  "even degree, bounded below, positive leading coefficient") map
  cleanly onto the hypotheses of `evenPolynomialWick_isLeeYang`?
* The asym lattice with periodic boundary conditions: does the Asano
  argument apply directly, or does it need cycle-by-cycle bookkeeping
  to handle the wrap-around?

**(Q4) Risks / blockers.** What's the single thing most likely to make
this not work as planned? Examples to consider:

* Mathlib's polynomial / entire-function infrastructure being
  insufficient for the Cayley / Möbius work in `RealZeros.lean`.
* Hurwitz's theorem (zero localization under locally uniform
  convergence) not being in Mathlib in the right shape for
  `GriffithsSimon.lean`.
* The Wick-ordering convention used by pphi2 (which is *not* the same
  as the most common textbook convention — pphi2 uses
  `wickConstant_eq_variance` with the GJ `(a²)⁻¹` normalization on
  the asym lattice) creating a mismatch when we try to apply
  `evenPolynomialWick_isLeeYang`.

Please be specific where you have concrete knowledge of the
constructive-QFT / Lee-Yang literature; flag uncertainty where you
have it. Short (under 800 words total) is fine.
