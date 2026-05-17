# Canonical on-site variance identification — discharge plan

If the variance-identification lemmas needed by S3
([`canonical-2site-wick-formula-plan.md`](canonical-2site-wick-formula-plan.md))
are landed as small focused axioms in `FieldDecomposition.lean`, here is
the plan to eventually discharge them into theorems.

## The three axioms

```lean
-- 1. Smooth on-site translation invariance
axiom canonicalSmoothFieldFunction_self_moment_const
    (T : ℝ) (hT : 0 < T) (x : FinLatticeSites d N) :
    canonicalSmoothFieldFunction_self_moment_diag d N a mass ha hmass T hT x =
    canonicalSmoothFieldFunction_self_moment_diag d N a mass ha hmass T hT 0

-- 2. Smooth Wick-constant identification
axiom canonicalSmoothFieldFunction_self_moment_eq_smoothWickConstant
    (T : ℝ) (hT : 0 < T) (x : FinLatticeSites d N) :
    canonicalSmoothFieldFunction_self_moment_diag d N a mass ha hmass T hT x =
    smoothWickConstant d N a mass T

-- 3. Rough analogue
axiom canonicalRoughFieldFunction_self_moment_eq_roughWickConstant
    (T : ℝ) (hT : 0 < T) (x : FinLatticeSites d N) :
    canonicalRoughFieldFunction_self_moment_diag d N a mass ha hmass T hT x =
    roughWickConstant d N a mass T
```

(Where `_diag x = canonicalSmoothFieldFunction_self_moment x x`; both are
real numbers obtained from the existing `canonicalSmoothFieldFunction_self_moment`
private lemma evaluated on the diagonal.)

Axioms 2 and 3 imply axiom 1 (since `smoothWickConstant` is x-independent),
so really only two axioms; axiom 1 is a useful intermediate lemma.

## Mathematical content

For a translation-invariant operator `f(M)` on the lattice torus
(where `M = -Δ_a + m²` is the lattice mass operator and `f` is any
spectral function), the kernel `K(x, y) = ⟨δ_x, f(M) δ_y⟩` satisfies:

1. Translation invariance: `K(x + z, y + z) = K(x, y)` for all `z`.
2. Diagonal value: `K(x, x) = K(0, 0) = (1/|Λ|) · tr(f(M)) = (1/|Λ|) · Σ_λ f(λ)`.

For the smooth covariance, `f(λ) = exp(-Tλ)/λ`, giving
`K(x, x) = (1/|Λ|) · Σ_λ exp(-Tλ)/λ`. Multiplying by `(a^d)⁻¹` (the
Glimm–Jaffe scaling) gives `smoothWickConstant`. Same argument for the
rough side with `f(λ) = (1 - exp(-Tλ))/λ`.

## Discharge route B (recommended) — abstract translation invariance

### Step 1: define the lattice translation action

`FinLatticeSites d N = Fin d → ZMod N` is an additive group. Define:
```lean
def latticeTranslate (z : FinLatticeSites d N) :
    FinLatticeField d N → FinLatticeField d N :=
  fun φ x => φ (x + z)
```
Linearity + measurability are immediate.

### Step 2: prove the lattice mass operator commutes with translations

The lattice Laplacian `Δ_a` is defined via nearest-neighbour differences,
which are translation-invariant on the periodic torus:
```lean
lemma latticeMassOperator_comm_translate (z : FinLatticeSites d N) :
    latticeMassOperator ∘ latticeTranslate z = latticeTranslate z ∘ latticeMassOperator
```
Direct computation from the explicit formula. Maybe already in
`gaussian-field/Lattice/` somewhere — search first.

### Step 3: lift to `f(M)` via functional calculus

Any function `f` of `M` (defined via spectral functional calculus, or
directly via eigendecomposition for our finite-dim setting) commutes
with anything `M` commutes with:
```lean
lemma spectralFunctional_comm_translate (f : ℝ → ℝ) (z : FinLatticeSites d N) :
    Matrix.cfc f latticeMassOperator ∘ latticeTranslate z =
    latticeTranslate z ∘ Matrix.cfc f latticeMassOperator
```
For finite-dim Hermitian `M` and continuous `f`, this is `cfc.commute_of_commute`
or similar. Concrete approach: write `f(M) = Σ_λ f(λ) · P_λ` where `P_λ`
are eigenprojections, show each `P_λ` commutes with translations (since
eigenspaces are translation-invariant — the mass operator is
translation-invariant).

### Step 4: kernel translation invariance

Define `K_f(x, y) = ⟨e_x, f(M) e_y⟩` where `e_x` is the indicator at site `x`.
From step 3:
```
K_f(x + z, y + z) = ⟨e_{x+z}, f(M) e_{y+z}⟩
                  = ⟨translate_z(e_x), f(M) translate_z(e_y)⟩
                  = ⟨translate_z(e_x), translate_z(f(M) e_y)⟩    [by step 3]
                  = ⟨e_x, f(M) e_y⟩                              [by isometry of translation]
                  = K_f(x, y)
```

In particular `K_f(x, x) = K_f(0, 0)`. **This proves axiom 1.**

### Step 5: trace identity

```
tr(f(M)) = Σ_x K_f(x, x) = |Λ| · K_f(0, 0)        -- by step 4
        = Σ_λ f(λ)                                 -- spectral trace
```
The first equality is `Matrix.trace_eq_sum_diag` (mathlib). The second
is the spectral trace formula; for finite Hermitian: `tr(f(M)) = Σ_i f(eigenvalues i)`.
Look for `Matrix.IsHermitian.trace_eq_sum_eigenvalues` or
`Matrix.IsHermitian.cfc_trace` in mathlib.

### Step 6: identify with `smoothWickConstant`

Apply step 5 with `f(λ) = exp(-Tλ)/λ` (smooth) and `f(λ) = (1-exp(-Tλ))/λ`
(rough). Get:
```
K_smooth(0, 0) = (1/|Λ|) · Σ_λ exp(-T·λ)/λ
              = (1/|Λ|) · Σ_m smoothCovEigenvalue d N a mass T m
```
Match against `smoothWickConstant`'s definition (after the `(a^d)⁻¹`
factor, which `canonicalSmoothFieldFunction_self_moment` carries via its
prefactor). **Axiom 2 follows.** Same for axiom 3.

### Step 7: relate `K_f` to `canonicalSmoothFieldFunction_self_moment`

The existing self-moment formula at `FieldDecomposition.lean:487` gives the
2-point function in DFT-product-basis form. We need to identify it with
the operator-kernel `K_f`. This is the spectral decomposition of `M`:
the DFT-product basis diagonalises `M` (eigenvalue `canonicalEigenvalue m`),
so the two formulas are the same expanded in different bases.

The bridge already exists in the codebase: `abstract_spectral_eq_dft_spectral_family`
(in `Lattice/LatticeFourierProduct.lean`) gives this. Use it to rewrite the
self-moment formula into operator-kernel form.

## Discharge route A (fallback) — direct cosine/sine pairing

If route B's operator-theoretic infrastructure (steps 3, 5, 7) turns out to
require non-trivial mathlib glue, fall back to direct calculation in the
DFT-product basis.

### Mathematical content (1D case first)

The 1D real DFT basis on `ZMod N` consists of:
- `m = 0`: `basisFun(0)(x) = 1`, `normSq(0) = N`
- For each `0 < k < N/2`: a cos/sin pair at frequency `2πk/N`,
  `normSq = N/2` each
- (if `N` is even) `m = N/2`: Nyquist, `basisFun(N/2)(x) = (-1)^x`,
  `normSq = N`

Per-site contribution `(basisFun m x)² / normSq m`:
- `m = 0`: `1/N`
- cos/sin pair at freq `k`: cos²(2πkx/N)·(2/N) + sin²(2πkx/N)·(2/N)
  = `(cos² + sin²)·(2/N) = 2/N` ⟹ averaged per mode `1/N`
- Nyquist: `1/N`

So per-site sum over modes (with eigenvalues `λ_m` shared by paired modes):
```
Σ_m λ_m · (basisFun m x)² / normSq m
  = λ_0 · 1/N
  + Σ_{0 < k < N/2} λ_k · 2/N             [cos/sin pair shares λ_k, so contributes 2λ_k/N]
  + λ_{N/2} · 1/N                           [Nyquist, if applicable]
  = (1/N) · Σ_m λ_m                          [counting cos and sin separately = total |Λ| modes]
```

The key identity: cos/sin paired modes share eigenvalue (since
`latticeEigenvalue1d` depends only on the frequency, not on cos vs sin).

### d-dimensional case

Factorise the DFT-product basis: `basisFun(m)(x) = ∏_i basisFun_1D(m_i)(x_i)`,
`normSq(m) = ∏_i normSq_1D(m_i)`. The eigenvalue is
`canonicalEigenvalue m = Σ_i latticeEigenvalue1d N a (m_i) + mass²`.

Pairing now happens per coordinate. The identity becomes a tensor-product
of 1D pairing identities:
```
Σ_m canonicalSmoothWeight m · (basisFun m x)² / normSq m
  = (1/|Λ|) · Σ_m canonicalSmoothWeight m
```

### Lean proof outline

- `latticeFourierBasis_sq_pair_const` (1D pairing): for each frequency
  `k`, `(basisFun cos_k x)² / (N/2) + (basisFun sin_k x)² / (N/2) = 2/N`.
  Direct computation from the cos² + sin² = 1 identity.
- `latticeFourierProductBasis_sq_sum` (d-dim): per-site sum over all
  modes equals `1`. Tensor-product of 1D pairing.
- Weighted form: `Σ_m λ_m · (basisFun m x)² / normSq m = (1/|Λ|) · Σ_m λ_m`
  when `λ` depends only on the multi-index `m_i` collection (paired modes
  share eigenvalues). For the smooth/rough eigenvalues this is the case.
- Identification with `smoothWickConstant`: use
  `sum_latticeEigenvalue_eq_sum_latticeEigenvalue1d_family` to bridge
  the integer-indexed `Σ_m smoothCovEigenvalue m` (matrix-spectral)
  to the DFT-product `Σ_m canonicalSmoothWeight m`.

Estimated size: ~300-500 lines of careful indexing in `FieldDecomposition.lean`
(or a new helper file `Pphi2/NelsonEstimate/CanonicalDFTPairing.lean`).

## Mathlib survey to do first

Before either route, search mathlib for:

- `Matrix.IsHermitian.cfc` or `Matrix.cfc` — continuous functional calculus
  for Hermitian matrices
- `Matrix.trace_eq_sum_eigenvalues` — spectral trace
- `Matrix.commute_of_commute` for spectral functional calculus
- Translation-invariant operators on torus / `MeasurePreserving` for the
  lattice translation action
- `Finset.inner_apply_eq_sum` or similar for the kernel formula

If route B's infrastructure is largely mathlib-supported, prefer it. If
not (i.e., heavy glue work), prefer route A's direct calculation.

## Acceptance criteria

- All three lemmas proved as theorems, replacing the axioms.
- `lake build` clean.
- `#print axioms canonicalSmoothFieldFunction_self_moment_eq_smoothWickConstant`
  shows only `[propext, Classical.choice, Quot.sound]`.
- The axioms are removed from `FieldDecomposition.lean`.
- Downstream `canonical-2site-wick-formula-plan.md` work in
  `RoughErrorBound.lean` (S3 discharge) is unblocked and the relevant
  pphi2 sorry is removed.

## Estimate (recalibrated to local norms)

- Route B (preferred, if mathlib infrastructure is mostly in place):
  ~1-2 weeks active.
- Route A (fallback, direct cosine/sine pairing):
  ~2-3 weeks active for the 1D pairing + d-dim tensorisation + Wick
  constant identification.
- Mathlib survey to determine which: ~1-2 days.
