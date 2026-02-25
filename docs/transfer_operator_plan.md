# Plan: Define transferOperatorCLM from kernel factorization

## Goal

Replace the axiom `transferOperatorCLM` with a definition, and prove
`transferOperator_isSelfAdjoint` as a theorem. This eliminates 2 axioms
(the CLM existence and self-adjointness) by defining the operator from
its kernel factorization.

## Key insight: kernel factorization

The transfer kernel factors as:

```
T(ψ, ψ') = exp(-½|ψ-ψ'|²) · exp(-(a/2)h(ψ)) · exp(-(a/2)h(ψ'))
```

This means the integral operator `(Tf)(ψ) = ∫ T(ψ,ψ') f(ψ') dψ'` factors as:

```
T = M_w ∘ Conv_G ∘ M_w
```

where:
- `w(ψ) = exp(-(a/2) · h(ψ))` — bounded positive weight (since `h ≥ -B`)
- `G(x) = exp(-½|x|²)` — Gaussian kernel
- `M_w` = multiplication by `w` (a CLM on L²)
- `Conv_G` = convolution with `G` (a CLM on L² by Young's inequality)

## Building blocks

### Step 1: Multiplication operator (from aqft2) ✅ READY

Adapt `linfty_mul_L2_CLM` from `aqft2/OSforGFF/FunctionalAnalysis.lean`
to work over `ℝ` (the aqft2 version is over `ℂ`).

Given `w : α → ℝ` bounded and measurable, construct:
```lean
def mulCLM (w : α → ℝ) (hw_meas : Measurable w) (C : ℝ) (hC : 0 < C)
    (hw_bound : ∀ᵐ x ∂μ, ‖w x‖ ≤ C) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ
```

This uses Hölder's inequality: `‖w · f‖₂ ≤ ‖w‖_∞ · ‖f‖₂`.

**Self-adjointness of M_w**: `⟨f, M_w g⟩ = ∫ f·w·g = ∫ w·f·g = ⟨M_w f, g⟩`
since `w` is real-valued. This should be provable from the pointwise spec.

### Step 2: Gaussian convolution operator (NEW AXIOM)

Axiomatize: convolution with `G ∈ L¹` is a CLM on `L²`.

```lean
axiom gaussianConvCLM (Ns : ℕ) :
    Lp ℝ 2 (volume : Measure (SpatialField Ns)) →L[ℝ]
    Lp ℝ 2 (volume : Measure (SpatialField Ns))
```

with a specification axiom:
```lean
axiom gaussianConvCLM_spec (f : L2SpatialField Ns) :
    gaussianConvCLM Ns f =ᵐ[volume] fun ψ =>
      ∫ ψ', exp(-½ * ‖ψ - ψ'‖² ) * f ψ' ∂volume
```

**Self-adjointness of Conv_G**: Since `G(x) = G(-x)` (symmetric Gaussian),
convolution with G is self-adjoint. This could be proved from the spec +
Fubini, or axiomatized.

**Alternative**: Instead of axiomatizing Conv_G separately, axiomatize
Young's inequality `‖g * f‖₂ ≤ ‖g‖₁ · ‖f‖₂` and construct the CLM.
This is more general but harder to use.

### Step 3: Define transferOperatorCLM

```lean
def transferOperatorCLM (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    L2SpatialField Ns →L[ℝ] L2SpatialField Ns :=
  let w := fun ψ => exp(-(a/2) * spatialAction Ns P a mass c ψ)
  mulCLM w ... ∘L gaussianConvCLM Ns ∘L mulCLM w ...
```

### Step 4: Prove self-adjointness

From self-adjointness of each factor:
```
⟨f, M_w (G (M_w g))⟩
= ⟨M_w f, G (M_w g)⟩           (M_w self-adjoint)
= ⟨G (M_w f), M_w g⟩           (Conv_G self-adjoint)
= ⟨M_w (G (M_w f)), g⟩         (M_w self-adjoint)
= ⟨Tf, g⟩
```

### Step 5: Keep remaining axioms

- `transferOperator_isCompact` — KEEP as axiom (proving compactness
  requires Hilbert-Schmidt theory not in Mathlib)
- `transferOperator_inner_nonneg` — KEEP as axiom (Perron-Frobenius)
- Eigenvalue axioms — KEEP (sorted eigenvalue sequence)

## Axiom accounting

**Before**: 8 axioms in L2Operator.lean
- `transferOperatorCLM` (existence)
- `transferOperator_isSelfAdjoint`
- `transferOperator_inner_nonneg`
- `transferOperator_isCompact`
- `transferEigenvalue` (sorted sequence)
- `transferEigenvalue_pos`
- `transferEigenvalue_antitone`
- `transferEigenvalue_ground_simple`

**After**: 7 axioms (+ 1 proved theorem)
- `gaussianConvCLM` (NEW — replaces transferOperatorCLM)
- `gaussianConvCLM_isSelfAdjoint` (NEW — for the Conv_G factor)
- `transferOperator_inner_nonneg` (KEEP)
- `transferOperator_isCompact` (KEEP)
- `transferEigenvalue` (KEEP)
- `transferEigenvalue_pos` (KEEP)
- `transferEigenvalue_antitone` (KEEP)
- `transferEigenvalue_ground_simple` (KEEP)
- `transferOperatorCLM` → DEFINITION (from factorization)
- `transferOperator_isSelfAdjoint` → PROVED THEOREM

Net change: -1 axiom (8 → 7), but the axioms are cleaner and more
foundational. The Gaussian convolution axiom is a standard result
(Young's inequality) that could eventually be proved from Mathlib.

## File structure

- `Pphi2/TransferMatrix/L2Multiplication.lean` — mulCLM (adapted from aqft2)
- `Pphi2/TransferMatrix/L2Operator.lean` — modified to use definition
