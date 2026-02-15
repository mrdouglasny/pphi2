# Schwartz Map Lemmas: Inventory and Gaps

**Context:** What we need to fill sorrys in `pphi2/Pphi2/Basic.lean`, cross-referenced
with what Mathlib provides and what `aqft2` postulates.

## 1. What Mathlib Already Has

### SchwartzMap Instances (all complete)
| Instance | Location |
|----------|----------|
| `AddCommGroup 𝓢(E, F)` | `SchwartzMap.instAddCommGroup` |
| `Module 𝕜 𝓢(E, F)` | `SchwartzMap.instModule` |
| `TopologicalSpace 𝓢(E, F)` | via seminorm family |
| `ContinuousMapClass 𝓢(E, F) E F` | `SchwartzMap.instContinuousMapClass` |

### Seminorm API (from `Mathlib.Analysis.Seminorm`)
| Lemma | Statement | Status |
|-------|-----------|--------|
| `map_zero` | `p 0 = 0` | proved |
| `map_add_le_add` | `p (x + y) ≤ p x + p y` | proved |
| `map_neg_eq_map` | `p (-x) = p x` | proved |
| `map_smul_eq_mul` | `p (a • x) = ‖a‖ * p x` | proved |
| `apply_nonneg` | `0 ≤ p x` | proved |

### SchwartzMap.seminorm Specific
| Lemma | Statement | Status |
|-------|-----------|--------|
| `SchwartzMap.seminorm` | `ℕ → ℕ → Seminorm 𝕜 𝓢(E, F)` | defined |
| `SchwartzMap.le_seminorm` | `‖x‖^k * ‖itFDeriv n f x‖ ≤ seminorm k n f` | proved |
| `SchwartzMap.seminorm_le_bound` | upper bound from pointwise bound | proved |
| `SchwartzMap.norm_le_seminorm` | `‖f x‖ ≤ seminorm 0 0 f` | proved |

### Composition
| Lemma | Statement | Status |
|-------|-----------|--------|
| `SchwartzMap.compCLM` | `𝓢(E,F) →L[𝕜] 𝓢(D,F)` for temperate growth g | proved |
| `SchwartzMap.compCLMOfContinuousLinearEquiv` | `𝓢(E,F) →L[𝕜] 𝓢(D,F)` for CLE | proved |
| `SchwartzMap.derivCLM` | differentiation as CLM | proved |
| `SchwartzMap.laplacianCLM` | Laplacian as CLM | proved |

### Star/Conjugation (from `Mathlib.Algebra.Star`)
| Lemma | Statement | Status |
|-------|-----------|--------|
| `star_add` | `star (x + y) = star x + star y` | proved |
| `star_neg` | `star (-x) = -star x` | proved |
| `star_zero` | `star 0 = 0` | proved |
| `star_smul` | `star (a • x) = star a • star x` | proved |
| `star_star` | `star (star x) = x` | proved |
| `starRingEnd_self_apply` | `starRingEnd ℂ (starRingEnd ℂ z) = z` | proved |

Note: `starRingEnd ℂ` is `Complex.conj`, the complex conjugation ring endomorphism.

## 2. What aqft2 Postulates (Axioms)

These are textbook results not in Mathlib, declared as `axiom` in aqft2:

| Axiom | What It Says | Where |
|-------|-------------|-------|
| `schwartz_nuclear` | `𝓢(E,F)` is a nuclear space | NuclearSpace.lean |
| `hermiteFunction_seminorm_bound` | Hermite seminorms grow polynomially in n | HermiteFunctions.lean |
| `schwartz_hermite_expansion` | Hermite basis resolves any CLM | HermiteFunctions.lean |
| `schwartz_hermite_coefficient_decay` | Coefficients decay super-polynomially | HermiteFunctions.lean |
| `banach_steinhaus_schwartz` | Uniform boundedness for Schwartz CLMs | TextbookAxioms.lean |
| `gaussian_series_nuclear_convergence` | Gaussian series on nuclear spaces converge | TextbookAxioms.lean |

## 3. What pphi2 Needs (Grouped by Sorry)

### A. Rapid Decay Closure Under Operations

These are needed for `instAdd`, `instNeg`, `instZero`, `instModule.smul` on
both `TestFunctionCyl` and `TestFunctionCylℂ`.

**Lemma needed:** If `{fₙ}` and `{gₙ}` are ℤ-indexed families of Schwartz maps
with rapid decay of seminorms, then `{fₙ + gₙ}`, `{-fₙ}`, `{0}`, `{r • fₙ}`
also have rapid decay.

| Lemma | Proof Sketch | Difficulty |
|-------|-------------|------------|
| `rapidDecay_add` | Triangle inequality: `seminorm(fₙ+gₙ) ≤ seminorm(fₙ) + seminorm(gₙ)` via `map_add_le_add`. Bound by `(C₁+C₂)/(1+\|n\|)^{k+1}`. | **Easy.** All ingredients in Mathlib. ~15 lines. |
| `rapidDecay_neg` | `seminorm(-fₙ) = seminorm(fₙ)` via `map_neg_eq_map`. Same bound. | **Trivial.** 3 lines. |
| `rapidDecay_zero` | `seminorm(0) = 0` via `map_zero`. Bound `1/(1+\|n\|)^{k+1}` with C=1. | **Trivial.** 5 lines. |
| `rapidDecay_smul` | `seminorm(r•fₙ) = \|r\| * seminorm(fₙ)` via `map_smul_eq_mul`. Bound by `(\|r\|*C)/(1+\|n\|)^{k+1}`. | **Easy.** ~10 lines. Need `‖r‖ > 0 ∨ r = 0` case split for positivity of constant. |

### B. Reality Condition Closure Under Operations

Needed for `instAdd`, `instNeg`, `instZero`, `instModule.smul` on `TestFunctionCyl`.

The reality condition is: `f(-n)(t) = conj(f(n)(t))` pointwise.

| Lemma | Proof Sketch | Difficulty |
|-------|-------------|------------|
| `reality_add` | `(f+g)(-n)(t) = f(-n)(t) + g(-n)(t) = conj(f(n)(t)) + conj(g(n)(t)) = conj(f(n)(t) + g(n)(t))` via `star_add` / `map_add`. | **Easy.** ~8 lines. Need `starRingEnd` distributes over add. |
| `reality_neg` | `(-f)(-n)(t) = -(f(-n)(t)) = -conj(f(n)(t)) = conj(-f(n)(t))` via `star_neg` / `map_neg`. | **Easy.** ~5 lines. |
| `reality_zero` | `0(-n)(t) = 0 = conj(0) = conj(0(n)(t))` via `star_zero` / `map_zero`. | **Trivial.** 3 lines. |
| `reality_smul` | For r : ℝ, `(r•f)(-n)(t) = r * f(-n)(t) = r * conj(f(n)(t)) = conj(r * f(n)(t))` since `conj(↑r) = ↑r` for real r. Via `starRingEnd_ofReal` or `Complex.conj_ofReal`. | **Easy-Medium.** ~12 lines. The coercion ℝ → ℂ and showing `conj` fixes it requires finding the right Mathlib lemma. Likely `Complex.conj_ofReal` or `RCLike.conj_ofReal`. |

### C. AddCommGroup Laws

Needed for both `TestFunctionCyl` and `TestFunctionCylℂ`.

| Law | Proof Sketch | Difficulty |
|-----|-------------|------------|
| `add_assoc` | Extensionality on fourierMode, then `add_assoc` on `SchwartzMap`. | **Easy** if ext works. |
| `zero_add` | Extensionality, then `zero_add` on `SchwartzMap`. | **Easy.** |
| `add_zero` | Extensionality, then `add_zero` on `SchwartzMap`. | **Easy.** |
| `add_comm` | Extensionality, then `add_comm` on `SchwartzMap`. | **Easy.** |
| `neg_add_cancel` | Extensionality, then `neg_add_cancel` on `SchwartzMap`. | **Easy.** |

**Prerequisite:** An `ext` lemma for `TestFunctionCyl`:
```
f.fourierMode = g.fourierMode → f = g
```
This follows because `rapidDecay` and `reality` are Prop fields (proof-irrelevant
after `cases` + `subst`). ~5 lines.

### D. Module Laws

| Law | Proof Sketch | Difficulty |
|-----|-------------|------------|
| `one_smul` | Ext, then `one_smul` on `SchwartzMap`. | **Easy.** |
| `mul_smul` | Ext, then `mul_smul` on `SchwartzMap`. | **Easy.** |
| `smul_zero` | Ext, then `smul_zero` on `SchwartzMap`. | **Easy.** |
| `smul_add` | Ext, then `smul_add` on `SchwartzMap`. | **Easy.** |
| `add_smul` | Ext, then `add_smul` on `SchwartzMap`. | **Easy.** |
| `zero_smul` | Ext, then `zero_smul` on `SchwartzMap`. | **Easy.** |

Note: For `TestFunctionCylℂ`, the module is over ℂ, and `SchwartzMap ℝ ℂ` has
`Module ℂ` via the scalar action. Should just work.

### E. Topology

| Instance | What's Needed | Difficulty |
|----------|--------------|------------|
| `TopologicalSpace (TestFunctionCyl d L)` | Product topology on `ℤ → SchwartzMap ℝ ℂ` restricted to rapid decay subset. Or: initial topology from all seminorm evaluations. | **Hard.** Defining the right topology is nontrivial. The Schwartz space on ℝ × S¹_L should have the projective limit topology from the mode decomposition. Best left as sorry or axiom for now. |
| `IsTopologicalAddGroup` | Addition is continuous in the above topology. | **Hard.** Depends on topology definition. |
| `ContinuousSMul ℝ` | Scalar multiplication is continuous. | **Hard.** Same. |

### F. QFTFramework Operations

| Definition | What's Needed | Difficulty |
|-----------|--------------|------------|
| `complexPairingCyl` | Decompose complex test fn into Re/Im parts, pair each with distribution. Need: extracting real/imaginary parts of a SchwartzMap preserves Schwartz class and rapid decay. | **Medium.** The math is clear but showing `Complex.re ∘ f` and `Complex.im ∘ f` are Schwartz requires `SchwartzMap.compCLM` with `Complex.reCLM`/`Complex.imCLM`. These CLMs exist in Mathlib but checking `HasTemperateGrowth` is fiddly. |
| `timeReflectionCyl` | Compose each mode with negation on ℝ. Use `SchwartzMap.compCLMOfContinuousLinearEquiv` with `ContinuousLinearEquiv.neg ℝ`. | **Medium.** The composition CLM exists. Need to show rapid decay is preserved (same indices, same bounds) and reality is preserved. ~20 lines once you find the right CLM. |
| `positiveTimeSubmoduleCyl.zero_mem'` | `tsupport 0 = ∅ ⊆ Ioi 0`. | **Trivial.** `tsupport_zero` or `Function.tsupport_zero` gives `tsupport 0 = ∅`. |
| `positiveTimeSubmoduleCyl.add_mem'` | `tsupport (f+g) ⊆ tsupport f ∪ tsupport g ⊆ Ioi 0`. | **Easy.** Via `tsupport_add` or similar. Need union of subsets of Ioi 0 is subset of Ioi 0. |
| `positiveTimeSubmoduleCyl.smul_mem'` | `tsupport (r•f) ⊆ tsupport f ⊆ Ioi 0`. | **Easy.** Via `tsupport_smul` or `Function.tsupport_smul_left/right`. |
| `translateTestFunCyl` | Phase rotation + time shift of each mode. Time shift via `SchwartzMap.compCLMOfContinuousLinearEquiv` with translation. Phase rotation is multiplication by a unit complex number. | **Medium-Hard.** Translation on ℝ is an affine map, not linear, so `compCLMOfContinuousLinearEquiv` doesn't directly apply. May need a custom argument or `SchwartzMap.compCLM` with the translation map (which has temperate growth). Rapid decay + reality proofs also needed. |
| `symmetryActionCyl` | Blocked — `SymmetryGroupCyl` is axiomatized. | **Blocked.** Must stay sorry. |
| `timeTranslationDistCyl` | Dual action `⟨T_s ω, f⟩ = ⟨ω, T_{-s} f⟩`. Requires `translateTestFunCyl` to be defined first, then construct the new WeakDual element. | **Medium.** Straightforward once translation is defined, but need to show the resulting functional is continuous in the test function. |

## 4. Recommended Priority

### Phase 1: Algebraic (straightforward, high impact)
1. `ext` lemma for `TestFunctionCyl` and `TestFunctionCylℂ`
2. All `AddCommGroup` fields (5 each × 2 structures)
3. All `Module` fields (6 each × 2 structures)
4. `rapidDecay_zero` and `reality_zero` (for `instZero`)
5. `rapidDecay_neg` and `reality_neg` (for `instNeg`)
6. `rapidDecay_add` and `reality_add` (for `instAdd`)
7. `rapidDecay_smul` and `reality_smul` (for `instModule.smul`)

### Phase 2: Submodule (easy, important for OS3)
8. `positiveTimeSubmoduleCyl.zero_mem'`
9. `positiveTimeSubmoduleCyl.add_mem'`
10. `positiveTimeSubmoduleCyl.smul_mem'`

### Phase 3: Operations (medium, needed for OS axioms)
11. `timeReflectionCyl` via `compCLMOfContinuousLinearEquiv`
12. `complexPairingCyl` via Re/Im decomposition
13. `translateTestFunCyl` (hardest of this group)
14. `timeTranslationDistCyl` (depends on 13)

### Leave as sorry/axiom
- Topology instances (hard, requires defining the Fréchet topology)
- `symmetryActionCyl` (blocked on axiomatized group)
- Nuclearity (textbook result, axiomatized in aqft2 too)

## 5. Key Mathlib Lemma Names for Quick Reference

```
-- Seminorm
map_add_le_add       -- triangle inequality
map_neg_eq_map       -- p(-x) = p(x)
map_zero             -- p(0) = 0
map_smul_eq_mul      -- p(a•x) = ‖a‖ * p(x)
apply_nonneg         -- 0 ≤ p(x)

-- Star / conjugation
star_add             -- star(a+b) = star(a) + star(b)
star_neg             -- star(-a) = -star(a)
star_zero            -- star(0) = 0
star_smul            -- star(a•x) = star(a)•star(x)
Complex.conj_ofReal  -- conj(↑r) = ↑r for r : ℝ

-- SchwartzMap composition
SchwartzMap.compCLMOfContinuousLinearEquiv  -- compose with CLE
ContinuousLinearEquiv.neg                   -- negation as CLE

-- Support
Function.tsupport_zero  -- tsupport(0) = ∅
tsupport_add            -- tsupport(f+g) ⊆ tsupport(f) ∪ tsupport(g)  (check name)
```
