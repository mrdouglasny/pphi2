# Route B': Constructing P(φ)₂ on the Cylinder via IR Limit

**Updated**: 2026-03-20

## 1. Goal

Construct a probability measure ν on S'(S¹_{Ls} × ℝ) — distributions on the
cylinder with spatial circle of circumference Ls and infinite time axis ℝ —
satisfying the Osterwalder-Schrader axioms OS0–OS3. The cylinder geometry
is the natural setting for the OS axioms because:

- **ℝ gives a clean time axis**: time reflection Θ: t ↦ -t is an involution
  with a well-defined positive-time half-space {t > 0}.
- **S¹ gives finite spatial volume**: the mass gap is discrete (spectral gap
  of the transfer matrix), making clustering (OS4) accessible.
- **No IR divergences in the spatial direction**: the circle circumference Ls
  is fixed, and only the time direction needs an infinite-volume limit.

## 2. The Two-Step Construction

Route B' reaches the cylinder in two limits:

### Step 1: UV limit (N → ∞ at fixed Lt, Ls)

Start with the lattice (ℤ/Nℤ)² with geometric-mean spacing a = √(Lt·Ls)/N.
The interacting lattice measure μ^{lat}_{N} on (ℤ/Nℤ)² is:

  dμ^{lat}_{N} = (1/Z_N) · exp(-V_N(φ)) · dμ^{GFF}_{N}

where V_N is the Wick-ordered interaction and μ^{GFF}_{N} is the lattice
Gaussian free field. As N → ∞, the lattice approximation converges to a
continuum measure μ_{Lt,Ls} on the asymmetric torus T_{Lt,Ls}.

**Status**: Fully proved in `AsymTorus/AsymTorusOS.lean` (**0 axioms, 0 sorries**).
OS0 (analyticity), OS1 (regularity), and OS2 (translation + time reflection
invariance) are all verified for the continuum torus measure.

### Step 2: IR limit (Lt → ∞ at fixed Ls)

Take a sequence Lt_n → ∞. Each torus measure μ_{Lt_n, Ls} satisfies
OS0–OS2. Pull back to the cylinder via periodization embedding, then
extract a weak limit ν on S¹_{Ls} × ℝ.

**Status**: 0 local IR-limit axioms and 0 sorries in pphi2. OS0, OS2, and the
OS3 limit transfer are proved conditional on the explicit family-level inputs
`AsymTorusSequenceHasUniformGreenMomentBound` and
`CylinderMeasureSequenceEventuallyReflectionPositive`.

## 3. The Embedding: Cylinder → Torus

### 3.1 Test function spaces

The cylinder test function space is the nuclear tensor product:

  CylinderTestFunction Ls = C∞(S¹_{Ls}) ⊗̂ 𝓢(ℝ)

where C∞(S¹_{Ls}) is smooth Ls-periodic functions (spatial) and 𝓢(ℝ) is
Schwartz class functions (temporal). A test function f ∈ CylinderTestFunction Ls
is morally a function f(x, t) with x periodic in Ls and t decaying rapidly.

The torus test function space is:

  AsymTorusTestFunction Lt Ls = C∞(S¹_{Lt}) ⊗̂ C∞(S¹_{Ls})

Morally a function g(t, x) periodic in both Lt (temporal) and Ls (spatial).

### 3.2 Periodization

The key map is periodization `periodizeCLM Lt : 𝓢(ℝ) →L[ℝ] C∞(S¹_{Lt})`:

  (periodize_{Lt} h)(t) = Σ_{k ∈ ℤ} h(t + k·Lt)

This wraps a Schwartz function onto a circle of period Lt. The sum converges
absolutely because h is rapidly decaying. Key properties (all proved):

- **Pointwise formula**: `periodizeCLM_apply` gives the tsum representation
- **Time translation intertwining**: `periodize(T_τ h) = T_τ(periodize h)`
  (reindexing the sum over ℤ)
- **Time reflection intertwining**: `periodize(Θh) = Θ(periodize h)`
  (reindexing k → -k)
- **No wrap-around for large Lt**: for h supported in [-T, T] and Lt > 2T,
  periodize(h) agrees with h on [0, Lt/2] (only k=0 term is nonzero)

### 3.3 The embedding CLM

The embedding `cylinderToTorusEmbed Lt Ls` maps cylinder test functions
to torus test functions by periodizing the temporal factor:

  embed = swap ∘ (id_{C∞(S¹_{Ls})} ⊗ periodize_{Lt})

For a pure tensor g ⊗ h ∈ C∞(S¹_{Ls}) ⊗̂ 𝓢(ℝ):

  embed(g ⊗ h) = periodize_{Lt}(h) ⊗ g ∈ C∞(S¹_{Lt}) ⊗̂ C∞(S¹_{Ls})

The swap is needed because the torus convention puts time first.

This is a **definition** (not an axiom) in both pphi2 and gaussian-field.

### 3.4 Pullback on configurations

A torus configuration ω_torus (a distribution on T_{Lt,Ls}) pulls back
to a cylinder configuration ω_cyl via:

  (pullback ω_torus)(f) = ω_torus(embed f)

This defines `cylinderPullback Lt Ls : Configuration(AsymTorusTF) → Configuration(CylinderTF)`,
which is continuous (proved via `WeakDual.continuous_of_continuous_eval`).

The pullback measure is the pushforward:

  ν_{Lt} = (pullback)_* μ_{Lt} = cylinderPullbackMeasure Lt Ls μ_{Lt}

### 3.5 Intertwining with symmetries (proved)

The embedding commutes with time translation and time reflection:

  embed(T_{0,τ} f) = T_{(τ,0)}(embed f)     [time translation]
  embed(Θ f) = Θ_torus(embed f)             [time reflection]

**Proof technique**: The `cylinderToTorus_clm_ext_of_pure` lemma reduces
CLM equality on the NTP to agreement on pure tensors. On pure tensors,
the identity follows from the periodization intertwining theorems.

This is a novel technique: two CLMs on a nuclear tensor product that agree
on all pure tensors are equal, by the density of pure tensors via the
DyninMityagin basis expansion (`rapidDecay_expansion` + `basisVec_eq_pure`).

## 4. OS2: Translation/Reflection Invariance (Proved)

### At each finite Lt (exact, no limiting argument)

Since periodization perfectly intertwines time shifts:

  Z_{Lt}(T_τ f) = ∫ exp(iω(T_τ f)) dν_{Lt}
               = ∫ exp(iω_torus(T_{τ,0}(embed f))) dμ_{Lt}     [pullback + intertwining]
               = ∫ exp(iω_torus(embed f)) dμ_{Lt}               [torus translation invariance]
               = Z_{Lt}(f)

So the pullback measure is EXACTLY time-translation invariant at every finite Lt.
Similarly for time reflection. This is purely algebraic — no limiting argument.

### For the limit (via characteristic functional convergence)

The theorem `cylinderIRLimit_exists`, conditional on the eventual
Green-controlled moment input, provides characteristic-functional convergence:
Z_{Lt_n}(f) → Z(f) for all f along the extracted subsequence. Since
Z_{Lt_n}(f) = Z_{Lt_n}(Θf) at every n (exact reflection invariance), taking
the limit:

  Z(f) = lim Z_{Lt_n}(f) = lim Z_{Lt_n}(Θf) = Z(Θf)

This uses `tendsto_nhds_unique`: if a_n → L₁ and a_n = b_n → L₂, then L₁ = L₂.

## 5. Conditional Theorems and Remaining Inputs

### 5.1 Uniform second moment bound (`cylinderIR_uniform_second_moment`)

**Statement**: Given uniform Green-controlled constants `KG, CG`, there exist
`C₁, C₂ > 0` and a continuous seminorm q on `CylinderTestFunction Ls` such
that for all `Lt ≥ 1` and all torus measures μ satisfying
`MeasureHasGreenMomentBound Ls mass hmass KG CG μ`:

  ∫ (ω f)² dν_{Lt} ≤ C₁ · q(f)² + C₂

**Mathematical content**: The second moment of the cylinder field is bounded
uniformly in the time period. This is the core tightness input.

**Proof chain**:

1. `MeasureHasGreenMomentBound` gives `∫ exp(|ω g|) dμ ≤ KG · exp(CG · G(g,g))`.
2. The method-of-images estimate `torusGreen_uniform_bound` controls
   `G(embed f, embed f)` by a cylinder seminorm uniformly for `Lt ≥ 1`.
3. `cylinderIR_uniform_exponential_moment` gives the uniform cylinder
   exponential moment.
4. The elementary inequality `x² ≤ 2 e^|x|`, with a scaling optimization,
   gives the additive second-moment bound.

**Why it matters**: This bound feeds into the Mitoma-Chebyshev tightness
criterion, which is the gateway to Prokhorov extraction.

### 5.2 Uniform exponential moment bound (`cylinderIR_uniform_exponential_moment`)

**Statement**: There exist K, C > 0 and continuous seminorm q such that:

  ∫ exp(|ω f|) dν_{Lt} ≤ K · exp(C · q(f)²)

uniformly in Lt ≥ 1.

**Mathematical content**: The exponential moments (moment generating function)
are uniformly bounded. This is stronger than second moments and is needed
for OS0 analyticity.

**Proof chain**: The theorem assumes `MeasureHasGreenMomentBound` for the
torus measure with constants uniform in `Lt`. Apply this to `g = embed(f)` and
compose with the method-of-images bound on the torus Green form. The abstract
`AsymSatisfiesTorusOS.os1` seminorm is deliberately not used, because it does
not encode the uniform Green control needed as `Lt → ∞`.

**Why it matters**: Without exponential moment bounds, we can only prove
pointwise convergence of the characteristic function on the real axis —
insufficient for the proved integral analyticity argument. The exponential
bound supplies compact-set domination for `analyticOnNhd_integral`.

### 5.3 IR limit existence (`cylinderIRLimit_exists`)

**Statement**: Given `Lt_n → ∞`, probability measures `μ_n` on `T_{Lt_n,Ls}`,
and the eventual sequence-level input `AsymTorusSequenceHasUniformGreenMomentBound`,
there exist a subsequence φ and a probability measure ν on S¹_{Ls} × ℝ such
that bounded-continuous observables and characteristic functionals converge:

  ∫ exp(iωf) dν_{φ(n)} → ∫ exp(iωf) dν  for all f

**Mathematical content**: The family of pulled-back cylinder measures is
tight (compact in the weak topology), so Prokhorov's theorem gives a
convergent subsequence.

**Proof chain**:
1. Combine `AsymTorusSequenceHasUniformGreenMomentBound` with `Lt → ∞` to pass
   to a tail where both the Green bound and `Lt ≥ 1` hold.
2. Uniform second moments (§5.1) → for each f, the 1D marginals {(ev_f)_* ν_{Lt}}
   have uniformly bounded variance.
3. Mitoma-Chebyshev criterion: 1D tightness ⟹ tightness on S'(S¹ × ℝ)
   (this is `configuration_tight_of_uniform_second_moments` in gaussian-field)
4. Prokhorov's theorem: tightness on the configuration space gives a
   bounded-continuous convergent subsequence
5. Characteristic-functional convergence is then derived directly from
   bounded-continuous convergence by the cos/sin decomposition, avoiding any
   unformalized Lévy-continuity step in the Route B′ Lean proof

**Why characteristic functionals**: Convergence ∫ exp(iωf) dν_n → ∫ exp(iωf) dν
is needed (not just first moments ∫ ωf dν_n → ∫ ωf dν) because OS2
transfers through characteristic functionals, and OS0 requires analytic
continuation of the characteristic functional.

### 5.4 OS0: Analyticity

**Statement**: The multivariate generating functional

  Z(z₁,...,z_n) = ∫ exp(Σᵢ zᵢ · ω(Jᵢ)) dν

is entire analytic on ℂⁿ for any test functions J₁,...,Jₙ.

**Proof route**:
1. `cylinderIRLimit_exists` gives bounded-continuous convergence of a pulled-back
   subsequence to the limit measure.
2. `limit_exponential_moment` transfers the uniform exponential moment bound to
   the limit by truncation and monotone convergence.
3. `analyticOnNhd_integral` proves analyticity directly from pointwise
   analyticity, measurability, and compact-set domination by the transferred
   exponential moments.

**Why it matters**: OS0 ensures the Schwinger functions (coefficients of
the Taylor expansion of Z) are well-defined and determine the measure.

### 5.5 OS3: Reflection Positivity (`CylinderMeasureSequenceEventuallyReflectionPositive`)

**Statement**: For positive-time test functions f₁,...,fₙ ∈ C∞(S¹_{Ls}) ⊗̂ 𝓢((0,∞))
and complex coefficients c₁,...,cₙ:

  Re(Σᵢⱼ cᵢ c̄ⱼ ∫ exp(iω(fᵢ - Θfⱼ)) dν) ≥ 0

**Current implementation**: `CylinderOS.lean` assumes the pullback sequence
satisfies the exact eventual RP predicate
`CylinderMeasureSequenceEventuallyReflectionPositive` and proves the weak-limit
transfer inside `routeBPrime_cylinder_OS` by applying characteristic-functional
convergence entrywise to the finite RP matrix. This avoids asserting full
cylinder RP for every finite `Lt`, which would be too strong because arbitrary
positive-time cylinder tests can wrap around the finite time circle.

**Remaining proof route for the eventual input** (compact support → density):

1. **Restrict to compact support**: Take f ∈ C_c^∞((0,R) × S¹_{Ls})
   (smooth, compactly supported in time interval (0,R)).

2. **No wrap-around for large Lt**: When Lt > 2R, the periodization of f
   has support in (0, R) ⊂ (0, Lt/2), so embed(f) fits entirely in the
   positive-time half of the torus. This uses `periodizeCLM_eq_on_large_period`.

3. **Torus RP applies**: Since embed(f) is supported in positive time on
   the torus, torus OS3 gives ∫ F·(ΘF) dμ_{Lt} ≥ 0. By the intertwining
   theorems, this equals ∫ F_cyl·(Θ F_cyl) dν_{Lt} ≥ 0.

4. **Use the implemented weak-limit transfer**: The RP matrix entries are
   characteristic functionals of fixed real test functions, so convergence
   passes through finite sums and real parts. This step is proved in
   `routeBPrime_cylinder_OS`.

5. **Extend by density**: C_c^∞((0,∞) × S¹) is dense in the positive-time
   submodule (in the nuclear Fréchet topology). Since both sides of the
   RP inequality are continuous in f, the inequality extends to all
   positive-time test functions.

**Why it matters**: OS3 is the Euclidean counterpart of unitarity. It
ensures the reconstructed Wightman QFT has a Hilbert space with
positive-definite inner product.

## 6. Dependency Graph

```
                  ┌──────────────────────────────────────────┐
                  │ Step 1: UV limit (DONE, 0 axioms)        │
                  │ Lattice → Continuum torus T_{Lt,Ls}      │
                  │ AsymTorusOS: OS0, OS1, OS2 proved         │
                  └─────────────────┬────────────────────────┘
                                    │
                  ┌─────────────────▼────────────────────────┐
                  │ Embedding (DONE, 0 axioms)                │
                  │ cylinderToTorusEmbed: periodize + swap     │
                  │ Intertwining: T,Θ commute with embed       │
                  │ Pullback: ν_{Lt} = (pullback)_* μ_{Lt}     │
                  └─────────────────┬────────────────────────┘
                                    │
                  ┌─────────────────▼────────────────────────┐
                  │ Input 1: Eventual Green moment             │
                  │ MeasureHasGreenMomentBound eventually;     │
                  │ combine with Lt → ∞ for Lt ≥ 1 tail        │
                  │ [not abstract OS1 regularity]              │
                  └──────┬──────────┬────────────────────────┘
                         │          │
          ┌──────────────▼──┐   ┌──▼─────────────────────────┐
          │ Theorem: Exp     │   │ Theorem: IR limit exists    │
          │ moments          │   │ {ν_{Lt}} → ν weakly         │
          │ [Green input +   │   │ [Mitoma + Prokhorov]         │
          │  images]         │   └──────┬──────────┬──────────┘
          └────────┬─────────┘          │          │
                   │          ┌─────────▼──┐   ┌──▼──────────┐
                   │          │ Theorem:    │   │ Input 2 +   │
                   └──────────▶ OS0 analyt  │   │ theorem:    │
                              │ [MCT +      │   │ OS3 RP      │
                              │  integral]  │   │ [eventual RP]│
                              └─────────────┘   └─────────────┘
```

## 7. Upstream Dependencies (gaussian-field)

### Cylinder infrastructure (0 axioms, fully proved)
- `Cylinder/Basic.lean`: CylinderTestFunction type definition
- `Cylinder/Symmetry.lean`: Time translation, spatial translation, time reflection
  as CLMs on the cylinder. Configuration-level actions. All continuity proved.
- `Cylinder/PositiveTime.lean`: Positive-time submodule (topological closure of
  span of pure tensors with positive-time Schwartz factor). Disjointness from
  negative-time submodule proved. Spatial translation preserves positive time.
- `Cylinder/FreeHeatSemigroup.lean`: Heat semigroup on the cylinder.

### Cylinder analysis (pinned dependency: 4 axioms)
- `Cylinder/GreenFunction.lean` (1): cylinder Green-function analytic input.
- `Cylinder/MethodOfImages.lean` (1): uniform torus-cylinder Green function
  bound `torusGreen_uniform_bound` (method of images with exponential
  suppression).
- `Cylinder/ReflectionPositivity.lean` (1): cylinder reflection-positivity
  support.
- `SchwartzFourier/ResolventUniformBound.lean` (1): uniform Fourier/resolvent
  bound.

## 8. Comparison with Route C

Route C (`future/CylinderContinuumLimit/`, 21 axioms) constructs the cylinder
measure directly by:
1. Defining the OU process on the cylinder via Hermite series
2. UV removal (Λ → ∞ cutoff removal)
3. IR removal (T → ∞ time cutoff removal)

Route B' advantages:
- Reuses the entire torus UV limit (0 axioms, fully proved)
- Adds an IR-limit layer with 0 local axioms, conditional on explicit
  Green-moment and eventual pullback-RP inputs
- The embedding construction is clean (NTP functor + periodization)
- OS2 is exact (not a limiting statement)

Route C advantages:
- More direct construction (no torus intermediate)
- OU process gives explicit field representation
- Potentially better for constructing the Hamiltonian

## 9. What Would Close the Construction

To close the Route B′ IR-limit construction, the remaining mathematical
ingredients are the explicit family-level inputs now exposed by the Lean API:

1. **Uniform Green-moment family bound**: prove
   `AsymTorusSequenceHasUniformGreenMomentBound` for the concrete
   asymmetric-torus UV-limit family. This is the real Nelson/Fröhlich +
   Green-control obligation.

2. **Eventual pullback reflection positivity**: prove
   `CylinderMeasureSequenceEventuallyReflectionPositive` for the concrete
   pullback sequence via no-wrap compact support, torus RP, and density.

3. **Prokhorov on cylinder configurations**: implemented through
   `prokhorov_configuration`, producing bounded-continuous convergence.

4. **OS0 analyticity**: implemented via `limit_exponential_moment` and
   `analyticOnNhd_integral`; no Route B′ Vitali/Montel axiom remains.

5. **Limit transfer for OS3**: implemented in `CylinderOS.lean` from
   characteristic-functional convergence and eventual matrixwise RP.

The pinned Lake `GaussianField` dependency currently contributes 4 axioms and
0 sorries; see `status.md` and `docs/axiom_audit.md` for the live inventory.
