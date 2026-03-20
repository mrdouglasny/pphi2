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

**Status**: 5 axioms remain. OS2 (time reflection invariance) is proved
for the limit. OS0 (analyticity) and OS3 (reflection positivity) are
axiomatized with documented proof routes.

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

The IR limit axiom `cylinderIRLimit_exists` provides characteristic functional
convergence: Z_{Lt_n}(f) → Z(f) for all f. Since Z_{Lt_n}(f) = Z_{Lt_n}(Θf)
at every n (exact reflection invariance), taking the limit:

  Z(f) = lim Z_{Lt_n}(f) = lim Z_{Lt_n}(Θf) = Z(Θf)

This uses `tendsto_nhds_unique`: if a_n → L₁ and a_n = b_n → L₂, then L₁ = L₂.

## 5. Remaining Axioms and Proof Routes

### 5.1 Uniform second moment bound (`cylinderIR_uniform_second_moment`)

**Statement**: There exist C > 0 and continuous seminorm q on CylinderTestFunction Ls
such that for all Lt ≥ 1 and all OS-satisfying torus measures μ:

  ∫ (ω f)² dν_{Lt} ≤ C · q(f)²

**Mathematical content**: The second moment of the cylinder field is bounded
uniformly in the time period. This is the core tightness input.

**Proof chain**:

1. **Pullback identity**: ∫ (ωf)² dν_{Lt} = ∫ (ω(embed f))² dμ_{Lt}

2. **OS1 regularity**: The torus measure satisfies OS1, giving
   ∫ (ωg)² dμ ≤ C₁ · q₁(g)² for a continuous seminorm q₁ on AsymTorusTF.
   This follows from the Nelson exponential bound + Cauchy-Schwarz.

3. **Method of images**: The torus Green's function decomposes as
   G_{Lt,Ls}(embed f, embed f) = G_{Ls}(f, f) + Σ_{k≠0} wrap-around terms.
   Each wrap-around term decays as e^{-m|k|Lt} (exponential suppression by
   the mass gap). For Lt ≥ 1, the geometric series sums to at most
   2e^{-m}/(1-e^{-m}). Combined: q₁(embed f) ≤ C₂ · q₂(f) uniformly.

**Why it matters**: This bound feeds into the Mitoma-Chebyshev tightness
criterion, which is the gateway to Prokhorov extraction.

### 5.2 Uniform exponential moment bound (`cylinderIR_uniform_exponential_moment`)

**Statement**: There exist K, C > 0 and continuous seminorm q such that:

  ∫ exp(|ω f|) dν_{Lt} ≤ K · exp(C · q(f)²)

uniformly in Lt ≥ 1.

**Mathematical content**: The exponential moments (moment generating function)
are uniformly bounded. This is stronger than second moments and is needed
for OS0 analyticity.

**Proof chain**: The torus measure satisfies the Nelson/Fröhlich exponential
bound (from the hypercontractive estimate). Apply this to g = embed(f) and
use the method of images bound on ‖embed f‖.

**Why it matters**: Without exponential moment bounds, we can only prove
pointwise convergence of the characteristic function on the real axis —
insufficient for analyticity. The exponential bound gives Vitali/Montel.

### 5.3 IR limit existence (`cylinderIRLimit_exists`)

**Statement**: Given Lt_n → ∞ and OS-satisfying measures μ_n on T_{Lt_n, Ls},
there exist a subsequence φ and a probability measure ν on S¹_{Ls} × ℝ
such that the characteristic functionals converge:

  ∫ exp(iωf) dν_{φ(n)} → ∫ exp(iωf) dν  for all f

**Mathematical content**: The family of pulled-back cylinder measures is
tight (compact in the weak topology), so Prokhorov's theorem gives a
convergent subsequence.

**Proof chain**:
1. Uniform second moments (§5.1) → for each f, the 1D marginals {(ev_f)_* ν_{Lt}}
   have uniformly bounded variance
2. Mitoma-Chebyshev criterion: 1D tightness ⟹ tightness on S'(S¹ × ℝ)
   (this is `configuration_tight_of_uniform_second_moments` in gaussian-field)
3. Prokhorov's theorem: tightness on a Polish space ⟹ sequential compactness
4. Lévy continuity: weak convergence ⟺ characteristic functional convergence
   (on nuclear spaces)

**Why characteristic functionals**: Convergence ∫ exp(iωf) dν_n → ∫ exp(iωf) dν
is needed (not just first moments ∫ ωf dν_n → ∫ ωf dν) because OS2
transfers through characteristic functionals, and OS0 requires analytic
continuation of the characteristic functional.

### 5.4 OS0: Analyticity (`cylinderIR_os0`)

**Statement**: The multivariate generating functional

  Z(z₁,...,z_n) = ∫ exp(Σᵢ zᵢ · ω(Jᵢ)) dν

is entire analytic on ℂⁿ for any test functions J₁,...,Jₙ.

**Proof route**:
1. At each finite Lt, Z_{Lt} is entire (from torus OS0)
2. The uniform exponential moment bound (§5.2) gives
   |Z_{Lt}(z)| ≤ K · exp(C · Σ |Re(zᵢ)|² · q(Jᵢ)²)
   which is locally uniform on compact subsets of ℂⁿ
3. By Vitali's convergence theorem: a sequence of analytic functions
   that converges pointwise on a set with a limit point (here: the
   imaginary axis, from characteristic functional convergence) and
   is locally uniformly bounded converges to an analytic function

**Why it matters**: OS0 ensures the Schwinger functions (coefficients of
the Taylor expansion of Z) are well-defined and determine the measure.

### 5.5 OS3: Reflection Positivity (`cylinderIR_os3`)

**Statement**: For positive-time test functions f₁,...,fₙ ∈ C∞(S¹_{Ls}) ⊗̂ 𝓢((0,∞))
and complex coefficients c₁,...,cₙ:

  Re(Σᵢⱼ cᵢ c̄ⱼ ∫ exp(iω(fᵢ - Θfⱼ)) dν) ≥ 0

**Proof route** (compact support → density):

1. **Restrict to compact support**: Take f ∈ C_c^∞((0,R) × S¹_{Ls})
   (smooth, compactly supported in time interval (0,R)).

2. **No wrap-around for large Lt**: When Lt > 2R, the periodization of f
   has support in (0, R) ⊂ (0, Lt/2), so embed(f) fits entirely in the
   positive-time half of the torus. This uses `periodizeCLM_eq_on_large_period`.

3. **Torus RP applies**: Since embed(f) is supported in positive time on
   the torus, torus OS3 gives ∫ F·(ΘF) dμ_{Lt} ≥ 0. By the intertwining
   theorems, this equals ∫ F_cyl·(Θ F_cyl) dν_{Lt} ≥ 0.

4. **Pass through weak limit**: The function ω ↦ F(ω)·F(Θω) is continuous
   and bounded (for the exponential generating functional with bounded
   test functions). By weak convergence: ∫ F·(ΘF) dν ≥ 0.
   (This uses `rp_closed_under_weak_limit`, already proved.)

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
                  │ Axiom 1: Uniform second moment             │
                  │ ∫ (ωf)² dν_{Lt} ≤ C·q(f)²                │
                  │ [method of images + OS1 regularity]        │
                  └──────┬──────────┬────────────────────────┘
                         │          │
          ┌──────────────▼──┐   ┌──▼─────────────────────────┐
          │ Axiom 2: Exp     │   │ Axiom 3: IR limit exists    │
          │ moments          │   │ {ν_{Lt}} → ν weakly         │
          │ [Nelson +        │   │ [Mitoma + Prokhorov]         │
          │  images]         │   └──────┬──────────┬──────────┘
          └────────┬─────────┘          │          │
                   │          ┌─────────▼──┐   ┌──▼──────────┐
                   │          │ Axiom 4:    │   │ Axiom 5:    │
                   └──────────▶ OS0 analyt  │   │ OS3 RP      │
                              │ [Vitali/    │   │ [wrap-around│
                              │  Montel]    │   │  + density] │
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

### Cylinder analysis (10 axioms)
- `Cylinder/FourierMultiplier.lean` (3): Fourier multiplier CLM properties —
  preserves real-valuedness (even symbol), commutes with translation, commutes
  with reflection.
- `Cylinder/GreenFunction.lean` (3): Mass operator T: CylinderTF → ℓ² (construction),
  Green's function G(f,f) > 0 for f ≠ 0 (injectivity), heat kernel equivariance
  principle (Bochner integral commutation).
- `Cylinder/ReflectionPositivity.lean` (3): Laplace embedding Λ (construction),
  Laplace factorization G(f,Θf) = ‖Λf‖² (resolvent kernel factorization),
  strict RP G(f,Θf) > 0 for f ≠ 0 (Laplace injectivity).
- `Cylinder/MethodOfImages.lean` (1): Uniform torus-cylinder Green function bound
  `torusGreen_uniform_bound` (method of images with exponential suppression).

### Periodization and NTP (4 axioms)
- `SchwartzNuclear/Periodization.lean` (2): Periodization CLM existence +
  pointwise formula. The 3 properties (translation, reflection, large period)
  are proved from the pointwise formula.
- `Nuclear/GeneralMapCLM.lean` (2): NTP functor for general CLMs (not just
  endomorphisms). Used for the embedding construction.

## 8. Comparison with Route C

Route C (`future/CylinderContinuumLimit/`, 21 axioms) constructs the cylinder
measure directly by:
1. Defining the OU process on the cylinder via Hermite series
2. UV removal (Λ → ∞ cutoff removal)
3. IR removal (T → ∞ time cutoff removal)

Route B' advantages:
- Reuses the entire torus UV limit (0 axioms, fully proved)
- Only adds the IR limit step (5 axioms)
- The embedding construction is clean (NTP functor + periodization)
- OS2 is exact (not a limiting statement)

Route C advantages:
- More direct construction (no torus intermediate)
- OU process gives explicit field representation
- Potentially better for constructing the Hamiltonian

## 9. What Would Close the Construction

To eliminate all 5 IR limit axioms, the main mathematical ingredients needed are:

1. **Spectral decomposition bridge** (~200 lines): Connect the method of images
   bound `torusGreen_uniform_bound` (axiom in gaussian-field) to the second
   moment bound. This requires working with the covariance operator's spectral
   decomposition on the tensor product space.

2. **Nelson exponential transfer** (~100 lines): Pull the torus Nelson/Fröhlich
   exponential bound through the embedding. Straightforward once §1 is done.

3. **Prokhorov on cylinder configurations** (~150 lines): Either prove Polish
   space for CylinderTestFunction configurations (deep topology), or use the
   Lévy continuity theorem on nuclear spaces (equivalent to weak convergence).
   Template exists in `AsymTorusInteractingLimit.lean`.

4. **Vitali/Montel for OS0** (~200 lines): Apply the Vitali convergence theorem
   to the sequence of entire generating functionals. Requires complex analysis
   infrastructure (locally uniform bounds → analytic limit).

5. **Compact support density for OS3** (~200 lines): The most novel argument.
   Show C_c^∞((0,∞) × S¹) is dense in the positive-time submodule, use
   `periodizeCLM_eq_on_large_period` for no-wrap-around, and
   `rp_closed_under_weak_limit` (already proved) for the limit transfer.

Total estimated effort: ~850 lines of Lean proofs + ~14 gaussian-field axioms
that provide the cylinder analysis infrastructure (Green's function, Fourier
multipliers, reflection positivity, method of images).
