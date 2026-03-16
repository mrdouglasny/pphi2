# Torus Interacting P(φ)₂: Construction and OS Axioms

## Overview

We construct the interacting P(φ)₂ Euclidean quantum field theory on the
two-dimensional torus T²_L = (ℝ/Lℤ)² and prove the Osterwalder-Schrader
axioms OS0–OS2 for the continuum limit measure.

The construction follows the Glimm-Jaffe/Nelson lattice approach:
1. Define the interacting measure at each lattice cutoff N
2. Prove tightness (uniform moment bounds)
3. Extract a weakly convergent subsequence (Prokhorov)
4. Verify the limit satisfies the OS axioms

All results are formalized in Lean 4 in `Pphi2/TorusContinuumLimit/TorusInteractingOS.lean`.

## The Interacting Measure

### Lattice Cutoff

At cutoff N, the lattice spacing is a = L/N. The interacting measure on
configurations of the lattice (ℤ/Nℤ)² is:

  μ_{P,N} = (1/Z_N) exp(-V_N) dμ_{GFF,N}

where:
- μ_{GFF,N} is the lattice Gaussian free field (centered Gaussian with
  covariance (-Δ_lattice + m²)⁻¹)
- V_N = a² Σ_x :P(φ(x)):_c is the Wick-ordered interaction
- Z_N = ∫ exp(-V_N) dμ_{GFF,N} is the partition function
- :P:_c denotes Wick ordering with respect to the lattice Wick constant c

### Torus Embedding

The lattice measure is embedded into the torus configuration space via
`torusEmbedLift`: each lattice field φ : (ℤ/Nℤ)² → ℝ maps to a
distribution ω on smooth torus test functions by:

  ω(f) = Σ_x φ(x) · evalTorusAtSite(x)(f)

where `evalTorusAtSite` samples the test function at lattice points.

### Continuum Limit

The sequence of torus-embedded interacting measures {μ_{P,N}} is tight
(by the Mitoma-Chebyshev criterion + Nelson's exponential estimate).
By Prokhorov's theorem, a subsequence converges weakly to a probability
measure μ_P on the torus configuration space.

## Nelson's Exponential Estimate

The key analytical input: the L² norm of the Boltzmann weight is bounded
uniformly in N:

  ∫ exp(-2V_N) dμ_{GFF} ≤ K    for all N

This is proved using the physical volume argument: a²N² = L² (fixed),
so V_N ≥ -L²A gives exp(-2V_N) ≤ exp(2L²A) uniformly.

Nelson's estimate enables:
- Uniform second moment bounds (via Cauchy-Schwarz density transfer)
- Tightness of the interacting measures
- Exponential moment bounds for the limit measure

## OS Axioms

### OS0: Analyticity

**Statement:** The generating functional
  Z_ℂ[z] = ∫ exp(i Σ zᵢ ω(Jᵢ)) dμ_P
is entire analytic in z ∈ ℂⁿ for any test functions J₁,...,Jₙ.

**Proof:** Apply `analyticOnNhd_integral` (Morera's theorem for
parametric integrals):
1. Pointwise analyticity: z ↦ exp(i Σ zᵢ ω(Jᵢ)) is entire for each ω
   (composition of exp with a linear function, using Re(z)+I·Im(z)=z)
2. Measurability: from `configuration_eval_measurable`
3. Domination on compact sets: ‖exp(i Σ zᵢ ωᵢ)‖ ≤ exp(C_K Σ|ωᵢ|)
   ≤ Σ exp(n·C_K·|ωᵢ|), integrable by the exponential moment bound

### OS1: Regularity

**Statement:** ‖Z_ℂ[f_re, f_im]‖ ≤ exp(c·(q(f_re) + q(f_im)))
for a continuous seminorm q and constant c > 0.

**Proof:** By the triangle inequality + |exp(ix)-exp(iy)| trick:
  ‖Z_ℂ‖ ≤ ∫ exp(|ω(f_im)|) dμ_P ≤ K · exp(G(f_im, f_im))

The exponential moment bound gives K · exp(G(f,f)), and we absorb K
into the seminorm: q(f) = G(f,f) + |log K|, c = 1.

The exponential moment bound itself is proved via:
- Cutoff: E_P[exp(|ωf|)] ≤ √(2K) · exp(G_N(f,f)) (density transfer + Nelson + Gaussian MGF)
- Transfer to limit: MCT truncation argument (min(exp, M) is bounded continuous → weak convergence applies, then M → ∞)

### OS2: Translation Invariance

**Statement:** Z[f] = Z[T_v f] for all v ∈ ℝ² and test functions f.

**Proof:** The lattice measure is only translation-invariant for lattice
translations (multiples of L/N). For general v, we use an approximation:

1. For each n, approximate v by the nearest lattice vector w_n
2. Z_N[T_{w_n} f] = Z_N[f] (lattice translation invariance)
3. ‖Z_N[T_v f] - Z_N[T_{w_n} f]‖ → 0 as the lattice refines

Step 3 uses the chain:
  ‖Z[g] - Z[h]‖ ≤ √(E_P[(ω(g-h))²]) ≤ √(C · G_N(g-h, g-h)) ≤ √C · p(g-h)

where the interacting-to-Gaussian bridge (E_P ≤ C · E_GFF, from
Cauchy-Schwarz + Nelson) converts the interacting problem to a Gaussian one,
and translation continuity gives p(T_v f - T_{w_n} f) → 0.

**Why the second moment suffices:** |exp(ix) - exp(iy)| ≤ |x - y| reduces
the generating functional's continuity to the first moment, which by
Cauchy-Schwarz is ≤ √(second moment). So we only need 2-point control,
not higher moments.

**Higher-point functions** inherit translation invariance automatically:
once Z is translation-invariant, it determines the measure μ_P, and all
Schwinger functions S_n(f₁,...,f_n) = ∫ ω(f₁)···ω(f_n) dμ_P are invariant.

### OS2: D4 Point Group Invariance

**Statement:** Z[f] = Z[σf] for swap σ(t,x) = (x,t) and
time reflection Θ(t,x) = (-t,x).

**Proof:** These are discrete lattice symmetries — the cutoff measure
IS exactly invariant (not just approximately):

1. `evalTorusAtSite` equivariance: evaluation at site x of σf equals
   evaluation at σ(x) of f (proved via `evalCLM_comp_swapCLM` /
   `evalCLM_comp_mapCLM` for the nuclear tensor product)
2. Lattice measure invariance: the interacting measure is invariant
   under any site bijection σ that preserves the Laplacian eigenvalues
   (proved via BW relabeling + density invariance + volume preservation)
3. Transfer to limit via weak convergence + `tendsto_nhds_unique`

The Laplacian commutativity (massOperator commutes with swap/reflection)
is proved by unrolling the stencil sum with `Fin.sum_univ_two` and
using `add_comm` on the direction exchange.

## Key Infrastructure

### Gaussian-field library (upstream)
- `evalCLM_comp_swapCLM`: evalCLM commutes with NTP swap
- `evalCLM_comp_mapCLM`: evalCLM commutes with NTP mapCLM
- `basisVec_eq_pure`: NTP basis vectors = pure tensors (biorthogonality)
- `evalTorusAtSite_swap/latticeTranslation`: torus evaluation equivariance
- `pairing_is_gaussian`: ω(f) under GFF is Gaussian with known variance
- `measure_isGaussian`: our Gaussian measure satisfies Mathlib's IsGaussian

### Mathlib
- `mgf_id_gaussianReal`: Gaussian MGF E[exp(tX)] = exp(σ²t²/2)
- `analyticOnNhd_integral`: Morera for parametric integrals (axiomatized)
- Portmanteau theorem, MCT, Cauchy-Schwarz for integrals

### Key proof techniques
- **Density transfer:** E_P[F] ≤ √K · √(E_GFF[F²]) converts interacting to Gaussian
- **MCT truncation:** min(exp, M) is bounded continuous → weak convergence
  applies, then M → ∞ gives the full bound
- **Lattice approximation:** nearest lattice vector converges to any v as
  spacing → 0, with error controlled by the Green's function seminorm

## Axiom Status

The file `TorusInteractingOS.lean` has:
- **1 axiom:** `torusTranslation_continuous_in_v` (v ↦ T_v f continuous in DM topology)
- **0 sorry**

The single remaining axiom is a standard property of smooth functions on the
torus: translation varies continuously in the shift parameter. Its proof
requires dominated convergence for Fourier series (phase shifts converge
pointwise, dominated by the rapidly decaying coefficients).

## References

- Glimm-Jaffe, *Quantum Physics*, Chapters 6, 8, 19
- Simon, *The P(φ)₂ Euclidean QFT*, Chapters I, V
- Nelson (1966), "A quartic interaction in two dimensions"
- Osterwalder-Schrader (1973, 1975)
