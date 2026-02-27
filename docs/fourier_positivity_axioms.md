# Gaussian Strict Positive Definiteness: Axiom Decomposition

## Old axiom (1 axiom, removed)

**`convolution_gaussian_strictly_positive_definite`**

For all f ∈ L²(ℝⁿ) with f ≠ 0:

⟨f, G⋆f⟩ > 0

where G(x) = exp(-½‖x‖²) is the Gaussian kernel.

*Proof route*: Plancherel gives ⟨f, G⋆f⟩ = ∫ |f̂(k)|² Ĝ(k) dk.
Since Ĝ(k) > 0 and f ≠ 0 ⟹ f̂ ≠ 0 a.e., the integral is positive.

## New axioms (2 axioms, replacing the above)

### Axiom A: `gaussian_operator_factorization`

There exists C > 0 such that for all f ∈ L²(ℝⁿ):

⟨f, G⋆f⟩ = C · ‖H⋆f‖²

where H(x) = exp(-‖x‖²) is the square-root Gaussian.

*Proof route*: The Gaussian convolution identity

∫ exp(-‖s‖²) exp(-‖z-s‖²) ds = (π/2)^{n/2} exp(-½‖z‖²)

(completing the square + ∫ exp(-2u²) du = √(π/2)) gives G = C⁻¹ · (H⋆H).
Then ⟨f, G⋆f⟩ = C · ⟨f, H⋆(H⋆f)⟩ = C · ⟨H⋆f, H⋆f⟩ (self-adjointness of H, since H is even).

### Axiom B: `sqrtGaussian_convolution_injective`

For all f ∈ L²(ℝⁿ):

H⋆f = 0 ⟹ f = 0

*Proof route*: The Fourier transform Ĥ(ξ) = π^{n/2} exp(-π²‖ξ‖²) > 0 has no zeros.
By Plancherel + convolution theorem: H⋆f = 0 ⟹ Ĥ·f̂ = 0 ⟹ f̂ = 0 ⟹ f = 0.

## How the theorem follows

From Axiom A: ⟨f, G⋆f⟩ = C · ‖H⋆f‖².
From Axiom B: f ≠ 0 ⟹ H⋆f ≠ 0 ⟹ ‖H⋆f‖ > 0.
Since C > 0: ⟨f, G⋆f⟩ = C · ‖H⋆f‖² > 0. ∎
