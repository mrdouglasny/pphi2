/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Torus Propagator Convergence

The main analytical content of the torus Gaussian continuum limit: the lattice
Green's function on T²_L converges to the continuum Green's function as N → ∞.

## Main results

- `torus_propagator_convergence` — (axiom) lattice eigenvalues → continuum eigenvalues
- `torusEmbeddedTwoPoint_uniform_bound` — (axiom) `E[Φ_N(f)²] ≤ C/m²·‖f‖²` uniformly in N
- `torusContinuumGreen_pos` — `G_L(f,f) > 0` for f ≠ 0

## Mathematical background

On the torus T²_L with lattice spacing a = L/N, the lattice eigenvalues are:

  `λ_{n}^{lat} = (4N²/L²) sin²(πn₁/N) + (4N²/L²) sin²(πn₂/N) + m²`

for n ∈ (ℤ/Nℤ)². As N → ∞ (pure UV limit, L fixed):

  `λ_{n}^{lat} → (2πn₁/L)² + (2πn₂/L)² + m² = λ_{n}^{cont}`

This is a **pure UV limit** — no IR tail issues since the volume L is fixed.
The convergence is mode-by-mode and the smooth test function Fourier coefficients
f̂(n) decay rapidly, providing dominated convergence.

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I
-/

import Pphi2.TorusContinuumLimit.TorusEmbedding
import Lattice.Covariance

noncomputable section

open GaussianField MeasureTheory Filter

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Lattice test function from a torus test function

The torus test function f ∈ C∞(T²_L) induces a lattice field `latticeTestFn f`
via point evaluation at lattice sites:
  `(latticeTestFn f)(x) = evalTorusAtSite L N x f`

This is the function whose second moment under the lattice Gaussian gives
the embedded two-point function. -/

/-- The lattice field induced by evaluating a torus test function at lattice sites. -/
def latticeTestFn (N : ℕ) [NeZero N] (f : TorusTestFunction L) : FinLatticeField 2 N :=
  fun x => evalTorusAtSite L N x f

/-- Key identity: the lattice test function equals the sum of its values times delta functions. -/
private theorem latticeTestFn_expand (N : ℕ) [NeZero N] (f : TorusTestFunction L) :
    latticeTestFn L N f =
    ∑ x : FinLatticeSites 2 N, (latticeTestFn L N f) x • Pi.single x (1 : ℝ) := by
  funext y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The embedded two-point function (with f = g) factors through the lattice. -/
private theorem torusEmbedLift_eval_eq (N : ℕ) [NeZero N]
    (f : TorusTestFunction L) (ω : Configuration (FinLatticeField 2 N)) :
    (torusEmbedLift L N ω) f = ω (latticeTestFn L N f) := by
  -- LHS = Σ_x ω(δ_x) * eval_x(f) by definition of torusEmbedLift
  simp only [torusEmbedLift, torusEmbedCLM_apply]
  -- RHS = ω(Σ_x eval_x(f) • δ_x) = Σ_x eval_x(f) * ω(δ_x) by linearity
  conv_rhs => rw [latticeTestFn_expand L N f, map_sum]
  simp_rw [map_smul, smul_eq_mul]
  congr 1; ext x
  unfold latticeTestFn
  ring

theorem torusEmbeddedTwoPoint_eq_lattice_second_moment
    (N : ℕ) [NeZero N] (mass : ℝ) (hmass : 0 < mass)
    (f : TorusTestFunction L) :
    torusEmbeddedTwoPoint L N mass hmass f f =
    ∫ ω : Configuration (FinLatticeField 2 N),
      (ω (latticeTestFn L N f)) ^ 2
      ∂(latticeGaussianMeasure 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass) := by
  unfold torusEmbeddedTwoPoint torusContinuumMeasure
  -- Change of variables: integral under pushforward = integral of composition
  rw [integral_map (torusEmbedLift_measurable L N).aemeasurable]
  · -- Show the integrands match
    congr 1
    ext ω
    simp only [sq]
    rw [torusEmbedLift_eval_eq L N f ω]
  · -- Measurability of the function ω ↦ ω(f) * ω(f)
    exact (configuration_eval_measurable f).mul (configuration_eval_measurable f)
      |>.aestronglyMeasurable

/-- The lattice second moment equals the covariance inner product.

  `∫ φ(g)² dμ_GFF = ⟨T(g), T(g)⟩_ℓ²`

This is `second_moment_eq_covariance` specialized to the lattice. -/
theorem lattice_second_moment_eq_inner
    (N : ℕ) [NeZero N] (mass : ℝ) (hmass : 0 < mass)
    (g : FinLatticeField 2 N) :
    ∫ ω : Configuration (FinLatticeField 2 N),
      (ω g) ^ 2
      ∂(latticeGaussianMeasure 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass) =
    @inner ℝ ell2' _
      (latticeCovariance 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass g)
      (latticeCovariance 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass g) := by
  exact second_moment_eq_covariance _ g

/-- **Eigenvalue lower bound for the mass operator.**

All eigenvalues of `-Δ + m²` satisfy `λ_k ≥ m²`, since `-Δ ≥ 0`.
This gives `(massEigenvalues k)⁻¹ ≤ m⁻²`. -/
theorem massEigenvalues_ge_mass_sq (N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (_hmass : 0 < mass)
    (k : FinLatticeSites 2 N) :
    mass ^ 2 ≤ massEigenvalues 2 N a mass k := by
  -- The mass operator is Q = -Δ + m², and -Δ is nonneg-definite.
  -- For eigenvector e_k: ⟨e_k, Q e_k⟩ = λ_k ⟨e_k, e_k⟩ = λ_k.
  -- Also ⟨e_k, Q e_k⟩ = ⟨e_k, (-Δ)e_k⟩ + m²⟨e_k, e_k⟩ ≥ m².
  set herm := massMatrixHerm 2 N a mass
  set v := herm.eigenvectorBasis k
  -- The eigenvector is a unit vector: ‖v‖ = 1
  have hv_unit : ‖v‖ = 1 := (herm.eigenvectorBasis.orthonormal).1 k
  have hv_norm : @inner ℝ (EuclideanSpace ℝ _) _ v v = 1 := by
    rw [real_inner_self_eq_norm_sq, hv_unit, one_pow]
  -- Qv = λ_k v (eigenvector equation)
  -- So ⟨v, Qv⟩ = λ_k ⟨v, v⟩ = λ_k
  have hQv : ∀ i, (massOperator 2 N a mass (v : EuclideanSpace ℝ _)) i =
      massEigenvalues 2 N a mass k * (v : EuclideanSpace ℝ _) i := by
    intro i
    rw [massOperator_eq_matrix_mulVec 2 N a mass _ i]
    have := congrFun (Matrix.IsHermitian.mulVec_eigenvectorBasis
      (hA := massOperatorMatrix_isHermitian 2 N a mass) k) i
    simpa [massEigenvalues, massEigenvectorBasis] using this
  -- Σ_x v(x)² = ⟨v, v⟩ = 1
  have hv_sum_sq : ∑ x : FinLatticeSites 2 N,
      (v : EuclideanSpace ℝ _) x * (v : EuclideanSpace ℝ _) x = 1 := by
    -- Use ‖v‖² = Σ_x v(x)² (EuclideanSpace norm)
    have h1 : ‖v‖ ^ 2 = ∑ x, (v : EuclideanSpace ℝ _) x * (v : EuclideanSpace ℝ _) x := by
      rw [EuclideanSpace.norm_eq]
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
      congr 1; ext x
      rw [sq, Real.norm_eq_abs, abs_mul_abs_self]
    rw [hv_unit, one_pow] at h1
    exact h1.symm
  have hvQv : (∑ x : FinLatticeSites 2 N,
      (v : EuclideanSpace ℝ _) x * (massOperator 2 N a mass v) x) =
      massEigenvalues 2 N a mass k := by
    conv_lhs => arg 2; ext x; rw [hQv x]
    -- Now goal is: Σ_x v(x) * (λ_k * v(x)) = λ_k
    have : ∀ x : FinLatticeSites 2 N,
        (v : EuclideanSpace ℝ _) x * (massEigenvalues 2 N a mass k * (v : EuclideanSpace ℝ _) x) =
        massEigenvalues 2 N a mass k * ((v : EuclideanSpace ℝ _) x * (v : EuclideanSpace ℝ _) x) := by
      intro x; ring
    simp_rw [this, ← Finset.mul_sum, hv_sum_sq, mul_one]
  -- Also: ⟨v, Qv⟩ = ⟨v, -Δv⟩ + m²⟨v, v⟩
  -- Since -Δ is nonneg-definite, ⟨v, -Δv⟩ ≥ 0
  -- So ⟨v, Qv⟩ ≥ m²
  have hLap_nonneg : 0 ≤ ∑ x : FinLatticeSites 2 N,
      (v : EuclideanSpace ℝ _) x * ((-finiteLaplacian 2 N a) v) x := by
    have h := finiteLaplacian_neg_semidefinite 2 N a ha (v : EuclideanSpace ℝ _)
    simp only [ContinuousLinearMap.neg_apply, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib] at *
    linarith
  have hQ_decomp : (∑ x : FinLatticeSites 2 N,
      (v : EuclideanSpace ℝ _) x * (massOperator 2 N a mass v) x) =
      (∑ x : FinLatticeSites 2 N,
        (v : EuclideanSpace ℝ _) x * ((-finiteLaplacian 2 N a) v) x) +
      mass ^ 2 * (∑ x : FinLatticeSites 2 N,
        (v : EuclideanSpace ℝ _) x * (v : EuclideanSpace ℝ _) x) := by
    have : ∀ x : FinLatticeSites 2 N,
        (v : EuclideanSpace ℝ _) x * (massOperator 2 N a mass v) x =
        (v : EuclideanSpace ℝ _) x * ((-finiteLaplacian 2 N a) v) x +
        mass ^ 2 * ((v : EuclideanSpace ℝ _) x * (v : EuclideanSpace ℝ _) x) := by
      intro x
      simp only [massOperator, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
        Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  -- From hvQv and hQ_decomp:
  -- λ_k = ⟨v, -Δv⟩ + m² * ⟨v, v⟩ = ⟨v, -Δv⟩ + m² (since ⟨v,v⟩ = 1)
  rw [hv_sum_sq, mul_one] at hQ_decomp
  linarith [hvQv, hQ_decomp, hLap_nonneg]

/-- **Covariance spectral bound.**

The covariance inner product is bounded by `(1/m²) * ‖g‖²` where ‖g‖² is the
EuclideanSpace norm squared.

  `⟨Tg, Tg⟩ = Σ_k λ_k⁻¹ c_k(g)² ≤ (1/m²) Σ_k c_k(g)² = (1/m²) ‖g‖²` -/
theorem covariance_inner_le_mass_inv_sq_norm_sq
    (N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (g : FinLatticeField 2 N) :
    @inner ℝ ell2' _
      (latticeCovariance 2 N a mass ha hmass g)
      (latticeCovariance 2 N a mass ha hmass g)
    ≤ mass⁻¹ ^ 2 * ∑ x : FinLatticeSites 2 N, g x ^ 2 := by
  -- Rewrite LHS using spectral decomposition
  rw [show latticeCovariance 2 N a mass ha hmass = spectralLatticeCovariance 2 N a mass ha hmass from rfl]
  rw [spectralLatticeCovariance_norm_sq]
  -- LHS = Σ_k (massEigenvalues k)⁻¹ * c_k(g)²
  -- Bound: (massEigenvalues k)⁻¹ ≤ mass⁻²
  have hev_bound : ∀ k : FinLatticeSites 2 N,
      (massEigenvalues 2 N a mass k)⁻¹ ≤ mass⁻¹ ^ 2 := by
    intro k
    have hmsq_pos := sq_pos_of_pos hmass
    have hge := massEigenvalues_ge_mass_sq N a mass ha hmass k
    rw [inv_pow, inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le hmsq_pos hge
  -- Σ_k λ_k⁻¹ c_k² ≤ Σ_k (1/m²) c_k² = (1/m²) Σ_k c_k²
  calc
    ∑ k : FinLatticeSites 2 N,
        (massEigenvalues 2 N a mass k)⁻¹ *
        (∑ x, (massEigenvectorBasis 2 N a mass k : EuclideanSpace ℝ _) x * g x) ^ 2
      ≤ ∑ k : FinLatticeSites 2 N,
          mass⁻¹ ^ 2 *
          (∑ x, (massEigenvectorBasis 2 N a mass k : EuclideanSpace ℝ _) x * g x) ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_right (hev_bound k) (sq_nonneg _)
    _ = mass⁻¹ ^ 2 *
          ∑ k : FinLatticeSites 2 N,
            (∑ x, (massEigenvectorBasis 2 N a mass k : EuclideanSpace ℝ _) x * g x) ^ 2 := by
        rw [Finset.mul_sum]
    _ = mass⁻¹ ^ 2 * ∑ x : FinLatticeSites 2 N, g x ^ 2 := by
        congr 1
        -- Parseval: Σ_k c_k² = Σ_x g(x)²
        have hparseval := massEigenbasis_sum_mul_sum_eq_site_inner (d := 2) (N := N) a mass g g
        -- hparseval : Σ_k (Σ_x e_k(x) g(x)) * (Σ_x e_k(x) g(x)) = Σ_x g(x) * g(x)
        simp_rw [← sq] at hparseval ⊢
        linarith

/-- **Riemann sum bound.**

The sum `Σ_x (evalTorusAtSite L N x f)²` is bounded uniformly in N.
This is because it's a Riemann sum of a continuous function on the compact torus.

More precisely: `evalTorusAtSite L N x f` involves `circleRestriction` with
`√(L/N)` normalization, so the squared sum is `O(1)` as N → ∞. -/
theorem latticeTestFn_norm_sq_bounded (f : TorusTestFunction L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N],
    ∑ x : FinLatticeSites 2 N, (latticeTestFn L N f x) ^ 2 ≤ C := by
  sorry

/-! ## Propagator convergence on the torus -/

/-- **Lattice propagator on the torus converges to the continuum Green's function.**

For smooth torus test functions f, g ∈ C∞(T²_L):

  `torusEmbeddedTwoPoint L N mass f g → torusContinuumGreen L mass f g`

as N → ∞ (with L fixed, a = L/N → 0).

Mathematically: the lattice eigenvalues `(4N²/L²) sin²(πn/N) + m²` converge
to the continuum eigenvalues `(2πn/L)² + m²` for each mode n. The sum over
n ∈ (ℤ/Nℤ)² with rapidly decaying f̂(n) converges to the ℤ²-sum by dominated
convergence.

This is a **pure UV limit**: L is fixed, only N → ∞. There is no IR tail
issue because the torus has finite volume.

Reference: Glimm-Jaffe §6.1, Simon Ch. I. -/
axiom torus_propagator_convergence
    (mass : ℝ) (hmass : 0 < mass)
    (f g : TorusTestFunction L) :
    Tendsto
      (fun N : ℕ => torusEmbeddedTwoPoint L (N + 1) mass hmass f g)
      atTop
      (nhds (torusContinuumGreen L mass hmass f g))

/-! ## Uniform bound on the embedded two-point function -/

/-- **Uniform bound on torus second moments.**

  `E[Φ_N(f)²] ≤ C(f, L, m)` uniformly in N ≥ 1

This follows from:
1. **Eigenvalue lower bound:** All eigenvalues of `-Δ_{lat} + m²` satisfy `λ_k ≥ m²`
   (since the discrete Laplacian is nonneg-definite), so `λ_k⁻¹ ≤ 1/m²`.
2. **Parseval:** `Σ_k ⟨e_k, ι*f⟩² = ‖ι*f‖²` (lattice eigenvectors are orthonormal).
3. **Riemann sum bound:** `‖ι*f‖² = (L/N)² Σ_x |f(xL/N)|²` is a Riemann sum for
   `‖f‖²_{L²(T²_L)}` of a continuous function on the compact torus, hence bounded
   uniformly in N.
4. **Combined:** `E[Φ_N(f)²] = Σ_k λ_k⁻¹ ⟨e_k, ι*f⟩² ≤ (1/m²) · C_f`.

The key advantage over S'(ℝ^d): finite volume means the Riemann sum is over
a finite domain, eliminating any IR contribution.

Reference: Glimm-Jaffe §6.1 (lattice propagator bounds). -/
theorem torusEmbeddedTwoPoint_uniform_bound (mass : ℝ) (hmass : 0 < mass)
    (f : TorusTestFunction L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N],
    torusEmbeddedTwoPoint L N mass hmass f f ≤ C := by
  -- Step 1: Get the Riemann sum bound
  obtain ⟨C_f, hC_f_pos, hC_f_bound⟩ := latticeTestFn_norm_sq_bounded L f
  -- The bound is C = mass⁻² * C_f
  refine ⟨mass⁻¹ ^ 2 * C_f, mul_pos (pow_pos (inv_pos.mpr hmass) 2) hC_f_pos, fun N _ => ?_⟩
  -- Step 2: Rewrite as lattice second moment
  rw [torusEmbeddedTwoPoint_eq_lattice_second_moment]
  -- Step 3: Apply second moment = covariance identity
  rw [lattice_second_moment_eq_inner]
  -- Step 4: Apply covariance bound
  calc
    @inner ℝ ell2' _
        (latticeCovariance 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass
          (latticeTestFn L N f))
        (latticeCovariance 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass
          (latticeTestFn L N f))
      ≤ mass⁻¹ ^ 2 *
          ∑ x : FinLatticeSites 2 N, (latticeTestFn L N f x) ^ 2 := by
        exact covariance_inner_le_mass_inv_sq_norm_sq N (circleSpacing L N) mass
          (circleSpacing_pos L N) hmass (latticeTestFn L N f)
    _ ≤ mass⁻¹ ^ 2 * C_f := by
        apply mul_le_mul_of_nonneg_left (hC_f_bound N) (le_of_lt (pow_pos (inv_pos.mpr hmass) 2))

/-! ## Positivity of the continuum Green's function -/

/-- **Positivity of the torus continuum Green's function.**

  `G_L(f, f) > 0` for nonzero f ∈ C∞(T²_L)

The Fourier-space representation has integrand
`|f̂(n)|² / ((2πn/L)² + m²)` which is nonneg, and strictly positive for
at least one n since f̂ ≠ 0 (Fourier transform is injective on C∞(T²)). -/
theorem torusContinuumGreen_pos (mass : ℝ) (hmass : 0 < mass)
    (f : TorusTestFunction L) (hf : f ≠ 0) :
    0 < torusContinuumGreen L mass hmass f f := by
  unfold torusContinuumGreen
  exact greenFunctionBilinear_pos mass hmass f hf

/-- **Nonnegativity of the torus continuum Green's function on the diagonal.**

  `G_L(f, f) ≥ 0` for all f ∈ C∞(T²_L)

Each spectral term `|f̂(n)|² / ((2πn/L)² + m²) ≥ 0`. -/
theorem torusContinuumGreen_nonneg (mass : ℝ) (hmass : 0 < mass)
    (f : TorusTestFunction L) :
    0 ≤ torusContinuumGreen L mass hmass f f := by
  unfold torusContinuumGreen
  exact greenFunctionBilinear_nonneg mass hmass f

end Pphi2

end
