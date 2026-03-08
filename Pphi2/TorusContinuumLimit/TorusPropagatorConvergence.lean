/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Torus Propagator Convergence

The main analytical content of the torus Gaussian continuum limit: the lattice
Green's function on T²_L converges to the continuum Green's function as N → ∞.

## Main results

- `torusEmbeddedTwoPoint_eq_spectral_sum` — spectral decomposition of lattice two-point
- `torus_propagator_convergence` — lattice → continuum convergence (DCT on spectral modes)
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
import Lattice.Convergence

noncomputable section

open GaussianField MeasureTheory Filter NuclearTensorProduct

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
theorem latticeTestFn_expand (N : ℕ) [NeZero N] (f : TorusTestFunction L) :
    latticeTestFn L N f =
    ∑ x : FinLatticeSites 2 N, (latticeTestFn L N f) x • Pi.single x (1 : ℝ) := by
  funext y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The embedded two-point function (with f = g) factors through the lattice. -/
theorem torusEmbedLift_eval_eq (N : ℕ) [NeZero N]
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
        (v : EuclideanSpace ℝ _) x *
          (massEigenvalues 2 N a mass k *
            (v : EuclideanSpace ℝ _) x) =
        massEigenvalues 2 N a mass k *
          ((v : EuclideanSpace ℝ _) x *
            (v : EuclideanSpace ℝ _) x) := by
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
  rw [show latticeCovariance 2 N a mass ha hmass =
    spectralLatticeCovariance 2 N a mass ha hmass from rfl]
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

/-! ## Helper lemmas for the Riemann sum bound

The following lemmas connect the DyninMityaginSpace structure (basis, coefficients)
of `SmoothMap_Circle` and `NuclearTensorProduct` to the concrete Fourier basis
and circle restriction map, enabling pointwise bounds on `evalTorusAtSite`. -/

/-- Biorthogonality of the DyninMityaginSpace coefficient and basis functions
for `SmoothMap_Circle`. -/
private theorem smoothCircle_coeff_basis (m n : ℕ) :
    DyninMityaginSpace.coeff m (DyninMityaginSpace.basis n : SmoothMap_Circle L ℝ) =
    if m = n then 1 else 0 := by
  change (RapidDecaySeq.coeffCLM m).comp
    (SmoothMap_Circle.smoothCircleRapidDecayEquiv (L := L)).toContinuousLinearMap
    ((SmoothMap_Circle.smoothCircleRapidDecayEquiv (L := L)).symm (RapidDecaySeq.basisVec n)) =
    if m = n then 1 else 0
  simp only [ContinuousLinearMap.comp_apply,
    RapidDecaySeq.coeffCLM, ContinuousLinearMap.coe_mk', RapidDecaySeq.coeffLM,
    LinearMap.coe_mk, AddHom.coe_mk]
  change (SmoothMap_Circle.smoothCircleRapidDecayEquiv (L := L)
    ((SmoothMap_Circle.smoothCircleRapidDecayEquiv (L := L)).symm
      (RapidDecaySeq.basisVec n))).val m = if m = n then 1 else 0
  rw [ContinuousLinearEquiv.apply_symm_apply]; simp [RapidDecaySeq.basisVec]

/-- The pure tensor of DyninMityaginSpace basis elements equals a `basisVec`
indexed by the Cantor pairing. -/
private theorem pure_basis_eq_basisVec_pair (i j : ℕ) :
    (NuclearTensorProduct.pure
      (DyninMityaginSpace.basis i : SmoothMap_Circle L ℝ)
      (DyninMityaginSpace.basis j : SmoothMap_Circle L ℝ) : TorusTestFunction L) =
    RapidDecaySeq.basisVec (Nat.pair i j) := by
  ext m
  simp only [NuclearTensorProduct.pure_val, RapidDecaySeq.basisVec]
  rw [smoothCircle_coeff_basis L (Nat.unpair m).1 i,
      smoothCircle_coeff_basis L (Nat.unpair m).2 j]
  by_cases h1 : (Nat.unpair m).1 = i <;> by_cases h2 : (Nat.unpair m).2 = j <;>
    simp only [h1, h2, ↓reduceIte, mul_one, mul_zero,
      left_eq_ite_iff, right_eq_ite_iff, one_ne_zero,
      zero_ne_one, imp_false, Decidable.not_not]
  · conv_lhs => rw [← Nat.pair_unpair m]; rw [h1, h2]
  · intro h; exact h2 (by have := congr_arg (fun p => (Nat.unpair p).2) h
                          simpa only [Nat.unpair_pair] using this)
  · intro h; exact h1 (by have := congr_arg (fun p => (Nat.unpair p).1) h
                          simpa only [Nat.unpair_pair] using this)
  · intro h; exact h1 (by have := congr_arg (fun p => (Nat.unpair p).1) h
                          simpa only [Nat.unpair_pair] using this)

/-- Evaluation of a torus test function at a lattice site, applied to a basis vector,
equals the product of circle restrictions applied to each component. -/
private theorem evalTorusAtSite_basisVec (N : ℕ) [NeZero N]
    (x : FinLatticeSites 2 N) (m : ℕ) :
    evalTorusAtSite L N x (RapidDecaySeq.basisVec m) =
    circleRestriction L N (DyninMityaginSpace.basis (Nat.unpair m).1 :
      SmoothMap_Circle L ℝ) (x 0) *
    circleRestriction L N (DyninMityaginSpace.basis (Nat.unpair m).2 :
      SmoothMap_Circle L ℝ) (x 1) := by
  rw [show RapidDecaySeq.basisVec m = NuclearTensorProduct.pure
      (DyninMityaginSpace.basis (Nat.unpair m).1 : SmoothMap_Circle L ℝ)
      (DyninMityaginSpace.basis (Nat.unpair m).2 : SmoothMap_Circle L ℝ) from by
    rw [pure_basis_eq_basisVec_pair, Nat.pair_unpair]]
  change NuclearTensorProduct.evalCLM _ _ _ = _
  rw [NuclearTensorProduct.evalCLM_pure]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

/-- The DyninMityaginSpace basis for `SmoothMap_Circle` is the Fourier basis. -/
private theorem dm_basis_eq_fourierBasis (m : ℕ) :
    (DyninMityaginSpace.basis m : SmoothMap_Circle L ℝ) =
    SmoothMap_Circle.fourierBasis (L := L) m := by
  apply SmoothMap_Circle.ext; intro x
  change (SmoothMap_Circle.fromRapidDecay (RapidDecaySeq.basisVec m) : ℝ → ℝ) x =
    SmoothMap_Circle.fourierBasisFun m x
  change ∑' n, (RapidDecaySeq.basisVec m).val n *
    SmoothMap_Circle.fourierBasisFun (L := L) n x = SmoothMap_Circle.fourierBasisFun m x
  rw [tsum_eq_single m]
  · simp [RapidDecaySeq.basisVec]
  · intro n hn; simp [RapidDecaySeq.basisVec, hn]

/-- **Riemann sum bound.**

The sum `Σ_x (evalTorusAtSite L N x f)²` is bounded uniformly in N.
This is because it's a Riemann sum of a continuous function on the compact torus.

More precisely: `evalTorusAtSite L N x f` involves `circleRestriction` with
`√(L/N)` normalization, so the squared sum is `O(1)` as N → ∞. -/
theorem latticeTestFn_norm_sq_bounded (f : TorusTestFunction L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N],
    ∑ x : FinLatticeSites 2 N, (latticeTestFn L N f x) ^ 2 ≤ C := by
  -- Step 1: Uniform C^0 bound on Fourier basis elements.
  -- sobolevSeminorm 0 (fourierBasis n) <= C₀ uniformly in n
  obtain ⟨C₀, hC₀_pos, hC₀_bound⟩ :=
    SmoothMap_Circle.sobolevSeminorm_fourierBasis_le (L := L) 0
  have hC₀ : ∀ n, SmoothMap_Circle.sobolevSeminorm (L := L) 0
      (SmoothMap_Circle.fourierBasis n) ≤ C₀ := fun n => by
    specialize hC₀_bound n; simp only [pow_zero, mul_one] at hC₀_bound; exact hC₀_bound
  -- Step 2: Set up the witness for the bound.
  set p₀f := RapidDecaySeq.rapidDecaySeminorm 0 f
  refine ⟨L ^ 2 * C₀ ^ 4 * p₀f ^ 2 + 1, by positivity, fun N _ => ?_⟩
  -- Step 3: Summability of |f.val m|.
  have hf_sum : Summable (fun m => |f.val m|) :=
    (f.rapid_decay 0).congr (fun m => by simp [pow_zero])
  -- Step 4: Bound |circleRestriction L N (DM.basis n) k| ≤ √(L/N) * C₀.
  have h_cr : ∀ n (k : ZMod N),
      |circleRestriction L N (DyninMityaginSpace.basis n :
        SmoothMap_Circle L ℝ) k| ≤ Real.sqrt (L / ↑N) * C₀ := by
    intro n k
    rw [dm_basis_eq_fourierBasis, circleRestriction_apply, circleSpacing_eq,
      abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    calc |(SmoothMap_Circle.fourierBasis (L := L) n : ℝ → ℝ) (circlePoint L N k)|
        = ‖iteratedDeriv 0 ((SmoothMap_Circle.fourierBasis (L := L) n : ℝ → ℝ))
            (circlePoint L N k)‖ := by rw [iteratedDeriv_zero, Real.norm_eq_abs]
      _ ≤ SmoothMap_Circle.sobolevSeminorm 0 (SmoothMap_Circle.fourierBasis n) :=
          SmoothMap_Circle.norm_iteratedDeriv_le_sobolevSeminorm' _ 0 _
      _ ≤ C₀ := hC₀ n
  -- Step 5: Bound |eval_x(basisVec m)| ≤ (L/N) * C₀².
  have hLN : (0 : ℝ) ≤ L / ↑N :=
    (div_pos hL.out (Nat.cast_pos.mpr (NeZero.pos N))).le
  have h_basis : ∀ (x : FinLatticeSites 2 N) (m : ℕ),
      |evalTorusAtSite L N x (RapidDecaySeq.basisVec m)| ≤ L / ↑N * C₀ ^ 2 := by
    intro x m
    rw [evalTorusAtSite_basisVec, abs_mul]
    calc |circleRestriction L N (DyninMityaginSpace.basis (Nat.unpair m).1 :
            SmoothMap_Circle L ℝ) (x 0)| *
          |circleRestriction L N (DyninMityaginSpace.basis (Nat.unpair m).2 :
            SmoothMap_Circle L ℝ) (x 1)|
        ≤ (Real.sqrt (L / ↑N) * C₀) * (Real.sqrt (L / ↑N) * C₀) :=
          mul_le_mul (h_cr _ _) (h_cr _ _) (abs_nonneg _)
            (mul_nonneg (Real.sqrt_nonneg _) hC₀_pos.le)
      _ = L / ↑N * C₀ ^ 2 := by nlinarith [Real.sq_sqrt hLN]
  -- Step 6: Bound |eval_x f| ≤ (L/N) * C₀² * p₀f using DM expansion.
  have h_pw : ∀ x : FinLatticeSites 2 N,
      |evalTorusAtSite L N x f| ≤ L / ↑N * C₀ ^ 2 * p₀f := by
    intro x
    rw [DyninMityaginSpace.expansion (evalTorusAtSite L N x) f]
    -- Summability of the product series
    have hsf : Summable (fun m => f.val m *
        evalTorusAtSite L N x (RapidDecaySeq.basisVec m)) :=
      (hf_sum.mul_right (L / ↑N * C₀ ^ 2)).of_norm_bounded
        (fun m => by rw [Real.norm_eq_abs, abs_mul]
                     exact mul_le_mul_of_nonneg_left (h_basis x m) (abs_nonneg _))
    -- |∑' m, c_m * eval_x(e_m)| ≤ ∑' m, |c_m| * bound = bound * ∑' |c_m| = bound * p₀f
    calc |∑' m, f.val m * evalTorusAtSite L N x (RapidDecaySeq.basisVec m)|
        = ‖∑' m, f.val m * evalTorusAtSite L N x (RapidDecaySeq.basisVec m)‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∑' m, ‖f.val m * evalTorusAtSite L N x (RapidDecaySeq.basisVec m)‖ :=
          norm_tsum_le_tsum_norm hsf.norm
      _ ≤ ∑' m, |f.val m| * (L / ↑N * C₀ ^ 2) := by
          apply Summable.tsum_le_tsum _ hsf.norm (hf_sum.mul_right _)
          intro m
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_left (h_basis x m) (abs_nonneg _)
      _ = L / ↑N * C₀ ^ 2 * ∑' m, |f.val m| := by rw [tsum_mul_right]; ring
      _ = L / ↑N * C₀ ^ 2 * p₀f := by
          congr 1
          change ∑' m, |f.val m| = ∑' m, |f.val m| * (1 + (m : ℝ)) ^ 0
          simp
  -- Step 7: Sum of squares over lattice sites.
  -- N² * (L/N)² * C₀⁴ * p₀f² = L² * C₀⁴ * p₀f² (the N cancels)
  calc ∑ x : FinLatticeSites 2 N, (latticeTestFn L N f x) ^ 2
      = ∑ x, (evalTorusAtSite L N x f) ^ 2 := rfl
    _ ≤ ∑ _x : FinLatticeSites 2 N, (L / ↑N * C₀ ^ 2 * p₀f) ^ 2 := by
        apply Finset.sum_le_sum; intro x _
        exact sq_le_sq' (by linarith [h_pw x, neg_abs_le (evalTorusAtSite L N x f)])
          (le_of_abs_le (h_pw x))
    _ = ↑(Fintype.card (FinLatticeSites 2 N)) * (L / ↑N * C₀ ^ 2 * p₀f) ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ↑N ^ 2 * (L / ↑N * C₀ ^ 2 * p₀f) ^ 2 := by
        congr 1; simp [FinLatticeSites, ZMod.card, Fintype.card_fin]
    _ = L ^ 2 * C₀ ^ 4 * p₀f ^ 2 := by
        have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
        field_simp
    _ ≤ L ^ 2 * C₀ ^ 4 * p₀f ^ 2 + 1 := le_add_of_nonneg_right one_pos.le

/-! ## Cross-moment spectral identity -/

/-- The embedded two-point function for general f, g factors through the lattice.

Generalization of `torusEmbeddedTwoPoint_eq_lattice_second_moment` to the cross case:
  `⟨Φ_N(f), Φ_N(g)⟩ = ∫ ω(ι*f) · ω(ι*g) dμ_{GFF}` -/
theorem torusEmbeddedTwoPoint_eq_lattice_cross_moment
    (N : ℕ) [NeZero N] (mass : ℝ) (hmass : 0 < mass)
    (f g : TorusTestFunction L) :
    torusEmbeddedTwoPoint L N mass hmass f g =
    ∫ ω : Configuration (FinLatticeField 2 N),
      (ω (latticeTestFn L N f)) * (ω (latticeTestFn L N g))
      ∂(latticeGaussianMeasure 2 N (circleSpacing L N) mass
        (circleSpacing_pos L N) hmass) := by
  unfold torusEmbeddedTwoPoint torusContinuumMeasure
  rw [integral_map (torusEmbedLift_measurable L N).aemeasurable]
  · congr 1; ext ω
    rw [torusEmbedLift_eval_eq L N f ω, torusEmbedLift_eval_eq L N g ω]
  · exact ((configuration_eval_measurable f).mul
      (configuration_eval_measurable g)).aestronglyMeasurable

/-- The embedded two-point function equals the lattice spectral sum.

  `⟨Φ_N(f), Φ_N(g)⟩ = Σ_k λ_k⁻¹ · c_k(ι*f) · c_k(ι*g)`

where λ_k are eigenvalues of `-Δ_{lat} + m²`, c_k(h) = Σ_x e_k(x) h(x) are
the coefficients in the lattice eigenbasis, and ι*f = latticeTestFn f. -/
theorem torusEmbeddedTwoPoint_eq_spectral_sum
    (N : ℕ) [NeZero N] (mass : ℝ) (hmass : 0 < mass)
    (f g : TorusTestFunction L) :
    torusEmbeddedTwoPoint L N mass hmass f g =
    ∑ k : FinLatticeSites 2 N,
      (massEigenvalues 2 N (circleSpacing L N) mass k)⁻¹ *
      (∑ x, (massEigenvectorBasis 2 N (circleSpacing L N) mass k :
        EuclideanSpace ℝ _) x * (latticeTestFn L N f) x) *
      (∑ x, (massEigenvectorBasis 2 N (circleSpacing L N) mass k :
        EuclideanSpace ℝ _) x * (latticeTestFn L N g) x) := by
  rw [torusEmbeddedTwoPoint_eq_lattice_cross_moment,
      lattice_cross_moment,
      lattice_covariance_eq_spectral]

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

Proof strategy:
1. Each `torusEmbeddedTwoPoint L (N+1)` is a finite spectral sum
   (by `torusEmbeddedTwoPoint_eq_spectral_sum`).
2. The continuum `torusContinuumGreen` is `∑' m, greenTerm mass f g m`.
3. For each Fourier mode m, the lattice spectral term converges to
   the continuum term: `sin(πn/N)/(πn/N) → 1` for eigenvalues,
   and aliasing terms vanish by rapid decay of Schwartz coefficients.
4. Each term is bounded by `|coeff_m(f)|·|coeff_m(g)|/mass²` (summable).
5. Apply `tendsto_tsum_of_dominated_convergence`.

Reference: Glimm-Jaffe §6.1, Simon Ch. I. -/
theorem torus_propagator_convergence
    (mass : ℝ) (hmass : 0 < mass)
    (f g : TorusTestFunction L) :
    Tendsto
      (fun N : ℕ => torusEmbeddedTwoPoint L (N + 1) mass hmass f g)
      atTop
      (nhds (torusContinuumGreen L mass hmass f g)) := by
  -- Rewrite each torusEmbeddedTwoPoint as lattice covariance
  have h_eq : ∀ N : ℕ, torusEmbeddedTwoPoint L (N + 1) mass hmass f g =
      covariance
        (latticeCovariance 2 (N + 1) (circleSpacing L (N + 1)) mass
          (circleSpacing_pos L (N + 1)) hmass)
        (fun x => evalTorusAtSite L (N + 1) x f)
        (fun x => evalTorusAtSite L (N + 1) x g) := by
    intro N
    rw [torusEmbeddedTwoPoint_eq_lattice_cross_moment, lattice_cross_moment]
    rfl
  simp_rw [h_eq]
  -- The target is greenFunctionBilinear
  change Tendsto _ atTop (nhds (greenFunctionBilinear mass hmass f g))
  exact lattice_green_tendsto_continuum L mass hmass f g

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
