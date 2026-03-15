/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Interacting P(φ)₂ Continuum Limit on the Torus

Defines the interacting P(φ)₂ measure on the torus and proves existence
of a subsequential weak limit via the Cauchy-Schwarz density transfer.

## Main results

- `torusInteractingMeasure` — pushforward of lattice interacting measure to torus
- `nelson_exponential_estimate` — (axiom) uniform-in-N L² bound on Boltzmann weight
- `torus_interacting_second_moment_uniform` — uniform second moment bound (from Nelson)
- `torus_interacting_tightness` — (proved!) tightness via Mitoma-Chebyshev
- `torusInteractingLimit_exists` — existence of subsequential limit (proved!)

## Mathematical background

### Cauchy-Schwarz density transfer

The interacting measure `dμ_P = (1/Z) e^{-V} dμ_{GFF}` has second moments
controlled by the Gaussian second moments via Cauchy-Schwarz:

  `E_P[|ω(f)|²] ≤ (1/Z) · E_{GFF}[|ω(f)|⁴]^{1/2} · E_{GFF}[e^{-2V}]^{1/2}`

The Gaussian fourth moment is controlled by the second moment (Gaussian
hypercontractivity), and `E_{GFF}[e^{-2V}]` is bounded by Nelson's exponential
estimate. Combined with the **uniform Gaussian tightness** on the torus, this
gives interacting tightness.

### Advantage of the torus

The finite volume makes both Nelson's estimate and the Riemann sum bounds
significantly cleaner. The infinite-volume limit (L → ∞) can be done
separately as a second step.

## References

- Glimm-Jaffe, *Quantum Physics*, §19.3-19.4
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. V-VI
-/

import Pphi2.TorusContinuumLimit.TorusGaussianLimit

noncomputable section

open GaussianField MeasureTheory Filter

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Interacting measure on the torus -/

/-- The torus-embedded interacting P(φ)₂ measure.

Pushforward of the lattice interacting measure `μ_{P,N}` under the torus
embedding, where the lattice spacing is a = L/N.

  `μ_{P,N}^{torus} = (ι̃_N)_* μ_{P,N}` -/
def torusInteractingMeasure (N : ℕ) [NeZero N] (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) :
    Measure (Configuration (TorusTestFunction L)) :=
  Measure.map (torusEmbedLift L N)
    (interactingLatticeMeasure 2 N P (circleSpacing L N) mass (circleSpacing_pos L N) hmass)

/-- The torus interacting measure is a probability measure. -/
instance torusInteractingMeasure_isProbability (N : ℕ) [NeZero N]
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    IsProbabilityMeasure (torusInteractingMeasure L N P mass hmass) := by
  unfold torusInteractingMeasure
  haveI := interactingLatticeMeasure_isProbability 2 N P
    (circleSpacing L N) mass (circleSpacing_pos L N) hmass
  exact Measure.isProbabilityMeasure_map
    (torusEmbedLift_measurable L N).aemeasurable

/-! ## Nelson's exponential estimate

The key analytical input for the interacting continuum limit. The naive
bound from `exponential_moment_bound` gives K_N = exp(2·N²·A) which
blows up as N → ∞. Nelson's estimate shows that K can be chosen
independently of the lattice size N. -/

/-- **Nelson's exponential estimate** (uniform in lattice size N).

The L² norm of the Boltzmann weight `exp(-V_a)` with respect to the lattice
GFF measure is bounded by a constant K that depends on P, mass, and L,
but NOT on the lattice size N:

  `∫ exp(-2·V_{L/N}(φ)) dμ_{GFF}(φ) ≤ K`   for all `N ≥ 1`

The Wick constant `c_a ≤ mass⁻²` is bounded uniformly (proved in
`wickConstant_le_inv_mass_sq`), so the Wick polynomial has a uniform
lower bound. The difficulty is that the interaction `V = a² Σ_x :P(φ(x)):_c`
sums over `N²` lattice sites, giving the naive bound `V ≥ -N²·A` and hence
`exp(-2V) ≤ exp(2·N²·A)`. This blows up as N → ∞.

Nelson's estimate overcomes this by exploiting the Gaussian measure's
correlation structure: the probability that many sites simultaneously have
large negative Wick polynomial values is exponentially suppressed.

**Proof methods** (not yet formalized):
1. Nelson's symmetry + hypercontractivity of the OU semigroup (Simon §V.1-V.2)
2. Cluster expansions (Glimm-Jaffe §19.1, Battle-Federbush)

References: Nelson (1966), Simon *P(φ)₂* Ch. V, Glimm-Jaffe §19.1-19.2. -/
axiom nelson_exponential_estimate
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (K : ℝ), 0 < K ∧
    ∀ (N : ℕ) [NeZero N],
    ∫ ω : Configuration (FinLatticeField 2 N),
        (Real.exp (-interactionFunctional 2 N P (circleSpacing L N) mass ω)) ^ 2
        ∂(latticeGaussianMeasure 2 N (circleSpacing L N) mass
          (circleSpacing_pos L N) hmass) ≤ K

/-! ## Uniform second moment bounds for interacting measures -/

/-- **Uniform second moment bound** for the torus interacting measures.

For each test function `f`, the second moment `∫ (ω f)² dμ_{P,N}` is bounded
uniformly in N. This is the key step from Nelson's estimate to tightness.

**Proof outline** (Cauchy-Schwarz density transfer):

1. Push through torus embedding:
   `∫ (ω f)² dμ_{P,N}^{torus} = ∫ (ω g_f)² dμ_{P,N}^{lattice}`
   where `g_f` is the pullback of `f` to the lattice.

2. Expand interacting measure and apply Cauchy-Schwarz:
   `∫ F dμ_{int} = (1/Z) ∫ F·bw dμ_{GFF} ≤ (1/Z)·√(∫ F² dμ_{GFF})·√(∫ bw² dμ_{GFF})`

3. Bound each factor:
   - `Z ≥ 1` by Jensen (proved in `partitionFunction_ge_one`)
   - `∫ bw² dμ_{GFF} ≤ K` by `nelson_exponential_estimate`
   - `∫ (ω g_f)⁴ dμ_{GFF} ≤ 9·(∫ (ω g_f)² dμ_{GFF})²` by `gaussian_hypercontractive`
   - `∫ (ω g_f)² dμ_{GFF} ≤ Cg(f)` by `torusEmbeddedTwoPoint_uniform_bound`

4. Combine: `∫ (ω f)² dμ_{P,N}^{torus} ≤ √K · 3 · Cg(f)` uniformly in N.

Reference: Glimm-Jaffe §19.3, Simon Ch. V. -/
theorem torus_interacting_second_moment_uniform
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (f : TorusTestFunction L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N],
    ∫ ω : Configuration (TorusTestFunction L),
      (ω f) ^ 2 ∂(torusInteractingMeasure L N P mass hmass) ≤ C := by
  -- Step 1: Get K from Nelson's exponential estimate (uniform in N)
  obtain ⟨K, hK_pos, hK_bound⟩ := nelson_exponential_estimate L P mass hmass
  -- Step 2: Get Cg from uniform Gaussian second moment bound
  obtain ⟨Cg, hCg_pos, hCg_bound⟩ := torusEmbeddedTwoPoint_uniform_bound L mass hmass f
  -- C = 3 · √K · Cg works, from density transfer + hypercontractivity
  refine ⟨3 * Real.sqrt K * Cg,
    mul_pos (mul_pos (by norm_num : (0:ℝ) < 3) (Real.sqrt_pos_of_pos hK_pos)) hCg_pos,
    fun N _ => ?_⟩
  -- Step 1: Push integral through torus embedding
  -- torusInteractingMeasure = Measure.map (torusEmbedLift L N) (interactingLatticeMeasure ...)
  set μ_int := interactingLatticeMeasure 2 N P (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass
  set μ_GFF := latticeGaussianMeasure 2 N (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass
  set ι := torusEmbedLift L N
  set g := latticeTestFn L N f
  have hι_meas : AEMeasurable ι μ_int :=
    (torusEmbedLift_measurable L N).aemeasurable
  -- ∫ (ω f)² d(map ι μ_int) = ∫ ((ι ω) f)² dμ_int = ∫ (ω g)² dμ_int
  change ∫ ω, (ω f) ^ 2 ∂(Measure.map ι μ_int) ≤ 3 * Real.sqrt K * Cg
  rw [integral_map hι_meas
    ((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable]
  -- Rewrite (ι ω) f = ω g using torusEmbedLift_eval_eq
  have h_eval : ∀ ω : Configuration (FinLatticeField 2 N),
      (ι ω) f = ω g := fun ω => torusEmbedLift_eval_eq L N f ω
  simp_rw [h_eval]
  -- Now goal: ∫ (ω g)² dμ_int ≤ 3 * √K * Cg
  -- Step 2: Apply density_transfer_bound with F(ω) = (ω g)²
  have hZ_ge_one := partitionFunction_ge_one 2 N P mass hmass
    (circleSpacing L N) (circleSpacing_pos L N)
  -- F is nonneg, measurable, and has finite Gaussian L²
  have hF_nn : ∀ ω : Configuration (FinLatticeField 2 N), 0 ≤ (ω g) ^ 2 :=
    fun ω => sq_nonneg _
  have hF_meas : AEStronglyMeasurable (fun ω : Configuration (FinLatticeField 2 N) =>
      (ω g) ^ 2) μ_GFF :=
    ((configuration_eval_measurable g).pow_const 2).aestronglyMeasurable
  -- F² = (ω g)⁴ is integrable under μ_GFF (all Gaussian moments are finite)
  have hF_sq_int : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
      ((ω g) ^ 2) ^ 2) μ_GFF := by
    have h4 : MemLp (fun ω : Configuration (FinLatticeField 2 N) => ω g)
        4 μ_GFF := by
      exact_mod_cast pairing_memLp (latticeCovariance 2 N (circleSpacing L N) mass
        (circleSpacing_pos L N) hmass) g 4
    have hmem := h4.norm_rpow (p := (4 : ENNReal))
      (by norm_num : (4 : ENNReal) ≠ 0) (by norm_num : (4 : ENNReal) ≠ ⊤)
    rw [memLp_one_iff_integrable] at hmem
    have h_int : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
        ‖ω g‖ ^ (4 : ℕ)) μ_GFF := by
      refine hmem.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp [ENNReal.toReal_ofNat]
    exact h_int.congr (Filter.Eventually.of_forall fun ω => by
      dsimp only
      rw [Real.norm_eq_abs]
      conv_rhs => rw [show ω g ^ 2 = |ω g| ^ 2 from (sq_abs _).symm]
      ring)
  -- Apply density_transfer_bound
  have h_dt := density_transfer_bound 2 N P (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass K hK_pos (hK_bound N)
    hZ_ge_one (fun ω => (ω g) ^ 2) hF_nn hF_meas hF_sq_int
  -- h_dt: ∫ (ω g)² dμ_int ≤ K^{1/2} * (∫ F^{(2:ℝ)} dμ_GFF)^{1/2}
  -- where F ω = (ω g) ^ 2
  -- Step 3: Convert rpow to nat pow in h_dt and bound
  -- ((ω g)^2) ^ (2:ℝ) = ((ω g)^2) ^ 2 since (ω g)^2 ≥ 0
  have h_rpow_to_npow : ∀ ω : Configuration (FinLatticeField 2 N),
      (fun ω => (ω g) ^ 2) ω ^ (2:ℝ) = ((ω g) ^ 2) ^ 2 := by
    intro ω
    exact Real.rpow_natCast ((ω g) ^ 2) 2
  -- Rewrite the integral in h_dt from rpow to nat pow
  have h_int_rpow_eq : ∫ ω, (fun ω => (ω g) ^ 2) ω ^ (2:ℝ) ∂μ_GFF =
      ∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF := by
    congr 1; ext ω; exact h_rpow_to_npow ω
  -- Step 4: Bound ∫ ((ω g)²)² dμ_GFF using hypercontractivity
  -- ∫ (ω g)⁴ dμ_GFF ≤ 9 * (∫ (ω g)² dμ_GFF)²
  -- We use gaussian_hypercontractive via nat-pow 1D form
  -- hypercontractive_1d_p4 with n=1:
  --   ∫ |x|^4 dN(0,v) ≤ 3^2 * (∫ |x|^2 dN(0,v))^2
  -- Applied via pairing_is_gaussian to get:
  --   ∫ (ω g)⁴ dμ_GFF ≤ 9 * (∫ (ω g)² dμ_GFF)²
  -- But we use the direct bound: ∫ ((ω g)²)² = ∫ (ω g)⁴
  -- torusEmbeddedTwoPoint ≤ Cg, so ∫ (ω g)² ≤ Cg, so ∫ (ω g)⁴ ≤ 9 * Cg²
  have h_second_moment_eq : ∫ ω, (ω g) ^ 2 ∂μ_GFF =
      torusEmbeddedTwoPoint L N mass hmass f f :=
    (torusEmbeddedTwoPoint_eq_lattice_second_moment L N mass hmass f).symm
  have h_second_le : ∫ ω, (ω g) ^ 2 ∂μ_GFF ≤ Cg := by
    rw [h_second_moment_eq]; exact hCg_bound N
  have h_second_nn : 0 ≤ ∫ ω, (ω g) ^ 2 ∂μ_GFF :=
    integral_nonneg fun ω => sq_nonneg _
  -- ∫ ((ω g)²)² ≤ 9 * Cg² via hypercontractivity
  -- Use gaussian_hypercontractive from GaussianField
  set T := latticeCovariance 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass
  have hμ_eq : μ_GFF = GaussianField.measure T := rfl
  -- Apply hypercontractive_1d_p4 via pairing_is_gaussian
  have h_fourth_le : ∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF ≤ 9 * Cg ^ 2 := by
    -- First convert to |ω g|^4
    have h_eq4 : ∀ ω : Configuration (FinLatticeField 2 N),
        ((ω g) ^ 2) ^ 2 = |ω g| ^ 4 := by
      intro ω; rw [show ω g ^ 2 = |ω g| ^ 2 from (sq_abs _).symm]; ring
    simp_rw [h_eq4]
    -- Use gaussian_hypercontractive with p=4, n=1, m=2
    have h_hyper := gaussian_hypercontractive T g 1 4
      (by norm_num : (2:ℝ) ≤ 4) 2 (by norm_num : 1 ≤ 2)
      (by norm_num : (4:ℝ) = 2 * ↑2)
    -- h_hyper : ∫ |ω g| ^ (4 * ↑1) dμ ≤ (4-1)^(4*1/2) * (∫ |ω g|^(2*1) dμ)^(4/2)
    -- Convert |ω g| ^ 4 (nat pow) to |ω g| ^ (4 * ↑1) (rpow)
    have h_lhs_eq : ∫ ω, |ω g| ^ 4 ∂μ_GFF =
        ∫ ω, |ω g| ^ ((4:ℝ) * ↑(1:ℕ)) ∂(GaussianField.measure T) := by
      rw [hμ_eq]
      congr 1; ext ω
      simp only [Nat.cast_one, mul_one]
      exact (Real.rpow_natCast _ 4).symm
    rw [h_lhs_eq]
    -- The RHS of h_hyper: (4-1)^(4*1/2) * (∫ |ω g|^(2*1))^(4/2)
    -- Simplify the coefficient: (4-1)^(4*1/2) = 3^2 = 9
    have h_coeff : ((4:ℝ) - 1) ^ ((4:ℝ) * ↑(1:ℕ) / 2) = 9 := by
      simp only [Nat.cast_one, mul_one]
      rw [show (4:ℝ) / 2 = ↑(2:ℕ) from by norm_num, Real.rpow_natCast]
      norm_num
    -- Simplify the exponent: (4/2) = 2
    have h_exp_eq : (∫ ω, |ω g| ^ ((2:ℝ) * ↑(1:ℕ)) ∂(GaussianField.measure T)) ^ ((4:ℝ) / 2) =
        (∫ ω, |ω g| ^ ((2:ℝ) * ↑(1:ℕ)) ∂(GaussianField.measure T)) ^ 2 := by
      rw [show (4:ℝ) / 2 = ↑(2:ℕ) from by norm_num, Real.rpow_natCast]
    -- Convert the RHS integral to nat pow form
    have h_rhs_int_eq : ∫ ω, |ω g| ^ ((2:ℝ) * ↑(1:ℕ)) ∂(GaussianField.measure T) =
        ∫ ω, (ω g) ^ 2 ∂μ_GFF := by
      rw [hμ_eq]; congr 1; ext ω
      simp only [Nat.cast_one, mul_one]
      rw [show |ω g| ^ (2:ℝ) = (|ω g| ^ 2 : ℝ) from Real.rpow_natCast _ 2]
      exact sq_abs _
    -- h_hyper has |ω g| ^ ((2:ℕ)*1) in the RHS integral (nat pow),
    -- while we need (ω g) ^ 2. Show they give the same integral.
    have h_int_2_eq : ∫ ω, |ω g| ^ (2 * 1) ∂(GaussianField.measure T) =
        ∫ ω, (ω g) ^ 2 ∂μ_GFF := by
      rw [hμ_eq]; congr 1; ext ω; simp [sq_abs]
    -- Combine h_hyper with the integral identity
    have h_hyper' : ∫ ω, |ω g| ^ ((4:ℝ) * ↑(1:ℕ)) ∂(GaussianField.measure T) ≤
        ((4:ℝ) - 1) ^ ((4:ℝ) * ↑(1:ℕ) / 2) *
        (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((4:ℝ) / 2) := by
      have := h_hyper
      rwa [h_int_2_eq] at this
    -- rpow-to-nat conversion for the integral exponent
    have h_exp_eq' : (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((4:ℝ) / 2) =
        (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 2 := by
      rw [show (4:ℝ) / 2 = ↑(2:ℕ) from by norm_num, Real.rpow_natCast]
    -- Chain: ∫ |ω g|^{4*1} ≤ 9 * (∫ (ω g)² dμ_GFF)² ≤ 9 * Cg²
    calc ∫ ω, |ω g| ^ ((4:ℝ) * ↑(1:ℕ)) ∂(GaussianField.measure T)
        ≤ ((4:ℝ) - 1) ^ ((4:ℝ) * ↑(1:ℕ) / 2) *
          (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((4:ℝ) / 2) := h_hyper'
      _ = 9 * (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 2 := by
          rw [h_coeff, h_exp_eq']
      _ ≤ 9 * Cg ^ 2 := by
          apply mul_le_mul_of_nonneg_left
          · exact pow_le_pow_left₀ h_second_nn h_second_le 2
          · norm_num
  -- Step 5: Convert back to rpow form and combine
  -- h_dt uses rpow, h_fourth_le uses nat pow; connect them
  have h_fourth_nn : (0:ℝ) ≤ ∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF :=
    integral_nonneg fun ω => by positivity
  have h_4th_bound : (∫ ω, (fun ω => (ω g) ^ 2) ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) ≤
      3 * Cg := by
    rw [h_int_rpow_eq]
    -- (∫ ((ω g)²)²)^{1/2} ≤ (9 * Cg²)^{1/2} = 3 * Cg
    calc (∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF) ^ (1/2:ℝ)
        ≤ (9 * Cg ^ 2) ^ (1/2:ℝ) :=
          Real.rpow_le_rpow h_fourth_nn h_fourth_le (by norm_num : (0:ℝ) ≤ 1/2)
      _ = 3 * Cg := by
          rw [show (9:ℝ) = 3 ^ 2 from by norm_num, ← mul_pow]
          rw [← Real.sqrt_eq_rpow, Real.sqrt_sq
            (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hCg_pos.le)]
  -- Final combination
  have hK_sqrt : K ^ (1/2:ℝ) = Real.sqrt K :=
    (Real.sqrt_eq_rpow K).symm
  calc ∫ ω, (ω g) ^ 2 ∂μ_int
      ≤ K ^ (1/2:ℝ) * (∫ ω, (fun ω => (ω g) ^ 2) ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) := h_dt
    _ ≤ K ^ (1/2:ℝ) * (3 * Cg) :=
        mul_le_mul_of_nonneg_left h_4th_bound (Real.rpow_nonneg hK_pos.le _)
    _ = Real.sqrt K * (3 * Cg) := by rw [hK_sqrt]
    _ = 3 * Real.sqrt K * Cg := by ring

/-! ## Tightness of interacting measures -/

/-- **Tightness of the torus interacting measures.**

The family `{μ_{P,N}^{torus}}_{N ≥ 1}` is tight on Configuration(TorusTestFunction L).

**Proved** from `torus_interacting_second_moment_uniform` (uniform second moment
bounds from Nelson's estimate) via `configuration_tight_of_uniform_second_moments`
(Mitoma-Chebyshev criterion on nuclear duals).

This replaces the former axiom with a theorem that depends only on
`nelson_exponential_estimate` (plus the existing `configuration_tight_of_uniform_second_moments`).

Reference: Glimm-Jaffe §19.3, Simon Ch. V. -/
theorem torus_interacting_tightness
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∀ ε : ℝ, 0 < ε →
    ∃ (K : Set (Configuration (TorusTestFunction L))),
      IsCompact K ∧
      ∀ (N : ℕ) [NeZero N],
      1 - ε ≤ (torusInteractingMeasure L N P mass hmass K).toReal := by
  haveI := configuration_torus_polish L
  haveI := configuration_torus_borelSpace L
  intro ε hε
  -- Apply Mitoma-Chebyshev with ι = {N : ℕ // 0 < N}
  obtain ⟨K, hK_compact, hK_bound⟩ := configuration_tight_of_uniform_second_moments
    (ι := {N : ℕ // 0 < N})
    (fun ⟨N, hN⟩ => haveI : NeZero N := ⟨by omega⟩;
      torusInteractingMeasure L N P mass hmass)
    (fun ⟨N, hN⟩ => by haveI : NeZero N := ⟨by omega⟩; infer_instance)
    (fun f ⟨N, hN⟩ => by  -- integrability of (ω f)² w.r.t. interacting measure
      haveI : NeZero N := ⟨by omega⟩
      -- Push through Measure.map to reduce to lattice integrability
      show Integrable (fun ω => (ω f) ^ 2) (torusInteractingMeasure L N P mass hmass)
      unfold torusInteractingMeasure
      rw [integrable_map_measure
        ((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable
        (torusEmbedLift_measurable L N).aemeasurable]
      -- Rewrite composition using torusEmbedLift_eval_eq
      have h_eq : (fun ω => (ω f) ^ 2) ∘ (torusEmbedLift L N) =
          fun ω => (ω (latticeTestFn L N f)) ^ 2 := by
        ext ω; simp [Function.comp, torusEmbedLift_eval_eq L N f ω]
      rw [h_eq]
      -- Now show: Integrable (fun ω => (ω g)²) (interactingLatticeMeasure ...)
      -- Decompose interacting measure = (1/Z) • μ_GFF.withDensity(bw)
      set g := latticeTestFn L N f
      set μ_GFF := latticeGaussianMeasure 2 N (circleSpacing L N) mass
        (circleSpacing_pos L N) hmass
      set bw := boltzmannWeight 2 N P (circleSpacing L N) mass
      obtain ⟨B, hB⟩ := interactionFunctional_bounded_below 2 N P
        (circleSpacing L N) mass (circleSpacing_pos L N) hmass
      have hZ := partitionFunction_pos 2 N P (circleSpacing L N) mass
        (circleSpacing_pos L N) hmass
      -- Step 1: Reduce to withDensity measure
      suffices h : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
          (ω g) ^ 2)
          (μ_GFF.withDensity (fun ω => ENNReal.ofReal (bw ω))) by
        unfold interactingLatticeMeasure
        exact h.smul_measure (ENNReal.inv_ne_top.mpr ((ENNReal.ofReal_pos.mpr hZ).ne'))
      -- Step 2: Use integrable_withDensity_iff
      have hf_meas : Measurable (fun ω : Configuration (FinLatticeField 2 N) =>
          ENNReal.ofReal (bw ω)) :=
        ENNReal.measurable_ofReal.comp
          ((interactionFunctional_measurable 2 N P (circleSpacing L N) mass).neg.exp)
      apply (integrable_withDensity_iff hf_meas
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
      -- Simplify toReal ∘ ofReal
      have hbw_simp : ∀ ω : Configuration (FinLatticeField 2 N),
          (ENNReal.ofReal (bw ω)).toReal = bw ω :=
        fun ω => ENNReal.toReal_ofReal
          (le_of_lt (boltzmannWeight_pos 2 N P (circleSpacing L N) mass ω))
      simp_rw [hbw_simp]
      -- Goal: Integrable (fun ω => (ω g)^2 * bw ω) μ_GFF
      -- Step 3: Gaussian integrability of (ω g)²
      have h_sq_int : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
          (ω g) ^ 2) μ_GFF :=
        (pairing_memLp (latticeCovariance 2 N (circleSpacing L N) mass
          (circleSpacing_pos L N) hmass) g 2).integrable_sq
      -- Step 4: Dominate (ω g)² * bw ω by (ω g)² * exp(B)
      apply (h_sq_int.mul_const (Real.exp B)).mono
      · exact ((configuration_eval_measurable g).pow_const 2).aestronglyMeasurable.mul
          (Measurable.aestronglyMeasurable
            (interactionFunctional_measurable 2 N P (circleSpacing L N) mass).neg.exp)
      · exact Filter.Eventually.of_forall fun ω => by
          simp only [Real.norm_eq_abs]
          have h1 : 0 ≤ (ω g) ^ 2 := sq_nonneg _
          have h2 : 0 < bw ω :=
            boltzmannWeight_pos 2 N P (circleSpacing L N) mass ω
          have h3 : bw ω ≤ Real.exp B := by
            change Real.exp (-interactionFunctional 2 N P (circleSpacing L N) mass ω)
              ≤ Real.exp B
            exact Real.exp_le_exp_of_le (by linarith [hB ω])
          rw [abs_of_nonneg (mul_nonneg h1 (le_of_lt h2)),
              abs_of_nonneg (mul_nonneg h1 (le_of_lt (Real.exp_pos B)))]
          exact mul_le_mul_of_nonneg_left h3 h1)
    (fun f => by
      obtain ⟨C, _, hC_bound⟩ := torus_interacting_second_moment_uniform L P mass hmass f
      exact ⟨C, fun ⟨N, hN⟩ => by haveI : NeZero N := ⟨by omega⟩; exact hC_bound N⟩)
    ε hε
  exact ⟨K, hK_compact, fun N inst => hK_bound ⟨N, Nat.pos_of_ne_zero (NeZero.ne N)⟩⟩

/-! ## Existence of the interacting continuum limit -/

/-- **Existence of the torus P(φ)₂ continuum limit.**

For N → ∞, the torus-embedded interacting measures have a weakly
convergent subsequence. The limit is a probability measure on
Configuration(TorusTestFunction L).

**This theorem is PROVED**, not axiomatized. The proof uses:
1. Interacting tightness (`torus_interacting_tightness` — proved from Nelson's estimate)
2. Polish space (`configuration_torus_polish`)
3. Prokhorov's theorem (`prokhorov_sequential` — already proved) -/
theorem torusInteractingLimit_exists
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (φ : ℕ → ℕ) (μ : Measure (Configuration (TorusTestFunction L))),
      StrictMono φ ∧
      IsProbabilityMeasure μ ∧
      ∀ (f : Configuration (TorusTestFunction L) → ℝ),
        Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun n => ∫ ω, f ω ∂(torusInteractingMeasure L (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, f ω ∂μ)) := by
  let ν : ℕ → Measure (Configuration (TorusTestFunction L)) :=
    fun n => torusInteractingMeasure L (n + 1) P mass hmass
  haveI : PolishSpace (Configuration (TorusTestFunction L)) :=
    configuration_torus_polish L
  haveI : BorelSpace (Configuration (TorusTestFunction L)) :=
    configuration_torus_borelSpace L
  exact prokhorov_sequential ν
    (fun n => torusInteractingMeasure_isProbability L (n + 1) P mass hmass)
    (fun ε hε => by
      obtain ⟨K, hK_compact, hK_bound⟩ :=
        torus_interacting_tightness L P mass hmass ε hε
      exact ⟨K, hK_compact, fun n => hK_bound (n + 1)⟩)

end Pphi2

end
