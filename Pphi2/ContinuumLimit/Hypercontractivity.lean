/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nelson's Hypercontractive Estimate for the Interacting Measure

Bounds the L^p moments of the interacting measure μ_a in terms of the
free Gaussian measure μ_{GFF}:

  ∫ |ω(f)|^{pn} dμ_a ≤ C · (2p-1)^{pn/2} · (∫ |ω(f)|^{2n} dμ_{GFF})^{p/2}

The RHS is evaluated against the FREE Gaussian measure, not the interacting
measure. This is mathematically essential: the reverse transfer (from μ_{GFF}
to μ_a) would require bounding ∫ e^{+V_a} dμ_{GFF}, which diverges because
V_a ~ φ⁴ grows faster than the Gaussian e^{-φ²} suppression.

Two proof paths are provided, both decomposed into textbook axioms.

## Option A: Cauchy-Schwarz Density Transfer (3 axioms → interacting_moment_bound)

The interacting measure dμ_a = (1/Z_a) exp(-V_a) dμ_{GFF,a} is absolutely
continuous w.r.t. the Gaussian free field. The proof:

1. **Gaussian hypercontractivity** — Already proved in gaussian-field for
   the abstract Gaussian measure. Here we state the consequence for the
   lattice GFF in the continuum-embedded form.

2. **Exponential moment bound** — ∫ exp(-2V_a) dμ_{GFF} ≤ K uniformly
   in a. This is the key analytic input (Nelson's estimate / Simon §V).
   Note: only the NEGATIVE exponential exp(-sV_a) is bounded; the positive
   exponential exp(+V_a) diverges because V_a ~ φ⁴.

3. **Cauchy-Schwarz density transfer** — Cauchy-Schwarz on the density
   e^{-V_a}/Z_a gives:
     ∫ F dμ_a = (1/Z_a) ∫ F·e^{-V_a} dμ_{GFF}
              ≤ (1/Z_a)·(∫ F² dμ_{GFF})^{1/2}·(∫ e^{-2V_a} dμ_{GFF})^{1/2}
   Combined with Gaussian hypercontractivity for ∫ F² and the exponential
   moment bound, this gives the interacting moment bound with RHS in terms
   of μ_{GFF}.

Note: An earlier version used Holley-Stroock perturbation, but that requires
bounded oscillation of V_a, which is FALSE for P(φ)₂ (V_a grows like φ⁴).
A subsequent version stated the RHS in terms of the interacting measure μ_a,
but converting back from μ_{GFF} requires e^{+V_a} integrability, which fails.

## Option B: Full Gross-Rothaus-Simon framework (5 additional axioms)

Not required for the main theorem. Provides the full OU semigroup
infrastructure for extensions beyond Wick monomials.

## References

- Simon, *The P(φ)₂ Euclidean QFT*, §V (exponential moment estimates)
- Glimm-Jaffe, *Quantum Physics*, §19.4
- Nelson, "The free Markoff field," J. Funct. Anal. 12 (1973), 211–227
- Gross, "Logarithmic Sobolev inequalities," Amer. J. Math. 97 (1975), 1061–1083
-/

import Pphi2.ContinuumLimit.Embedding
import GaussianField.HypercontractiveNat

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

variable (d N : ℕ) [NeZero N]

/-! # Option A: Cauchy-Schwarz Density Transfer

This is the standard approach for P(φ)₂. The interacting measure μ_a is
absolutely continuous w.r.t. the Gaussian μ_{GFF}, so we can transfer
moment bounds via Cauchy-Schwarz on the density e^{-V_a}/Z_a, paying a
cost controlled by exponential moments of the interaction V_a. The key
point is that the RHS of the bound uses the FREE Gaussian measure, not
the interacting measure. -/

/-! ## Step A1: Gaussian hypercontractivity for the continuum-embedded measure

The Gaussian free field μ_{GFF} satisfies the hypercontractive inequality
for polynomial functionals. This is already proved in gaussian-field
(`gaussian_hypercontractive`). Here we state it in the continuum-embedded
form used by the rest of the proof. -/

/-- The lattice test function corresponding to a continuum test function f under
the embedding: `g_f(x) = a^d * f(physicalPosition x)`.

This is the element of `FinLatticeField d N` such that for any configuration
`ω ∈ Configuration (FinLatticeField d N)`, we have
  `(latticeEmbedLift ω)(f) = ω(g_f)`. -/
private def embeddedTestFunction (a : ℝ) (f : ContinuumTestFunction d) :
    FinLatticeField d N :=
  fun x => a ^ d * f (physicalPosition d N a x)

/-- Key identity: the continuum evaluation `(latticeEmbedLift ω)(f)` equals
`ω(g_f)` where `g_f` is the embedded test function.

This follows from linearity of ω: the embedding evaluates
`a^d * Σ_x ω(e_x) * f(a·x)` which equals `ω(Σ_x a^d * f(a·x) * e_x) = ω(g_f)`. -/
private theorem latticeEmbedLift_eval_eq (a : ℝ) (ha : 0 < a)
    (ω : Configuration (FinLatticeField d N)) (f : ContinuumTestFunction d) :
    (latticeEmbedLift d N a ha ω) f = ω (embeddedTestFunction d N a f) := by
  -- LHS: (latticeEmbedLift ω)(f) = a^d * Σ_x ω(Pi.single x 1) * f(pos x)
  -- RHS: ω(g_f) where g_f(y) = a^d * f(pos y)
  -- By linearity of ω: ω(g_f) = ω(Σ_x g_f(x) • e_x) = Σ_x g_f(x) * ω(e_x)
  -- Unfold definitions to get to raw sums
  unfold latticeEmbedLift embeddedTestFunction
  rw [latticeEmbed_eval]
  simp only [latticeEmbedEval, evalAtSite]
  -- Goal: a^d * Σ_x ω(e_x) * f(pos x) = ω(fun x => a^d * f(pos x))
  -- Decompose target function as sum of basis vectors
  have h_basis : (fun x : FinLatticeSites d N => a ^ d * f (physicalPosition d N a x)) =
      ∑ x : FinLatticeSites d N,
        (a ^ d * f (physicalPosition d N a x)) • Pi.single x (1 : ℝ) := by
    ext1 y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply, mul_ite, mul_one, mul_zero]
    classical
    rw [Finset.sum_eq_single y (fun x _ hxy => if_neg (Ne.symm hxy))
      (fun h => absurd (Finset.mem_univ y) h), if_pos rfl]
  rw [h_basis, map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Finset.mul_sum]
  congr 1; ext1 x; ring

/-- **Gaussian hypercontractivity** in continuum-embedded form.

For the continuum-embedded Gaussian measure (pushforward of μ_{GFF} under
the lattice embedding ι_a), Wick monomials satisfy:

  ∫ |ω(f)|^{pn} d(ι_a)_*μ_{GFF} ≤ (p-1)^{pn/2} · (∫ |ω(f)|^{2n} d(ι_a)_*μ_{GFF})^{p/2}

This follows from `gaussian_hypercontractive` in gaussian-field by
rewriting the pushforward integral back to the lattice Gaussian measure
via `integral_map`, then observing that `(latticeEmbedLift ω)(f) = ω(g_f)`
where `g_f` is the embedded test function, reducing to an instance of
the abstract Gaussian hypercontractive bound.

Reference: Gross (1975); gaussian-field/Hypercontractive.lean. -/
theorem gaussian_hypercontractivity_continuum
    (mass : ℝ) (hmass : 0 < mass)
    (n : ℕ) (p : ℝ) (hp : 2 ≤ p) (m : ℕ) (hm : 1 ≤ m) (hp_eq : p = 2 * ↑m)
    (f : ContinuumTestFunction d)
    (a : ℝ) (ha : 0 < a) (_ha1 : a ≤ 1) :
    ∫ ω : Configuration (ContinuumTestFunction d),
        |ω f| ^ (p * ↑n) ∂(Measure.map (latticeEmbedLift d N a ha)
          (latticeGaussianMeasure d N a mass ha hmass)) ≤
      (p - 1) ^ (p * ↑n / 2) *
      (∫ ω : Configuration (ContinuumTestFunction d),
        |ω f| ^ (2 * ↑n) ∂(Measure.map (latticeEmbedLift d N a ha)
          (latticeGaussianMeasure d N a mass ha hmass))) ^
      (p / 2) := by
  -- Step 1: Rewrite integrals using integral_map to pull back from S'(ℝ^d) to lattice
  set μ := latticeGaussianMeasure d N a mass ha hmass
  set ι := latticeEmbedLift d N a ha
  have hι : AEMeasurable ι μ := (latticeEmbedLift_measurable d N a ha).aemeasurable
  -- Measurability of the integrands (needed for integral_map)
  have hmeas_p : AEStronglyMeasurable (fun (ω : Configuration (ContinuumTestFunction d)) =>
      |ω f| ^ (p * ↑n)) (Measure.map ι μ) :=
    ((configuration_eval_measurable f).norm.pow_const _).aestronglyMeasurable
  have hmeas_2 : AEStronglyMeasurable (fun (ω : Configuration (ContinuumTestFunction d)) =>
      |ω f| ^ (2 * ↑n)) (Measure.map ι μ) :=
    ((configuration_eval_measurable f).norm.pow_const _).aestronglyMeasurable
  -- LHS: ∫ |ω f|^{pn} d(map ι μ) = ∫ |(ι ω) f|^{pn} dμ(ω)
  rw [integral_map hι hmeas_p, integral_map hι hmeas_2]
  -- Step 2: Use latticeEmbedLift_eval_eq to rewrite (ι ω) f = ω g_f
  set g_f := embeddedTestFunction d N a f
  have h_eval : ∀ ω : Configuration (FinLatticeField d N),
      (ι ω) f = ω g_f := fun ω => latticeEmbedLift_eval_eq d N a ha ω f
  simp_rw [h_eval]
  -- Step 3: Apply gaussian_hypercontractive from gaussian-field
  -- μ = GaussianField.measure (latticeCovariance d N a mass ha hmass)
  have h_μ : μ = measure (latticeCovariance d N a mass ha hmass) := rfl
  rw [h_μ]
  exact gaussian_hypercontractive (latticeCovariance d N a mass ha hmass) g_f n p hp m hm hp_eq

/-! ## Step A2: Exponential moment bound for the interaction -/

/-- **Exponential moment bound** for the Wick-ordered interaction.

The Boltzmann weight exp(-V_a) has uniformly bounded L² norm w.r.t. the
Gaussian free field measure:

  ∫ exp(-2·V_a(φ)) dμ_{GFF}(φ) ≤ K

for all a ∈ (0, 1], where K depends on the polynomial P and mass m
but not on a.

**Important:** Only the NEGATIVE exponential exp(-s·V_a) is bounded.
The positive exponential exp(+c·|V_a|) ≈ exp(+c·φ⁴) diverges when
integrated against the Gaussian measure, because V_a ~ φ⁴ grows faster
than the Gaussian e^{-φ²} suppression.

This is a deep stability estimate from the Glimm-Jaffe program. The uniform-
in-a bound requires cluster expansions and chessboard estimates because:
- The Wick constant c_a ~ (1/2π)log(1/a) diverges as a → 0
- The lower bound on V_a depends on c_a, hence on a
- The number of lattice sites |Λ| ~ 1/a² grows as a → 0
- So the naive bound V_a ≥ -B with B uniform is FALSE

Reference: Simon (1974), §V.1, Theorem V.1; Glimm-Jaffe (1987), §19.1,
Theorem 8.6.1. -/
axiom exponential_moment_bound (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ (K : ℝ), 0 < K ∧
    ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
    -- The Boltzmann weight exp(-V_a) has uniformly bounded L² norm
    -- w.r.t. the Gaussian measure. This is the key estimate.
    ∫ ω : Configuration (FinLatticeField d N),
        (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2
        ∂(latticeGaussianMeasure d N a mass ha hmass) ≤ K

/-! ## Step A3: Cauchy-Schwarz density transfer -/

/-- **Partition function lower bound**: Z_a ≥ 1 for all a.

This follows from Jensen's inequality applied to the convex function exp:

  Z = ∫ exp(-V) dμ_{GFF} ≥ exp(-∫ V dμ_{GFF}) = exp(0) = 1

The key fact is that E_{GFF}[V_a] = 0. This holds because the Wick-ordered
interaction :P(φ(x)):_c is a sum of Hermite polynomials H_{2k}(φ(x); c) of
degree ≥ 2, and by the defining property of Hermite polynomials:

  ∫ H_{2k}(t; c) dN(0,c)(t) = 0  for k ≥ 1

**Proof strategy**: By Mathlib's `ConvexOn.map_integral_le` (Jensen for probability
measures), `exp(∫ -V dμ) ≤ ∫ exp(-V) dμ = Z`. The Wick ordering property gives
`∫ V dμ_GFF = 0`, so `exp(0) = 1 ≤ Z`. The Wick ordering proof requires Hermite
polynomial orthogonality under Gaussian measures.

Reference: Simon (1974), §I.3; Glimm-Jaffe (1987), §1.3. -/
axiom partitionFunction_ge_one (d N : ℕ) [NeZero N] (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) (a : ℝ) (ha : 0 < a) :
    1 ≤ partitionFunction d N P a mass ha hmass

/-- **Cauchy-Schwarz density transfer bound**: any nonneg integrable function F
satisfies ∫ F dμ_int ≤ K^{1/2} · (∫ F² dμ_GFF)^{1/2}, where K is the
exponential moment bound.

This combines three facts:
1. Density transfer: ∫ F dμ_int = Z⁻¹ ∫ F·bw dμ_GFF
2. Cauchy-Schwarz:   ∫ F·bw ≤ (∫ F²)^{1/2} · (∫ bw²)^{1/2}
3. Z ≥ 1 and ∫ bw² ≤ K give Z⁻¹·(∫ bw²)^{1/2} ≤ K^{1/2} -/
private lemma density_transfer_bound
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (K : ℝ) (_hK_pos : 0 < K)
    (hK : ∫ ω : Configuration (FinLatticeField d N),
        (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2
        ∂(latticeGaussianMeasure d N a mass ha hmass) ≤ K)
    (hZ : 1 ≤ partitionFunction d N P a mass ha hmass)
    (F : Configuration (FinLatticeField d N) → ℝ)
    (hF_nn : ∀ ω, 0 ≤ F ω)
    (hF_meas : AEStronglyMeasurable F (latticeGaussianMeasure d N a mass ha hmass))
    (hF_sq_int : Integrable (fun ω => F ω ^ 2) (latticeGaussianMeasure d N a mass ha hmass)) :
    ∫ ω, F ω ∂(interactingLatticeMeasure d N P a mass ha hmass) ≤
    K ^ (1 / 2 : ℝ) *
    (∫ ω, F ω ^ (2 : ℝ) ∂(latticeGaussianMeasure d N a mass ha hmass)) ^ (1 / 2 : ℝ) := by
  set μ_GFF := latticeGaussianMeasure d N a mass ha hmass
  set bw := boltzmannWeight d N P a mass
  set V := interactionFunctional d N P a mass
  set Z := partitionFunction d N P a mass ha hmass
  have hZ_pos : 0 < Z := partitionFunction_pos d N P a mass ha hmass
  -- ENNReal infrastructure
  have hZ_ennreal_ne_zero : ENNReal.ofReal Z ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hZ_pos).ne'
  have hc_ne_zero : (ENNReal.ofReal Z)⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have hc_ne_top : (ENNReal.ofReal Z)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr hZ_ennreal_ne_zero
  -- Density measurability
  have hbw_meas : Measurable bw :=
    (interactionFunctional_measurable d N P a mass).neg.exp
  set bw_nn := fun ω : Configuration (FinLatticeField d N) => Real.toNNReal (bw ω)
  have hbw_nn_meas : Measurable bw_nn :=
    Measurable.real_toNNReal hbw_meas
  -- Step 1: Unfold interacting measure to weighted Gaussian integral
  -- ∫ F dμ_int = Z⁻¹ * ∫ bw * F dμ_GFF
  unfold interactingLatticeMeasure
  rw [integral_smul_measure]
  have wd_eq : ∫ ω, F ω ∂(μ_GFF.withDensity (fun ω => ENNReal.ofReal (bw ω))) =
      ∫ ω, bw ω * F ω ∂μ_GFF := by
    change ∫ ω, F ω ∂(μ_GFF.withDensity (fun ω => ↑(bw_nn ω))) =
      ∫ ω, bw ω * F ω ∂μ_GFF
    rw [integral_withDensity_eq_integral_smul hbw_nn_meas]
    congr 1; ext ω
    simp only [bw_nn, NNReal.smul_def, smul_eq_mul]
    rw [Real.coe_toNNReal _ (le_of_lt (boltzmannWeight_pos d N P a mass ω))]
  rw [wd_eq]
  have hc_real : ((ENNReal.ofReal Z)⁻¹).toReal = Z⁻¹ := by
    simp [ENNReal.toReal_inv, ENNReal.toReal_ofReal (le_of_lt hZ_pos)]
  rw [hc_real]
  -- Goal: Z⁻¹ * ∫ bw * F dμ_GFF ≤ K^{1/2} * (∫ F^2 dμ_GFF)^{1/2}
  -- Step 2: Cauchy-Schwarz + bounds
  -- ∫ bw*F ≤ (∫ bw²)^{1/2} * (∫ F²)^{1/2}   [CS]
  -- Z⁻¹ ≤ 1                                    [Z ≥ 1]
  -- (∫ bw²)^{1/2} ≤ K^{1/2}                   [exponential moment bound]
  -- Construct MemLp instances for Cauchy-Schwarz
  -- bw bounded above from interactionFunctional_bounded_below
  obtain ⟨B, hB⟩ := interactionFunctional_bounded_below d N P a mass ha hmass
  have hbw_bound : ∀ ω, bw ω ≤ Real.exp B := fun ω =>
    Real.exp_le_exp_of_le (by linarith [hB ω])
  haveI : IsProbabilityMeasure μ_GFF :=
    latticeGaussianMeasure_isProbability d N a mass ha hmass
  have hbw_sq_int : Integrable (fun ω => bw ω ^ 2) μ_GFF :=
    Integrable.of_bound (hbw_meas.pow_const 2).aestronglyMeasurable (Real.exp B ^ 2)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact sq_le_sq'
          (by linarith [boltzmannWeight_pos d N P a mass ω, Real.exp_pos B])
          (hbw_bound ω))
  have hbw_memLp : MemLp bw 2 μ_GFF :=
    (memLp_two_iff_integrable_sq hbw_meas.aestronglyMeasurable).mpr hbw_sq_int
  have hF_memLp : MemLp F 2 μ_GFF :=
    (memLp_two_iff_integrable_sq hF_meas).mpr hF_sq_int
  -- Apply Cauchy-Schwarz (Hölder with p = q = 2)
  -- integral_mul_le_Lp_mul_Lq_of_nonneg with HolderConjugate.two_two
  -- gives ∫ bw*F ≤ (∫ bw²)^{1/2} * (∫ F²)^{1/2}
  have h_cs : ∫ ω, bw ω * F ω ∂μ_GFF ≤
      (∫ ω, bw ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2 : ℝ) *
      (∫ ω, F ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2 : ℝ) := by
    -- Hölder/Cauchy-Schwarz with p = q = 2
    have h_ofReal : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by norm_num
    have hbw' : MemLp bw (ENNReal.ofReal 2) μ_GFF := h_ofReal ▸ hbw_memLp
    have hF' : MemLp F (ENNReal.ofReal 2) μ_GFF := h_ofReal ▸ hF_memLp
    exact integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (ae_of_all _ (fun ω => le_of_lt (boltzmannWeight_pos d N P a mass ω)))
      (ae_of_all _ hF_nn) hbw' hF'
  -- Chain: Z⁻¹ * ∫ bw*F ≤ Z⁻¹ * (∫ bw²)^{1/2} * (∫ F²)^{1/2}
  --                       ≤ 1 * K^{1/2} * (∫ F²)^{1/2}
  --                       = K^{1/2} * (∫ F²)^{1/2}
  have hZinv_le : Z⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hZ
  have hbw_sq_le : (∫ ω, bw ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2 : ℝ) ≤ K ^ (1/2 : ℝ) := by
    apply Real.rpow_le_rpow (integral_nonneg (fun ω =>
      Real.rpow_nonneg (le_of_lt (boltzmannWeight_pos d N P a mass ω)) _))
    · -- ∫ bw^{rpow 2} ≤ K: convert rpow to nat pow, then match by definition
      have : ∫ ω, bw ω ^ (2:ℝ) ∂μ_GFF = ∫ ω, (Real.exp (-V ω)) ^ 2 ∂μ_GFF := by
        congr 1; ext ω; exact Real.rpow_natCast _ 2
      linarith
    · linarith
  calc Z⁻¹ * ∫ ω, bw ω * F ω ∂μ_GFF
      ≤ Z⁻¹ * ((∫ ω, bw ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) * (∫ ω, F ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ)) :=
        mul_le_mul_of_nonneg_left h_cs (le_of_lt (inv_pos.mpr hZ_pos))
    _ ≤ 1 * (K ^ (1/2:ℝ) * (∫ ω, F ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ)) := by
        have hF_int_nn : 0 ≤ (∫ ω, F ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) :=
          Real.rpow_nonneg (integral_nonneg (fun ω =>
            Real.rpow_nonneg (hF_nn ω) _)) _
        have hbw_int_nn : 0 ≤ (∫ ω, bw ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) :=
          Real.rpow_nonneg (integral_nonneg (fun ω =>
            Real.rpow_nonneg (le_of_lt (boltzmannWeight_pos d N P a mass ω)) _)) _
        apply mul_le_mul hZinv_le _ (mul_nonneg hbw_int_nn hF_int_nn) (by linarith)
        exact mul_le_mul_of_nonneg_right hbw_sq_le hF_int_nn
    _ = K ^ (1/2:ℝ) * (∫ ω, F ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) := one_mul _

/-- **Interacting moment bound** via Cauchy-Schwarz density transfer.

Bounds the L^{pn} moment of the interacting measure μ_a in terms of the
FREE Gaussian measure μ_{GFF}:

  ∫ |ω(f)|^{pn} dμ_a ≤ C · (2p-1)^{pn/2} · (∫ |ω(f)|^{2n} dμ_{GFF})^{p/2}

where C = K^{1/2} is uniform in a, n, m, f and `p = 2m`.

Proof:
  ∫ |ω(f)|^{pn} dμ_a = (1/Z_a) ∫ |ω(f)|^{pn} · e^{-V_a} dμ_{GFF}
    ≤ (1/Z_a) · (∫ |ω(f)|^{2pn} dμ_{GFF})^{1/2} · (∫ e^{-2V_a} dμ_{GFF})^{1/2}
                                                                [Cauchy-Schwarz]
    ≤ (1/Z_a) · K^{1/2} · (∫ |ω(f)|^{2pn} dμ_{GFF})^{1/2}
                                                    [exponential_moment_bound]
    ≤ K^{1/2} · (2p-1)^{pn/2} · (∫ |ω(f)|^{2n} dμ_{GFF})^{p/2}
                                    [Z ≥ 1 + gaussian_hypercontractivity_continuum]

The RHS is in terms of μ_{GFF}, NOT μ_a. This is essential: converting the
RHS back to μ_a would require ∫ e^{+V_a} dμ_{GFF}, which diverges because
V_a ~ φ⁴ grows faster than the Gaussian suppression e^{-φ²}.

Reference: Simon (1974), §V.1; Glimm-Jaffe (1987), §19.4. -/
theorem interacting_moment_bound
    (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ (C : ℝ), 0 < C ∧
    ∀ (n : ℕ) (p : ℝ) (m : ℕ), 1 ≤ m → p = 2 * ↑m →
    ∀ (f : ContinuumTestFunction d) (a : ℝ) (ha : 0 < a), a ≤ 1 →
    ∫ ω : Configuration (ContinuumTestFunction d),
        |ω f| ^ (p * ↑n) ∂(continuumMeasure d N P a mass ha hmass) ≤
      C * (2 * p - 1) ^ (p * ↑n / 2) *
      (∫ ω : Configuration (ContinuumTestFunction d),
        |ω f| ^ (2 * ↑n) ∂(Measure.map (latticeEmbedLift d N a ha)
          (latticeGaussianMeasure d N a mass ha hmass))) ^
      (p / 2) := by
  -- Step A2: Get K from exponential_moment_bound
  obtain ⟨K, hK_pos, hK⟩ := exponential_moment_bound d N P mass hmass
  -- C = K^(1/2) works because Z ≥ 1 gives 1/Z ≤ 1
  refine ⟨K ^ (1 / 2 : ℝ), Real.rpow_pos_of_pos hK_pos _, ?_⟩
  intro n p m hm hp f a ha ha1
  -- Setup
  set μ_GFF := latticeGaussianMeasure d N a mass ha hmass
  set μ_int := interactingLatticeMeasure d N P a mass ha hmass
  set ι := latticeEmbedLift d N a ha
  set bw := boltzmannWeight d N P a mass
  set Z := partitionFunction d N P a mass ha hmass
  set g_f := embeddedTestFunction d N a f
  have hZ_pos : 0 < Z := partitionFunction_pos d N P a mass ha hmass
  have hZ_ge_one : 1 ≤ Z := partitionFunction_ge_one d N P mass hmass a ha
  have hι_meas : AEMeasurable ι μ_int :=
    (latticeEmbedLift_measurable d N a ha).aemeasurable
  have hι_meas_gauss : AEMeasurable ι μ_GFF :=
    (latticeEmbedLift_measurable d N a ha).aemeasurable
  have h_eval : ∀ ω : Configuration (FinLatticeField d N),
      (ι ω) f = ω g_f := fun ω => latticeEmbedLift_eval_eq d N a ha ω f
  -- Step 1: Pull back LHS through integral_map
  -- LHS = ∫ |ω f|^{pn} d(map ι μ_int) = ∫ |(ι ω) f|^{pn} dμ_int
  have hmeas_lhs : AEStronglyMeasurable (fun (ω : Configuration (ContinuumTestFunction d)) =>
      |ω f| ^ (p * ↑n)) (Measure.map ι μ_int) :=
    ((configuration_eval_measurable f).norm.pow_const _).aestronglyMeasurable
  -- The continuum measure is the pushforward of the interacting measure
  have h_cont_eq : continuumMeasure d N P a mass ha hmass = Measure.map ι μ_int := rfl
  rw [h_cont_eq, integral_map hι_meas hmeas_lhs]
  -- Rewrite using h_eval: |(ι ω) f| = |ω g_f|
  simp_rw [h_eval]
  -- Step 2: Apply density_transfer_bound
  -- F(ω) = |ω g_f|^{pn} is nonneg, measurable, and has finite Gaussian L² norm
  have hF_meas_gauss : AEStronglyMeasurable (fun ω : Configuration (FinLatticeField d N) =>
      |ω g_f| ^ (p * ↑n)) μ_GFF :=
    ((configuration_eval_measurable g_f).norm.pow_const _).aestronglyMeasurable
  have hF_sq_int : Integrable (fun ω : Configuration (FinLatticeField d N) =>
      (|ω g_f| ^ (p * ↑n)) ^ 2) μ_GFF := by
    -- All polynomial moments of Gaussian linear functionals are finite
    -- (pairing_memLp from gaussian-field: Gaussian pairings are in L^p for all p)
    have h_μ : μ_GFF = GaussianField.measure (latticeCovariance d N a mass ha hmass) := rfl
    haveI := latticeGaussianMeasure_isProbability d N a mass ha hmass
    have hp_nn : (0 : ℝ) ≤ p := by rw [hp]; positivity
    have h_nn : (0 : ℝ) ≤ 2 * p * ↑n :=
      mul_nonneg (mul_nonneg (by norm_num) hp_nn) (Nat.cast_nonneg _)
    have h_memLp := GaussianField.pairing_memLp
      (latticeCovariance d N a mass ha hmass) g_f ⟨2 * p * ↑n, h_nn⟩
    have h_int : Integrable (fun ω : Configuration (FinLatticeField d N) =>
        ‖ω g_f‖ ^ (2 * p * ↑n)) μ_GFF := by rw [h_μ]; exact h_memLp.integrable_norm_rpow'
    exact h_int.congr (ae_of_all _ fun ω => by
      change ‖ω g_f‖ ^ (2 * p * ↑n) = (|ω g_f| ^ (p * ↑n)) ^ 2
      rw [Real.norm_eq_abs, ← Real.rpow_natCast (|ω g_f| ^ (p * ↑n)) 2,
          ← Real.rpow_mul (abs_nonneg _)]; congr 1; ring)
  have h_dt := density_transfer_bound d N P a mass ha hmass K hK_pos
    (hK a ha ha1) hZ_ge_one (fun ω => |ω g_f| ^ (p * ↑n))
    (fun ω => Real.rpow_nonneg (abs_nonneg _) _) hF_meas_gauss hF_sq_int
  -- h_dt: ∫ |ω g_f|^{pn} dμ_int ≤ K^{1/2} * (∫ (|ω g_f|^{pn})^2 dμ_GFF)^{1/2}
  -- Step 3: Bound (∫ (|ω g_f|^{pn})^2 dμ_GFF)^{1/2} using hypercontractivity
  -- (|x|^a)^{(2:ℝ)} = |x|^{2a} by rpow_mul, so F² = |ω g_f|^{2pn}
  -- Convert to continuum integral, apply hypercontractivity with parameter 2p,
  -- then simplify exponents.
  have h2p_ge : 2 ≤ 2 * p := by
    rw [hp]; have : (1 : ℝ) ≤ ↑m := Nat.one_le_cast.mpr hm; nlinarith
  have h2m_ge : 1 ≤ 2 * m := by omega
  have h2p_eq : 2 * p = 2 * ↑(2 * m) := by rw [hp]; push_cast; ring
  -- Hypercontractivity for the Gaussian measure with parameter 2p
  have h_hyper := gaussian_hypercontractivity_continuum d N mass hmass n (2 * p) h2p_ge
    (2 * m) h2m_ge h2p_eq f a ha ha1
  -- h_hyper: ∫ |σ f|^{2p·n} d(map ι μ_GFF) ≤
  --   (2p-1)^{2p·n/2} * (∫ |σ f|^{2n} d(map ι μ_GFF))^{2p/2}
  -- Key: (|x|^{pn})^{2:ℝ} = |x|^{2*p*↑n} via rpow_mul
  have h_rpow_sq : ∀ ω : Configuration (FinLatticeField d N),
      (|ω g_f| ^ (p * ↑n)) ^ (2:ℝ) = |ω g_f| ^ (2 * p * ↑n) := fun ω => by
    rw [← Real.rpow_mul (abs_nonneg _)]; congr 1; ring
  -- Lattice ↔ continuum integral for 2pn exponent
  have h_int_map_2pn : ∫ σ, |σ f| ^ (2 * p * ↑n) ∂(Measure.map ι μ_GFF) =
      ∫ ω, |ω g_f| ^ (2 * p * ↑n) ∂μ_GFF := by
    simp only [← Real.norm_eq_abs]
    rw [integral_map hι_meas_gauss
        ((configuration_eval_measurable f).norm.pow_const _).aestronglyMeasurable]
    simp_rw [h_eval]
  -- F² integral = continuum 2pn integral
  have h_F2_eq : ∫ ω, (fun ω => |ω g_f| ^ (p * ↑n)) ω ^ (2:ℝ) ∂μ_GFF =
      ∫ σ, |σ f| ^ (2 * p * ↑n) ∂(Measure.map ι μ_GFF) := by
    trans ∫ ω, |ω g_f| ^ (2 * p * ↑n) ∂μ_GFF
    · congr 1; ext ω; exact h_rpow_sq ω
    · exact h_int_map_2pn.symm
  -- Nonneg helpers for rpow arithmetic
  have h_2pm1_nn : (0:ℝ) ≤ 2 * p - 1 := by linarith
  have h_I2_nn : (0 : ℝ) ≤ ∫ σ, |σ f| ^ (2 * ↑n) ∂(Measure.map ι μ_GFF) := by
    exact integral_nonneg fun σ => by positivity
  -- Bound (∫ F²)^{1/2} using h_hyper + rpow arithmetic
  have h_F2_bound : (∫ ω, (fun ω => |ω g_f| ^ (p * ↑n)) ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) ≤
      (2*p-1) ^ (p*↑n/2) * (∫ σ, |σ f| ^ (2*↑n) ∂(Measure.map ι μ_GFF)) ^ (p/2) := by
    rw [h_F2_eq]
    calc (∫ σ, |σ f| ^ (2*p*↑n) ∂(Measure.map ι μ_GFF)) ^ (1/2:ℝ)
        ≤ ((2*p-1) ^ (2*p*↑n/2) *
           (∫ σ, |σ f| ^ (2*↑n) ∂(Measure.map ι μ_GFF)) ^ (2*p/2)) ^ (1/2:ℝ) :=
          Real.rpow_le_rpow
            (integral_nonneg (fun σ => Real.rpow_nonneg (abs_nonneg _) _))
            h_hyper (by linarith)
      _ = (2*p-1) ^ (p*↑n/2) * (∫ σ, |σ f| ^ (2*↑n) ∂(Measure.map ι μ_GFF)) ^ (p/2) := by
          rw [Real.mul_rpow (Real.rpow_nonneg h_2pm1_nn _) (Real.rpow_nonneg h_I2_nn _)]
          congr 1
          · rw [← Real.rpow_mul h_2pm1_nn]; congr 1; ring
          · rw [← Real.rpow_mul h_I2_nn]; congr 1; ring
  -- Final chain: h_dt ≤ K^{1/2} * bound
  calc ∫ x, |x g_f| ^ (p * ↑n) ∂μ_int
      ≤ K ^ (1/2:ℝ) * (∫ ω, (fun ω => |ω g_f| ^ (p * ↑n)) ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) :=
        h_dt
    _ ≤ K ^ (1/2:ℝ) * ((2*p-1) ^ (p*↑n/2) *
         (∫ σ, |σ f| ^ (2*↑n) ∂(Measure.map ι μ_GFF)) ^ (p/2)) :=
        mul_le_mul_of_nonneg_left h_F2_bound (Real.rpow_nonneg (le_of_lt hK_pos) _)
    _ = K ^ (1/2:ℝ) * (2*p-1) ^ (p*↑n/2) *
         (∫ ω, |ω f| ^ (2*↑n) ∂(Measure.map ι μ_GFF)) ^ (p/2) :=
        (mul_assoc _ _ _).symm

end Pphi2

end
