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
import Mathlib.Analysis.Convex.Integral

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

/-! ## Textbook axioms

These axioms replace the compound axioms `exponential_moment_bound` and
`interactionFunctional_mean_nonpos` with cleaner, elementary statements. -/

/-- **Hermite orthogonality for the lattice Gaussian measure.**

Wick monomials `:x^n:_c` of order n ≥ 1 have zero mean under the Gaussian
measure with matching variance parameter c = wickConstant. This combines:
1. The variance of `ω(δ_x)` under `μ_{GFF}` equals `wickConstant`
   (the diagonal of the lattice Green's function)
2. Hermite polynomial orthogonality: `∫ He_n(t/√c) dN(0,c)(t) = 0` for n ≥ 1

Also states integrability, which holds because all Gaussian moments are finite
(polynomial of a Gaussian random variable).

Reference: Simon (1974), §I.3; Glimm-Jaffe (1987), §1.3. -/
axiom wickMonomial_latticeGaussian (d N : ℕ) [NeZero N]
    (n : ℕ) (hn : 1 ≤ n) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (x : FinLatticeSites d N) :
    Integrable (fun ω : Configuration (FinLatticeField d N) =>
        wickMonomial n (wickConstant d N a mass) (ω (finLatticeDelta d N x)))
      (latticeGaussianMeasure d N a mass ha hmass) ∧
    ∫ ω, wickMonomial n (wickConstant d N a mass) (ω (finLatticeDelta d N x))
      ∂(latticeGaussianMeasure d N a mass ha hmass) = 0

/-- **Uniform lower bound on the Wick polynomial.**

For any even-degree polynomial P with positive leading coefficient and any
bound C on the variance parameter c, the Wick polynomial `:P(x):_c` is
bounded below uniformly over c ∈ [0, C] and x ∈ ℝ.

The bound holds because the leading term `(1/n)x^n` (independent of c)
dominates for large |x|, and on bounded |x| the polynomial is continuous
with coefficients varying continuously in c.

Reference: Elementary real analysis (even-degree monic polynomial). -/
axiom wickPolynomial_uniform_bounded_below
    (P : InteractionPolynomial) (C : ℝ) (hC : 0 ≤ C) :
    ∃ A : ℝ, 0 < A ∧ ∀ (c : ℝ), 0 ≤ c → c ≤ C → ∀ x : ℝ,
    wickPolynomial P c x ≥ -A

/-! ## Step A2: Exponential moment bound for the interaction -/

/-- **Exponential moment bound** for the Wick-ordered interaction.

The Boltzmann weight exp(-V_a) has uniformly bounded L² norm w.r.t. the
Gaussian free field measure:

  ∫ exp(-2·V_a(φ)) dμ_{GFF}(φ) ≤ K

for all a ∈ (0, 1], where K depends on the polynomial P and mass m
but not on a.

Proof: On a fixed lattice (d, N fixed), the wickConstant ≤ mass⁻², so
by `wickPolynomial_uniform_bounded_below`, V_a(ω) ≥ -(a^d · |Λ| · A).
For a ≤ 1, exp(-2V) ≤ exp(2 · |Λ| · A). Integrating over the probability
measure gives K = exp(2 · |Λ| · A).

Note: In the full continuum limit (N ~ 1/a → ∞), this simple argument
fails and one needs cluster expansions (Simon §V.1, Glimm-Jaffe §19.1).
For fixed (d, N), the bound is elementary. -/
theorem exponential_moment_bound (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ (K : ℝ), 0 < K ∧
    ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
    ∫ ω : Configuration (FinLatticeField d N),
        (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2
        ∂(latticeGaussianMeasure d N a mass ha hmass) ≤ K := by
  -- Step 1: Get uniform lower bound on wickPolynomial for c ∈ [0, mass⁻²]
  obtain ⟨A, hA_pos, hA_bound⟩ :=
    wickPolynomial_uniform_bounded_below P (mass⁻¹ ^ 2) (by positivity)
  -- Step 2: K = exp(2 · |Λ| · A) works uniformly
  set Λ := Fintype.card (FinLatticeSites d N)
  refine ⟨Real.exp (2 * ↑Λ * A), Real.exp_pos _, fun a ha ha1 => ?_⟩
  set μ := latticeGaussianMeasure d N a mass ha hmass
  haveI : IsProbabilityMeasure μ := latticeGaussianMeasure_isProbability d N a mass ha hmass
  -- Step 3: V(ω) ≥ -(a^d · |Λ| · A) for all ω
  have hc_nn : 0 ≤ wickConstant d N a mass :=
    le_of_lt (wickConstant_pos d N a mass ha hmass)
  have hc_le : wickConstant d N a mass ≤ mass⁻¹ ^ 2 :=
    wickConstant_le_inv_mass_sq d N a mass ha hmass
  have h_wp_bound : ∀ (ω : Configuration (FinLatticeField d N)),
      interactionFunctional d N P a mass ω ≥ -(↑Λ * A) := by
    intro ω
    unfold interactionFunctional
    have ha_pow : (0 : ℝ) ≤ a ^ d := pow_nonneg (le_of_lt ha) d
    calc a ^ d * ∑ x : FinLatticeSites d N,
          wickPolynomial P (wickConstant d N a mass) (ω (finLatticeDelta d N x))
        ≥ a ^ d * ∑ _x : FinLatticeSites d N, (-A) := by
          apply mul_le_mul_of_nonneg_left _ ha_pow
          exact Finset.sum_le_sum fun x _ => hA_bound _ hc_nn hc_le _
      _ = a ^ d * (-(↑Λ * A)) := by
          congr 1; rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
      _ ≥ -(↑Λ * A) := by
          have had : a ^ d ≤ 1 := pow_le_one₀ (le_of_lt ha) ha1
          nlinarith [mul_nonneg (Nat.cast_nonneg' Λ) (le_of_lt hA_pos)]
  -- Step 4: exp(-2V) ≤ exp(2 · |Λ| · A) pointwise
  have h_exp_bound : ∀ ω, (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2 ≤
      Real.exp (2 * ↑Λ * A) := by
    intro ω
    -- (exp x)^2 = exp(2x)
    rw [sq, ← Real.exp_add, show -interactionFunctional d N P a mass ω +
        (-interactionFunctional d N P a mass ω) =
        -2 * interactionFunctional d N P a mass ω from by ring]
    exact Real.exp_le_exp_of_le (by linarith [h_wp_bound ω])
  -- Step 5: Integrate the pointwise bound
  calc ∫ ω, (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2 ∂μ
      ≤ ∫ _ω, Real.exp (2 * ↑Λ * A) ∂μ := by
        apply integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _)
          (integrable_const _) (ae_of_all _ h_exp_bound)
    _ = Real.exp (2 * ↑Λ * A) := by
        simp [integral_const]

/-! ## Step A3: Cauchy-Schwarz density transfer -/

/-- Helper: integrability and integral computation for a single-site
Wick polynomial under the lattice Gaussian.

`∫ :P(ω(δ_x)):_c dμ_{GFF} = P.coeff₀` because all Wick monomials of
order ≥ 1 have zero Gaussian mean, and `:x^0:_c = 1`. -/
private lemma wickPolynomial_integral_eq_coeff_zero
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (x : FinLatticeSites d N) :
    Integrable (fun ω : Configuration (FinLatticeField d N) =>
        wickPolynomial P (wickConstant d N a mass) (ω (finLatticeDelta d N x)))
      (latticeGaussianMeasure d N a mass ha hmass) ∧
    ∫ ω, wickPolynomial P (wickConstant d N a mass) (ω (finLatticeDelta d N x))
      ∂(latticeGaussianMeasure d N a mass ha hmass) = P.coeff ⟨0, by have := P.hn_ge; omega⟩ := by
  set μ := latticeGaussianMeasure d N a mass ha hmass
  set c := wickConstant d N a mass
  set δx := finLatticeDelta d N x
  haveI : IsProbabilityMeasure μ := latticeGaussianMeasure_isProbability d N a mass ha hmass
  -- Integrability of each term
  have h_lead_int : Integrable (fun ω : Configuration (FinLatticeField d N) =>
      (1 / P.n : ℝ) * wickMonomial P.n c (ω δx)) μ :=
    (wickMonomial_latticeGaussian d N P.n (by have := P.hn_ge; omega)
      a mass ha hmass x).1.const_mul _
  have h_term_int : ∀ m : Fin P.n, Integrable (fun ω : Configuration (FinLatticeField d N) =>
      P.coeff m * wickMonomial (m : ℕ) c (ω δx)) μ := by
    intro m
    by_cases hm : (m : ℕ) = 0
    · have : (fun ω : Configuration (FinLatticeField d N) =>
          P.coeff m * wickMonomial (m : ℕ) c (ω δx)) = fun _ => P.coeff m := by
        ext ω; simp [hm]
      rw [this]; exact integrable_const _
    · exact ((wickMonomial_latticeGaussian d N m (by omega) a mass ha hmass x).1).const_mul _
  have h_sum_int : Integrable (fun ω : Configuration (FinLatticeField d N) =>
      ∑ m : Fin P.n, P.coeff m * wickMonomial (m : ℕ) c (ω δx)) μ :=
    integrable_finset_sum _ fun m _ => h_term_int m
  constructor
  · -- Integrability of wickPolynomial = leading + sum
    show Integrable (fun ω => (1 / P.n : ℝ) * wickMonomial P.n c (ω δx) +
      ∑ m : Fin P.n, P.coeff m * wickMonomial (m : ℕ) c (ω δx)) μ
    exact h_lead_int.add h_sum_int
  · -- Integral = P.coeff 0
    show ∫ ω, ((1 / P.n : ℝ) * wickMonomial P.n c (ω δx) +
      ∑ m : Fin P.n, P.coeff m * wickMonomial (m : ℕ) c (ω δx)) ∂μ = _
    rw [integral_add h_lead_int h_sum_int,
        integral_const_mul,
        (wickMonomial_latticeGaussian d N P.n (by have := P.hn_ge; omega)
          a mass ha hmass x).2,
        mul_zero, zero_add,
        integral_finset_sum _ (fun m _ => h_term_int m)]
    simp_rw [integral_const_mul]
    -- Each integral: ∫ wM_m = 1 if m=0, 0 if m≥1
    have h_wm_eval : ∀ m : Fin P.n,
        ∫ ω, wickMonomial (↑m) c (ω δx) ∂μ = if (m : ℕ) = 0 then 1 else 0 := by
      intro m
      by_cases hm : (m : ℕ) = 0
      · simp_rw [if_pos hm, hm, wickMonomial_zero]
        simp [integral_const]
      · rw [if_neg hm, (wickMonomial_latticeGaussian d N m (by omega) a mass ha hmass x).2]
    simp_rw [h_wm_eval, mul_ite, mul_one, mul_zero]
    -- ∑ (if m.val = 0 then coeff m else 0) = coeff ⟨0, _⟩
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    -- The filter picks out exactly ⟨0, _⟩
    have : Finset.univ.filter (fun m : Fin P.n => (m : ℕ) = 0) =
        {⟨0, by have := P.hn_ge; omega⟩} := by
      ext m; simp [Fin.ext_iff]
    rw [this, Finset.sum_singleton]

/-- **Wick ordering mean property**: the mean of the interaction functional
under the GFF is nonpositive.

`∫ V dμ_{GFF} = a^d · |Λ| · P.coeff₀ ≤ 0` since `P.coeff₀ ≤ 0`.

Proved from `wickMonomial_latticeGaussian` (Hermite orthogonality),
`wickMonomial 0 c x = 1`, and `P.coeff_zero_nonpos`.

Reference: Simon (1974), §I.3; Glimm-Jaffe (1987), §1.3. -/
theorem interactionFunctional_mean_nonpos (d N : ℕ) [NeZero N]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Integrable (interactionFunctional d N P a mass)
      (latticeGaussianMeasure d N a mass ha hmass) ∧
    ∫ ω, interactionFunctional d N P a mass ω
      ∂(latticeGaussianMeasure d N a mass ha hmass) ≤ 0 := by
  set μ := latticeGaussianMeasure d N a mass ha hmass
  haveI : IsProbabilityMeasure μ := latticeGaussianMeasure_isProbability d N a mass ha hmass
  -- Get per-site integrability and integral from helper
  have h_site : ∀ x : FinLatticeSites d N,
      Integrable (fun ω : Configuration (FinLatticeField d N) =>
        wickPolynomial P (wickConstant d N a mass) (ω (finLatticeDelta d N x))) μ ∧
      ∫ ω, wickPolynomial P (wickConstant d N a mass) (ω (finLatticeDelta d N x)) ∂μ =
        P.coeff ⟨0, by have := P.hn_ge; omega⟩ :=
    fun x => wickPolynomial_integral_eq_coeff_zero d N P a mass ha hmass x
  set c := wickConstant d N a mass
  -- Integrability of each site term
  have h_wp_int : ∀ x : FinLatticeSites d N,
      Integrable (fun ω : Configuration (FinLatticeField d N) =>
        wickPolynomial P c (ω (finLatticeDelta d N x))) μ := fun x => (h_site x).1
  constructor
  · -- Integrability of V = a^d * Σ_x wP(ω(δ_x))
    unfold interactionFunctional
    exact (integrable_finset_sum _ fun x _ => h_wp_int x).const_mul _
  · -- Mean ≤ 0: ∫ V = a^d * |Λ| * P.coeff 0 ≤ 0
    unfold interactionFunctional
    rw [integral_const_mul, integral_finset_sum _ (fun x _ => h_wp_int x)]
    simp_rw [(h_site _).2, Finset.sum_const, nsmul_eq_mul]
    apply mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (le_of_lt ha) d)
    exact mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast Fintype.card_pos.le)
      P.coeff_zero_nonpos

/-- **Partition function lower bound**: Z_a ≥ 1 for all a.

Proved from Jensen's inequality (`ConvexOn.map_integral_le`) applied to
the convex function `exp` and `f = -V`:

  Z = ∫ exp(-V) dμ_{GFF} ≥ exp(-∫ V dμ_{GFF}) ≥ exp(0) = 1

The second inequality uses `interactionFunctional_mean_nonpos`. -/
private theorem partitionFunction_ge_one (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) (a : ℝ) (ha : 0 < a) :
    1 ≤ partitionFunction d N P a mass ha hmass := by
  set μ := latticeGaussianMeasure d N a mass ha hmass
  set V := interactionFunctional d N P a mass
  haveI : IsProbabilityMeasure μ := latticeGaussianMeasure_isProbability d N a mass ha hmass
  obtain ⟨hV_int, hV_mean⟩ := interactionFunctional_mean_nonpos d N P a mass ha hmass
  -- Jensen's inequality: exp(∫ -V dμ) ≤ ∫ exp(-V) dμ = Z
  have h_jensen : Real.exp (∫ ω, (-V ω) ∂μ) ≤ ∫ ω, Real.exp (-V ω) ∂μ := by
    have h_conv := convexOn_exp
    have h_cont := Real.continuous_exp.continuousOn (s := Set.univ)
    have h_closed := isClosed_univ (X := ℝ)
    have h_mem : ∀ᵐ ω ∂μ, (-V ω) ∈ Set.univ := ae_of_all _ (fun _ => Set.mem_univ _)
    have h_neg_int : Integrable (fun ω => -V ω) μ := hV_int.neg
    have h_exp_int : Integrable (fun ω => Real.exp (-V ω)) μ :=
      boltzmannWeight_integrable d N P a mass ha hmass
    exact h_conv.map_integral_le h_cont h_closed h_mem h_neg_int h_exp_int
  -- ∫ -V dμ = -(∫ V dμ) ≥ 0
  have h_neg_mean : 0 ≤ ∫ ω, (-V ω) ∂μ := by
    rw [integral_neg]; linarith
  -- Chain: 1 = exp(0) ≤ exp(∫ -V) ≤ Z
  calc (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
    _ ≤ Real.exp (∫ ω, (-V ω) ∂μ) := Real.exp_le_exp_of_le h_neg_mean
    _ ≤ ∫ ω, Real.exp (-V ω) ∂μ := h_jensen
    _ = partitionFunction d N P a mass ha hmass := rfl

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
