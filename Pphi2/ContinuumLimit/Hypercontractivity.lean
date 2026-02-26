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
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
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

/-- **Interacting moment bound** via Cauchy-Schwarz density transfer.

Bounds the L^{pn} moment of the interacting measure μ_a in terms of the
FREE Gaussian measure μ_{GFF}:

  ∫ |ω(f)|^{pn} dμ_a ≤ C · (2p-1)^{pn/2} · (∫ |ω(f)|^{2n} dμ_{GFF})^{p/2}

where C = K^{1/2}/Z_min is uniform in a, n, m, f and `p = 2m`.

Proof:
  ∫ |ω(f)|^{pn} dμ_a = (1/Z_a) ∫ |ω(f)|^{pn} · e^{-V_a} dμ_{GFF}
    ≤ (1/Z_a) · (∫ |ω(f)|^{2pn} dμ_{GFF})^{1/2} · (∫ e^{-2V_a} dμ_{GFF})^{1/2}
                                                                [Cauchy-Schwarz]
    ≤ (K^{1/2}/Z_a) · (∫ |ω(f)|^{2pn} dμ_{GFF})^{1/2}
                                                    [exponential_moment_bound]
    ≤ (K^{1/2}/Z_a) · (2p-1)^{pn/2} · (∫ |ω(f)|^{2n} dμ_{GFF})^{p/2}
                                          [gaussian_hypercontractivity_continuum]

The RHS is in terms of μ_{GFF}, NOT μ_a. This is essential: converting the
RHS back to μ_a would require ∫ e^{+V_a} dμ_{GFF}, which diverges because
V_a ~ φ⁴ grows faster than the Gaussian suppression e^{-φ²}.

For proving tightness (Prokhorov), we only need the moments to be uniformly
bounded in a. The Gaussian L^{2n} norm on the RHS equals the lattice
Green's function ⟨f, G_a f⟩ (for n=1), which is trivially bounded uniformly
in a since G_a → G in operator norm.

Reference: Simon (1974), §V.1; Glimm-Jaffe (1987), §19.4. -/
axiom interacting_moment_bound
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
      (p / 2)

end Pphi2

end
