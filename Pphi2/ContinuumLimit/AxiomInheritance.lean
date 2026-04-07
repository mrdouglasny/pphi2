/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michael R. Douglas

# OS Axioms Pass to the Continuum Limit

Shows that OS axioms verified on the lattice transfer to the continuum
limit measure μ = lim ν_{aₙ}.

## Main results

- `os0_inheritance` — analyticity from uniform exponential bounds
- `os1_inheritance` — regularity from uniform moment bounds
- `os3_inheritance` — RP from weak closure (provable)
- `os4_inheritance` — clustering from uniform mass gap

## Mathematical background

Each OS axiom transfers to the limit by a different mechanism:

### OS0 (Analyticity)
The generating functional `Z[f] = ∫ exp(iΦ(f)) dμ` is entire analytic.
On the lattice, Z_a[f] is entire with uniform bounds on derivatives.
Uniform bounds + pointwise convergence → limit is entire
(by Vitali's convergence theorem for analytic functions).

### OS1 (Regularity)
The bound `|Z[f]| ≤ exp(c‖f‖²)` holds uniformly on the lattice
(from the Gaussian covariance structure). Pointwise limits of
uniformly bounded functions preserve the bound.

### OS3 (Reflection Positivity)
RP is a nonnegativity condition `Σ cᵢc̄ⱼ Z[fᵢ - Θfⱼ] ≥ 0`.
Since each Z_a satisfies this and Z_a → Z pointwise, the limit
inherits the nonnegativity. (Proved in OS3_RP_Inheritance.lean.)

### OS4 (Clustering)
The uniform mass gap `m_phys ≥ m₀ > 0` (from `spectral_gap_uniform`)
gives uniform exponential clustering on the lattice. Weak convergence
preserves the exponential bound.

### OS2 (Euclidean Invariance) — handled in Phase 5
This is the hardest axiom. The lattice breaks E(2) symmetry, and its
restoration requires the Ward identity argument (see OS2_WardIdentity.lean).

## References

- Glimm-Jaffe, *Quantum Physics*, §19.4
- Simon, *The P(φ)₂ Euclidean QFT*, §V
-/

import Pphi2.ContinuumLimit.CharacteristicFunctional
import Pphi2.ContinuumLimit.Convergence
import Pphi2.GaussianContinuumLimit.PropagatorConvergence
import Pphi2.OSProofs.OS3_RP_Inheritance
import Pphi2.OSProofs.OS4_MassGap
import Pphi2.ContinuumLimit.TimeReflection

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

variable (d N : ℕ) [NeZero N]

/-! ## OS1: Regularity -/

/-- **OS1 transfers to the continuum limit.**

The regularity bound `|Z[f]| ≤ exp(c · ‖f‖²_{H^{-1}})` holds for
the continuum limit.

Proof outline:
1. On the lattice: `|Z_a[f]| ≤ 1` trivially for real f (|exp(it)| = 1).
2. The nontrivial bound on moments:
   `∫ |Φ_a(f)|^{2n} dν_a ≤ (2n)! · C^n · ‖f‖^{2n}_{H^{-1}}`
   holds uniformly in a (from the Gaussian structure + Nelson's estimate).
3. These moment bounds transfer to the limit. -/
theorem os1_inheritance (_P : InteractionPolynomial)
    (_mass : ℝ) (_hmass : 0 < _mass)
    (μ : Measure (Configuration (ContinuumTestFunction d)))
    (hμ : IsProbabilityMeasure μ) :
    -- |Z[f]| ≤ 1 for all real test functions f
    ∀ (f : ContinuumTestFunction d),
    |∫ ω : Configuration (ContinuumTestFunction d),
      Real.cos (ω f) ∂μ| ≤ 1 := by
  intro f
  have h1 : |∫ ω, Real.cos (ω f) ∂μ| ≤ ∫ ω, |Real.cos (ω f)| ∂μ := by
    rw [show |∫ ω, Real.cos (ω f) ∂μ| = ‖∫ ω, Real.cos (ω f) ∂μ‖ from
      (Real.norm_eq_abs _).symm]
    exact norm_integral_le_integral_norm _
  have h2 : ∫ ω, |Real.cos (ω f)| ∂μ ≤ ∫ _ω, (1 : ℝ) ∂μ := by
    apply integral_mono_of_nonneg
    · exact ae_of_all μ (fun ω => abs_nonneg _)
    · exact integrable_const 1
    · exact ae_of_all μ (fun ω => Real.abs_cos_le_one _)
  simp at h2
  linarith

/-- **Continuum-limit exponential moment bound in Green-form.**

The continuum-limit measure satisfies the textbook Simon/Nelson estimate

`∫ exp(|⟨ω, f⟩|) dμ(ω) ≤ exp(c₁ · ‖f‖₁ + c₂ · G(f,f))`,

where `G` is the continuum Green quadratic form. This is the single
substantive continuum-limit input from which both the all-`c` exponential
moment integrability used in OS0 and the Schwartz-norm bound used in OS1 are
derived downstream.

Reference: Simon, *The P(φ)₂ Euclidean QFT*, §V.2; Nelson (1973). -/
axiom continuum_exponential_moment_green_bound (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (h_limit : IsPphi2Limit μ P mass) :
    ∃ (c₁ c₂ : ℝ), 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (f : TestFunction2),
        Integrable (fun ω : FieldConfig2 => Real.exp (|ω f|)) μ ∧
        ∫ ω : FieldConfig2, Real.exp (|ω f|) ∂μ ≤
          Real.exp
            (c₁ * (∫ x, ‖f x‖ ∂volume) +
              c₂ * continuumGreenBilinear 2 mass f f)

/-- **Exponential moments of the continuum limit** for all positive scales.

This follows from `continuum_exponential_moment_green_bound` by scaling the
test function `f ↦ c • f`. -/
theorem continuum_exponential_moments (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (h_limit : IsPphi2Limit μ P mass)
    (f : TestFunction2) :
    ∀ (c : ℝ), 0 < c →
    Integrable (fun ω : FieldConfig2 => Real.exp (c * |ω f|)) μ := by
  intro c hc
  obtain ⟨c₁, c₂, hc₁, hc₂, hbound⟩ :=
    continuum_exponential_moment_green_bound P mass hmass μ h_limit
  refine (hbound (c • f)).1.congr ?_
  exact ae_of_all μ fun ω => by
    simp [map_smul, smul_eq_mul, abs_mul, abs_of_pos hc]

/-- **Exponential moment bound via Schwartz norms.**

The exponential moment `∫ exp(|ω(g)|) dμ` is bounded by
`exp(c · (‖g‖₁ + ‖g‖₂²))` for some universal constant `c > 0`.

This combines `continuum_exponential_moment_green_bound` with the deterministic
estimate `continuumGreenBilinear_le_mass_inv_sq`. -/
theorem exponential_moment_schwartz_bound
    (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (h_limit : IsPphi2Limit μ P mass) :
    ∃ (c : ℝ), 0 < c ∧ ∀ (g : TestFunction2),
      ∫ ω : FieldConfig2, Real.exp (|ω g|) ∂μ ≤
        Real.exp (c * (∫ x, ‖g x‖ ∂volume + ∫ x, ‖g x‖ ^ (2 : ℝ) ∂volume)) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hbound⟩ :=
    continuum_exponential_moment_green_bound P mass hmass μ h_limit
  let Cmass : ℝ := (2 * Real.pi) ^ (-(2 : ℤ)) * (mass ^ 2)⁻¹
  have hCmass_nonneg : 0 ≤ Cmass := by
    dsimp [Cmass]
    positivity
  let c : ℝ := max c₁ (c₂ * Cmass)
  refine ⟨c, lt_of_lt_of_le hc₁ (le_max_left _ _), ?_⟩
  intro g
  obtain ⟨_, hg_bound⟩ := hbound g
  have hL2_eq :
      ∫ x : SpaceTime2, (g x) ^ 2 =
        ∫ x : SpaceTime2, ‖g x‖ ^ (2 : ℝ) := by
    congr 1
    ext x
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
  have hGreen :
      continuumGreenBilinear 2 mass g g ≤
        Cmass * ∫ x : SpaceTime2, ‖g x‖ ^ (2 : ℝ) := by
    calc
      continuumGreenBilinear 2 mass g g
          ≤ Cmass * ∫ x : SpaceTime2, (g x) ^ 2 :=
        continuumGreenBilinear_le_mass_inv_sq (d := 2) mass hmass g
      _ = Cmass * ∫ x : SpaceTime2, ‖g x‖ ^ (2 : ℝ) := by rw [hL2_eq]
  have hc₁_le : c₁ ≤ c := le_max_left _ _
  have hc₂_le : c₂ * Cmass ≤ c := le_max_right _ _
  have hL1_nonneg : 0 ≤ ∫ x : SpaceTime2, ‖g x‖ ∂volume :=
    integral_nonneg fun _ => norm_nonneg _
  have hL2_nonneg : 0 ≤ ∫ x : SpaceTime2, ‖g x‖ ^ (2 : ℝ) ∂volume := by
    apply integral_nonneg
    intro x
    positivity
  calc
    ∫ ω : FieldConfig2, Real.exp (|ω g|) ∂μ
        ≤ Real.exp
            (c₁ * (∫ x, ‖g x‖ ∂volume) +
              c₂ * continuumGreenBilinear 2 mass g g) :=
      hg_bound
    _ ≤ Real.exp
          (c₁ * (∫ x : SpaceTime2, ‖g x‖ ∂volume) +
            c₂ * (Cmass * ∫ x : SpaceTime2, ‖g x‖ ^ (2 : ℝ) ∂volume)) := by
        apply Real.exp_le_exp_of_le
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hGreen (le_of_lt hc₂))
    _ ≤ Real.exp
          (c * (∫ x : SpaceTime2, ‖g x‖ ∂volume +
            ∫ x : SpaceTime2, ‖g x‖ ^ (2 : ℝ) ∂volume)) := by
        apply Real.exp_le_exp_of_le
        have h1 :
            c₁ * (∫ x : SpaceTime2, ‖g x‖ ∂volume) ≤
              c * (∫ x : SpaceTime2, ‖g x‖ ∂volume) :=
          mul_le_mul_of_nonneg_right hc₁_le hL1_nonneg
        have h2 :
            c₂ * (Cmass * ∫ x : SpaceTime2, ‖g x‖ ^ (2 : ℝ) ∂volume) ≤
              c * (∫ x : SpaceTime2, ‖g x‖ ^ (2 : ℝ) ∂volume) := by
          calc
            c₂ * (Cmass * ∫ x : SpaceTime2, ‖g x‖ ^ (2 : ℝ) ∂volume) =
                (c₂ * Cmass) * ∫ x : SpaceTime2, ‖g x‖ ^ (2 : ℝ) ∂volume := by ring
            _ ≤ c * (∫ x : SpaceTime2, ‖g x‖ ^ (2 : ℝ) ∂volume) :=
              mul_le_mul_of_nonneg_right hc₂_le hL2_nonneg
        have hsum :
            c₁ * (∫ x : SpaceTime2, ‖g x‖ ∂volume) +
                c₂ * (Cmass * ∫ x : SpaceTime2, ‖g x‖ ^ (2 : ℝ) ∂volume) ≤
              c * (∫ x : SpaceTime2, ‖g x‖ ∂volume) +
                c * (∫ x : SpaceTime2, ‖g x‖ ^ (2 : ℝ) ∂volume) :=
          add_le_add h1 h2
        exact hsum.trans_eq (by ring)

/-- **OS0 for the continuum limit** from exponential moments.

The generating functional `Z[Σ zᵢJᵢ] = ∫ exp(i · Σ zᵢ⟨ω, Jᵢ⟩) dμ` is entire
analytic in `z ∈ ℂⁿ`. This is the direct packaging of
`continuum_exponential_moments` and `analyticOn_generatingFunctionalC` into the
generic OS0 axiom bundle. -/
theorem os0_for_continuum_limit (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure FieldConfig2)
    (hμ : IsProbabilityMeasure μ)
    (h_limit : IsPphi2Limit μ P mass) :
    @EuclideanOS.OS0_Analyticity plane2Background μ hμ := by
  have h_exp := continuum_exponential_moments P mass hmass μ h_limit
  intro n J
  exact analyticOn_generatingFunctionalC μ h_exp n J

/-- **OS1 for the continuum limit** from exponential moments.

The regularity bound `‖Z[J]‖ ≤ exp(c · (‖J‖₁ + ‖J‖₂²))` follows by bounding the
complex source through its imaginary part and then applying
`exponential_moment_schwartz_bound`. -/
theorem os1_for_continuum_limit (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure FieldConfig2)
    (hμ : IsProbabilityMeasure μ)
    (h_limit : IsPphi2Limit μ P mass) :
    @EuclideanOS.OS1_Regularity plane2Background μ hμ := by
  have h_exp := continuum_exponential_moments P mass hmass μ h_limit
  have h_bound : ∀ (J : TestFunction2ℂ),
      ‖EuclideanOS.generatingFunctionalℂ (B := plane2Background) μ J‖ ≤
        ∫ ω : FieldConfig2, Real.exp (|ω (EuclideanOS.schwartzIm J)|) ∂μ := by
    intro J
    have hint_abs : Integrable
        (fun ω : FieldConfig2 => Real.exp (|ω (EuclideanOS.schwartzIm J)|)) μ := by
      have := h_exp (EuclideanOS.schwartzIm J) 1 one_pos
      simpa only [one_mul] using this
    have h_le : ∀ ω : FieldConfig2,
        ‖Complex.exp
            (Complex.I * (↑(ω (EuclideanOS.schwartzRe J)) +
              Complex.I * ↑(ω (EuclideanOS.schwartzIm J))))‖ ≤
          Real.exp (|ω (EuclideanOS.schwartzIm J)|) := by
      intro ω
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have h_re :
          (Complex.I * (↑(ω (EuclideanOS.schwartzRe J)) +
            Complex.I * ↑(ω (EuclideanOS.schwartzIm J)))).re =
            -(ω (EuclideanOS.schwartzIm J)) := by
        simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [h_re]
      exact (le_abs_self (-(ω (EuclideanOS.schwartzIm J)))).trans_eq (abs_neg _)
    exact (norm_integral_le_integral_norm _).trans
      (integral_mono_of_nonneg
        (ae_of_all μ fun ω => norm_nonneg _)
        hint_abs
        (ae_of_all μ h_le))
  obtain ⟨c, hc, h_norm⟩ := exponential_moment_schwartz_bound P mass hmass μ h_limit
  refine ⟨2, c, one_le_two, le_refl _, hc, ?_⟩
  intro J
  calc ‖EuclideanOS.generatingFunctionalℂ (B := plane2Background) μ J‖
      ≤ ∫ ω : FieldConfig2, Real.exp |ω (EuclideanOS.schwartzIm J)| ∂μ := h_bound J
    _ ≤ Real.exp
          (c * ((∫ x, ‖EuclideanOS.schwartzIm J x‖) +
            ∫ x, ‖EuclideanOS.schwartzIm J x‖ ^ (2 : ℝ))) :=
        h_norm (EuclideanOS.schwartzIm J)
    _ ≤ Real.exp
          (c * ((∫ x : SpaceTime2, ‖J x‖) +
            ∫ x : SpaceTime2, ‖J x‖ ^ (2 : ℝ))) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hc)
        have hIm : ∀ x, ‖EuclideanOS.schwartzIm J x‖ ≤ ‖J x‖ :=
          fun x => RCLike.norm_im_le_norm (J x)
        apply add_le_add
        · exact integral_mono
            (SchwartzMap.integrable (EuclideanOS.schwartzIm J)).norm
            (SchwartzMap.integrable J).norm hIm
        · exact integral_mono
            (schwartz_integrable_norm_rpow (EuclideanOS.schwartzIm J) two_pos)
            (schwartz_integrable_norm_rpow J two_pos)
            (fun x => Real.rpow_le_rpow (norm_nonneg _) (hIm x) (by norm_num))

/-! ## Canonical approximant convergence input -/

/-- **Canonical characteristic-functional convergence from the lattice construction.**

The abstract marker predicate `IsPphi2Limit μ P mass` only records the
existence of some approximating sequence. For Ward-identity arguments that must
use the actual lattice measures at spacing `a`, we need the stronger statement
that `μ` is obtained as a limit of the canonical continuum-embedded measures
`continuumMeasure 2 N P a mass`.

This is the precise lower-layer input needed to derive continuum rotation
invariance from the already-formalized anomaly estimate, without axiomatizing
the final symmetry statement itself. -/
axiom canonical_continuumMeasure_cf_tendsto (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (h_limit : IsPphi2Limit μ P mass) :
    ∃ (a : ℕ → ℝ) (ha_pos : ∀ n, 0 < a n),
      (∀ n, a n ≤ 1) ∧
      Filter.Tendsto a Filter.atTop (nhds 0) ∧
      ∀ (f : TestFunction2),
        Filter.Tendsto
          (fun n =>
            ∫ ω : FieldConfig2,
              Complex.exp (Complex.I * ↑(ω f)) ∂
                (continuumMeasure 2 N P (a n) mass (ha_pos n) hmass))
          Filter.atTop
          (nhds (EuclideanOS.generatingFunctional (B := plane2Background) μ f))

/-- **Exponential clustering of the continuum limit** from spectral gap.

For any test functions `f, g ∈ S(ℝ²)`, there exist `m₀, C > 0` such that

  `‖Z[f + τ_a g] - Z[f] · Z[g]‖ ≤ C · exp(-m₀ · ‖a‖)`

for all translations `a ∈ ℝ²`. This is the substantive continuum-limit OS4
input, transferred from the lattice spectral gap. -/
axiom continuum_exponential_clustering (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (h_limit : IsPphi2Limit μ P mass)
    (f g : TestFunction2) :
    ∃ (m₀ C : ℝ), 0 < m₀ ∧ 0 < C ∧
    ∀ (a : SpaceTime2),
    ‖EuclideanOS.generatingFunctional (B := plane2Background) μ
        (f + SchwartzMap.translate a g)
      - EuclideanOS.generatingFunctional (B := plane2Background) μ f *
          EuclideanOS.generatingFunctional (B := plane2Background) μ g‖
    ≤ C * Real.exp (-m₀ * ‖a‖)

/-- **OS4 for the continuum limit** from exponential clustering.

The ε-δ formulation of OS4 follows immediately from the exponential bound:
given `ε > 0`, choose `R` large enough that `C · exp(-m₀ · R) < ε`. -/
theorem os4_for_continuum_limit (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (ContinuumTestFunction 2)))
    (hμ : IsProbabilityMeasure μ)
    (h_limit : IsPphi2Limit μ P mass) :
    @EuclideanOS.OS4_Clustering plane2Background μ hμ := by
  intro f g ε hε
  obtain ⟨m₀, C, hm₀, hC, h_bound⟩ := continuum_exponential_clustering P mass hmass μ h_limit f g
  refine ⟨max 1 (Real.log (C / ε) / m₀), lt_max_of_lt_left one_pos, fun a ha => ?_⟩
  have ha_pos : (0 : ℝ) < ‖a‖ :=
    lt_of_lt_of_le one_pos (le_of_lt (lt_of_le_of_lt (le_max_left _ _) ha))
  calc ‖EuclideanOS.generatingFunctional (B := plane2Background) μ
          (f + SchwartzMap.translate a g)
         - EuclideanOS.generatingFunctional (B := plane2Background) μ f *
            EuclideanOS.generatingFunctional (B := plane2Background) μ g‖
      ≤ C * Real.exp (-m₀ * ‖a‖) := h_bound a
    _ < ε := by
        have hCε_pos : (0 : ℝ) < C / ε := div_pos hC hε
        have hm₀a_gt : Real.log (C / ε) < m₀ * ‖a‖ := by
          have h : Real.log (C / ε) / m₀ < ‖a‖ :=
            lt_of_le_of_lt (le_max_right _ _) ha
          nlinarith [div_mul_cancel₀ (Real.log (C / ε)) (ne_of_gt hm₀)]
        have hexp_lt : Real.exp (-m₀ * ‖a‖) < Real.exp (-Real.log (C / ε)) := by
          apply Real.exp_lt_exp.mpr
          linarith
        have hexp_simp : Real.exp (-Real.log (C / ε)) = ε / C := by
          rw [Real.exp_neg, Real.exp_log hCε_pos, inv_div]
        rw [hexp_simp] at hexp_lt
        calc C * Real.exp (-m₀ * ‖a‖)
            < C * (ε / C) := by
                apply mul_lt_mul_of_pos_left hexp_lt hC
          _ = ε := by field_simp

-- OS3 inheritance is now `os3_for_continuum_limit` in `OS2_WardIdentity.lean`,
-- stated directly in the standard `OS3_ReflectionPositivity` form.

-- NOTE: os0_inheritance and os4_inheritance were removed as dead axioms
-- (only used in SatisfiesOS0134 bundle which was never consumed downstream).
-- The actual OS0/OS1 proof chains now live here:
-- continuum_exponential_moments → analyticOn_generatingFunctionalC → os0_for_continuum_limit
-- continuum_exponential_moment_green_bound → exponential_moment_schwartz_bound
--   → os1_for_continuum_limit.
-- OS4 goes through continuum_exponential_clustering → os4_for_continuum_limit.

end Pphi2

end
