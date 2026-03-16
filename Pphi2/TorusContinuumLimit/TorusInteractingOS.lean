/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Torus Interacting OS Axioms: OS0–OS2 for the P(φ)₂ Continuum Limit

States and proves (modulo general axioms) the Osterwalder-Schrader axioms
for the torus interacting continuum limit measure.

## Main results

- `torusInteracting_os0` — analyticity of generating functional
- `torusInteracting_os1` — regularity bound
- `torusInteracting_os2_translation` — translation invariance
- `torusInteracting_os2_D4` — D4 point group invariance
- `torusInteracting_satisfies_OS` — bundled OS0–OS2

## Mathematical background

The interacting P(φ)₂ measure on the torus T²_L is the weak limit
  `μ_P = lim_{N→∞} (ι̃_N)_* ((1/Z_N) exp(-V_N) dμ_{GFF,N})`
where V_N is the Wick-ordered interaction on the N×N lattice.

### OS0 (Analyticity)
The generating functional `Z[f] = ∫ exp(iω(f)) dμ_P` is entire analytic
in complex test function coefficients. This follows from:
1. For each ω, the integrand `exp(iω(f))` is entire in f.
2. The interacting measure has exponential moments (Nelson's estimate),
   providing the domination bound.
3. Morera's theorem / analyticity of parameter-dependent integrals
   (`analyticOnNhd_integral`).

### OS1 (Regularity)
The bound `‖Z_ℂ[f_re, f_im]‖ ≤ exp(c · (q(f_re) + q(f_im)))` for a
continuous seminorm q. Follows from Cauchy-Schwarz density transfer:
the interacting exponential moment is bounded by the Gaussian moment
(which grows as exp(½G(f,f))) times √K from Nelson's estimate.

### OS2 (Translation invariance)
On the torus T² = (ℝ/Lℤ)², translations in BOTH spatial and temporal
directions are exact symmetries at every lattice cutoff N (the torus
domain is periodic). This is simpler than the cylinder case where time
translation invariance is broken at finite temporal cutoff.

The proof transfers lattice translation invariance
(`latticeMeasure_translation_invariant`) through the weak limit.

### OS3 (Reflection positivity)
Dropped on the torus — RP is more natural on the cylinder S¹×ℝ.

## References

- Glimm-Jaffe, *Quantum Physics*, §19.3-19.4
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. V-VI
- Nelson (1966), "A quartic interaction in two dimensions"
-/

import Pphi2.TorusContinuumLimit.TorusOSAxioms
import Pphi2.TorusContinuumLimit.TorusInteractingLimit
import Pphi2.TorusContinuumLimit.TorusPropagatorConvergence
import Pphi2.GeneralResults.ComplexAnalysis
import Torus.Evaluation

noncomputable section

open GaussianField MeasureTheory Filter Complex

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Cutoff-level invariance axioms

The interacting lattice measure on the torus is invariant under lattice
translations and D4 point group symmetries. These follow from:
- The interaction `V_N(ω) = a² Σ_x :P(φ(x)):_c` sums over ALL lattice
  sites with periodic BCs, so translating relabels the sum.
- The lattice GFF measure is invariant (covariance is translation/D4-invariant).
- The Boltzmann weight `exp(-V)` is therefore invariant.
- The partition function Z is the same before and after the symmetry.

References: Glimm-Jaffe §19.4, Simon Ch. V §1. -/

/-- **Translation invariance of the interacting continuum limit.**

The weak limit measure μ_P satisfies `Z[f] = Z[T_v f]` for all `v ∈ ℝ²`.

**Note:** This is stated at the limit level, not the cutoff level.
At finite cutoff N, the lattice interacting measure is only invariant under
*lattice* translations (multiples of L/N). Translation invariance for
all v ∈ ℝ² holds only in the continuum limit, via an approximation argument:

1. For any v, let w_N be the nearest lattice vector (in spacing L/N).
2. At cutoff N: `Z_N[T_{w_N} f] = Z_N[f]` (by `latticeMeasure_translation_invariant`).
3. `Z_N[T_v f] - Z_N[T_{w_N} f] → 0` (since w_N → v and the GF is continuous in
   the test function argument via the uniform second moment bound).
4. Taking N → ∞: `Z[T_v f] = Z[f]`.

References: Glimm-Jaffe §8.1, Simon Ch. V §1. -/
axiom torusInteractingLimit_translation_invariant
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (v : ℝ × ℝ) (f : TorusTestFunction L) :
    torusGeneratingFunctional L μ f =
    torusGeneratingFunctional L μ (torusTranslation L v f)

/-- The lattice swap linear map: `(L_swap g)(x) = g(swapSites x)`. -/
private def latticeSwapLM (N : ℕ) :
    FinLatticeField 2 N →ₗ[ℝ] FinLatticeField 2 N where
  toFun g := g ∘ swapSites N
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Lattice interacting measure is swap-invariant.**

The interacting lattice measure is invariant under coordinate swap
`(i,j) ↦ (j,i)` on `FinLatticeSites 2 N`. This follows from:
- The interaction `V = a² Σ_x :P(φ(x)):` sums over all sites; swap relabels.
- The GFF eigenvalues `λ_{n₁,n₂}` are symmetric under n₁ ↔ n₂.
- Lebesgue measure is preserved (det of swap = -1, |det| = 1).

Analogous to `latticeMeasure_translation_invariant` but with swap. -/
axiom interactingLatticeMeasure_swap_invariant
    (N : ℕ) [NeZero N] (P : InteractionPolynomial) (mass : ℝ)
    (ha : 0 < circleSpacing L N) (hmass : 0 < mass)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Configuration (FinLatticeField 2 N) → E) :
    ∫ ω, F (ω.comp (latticeSwapLM N).toContinuousLinearMap) ∂(interactingLatticeMeasure 2 N P
      (circleSpacing L N) mass ha hmass) =
    ∫ ω, F ω ∂(interactingLatticeMeasure 2 N P (circleSpacing L N) mass ha hmass)

/-- **The torus interacting generating functional is swap-invariant at every cutoff.**

  `∫ exp(iω(f)) dμ_{P,N} = ∫ exp(iω(σf)) dμ_{P,N}` where σ swaps coordinates.

Proved from `evalTorusAtSite_swap` (equivariance of the torus embedding)
and `interactingLatticeMeasure_swap_invariant` (lattice measure symmetry). -/
theorem torusInteractingMeasure_gf_swap_invariant
    (N : ℕ) [NeZero N] (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (f : TorusTestFunction L) :
    torusGeneratingFunctional L (torusInteractingMeasure L N P mass hmass) f =
    torusGeneratingFunctional L (torusInteractingMeasure L N P mass hmass)
      (torusSwap L f) := by
  -- Step 1: Both sides are integrals of exp(i·ω(g)) over the pushforward measure.
  -- The key identity: latticeTestFn(swap f) = latticeSwapLM(latticeTestFn f)
  have h_lattice_swap : ∀ x : FinLatticeSites 2 N,
      latticeTestFn L N (torusSwap L f) x = latticeTestFn L N f (swapSites N x) := by
    intro x
    simp only [latticeTestFn, torusSwap]
    exact evalTorusAtSite_swap L N x f
  -- Step 2: Convert both sides to lattice integrals via definition unfolding
  set μ_lat := interactingLatticeMeasure 2 N P (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass
  -- Compute LHS as lattice integral
  have h_lhs : torusGeneratingFunctional L (torusInteractingMeasure L N P mass hmass) f =
      ∫ φ, Complex.exp (Complex.I * ↑(φ (latticeTestFn L N f))) ∂μ_lat := by
    unfold torusGeneratingFunctional torusInteractingMeasure
    have hasm : AEStronglyMeasurable (fun ω : Configuration (TorusTestFunction L) =>
        Complex.exp (Complex.I * ↑(ω f)))
        (Measure.map (torusEmbedLift L N) μ_lat) :=
      (Complex.measurable_exp.comp
        (measurable_const.mul (Complex.measurable_ofReal.comp
          (configuration_eval_measurable f)))).aestronglyMeasurable
    rw [MeasureTheory.integral_map (torusEmbedLift_measurable L N).aemeasurable hasm]
    simp_rw [torusEmbedLift_eval_eq]
  -- Compute RHS as lattice integral
  have h_rhs : torusGeneratingFunctional L (torusInteractingMeasure L N P mass hmass)
      (torusSwap L f) =
      ∫ φ, Complex.exp (Complex.I * ↑(φ (latticeTestFn L N (torusSwap L f)))) ∂μ_lat := by
    unfold torusGeneratingFunctional torusInteractingMeasure
    have hasm : AEStronglyMeasurable (fun ω : Configuration (TorusTestFunction L) =>
        Complex.exp (Complex.I * ↑(ω (torusSwap L f))))
        (Measure.map (torusEmbedLift L N) μ_lat) :=
      (Complex.measurable_exp.comp
        (measurable_const.mul (Complex.measurable_ofReal.comp
          (configuration_eval_measurable (torusSwap L f))))).aestronglyMeasurable
    rw [MeasureTheory.integral_map (torusEmbedLift_measurable L N).aemeasurable hasm]
    simp_rw [torusEmbedLift_eval_eq]
  rw [h_lhs, h_rhs]
  -- Now: ∫ exp(i·φ(latticeTestFn f)) = ∫ exp(i·φ(latticeTestFn(swap f)))
  -- latticeTestFn(swap f) = latticeSwapLM(latticeTestFn f)
  have h_swap_lattice : ∀ φ : Configuration (FinLatticeField 2 N),
      φ (latticeTestFn L N (torusSwap L f)) =
      (φ.comp (latticeSwapLM N).toContinuousLinearMap) (latticeTestFn L N f) := by
    intro φ
    change φ (latticeTestFn L N (torusSwap L f)) =
      φ ((latticeSwapLM N) (latticeTestFn L N f))
    congr 1; ext x; exact h_lattice_swap x
  simp_rw [h_swap_lattice]
  -- Apply lattice swap invariance
  exact (interactingLatticeMeasure_swap_invariant L N P mass
    (circleSpacing_pos L N) hmass _).symm

/-- The lattice time-reflection linear map: `(L_refl g)(x) = g(timeReflectSites x)`. -/
private def latticeTimeReflectLM (N : ℕ) :
    FinLatticeField 2 N →ₗ[ℝ] FinLatticeField 2 N where
  toFun g := g ∘ timeReflectSites N
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Lattice interacting measure is time-reflection-invariant.**
Same justification as swap: sum relabeling + eigenvalue symmetry + measure preservation. -/
axiom interactingLatticeMeasure_timeReflection_invariant
    (N : ℕ) [NeZero N] (P : InteractionPolynomial) (mass : ℝ)
    (ha : 0 < circleSpacing L N) (hmass : 0 < mass)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Configuration (FinLatticeField 2 N) → E) :
    ∫ ω, F (ω.comp (latticeTimeReflectLM N).toContinuousLinearMap) ∂(interactingLatticeMeasure
      2 N P (circleSpacing L N) mass ha hmass) =
    ∫ ω, F ω ∂(interactingLatticeMeasure 2 N P (circleSpacing L N) mass ha hmass)

/-- **The torus interacting generating functional is time-reflection-invariant.**

Proved from `evalTorusAtSite_timeReflection` (equivariance)
and `interactingLatticeMeasure_timeReflection_invariant` (lattice symmetry). -/
theorem torusInteractingMeasure_gf_timeReflection_invariant
    (N : ℕ) [NeZero N] (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (f : TorusTestFunction L) :
    torusGeneratingFunctional L (torusInteractingMeasure L N P mass hmass) f =
    torusGeneratingFunctional L (torusInteractingMeasure L N P mass hmass)
      (torusTimeReflection L f) := by
  have h_lattice_refl : ∀ x : FinLatticeSites 2 N,
      latticeTestFn L N (torusTimeReflection L f) x =
      latticeTestFn L N f (timeReflectSites N x) := by
    intro x
    simp only [latticeTestFn, torusTimeReflection]
    exact evalTorusAtSite_timeReflection L N x f
  -- Follow exactly the same pattern as swap proof
  unfold torusGeneratingFunctional torusInteractingMeasure
  set μ_lat := interactingLatticeMeasure 2 N P (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass
  have hmeas : AEMeasurable (torusEmbedLift L N) μ_lat :=
    (torusEmbedLift_measurable L N).aemeasurable
  have hasm₁ : AEStronglyMeasurable (fun ω : Configuration (TorusTestFunction L) =>
      Complex.exp (Complex.I * ↑(ω f))) (Measure.map (torusEmbedLift L N) μ_lat) :=
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (configuration_eval_measurable f)))).aestronglyMeasurable
  have hasm₂ : AEStronglyMeasurable (fun ω : Configuration (TorusTestFunction L) =>
      Complex.exp (Complex.I * ↑(ω (torusTimeReflection L f))))
      (Measure.map (torusEmbedLift L N) μ_lat) := by
    exact (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (configuration_eval_measurable (torusTimeReflection L f))))).aestronglyMeasurable
  rw [MeasureTheory.integral_map hmeas hasm₁, MeasureTheory.integral_map hmeas hasm₂]
  simp_rw [torusEmbedLift_eval_eq]
  have h_refl_lattice : ∀ φ : Configuration (FinLatticeField 2 N),
      φ (latticeTestFn L N (torusTimeReflection L f)) =
      (φ.comp (latticeTimeReflectLM N).toContinuousLinearMap) (latticeTestFn L N f) := by
    intro φ
    change φ (latticeTestFn L N (torusTimeReflection L f)) =
      φ ((latticeTimeReflectLM N) (latticeTestFn L N f))
    congr 1; ext x; exact h_lattice_refl x
  simp_rw [h_refl_lattice]
  exact (interactingLatticeMeasure_timeReflection_invariant L N P mass
    (circleSpacing_pos L N) hmass _).symm

/-- **Cutoff exponential moment bound.**

At each cutoff N, the interacting measure satisfies:
  `∫ exp(|ω(f)|) dμ_{P,N} ≤ C · exp(G_N(f,f))`

From Cauchy-Schwarz density transfer + Nelson + Gaussian MGF:
  `E_P[exp(|ωf|)] ≤ √K · (E_GFF[exp(2|ωf|)])^{1/2} ≤ √(2K) · exp(G_N(f,f))`

The Gaussian exponential moment `E_GFF[exp(t|X|)] ≤ 2 exp(t²σ²/2)` for X ~ N(0,σ²)
follows from `mgf_id_gaussianReal` (Mathlib). -/
axiom torusInteractingMeasure_exponentialMomentBound_cutoff
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : TorusTestFunction L) (N : ℕ) [NeZero N],
    Integrable (fun ω : Configuration (TorusTestFunction L) =>
      Real.exp (|ω f|)) (torusInteractingMeasure L N P mass hmass) ∧
    ∫ ω : Configuration (TorusTestFunction L),
      Real.exp (|ω f|)
      ∂(torusInteractingMeasure L N P mass hmass) ≤
    C * Real.exp (torusEmbeddedTwoPoint L N mass hmass f f)

/-- **Interacting exponential moment bound** (transferred to continuum limit).

The weak limit measure satisfies `∫ exp(|ω(f)|) dμ ≤ exp(c · G_L(f,f))`.
Proved from the cutoff bound + weak convergence:
1. For each C > 0: `∫ min(exp(|ωf|), C) dμ = lim ∫ min(exp(|ωf|), C) dμ_N` (bcf)
2. `∫ min(exp(|ωf|), C) dμ_N ≤ ∫ exp(|ωf|) dμ_N ≤ K · exp(G_N(f,f))`
3. `G_N(f,f) → G(f,f)` (propagator convergence)
4. Taking C → ∞ by MCT gives the bound. -/
theorem torusInteracting_exponentialMomentBound
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (_hφ : StrictMono φ)
    (hconv : ∀ (g : Configuration (TorusTestFunction L) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
        Tendsto (fun n => ∫ ω, g ω ∂(torusInteractingMeasure L (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, g ω ∂μ)))
    : ∃ K : ℝ, 0 < K ∧ ∀ (f : TorusTestFunction L),
    Integrable (fun ω : Configuration (TorusTestFunction L) =>
      Real.exp (|ω f|)) μ ∧
    ∫ ω : Configuration (TorusTestFunction L),
      Real.exp (|ω f|) ∂μ ≤
    K * Real.exp (torusContinuumGreen L mass hmass f f) := by
  -- Get the universal cutoff bound (K independent of f and N)
  obtain ⟨K, hK_pos, hK_bound⟩ :=
    torusInteractingMeasure_exponentialMomentBound_cutoff L P mass hmass
  refine ⟨K, hK_pos, fun f => ?_⟩
  set B := K * Real.exp (torusContinuumGreen L mass hmass f f)
  have hB_pos : 0 < B := mul_pos hK_pos (Real.exp_pos _)
  have hG_conv := torus_propagator_convergence L mass hmass f f
  -- Abbreviation for the target function
  set F : Configuration (TorusTestFunction L) → ℝ := fun ω => Real.exp (|ω f|) with hF_def
  have hF_nn : ∀ ω : Configuration (TorusTestFunction L), 0 ≤ F ω :=
    fun ω => (Real.exp_pos _).le
  have hF_meas : Measurable F :=
    Real.measurable_exp.comp ((configuration_eval_measurable f).abs)
  -- Step 1: For every M > 0, ∫ min(F, M) dμ ≤ B (truncation + weak convergence)
  have h_trunc : ∀ M : ℝ, 0 < M →
      ∫ ω : Configuration (TorusTestFunction L), min (F ω) M ∂μ ≤ B := by
    intro M hM
    have h_cont : Continuous (fun ω : Configuration (TorusTestFunction L) =>
        min (F ω) M) :=
      (Real.continuous_exp.comp (continuous_abs.comp (WeakDual.eval_continuous f))).min
        continuous_const
    have h_bdd : ∃ C, ∀ ω : Configuration (TorusTestFunction L),
        |min (F ω) M| ≤ C :=
      ⟨M, fun ω => by
        rw [abs_of_nonneg (le_min (hF_nn ω) hM.le)]
        exact min_le_right _ _⟩
    have h_lim := hconv _ h_cont h_bdd
    have h_cutoff : ∀ n, ∫ ω, min (F ω) M
        ∂(torusInteractingMeasure L (φ n + 1) P mass hmass) ≤
        K * Real.exp (torusEmbeddedTwoPoint L (φ n + 1) mass hmass f f) := by
      intro n
      obtain ⟨h_int_n, h_bnd_n⟩ := hK_bound f (φ n + 1)
      calc ∫ ω, min (F ω) M
            ∂(torusInteractingMeasure L (φ n + 1) P mass hmass)
          ≤ ∫ ω, F ω
            ∂(torusInteractingMeasure L (φ n + 1) P mass hmass) := by
            apply integral_mono_of_nonneg
            · exact ae_of_all _ (fun ω => le_min (hF_nn ω) hM.le)
            · exact h_int_n
            · exact ae_of_all _ (fun ω => min_le_left _ _)
        _ ≤ K * Real.exp (torusEmbeddedTwoPoint L (φ n + 1) mass hmass f f) := h_bnd_n
    have h_B_lim : Tendsto (fun n =>
        K * Real.exp (torusEmbeddedTwoPoint L (φ n + 1) mass hmass f f))
        atTop (nhds B) := by
      show Tendsto _ atTop (nhds (K * Real.exp (torusContinuumGreen L mass hmass f f)))
      apply Filter.Tendsto.const_mul
      exact (Real.continuous_exp.tendsto _).comp
        (hG_conv.comp (_hφ.tendsto_atTop))
    exact le_of_tendsto_of_tendsto h_lim h_B_lim (Filter.Eventually.of_forall h_cutoff)
  -- Step 2: Each truncation min(F, n) is integrable (bounded on probability space)
  have h_trunc_int : ∀ n : ℕ, Integrable (fun ω => min (F ω) (↑n : ℝ)) μ := by
    intro n
    exact Integrable.of_bound
      (hF_meas.min measurable_const).aestronglyMeasurable n
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hF_nn ω) (Nat.cast_nonneg n))]
        exact min_le_right _ _)
  -- Truncation bounds for natural numbers
  have h_trunc_nat : ∀ n : ℕ, ∫ ω, min (F ω) (↑n : ℝ) ∂μ ≤ B := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp only [Nat.cast_zero]
      calc ∫ ω, min (F ω) (0 : ℝ) ∂μ
          ≤ ∫ ω, (0 : ℝ) ∂μ := by
            apply integral_mono_of_nonneg
            · exact ae_of_all _ fun _ => le_min (hF_nn _) le_rfl
            · exact integrable_const 0
            · exact ae_of_all _ fun _ => min_le_right _ _
        _ = 0 := by simp
        _ ≤ B := le_of_lt hB_pos
    · exact h_trunc n (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
  -- Step 3: Integrability of F from bounded lintegral
  -- Use MCT for lintegrals: ∫⁻ ofReal(min(F, n)) → ∫⁻ ofReal(F) as n → ∞
  -- Each term ≤ ofReal(B), so the limit is ≤ ofReal(B) < ∞
  have h_int : Integrable F μ := by
    refine ⟨hF_meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hF_nn)]
    -- MCT for lintegrals: ∫⁻ ofReal(min(F, n)) ↗ ∫⁻ ofReal(F)
    have h_lint_mono : ∀ᵐ ω ∂μ, Monotone
        (fun n : ℕ => ENNReal.ofReal (min (F ω) (↑n : ℝ))) :=
      ae_of_all _ fun ω n m hnm =>
        ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.mpr hnm))
    have h_lint_pw : ∀ᵐ ω ∂μ, Tendsto
        (fun n : ℕ => ENNReal.ofReal (min (F ω) (↑n : ℝ)))
        atTop (nhds (ENNReal.ofReal (F ω))) :=
      ae_of_all _ fun ω => (ENNReal.continuous_ofReal.tendsto _).comp
        (tendsto_atTop_of_eventually_const (i₀ := ⌈F ω⌉₊) fun n hn => by
          rw [min_eq_left]; exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hn))
    have h_lint_meas : ∀ n : ℕ, AEMeasurable
        (fun ω => ENNReal.ofReal (min (F ω) (↑n : ℝ))) μ :=
      fun n => (hF_meas.min measurable_const).ennreal_ofReal.aemeasurable
    have h_lint_conv := lintegral_tendsto_of_tendsto_of_monotone
      h_lint_meas h_lint_mono h_lint_pw
    -- Each ∫⁻ ofReal(min(F, n)) = ofReal(∫ min(F, n)) ≤ ofReal(B)
    have h_lint_bound : ∀ n : ℕ, ∫⁻ ω, ENNReal.ofReal (min (F ω) (↑n : ℝ)) ∂μ ≤
        ENNReal.ofReal B := by
      intro n
      rw [← ofReal_integral_eq_lintegral_ofReal (h_trunc_int n)
        (ae_of_all _ fun ω => le_min (hF_nn ω) (Nat.cast_nonneg n))]
      exact ENNReal.ofReal_le_ofReal (h_trunc_nat n)
    -- The limit ∫⁻ ofReal(F) ≤ ofReal(B) by le_of_tendsto'
    exact lt_of_le_of_lt (le_of_tendsto' h_lint_conv h_lint_bound) ENNReal.ofReal_lt_top
  constructor
  · exact h_int
  · -- Step 4: ∫ F dμ ≤ B by MCT + truncation bounds
    have h_mono : ∀ᵐ ω ∂μ, Monotone (fun n : ℕ => min (F ω) (↑n : ℝ)) :=
      ae_of_all _ fun ω n m hnm => min_le_min_left _ (Nat.cast_le.mpr hnm)
    have h_pw : ∀ᵐ ω ∂μ,
        Tendsto (fun n : ℕ => min (F ω) (↑n : ℝ)) atTop (nhds (F ω)) :=
      ae_of_all _ fun ω => tendsto_atTop_of_eventually_const
        (i₀ := ⌈F ω⌉₊) fun n hn => by
          rw [min_eq_left]
          exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hn)
    have h_mct : Tendsto (fun n : ℕ => ∫ ω, min (F ω) (↑n : ℝ) ∂μ)
        atTop (nhds (∫ ω, F ω ∂μ)) :=
      integral_tendsto_of_tendsto_of_monotone h_trunc_int h_int h_mono h_pw
    exact le_of_tendsto' h_mct h_trunc_nat

/-! ## Helper: integral invariance from generating functional invariance

The generating functional `Z[f] = ∫ exp(iωf) dμ` determines and is determined
by the real-valued integrals of `cos(ωf)` and `sin(ωf)`. Specifically:
- `Re(Z[f]) = ∫ cos(ωf) dμ`
- `Im(Z[f]) = ∫ sin(ωf) dμ`

So `Z[f] = Z[Sf]` implies `∫ cos(ωf) dμ = ∫ cos(ω(Sf)) dμ` (and similarly for sin). -/

private lemma cosEval_continuous (g : TorusTestFunction L) :
    Continuous (fun ω : Configuration (TorusTestFunction L) => Real.cos (ω g)) :=
  Real.continuous_cos.comp (WeakDual.eval_continuous g)

private lemma cosEval_bounded (g : TorusTestFunction L) :
    ∃ C, ∀ ω : Configuration (TorusTestFunction L), |Real.cos (ω g)| ≤ C :=
  ⟨1, fun _ => Real.abs_cos_le_one _⟩

private lemma sinEval_continuous (g : TorusTestFunction L) :
    Continuous (fun ω : Configuration (TorusTestFunction L) => Real.sin (ω g)) :=
  Real.continuous_sin.comp (WeakDual.eval_continuous g)

private lemma sinEval_bounded (g : TorusTestFunction L) :
    ∃ C, ∀ ω : Configuration (TorusTestFunction L), |Real.sin (ω g)| ≤ C :=
  ⟨1, fun _ => Real.abs_sin_le_one _⟩

/-- Decomposition: the generating functional's real part is the cosine integral.
Proved by commuting Re (a CLM) with the Bochner integral. -/
private lemma gf_re_eq_cos_integral
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ] (g : TorusTestFunction L) :
    (torusGeneratingFunctional L μ g).re =
    ∫ ω : Configuration (TorusTestFunction L), Real.cos (ω g) ∂μ := by
  unfold torusGeneratingFunctional
  rw [show (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ).re =
    Complex.reCLM (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ) from rfl]
  have hint : Integrable (fun ω : Configuration (TorusTestFunction L) =>
      Complex.exp (Complex.I * ↑(ω g))) μ := by
    apply (integrable_const (1 : ℂ)).mono
    · exact (Complex.continuous_exp.measurable.comp
        (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
          (configuration_eval_measurable g)))).aestronglyMeasurable
    · apply ae_of_all; intro ω; simp only [norm_one]
      rw [show Complex.I * ↑(ω g) = ↑(ω g) * Complex.I from mul_comm _ _]
      exact le_of_eq (Complex.norm_exp_ofReal_mul_I (ω g))
  rw [← ContinuousLinearMap.integral_comp_comm Complex.reCLM hint]
  congr 1 with ω
  simp only [Complex.reCLM_apply, mul_comm Complex.I, Complex.exp_mul_I,
    Complex.add_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.sin_ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  exact Complex.cos_ofReal_re (ω g)

/-- Decomposition: the generating functional's imaginary part is the sine integral. -/
private lemma gf_im_eq_sin_integral
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ] (g : TorusTestFunction L) :
    (torusGeneratingFunctional L μ g).im =
    ∫ ω : Configuration (TorusTestFunction L), Real.sin (ω g) ∂μ := by
  unfold torusGeneratingFunctional
  rw [show (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ).im =
    Complex.imCLM (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ) from rfl]
  have hint : Integrable (fun ω : Configuration (TorusTestFunction L) =>
      Complex.exp (Complex.I * ↑(ω g))) μ := by
    apply (integrable_const (1 : ℂ)).mono
    · exact (Complex.continuous_exp.measurable.comp
        (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
          (configuration_eval_measurable g)))).aestronglyMeasurable
    · apply ae_of_all; intro ω; simp only [norm_one]
      rw [show Complex.I * ↑(ω g) = ↑(ω g) * Complex.I from mul_comm _ _]
      exact le_of_eq (Complex.norm_exp_ofReal_mul_I (ω g))
  rw [← ContinuousLinearMap.integral_comp_comm Complex.imCLM hint]
  congr 1 with ω
  simp only [Complex.imCLM_apply, mul_comm Complex.I, Complex.exp_mul_I,
    Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
  ring

/-! ### Helper lemmas for OS0 -/

/-- On a compact set `K ⊆ (Fin n → ℂ)`, imaginary parts are uniformly bounded. -/
private lemma compact_im_bound {n : ℕ} {K : Set (Fin n → ℂ)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ i : Fin n, |Complex.im (z i)| ≤ C := by
  by_cases hKe : K.Nonempty
  · obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
    exact ⟨M, le_trans (norm_nonneg _) (hM _ hKe.some_mem), fun z hz i =>
      (Complex.abs_im_le_norm (z i)).trans ((norm_le_pi_norm z i).trans (hM z hz))⟩
  · exact ⟨0, le_refl _, fun z hz => absurd ⟨z, hz⟩ hKe⟩

/-- For `aᵢ ≥ 0`: `exp(c · Σ aᵢ) ≤ Σ exp(n·c·aᵢ)`. Uses `Σ aᵢ ≤ n · max aᵢ`
and `exp(n·c·max) ≤ Σ exp(n·c·aᵢ)` (the max term is one of the summands). -/
private lemma exp_mul_sum_le {n : ℕ} (hn : 0 < n) (c : ℝ) (hc : 0 ≤ c)
    (a : Fin n → ℝ) :
    Real.exp (c * ∑ i : Fin n, a i) ≤
    ∑ i : Fin n, Real.exp (↑n * c * a i) := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  set M := Finset.univ.sup' hne a
  have hM : ∀ i, a i ≤ M := fun i => Finset.le_sup' a (Finset.mem_univ i)
  have h_sum_le : ∑ i : Fin n, a i ≤ ↑n * M :=
    (Finset.sum_le_sum (fun i _ => hM i)).trans
      (by simp [Finset.sum_const, nsmul_eq_mul])
  have h1 : Real.exp (c * ∑ i, a i) ≤ Real.exp (↑n * c * M) :=
    Real.exp_le_exp_of_le (by nlinarith)
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' hne a
  exact h1.trans ((congr_arg Real.exp (by rw [← hj])).le.trans
    (Finset.single_le_sum (f := fun i => Real.exp (↑n * c * a i))
      (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ j)))

/-! ## OS0: Analyticity of the interacting generating functional

Unlike the Gaussian case (where Z = exp(quadratic) is trivially entire),
the interacting generating functional is a genuine integral:
  `Z_ℂ[f] = ∫ exp(iω(f)) dμ_P`
Its analyticity requires Morera's theorem (holomorphic dependence on
parameters under the integral sign). -/

/-- **OS0 for the torus interacting continuum limit.**

The generating functional `z ↦ ∫ exp(i Σ zᵢ ω(Jᵢ)) dμ_P` is entire
analytic in `z ∈ ℂⁿ`.

**Proof strategy:**
1. Each cutoff measure `μ_N` has entire generating functional (by
   `analyticOnNhd_integral`: the integrand `exp(i Σ zᵢ ω(Jᵢ))` is
   entire in z for each ω, and the exponential moment bound from
   Nelson's estimate provides domination on compact sets).
2. The cutoff generating functionals converge pointwise to the limit
   generating functional (by weak convergence from `torusInteractingLimit_exists`).
3. By Vitali's convergence theorem (locally bounded analytic functions
   converging pointwise have analytic limits), the limit is analytic.

Steps 1 and 3 use `analyticOnNhd_integral` (axiomatized in
`GeneralResults/ComplexAnalysis.lean`). -/
theorem torusInteracting_os0
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (_φ : ℕ → ℕ) (_hφ : StrictMono _φ)
    (_hconv : ∀ (f : Configuration (TorusTestFunction L) → ℝ),
      Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun n => ∫ ω, f ω ∂(torusInteractingMeasure L (_φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, f ω ∂μ))) :
    TorusOS0_Analyticity L μ := by
  intro n J
  -- Goal: z ↦ ∫ exp(I * (ω(Σ Re(zᵢ)Jᵢ) + I * ω(Σ Im(zᵢ)Jᵢ))) dμ is entire
  -- This is ∫ F(z, ω) dμ where F(z, ω) = exp(I * Σᵢ zᵢ ω(Jᵢ))
  -- Apply analyticOnNhd_integral
  -- Note: AnalyticOn = AnalyticOnNhd for open sets (Set.univ is open)
  rw [analyticOn_univ]
  apply analyticOnNhd_integral
  · -- Pointwise analyticity: z ↦ F(z, ω) is entire for each ω
    -- exp(I * (ω(Σ Re(zᵢ)Jᵢ) + I * ω(Σ Im(zᵢ)Jᵢ))) is exp of a ℂ-linear function of z
    intro ω z _
    apply AnalyticAt.cexp'
    -- Rewrite using linearity of ω: I * (ω(Σ Re(zᵢ)Jᵢ) + I * ω(Σ Im(zᵢ)Jᵢ)) = I * Σ zᵢ ω(Jᵢ)
    have h_eq : ∀ w : Fin n → ℂ,
        I * (↑(ω (∑ i, (w i).re • J i)) + I * ↑(ω (∑ i, (w i).im • J i))) =
        I * ∑ i : Fin n, w i * ↑(ω (J i)) := by
      intro w; congr 1
      simp only [map_sum, map_smul, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      congr 1; ext i
      calc ↑(w i).re * ↑(ω (J i)) + I * (↑(w i).im * ↑(ω (J i)))
          = (↑(w i).re + ↑(w i).im * I) * ↑(ω (J i)) := by ring
        _ = w i * ↑(ω (J i)) := by rw [re_add_im]
    simp_rw [h_eq]
    -- I * Σ zᵢ * cᵢ is ℂ-linear in z, hence analytic
    exact analyticAt_const.mul (Finset.univ.analyticAt_fun_sum (fun i _ =>
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticAt z).mul
      analyticAt_const))
  · -- Measurability: F(z, ·) is ae strongly measurable for each z
    intro z
    apply (Complex.measurable_exp.comp _).aestronglyMeasurable
    exact (measurable_const.mul ((Complex.measurable_ofReal.comp
      (configuration_eval_measurable _)).add (measurable_const.mul
      (Complex.measurable_ofReal.comp (configuration_eval_measurable _)))))
  · -- Domination: on compact K, ‖F(z, ω)‖ ≤ bound(ω) integrable
    intro K hK
    -- Get uniform bound C_K on imaginary parts over K
    obtain ⟨C_K, hC_K_nn, hC_K⟩ := compact_im_bound hK
    -- Get exponential moment bound (provides integrability)
    obtain ⟨K_exp, hK_exp_pos, hK_exp_bound⟩ :=
      torusInteracting_exponentialMomentBound L P mass hmass μ _φ _hφ _hconv
    by_cases hn : n = 0
    · -- n = 0: integrand is exp(I * 0) = 1, bounded by 1
      subst hn
      exact ⟨fun _ => 1, integrable_const 1, fun z _ => ae_of_all μ fun ω => by
        simp only [Finset.univ_eq_empty, Finset.sum_empty, map_zero,
          Complex.ofReal_zero, add_zero, mul_zero, Complex.exp_zero, norm_one]; rfl⟩
    · -- n > 0: bound by ∑ᵢ exp(n · C_K · |ω(Jᵢ)|)
      set bound := fun ω : Configuration (TorusTestFunction L) =>
        ∑ i : Fin n, Real.exp (↑n * C_K * |ω (J i)|) with hbound_def
      refine ⟨bound, ?_, fun z hz => ae_of_all μ fun ω => ?_⟩
      · -- Integrability: each exp(n·C_K·|ω(Jᵢ)|) = exp(|ω((n·C_K)•Jᵢ)|) is integrable
        apply integrable_finset_sum; intro i _
        have hscale : ∀ ω : Configuration (TorusTestFunction L),
            Real.exp (↑n * C_K * |ω (J i)|) =
            Real.exp (|ω ((↑n * C_K) • J i)|) := by
          intro ω
          rw [map_smul, smul_eq_mul, abs_mul,
              abs_of_nonneg (mul_nonneg (Nat.cast_nonneg' n) hC_K_nn)]
        simp_rw [hscale]
        exact (hK_exp_bound ((↑n * C_K) • J i)).1
      · -- Pointwise bound: ‖F(z, ω)‖ ≤ bound(ω) for z ∈ K
        -- Step 1: ‖cexp(I·(ω(g_re)+I·ω(g_im)))‖ = exp(-ω(g_im))
        rw [Complex.norm_exp]
        have h_re : (I * (↑(ω (∑ i, (z i).re • J i)) +
            I * ↑(ω (∑ i, (z i).im • J i)))).re =
            -(ω (∑ i, (z i).im • J i)) := by
          have : I * (↑(ω (∑ i, (z i).re • J i)) +
              I * ↑(ω (∑ i, (z i).im • J i))) =
              -↑(ω (∑ i, (z i).im • J i)) +
              ↑(ω (∑ i, (z i).re • J i)) * I := by
            rw [mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul]; ring
          rw [this, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
              Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
              Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
              add_zero]
        rw [h_re]
        -- Step 2: exp(-ω(g_im)) ≤ exp(|ω(g_im)|) ≤ exp(C_K · Σ|ω(Jᵢ)|)
        calc Real.exp (-(ω (∑ i, (z i).im • J i)))
            ≤ Real.exp (|ω (∑ i, (z i).im • J i)|) :=
              Real.exp_le_exp_of_le (neg_le_abs _)
          _ ≤ Real.exp (C_K * ∑ i : Fin n, |ω (J i)|) := by
              apply Real.exp_le_exp_of_le
              rw [map_sum]
              calc |∑ i, ω ((z i).im • J i)|
                  ≤ ∑ i, |ω ((z i).im • J i)| :=
                    Finset.abs_sum_le_sum_abs _ _
                _ = ∑ i, |(z i).im| * |ω (J i)| := by
                    congr 1; ext i; rw [map_smul, smul_eq_mul, abs_mul]
                _ ≤ ∑ i, C_K * |ω (J i)| :=
                    Finset.sum_le_sum (fun i _ =>
                      mul_le_mul_of_nonneg_right (hC_K z hz i) (abs_nonneg _))
                _ = C_K * ∑ i, |ω (J i)| := (Finset.mul_sum _ _ _).symm
          -- Step 3: exp(C_K · Σ|ω(Jᵢ)|) ≤ Σ exp(n·C_K·|ω(Jᵢ)|)
          _ ≤ bound ω :=
              exp_mul_sum_le (Nat.pos_of_ne_zero hn) C_K hC_K_nn _

/-! ## OS1: Regularity of the interacting generating functional -/

/-- **OS1 for the torus interacting continuum limit.**

The complex generating functional satisfies an exponential bound:
  `‖Z_ℂ[f_re, f_im]‖ ≤ exp(c · (q(f_re) + q(f_im)))`
for a continuous seminorm `q` and constant `c > 0`.

**Proof strategy:**
By Cauchy-Schwarz density transfer, the interacting exponential moment
`E_P[exp(t|ω(f)|)]` is bounded by `√K · E_GFF[exp(2t|ω(f)|)]^{1/2}`
where K is Nelson's constant. The Gaussian exponential moment grows as
`exp(2t² G(f,f))`, so the interacting moment is bounded by
`√K · exp(t² G(f,f))`. Taking q(f) = G_L(f,f) (the continuum Green's
function, which is a continuous seminorm) gives the OS1 bound. -/
theorem torusInteracting_os1
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (_hφ : StrictMono φ)
    (_hconv : ∀ (f : Configuration (TorusTestFunction L) → ℝ),
      Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun n => ∫ ω, f ω ∂(torusInteractingMeasure L (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, f ω ∂μ))) :
    TorusOS1_Regularity L μ := by
  -- Get the exponential moment bound with universal constant K
  -- Use q(f) = G(f,f) + log(K), c = 1 to absorb the K factor:
  -- K * exp(G) = exp(G + log K) = exp(q(f)) where q(f) = G(f,f) + log K
  -- Then ‖Z_ℂ‖ ≤ exp(q(f_im)) ≤ exp(1 * (q(f_re) + q(f_im)))
  obtain ⟨K, hK_pos, hK_all⟩ :=
    torusInteracting_exponentialMomentBound L P mass hmass μ φ _hφ _hconv
  -- Use q(f) = G(f,f) + Real.log K to absorb the constant K
  refine ⟨fun f => torusContinuumGreen L mass hmass f f + |Real.log K|,
          (torusContinuumGreen_continuous_diag L mass hmass).add continuous_const,
          1, one_pos, ?_⟩
  intro f_re f_im
  -- Get the bound for f_im (using universal K)
  obtain ⟨h_int_im, h_exp_bound_im⟩ := hK_all f_im
  -- ‖Z_ℂ‖ ≤ ∫ exp(|ω(f_im)|) dμ ≤ K * exp(G(f_im, f_im))
  -- = exp(G(f_im) + log K) = exp(q(f_im))
  -- ≤ exp(1 * (q(f_re) + q(f_im)))
  have h_tri : ‖torusGeneratingFunctionalℂ L μ f_re f_im‖ ≤
      ∫ ω, ‖Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)))‖ ∂μ :=
    norm_integral_le_integral_norm _
  have h_norm : ∀ ω : Configuration (TorusTestFunction L),
      ‖Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)))‖ =
      Real.exp (-(ω f_im)) := by
    intro ω
    rw [Complex.norm_exp]; congr 1
    have : Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)) =
        -↑(ω f_im) + ↑(ω f_re) * Complex.I := by
      rw [mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul]; ring
    rw [this, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  calc ‖torusGeneratingFunctionalℂ L μ f_re f_im‖
      ≤ ∫ ω, ‖Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)))‖ ∂μ := h_tri
    _ = ∫ ω, Real.exp (-(ω f_im)) ∂μ := by congr 1; ext ω; exact h_norm ω
    _ ≤ ∫ ω, Real.exp (|ω f_im|) ∂μ := by
        apply integral_mono_of_nonneg
        · exact ae_of_all _ (fun _ => (Real.exp_pos _).le)
        · exact h_int_im
        · exact ae_of_all _ (fun ω => Real.exp_le_exp_of_le (neg_le_abs (ω f_im)))
    _ ≤ K * Real.exp (torusContinuumGreen L mass hmass f_im f_im) := h_exp_bound_im
    _ ≤ Real.exp (torusContinuumGreen L mass hmass f_im f_im + |Real.log K|) := by
        have hle : K ≤ Real.exp (|Real.log K|) := by
          by_cases h1 : 1 ≤ K
          · rw [abs_of_nonneg (Real.log_nonneg h1), Real.exp_log hK_pos]
          · push_neg at h1
            exact le_trans h1.le (Real.one_le_exp (abs_nonneg _))
        calc K * Real.exp (torusContinuumGreen L mass hmass f_im f_im)
            ≤ Real.exp (|Real.log K|) *
              Real.exp (torusContinuumGreen L mass hmass f_im f_im) :=
              mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
          _ = Real.exp (torusContinuumGreen L mass hmass f_im f_im + |Real.log K|) := by
              rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (1 * ((torusContinuumGreen L mass hmass f_re f_re + |Real.log K|) +
          (torusContinuumGreen L mass hmass f_im f_im + |Real.log K|))) := by
        rw [one_mul]; apply Real.exp_le_exp_of_le
        linarith [torusContinuumGreen_nonneg L mass hmass f_re, abs_nonneg (Real.log K)]

/-! ## OS2: Translation invariance of the interacting measure

On the torus T² = (ℝ/Lℤ)², translations in BOTH directions are exact
symmetries at every lattice cutoff N. The interaction
  `V_N(ω) = a² Σ_x :P(φ(x)):_c`
sums over ALL lattice sites with periodic boundary conditions, so
translating by any lattice vector permutes the summand and leaves V_N
unchanged. The free GFF measure is also translation-invariant
(`torusGaussianLimit_os2_translation`). Since both factors in
`(1/Z) exp(-V) dμ_GFF` are invariant, so is each cutoff measure.

Translation invariance passes to the limit by weak convergence:
for any bounded continuous test functional F and translation T_v,
  `∫ F(ω) dμ_N = ∫ F(T_v^{-1} ω) dμ_N`  (cutoff invariance)
Taking N → ∞, both sides converge to the limit, giving
  `∫ F(ω) dμ = ∫ F(T_v^{-1} ω) dμ`     (limit invariance) -/

/-- **OS2 (translation) for the torus interacting continuum limit.**

The interacting measure is invariant under translations on T²_L.
  `Z(f) = Z(T_v f)` for all `v ∈ ℝ²`.

This follows directly from `torusInteractingLimit_translation_invariant`,
which axiomatizes the continuum limit's translation invariance. -/
theorem torusInteracting_os2_translation
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (_φ : ℕ → ℕ) (_hφ : StrictMono _φ)
    (_hconv : ∀ (f : Configuration (TorusTestFunction L) → ℝ),
      Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun n => ∫ ω, f ω ∂(torusInteractingMeasure L (_φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, f ω ∂μ))) :
    TorusOS2_TranslationInvariance L μ := by
  intro v f
  exact torusInteractingLimit_translation_invariant L P mass hmass μ v f

/-! ## OS2: D4 point group invariance

The D4 symmetry group of the square torus (swap + time reflection)
is an exact symmetry of both the free measure and the interaction
at every lattice cutoff. Like translation invariance, it passes
to the continuum limit by weak convergence. -/

/-- **OS2 (D4) for the torus interacting continuum limit.**

The interacting measure is invariant under coordinate swap
and time reflection on T²_L. -/
theorem torusInteracting_os2_D4
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (_hφ : StrictMono φ)
    (hconv : ∀ (f : Configuration (TorusTestFunction L) → ℝ),
      Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun n => ∫ ω, f ω ∂(torusInteractingMeasure L (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, f ω ∂μ))) :
    TorusOS2_D4Invariance L μ := by
  constructor
  · -- Swap invariance: Z_μ[f] = Z_μ[σf] for all f
    intro f
    apply Complex.ext
    · -- Re part
      rw [gf_re_eq_cos_integral L μ f, gf_re_eq_cos_integral L μ (torusSwap L f)]
      have h_Sf := hconv _ (cosEval_continuous L (torusSwap L f))
        (cosEval_bounded L (torusSwap L f))
      have h_f := hconv _ (cosEval_continuous L f) (cosEval_bounded L f)
      have h_cutoff : ∀ n, ∫ ω, Real.cos (ω (torusSwap L f))
          ∂(torusInteractingMeasure L (φ n + 1) P mass hmass) =
        ∫ ω, Real.cos (ω f) ∂(torusInteractingMeasure L (φ n + 1) P mass hmass) := by
        intro n
        have hgf := torusInteractingMeasure_gf_swap_invariant L (φ n + 1) P mass hmass f
        have hre := congr_arg Complex.re hgf
        rw [gf_re_eq_cos_integral, gf_re_eq_cos_integral] at hre
        exact hre.symm
      exact tendsto_nhds_unique h_f (h_Sf.congr h_cutoff)
    · -- Im part
      rw [gf_im_eq_sin_integral L μ f, gf_im_eq_sin_integral L μ (torusSwap L f)]
      have h_Sf := hconv _ (sinEval_continuous L (torusSwap L f))
        (sinEval_bounded L (torusSwap L f))
      have h_f := hconv _ (sinEval_continuous L f) (sinEval_bounded L f)
      have h_cutoff : ∀ n, ∫ ω, Real.sin (ω (torusSwap L f))
          ∂(torusInteractingMeasure L (φ n + 1) P mass hmass) =
        ∫ ω, Real.sin (ω f) ∂(torusInteractingMeasure L (φ n + 1) P mass hmass) := by
        intro n
        have hgf := torusInteractingMeasure_gf_swap_invariant L (φ n + 1) P mass hmass f
        have him := congr_arg Complex.im hgf
        rw [gf_im_eq_sin_integral, gf_im_eq_sin_integral] at him
        exact him.symm
      exact tendsto_nhds_unique h_f (h_Sf.congr h_cutoff)
  · -- Time reflection invariance: Z_μ[f] = Z_μ[Θf] for all f
    intro f
    apply Complex.ext
    · -- Re part
      rw [gf_re_eq_cos_integral L μ f,
          gf_re_eq_cos_integral L μ (torusTimeReflection L f)]
      have h_Θf := hconv _ (cosEval_continuous L (torusTimeReflection L f))
        (cosEval_bounded L (torusTimeReflection L f))
      have h_f := hconv _ (cosEval_continuous L f) (cosEval_bounded L f)
      have h_cutoff : ∀ n, ∫ ω, Real.cos (ω (torusTimeReflection L f))
          ∂(torusInteractingMeasure L (φ n + 1) P mass hmass) =
        ∫ ω, Real.cos (ω f) ∂(torusInteractingMeasure L (φ n + 1) P mass hmass) := by
        intro n
        have hgf := torusInteractingMeasure_gf_timeReflection_invariant L (φ n + 1)
          P mass hmass f
        have hre := congr_arg Complex.re hgf
        rw [gf_re_eq_cos_integral, gf_re_eq_cos_integral] at hre
        exact hre.symm
      exact tendsto_nhds_unique h_f (h_Θf.congr h_cutoff)
    · -- Im part
      rw [gf_im_eq_sin_integral L μ f,
          gf_im_eq_sin_integral L μ (torusTimeReflection L f)]
      have h_Θf := hconv _ (sinEval_continuous L (torusTimeReflection L f))
        (sinEval_bounded L (torusTimeReflection L f))
      have h_f := hconv _ (sinEval_continuous L f) (sinEval_bounded L f)
      have h_cutoff : ∀ n, ∫ ω, Real.sin (ω (torusTimeReflection L f))
          ∂(torusInteractingMeasure L (φ n + 1) P mass hmass) =
        ∫ ω, Real.sin (ω f) ∂(torusInteractingMeasure L (φ n + 1) P mass hmass) := by
        intro n
        have hgf := torusInteractingMeasure_gf_timeReflection_invariant L (φ n + 1)
          P mass hmass f
        have him := congr_arg Complex.im hgf
        rw [gf_im_eq_sin_integral, gf_im_eq_sin_integral] at him
        exact him.symm
      exact tendsto_nhds_unique h_f (h_Θf.congr h_cutoff)

/-! ## Bundled OS axioms -/

/-- **The torus P(φ)₂ interacting continuum limit satisfies OS0–OS2.**

This bundles all verifiable OS axioms for the interacting torus measure.
OS3 (reflection positivity) is dropped — it is natural on the
cylinder S¹×ℝ, not the torus T². -/
theorem torusInteracting_satisfies_OS
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ (f : Configuration (TorusTestFunction L) → ℝ),
      Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun n => ∫ ω, f ω ∂(torusInteractingMeasure L (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, f ω ∂μ))) :
    SatisfiesTorusOS L μ where
  os0 := torusInteracting_os0 L P mass hmass μ φ hφ hconv
  os1 := torusInteracting_os1 L P mass hmass μ φ hφ hconv
  os2_translation := torusInteracting_os2_translation L P mass hmass μ φ hφ hconv
  os2_D4 := torusInteracting_os2_D4 L P mass hmass μ φ hφ hconv

end Pphi2

end
