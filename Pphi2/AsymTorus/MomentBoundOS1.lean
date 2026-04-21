/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Green-Function-Controlled Exponential Moment Bound

Defines a **strengthened OS1 clause** for asymmetric torus measures,
replacing the abstract continuous-`q` form of `AsymTorusOS1_Regularity`
with a bound controlled by the torus Green's function `asymTorusContinuumGreen`:

  `∫ exp(|ω f|) dμ ≤ K · exp(C · G_Lt(f, f))`.

The abstract OS1 form is too weak to yield the uniform-in-`Lt` cylinder
bounds required by the Route B′ IR-limit axioms
(`cylinderIR_uniform_second_moment`, `cylinderIR_uniform_exponential_moment`,
`cylinderIR_os3`): it allows `q_torus` to be any continuous function, including
ones with explicit `Lt` growth. The Green-bounded form combines cleanly with
`torusGreen_uniform_bound` (from gaussian-field) to give the uniform cylinder
bound after pullback.

## Main definitions

- `MeasureHasGreenMomentBound mass K C μ` — the per-measure predicate:
  `∫ exp(|ω f|) dμ ≤ K · exp(C · G_Lt(f, f))` for all test functions `f`.

## Main results

- `cylinderPullback_expMoment_eq` — pullback identity for `exp(|ωf|)`.
- `cylinderPullback_expMoment_le_green` — after pullback, the bound above
  transfers with `G_Lt(embed f, embed f)` on the right.
- `cylinderPullback_expMoment_uniform_bound` — composing with
  `torusGreen_uniform_bound` yields the uniform-in-`Lt` cylinder-seminorm
  bound in the exact form required by `cylinderIR_uniform_exponential_moment`.

These results give a clean reduction of the Route B′ IR-limit exponential
moment axiom to the (still-to-be-proved) property that the concrete UV-limit
asymmetric torus measures satisfy `MeasureHasGreenMomentBound` with constants
uniform in `Lt`. That uniform property can be established by refactoring
`asymTorusInteractingMeasure_exponentialMomentBound_cutoff` to bound the
lattice second moment by the continuum torus Green's function instead of by
the Lt-dependent Sobolev seminorm currently used.

## References

- Glimm-Jaffe §19.4 (Nelson's estimate in volume-independent form)
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. VIII
-/

import Pphi2.IRLimit.CylinderEmbedding
import Pphi2.AsymTorus.AsymTorusEmbedding
import Cylinder.MethodOfImages

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory

variable (Ls : ℝ) [hLs : Fact (0 < Ls)]

/-! ## The Green-function-controlled OS1 clause -/

/-- **OS1 with Green-function-controlled exponential moments.**

A strengthening of `AsymTorusOS1_Regularity` in which the continuous bound
`q` is replaced by the torus Green's function `asymTorusContinuumGreen`
with explicit constants `K, C`:

  `∫ exp(|ω f|) dμ ≤ K · exp(C · G_Lt(f, f))`.

This form composes cleanly with `torusGreen_uniform_bound` to yield
uniform-in-`Lt` bounds after the cylinder pullback — the abstract
`AsymTorusOS1_Regularity` form does not (see docstrings in `IRLimit/`).

The constants `K, C` are intended to be **uniform across the family of
UV-limit measures indexed by `Lt`**; this uniformity is what makes the
eventual derivation of `cylinderIR_uniform_exponential_moment` work. The
uniformity is not encoded in this per-measure predicate; the IR-limit
axioms expose it externally as `∃ K C, ∀ Lt …`.

Proof that the concrete UV-limit interacting measures satisfy this form
reduces to replacing the Sobolev-seminorm RHS in
`asymTorusInteractingMeasure_exponentialMomentBound_cutoff` with a
continuum-Green-function RHS, then passing to the UV limit. -/
def MeasureHasGreenMomentBound
    {Lt : ℝ} [Fact (0 < Lt)]
    (mass : ℝ) (hmass : 0 < mass)
    (K C : ℝ)
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls))) : Prop :=
  ∀ f : AsymTorusTestFunction Lt Ls,
    Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
      Real.exp (|ω f|)) μ ∧
    ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
      Real.exp (|ω f|) ∂μ ≤
    K * Real.exp (C * GaussianField.asymTorusContinuumGreen Ls Lt mass hmass f f)

/-! ## Pullback identity for exponential moments -/

/-- Exponential moment under the cylinder pullback equals exponential moment of
the embedded test function under the torus measure — the `exp(|ωf|)` analogue of
`cylinderPullbackMeasure_integral_sq`. Also transfers integrability. -/
theorem cylinderPullback_expMoment_eq
    (Lt : ℝ) [Fact (0 < Lt)]
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (f : CylinderTestFunction Ls)
    (h_int : Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
      Real.exp (|ω (cylinderToTorusEmbed Lt Ls f)|)) μ) :
    Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
      Real.exp (|ω f|)) (cylinderPullbackMeasure Lt Ls μ) ∧
    ∫ ω : Configuration (CylinderTestFunction Ls),
      Real.exp (|ω f|) ∂(cylinderPullbackMeasure Lt Ls μ) =
    ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
      Real.exp (|ω (cylinderToTorusEmbed Lt Ls f)|) ∂μ := by
  unfold cylinderPullbackMeasure
  have hmeas : Measurable (cylinderPullback Lt Ls) :=
    configuration_measurable_of_eval_measurable _
      (fun φ => configuration_eval_measurable _)
  have hexp_sm : StronglyMeasurable
      (fun ω : Configuration (CylinderTestFunction Ls) => Real.exp (|ω f|)) :=
    (Real.measurable_exp.comp
      (configuration_eval_measurable f).abs).stronglyMeasurable
  refine ⟨?_, ?_⟩
  · -- Integrability under the pushforward via integrable_map_measure
    rw [integrable_map_measure hexp_sm.aestronglyMeasurable hmeas.aemeasurable]
    -- Composition with cylinderPullback yields ω ↦ exp(|(pullback ω) f|) =
    -- ω ↦ exp(|ω (embed f)|), agreeing with `h_int`.
    refine h_int.congr (Filter.Eventually.of_forall ?_)
    intro ω; simp [cylinderPullback_eval]
  · rw [integral_map_of_stronglyMeasurable hmeas hexp_sm]
    simp_rw [cylinderPullback_eval]

/-! ## Bridge: Green moment bound ⟹ cylinder bound (per Lt) -/

/-- If the torus measure `μ` satisfies the Green-controlled exponential moment
bound with constants `(K, C)`, the cylinder pullback inherits the bound with the
Green's function evaluated at the embedded test function. -/
theorem cylinderPullback_expMoment_le_green
    {Lt : ℝ} [Fact (0 < Lt)]
    (mass : ℝ) (hmass : 0 < mass)
    (K C : ℝ)
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (hμ : MeasureHasGreenMomentBound Ls mass hmass K C μ)
    (f : CylinderTestFunction Ls) :
    Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
      Real.exp (|ω f|)) (cylinderPullbackMeasure Lt Ls μ) ∧
    ∫ ω : Configuration (CylinderTestFunction Ls),
      Real.exp (|ω f|) ∂(cylinderPullbackMeasure Lt Ls μ) ≤
    K * Real.exp (C * GaussianField.asymTorusContinuumGreen Ls Lt mass hmass
      (cylinderToTorusEmbed Lt Ls f) (cylinderToTorusEmbed Lt Ls f)) := by
  obtain ⟨h_int_torus, h_bd_torus⟩ := hμ (cylinderToTorusEmbed Lt Ls f)
  obtain ⟨h_int_cyl, h_eq⟩ :=
    cylinderPullback_expMoment_eq Ls Lt μ f h_int_torus
  exact ⟨h_int_cyl, h_eq.le.trans h_bd_torus⟩

/-! ## Uniform cylinder bound via method of images

Composition with `torusGreen_uniform_bound` (proved in gaussian-field) yields
the uniform-in-`Lt` cylinder-seminorm bound that matches the statement of
`cylinderIR_uniform_exponential_moment` — once we assume the `Lt`-family of
measures all satisfy `MeasureHasGreenMomentBound` with the **same** constants
`K, C`. -/

/-- Uniform cylinder exponential moment bound from a uniform-in-Lt
Green-controlled moment bound on the torus family.

This is the target theorem: given constants `K, C` and the assumption that
every measure `μ` in a family indexed by `Lt ≥ 1` satisfies
`MeasureHasGreenMomentBound mass hmass K C μ`, produce a continuous cylinder
seminorm `q` and constants such that the pullback exponential moment is
bounded uniformly in `Lt`.

This is exactly the content of `cylinderIR_uniform_exponential_moment`,
conditional on having established the uniform Green-moment bound for the
UV-limit family. -/
theorem cylinderPullback_expMoment_uniform_bound
    (mass : ℝ) (hmass : 0 < mass)
    (K C : ℝ) (hK_pos : 0 < K) (hC_pos : 0 < C) :
    ∃ (K' C' : ℝ) (q : Seminorm ℝ (CylinderTestFunction Ls)),
    0 < K' ∧ 0 < C' ∧ Continuous q ∧
    ∀ (Lt : ℝ) [Fact (0 < Lt)] (_ : 1 ≤ Lt)
      (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
      [IsProbabilityMeasure μ]
      (_ : MeasureHasGreenMomentBound Ls mass hmass K C μ)
      (f : CylinderTestFunction Ls),
    Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
      Real.exp (|ω f|)) (cylinderPullbackMeasure Lt Ls μ) ∧
    ∫ ω : Configuration (CylinderTestFunction Ls),
      Real.exp (|ω f|) ∂(cylinderPullbackMeasure Lt Ls μ) ≤
    K' * Real.exp (C' * q f ^ 2) := by
  -- Method of images gives a cylinder seminorm controlling G_Lt uniformly
  obtain ⟨C_MI, hC_MI_pos, q, hq_cont, hq_bound⟩ :=
    torusGreen_uniform_bound (Ls := Ls) mass hmass
  refine ⟨K, C * C_MI, q, hK_pos, mul_pos hC_pos hC_MI_pos, hq_cont, ?_⟩
  intro Lt _ hLt μ _ hμ f
  have h_green_le : GaussianField.asymTorusContinuumGreen Ls Lt mass hmass
      (cylinderToTorusEmbed Lt Ls f) (cylinderToTorusEmbed Lt Ls f) ≤
      C_MI * q f ^ 2 := hq_bound Lt hLt f
  obtain ⟨h_int, h_bd⟩ := cylinderPullback_expMoment_le_green
    Ls mass hmass K C μ hμ f
  refine ⟨h_int, h_bd.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hK_pos.le
  apply Real.exp_le_exp_of_le
  have hC_nn : 0 ≤ C := hC_pos.le
  calc C * GaussianField.asymTorusContinuumGreen Ls Lt mass hmass
        (cylinderToTorusEmbed Lt Ls f) (cylinderToTorusEmbed Lt Ls f)
      ≤ C * (C_MI * q f ^ 2) :=
        mul_le_mul_of_nonneg_left h_green_le hC_nn
    _ = C * C_MI * q f ^ 2 := by ring

end Pphi2

end
