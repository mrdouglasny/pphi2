/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.InteractingMeasure.ConnectedCorrelatorDerivative
import Pphi2.InteractingMeasure.InteractionFourPoint
import Pphi2.InteractingMeasure.FieldRedefinition

/-!
# First-order connected four-point of the coupling family (u₄ step 2c, brick 5)

The cumulant→Wick finale. For the normalised-moment connected four-point
`u₄(g) = ⟨φ(f)⁴⟩_g − 3⟨φ(f)²⟩²_g` of the Gibbs family `μ_g`, the right-derivative at `g = 0` is
`u₄'(0) = −6·a^d·∑_z (C_a f)(z)⁴ < 0`:

* assemble `u₄'(0) = M₄'(0) − 6 M₂(0) M₂'(0)` from brick 4 (`normalizedMoment_hasDerivWithinAt`) via
  the product rule;
* `M₂(0) = ∫(ω f)²` (the free variance), `M₂'(0) = −⟨(ω f)²;V⟩^c`, `M₄'(0) = −⟨(ω f)⁴;V⟩^c`;
* reduce via Isserlis `∫(ω f)⁴ = 3(∫(ω f)²)²` (`connectedFourPoint_gaussianMeasure_eq_zero`) and the
  variance bridge `∫(ω f)² = gffSmearedCovariance f f` (`gff_wickPower_two_smeared_inner` at `n=m=1`);
* identify `M₄'(0) − 6 M₂(0) M₂'(0) = −∫ :φ(f)⁴:·V` and apply step 2b
  (`wickFourth_interaction_inner_quartic`).
-/

namespace Pphi2

open MeasureTheory GaussianField Set

variable (d N : ℕ) [NeZero N]

/-- The degree-4 univariate Wick (Hermite) monomial: `:x⁴:_c = x⁴ − 6c x² + 3c²`. -/
lemma wickMonomial_four_eq (c x : ℝ) :
    _root_.wickMonomial 4 c x = x ^ 4 - 6 * c * x ^ 2 + 3 * c ^ 2 := by
  have e2 := _root_.wickMonomial_succ_succ 0 c x
  have e3 := _root_.wickMonomial_succ_succ 1 c x
  have e4 := _root_.wickMonomial_succ_succ 2 c x
  simp only [Nat.reduceAdd, _root_.wickMonomial_one, _root_.wickMonomial_zero] at e2 e3 e4
  rw [e4, e3, e2]; push_cast; ring

/-- **Variance bridge.** The free lattice second moment is the smeared covariance:
`∫(ω f)² dμ_GFF = gffSmearedCovariance f f`. (The `n=m=1` case of the smeared Wick kernel.) -/
lemma latticeSecondMoment_eq_smearedCovariance (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : FinLatticeField d N) :
    (∫ ω, (ω f) ^ 2 ∂(latticeGaussianMeasure d N a mass ha hmass))
      = gffSmearedCovariance d N a mass f f := by
  have h := GaussianField.gff_wickPower_two_smeared_inner d N a mass ha hmass 1 1 f f
  simp only [_root_.wickMonomial_one, if_true, Nat.factorial_one, Nat.cast_one, pow_one,
    one_mul] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)

/-- **Isserlis / Wick** for the free lattice field: `∫(ω f)⁴ = 3(∫(ω f)²)²`. -/
lemma latticeFourthMoment_eq (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : FinLatticeField d N) :
    (∫ ω, (ω f) ^ 4 ∂(latticeGaussianMeasure d N a mass ha hmass))
      = 3 * (∫ ω, (ω f) ^ 2 ∂(latticeGaussianMeasure d N a mass ha hmass)) ^ 2 := by
  have h := connectedFourPoint_gaussianMeasure_eq_zero (latticeCovarianceGJ d N a mass ha hmass) f
  unfold connectedFourPoint at h
  rw [sub_eq_zero] at h
  exact h

/-- **Brick 5 — first-order connected four-point of the coupling family.** The normalised-moment
connected four-point `u₄(g) = ⟨φ(f)⁴⟩_g − 3⟨φ(f)²⟩²_g` of `μ_g = Z_g⁻¹e^{−gV}μ_GFF` has
right-derivative `u₄'(0) = −6·a^d·∑_z (C_a f)(z)⁴ < 0` (the weak-coupling non-triviality slope). -/
theorem u4_hasDerivWithinAt (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (hP : P.n = 4) (f : FinLatticeField d N) :
    HasDerivWithinAt
      (fun g =>
        (∫ ω, (ω f) ^ 4 * Real.exp (-(g * interactionFunctional d N P a mass ω))
            ∂(latticeGaussianMeasure d N a mass ha hmass)) /
          (∫ ω, Real.exp (-(g * interactionFunctional d N P a mass ω))
            ∂(latticeGaussianMeasure d N a mass ha hmass))
        - 3 * ((∫ ω, (ω f) ^ 2 * Real.exp (-(g * interactionFunctional d N P a mass ω))
            ∂(latticeGaussianMeasure d N a mass ha hmass)) /
          (∫ ω, Real.exp (-(g * interactionFunctional d N P a mass ω))
            ∂(latticeGaussianMeasure d N a mass ha hmass))) ^ 2)
      (-6 * a ^ d * ∑ z, (∑ x, f x * gffPositionCovariance d N a mass x z) ^ 4)
      (Ici 0) 0 := by
  set μ := latticeGaussianMeasure d N a mass ha hmass with hμ
  set V := interactionFunctional d N P a mass with hVdef
  set σ := gffSmearedCovariance d N a mass f f with hσdef
  -- brick 4 at n = 4 and n = 2, assembled by the product rule
  have h4 := normalizedMoment_hasDerivWithinAt d N a mass ha hmass P f 4
  have h2 := normalizedMoment_hasDerivWithinAt d N a mass ha hmass P f 2
  have hu4 := h4.sub ((h2.pow 2).const_mul (3 : ℝ))
  -- `M₂(0) = ∫(ω f)²`
  have hM20 : (∫ ω, (ω f) ^ 2 * Real.exp (-((0 : ℝ) * V ω)) ∂μ) /
        (∫ ω, Real.exp (-((0 : ℝ) * V ω)) ∂μ) = ∫ ω, (ω f) ^ 2 ∂μ := by
    rw [partitionFn_zero d N a mass ha hmass P, div_one]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_); simp
  -- `(ω f)^k · V` integrable, and `V` integrable (brick 1)
  have iV : ∀ k : ℕ, Integrable (fun ω => (ω f) ^ k * V ω) μ := by
    intro k
    refine (integrable_powMul_interaction d N a mass ha hmass P f k).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hVdef, interactionFunctional_eq_single]
  have iVraw : Integrable V μ := by simpa using iV 0
  -- variance bridge and Isserlis
  have hσm2 : σ = ∫ ω, (ω f) ^ 2 ∂μ :=
    (latticeSecondMoment_eq_smearedCovariance d N a mass ha hmass f).symm
  have hIss : (∫ ω, (ω f) ^ 4 ∂μ) = 3 * (∫ ω, (ω f) ^ 2 ∂μ) ^ 2 :=
    latticeFourthMoment_eq d N a mass ha hmass f
  -- step 2b, expanded into raw moments: `∫:φ⁴:V = ∫(ωf)⁴V − 6σ∫(ωf)²V + 3σ²∫V = 6a^d∑(Cf)⁴`
  have hexp : (∫ ω, (ω f) ^ 4 * V ω ∂μ) - 6 * σ * (∫ ω, (ω f) ^ 2 * V ω ∂μ)
        + 3 * σ ^ 2 * (∫ ω, V ω ∂μ)
      = 6 * a ^ d * ∑ z, (∑ x, f x * gffPositionCovariance d N a mass x z) ^ 4 := by
    have h2b : ∫ ω, _root_.wickMonomial 4 σ (ω f) * V ω ∂μ
        = 6 * a ^ d * ∑ z, (∑ x, f x * gffPositionCovariance d N a mass x z) ^ 4 := by
      have e : (fun ω => _root_.wickMonomial 4 σ (ω f) * V ω)
          = (fun ω => _root_.wickMonomial 4 σ (ω f) *
              (a ^ d * ∑ z, wickPolynomial P (wickConstant d N a mass) (ω (Pi.single z 1)))) := by
        funext ω; simp only [hVdef, interactionFunctional_eq_single]
      rw [e]
      exact wickFourth_interaction_inner_quartic d N a mass ha hmass P hP f
    rw [← h2b]
    have e1 : ∫ ω, _root_.wickMonomial 4 σ (ω f) * V ω ∂μ
        = ∫ ω, ((ω f) ^ 4 * V ω - 6 * σ * ((ω f) ^ 2 * V ω) + 3 * σ ^ 2 * V ω) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by
        dsimp only; rw [wickMonomial_four_eq]; ring)
    rw [e1, integral_add (f := fun ω => (ω f) ^ 4 * V ω - 6 * σ * ((ω f) ^ 2 * V ω))
        (g := fun ω => 3 * σ ^ 2 * V ω) ((iV 4).sub ((iV 2).const_mul (6 * σ)))
        (iVraw.const_mul (3 * σ ^ 2)),
      integral_sub (iV 4) ((iV 2).const_mul (6 * σ)), integral_const_mul, integral_const_mul]
  -- the value of the assembled derivative
  convert hu4 using 1
  rw [← hμ, ← hVdef, hM20]
  rw [hσm2] at hexp
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  linear_combination hexp - (∫ ω, V ω ∂μ) * hIss

end Pphi2
