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

/-! ## Step II — strict positivity of the quartic kernel sum -/

/-- The quartic kernel sum `∑_z (C_a f)(z)⁴` is nonnegative (a sum of fourth powers); hence the
first-order slope `u₄'(0) = −6 a^d · (this)` is `≤ 0`. -/
lemma quartic_kernel_sum_nonneg (a mass : ℝ) (f : FinLatticeField d N) :
    0 ≤ ∑ z, (∑ x, f x * gffPositionCovariance d N a mass x z) ^ 4 :=
  Finset.sum_nonneg fun z _ => by positivity

/-- **Step II (positivity).** If the smeared covariance `C_a f` is not identically zero, the quartic
kernel sum is strictly positive. -/
lemma quartic_kernel_sum_pos (a mass : ℝ) (f : FinLatticeField d N)
    (hf : ∃ z, (∑ x, f x * gffPositionCovariance d N a mass x z) ≠ 0) :
    0 < ∑ z, (∑ x, f x * gffPositionCovariance d N a mass x z) ^ 4 := by
  obtain ⟨z₀, hz₀⟩ := hf
  exact Finset.sum_pos' (fun z _ => by positivity) ⟨z₀, Finset.mem_univ z₀, by positivity⟩

/-- **Step II (strict slope).** When `C_a f ≢ 0`, the first-order slope `u₄'(0) = −6 a^d · ∑(C_a f)⁴`
is strictly negative (`0 < a`). -/
lemma u4_slope_neg (a mass : ℝ) (ha : 0 < a) (f : FinLatticeField d N)
    (hf : ∃ z, (∑ x, f x * gffPositionCovariance d N a mass x z) ≠ 0) :
    -6 * a ^ d * ∑ z, (∑ x, f x * gffPositionCovariance d N a mass x z) ^ 4 < 0 := by
  have hsum := quartic_kernel_sum_pos d N a mass f hf
  have had : 0 < a ^ d := pow_pos ha d
  nlinarith [hsum, had]

/-- **Step II (witness).** There is a test function — the single-site `δ_{z₀}` — whose first-order
slope is strictly negative: `C_a δ_{z₀}(z₀) = gffPositionCovariance z₀ z₀ = wickConstant > 0`. -/
lemma exists_u4_slope_neg (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    ∃ f : FinLatticeField d N,
      -6 * a ^ d * ∑ z, (∑ x, f x * gffPositionCovariance d N a mass x z) ^ 4 < 0 := by
  classical
  obtain ⟨z₀⟩ : Nonempty (FinLatticeSites d N) := inferInstance
  refine ⟨fun x => if x = z₀ then (1 : ℝ) else 0, u4_slope_neg d N a mass ha _ ⟨z₀, ?_⟩⟩
  show (∑ x, (if x = z₀ then (1 : ℝ) else 0) * gffPositionCovariance d N a mass x z₀) ≠ 0
  have hval : (∑ x, (if x = z₀ then (1 : ℝ) else 0) * gffPositionCovariance d N a mass x z₀)
      = gffPositionCovariance d N a mass z₀ z₀ := by
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hval, ← wickConstant_eq_gffPositionCovariance d N a mass ha hmass z₀]
  exact ne_of_gt (wickConstant_pos d N a mass ha hmass)

/-! ## Step III — first-order sign control: `u₄(g) < 0` just right of `g = 0` -/

open Filter Topology in
/-- **General one-sided first-order sign lemma.** A function with value `0` at `0` and a strictly
negative right-derivative there is strictly negative just to the right of `0`. (The `o(g)` from
`HasDerivWithinAt` is all that is needed — no quantitative remainder bound.) -/
lemma exists_pos_lt_zero_of_hasDerivWithinAt_neg {φ : ℝ → ℝ} {D : ℝ}
    (hderiv : HasDerivWithinAt φ D (Ici 0) 0) (hD : D < 0) (h0 : φ 0 = 0) :
    ∃ g : ℝ, 0 < g ∧ φ g < 0 := by
  have hslope : Tendsto (slope φ 0) (𝓝[Ici 0 \ {0}] 0) (𝓝 D) :=
    hasDerivWithinAt_iff_tendsto_slope.mp hderiv
  rw [Set.Ici_diff_left] at hslope
  have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), φ y < 0 := by
    have hslopeneg : ∀ᶠ y in 𝓝[>] (0 : ℝ), slope φ 0 y < 0 := hslope.eventually_lt_const hD
    filter_upwards [hslopeneg, self_mem_nhdsWithin] with y hy hypos
    have hypos' : (0 : ℝ) < y := hypos
    rw [slope_def_field, h0, sub_zero, sub_zero] at hy
    have := mul_neg_of_neg_of_pos hy hypos'
    rwa [div_mul_cancel₀ _ (ne_of_gt hypos')] at this
  obtain ⟨y, hyneg, hypos⟩ := (hev.and self_mem_nhdsWithin).exists
  exact ⟨y, hypos, hyneg⟩

/-- **`u₄(0) = 0`** (the free-field baseline / Isserlis): at `g = 0` the Gibbs family is the free
GFF, whose connected four-point vanishes. -/
theorem u4_at_zero (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (P : InteractionPolynomial)
    (f : FinLatticeField d N) :
    (∫ ω, (ω f) ^ 4 * Real.exp (-(0 * interactionFunctional d N P a mass ω))
          ∂(latticeGaussianMeasure d N a mass ha hmass)) /
        (∫ ω, Real.exp (-(0 * interactionFunctional d N P a mass ω))
          ∂(latticeGaussianMeasure d N a mass ha hmass))
      - 3 * ((∫ ω, (ω f) ^ 2 * Real.exp (-(0 * interactionFunctional d N P a mass ω))
            ∂(latticeGaussianMeasure d N a mass ha hmass)) /
          (∫ ω, Real.exp (-(0 * interactionFunctional d N P a mass ω))
            ∂(latticeGaussianMeasure d N a mass ha hmass))) ^ 2 = 0 := by
  have hZ : (∫ ω, Real.exp (-(0 * interactionFunctional d N P a mass ω))
      ∂(latticeGaussianMeasure d N a mass ha hmass)) = 1 :=
    partitionFn_zero d N a mass ha hmass P
  have h4 : (∫ ω, (ω f) ^ 4 * Real.exp (-(0 * interactionFunctional d N P a mass ω))
        ∂(latticeGaussianMeasure d N a mass ha hmass)) = ∫ ω, (ω f) ^ 4
        ∂(latticeGaussianMeasure d N a mass ha hmass) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_); simp
  have h2 : (∫ ω, (ω f) ^ 2 * Real.exp (-(0 * interactionFunctional d N P a mass ω))
        ∂(latticeGaussianMeasure d N a mass ha hmass)) = ∫ ω, (ω f) ^ 2
        ∂(latticeGaussianMeasure d N a mass ha hmass) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_); simp
  rw [hZ, h4, h2, div_one, div_one, latticeFourthMoment_eq d N a mass ha hmass f]; ring

/-- **Step III (lattice weak-coupling non-triviality).** For any test function with `C_a f ≢ 0`
there is a coupling `g > 0` at which the Gibbs-family connected four-point is strictly negative:
`u₄(g) < 0`. Combined with `exists_u4_slope_neg`, the interacting lattice theory is non-Gaussian at
weak coupling. -/
theorem exists_pos_u4_neg (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (P : InteractionPolynomial)
    (hP : P.n = 4) (f : FinLatticeField d N)
    (hf : ∃ z, (∑ x, f x * gffPositionCovariance d N a mass x z) ≠ 0) :
    ∃ g : ℝ, 0 < g ∧
      (∫ ω, (ω f) ^ 4 * Real.exp (-(g * interactionFunctional d N P a mass ω))
            ∂(latticeGaussianMeasure d N a mass ha hmass)) /
          (∫ ω, Real.exp (-(g * interactionFunctional d N P a mass ω))
            ∂(latticeGaussianMeasure d N a mass ha hmass))
        - 3 * ((∫ ω, (ω f) ^ 2 * Real.exp (-(g * interactionFunctional d N P a mass ω))
              ∂(latticeGaussianMeasure d N a mass ha hmass)) /
            (∫ ω, Real.exp (-(g * interactionFunctional d N P a mass ω))
              ∂(latticeGaussianMeasure d N a mass ha hmass))) ^ 2 < 0 :=
  exists_pos_lt_zero_of_hasDerivWithinAt_neg
    (u4_hasDerivWithinAt d N a mass ha hmass P hP f)
    (u4_slope_neg d N a mass ha f hf)
    (u4_at_zero d N a mass ha hmass P f)

/-! ## Quantitative uniform upgrade (interface for the `N`-uniform discharge)

The qualitative `∃ g>0, u₄(g)<0` (above) does not control the threshold `g` uniformly in the lattice
size `N`. The general lemma below is the quantitative interface: given a function `φ` with `φ 0 = 0`,
a derivative obeying an **affine upper bound** `φ'(t) ≤ -s + K·t` on `[0, g₀]`, and any `g` with
`K·g ≤ s/2`, one gets `φ g ≤ -(s/2)·g`. The point: if `s` (leading-slope strength), `K` (a uniform
second-order/`O(g²)` constant), and `g₀` are all **uniform in `N`** — `s` from the leading term
`6 a²∑(C_a f)⁴` bounded below, `K` from the Nelson chaos bounds on `⟨|(φf)ⁿ V^k|⟩₀` (`V ≥ -L²A`,
`Z_g ≥ 1` uniform) — then `c := (s/2)·g` is uniform in `N`, which is exactly the headline axiom
`torus_weakCoupling_lattice_connectedFourPoint_strictNeg`. -/

/-- **Quantitative one-sided bound (MVT).** If `φ 0 = 0` and `φ'(t) ≤ -s + K·t` on `[0, g₀]`, then for
any `g ∈ (0, g₀]` with `K·g ≤ s/2`, `φ g ≤ -(s/2)·g`. (No second-derivative/`C²` hypothesis — only an
affine bound on the first derivative, which the Nelson remainder estimate supplies.) -/
lemma deriv_affine_bound_neg {φ φ' : ℝ → ℝ} {s K g₀ : ℝ}
    (h0 : φ 0 = 0) (hderiv : ∀ t ∈ Icc 0 g₀, HasDerivAt φ (φ' t) t)
    (hbound : ∀ t ∈ Icc 0 g₀, φ' t ≤ -s + K * t) (hK : 0 ≤ K)
    {g : ℝ} (hg : 0 < g) (hgg₀ : g ≤ g₀) (hKg : K * g ≤ s / 2) :
    φ g ≤ -(s / 2) * g := by
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope φ φ' hg
    (fun t ht => (hderiv t ⟨ht.1, ht.2.trans hgg₀⟩).continuousAt.continuousWithinAt)
    (fun x hx => hderiv x ⟨le_of_lt hx.1, (le_of_lt hx.2).trans hgg₀⟩)
  rw [h0, sub_zero, sub_zero] at hξeq
  have hφg : φ g = φ' ξ * g := by rw [hξeq, div_mul_cancel₀ _ (ne_of_gt hg)]
  have hξle : φ' ξ ≤ -s + K * ξ := hbound ξ ⟨le_of_lt hξ.1, (le_of_lt hξ.2).trans hgg₀⟩
  have hKξ : K * ξ ≤ K * g := mul_le_mul_of_nonneg_left (le_of_lt hξ.2) hK
  have : φ' ξ ≤ -(s / 2) := by linarith [hξle, hKξ, hKg]
  rw [hφg]
  exact mul_le_mul_of_nonneg_right this (le_of_lt hg)

end Pphi2
