/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.TorusContinuumLimit.TorusCouplingLimit
import Pphi2.TorusContinuumLimit.TorusNontriviality
import Pphi2.InteractingMeasure.U4AffineBound

/-!
# Route A headline: φ⁴₂ on T² is interacting at weak coupling (axiom-free)

Assembles the weak-coupling continuum-limit machinery (`TorusCouplingLimit`) with the proved lattice
negativity `lattice_u4_neg_uniform` into a THEOREM (no axiom): for some small coupling `g₀ > 0`,
the continuum limit of the coupling-`g₀` interacting torus measures is non-Gaussian
(`TorusIsInteractingStrict`, hence `TorusIsInteracting`).

The bridge from the engine (stated for the N-dependent constant lattice test function `1/card`) to a
**fixed** torus test function uses two facts:
* `u4` (the connected four-point) is degree-4 homogeneous in the test function (`u4_smul`);
* the constant torus test function `1 ⊗ 1` (`torusOne`) samples to `latticeTestFn = L² • (1/card)`
  (`latticeTestFn_torusOne`), exactly proportional to the engine's test function.

So `torusConnectedFourPoint(μ_{g₀,N}) (torusOne) = L⁸ · u4(1/card, g₀) ≤ −L⁸c` uniformly in `N`.

## Main results
* `u4_smul` — `u4 (c•φ) g = c⁴ · u4 φ g`.
* `latticeTestFn_torusOne` — `latticeTestFn L N (torusOne) = L² • (1/card)`.
* `torus_weakCoupling_connectedFourPoint_strictNeg` — uniform strict lattice bound at `torusOne`.
* `torus_pphi2_isInteractingStrict_weakCoupling` — the headline (axiom-free).
-/

namespace Pphi2

open MeasureTheory GaussianField Filter Topology

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Degree-4 homogeneity of `u4` in the test function -/

/-- `gibbsMoment` scales as `cⁿ` under `φ ↦ c • φ` (since `ω (c•φ) = c · ω φ`). -/
lemma gibbsMoment_smul (d N : ℕ) [NeZero N] (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (φ : FinLatticeField d N) (c : ℝ) (n : ℕ) (g : ℝ) :
    gibbsMoment d N a mass ha hmass P (c • φ) n g
      = c ^ n * gibbsMoment d N a mass ha hmass P φ n g := by
  unfold gibbsMoment
  have h : ∀ ω : Configuration (FinLatticeField d N),
      (ω (c • φ)) ^ n * Real.exp (-(g * interactionFunctional d N P a mass ω))
        = c ^ n * ((ω φ) ^ n * Real.exp (-(g * interactionFunctional d N P a mass ω))) := by
    intro ω; rw [map_smul, smul_eq_mul, mul_pow]; ring
  simp_rw [h]
  rw [integral_const_mul]

/-- `normalizedMoment` scales as `cⁿ` under `φ ↦ c • φ`. -/
lemma normalizedMoment_smul (d N : ℕ) [NeZero N] (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (φ : FinLatticeField d N) (c : ℝ) (n : ℕ) (g : ℝ) :
    normalizedMoment d N a mass ha hmass P (c • φ) n g
      = c ^ n * normalizedMoment d N a mass ha hmass P φ n g := by
  unfold normalizedMoment
  rw [gibbsMoment_smul, mul_div_assoc]

/-- **Degree-4 homogeneity of `u4` in the test function.** `u4 (c•φ) g = c⁴ · u4 φ g`. -/
lemma u4_smul (d N : ℕ) [NeZero N] (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (φ : FinLatticeField d N) (c : ℝ) (g : ℝ) :
    u4 d N a mass ha hmass P (c • φ) g = c ^ 4 * u4 d N a mass ha hmass P φ g := by
  unfold u4
  simp only [normalizedMoment_smul]
  ring

/-! ## The constant torus test function and its lattice sampling -/

/-- The constant function `1` on the circle `ℝ/Lℤ` as a `SmoothMap_Circle`. -/
def circleOne : SmoothMap_Circle L ℝ := ⟨fun _ => 1, fun _ => rfl, contDiff_const⟩

@[simp] lemma circleOne_apply (x : ℝ) : (circleOne L) x = 1 := rfl

/-- The constant torus test function `1 ⊗ 1`. -/
noncomputable def torusOne : TorusTestFunction L :=
  NuclearTensorProduct.pure (circleOne L) (circleOne L)

/-- `evalTorusAtSite` of the constant `1 ⊗ 1` is `√a · √a = a` (`a = circleSpacing`). -/
lemma evalTorusAtSite_torusOne (N : ℕ) [NeZero N] (x : FinLatticeSites 2 N) :
    evalTorusAtSite L N x (torusOne L) = circleSpacing L N := by
  unfold torusOne evalTorusAtSite
  rw [NuclearTensorProduct.evalCLM_pure]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    circleRestriction_apply, circleOne_apply, mul_one]
  exact Real.mul_self_sqrt (circleSpacing_pos L N).le

/-- **The constant torus test function samples to `L² • (1/card)`.** Its GJ-sampling at every site is
`a² = L²/card`, exactly `L²` times the engine's test function `1/card`. -/
lemma latticeTestFn_torusOne (N : ℕ) [NeZero N] :
    latticeTestFn L N (torusOne L)
      = (L ^ 2 : ℝ) • (fun _ : FinLatticeSites 2 N => (Fintype.card (FinLatticeSites 2 N) : ℝ)⁻¹) := by
  funext x
  have hcard : (Fintype.card (FinLatticeSites 2 N) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (FinLatticeSites 2 N) := Fintype.card_pos
    positivity
  have hvol := torus_volume_eq L 2 N
  show evalTorusAtSiteGJ L N x (torusOne L)
      = (L ^ 2 : ℝ) * (Fintype.card (FinLatticeSites 2 N) : ℝ)⁻¹
  rw [evalTorusAtSiteGJ, ContinuousLinearMap.smul_apply, smul_eq_mul, evalTorusAtSite_torusOne]
  -- a * a = a² = L² · card⁻¹
  rw [← sq]
  field_simp
  linarith [hvol]

/-! ## Coupling torus→lattice pull-back of the connected four-point -/

/-- Coupling analog of `torusConnectedFourPoint_eq_lattice`: the torus connected four-point of the
coupling-`g` measure equals the lattice connected four-point at the embedded test function. -/
theorem torusConnectedFourPoint_coupling_eq_lattice (N : ℕ) [NeZero N] (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) (g : ℝ) (f : TorusTestFunction L) :
    torusConnectedFourPoint L (torusInteractingMeasureCoupling L N P mass hmass g) f
      = connectedFourPoint (interactingLatticeMeasureCoupling 2 N P (circleSpacing L N) mass
          (circleSpacing_pos L N) hmass g) (latticeTestFn L N f) := by
  unfold torusConnectedFourPoint connectedFourPoint torusInteractingMeasureCoupling
  rw [integral_map (torusEmbedLift_measurable L N).aemeasurable
      ((configuration_eval_measurable f).pow_const 4).aestronglyMeasurable,
    integral_map (torusEmbedLift_measurable L N).aemeasurable
      ((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable]
  simp_rw [torusEmbedLift_eval_eq L N f]

/-- Coupling torus connected four-point as the lattice `u4` at coupling `g` (`g ≥ 0`). -/
theorem torusConnectedFourPoint_coupling_eq_u4 (N : ℕ) [NeZero N] (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) {g : ℝ} (hg : 0 ≤ g) (f : TorusTestFunction L) :
    torusConnectedFourPoint L (torusInteractingMeasureCoupling L N P mass hmass g) f
      = u4 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass P (latticeTestFn L N f) g := by
  rw [torusConnectedFourPoint_coupling_eq_lattice,
    connectedFourPoint_interactingLatticeMeasureCoupling_eq_u4 2 N (circleSpacing L N) mass
      (circleSpacing_pos L N) hmass P (latticeTestFn L N f) hg]

/-! ## Route A discharge: strict lattice negativity at the fixed test function `torusOne` -/

/-- **A6 — uniform strict lattice negativity at a fixed torus test function.** There are `g₀ ∈ (0,1]`
and `c' > 0` with `torusConnectedFourPoint (μ_{g₀,N}) (torusOne) ≤ −c'` for all `N` (uniform in the
UV cutoff). Reduces the engine's constant-test-function bound to the fixed `torusOne` via
4-homogeneity (`u4_smul`) and `latticeTestFn_torusOne`. -/
theorem torus_weakCoupling_connectedFourPoint_strictNeg
    (P : InteractionPolynomial) (hP : P.n = 4) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (g₀ : ℝ), 0 < g₀ ∧ g₀ ≤ 1 ∧ ∃ (c' : ℝ), 0 < c' ∧ ∀ (N : ℕ) [NeZero N],
      torusConnectedFourPoint L (torusInteractingMeasureCoupling L N P mass hmass g₀) (torusOne L)
        ≤ -c' := by
  obtain ⟨g₀, c, hg₀pos, hcpos, hg₀le1, hbound⟩ := lattice_u4_neg_uniform L mass hmass P hP
  have hLpos : (0 : ℝ) < L := hL.out
  refine ⟨g₀, hg₀pos, hg₀le1, L ^ 8 * c, by positivity, fun N _ => ?_⟩
  -- torusConnectedFourPoint(μ_{g₀,N}) torusOne = u4(latticeTestFn torusOne, g₀)
  rw [torusConnectedFourPoint_coupling_eq_u4 L N P mass hmass hg₀pos.le (torusOne L),
    latticeTestFn_torusOne L N, u4_smul]
  -- = (L²)⁴ · u4(1/card, g₀) ≤ L⁸ · (−c) = −(L⁸c)
  have hub := hbound N
  have hL8 : (0 : ℝ) ≤ (L ^ 2) ^ 4 := by positivity
  calc (L ^ 2) ^ 4 * u4 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass P
          (fun _ : FinLatticeSites 2 N => (Fintype.card (FinLatticeSites 2 N) : ℝ)⁻¹) g₀
      ≤ (L ^ 2) ^ 4 * (-c) := by exact mul_le_mul_of_nonneg_left hub hL8
    _ = -(L ^ 8 * c) := by ring

/-! ## Route A headline -/

/-- **The P(φ)₂ theory on T² is interacting at weak coupling — axiom-free.** There is a small
coupling `g₀ ∈ (0,1]` for which the continuum limit `μ` of the coupling-`g₀` interacting torus
measures is non-Gaussian: `TorusIsInteractingStrict μ` (the connected four-point is strictly negative
at `torusOne`), hence `TorusIsInteracting μ`. This discharges φ⁴₂ non-triviality at weak coupling
*without* the axiom `torus_weakCoupling_lattice_connectedFourPoint_strictNeg` and without the
continuum dilation (Route B). -/
theorem torus_pphi2_isInteractingStrict_weakCoupling
    (P : InteractionPolynomial) (hP : P.n = 4) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (g₀ : ℝ), 0 < g₀ ∧ g₀ ≤ 1 ∧
      ∃ (μ : Measure (Configuration (TorusTestFunction L))) (_ : IsProbabilityMeasure μ)
        (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ (h : Configuration (TorusTestFunction L) → ℝ),
          Continuous h → (∃ B, ∀ x, |h x| ≤ B) →
          Tendsto (fun n => ∫ ω, h ω ∂(torusInteractingMeasureCoupling L (φ n + 1) P mass hmass g₀))
            atTop (nhds (∫ ω, h ω ∂μ))) ∧
        TorusIsInteractingStrict L μ := by
  obtain ⟨g₀, hg₀pos, hg₀le1, c', hc'pos, hbound⟩ :=
    torus_weakCoupling_connectedFourPoint_strictNeg L P hP mass hmass
  obtain ⟨φ, μ, hφ, hprob, hconv⟩ :=
    torusInteractingLimitCoupling_exists L P mass hmass hg₀pos.le hg₀le1
  refine ⟨g₀, hg₀pos, hg₀le1, μ, hprob, φ, hφ, hconv, torusOne L, ?_⟩
  have htendsto :=
    torus_connectedFourPoint_tendsto_coupling L P mass hmass (torusOne L) hg₀pos.le hg₀le1 μ φ hφ hconv
  have hlim : torusConnectedFourPoint L μ (torusOne L) ≤ -c' :=
    le_of_tendsto htendsto (Filter.Eventually.of_forall fun n => hbound (φ n + 1))
  linarith [hlim]

end Pphi2
