/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.AsymTorus.AsymObsTrunc
import Pphi2.AsymTorus.AsymSpectralGap
import Pphi2.AsymTorus.AsymVarianceDischarge
import ReflectionPositivity.GroundMeasure
import ReflectionPositivity.GroundSemigroup
import ReflectionPositivity.GroundGap
import ReflectionPositivity.GroundSusceptibility

/-!
# Asym transfer GNS bridge instance (Layer-B2, Piece 2)

This file instantiates the upstream finite-periodic GNS/path-measure bridge for
the asymmetric torus transfer system.  The algebraic part is now concrete:

* the `L²(volume)` ground vector is exposed through a measurable pointwise
  representative `asymGroundStateRep`;
* the asym transfer data are packaged as `GroundSemigroupData` and
  `GroundGapData`;
* the Piece-1 truncated observable contract `asymSliceObsTruncContract` is fed
  to `pathMeasure_connected_*_finite_periodic_bound`;
* the resulting path-measure second-moment expression is connected back to the
  pphi2 interacting torus moment via `interacting_second_moment_eq_pathMeasure`.

The remaining analytic inputs are isolated as axioms with audit records:

* sign/representative normalization for the chosen Jentzsch basis vector;
* normalized-transfer global contraction and ground-isometry intertwining;
* the finite-periodic denominator and scalar remainder estimates.

These are exactly the model-specific GNS discharge obligations described in the
Route-A plan: they are not hidden in theorem hypotheses downstream.
-/

open MeasureTheory GaussianField ReflectionPositivity
open scoped BigOperators

namespace Pphi2

variable {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]

local notation "ν" => (volume : Measure (SpatialField Ns))

/-! ## Ground-state representative -/

/-- A measurable representative of the asym Jentzsch ground vector.  We use the
`AEStronglyMeasurable.mk` representative because upstream GNS data require an
honest function `SpatialField Ns → ℝ`, not just an `L²` class. -/
noncomputable def asymGroundStateRep
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    SpatialField Ns → ℝ :=
  (Lp.aestronglyMeasurable (asymGroundVector Nt Ns P a mass ha hmass)).mk
    (asymGroundVector Nt Ns P a mass ha hmass)

/-- The selected representative is measurable. -/
theorem asymGroundStateRep_measurable
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Measurable (asymGroundStateRep (Nt := Nt) (Ns := Ns) P a mass ha hmass) :=
  (Lp.aestronglyMeasurable
    (asymGroundVector Nt Ns P a mass ha hmass)).stronglyMeasurable_mk.measurable

/-- The selected representative equals the `L²` ground vector a.e. -/
theorem asymGroundVector_coeFn_eq_groundStateRep
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    (⇑(asymGroundVector Nt Ns P a mass ha hmass) : SpatialField Ns → ℝ)
      =ᵐ[ν] asymGroundStateRep (Nt := Nt) (Ns := Ns) P a mass ha hmass :=
  (Lp.aestronglyMeasurable
    (asymGroundVector Nt Ns P a mass ha hmass)).ae_eq_mk

/-- **Axiom (representative sign normalization).** The chosen measurable
representative of the Jentzsch ground vector is strictly positive a.e.

Discharge plan: refine `asymTransferGroundExcitedData` so its distinguished
Hilbert-basis vector is sign-normalized.  The generic Jentzsch proof already
establishes constant sign for top eigenvectors; the missing pphi2-side step is
transporting that sign choice through the stored spectral-data package. -/
axiom asymGroundStateRep_pos_ae
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    ∀ᵐ ψ ∂ν, 0 < asymGroundStateRep (Nt := Nt) (Ns := Ns) P a mass ha hmass ψ

/-- The measurable ground representative has total `L²(volume)` mass one. -/
theorem asymGroundStateRep_norm_integral_eq_one
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    ∫ ψ, (asymGroundStateRep (Nt := Nt) (Ns := Ns) P a mass ha hmass ψ) ^ 2 ∂ν = 1 := by
  set ΩL2 := asymGroundVector Nt Ns P a mass ha hmass
  set Ω := asymGroundStateRep (Nt := Nt) (Ns := Ns) P a mass ha hmass
  have hnorm : ‖ΩL2‖ ^ 2 = 1 := by
    rw [asymGroundVector_norm_eq_one (Nt := Nt) (Ns := Ns) P a mass ha hmass]
    norm_num
  have hL2 : ‖ΩL2‖ ^ 2 = ∫ ψ, (ΩL2 ψ) * (ΩL2 ψ) ∂ν := by
    rw [← real_inner_self_eq_norm_sq ΩL2, L2.inner_def]
    rfl
  have hae : (fun ψ => (ΩL2 ψ) * (ΩL2 ψ)) =ᵐ[ν] fun ψ => Ω ψ ^ 2 := by
    filter_upwards [asymGroundVector_coeFn_eq_groundStateRep
      (Nt := Nt) (Ns := Ns) P a mass ha hmass] with ψ hψ
    rw [hψ]
    ring
  calc
    ∫ ψ, Ω ψ ^ 2 ∂ν
        = ∫ ψ, (ΩL2 ψ) * (ΩL2 ψ) ∂ν := (integral_congr_ae hae).symm
    _ = ‖ΩL2‖ ^ 2 := hL2.symm
    _ = 1 := hnorm

/-- The ground measure from the asym representative is a probability measure. -/
noncomputable instance asymGroundStateRep_isProbabilityMeasure
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    IsProbabilityMeasure
      (groundMeasure ν (asymGroundStateRep (Nt := Nt) (Ns := Ns) P a mass ha hmass)) :=
  groundMeasure_isProbabilityMeasure ν
    (asymGroundStateRep (Nt := Nt) (Ns := Ns) P a mass ha hmass)
    (asymGroundStateRep_measurable (Nt := Nt) (Ns := Ns) P a mass ha hmass)
    (asymGroundStateRep_norm_integral_eq_one (Nt := Nt) (Ns := Ns) P a mass ha hmass)

/-! ## Model-specific GNS discharge axioms -/

/-- **Axiom (global normalized-transfer contraction).** The normalized asym
transfer is a contraction on all of `L²(volume)`.

The already-proved `asymTransferNormalized_gap` gives the strict contraction on
the vacuum-orthogonal complement.  This global bound follows from
self-adjoint positivity plus the Perron-Frobenius top-eigenvalue normalization;
the missing pphi2-side proof is the standard spectral-radius argument for the
compact self-adjoint transfer operator. -/
axiom asymTransferNormalized_contract
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    ∀ f : L2SpatialField Ns,
      ‖(((1 / asymTransferGroundEigenvalue Nt Ns P a mass ha hmass) •
          asymTransferOperatorCLM Nt Ns P a mass ha hmass) f)‖ ≤ ‖f‖

/-- **Axiom (ground isometry sends one to the selected ground vector).**

This is representative bookkeeping for `W 1 = Ω` after choosing the measurable
representative above.  It follows from `groundIsometry_coeFn`, the constant-one
representative, and `asymGroundVector_coeFn_eq_groundStateRep`; the proof is
routine but currently blocked by the upstream `mk` representative details. -/
axiom asymGroundStateRep_eq_groundIsometry_one
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    (letI : IsProbabilityMeasure
        (groundMeasure ν (asymGroundStateRep (Nt := Nt) (Ns := Ns) P a mass ha hmass)) :=
        asymGroundStateRep_isProbabilityMeasure (Nt := Nt) (Ns := Ns) P a mass ha hmass
      ;
      groundIsometry
        (asymGroundStateRep_measurable (Nt := Nt) (Ns := Ns) P a mass ha hmass)
        (Lp.const 2
          (groundMeasure ν (asymGroundStateRep (Nt := Nt) (Ns := Ns) P a mass ha hmass))
          (1 : ℝ))) =
      asymGroundVector Nt Ns P a mass ha hmass

/-- **Axiom (finite-periodic denominator lower bound).** The asym path
partition function dominates the ground eigenvalue contribution.

Discharge plan: identify `Ts.partition Nt` with the trace of the positive
compact transfer power and use the positive normalized top eigenvector
contribution `λ₀^Nt`. -/
axiom asymPartition_ground_bound
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    ∀ (n : ℕ) [NeZero n],
      (asymTransferGroundEigenvalue Nt Ns P a mass ha hmass) ^ n
        ≤ (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).partition n

/-- **Axiom (finite-periodic GNS remainder).** The scalar residual left by the
rank-one split, denominator correction, and finite-periodic one-point
corrections is bounded by `C_rem γ^n`.

Discharge plan: prove the signed-kernel remainder estimate from the explicit
Gaussian transfer kernel.  The expected route is an `L²`/Hilbert-Schmidt bound
for `kernelRemainder` plus the already-proved operator-norm decay bricks in
`AsymTraceBridge.lean`; if Mathlib's HS API remains insufficient, discharge via
a bespoke finite-dimensional kernel integral estimate on `SpatialField Ns`. -/
axiom asymFinitePeriodicBridge_remainder_bound
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hnorm : ∀ v : L2SpatialField Ns,
      @inner ℝ _ _ (asymGroundVector Nt Ns P a mass ha hmass) v = 0 →
        ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ ≤ γ * ‖v‖)
    (A B : MultiplicationCLMContract ν) :
    ∃ C_rem : ℝ, 0 ≤ C_rem ∧
      ∀ (n : ℕ) [NeZero n] (t : ZMod n),
        0 < t.val → t.val < n →
          finitePeriodicBridgeResidual
            (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
            A B (asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm)
            γ n t
            ≤ C_rem * γ ^ n

/-! ## Upstream GNS data instances -/

/-- Ground-state semigroup data for the asym transfer operator. -/
noncomputable def asymGroundSemigroupData
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    GroundSemigroupData ν where
  Ω := asymGroundStateRep (Nt := Nt) (Ns := Ns) P a mass ha hmass
  Ω_meas := asymGroundStateRep_measurable (Nt := Nt) (Ns := Ns) P a mass ha hmass
  Ω_pos_ae := asymGroundStateRep_pos_ae (Nt := Nt) (Ns := Ns) P a mass ha hmass
  Ω_norm := asymGroundStateRep_norm_integral_eq_one (Nt := Nt) (Ns := Ns) P a mass ha hmass
  omegaL2 := asymGroundVector Nt Ns P a mass ha hmass
  omegaL2_coeFn :=
    asymGroundVector_coeFn_eq_groundStateRep (Nt := Nt) (Ns := Ns) P a mass ha hmass
  T := asymTransferOperatorCLM Nt Ns P a mass ha hmass
  lambda0 := asymTransferGroundEigenvalue Nt Ns P a mass ha hmass
  lambda0_pos := asymTransferGroundEigenvalue_pos Nt Ns P a mass ha hmass
  hΩ_eigen := asymTransferOperatorCLM_groundVector (Nt := Nt) (Ns := Ns) P a mass ha hmass
  hT_normContract := asymTransferNormalized_contract (Nt := Nt) (Ns := Ns) P a mass ha hmass
  omegaL2_eq_W_one :=
    asymGroundStateRep_eq_groundIsometry_one (Nt := Nt) (Ns := Ns) P a mass ha hmass

/-- **Axiom (ground-state semigroup intertwining).** The adjoint-transport
ground semigroup associated to `asymGroundSemigroupData` intertwines with the
normalized transfer through `groundIsometry`.

Discharge plan: upgrade the upstream ground isometry to the usual unitary
ground-state transform using `Ω > 0` a.e.; then the adjoint in
`GroundSemigroupData.groundSemigroup` is the inverse of `W`, and the
intertwining equation is definitional. -/
axiom asymGroundSemigroup_intertwines
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hnorm : ∀ v : L2SpatialField Ns,
      @inner ℝ _ _ (asymGroundVector Nt Ns P a mass ha hmass) v = 0 →
        ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ ≤ γ * ‖v‖)
    (t : ℕ)
    (f : Lp ℝ 2
      (groundMeasure ν (asymGroundStateRep (Nt := Nt) (Ns := Ns) P a mass ha hmass))) :
    groundIsometry
        (asymGroundStateRep_measurable (Nt := Nt) (Ns := Ns) P a mass ha hmass)
        ((asymGroundSemigroupData (Nt := Nt) (Ns := Ns) P a mass ha hmass).groundSemigroup t f)
      =
      (((asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm).T) ^ t)
        (groundIsometry
          (asymGroundStateRep_measurable (Nt := Nt) (Ns := Ns) P a mass ha hmass) f)

/-- Gap data for the ground-state transformed asym transfer. -/
noncomputable def asymGroundGapData
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hnorm : ∀ v : L2SpatialField Ns,
      @inner ℝ _ _ (asymGroundVector Nt Ns P a mass ha hmass) v = 0 →
        ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ ≤ γ * ‖v‖) :
    GroundGapData ν (asymGroundStateRep (Nt := Nt) (Ns := Ns) P a mass ha hmass) where
  omega_meas := asymGroundStateRep_measurable (Nt := Nt) (Ns := Ns) P a mass ha hmass
  transfer := asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm
  vacuum_eq_ground := by
    simpa [groundVacuum, groundOne] using
      (asymGroundStateRep_eq_groundIsometry_one
        (Nt := Nt) (Ns := Ns) P a mass ha hmass).symm
  groundSemigroup :=
    (asymGroundSemigroupData (Nt := Nt) (Ns := Ns) P a mass ha hmass).groundSemigroup
  intertwines := by
    intro t f
    exact asymGroundSemigroup_intertwines (Nt := Nt) (Ns := Ns)
      P a mass ha hmass γ hγ0 hγ1 hnorm t f

/-- Remainder hypothesis for arbitrary bounded multiplication contracts on the
asym transfer system. -/
noncomputable def asymRemainderHypothesis
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hnorm : ∀ v : L2SpatialField Ns,
      @inner ℝ _ _ (asymGroundVector Nt Ns P a mass ha hmass) v = 0 →
        ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ ≤ γ * ‖v‖)
    (A B : MultiplicationCLMContract ν) :
    RemainderHypothesis
      (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
      (asymGroundStateRep (Nt := Nt) (Ns := Ns) P a mass ha hmass)
      (asymTransferGroundEigenvalue Nt Ns P a mass ha hmass) γ A B :=
  let hrem := asymFinitePeriodicBridge_remainder_bound
    (Nt := Nt) (Ns := Ns) P a mass ha hmass hγ0 hγ1 hnorm A B
  let C_rem := Classical.choose hrem
  let hC := Classical.choose_spec hrem
  { G := asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm
    vacuum_coeFn :=
      asymGroundVector_coeFn_eq_groundStateRep (Nt := Nt) (Ns := Ns) P a mass ha hmass
    gap_eq := rfl
    C_rem := C_rem
    C_rem_nonneg := hC.1
    partition_ground_bound :=
      asymPartition_ground_bound (Nt := Nt) (Ns := Ns) P a mass ha hmass
    remainder_bound := hC.2 }

/-! ## Finite-K truncated-observable path-measure bounds -/

/-- The finite-periodic connected two-point GNS bridge for the truncated asym
slice observable `A_{g,K}`. -/
theorem asymSliceObsTrunc_pathMeasure_connected_two_point_bound
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (g : SpatialField Ns) {K : ℝ} (hK : 0 < K)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hnorm : ∀ v : L2SpatialField Ns,
      @inner ℝ _ _ (asymGroundVector Nt Ns P a mass ha hmass) v = 0 →
        ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ ≤ γ * ‖v‖)
    (t : ZMod Nt) (ht : 0 < t.val) (htn : t.val < Nt) :
    let A := asymSliceObsTruncContract (Ns := Ns) g hK
    let hRem := asymRemainderHypothesis (Nt := Nt) (Ns := Ns)
      P a mass ha hmass hγ0 hγ1 hnorm A A
    |∫ ψ, A.A (ψ 0) * A.A (ψ t)
        ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt)
      - (∫ ψ, A.A (ψ 0)
          ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt)) *
        (∫ ψ, A.A (ψ t)
          ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt))|
      ≤ ‖hRem.G.vacuumPerp (A.M hRem.G.vacuum)‖ *
          ‖hRem.G.vacuumPerp (A.M hRem.G.vacuum)‖ *
          (γ ^ t.val + γ ^ (Nt - t.val))
        + hRem.C_rem * γ ^ Nt := by
  intro A hRem
  exact pathMeasure_connected_two_point_finite_periodic_bound
    (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
    (asymGroundStateRep (Nt := Nt) (Ns := Ns) P a mass ha hmass)
    (asymTransferGroundEigenvalue Nt Ns P a mass ha hmass)
    γ A A hRem Nt t ht htn

/-- Positive-time finite-periodic connected susceptibility bound for the
truncated asym slice observable.  This is the Lt-uniform Route-A finite-K
output; the zero-time term is intentionally not included because the upstream
bridge has a separate zero-time hypothesis for the all-time version. -/
theorem asymSliceObsTrunc_pathMeasure_connected_susceptibility_bound_pos
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (g : SpatialField Ns) {K : ℝ} (hK : 0 < K)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hnorm : ∀ v : L2SpatialField Ns,
      @inner ℝ _ _ (asymGroundVector Nt Ns P a mass ha hmass) v = 0 →
        ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ ≤ γ * ‖v‖) :
    let A := asymSliceObsTruncContract (Ns := Ns) g hK
    let hRem := asymRemainderHypothesis (Nt := Nt) (Ns := Ns)
      P a mass ha hmass hγ0 hγ1 hnorm A A
    ∑ d ∈ (Finset.range Nt).filter (fun d => 0 < d),
        |pathConnectedTwoPoint
          (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
          A A Nt (d : ZMod Nt)|
      ≤ (‖hRem.G.vacuumPerp (A.M hRem.G.vacuum)‖ *
          ‖hRem.G.vacuumPerp (A.M hRem.G.vacuum)‖) * (2 / (1 - γ))
        + hRem.C_rem * (Nt : ℝ) * γ ^ Nt := by
  intro A hRem
  exact pathMeasure_connected_susceptibility_finite_periodic_bound_pos
    (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
    (asymGroundStateRep (Nt := Nt) (Ns := Ns) P a mass ha hmass)
    (asymTransferGroundEigenvalue Nt Ns P a mass ha hmass)
    γ hγ0 hγ1 A A hRem Nt

/-- The same positive-time bound with the Piece-1 `a`-cancellation estimate
substituted for the perpendicular observable norm. -/
theorem asymSliceObsTrunc_pathMeasure_connected_susceptibility_bound_pos_integral
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (g : SpatialField Ns) {K : ℝ} (hK : 0 < K)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hnorm : ∀ v : L2SpatialField Ns,
      @inner ℝ _ _ (asymGroundVector Nt Ns P a mass ha hmass) v = 0 →
        ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ ≤ γ * ‖v‖)
    (hInt : Integrable (fun ψ => (asymSliceObsLinear g ψ) ^ 2 *
              ((asymGroundVector Nt Ns P a mass ha hmass) ψ) ^ 2) ν) :
    let A := asymSliceObsTruncContract (Ns := Ns) g hK
    let hRem := asymRemainderHypothesis (Nt := Nt) (Ns := Ns)
      P a mass ha hmass hγ0 hγ1 hnorm A A
    ∑ d ∈ (Finset.range Nt).filter (fun d => 0 < d),
        |pathConnectedTwoPoint
          (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
          A A Nt (d : ZMod Nt)|
      ≤ (∫ ψ, (asymSliceObsLinear g ψ) ^ 2 *
            ((asymGroundVector Nt Ns P a mass ha hmass) ψ) ^ 2 ∂ν) *
          (2 / (1 - γ))
        + hRem.C_rem * (Nt : ℝ) * γ ^ Nt := by
  intro A hRem
  have hsusc :=
    asymSliceObsTrunc_pathMeasure_connected_susceptibility_bound_pos
      (Nt := Nt) (Ns := Ns) P a mass ha hmass g hK hγ0 hγ1 hnorm
  dsimp only at hsusc ⊢
  set Ω := asymGroundVector Nt Ns P a mass ha hmass
  set MΩ := asymSliceObsTruncMulCLM g hK Ω
  have hperp_sq :
      ‖MΩ - (@inner ℝ _ _ Ω MΩ) • Ω‖ ^ 2
        ≤ ∫ ψ, (asymSliceObsLinear g ψ) ^ 2 * (Ω ψ) ^ 2 ∂ν :=
    norm_sq_proj_obsTrunc_omega_le (Nt := Nt) (Ns := Ns) P a mass ha hmass g hK hInt
  have hperp_eq :
      hRem.G.vacuumPerp (A.M hRem.G.vacuum)
        = MΩ - (@inner ℝ _ _ Ω MΩ) • Ω := by
    rfl
  have hperp_prod_le :
      ‖hRem.G.vacuumPerp (A.M hRem.G.vacuum)‖ *
          ‖hRem.G.vacuumPerp (A.M hRem.G.vacuum)‖
        ≤ ∫ ψ, (asymSliceObsLinear g ψ) ^ 2 * (Ω ψ) ^ 2 ∂ν := by
    rw [hperp_eq, ← sq]
    exact hperp_sq
  have hgeom_nonneg : 0 ≤ 2 / (1 - γ) := by
    have hden : 0 < 1 - γ := by linarith
    positivity
  calc
    ∑ d ∈ (Finset.range Nt).filter (fun d => 0 < d),
        |pathConnectedTwoPoint
          (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
          A A Nt (d : ZMod Nt)|
        ≤ (‖hRem.G.vacuumPerp (A.M hRem.G.vacuum)‖ *
            ‖hRem.G.vacuumPerp (A.M hRem.G.vacuum)‖) * (2 / (1 - γ))
          + hRem.C_rem * (Nt : ℝ) * γ ^ Nt := hsusc
    _ ≤ (∫ ψ, (asymSliceObsLinear g ψ) ^ 2 * (Ω ψ) ^ 2 ∂ν) * (2 / (1 - γ))
          + hRem.C_rem * (Nt : ℝ) * γ ^ Nt := by
        exact add_le_add (mul_le_mul_of_nonneg_right hperp_prod_le hgeom_nonneg) le_rfl

/-! ## Torus second-moment form -/

/-- The finite-volume interacting torus second moment, rewritten through the
already-proved path-measure dictionary.  This is the Piece-2 handoff point for
the later finite-`K` to untruncated Route-A limit. -/
theorem asym_interacting_second_moment_eq_pathMeasure_slicePairing
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (g : AsymLatticeField Nt Ns) :
    ∫ ω, (ω g) ^ 2 ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass)
      =
    ∫ ψ, (slicePairing Nt Ns g ψ) ^ 2
      ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt) :=
  interacting_second_moment_eq_pathMeasure Nt Ns P a mass ha hmass g

end Pphi2
