/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import ReflectionPositivity.TransferConstruction
import Pphi2.AsymTorus.AsymTorusOS
import Pphi2.AsymTorus.AsymSpectralGap

/-!
# Instantiating the abstract OS transfer bridge for the asym φ⁴₂ cylinder

This module instantiates `ReflectionPositivity.TransferConstruction` (the abstract OS
transfer operator + Feynman–Kac correlation bridge, D0–D3) for pphi2's asymmetric
lattice φ⁴₂ measure, towards discharging the Layer-B2 axiom
`asymInteractingVariance_le_freeVariance_Lt_uniform` (`AsymExpMomentDischarge.lean`).

**Entry point only (2026-06-03).** The reflection-positivity dependency is pinned to a
revision carrying `TransferConstruction` (D0–D3), and this import compiles, so the
cross-repo wiring is in place. The instantiation itself is sequenced in
`docs/transfer-instantiation-plan.md`:

* **M1** — asym lattice reflection positivity in the abstract `IsReflectionPositive`
  form (port the square `OSProofs.lattice_rp`; adapt `PositiveTimeSupported` raw
  functions to `mPos`-measurable `Lp` elements).
* **M2** — the `θ` involution + positive-time sub-σ-algebra `mPos` on
  `Configuration (AsymLatticeField Nt Ns)` (needs the currently-private
  `asymInteractingLatticeMeasure_timeReflection_invariant` exposed).
* **M3** — assemble `TimeTranslatedSystem` (τ = time shift, τmp/τθ/τPos, contraction).
* **M4** ⚠ — the operator-coincidence: `H_phys` / `transferOperator` ≃
  `L2SpatialField Ns` / `asymTransferOperatorCLM` (now correctly normalized, `bb4b86d`),
  transporting the proved gap (`asymGappedTransfer'`) to a `GappedTransfer H_phys`. The
  hard core.
* **M5** — connect D3's summed correlator to `∫ (ω f)² dμ_int` and identify the bound
  with `C·Var_free` via the `1/a` cancellation; B1 supplies `a`-uniformity.

No declarations yet — see the plan for the milestone breakdown and dependencies.
-/

open MeasureTheory ReflectionPositivity

namespace Pphi2

/-! ## M1-M3 transfer-system instantiation

The construction below is intentionally a thin wiring layer. The finite
site maps and positive-time sub-sigma-algebra are defined on the heterogeneous
isotropic lattice `AsymLatticeField Nt Ns`; the hard analytic transport
obligations are isolated as clearly marked `sorry`s.

The square-lattice reflection proof is already available as
`lattice_rp`, and the square cutoff reflection invariance theorem is
exposed by `AsymTorusOS`. Transporting those facts through the
`asymTorusInteractingMeasureIso`/heterogeneous-lattice bridge is the
remaining M1/M2 proof work.
-/

open GaussianField

/-- The heterogeneous asym-cylinder configuration space. -/
abbrev AsymTransferOmega (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :=
  Configuration (AsymLatticeField Nt Ns)

/-- Time reflection on heterogeneous lattice sites: `(t, x) ↦ (-t, x)`. -/
def asymTimeReflectSites (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (x : AsymLatticeSites Nt Ns) : AsymLatticeSites Nt Ns :=
  (-x.1, x.2)

@[simp] theorem asymTimeReflectSites_involutive (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    Function.Involutive (asymTimeReflectSites Nt Ns) := by
  intro x
  ext <;> simp [asymTimeReflectSites]

/-- Unit Euclidean-time shift on heterogeneous lattice sites. -/
def asymUnitTimeShiftSites (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (x : AsymLatticeSites Nt Ns) : AsymLatticeSites Nt Ns :=
  (x.1 + 1, x.2)

/-- Linear map on heterogeneous lattice fields induced by a site map. -/
def asymLatticeSiteMapLM (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (σ : AsymLatticeSites Nt Ns → AsymLatticeSites Nt Ns) :
    AsymLatticeField Nt Ns →ₗ[ℝ] AsymLatticeField Nt Ns where
  toFun g := g ∘ σ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Configuration map dual to a site map. -/
noncomputable def asymConfigurationSiteMap (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (σ : AsymLatticeSites Nt Ns → AsymLatticeSites Nt Ns) :
    AsymTransferOmega Nt Ns → AsymTransferOmega Nt Ns :=
  fun ω => ω.comp (asymLatticeSiteMapLM Nt Ns σ).toContinuousLinearMap

/-- OS time reflection on heterogeneous-lattice configurations. -/
noncomputable def Pphi2AsymTheta (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    AsymTransferOmega Nt Ns → AsymTransferOmega Nt Ns :=
  asymConfigurationSiteMap Nt Ns (asymTimeReflectSites Nt Ns)

/-- Unit OS time translation on heterogeneous-lattice configurations. -/
noncomputable def Pphi2AsymTau (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    AsymTransferOmega Nt Ns → AsymTransferOmega Nt Ns :=
  asymConfigurationSiteMap Nt Ns (asymUnitTimeShiftSites Nt Ns)

/-- Positive-time lattice sites, using the same strict half-cylinder convention as
`PositiveTimeSupported`: `0 < t.val < Nt / 2`. -/
abbrev AsymPositiveTimeSites (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :=
  {x : AsymLatticeSites Nt Ns // 0 < x.1.val ∧ x.1.val < Nt / 2}

/-- Evaluation of all positive-time lattice coordinates. -/
noncomputable def asymPositiveTimeEval (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    AsymTransferOmega Nt Ns → (AsymPositiveTimeSites Nt Ns → ℝ) :=
  fun ω x => ω (asymLatticeDelta Nt Ns x.1)

/-- Positive-time sub-sigma-algebra generated by positive-time site evaluations. -/
@[reducible] noncomputable def Pphi2AsymMPos (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    MeasurableSpace (AsymTransferOmega Nt Ns) :=
  MeasurableSpace.comap (asymPositiveTimeEval Nt Ns) inferInstance

/-- The interacting asym-cylinder lattice measure used by the transfer system. -/
noncomputable abbrev Pphi2AsymMu (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Measure (AsymTransferOmega Nt Ns) :=
  interactingLatticeMeasureAsym Nt Ns P a mass ha hmass

theorem Pphi2AsymTheta_involutive (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    Function.Involutive (Pphi2AsymTheta Nt Ns) := by
  intro ω
  apply ContinuousLinearMap.ext
  intro f
  simp [Pphi2AsymTheta, asymConfigurationSiteMap, asymLatticeSiteMapLM,
    Function.comp_assoc]

theorem Pphi2AsymTauTheta (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    ∀ ω : AsymTransferOmega Nt Ns,
      Pphi2AsymTau Nt Ns (Pphi2AsymTheta Nt Ns (Pphi2AsymTau Nt Ns ω)) =
        Pphi2AsymTheta Nt Ns ω := by
  intro ω
  apply ContinuousLinearMap.ext
  intro f
  simp [Pphi2AsymTau, Pphi2AsymTheta, asymConfigurationSiteMap,
    asymLatticeSiteMapLM, Function.comp_assoc]
  apply congrArg ω
  funext x
  exact congrArg f (by ext <;> simp [asymUnitTimeShiftSites, asymTimeReflectSites])

theorem asymPositiveTimeEval_measurable (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    Measurable (asymPositiveTimeEval Nt Ns) := by
  rw [measurable_pi_iff]
  intro x
  exact configuration_eval_measurable (asymLatticeDelta Nt Ns x.1)

theorem Pphi2AsymMPos_le (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    Pphi2AsymMPos Nt Ns ≤ (inferInstance : MeasurableSpace (AsymTransferOmega Nt Ns)) := by
  exact (asymPositiveTimeEval_measurable Nt Ns).comap_le

theorem Pphi2AsymTheta_measurePreserving (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    MeasurePreserving (Pphi2AsymTheta Nt Ns)
      (Pphi2AsymMu Nt Ns P a mass ha hmass)
      (Pphi2AsymMu Nt Ns P a mass ha hmass) := by
  -- TODO(M2): transport the square cutoff theorem
  -- `asymInteractingLatticeMeasure_timeReflection_invariant` through the
  -- heterogeneous `asymTorusInteractingMeasureIso` bridge, or prove the
  -- same site-permutation invariance directly for `interactingLatticeMeasureAsym`.
  sorry

theorem Pphi2Asym_reflectionPositive (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    @Measure.IsReflectionPositive (AsymTransferOmega Nt Ns)
      (inferInstance : MeasurableSpace (AsymTransferOmega Nt Ns))
      (Pphi2AsymMu Nt Ns P a mass ha hmass)
      (Pphi2AsymTheta Nt Ns)
      (Pphi2AsymMPos Nt Ns) := by
  -- TODO(M1): adapt the square raw-function theorem `lattice_rp` to the
  -- abstract `IsReflectionPositive` API. This requires the bridge from
  -- `PositiveTimeSupported` functions to `Pphi2AsymMPos`-measurable `Lp`
  -- representatives and transport across the heterogeneous/square iso.
  sorry

theorem Pphi2AsymTau_measurePreserving (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    MeasurePreserving (Pphi2AsymTau Nt Ns)
      (Pphi2AsymMu Nt Ns P a mass ha hmass)
      (Pphi2AsymMu Nt Ns P a mass ha hmass) := by
  -- TODO(M3): prove heterogeneous time-translation invariance for
  -- `interactingLatticeMeasureAsym`. The square theorem is
  -- `latticeMeasure_translation_invariant`; this needs the corresponding
  -- asym site-shift density/partition-function argument or iso transport.
  sorry

theorem Pphi2AsymTauPos (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    ∀ f : @Lp (AsymTransferOmega Nt Ns) ℝ inferInstance _ 2
        (Pphi2AsymMu Nt Ns P a mass ha hmass),
      AEStronglyMeasurable[Pphi2AsymMPos Nt Ns] (⇑f)
        (Pphi2AsymMu Nt Ns P a mass ha hmass) →
      AEStronglyMeasurable[Pphi2AsymMPos Nt Ns]
        (fun x => f (Pphi2AsymTau Nt Ns x))
        (Pphi2AsymMu Nt Ns P a mass ha hmass) := by
  intro f hf
  -- TODO(M3): establish the precise positive-time convention under the
  -- unit shift. Periodicity means this is not a purely formal monotonicity
  -- proof unless the half-cylinder support convention is fixed.
  sorry

/-- M1-M3 entry point: the asym phi^4_2 lattice cylinder as an abstract
time-translated reflection-positive system. -/
noncomputable def Pphi2AsymTTS (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    TimeTranslatedSystem (Configuration (AsymLatticeField Nt Ns)) :=
  letI : MeasurableSpace (AsymTransferOmega Nt Ns) := inferInstance
  { μ := Pphi2AsymMu Nt Ns P a mass ha hmass
    θ := Pphi2AsymTheta Nt Ns
    mp := Pphi2AsymTheta_measurePreserving Nt Ns P a mass ha hmass
    inv := Pphi2AsymTheta_involutive Nt Ns
    mPos := Pphi2AsymMPos Nt Ns
    le := Pphi2AsymMPos_le Nt Ns
    rp := Pphi2Asym_reflectionPositive Nt Ns P a mass ha hmass
    τ := Pphi2AsymTau Nt Ns
    τmp := Pphi2AsymTau_measurePreserving Nt Ns P a mass ha hmass
    τθ := Pphi2AsymTauTheta Nt Ns
    τPos := Pphi2AsymTauPos Nt Ns P a mass ha hmass
    contraction := by
      intro f
      -- TODO(M3): prove the reflection-seminorm contraction for the
      -- finite-volume transfer step, then identify it with the existing
      -- asym transfer operator estimates.
      sorry }


end Pphi2
