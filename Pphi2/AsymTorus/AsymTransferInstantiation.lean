/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import ReflectionPositivity.TransferConstruction
import ReflectionPositivity.TransferSystem
import Pphi2.AsymTorus.AsymSpectralGap

/-!
# Transfer-matrix discharge of the asym φ⁴₂ Layer-B2 bound — entry point

Towards discharging `asymInteractingVariance_le_freeVariance_Lt_uniform`
(`AsymExpMomentDischarge.lean`) via the transfer matrix.

**Route (decided 2026-06-03): Option B — the slice transfer matrix.** An axiom-vetting
pass (Gemini 3.1-pro) showed the finite-torus GNS instantiation of the abstract
`ReflectionPositivity.TransferConstruction` bridge is *unsound* — on a periodic torus the
positive-time sub-σ-algebra is not stable under the unit time shift (`τPos` is false), so
the GNS transfer operator is not well-defined. The sound route keeps the finite torus and
uses pphi2's **existing** slice operator `asymTransferOperatorCLM` on `L2SpatialField Ns`
(correctly normalized after the `a²/2` weight fix) together with its proved spectral gap
(`asymGappedTransfer'`, `ReflectionPositivity.GappedTransfer.susceptibility_le`).

The one missing theorem is the **Feynman–Kac trace dictionary**: the interacting measure's
time-correlations equal traces of powers of `asymTransferOperatorCLM`. Milestones B1–B5
(slice iso → Gaussian time-slice factorization → trace formula → `susceptibility_le` →
`1/a`-cancellation identification with `C·Var_free`) are scoped in
`docs/transfer-instantiation-plan.md` and `docs/layer-B2-discharge-plan.md`
("Feynman–Kac bridge — scoping"). B2 (the factorization) is the crux.

No declarations yet — this file imports the abstract bridge (`susceptibility_le` engine)
and the proved gap, and is the home for the B1–B5 trace dictionary.
-/

open MeasureTheory ReflectionPositivity GaussianField Real

namespace Pphi2

variable (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]

/-! ## The asym transfer kernel and its `TransferSystem`

The single-time-slice state space is `SpatialField Ns = Fin Ns → ℝ` with Lebesgue `volume`;
the transfer kernel is `k(x,y) = w(x)·G(x−y)·w(y)` with `w = asymTransferWeight` (the
corrected `a²/2` weight) and `G = transferGaussian`. This is exactly the kernel of
`asymTransferOperatorCLM = M_w ∘ Conv_G ∘ M_w`, so `kPow` of this kernel are the kernels of
its powers — the bridge to the proved spectral gap. Instantiating `TransferSystem` gives the
periodic path measure and the Feynman–Kac trace dictionary off the shelf. -/

/-- The asym transfer kernel `k(x,y) = w(x)·G(x−y)·w(y)`. -/
noncomputable def asymTransferKernel (P : InteractionPolynomial) (a mass : ℝ) :
    SpatialField Ns → SpatialField Ns → ℝ :=
  fun x y => asymTransferWeight Nt Ns P a mass x * transferGaussian Ns (x - y) *
    asymTransferWeight Nt Ns P a mass y

theorem asymTransferKernel_symm (P : InteractionPolynomial) (a mass : ℝ) (x y : SpatialField Ns) :
    asymTransferKernel Nt Ns P a mass x y = asymTransferKernel Nt Ns P a mass y x := by
  unfold asymTransferKernel
  rw [transferGaussian_sub_comm Ns x y]; ring

theorem asymTransferKernel_nonneg (P : InteractionPolynomial) (a mass : ℝ)
    (x y : SpatialField Ns) : 0 ≤ asymTransferKernel Nt Ns P a mass x y := by
  unfold asymTransferKernel transferGaussian
  exact mul_nonneg (mul_nonneg (asymTransferWeight_pos Nt Ns P a mass x).le
    (Real.exp_pos _).le) (asymTransferWeight_pos Nt Ns P a mass y).le

theorem asymTransferKernel_measurable (P : InteractionPolynomial) (a mass : ℝ) :
    Measurable (Function.uncurry (asymTransferKernel Nt Ns P a mass)) := by
  unfold asymTransferKernel Function.uncurry
  exact (((asymTransferWeight_measurable Nt Ns P a mass).comp measurable_fst).mul
    ((continuous_transferGaussian Ns).measurable.comp
      (measurable_fst.sub measurable_snd))).mul
    ((asymTransferWeight_measurable Nt Ns P a mass).comp measurable_snd)

/-- The asym φ⁴₂ cylinder packaged as a `TransferSystem` on the spatial slice space. -/
noncomputable def asymTransferSystem (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) : TransferSystem (SpatialField Ns) where
  ν := volume
  k := asymTransferKernel Nt Ns P a mass
  k_symm := asymTransferKernel_symm Nt Ns P a mass
  k_nonneg := asymTransferKernel_nonneg Nt Ns P a mass
  k_meas := asymTransferKernel_measurable Nt Ns P a mass
  ν_sigmaFinite := inferInstance
  openChain_step_integrable := by
    -- TODO(integrability): the open-chain step integrand is integrable — Gaussian decay of
    -- `w` (asymTransferWeight_gaussian_decay) + `G` makes the kernel products L¹.
    sorry
  partition_integrable := by
    -- TODO(integrability): closed-chain peeled integrand integrable (same Gaussian estimate).
    sorry
  pathDensity_measurable := by
    intro n _
    unfold periodicPathDensity asymTransferKernel
    refine Finset.measurable_prod _ (fun t _ => ?_)
    have hw := asymTransferWeight_measurable Nt Ns P a mass
    exact ((hw.comp (measurable_pi_apply t)).mul
      ((continuous_transferGaussian Ns).measurable.comp
        ((measurable_pi_apply t).sub (measurable_pi_apply (t + 1))))).mul
      (hw.comp (measurable_pi_apply (t + 1)))

end Pphi2
