/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import ReflectionPositivity.TransferConstruction
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

open MeasureTheory ReflectionPositivity

namespace Pphi2

open GaussianField

/-! ## B1 — slice structure: a spacetime field is a time-indexed family of spatial fields -/

/-- Currying a function on a product index into a function-of-functions, as a linear
equivalence. `(α × β → ℝ) ≃ₗ (α → β → ℝ)`. -/
def prodCurryLinearEquiv (α β : Type*) : (α × β → ℝ) ≃ₗ[ℝ] (α → β → ℝ) where
  toFun f a b := f (a, b)
  invFun g p := g p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **B1 slice equivalence.** A spacetime lattice field on `ZMod Nt × ZMod Ns` is the same
data as a time-indexed (`ZMod Nt`) family of spatial fields (`SpatialField Ns = Fin Ns → ℝ`).
Curry the time/space product index, then reindex the spatial `ZMod Ns` to `Fin Ns`. -/
noncomputable def asymSliceEquiv (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    AsymLatticeField Nt Ns ≃ₗ[ℝ] (ZMod Nt → SpatialField Ns) :=
  (prodCurryLinearEquiv (ZMod Nt) (ZMod Ns)).trans
    (LinearEquiv.piCongrRight fun _ =>
      LinearEquiv.funCongrLeft ℝ ℝ (ZMod.finEquiv Ns).toEquiv)

@[simp] theorem asymSliceEquiv_apply (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (φ : AsymLatticeField Nt Ns) (t : ZMod Nt) (x : Fin Ns) :
    asymSliceEquiv Nt Ns φ t x = φ (t, (ZMod.finEquiv Ns).toEquiv x) := rfl

end Pphi2
