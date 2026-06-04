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

-- B1–B5 (the Feynman–Kac trace dictionary) land here. See docs/transfer-instantiation-plan.md.

end Pphi2
