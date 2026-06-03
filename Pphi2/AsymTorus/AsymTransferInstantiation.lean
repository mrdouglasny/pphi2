/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import ReflectionPositivity.TransferConstruction
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

-- Instantiation declarations land here (M1–M5). See docs/transfer-instantiation-plan.md.

end Pphi2
