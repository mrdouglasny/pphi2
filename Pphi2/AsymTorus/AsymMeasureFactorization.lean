/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.AsymTorus.AsymEnergyFactorization
import Pphi2.AsymTorus.AsymLatticeMeasure
import GaussianField.DensityAsym

/-!
# Crux-2 steps 4–5: the measure factorization `μ_int.map sliceEquiv = pathMeasure`

The capstone of the Layer-B2 measure↔operator bridge: the interacting lattice measure, pushed
to coordinates (`evalMapAsym`) and then to time-slices (`asymSliceEquiv`), equals the periodic
path measure of `asymTransferKernel` (the abstract `TransferSystem.pathMeasure`). Once this
lands, the proved Feynman–Kac dictionary (`twoPoint_dictionary`) + the gap (`susceptibility_le`)
give the `Lt`-uniform correlator bound, and B5's `1/a` cancellation closes
`asymInteractingVariance_le_freeVariance_Lt_uniform`.

**All inputs are proved and in place** (this is gluing, no new mathematics):
1. `GaussianField.latticeGaussianFieldLawAsym_eq_normalizedQuadraticGaussianMeasure` — the free
   GFF pushed by `evalMapAsym` is the Lebesgue-density Gaussian `(Z_Q)⁻¹·exp(−(a²/2)⟨φ,Qφ⟩)·vol`.
2. `interactionFunctionalAsym` in coordinates: `V(ω) = a²·Σ_x :P:((evalMapAsym ω) x)`.
3. `energy_exponent_factorization` : `(a²/2)⟨φ,Qφ⟩ + a²Σ:P: = Σ_t (timeCoupling + a²·spatialAction)`.
4. `periodicPathDensity_asymTransferKernel_eq_exp` : `∏_t k(slices) = exp(−that)`.
5. `asymSliceEquiv` is measure-preserving for the Pi-Lebesgue volume (coordinate reindex, Jacobian 1).

## Proof strategy (the remaining gluing)

`interactingLatticeMeasureAsym = (Z_int)⁻¹ • (latticeGaussianMeasureAsym.withDensity exp(−V))`.
- Push through `evalMapAsym` (a measurable equiv, `evalMapAsymMeasurableEquiv`): `Measure.map` of a
  scaled `withDensity` through an equiv is the scaled `withDensity` of the pushforward with the
  density precomposed with the inverse (`withDensity_map_equiv`-style). Use input (1) for the free
  pushforward and input (2) for the interaction density in coordinates.
  ⟹ `= (Z_int·Z_Q)⁻¹ • volume.withDensity (exp(−((a²/2)⟨φ,Qφ⟩ + a²Σ:P:)))`.
- Rewrite the exponent by (3) and the exponential by (4): the density is `∏_t k(asymSliceEquiv φ)`.
- Push through `asymSliceEquiv` and use (5) (`volume.map asymSliceEquiv = Measure.pi (fun _ => volume)`):
  `= (Z_int·Z_Q)⁻¹ • (Measure.pi (fun _ => volume)).withDensity (∏_t k)`.
- Match `asymTransferSystem.pathMeasure Nt = (Z_path)⁻¹ • (Measure.pi (fun _ => volume)).withDensity
  (∏_t k)`. Both are probability measures with the *same* unnormalized density, so the normalizing
  constants agree (`Z_int·Z_Q = Z_path`, each `= ∫ ∏_t k`) and the measures are equal.
-/

open MeasureTheory GaussianField ReflectionPositivity
open scoped BigOperators

namespace Pphi2

variable (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]

/-- **Crux-2 steps 4–5 (measure factorization).** The interacting lattice measure, pushed to
coordinates and then to time-slices, equals the periodic path measure of `asymTransferKernel`.

WIP: the measure-pushforward gluing of the five proved inputs above (see strategy). -/
theorem interactingLatticeMeasureAsym_slice_pushforward_eq_pathMeasure
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    (((interactingLatticeMeasureAsym Nt Ns P a mass ha hmass).map (evalMapAsym Nt Ns)).map
        (asymSliceEquiv Nt Ns)) =
      (asymTransferSystem Nt Ns P a mass ha hmass).pathMeasure Nt := by
  sorry

end Pphi2
