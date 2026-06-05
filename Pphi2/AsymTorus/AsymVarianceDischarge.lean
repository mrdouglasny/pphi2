/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.AsymTorus.AsymMeasureFactorization

/-!
# Layer-B2 discharge: B3 entry point (second moment over the path measure)

With the measure factorization `interactingLatticeMeasureAsym_slice_pushforward_eq_pathMeasure`
in hand, the interacting lattice second moment `∫ (ω g)² dμ_int` is a path-measure integral of a
slice-pairing functional. This is the B3 entry point: the next steps (expand the square into
slice two-points, apply `twoPoint_dictionary`, bound via the gap `asymGappedTransfer'`, and the
B5 `1/a` cancellation) build on this.

## Main results

* `asym_pairing_sum_slice` — the bilinear site pairing through `asymSliceEquiv`.
* `config_pairing_eq_slice` — `ω g = Σ_t Σ_i (slice g)·(slice (evalMapAsym ω))`.
* `interacting_second_moment_eq_pathMeasure` — `∫ (ω g)² dμ_int = ∫ (slice pairing)² d(pathMeasure)`.
-/

open MeasureTheory GaussianField ReflectionPositivity
open scoped BigOperators

namespace Pphi2

variable (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]

/-- The bilinear site pairing in slice coordinates:
`Σ_x g(x)·φ(x) = Σ_t Σ_i (slice g)_t(i)·(slice φ)_t(i)`. -/
theorem asym_pairing_sum_slice (g φ : AsymLatticeField Nt Ns) :
    ∑ x, g x * φ x =
      ∑ t : ZMod Nt, ∑ i : Fin Ns,
        (asymSliceEquiv Nt Ns g t i) * (asymSliceEquiv Nt Ns φ t i) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [← Equiv.sum_comp (ZMod.finEquiv Ns).toEquiv (fun s => g (t, s) * φ (t, s))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [asymSliceEquiv_apply, asymSliceEquiv_apply]

/-- A configuration pairing in slice coordinates of the evaluated field. -/
theorem config_pairing_eq_slice (ω : Configuration (AsymLatticeField Nt Ns))
    (g : AsymLatticeField Nt Ns) :
    ω g =
      ∑ t : ZMod Nt, ∑ i : Fin Ns,
        (asymSliceEquiv Nt Ns g t i) * (asymSliceEquiv Nt Ns (evalMapAsym Nt Ns ω) t i) := by
  rw [config_apply_eq_sum_evalMapAsym]
  exact asym_pairing_sum_slice Nt Ns g (evalMapAsym Nt Ns ω)

/-- The slice-pairing functional on the path-measure side. -/
noncomputable def slicePairing (g : AsymLatticeField Nt Ns) (ψ : ZMod Nt → SpatialField Ns) : ℝ :=
  ∑ t : ZMod Nt, ∑ i : Fin Ns, (asymSliceEquiv Nt Ns g t i) * ψ t i

theorem slicePairing_measurable (g : AsymLatticeField Nt Ns) :
    Measurable (slicePairing Nt Ns g) := by
  unfold slicePairing
  refine Finset.measurable_sum _ (fun t _ => Finset.measurable_sum _ (fun i _ => ?_))
  exact measurable_const.mul ((measurable_pi_apply t).eval)

/-- **B3 entry point.** The interacting lattice second moment is a path-measure integral of the
squared slice pairing — via the measure factorization + change of variables. -/
theorem interacting_second_moment_eq_pathMeasure
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (g : AsymLatticeField Nt Ns) :
    ∫ ω, (ω g) ^ 2 ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) =
      ∫ ψ, (slicePairing Nt Ns g ψ) ^ 2
        ∂((asymTransferSystem Nt Ns P a mass ha hmass).pathMeasure Nt) := by
  have hsl : Measurable (asymSliceEquiv Nt Ns) := by
    rw [← asymSliceMeasurableEquiv_coe Nt Ns]; exact (asymSliceMeasurableEquiv Nt Ns).measurable
  have hev : Measurable (evalMapAsym Nt Ns) := measurable_evalMapAsym Nt Ns
  -- the composite pushforward equals the path measure
  have hcomp : (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass).map
        (asymSliceEquiv Nt Ns ∘ evalMapAsym Nt Ns) =
      (asymTransferSystem Nt Ns P a mass ha hmass).pathMeasure Nt := by
    rw [← Measure.map_map hsl hev]
    exact interactingLatticeMeasureAsym_slice_pushforward_eq_pathMeasure Nt Ns P a mass ha hmass
  rw [← hcomp, integral_map (hsl.comp hev).aemeasurable
    ((slicePairing_measurable Nt Ns g).pow_const 2).aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
  simp only [Function.comp_apply, slicePairing]
  rw [config_pairing_eq_slice]

end Pphi2
