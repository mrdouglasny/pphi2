/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.TorusContinuumLimit.TorusNontriviality
import Pphi2.InteractingMeasure.FieldRedefinition

/-!
# Torus → lattice pull-back of the connected four-point (uniform-discharge leaf `L6F`)

`torusConnectedFourPoint` of the torus interacting measure equals the lattice `connectedFourPoint` of
the interacting lattice measure at the embedded test function. Since
`torusInteractingMeasure = map (torusEmbedLift) (interactingLatticeMeasure)` and
`(torusEmbedLift ω) f = ω (latticeTestFn f)` (`torusEmbedLift_eval_eq`), the four-point pushes
straight through. This is the framing step that lets the lattice `u₄` bound discharge the torus axiom
`torus_weakCoupling_lattice_connectedFourPoint_strictNeg`.
-/

namespace Pphi2

open MeasureTheory GaussianField

variable (L : ℝ) [hL : Fact (0 < L)]

/-- **L6F pull-back.** The torus connected four-point of the interacting measure equals the lattice
connected four-point of the interacting lattice measure at the embedded test function
`latticeTestFn L N f`. -/
theorem torusConnectedFourPoint_eq_lattice (N : ℕ) [NeZero N] (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) (f : TorusTestFunction L) :
    torusConnectedFourPoint L (torusInteractingMeasure L N P mass hmass) f
      = connectedFourPoint
          (interactingLatticeMeasure 2 N P (circleSpacing L N) mass (circleSpacing_pos L N) hmass)
          (latticeTestFn L N f) := by
  unfold torusConnectedFourPoint connectedFourPoint torusInteractingMeasure
  rw [integral_map (torusEmbedLift_measurable L N).aemeasurable
      ((configuration_eval_measurable f).pow_const 4).aestronglyMeasurable,
    integral_map (torusEmbedLift_measurable L N).aemeasurable
      ((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable]
  simp_rw [torusEmbedLift_eval_eq L N f]

end Pphi2
