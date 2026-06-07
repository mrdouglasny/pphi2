/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.TorusContinuumLimit.TorusNontriviality
import Pphi2.InteractingMeasure.FieldRedefinition
import Pphi2.InteractingMeasure.U4AffineBound

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

/-- **L6F reduction.** The torus connected four-point of the interacting measure equals the lattice
`u₄` at full coupling `g=1` and embedded test function: `torusConnectedFourPoint L
(torusInteractingMeasure L N P mass hmass) f = u4 .. (latticeTestFn L N f) 1`. Hence the discharge
`torus_weakCoupling_lattice_connectedFourPoint_strictNeg` reduces to `u4(1,mass) ≤ -c` (`mass > m₀`).
The remaining step — `u4(1,mass) < 0` at large mass = weak coupling — is the mass↔g field
redefinition `g = 1/(4 mass²)` (`connectedFourPoint_interactingMeasure_field_rescale`); the
field-rescale ⟹ covariance/mass identity it needs is the deferred Cramér–Wold/Minlos fact. -/
theorem torusConnectedFourPoint_eq_u4_one (N : ℕ) [NeZero N] (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) (f : TorusTestFunction L) :
    torusConnectedFourPoint L (torusInteractingMeasure L N P mass hmass) f
      = u4 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass P (latticeTestFn L N f) 1 := by
  rw [torusConnectedFourPoint_eq_lattice, connectedFourPoint_interactingLatticeMeasure_eq_u4_one]

end Pphi2
