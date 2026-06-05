/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.TorusContinuumLimit.TorusNontriviality
import Pphi2.TorusContinuumLimit.TorusInteractingMoments

/-!
# The T² P(φ)₂ theory is interacting

Assembles the headline `TorusIsInteracting` for the **genuine** torus continuum limit `μ` from:
* `torusInteractingLimit_exists` — the limit exists (PROVED, axiom-clean);
* `torus_connectedFourPoint_tendsto` — `u₄(μ_N) → u₄(μ)` (PROVED step IV, axiom-clean);
* `torus_lattice_connectedFourPoint_uniform_strictNeg` — the uniform strict lattice bound
  `u₄(μ_N) ≤ −c < 0` (the one remaining analytic input, here an **axiom**).

The axiom is the irreducible constructive-QFT content (the theory is non-Gaussian); everything else
is the proved measure-theoretic + field-redefinition infrastructure built in this development.
-/

open GaussianField MeasureTheory Filter

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-- **Uniform strict negativity of the lattice connected four-point** (the analytic core).

For the interacting torus measures `torusInteractingMeasure L N P mass`, there is a test function
`f` and `c > 0` with `u₄(μ_N)(f) ≤ −c` for **all** `N` (uniformly in the lattice size). I.e. the
connected four-point (fourth cumulant) is bounded strictly away from `0` uniformly in the cutoff —
exactly what survives the continuum limit to give a genuinely non-Gaussian (interacting) theory.

Reference: Lebowitz (1974) `u₄ ≤ 0` for even ferromagnetic `:P(φ):`; Glimm–Jaffe *Quantum Physics*
Ch. 4, 12–14; Simon *P(φ)₂* Ch. V, VIII (the perturbative leading term `u₄'(0) = −6∫(C_a f)⁴ < 0`,
Gemini-vetted 2026-06-04/05, memory `pphi2-u4-proof-route`). Strategy: the strict uniform bound is
the standard non-triviality result for `φ⁴₂` (super-renormalizable `d=2`: no cancellation, `u₄` stays
`O(λ)`); to be discharged via the perturbative route enabled by the field-redefinition development
(`Pphi2/InteractingMeasure/FieldRedefinition.lean`) or Lebowitz + a uniform lower bound.
(NOT VERIFIED — to be re-proved; see `planning/torus-interacting-proof-plan.md`.) -/
axiom torus_lattice_connectedFourPoint_uniform_strictNeg
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (f : TorusTestFunction L) (c : ℝ), 0 < c ∧ ∀ (N : ℕ) [NeZero N],
      torusConnectedFourPoint L (torusInteractingMeasure L N P mass hmass) f ≤ -c

/-- **The P(φ)₂ theory on T² is interacting.** The genuine torus continuum limit `μ`
(`torusInteractingLimit_exists`) is a non-degenerate-aware interacting theory: it is an honest
subsequential limit of the interacting torus measures (`IsTorusPphi2Limit`) **and** non-Gaussian
(`TorusIsInteracting`: the connected four-point is nonzero). Assembled from the uniform strict
lattice bound (axiom) + the proved moment convergence `torus_connectedFourPoint_tendsto`. -/
theorem torus_pphi2_isInteracting
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (μ : Measure (Configuration (TorusTestFunction L))) (_ : IsProbabilityMeasure μ),
      IsTorusPphi2Limit L μ P mass hmass ∧ TorusIsInteracting L μ := by
  obtain ⟨φ, μ, hmono, hprob, hconv⟩ := torusInteractingLimit_exists L P mass hmass
  obtain ⟨f, c, hc, hbound⟩ :=
    torus_lattice_connectedFourPoint_uniform_strictNeg L P mass hmass
  refine ⟨μ, hprob, ⟨φ, hmono, hconv⟩, f, ?_⟩
  -- `u₄(μ)(f) = lim u₄(μ_{φ n + 1})(f) ≤ −c < 0`, hence `≠ 0`.
  have htendsto := torus_connectedFourPoint_tendsto L P mass hmass f μ φ hmono hconv
  have hle : torusConnectedFourPoint L μ f ≤ -c :=
    le_of_tendsto htendsto (Filter.Eventually.of_forall fun n => hbound (φ n + 1))
  exact ne_of_lt (lt_of_le_of_lt hle (by linarith))

end Pphi2
