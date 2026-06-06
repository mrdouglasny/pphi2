/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.TorusContinuumLimit.TorusNontriviality
import Pphi2.TorusContinuumLimit.TorusInteractingMoments

/-!
# The T² P(φ)₂ theory is interacting (weak coupling)

Assembles the headline `TorusIsInteracting` for the **genuine** torus continuum limit `μ`, in the
**weak-coupling regime** (large mass), from:
* `torusInteractingLimit_exists` — the limit exists (PROVED, axiom-clean);
* `torus_connectedFourPoint_tendsto` — `u₄(μ_N) → u₄(μ)` (PROVED step IV, axiom-clean);
* `torus_weakCoupling_lattice_connectedFourPoint_strictNeg` — the uniform strict lattice bound
  `u₄(μ_N) ≤ −c < 0` for `mass > m₀` (the one remaining analytic input, here an **axiom**, restricted
  to weak coupling where it is perturbatively controlled).

**Why weak coupling.** `u₄ ≠ 0` is enough for non-triviality (the theory is interacting). For the
fixed quartic, the dimensionless coupling is `g = 1/(4 mass²)`, so `mass > m₀` ⟺ `g < g₀ := 1/(4m₀²)`
— a *finite* upper bound on `g`. In that regime the perturbative leading term `u₄'(0) = −6∫(C_a f)⁴`
strictly dominates the `O(g²)` corrections (Nelson hypercontractivity at fixed volume — no cluster
expansion), so `u₄ < 0`. Strong coupling (small mass, where `φ⁴₂` has a phase transition) is *not*
needed for non-triviality and is left out; `u₄ < 0` still holds there (Lebowitz) but
non-perturbatively.
-/

open GaussianField MeasureTheory Filter

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-- **Weak-coupling uniform strict negativity of the lattice connected four-point** (the analytic
core, weak-coupling regime).

**Pure quartic only (`hP : P.n = 4`).** The vetted discharge route — `u₄'(0) = −6∫(C_a f)⁴`
(`U4Derivative.lean`) and step 2b (`wickFourth_interaction_inner_quartic`) — is quartic-specific
(the leading Wick term `6 = 4!·(1/4)`), so the axiom is scoped to `P.n = 4` rather than every
`InteractionPolynomial`, keeping the trust boundary aligned with what the route supports.

There is a mass threshold `m₀ > 0` such that for every `mass > m₀` (equivalently, dimensionless
coupling `g = 1/(4 mass²) < 1/(4 m₀²)`) there are a test function `f` and `c > 0` with
`u₄(torusInteractingMeasure L N P mass)(f) ≤ −c` for **all** `N`. I.e. above the threshold the
connected four-point is bounded strictly away from `0` uniformly in the lattice cutoff.

Reference / strategy: the perturbative weak-coupling non-triviality of `φ⁴₂`. Leading term
`u₄'(0) = −4!·(1/4)·∫(C_a f)⁴ = −6∫(C_a f)⁴ < 0` (Wick on the free GFF; `∫(C_a f)⁴ > 0`; the term is
Wick-ordering-invariant — all four legs external). Remainder `|R(g)| ≤ K g²` cutoff-uniform from
Nelson hypercontractivity (`GaussianHilbert.polynomial_chaos_concentration` /
`bonami_nelson_chaosLE` via `Pphi2/NelsonEstimate`; **no cluster expansion at fixed volume `L`**). So
for `g` below the convergence radius `g₀` the leading term dominates and `u₄ ≤ −(κg/2)∫(C f)⁴ < 0`.
Gemini-vetted 2026-06-04/05 (memory `pphi2-u4-proof-route`); Simon *P(φ)₂* Ch. V/VIII, Glimm–Jaffe
Ch. 8–9, 19. Discharge route enabled by the field-redefinition development
(`Pphi2/InteractingMeasure/FieldRedefinition.lean`). (NOT VERIFIED — to be proved; see
`planning/torus-interacting-proof-plan.md`, `planning/lambda-coupling-family-plan.md`.) -/
axiom torus_weakCoupling_lattice_connectedFourPoint_strictNeg
    (P : InteractionPolynomial) (hP : P.n = 4) :
    ∃ m₀ : ℝ, 0 < m₀ ∧ ∀ (mass : ℝ) (hmass : 0 < mass), m₀ < mass →
      ∃ (f : TorusTestFunction L) (c : ℝ), 0 < c ∧ ∀ (N : ℕ) [NeZero N],
        torusConnectedFourPoint L (torusInteractingMeasure L N P mass hmass) f ≤ -c

/-- **The P(φ)₂ theory on T² is interacting at weak coupling.** There is a mass threshold `m₀` above
which (weak coupling) the genuine torus continuum limit `μ` is an honest interacting theory: an
honest subsequential limit of the interacting torus measures (`IsTorusPphi2Limit`) **and**
non-Gaussian (`TorusIsInteracting`: the connected four-point is nonzero). Assembled from the
weak-coupling uniform strict lattice bound (axiom) + the proved moment convergence
`torus_connectedFourPoint_tendsto`. -/
theorem torus_pphi2_isInteracting_weakCoupling (P : InteractionPolynomial) (hP : P.n = 4) :
    ∃ m₀ : ℝ, 0 < m₀ ∧ ∀ (mass : ℝ) (hmass : 0 < mass), m₀ < mass →
      ∃ (μ : Measure (Configuration (TorusTestFunction L))) (_ : IsProbabilityMeasure μ),
        IsTorusPphi2Limit L μ P mass hmass ∧ TorusIsInteracting L μ := by
  obtain ⟨m₀, hm₀, hbound⟩ := torus_weakCoupling_lattice_connectedFourPoint_strictNeg L P hP
  refine ⟨m₀, hm₀, fun mass hmass hgt => ?_⟩
  obtain ⟨φ, μ, hmono, hprob, hconv⟩ := torusInteractingLimit_exists L P mass hmass
  obtain ⟨f, c, hc, hb⟩ := hbound mass hmass hgt
  refine ⟨μ, hprob, ⟨φ, hmono, hconv⟩, f, ?_⟩
  -- `u₄(μ)(f) = lim u₄(μ_{φ n + 1})(f) ≤ −c < 0`, hence `≠ 0`.
  have htendsto := torus_connectedFourPoint_tendsto L P mass hmass f μ φ hmono hconv
  have hle : torusConnectedFourPoint L μ f ≤ -c :=
    le_of_tendsto htendsto (Filter.Eventually.of_forall fun n => hb (φ n + 1))
  exact ne_of_lt (lt_of_le_of_lt hle (by linarith))

end Pphi2
