/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lattice Setup Construction — Smooth/Rough Decomposition Scaffolding

Concrete definitions for the smooth/rough decomposition of the
lattice interaction `V` at a Wick-constant cutoff scale `T`:

  V(ω) = V_S(T, ω) + E_R(T, ω),

where `V_S(T)` evaluates the same lattice interaction polynomial but
with Wick subtraction at the *smooth* Wick constant `c_S(T)` instead
of the full `c_a = c_S(T) + c_R(T)`, and `E_R(T)` is the
deterministic difference.

This is the **deterministic decomposition** at the Wick-constant
level. The genuine Glimm-Jaffe split into smooth/rough fields would
be `V(φ) = V_S(φ_S) + E_R(φ, φ_S)` — a different (joint-distributional)
decomposition. The deterministic version here is simpler and uses
only the Wick polynomial machinery already in pphi2; the resulting
`E_R(T)` has *one* lower polynomial degree than `V` (the leading
order cancels in the difference of Wick polynomials), giving a
chaos-LE membership of degree `deg(P) - 2`.

## Main definitions

* `latticeSmoothInteraction P a mass T`: the smooth-side interaction.
* `latticeRoughError P a mass T`: the rough error
  `V - latticeSmoothInteraction = wickPolynomial(P, c_a) -
  wickPolynomial(P, c_S(T))`, summed over sites.

## Main theorems

* `interactionFunctional_eq_smooth_plus_rough`: the decomposition
  identity (immediate by definition).

## Status

Definitions + decomposition lemma are landed. The chaos membership
(`E_R(T) ∈ wienerChaosLE n (deg(P) - 2)` after pushforward) and the
`L²`-norm bound `‖E_R(T)‖₂² ≤ K · T^δ` will populate
`LatticeRoughErrorSetup` once they're proved.
-/

import Pphi2.NelsonEstimate.CovarianceSplit
import Pphi2.WickOrdering.WickPolynomial

noncomputable section

namespace Pphi2.LatticeSetup

open GaussianField

variable (d N : ℕ) [NeZero N] (a mass : ℝ)

/-- The smooth-side interaction at cutoff scale `T`:
`V_S(T)(ω) = a^d Σ_x wickPolynomial P (smoothWickConstant T) (ω(δ_x))`.

Same shape as `interactionFunctional` but Wick-subtracted at the
smooth Wick constant `c_S(T)` instead of the full `c_a`. -/
def latticeSmoothInteraction (P : InteractionPolynomial) (T : ℝ) :
    Configuration (FinLatticeField d N) → ℝ :=
  fun ω => a ^ d * ∑ x : FinLatticeSites d N,
    wickPolynomial P (smoothWickConstant d N a mass T)
      (ω (finLatticeDelta d N x))

/-- The rough error at cutoff scale `T`:
`E_R(T)(ω) := V(ω) - V_S(T)(ω) =
  a^d Σ_x [wickPolynomial(P, c_a)(ω(δ_x)) - wickPolynomial(P, c_S(T))(ω(δ_x))]`.

The two polynomials in the difference have the same leading term
`a_n x^n / n`, so their difference is a polynomial of degree
`deg(P) - 2 = n - 2` in `ω(δ_x)`. -/
def latticeRoughError (P : InteractionPolynomial) (T : ℝ) :
    Configuration (FinLatticeField d N) → ℝ :=
  fun ω =>
    interactionFunctional d N P a mass ω - latticeSmoothInteraction d N a mass P T ω

/-- **The decomposition holds by definition.** -/
theorem interactionFunctional_eq_smooth_plus_rough
    (P : InteractionPolynomial) (T : ℝ)
    (ω : Configuration (FinLatticeField d N)) :
    interactionFunctional d N P a mass ω =
      latticeSmoothInteraction d N a mass P T ω +
        latticeRoughError d N a mass P T ω := by
  unfold latticeRoughError
  ring

end Pphi2.LatticeSetup
