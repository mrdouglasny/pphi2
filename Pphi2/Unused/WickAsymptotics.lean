/-
Unused computation axioms moved here.
Not referenced by any theorem in the proof chain.
Pure computations (Riemann sum ≈ integral) that could be proved
but are not needed for the P(Φ)₂ construction.

Sources:
- wickConstant_log_divergence: from WickOrdering/Counterterm.lean
- wick_constant_comparison: from Bridge.lean
-/

import Pphi2.WickOrdering.Counterterm

noncomputable section

open Real

namespace Pphi2

/-! ## Asymptotics

As a → 0 with N = L/a, the Wick constant diverges logarithmically.
This is the ONLY UV divergence in P(Φ)₂ (super-renormalizability). -/

/-- The Wick constant diverges as `(1/2π) log(1/a)` in d=2.

More precisely, for d = 2 and N = ⌊L/a⌋:
  `c_a = (1/2π) log(1/a) + O(1)`

The proof uses Euler-Maclaurin summation to compare the lattice sum
`Σ_k 1/(k² + m²)` with the integral `∫ dk/(k² + m²) = (1/2π) log(Λ²/m²)`.

The upper bound `wickConstant_le_inv_mass_sq` already provides a (crude)
uniform bound sufficient for the construction. -/
axiom wickConstant_log_divergence (mass : ℝ) (hmass : 0 < mass) :
    ∃ C : ℝ, ∀ (N : ℕ) [NeZero N] (a : ℝ), 0 < a → a ≤ 1 →
    |wickConstant 2 N a mass - (1 / (2 * π)) * Real.log (1 / a)| ≤ C

-- wick_constant_comparison (formerly in Bridge.lean) was a duplicate of the
-- above with slightly different formulation. Deleted.

end Pphi2

end
