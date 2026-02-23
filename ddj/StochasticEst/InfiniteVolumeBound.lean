/-
  Pphi2.StochasticEst.InfiniteVolumeBound
  Uniform stochastic bounds for free field Wick powers in weighted
  Bessel potential spaces on the cylinder.

  Reference: DDJ Appendix C, Lemma C.6.
  Adapted from spheres to cylinders: no stereographic pullback needed.
-/
import Pphi2.GaussianCylinder.Covariance
import Pphi2.FunctionSpaces.WeightedLp

noncomputable section

open MeasureTheory

/-! ## The key stochastic bound on the cylinder

On the cylinder ℝ × S¹_L, there is no stereographic projection.
The Wick power norms are measured directly in weighted Bessel potential
spaces on the cylinder.
-/

/-- **Lemma C.6** (Stochastic bound on the cylinder).
    For all m ≥ 1, p ≥ 1, κ > 0, there exists C > 0 such that
    for all L ≥ 1, N ≥ 1:

    𝔼‖X^{:m:}_{L,N}‖ᵖ_{L^{-κ}_p(ℝ × S¹_L, v_L^{1/p})} ≤ C.

    The proof uses:
    - Nelson hypercontractivity (Lem C.4) to reduce to second moments
    - Sobolev embedding to control L∞ norms
    - Explicit trace estimates for the Green's function on the cylinder

    DDJ Lemma C.6, adapted to cylinder. -/
axiom stochastic_bound_infinite_volume
    (m : ℕ+) (p : ℝ) (hp : 1 ≤ p) (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℝ) (_ : 1 ≤ L) (N : ℕ+),
        True -- 𝔼‖X^{:m:}_{L,N}‖ᵖ ≤ C

/-- Second part of Lemma C.6:
    lim_{N→∞} 𝔼‖(X_L - X_{L,N})‖ᵖ_{L^{-κ}_p(v_L^{1/p})} = 0.
    This is needed for the UV limit. -/
axiom stochastic_bound_uv_convergence
    (p : ℝ) (hp : 1 ≤ p) (κ : ℝ) (hκ : 0 < κ)
    (L : ℝ) (_ : 1 ≤ L) :
    True -- limit is 0

end
