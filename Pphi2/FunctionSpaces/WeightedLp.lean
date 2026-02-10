/-
  Pphi2.FunctionSpaces.WeightedLp
  Weighted Lp spaces and admissible weights.

  Reference: DDJ Appendix A, Definitions A.1-A.2.
-/
import Pphi2.Basic

noncomputable section

open MeasureTheory

/-! ## Admissible weights -/

/-- An admissible weight on ℝ²: smooth, positive, with polynomial growth
    control and bounded logarithmic derivatives.
    DDJ Definition A.1. -/
structure AdmissibleWeight where
  w : Plane → ℝ
  pos : ∀ x, 0 < w x
  smooth : ContDiff ℝ ⊤ w
  growth : ∃ (b c : ℝ), 0 ≤ b ∧ 0 < c ∧
    ∀ x y : Plane, w x ≤ c * w y * (1 + ‖x - y‖) ^ b

/-! ## Weighted Lp norms -/

/-- The weighted Lp norm ‖f‖_{Lp(w)} = ‖w·f‖_{Lp}.
    DDJ Definition A.2. -/
def weightedLpNorm (p : ℝ) (w : AdmissibleWeight) (f : Plane → ℝ) : ℝ :=
  sorry -- (∫ |w(x) f(x)|^p dx)^{1/p}

/-! ## Weighted Bessel potential spaces -/

/-- The weighted Bessel potential norm
    ‖f‖_{L^α_p(w)} = ‖(1-Δ)^{α/2} f‖_{Lp(w)}.
    DDJ Definition A.2. -/
def besselNorm (α p : ℝ) (w : AdmissibleWeight) (f : Plane → ℝ) : ℝ :=
  sorry -- ‖(1-Δ)^{α/2} f‖_{Lp(w)}

end
