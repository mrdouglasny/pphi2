/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.InteractingMeasure.InteractionFourPoint
import GaussianField.Properties

/-!
# Moment integrability foundations (u₄ step 2c, step 1)

Integrability of raw pairing powers `(ω f)ⁿ` and their products with the interaction `V` under the
lattice GFF — the domination inputs for differentiating the Gibbs family `g ↦ ∫ (ω f)ⁿ e^{−gV} dμ_GFF`
under the integral sign.

Key facts: `latticeGaussianMeasure = GaussianField.measure (latticeCovarianceGJ …)` (definitionally),
so `pairing_memLp` gives `ω f ∈ Lᵖ` for every `p`; the `‖·‖^n` route (mirroring
`TorusInteractingMoments`) then gives integrability of the raw powers.
-/

namespace Pphi2

open MeasureTheory GaussianField
open scoped NNReal ENNReal

variable (d N : ℕ) [NeZero N]

/-- The pairing `ω ↦ ω f` lies in every `Lᵖ` of the lattice GFF. (Repackages `pairing_memLp` for the
`latticeGaussianMeasure` form, which is `GaussianField.measure (latticeCovarianceGJ …)` by `rfl`.) -/
theorem pairing_memLp_lattice (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : FinLatticeField d N) (p : ℝ≥0) :
    MemLp (fun ω : Configuration (FinLatticeField d N) => ω f) (p : ℝ≥0∞)
      (latticeGaussianMeasure d N a mass ha hmass) :=
  pairing_memLp (latticeCovarianceGJ d N a mass ha hmass) f p

/-- **Raw moment integrability.** `(ω f)ⁿ` is integrable under the lattice GFF (the `n`-th moment of
the pairing is finite, since `ω f ∈ Lⁿ`). -/
theorem integrable_pow_pairing (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : FinLatticeField d N) (n : ℕ) :
    Integrable (fun ω => (ω f) ^ n) (latticeGaussianMeasure d N a mass ha hmass) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [pow_zero]
    exact integrable_const (1 : ℝ)
  · have hmem : MemLp (fun ω : Configuration (FinLatticeField d N) => ω f) (n : ℝ≥0∞)
        (latticeGaussianMeasure d N a mass ha hmass) := by
      exact_mod_cast pairing_memLp_lattice d N a mass ha hmass f n
    have h := hmem.norm_rpow (p := (n : ℝ≥0∞)) (by exact_mod_cast hn.ne') (by simp)
    rw [memLp_one_iff_integrable] at h
    have hint_abs : Integrable (fun ω => |ω f| ^ n)
        (latticeGaussianMeasure d N a mass ha hmass) := by
      refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs]
    exact hint_abs.mono'
      ((configuration_eval_measurable f).pow_const n).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => le_of_eq (by rw [Real.norm_eq_abs, abs_pow]))

/-- **Product of two raw pairing moments is integrable.** `(ω f)ⁿ · (ω g)ᵐ` is integrable under the
lattice GFF — by AM–GM domination `|XY| ≤ ½(X²+Y²)` with `X=(ω f)ⁿ`, `Y=(ω g)ᵐ` and the raw-moment
integrability of `(ω f)²ⁿ`, `(ω g)²ᵐ`. -/
theorem integrable_pow_pairing_mul (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f g : FinLatticeField d N) (n m : ℕ) :
    Integrable (fun ω => (ω f) ^ n * (ω g) ^ m) (latticeGaussianMeasure d N a mass ha hmass) := by
  have hf := integrable_pow_pairing d N a mass ha hmass f (2 * n)
  have hg := integrable_pow_pairing d N a mass ha hmass g (2 * m)
  have hG : Integrable (fun ω => (1 / 2 : ℝ) * ((ω f) ^ (2 * n) + (ω g) ^ (2 * m)))
      (latticeGaussianMeasure d N a mass ha hmass) := (hf.add hg).const_mul _
  refine hG.mono'
    (((configuration_eval_measurable f).pow_const n).mul
      ((configuration_eval_measurable g).pow_const m)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  have hx : (ω f) ^ (2 * n) = ((ω f) ^ n) ^ 2 := by rw [mul_comm, pow_mul]
  have hy : (ω g) ^ (2 * m) = ((ω g) ^ m) ^ 2 := by rw [mul_comm, pow_mul]
  rw [Real.norm_eq_abs, abs_mul, hx, hy]
  nlinarith [two_mul_le_add_sq |(ω f) ^ n| |(ω g) ^ m|, sq_abs ((ω f) ^ n), sq_abs ((ω g) ^ m),
    abs_nonneg ((ω f) ^ n), abs_nonneg ((ω g) ^ m)]

end Pphi2
