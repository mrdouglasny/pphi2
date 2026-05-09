/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lattice Setup — Wick-constant-only Decomposition (foundation file)

Defines the **deterministic** smooth/rough decomposition of `V` at
the Wick-constant level:

  `V(ω) = V_S(T, ω) + E_R(T, ω)`,

where `V_S(T)` re-evaluates the lattice interaction polynomial with
Wick subtraction at `c_S(T)` instead of `c_a`, and `E_R(T)` is the
deterministic difference. This file's contents are mostly definitions
and basic algebraic identities used as building blocks.

## ⚠️ Limitation: This decomposition cannot discharge the full bridge axiom

The Wick-constant-only decomposition gives a chaos-2 piece (for pure
quartic) of the form `c_R(T) · a^d · Σ_x :ω(δ_x)²:_{c_a}`. Its `L²`
norm under the GFF involves the **full covariance** Hilbert-Schmidt
norm `‖K‖²_HS = (a^d)^{-2} · Σ_k λ_k^{-2}`, which scales as `N^d`
(not uniformly in `N`).

The full Nelson exp-moment bound, by contrast, is uniform in `N`.
Discharging it requires the **genuine Glimm-Jaffe field
decomposition**: `φ = φ_S + φ_R` with `(φ_S, φ_R)` jointly Gaussian
with covariances `C_S(T), C_R(T)` (both per-mode in covariance, not
a partition of modes). The L² norm of the resulting rough error
then involves `‖C_R‖²_HS`, which `roughCovariance_sq_summable`
controls uniformly in N.

The field-decomposition machinery requires defining a joint measure
`μ_S × μ_R` on `Configuration × Configuration` and proving the
pushforward `(φ_S, φ_R) ↦ φ_S + φ_R` equals the lattice GFF — a
substantial measure-theoretic infrastructure that this file does
*not* build. The contents below are still useful as algebraic
building blocks, and many of the lemmas (especially the smooth-side
bound `latticeSmoothInteraction_lower_bound_at_cutoff_quartic`)
transfer directly to the field-decomposition setting since the
existing smooth bound is universally quantified over the field
argument.

The abstract chain (`DynamicalCutoff`, `LayerCake`, `BridgeFromTail`,
`IntegrabilityHelpers`, `ChaosTailBridge`, `LatticeBridge`) is
**fully reusable** for the field decomposition: it operates on
abstract `V_S, E_R : ℝ → α → ℝ` and is agnostic to which
decomposition produces them.

## Main definitions

* `latticeSmoothInteraction P a mass T`: smooth-side interaction
  with `c_S(T)` Wick subtraction. **Not the genuine `V_S(φ_S)` from
  the Glimm-Jaffe decomposition** — see limitation above.
* `latticeRoughError P a mass T`: deterministic difference
  `V - latticeSmoothInteraction`.

## Main theorems

* `interactionFunctional_eq_smooth_plus_rough`: the decomposition
  identity (immediate by definition).
* `latticeSmoothInteraction_measurable`,
  `latticeRoughError_measurable`: measurability.
* `latticeSmoothInteraction_lower_bound_at_cutoff_quartic`: smooth-side
  classical bound at the dynamical cutoff scale (pure quartic).
  **Transfers directly to the field-decomposition `V_S(φ_S)` since
  the underlying lemma is universally quantified.**
* `wickMonomial_four_diff`: algebraic identity
  `:x⁴:_c - :x⁴:_{c'} = -6(c-c')·:x²:_{c'} + 3(c-c')²`.
* `latticeRoughError_pure_quartic_*`: explicit chaos-2 + constant
  decomposition for pure quartic. **Useful for understanding the
  algebraic structure but does not give a uniform L² bound** —
  superseded by the field-decomposition version.

## Status

Foundation file. The genuine bridge discharge requires building the
field-decomposition layer on top of this; that work is the next
substantive Phase 1 push and is documented in
`docs/polynomial-chaos-exp-moment-bridge-proof-plan.md`.
-/

import Pphi2.NelsonEstimate.CovarianceSplit
import Pphi2.NelsonEstimate.DynamicalCutoff
import Pphi2.NelsonEstimate.SmoothLowerBound
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

/-- **Measurability of the smooth-side interaction.**
Same proof structure as `interactionFunctional_measurable`, with
`smoothWickConstant T` in place of `wickConstant`. -/
theorem latticeSmoothInteraction_measurable
    (P : InteractionPolynomial) (T : ℝ) :
    @Measurable (Configuration (FinLatticeField d N)) ℝ
      instMeasurableSpaceConfiguration (borel ℝ)
      (latticeSmoothInteraction d N a mass P T) := by
  unfold latticeSmoothInteraction
  apply Measurable.const_mul
  apply Finset.measurable_sum _ (fun x _ => ?_)
  -- wickPolynomial P (smoothWickConstant T) is continuous in its argument,
  -- hence measurable; composed with the measurable `ω ↦ ω(δ_x)`, the whole
  -- thing is measurable.
  have h_cont :
      Continuous (fun y : ℝ =>
        wickPolynomial P (smoothWickConstant d N a mass T) y) := by
    have h_pair := wickPolynomial_continuous₂ P
    -- Restrict to the slice {smoothWickConstant T} × ℝ.
    change Continuous (fun y : ℝ =>
      (fun p : ℝ × ℝ => wickPolynomial P p.1 p.2)
        (smoothWickConstant d N a mass T, y))
    exact h_pair.comp (continuous_const.prodMk continuous_id)
  have h_meas : Measurable
      (fun y : ℝ => wickPolynomial P (smoothWickConstant d N a mass T) y) :=
    h_cont.measurable
  exact h_meas.comp (configuration_eval_measurable _)

/-- **Measurability of the rough error.** Difference of measurable
functions is measurable. -/
theorem latticeRoughError_measurable
    (P : InteractionPolynomial) (T : ℝ) :
    @Measurable (Configuration (FinLatticeField d N)) ℝ
      instMeasurableSpaceConfiguration (borel ℝ)
      (latticeRoughError d N a mass P T) := by
  unfold latticeRoughError
  exact (interactionFunctional_measurable d N P a mass).sub
    (latticeSmoothInteraction_measurable d N a mass P T)

/-! ## Pure-monomial case: P with all lower coefficients zero -/

/-- For an `InteractionPolynomial` with all lower coefficients zero
(`P.coeff = 0`), `wickPolynomial P c x` reduces to the leading
monomial `(1/P.n) · wickMonomial P.n c x`. -/
theorem wickPolynomial_of_pure (P : InteractionPolynomial)
    (h_pure : ∀ m : Fin P.n, P.coeff m = 0) (c x : ℝ) :
    wickPolynomial P c x = (1 / P.n : ℝ) * wickMonomial P.n c x := by
  unfold wickPolynomial
  rw [show ∑ m : Fin P.n, P.coeff m * wickMonomial (m : ℕ) c x = 0 from ?_]
  · ring
  · apply Finset.sum_eq_zero
    intro m _
    rw [h_pure m, zero_mul]

/-- **Pure-polynomial smooth interaction = scaled leading Wick monomial sum.**

For `P` with all lower coefficients zero, the lattice smooth
interaction is `(1/P.n)` times the leading Wick monomial sum. -/
theorem latticeSmoothInteraction_of_pure
    (P : InteractionPolynomial) (h_pure : ∀ m : Fin P.n, P.coeff m = 0)
    (T : ℝ) (ω : Configuration (FinLatticeField d N)) :
    latticeSmoothInteraction d N a mass P T ω =
      (1 / P.n : ℝ) *
        (a ^ d * ∑ x : FinLatticeSites d N,
          wickMonomial P.n (smoothWickConstant d N a mass T)
            (ω (finLatticeDelta d N x))) := by
  unfold latticeSmoothInteraction
  simp_rw [wickPolynomial_of_pure P h_pure]
  rw [← Finset.mul_sum, ← mul_assoc, mul_comm (a ^ d) (1 / (P.n : ℝ)), mul_assoc]

/-! ## Smooth-side deterministic bound at the dynamical cutoff scale -/

open Pphi2.DynamicalCutoff

/-- **Smooth-side classical lower bound for the lattice interaction at
the dynamical cutoff scale (pure quartic case).**

For pure quartic `P` (with `P.n = 4` and all coefficients zero) and
`M ≥ 2 · smoothBoundConstant`, the smooth interaction at the
dynamical cutoff scale `T(M) := dynamicalCutoffScale C M` satisfies
`latticeSmoothInteraction P a mass T(M) ω ≥ -M/2` for all `ω`.

This is the `hsmooth` field of `LatticeRoughErrorSetup` for the
pure-quartic case.

**Proof:** By `latticeSmoothInteraction_of_pure`, the smooth
interaction equals `(1/P.n) · X` where
`X = a^d · Σ_x wickMonomial P.n c_S(T) (ω(δ_x))`. By
`smooth_interaction_lower_bound_log_uniform` (with `P.n = 4`),
`X ≥ -smoothBoundConstant · (1+|log T|)²`. By
`dynamicalCutoffScale_log_sq_le`, `smoothBoundConstant · (1+|log T(M)|)² ≤ M/2`
for `M ≥ 2C`. Hence `(1/4) · X ≥ -M/8 ≥ -M/2` (since `M > 0`). -/
theorem latticeSmoothInteraction_lower_bound_at_cutoff_quartic
    (P : InteractionPolynomial) (h_pure : ∀ m : Fin P.n, P.coeff m = 0)
    (h_quartic : P.n = 4)
    (ha : 0 < a) (hmass : 0 < mass)
    (hd : d = 2) (L : ℝ) (hL : 0 < L) (ha_eq : a = L / N)
    (M : ℝ) (hM : 2 * smoothBoundConstant d a mass L ≤ M)
    (ω : Configuration (FinLatticeField d N)) :
    -(M / 2) ≤
      latticeSmoothInteraction d N a mass P
        (dynamicalCutoffScale (smoothBoundConstant d a mass L) M) ω := by
  set T : ℝ := dynamicalCutoffScale (smoothBoundConstant d a mass L) M
  have hC_pos : 0 < smoothBoundConstant d a mass L :=
    smoothBoundConstant_pos d a mass L ha hmass hL
  have hT_pos : 0 < T := dynamicalCutoffScale_pos _ _
  -- Step 1: pure-polynomial reduction.
  rw [latticeSmoothInteraction_of_pure d N a mass P h_pure T ω]
  -- Step 2: smooth bound on `a^d · Σ wickMonomial P.n c_S(T)`.
  have h_lower :
      -(smoothBoundConstant d a mass L * (1 + |Real.log T|) ^ 2) ≤
        a ^ d * ∑ x : FinLatticeSites d N,
          wickMonomial 4 (smoothWickConstant d N a mass T)
            (ω (finLatticeDelta d N x)) :=
    smooth_interaction_lower_bound_log_uniform d N a mass ha hmass hd L hL ha_eq
      T hT_pos (fun x => ω (finLatticeDelta d N x))
  -- Step 3: cutoff inequality.
  have h_cutoff :
      smoothBoundConstant d a mass L * (1 + |Real.log T|) ^ 2 ≤ M / 2 :=
    dynamicalCutoffScale_log_sq_le (smoothBoundConstant d a mass L) M hC_pos hM
  -- Step 4: assemble. Using `P.n = 4` to identify the wick monomials.
  have h_n_eq_4 : (P.n : ℝ) = 4 := by exact_mod_cast h_quartic
  have h_n_pos : (0 : ℝ) < P.n := by rw [h_n_eq_4]; norm_num
  -- Substitute `P.n = 4` into the wick monomial sum.
  have h_sum_eq :
      a ^ d * ∑ x : FinLatticeSites d N,
        wickMonomial P.n (smoothWickConstant d N a mass T)
          (ω (finLatticeDelta d N x)) =
        a ^ d * ∑ x : FinLatticeSites d N,
          wickMonomial 4 (smoothWickConstant d N a mass T)
            (ω (finLatticeDelta d N x)) := by
    rw [h_quartic]
  rw [h_sum_eq]
  -- Sum bound: -M/2 ≤ a^d * Σ wickMonomial 4 ...
  have h_sum :
      -(M / 2) ≤ a ^ d * ∑ x : FinLatticeSites d N,
        wickMonomial 4 (smoothWickConstant d N a mass T)
          (ω (finLatticeDelta d N x)) := by
    linarith
  -- Now show: -(M/2) ≤ (1/P.n) * sum, with 1/P.n = 1/4.
  -- Strategy: (1/P.n) * sum ≥ (1/P.n) * (-M/2) since (1/P.n) ≥ 0,
  -- and (1/P.n) * (-M/2) ≥ -M/2 iff (1/P.n - 1) * (-M/2) ≥ 0 iff
  -- (1 - 1/P.n) * (M/2) ≥ 0, which holds since M ≥ 0 and P.n ≥ 1.
  have hM_nn : 0 ≤ M := by linarith
  have h_n_ge_one : (1 : ℝ) ≤ P.n := by rw [h_n_eq_4]; norm_num
  have h_inv_le_one : (1 : ℝ) / P.n ≤ 1 := by
    rw [div_le_one h_n_pos]; exact h_n_ge_one
  have h_inv_nn : 0 ≤ 1 / (P.n : ℝ) := by positivity
  -- (1/P.n) * sum ≥ (1/P.n) * (-M/2)
  have h_scaled := mul_le_mul_of_nonneg_left h_sum h_inv_nn
  -- (1/P.n) * (-M/2) ≥ -M/2 iff 1 * (-M/2) ≤ (1/P.n) * (-M/2) [flipped]
  -- equivalently: 1 * (M/2) ≥ (1/P.n) * (M/2), i.e., 1 ≥ 1/P.n. ✓
  have h_neg_half_M_le : -(M / 2) ≤ (1 / (P.n : ℝ)) * (-(M / 2)) := by
    have hMhalf_nn : 0 ≤ M / 2 := by linarith
    have : (1 / (P.n : ℝ)) * (M / 2) ≤ M / 2 := by
      calc (1 / (P.n : ℝ)) * (M / 2) ≤ 1 * (M / 2) :=
            mul_le_mul_of_nonneg_right h_inv_le_one hMhalf_nn
        _ = M / 2 := by ring
    linarith
  exact h_neg_half_M_le.trans h_scaled

/-! ## Explicit algebraic structure of the rough error (pure quartic) -/

/-- **Wick monomial difference identity** (degree 4):
`:x⁴:_c - :x⁴:_{c'} = -6(c-c') · :x²:_{c'} + 3(c-c')²`.

This is the key algebraic identity that makes the rough error a
chaos-2 element after subtracting the smooth Wick monomial. The
explicit `latticeRoughError` decomposition into chaos-2 + constant
pieces follows from this identity summed over sites. -/
theorem wickMonomial_four_diff (c c' x : ℝ) :
    wickMonomial 4 c x - wickMonomial 4 c' x =
      -6 * (c - c') * wickMonomial 2 c' x + 3 * (c - c') ^ 2 := by
  rw [wickMonomial_four, wickMonomial_four, wickMonomial_two]
  ring

/-- **Pointwise rough-error decomposition (pure quartic).**

At each site `x`, the difference of Wick polynomials in
`latticeRoughError` reduces to a chaos-2 piece (with prefactor
`c_R(T) = c_a - c_S(T)`) plus a constant piece (with prefactor
`c_R(T)²`). The chaos-2 piece is what gives the polynomial-chaos
concentration after pushforward; the constant piece shrinks
quadratically in `c_R(T)`. -/
theorem wickPolynomial_pure_quartic_diff
    (P : InteractionPolynomial) (h_pure : ∀ m : Fin P.n, P.coeff m = 0)
    (h_quartic : P.n = 4)
    (T : ℝ) (x : FinLatticeSites d N)
    (ω : Configuration (FinLatticeField d N)) :
    wickPolynomial P (wickConstant d N a mass) (ω (finLatticeDelta d N x)) -
      wickPolynomial P (smoothWickConstant d N a mass T)
        (ω (finLatticeDelta d N x)) =
    (1 / (P.n : ℝ)) *
      (-6 * (wickConstant d N a mass - smoothWickConstant d N a mass T) *
            wickMonomial 2 (smoothWickConstant d N a mass T)
              (ω (finLatticeDelta d N x)) +
        3 * (wickConstant d N a mass - smoothWickConstant d N a mass T) ^ 2) := by
  rw [wickPolynomial_of_pure P h_pure, wickPolynomial_of_pure P h_pure, h_quartic]
  have h_diff := wickMonomial_four_diff
    (wickConstant d N a mass) (smoothWickConstant d N a mass T)
    (ω (finLatticeDelta d N x))
  linarith

/-- **`latticeRoughError` as a sum of per-site differences.**

By definition, the rough error is
`a^d Σ_x [wickPolynomial P c_a (ω(δ_x)) - wickPolynomial P c_S(T) (ω(δ_x))]`. -/
theorem latticeRoughError_eq_sum_diff
    (P : InteractionPolynomial) (T : ℝ)
    (ω : Configuration (FinLatticeField d N)) :
    latticeRoughError d N a mass P T ω =
      a ^ d * ∑ x : FinLatticeSites d N,
        (wickPolynomial P (wickConstant d N a mass) (ω (finLatticeDelta d N x)) -
          wickPolynomial P (smoothWickConstant d N a mass T)
            (ω (finLatticeDelta d N x))) := by
  unfold latticeRoughError latticeSmoothInteraction interactionFunctional
  rw [← mul_sub, Finset.sum_sub_distrib]

/-- **Summed pure-quartic rough-error decomposition.**

For pure quartic `P` and any cutoff `T`, the summed rough error
admits the explicit decomposition into a chaos-2-related piece and
a constant piece:

  `latticeRoughError P T ω = (1/P.n) · a^d · Σ_x [-6 · c_R(T) ·
    :ω(δ_x)²:_{c_S(T)} + 3 · c_R(T)²]`

where `c_R(T) := c_a - c_S(T)` is the rough Wick constant. -/
theorem latticeRoughError_pure_quartic_summed
    (P : InteractionPolynomial) (h_pure : ∀ m : Fin P.n, P.coeff m = 0)
    (h_quartic : P.n = 4)
    (T : ℝ) (ω : Configuration (FinLatticeField d N)) :
    latticeRoughError d N a mass P T ω =
      (1 / (P.n : ℝ)) * a ^ d *
        ∑ x : FinLatticeSites d N,
          (-6 * (wickConstant d N a mass - smoothWickConstant d N a mass T) *
              wickMonomial 2 (smoothWickConstant d N a mass T)
                (ω (finLatticeDelta d N x)) +
            3 * (wickConstant d N a mass - smoothWickConstant d N a mass T) ^ 2) := by
  rw [latticeRoughError_eq_sum_diff d N a mass P T ω]
  simp_rw [wickPolynomial_pure_quartic_diff d N a mass P h_pure h_quartic T _ ω]
  rw [← Finset.mul_sum, ← mul_assoc, mul_comm (a ^ d) (1 / (P.n : ℝ)), mul_assoc]

/-- **Wick monomial 2 shift identity:** `:x²:_c = :x²:_{c'} + (c' - c)`.

Both sides equal `x² - c`. Useful for re-expressing the rough error
in terms of the GFF-canonical Wick subtraction (full `c_a`) instead
of the smooth Wick subtraction (`c_S(T)`). -/
theorem wickMonomial_two_shift (c c' x : ℝ) :
    wickMonomial 2 c x = wickMonomial 2 c' x + (c' - c) := by
  rw [wickMonomial_two, wickMonomial_two]; ring

/-- **Pure-quartic rough error in chaos-2 form (with full `c_a` Wick
subtraction).**

After re-expressing `:ω(δ_x)²:_{c_S(T)} = :ω(δ_x)²:_{c_a} + c_R(T)`
(using `wickMonomial_two_shift`) and simplifying, the rough error
admits the cleaner decomposition

  `latticeRoughError P T ω = -(3/2) · c_R(T) · a^d · Σ_x :ω(δ_x)²:_{c_a}
    - (3/4) · c_R(T)² · a^d · (Fintype.card (FinLatticeSites d N))`

where:
* The first term is a **chaos-2 element** of `L²(GFF)` (under the
  full Wick subtraction `c_a` it is centered: `E[:ω(δ_x)²:_{c_a}] = 0`),
  scaled by the small prefactor `c_R(T)`.
* The second term is a **constant** (function-independent of `ω`),
  scaled by `c_R(T)²` (which shrinks faster as `T → 0`).

This form is what the Phase 1 chaos+L² analysis directly uses:
Wick orthogonality on `Σ_x :ω(δ_x)²:_{c_a}` gives the L² bound
proportional to the rough-covariance Hilbert-Schmidt norm
(controlled by `roughCovariance_sq_summable`). -/
theorem latticeRoughError_pure_quartic_chaos2_form
    (P : InteractionPolynomial) (h_pure : ∀ m : Fin P.n, P.coeff m = 0)
    (h_quartic : P.n = 4)
    (T : ℝ) (ω : Configuration (FinLatticeField d N)) :
    latticeRoughError d N a mass P T ω =
      -(3 / 2 : ℝ) * (wickConstant d N a mass - smoothWickConstant d N a mass T) *
        a ^ d * ∑ x : FinLatticeSites d N,
          wickMonomial 2 (wickConstant d N a mass) (ω (finLatticeDelta d N x)) -
      (3 / 4 : ℝ) * (wickConstant d N a mass - smoothWickConstant d N a mass T) ^ 2 *
        a ^ d * (Fintype.card (FinLatticeSites d N) : ℝ) := by
  rw [latticeRoughError_pure_quartic_summed d N a mass P h_pure h_quartic T ω]
  rw [h_quartic]
  -- Rewrite each wickMonomial 2 c_S to wickMonomial 2 c_a + (c_a - c_S).
  have h_shift : ∀ x : FinLatticeSites d N,
      wickMonomial 2 (smoothWickConstant d N a mass T)
        (ω (finLatticeDelta d N x)) =
      wickMonomial 2 (wickConstant d N a mass)
        (ω (finLatticeDelta d N x)) +
      (wickConstant d N a mass - smoothWickConstant d N a mass T) :=
    fun x => wickMonomial_two_shift _ _ _
  simp_rw [h_shift]
  -- Goal: 1/4 · a^d · Σ_x [-6 c_R · (wickMonomial 2 c_a (ω(δ_x)) + c_R) + 3 c_R²]
  --       = -(3/2) c_R · a^d · Σ_x wickMonomial 2 c_a (...) - (3/4) c_R² · a^d · |Λ|.
  set c_R : ℝ :=
    wickConstant d N a mass - smoothWickConstant d N a mass T with hc_R_def
  -- Pull `-6 c_R · _ + (-3 c_R²)` out of the sum.
  simp_rw [show ∀ x : FinLatticeSites d N,
      (-6 * c_R *
        (wickMonomial 2 (wickConstant d N a mass)
          (ω (finLatticeDelta d N x)) + c_R) +
        3 * c_R ^ 2) =
      -6 * c_R *
        wickMonomial 2 (wickConstant d N a mass)
          (ω (finLatticeDelta d N x)) + (-3 * c_R ^ 2)
      from fun _ => by ring]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum]
  ring

/-! ## Chaos-2 sum: the variable-of-`ω` part of the pure-quartic rough error -/

/-- The "chaos-2 sum" appearing in the pure-quartic rough error
decomposition: `Σ_x :ω(δ_x)²:_{c_a}`. Under the lattice GFF,
each term is a centered chaos-2 random variable; summed, this is
itself in chaos-2. -/
noncomputable def latticeWickSquareSum :
    Configuration (FinLatticeField d N) → ℝ :=
  fun ω => ∑ x : FinLatticeSites d N,
    wickMonomial 2 (wickConstant d N a mass) (ω (finLatticeDelta d N x))

/-- Measurability of the chaos-2 sum. Same proof structure as
`latticeSmoothInteraction_measurable`. -/
theorem latticeWickSquareSum_measurable :
    @Measurable (Configuration (FinLatticeField d N)) ℝ
      instMeasurableSpaceConfiguration (borel ℝ)
      (latticeWickSquareSum d N a mass) := by
  unfold latticeWickSquareSum
  apply Finset.measurable_sum _ (fun x _ => ?_)
  have h_cont : Continuous (fun y : ℝ =>
      wickMonomial 2 (wickConstant d N a mass) y) := by
    have h_pair := wickMonomial_continuous₂ 2
    change Continuous (fun y : ℝ =>
      (fun p : ℝ × ℝ => wickMonomial 2 p.1 p.2)
        (wickConstant d N a mass, y))
    exact h_pair.comp (continuous_const.prodMk continuous_id)
  exact h_cont.measurable.comp (configuration_eval_measurable _)

end Pphi2.LatticeSetup
