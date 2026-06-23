/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.AsymTorus.AsymTraceBridge
import ReflectionPositivity.MultiplicationCLM

/-!
# Truncated slice observable + the `a`-cancellation lemma

**Layer-B2 wiring, Piece 1 of 5** (Route A blueprint, gemini-vetted
2026-06-22). See `planning/layer-B2-scoping.md` for the full route.

The slice-pairing observable `A_g(ψ) := ⟨g, ψ⟩` is a linear functional
on `SpatialField Ns = Fin Ns → ℝ`. As a function on the (infinite-Lebesgue-
measure) `L²(ν)` it is **unbounded**, so the multiplication operator
`M_{A_g} : L²(ν) → L²(ν)` is not a continuous linear map, and the
reflection-positivity bound `connected_two_point_le` (which needs
`M_A : H →L[ℝ] H` bounded) does not literally apply.

The Route-A fix is to truncate: `A_{g,K}(ψ) := clamp(-K, K, ⟨g, ψ⟩)` is
bounded by `K`, so `M_{A_{g,K}}` is a CLM via `mulCLM`. Eventually
(Piece 3) we take `K → ∞` via dominated convergence.

**This file** isolates the atomic Route-A building block: the
**`a`-cancellation lemma** that decouples the truncation parameter `K`
from the lattice spacing `a` (carried by `g = a · δ_site`). The trick:
bound the truncated `‖P₁(M_{A_K} Ω)‖²` by the *exact untruncated*
vacuum variance `∫ ⟨g, x⟩² · Ω(x)² dν`, before any K-limit is taken.
Because the RHS has no `K`-dependence, the `a²` factor pulls out
unconditionally and the K → ∞ limit is purely DCT bookkeeping.

## Main declarations

* `asymSliceObsLinear g` — the linear slice observable `ψ ↦ ⟨g, ψ⟩`.
* `asymSliceObsTrunc g K` — its truncation to `[-K, K]`.
* `asymSliceObsTruncMulCLM g hK` — the multiplication CLM
  `L²(volume) →L[ℝ] L²(volume)` for the truncated observable.
* `norm_sq_proj_obsTrunc_omega_le` — the **`a`-cancellation lemma**:
  the L²-norm of `M_{A_K} Ω − ⟪Ω, M_{A_K} Ω⟫·Ω` is bounded by
  `∫ ⟨g, x⟩² · Ω(x)² dν` — `K`-independent.

## References

* Glimm-Jaffe Ch. 6, 18: bounded-cutoff approximation for unbounded
  observables in the GNS construction.
* `planning/layer-B2-scoping.md`: the full Route-A blueprint and
  vetting verdict.
-/

open MeasureTheory

namespace Pphi2

variable {Ns : ℕ}

/-! ## The linear and truncated slice observables -/

/-- The linear slice observable `A_g(ψ) := ⟨g, ψ⟩`. Unbounded on `SpatialField Ns`
(non-trivial polynomial), so does not directly give a multiplication CLM on
`L²(volume)`. -/
def asymSliceObsLinear (g : SpatialField Ns) (ψ : SpatialField Ns) : ℝ :=
  ∑ i, g i * ψ i

/-- The truncated slice observable `A_{g,K}(ψ) := clamp(-K, K, A_g(ψ))`. Bounded
by `K`, hence in `L^∞`, hence lifts to a continuous linear map on `L²(volume)`. -/
def asymSliceObsTrunc (g : SpatialField Ns) (K : ℝ) (ψ : SpatialField Ns) : ℝ :=
  max (-K) (min K (asymSliceObsLinear g ψ))

/-- The truncated slice observable is bounded by `K` in absolute value (for
`K ≥ 0`). -/
theorem asymSliceObsTrunc_abs_le_bound (g : SpatialField Ns) {K : ℝ} (hK : 0 ≤ K)
    (ψ : SpatialField Ns) :
    |asymSliceObsTrunc g K ψ| ≤ K := by
  unfold asymSliceObsTrunc
  set t := asymSliceObsLinear g ψ
  rcases lt_or_ge t K with htK | htK
  · -- t < K, so `min K t = t`
    rw [min_eq_right htK.le]
    rcases lt_or_ge t (-K) with hKt | hKt
    · -- t < -K, so `max (-K) t = -K`
      rw [max_eq_left hKt.le]; rw [abs_neg]; exact (abs_of_nonneg hK).le
    · -- t ≥ -K, so `max (-K) t = t`
      rw [max_eq_right hKt]; exact abs_le.mpr ⟨hKt, htK.le⟩
  · -- t ≥ K, so `min K t = K`
    rw [min_eq_left htK]
    rw [max_eq_right (by linarith : -K ≤ K)]; exact (abs_of_nonneg hK).le

/-- The truncated observable is dominated by the linear one in absolute value:
`|A_{g,K}(ψ)| ≤ |A_g(ψ)|`. This is the pointwise key step of the `a`-cancellation
lemma. -/
theorem asymSliceObsTrunc_abs_le_linear (g : SpatialField Ns) {K : ℝ} (hK : 0 ≤ K)
    (ψ : SpatialField Ns) :
    |asymSliceObsTrunc g K ψ| ≤ |asymSliceObsLinear g ψ| := by
  unfold asymSliceObsTrunc
  set t := asymSliceObsLinear g ψ
  -- The clamp is closer to 0 than t whenever |t| > K.
  rcases lt_or_ge t (-K) with hLow | hLow
  · -- t < -K: clamp is -K, |clamp| = K, |t| > K so |clamp| ≤ |t|.
    have htK : t < K := lt_of_lt_of_le hLow (by linarith)
    rw [min_eq_right htK.le, max_eq_left hLow.le]
    rw [abs_neg, abs_of_nonneg hK, abs_of_neg (lt_of_lt_of_le hLow (by linarith))]
    linarith
  · rcases lt_or_ge t K with hHigh | hHigh
    · -- -K ≤ t < K: clamp is t itself
      rw [min_eq_right hHigh.le, max_eq_right hLow]
    · -- t ≥ K: clamp is K
      rw [min_eq_left hHigh, max_eq_right (by linarith : -K ≤ K)]
      rw [abs_of_nonneg hK, abs_of_nonneg (le_trans hK hHigh)]
      exact hHigh

/-- The linear slice observable is measurable. -/
theorem asymSliceObsLinear_measurable (g : SpatialField Ns) :
    Measurable (asymSliceObsLinear g) := by
  unfold asymSliceObsLinear
  exact Finset.measurable_sum _ (fun i _ => measurable_const.mul (measurable_pi_apply i))

/-- The truncated slice observable is measurable. -/
theorem asymSliceObsTrunc_measurable (g : SpatialField Ns) (K : ℝ) :
    Measurable (asymSliceObsTrunc g K) := by
  unfold asymSliceObsTrunc
  exact measurable_const.max (measurable_const.min (asymSliceObsLinear_measurable g))

/-! ## The multiplication CLM -/

/-- Multiplication-by-`A_{g,K}` as a continuous linear map on `L²(volume)`. Built
from the existing `mulCLM` with the bound `K`. Requires `K > 0` for the `mulCLM`
constructor (which needs a strictly positive bound). -/
noncomputable def asymSliceObsTruncMulCLM (g : SpatialField Ns) {K : ℝ} (hK : 0 < K) :
    L2SpatialField Ns →L[ℝ] L2SpatialField Ns :=
  mulCLM (asymSliceObsTrunc g K) (asymSliceObsTrunc_measurable g K) K hK
    (Filter.Eventually.of_forall (fun ψ => by
      rw [Real.norm_eq_abs]; exact asymSliceObsTrunc_abs_le_bound g hK.le ψ))

/-- The pointwise representative of `asymSliceObsTruncMulCLM g hK f`. -/
theorem asymSliceObsTruncMulCLM_coeFn (g : SpatialField Ns) {K : ℝ} (hK : 0 < K)
    (f : L2SpatialField Ns) :
    (⇑(asymSliceObsTruncMulCLM g hK f) : SpatialField Ns → ℝ) =ᵐ[volume]
      (fun ψ => asymSliceObsTrunc g K ψ * f ψ) := by
  unfold asymSliceObsTruncMulCLM
  exact mulCLM_spec (asymSliceObsTrunc g K) (asymSliceObsTrunc_measurable g K)
    K hK (Filter.Eventually.of_forall (fun ψ => by
      rw [Real.norm_eq_abs]; exact asymSliceObsTrunc_abs_le_bound g hK.le ψ)) f

/-- `asymSliceObsTruncMulCLM` is self-adjoint (the multiplication is by a real-valued
function). Needed by Piece 2 to feed `connected_two_point_le`. -/
theorem asymSliceObsTruncMulCLM_isSelfAdjoint (g : SpatialField Ns) {K : ℝ} (hK : 0 < K) :
    IsSelfAdjoint (asymSliceObsTruncMulCLM g hK) :=
  mulCLM_isSelfAdjoint (asymSliceObsTrunc g K) (asymSliceObsTrunc_measurable g K)
    K hK (Filter.Eventually.of_forall (fun ψ => by
      rw [Real.norm_eq_abs]; exact asymSliceObsTrunc_abs_le_bound g hK.le ψ))

/-- **Instantiate the `MultiplicationCLMContract` for the truncated slice observable.**
The contract is what the (forthcoming) GNS bridge in `reflection-positivity`
consumes. This is Piece 1's deliverable for downstream Layer-B2 pieces. -/
noncomputable def asymSliceObsTruncContract (g : SpatialField Ns) {K : ℝ} (hK : 0 < K) :
    ReflectionPositivity.MultiplicationCLMContract
      (volume : Measure (SpatialField Ns)) where
  A := asymSliceObsTrunc g K
  A_meas := asymSliceObsTrunc_measurable g K
  A_bound := ⟨K, hK, Filter.Eventually.of_forall
    (fun ψ => asymSliceObsTrunc_abs_le_bound g hK.le ψ)⟩
  M := asymSliceObsTruncMulCLM g hK
  spec := asymSliceObsTruncMulCLM_coeFn g hK
  selfAdjoint := asymSliceObsTruncMulCLM_isSelfAdjoint g hK

/-! ## The a-cancellation lemma

The headline of this file: bound the truncated projection L²-norm by the
**exact** untruncated vacuum variance, in which the truncation parameter
`K` does not appear. This is what decouples the truncation limit `K → ∞`
from the lattice-spacing limit `a → 0` and avoids the crux-2-style
`a`-power error.
-/

/-- Helper: `‖f‖²_{L²} = ∫ a, (f a) * (f a) ∂μ` for `f : Lp ℝ 2 μ`. -/
private theorem L2_norm_sq_eq_integral_mul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (f : Lp ℝ 2 μ) :
    ‖f‖ ^ 2 = ∫ a, (f a) * (f a) ∂μ := by
  rw [← real_inner_self_eq_norm_sq f, L2.inner_def]
  rfl

/-- **The `a`-cancellation lemma** (Route-A core).

`‖M_{A_{g,K}} Ω − ⟪Ω, M_{A_{g,K}} Ω⟫ • Ω‖²_{L²}  ≤  ∫ ⟨g, x⟩² · Ω(x)² dν.`

Three-step chain:
1. `‖P₁ v‖ ≤ ‖v‖` (vacuumPerp is a contraction; `‖Ω‖ = 1`) — `norm_sub_groundProj_le`.
2. `‖M_{A_K} Ω‖² = ∫ A_K(ψ)² · Ω(ψ)² dν` — L²-norm via `L2.inner_def`.
3. `|A_K(ψ)| ≤ |⟨g, ψ⟩|` pointwise — `asymSliceObsTrunc_abs_le_linear`.

Putting it together: `‖P₁(M_{A_K} Ω)‖² ≤ ‖M_{A_K} Ω‖² ≤ ∫ ⟨g,ψ⟩² · Ω(ψ)²`.

The RHS is `K`-independent — the key property for Route A's `K → ∞` limit. -/
theorem norm_sq_proj_obsTrunc_omega_le
    (Nt : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (g : SpatialField Ns) {K : ℝ} (hK : 0 < K)
    (hInt : Integrable (fun ψ => (asymSliceObsLinear g ψ) ^ 2 *
              ((asymGroundVector Nt Ns P a mass ha hmass) ψ) ^ 2) volume) :
    ‖asymSliceObsTruncMulCLM g hK (asymGroundVector Nt Ns P a mass ha hmass)
        - (@inner ℝ _ _ (asymGroundVector Nt Ns P a mass ha hmass)
            (asymSliceObsTruncMulCLM g hK (asymGroundVector Nt Ns P a mass ha hmass))) •
            asymGroundVector Nt Ns P a mass ha hmass‖ ^ 2
      ≤ ∫ ψ, (asymSliceObsLinear g ψ) ^ 2 *
            ((asymGroundVector Nt Ns P a mass ha hmass) ψ) ^ 2 ∂volume := by
  set Ω := asymGroundVector Nt Ns P a mass ha hmass with hΩ_def
  set MK := asymSliceObsTruncMulCLM g hK Ω with hMK_def
  -- Step 1: ‖P₁(MK)‖ ≤ ‖MK‖, hence squared inequality.
  have hcontract : ‖MK - (@inner ℝ _ _ Ω MK) • Ω‖ ≤ ‖MK‖ :=
    norm_sub_groundProj_le (Nt := Nt) (Ns := Ns) P a mass ha hmass MK
  have hcontract_sq : ‖MK - (@inner ℝ _ _ Ω MK) • Ω‖ ^ 2 ≤ ‖MK‖ ^ 2 := by
    have h0 : 0 ≤ ‖MK - (@inner ℝ _ _ Ω MK) • Ω‖ := norm_nonneg _
    nlinarith [hcontract]
  -- Step 2: ‖MK‖² = ∫ (MK ψ) * (MK ψ) ∂volume.
  have hnormSq : ‖MK‖ ^ 2 = ∫ ψ, (MK ψ) * (MK ψ) ∂volume :=
    L2_norm_sq_eq_integral_mul MK
  -- Step 3: pointwise replacement of MK ψ by A_K(ψ) * Ω(ψ).
  have hcoe : (⇑MK : SpatialField Ns → ℝ) =ᵐ[volume]
      (fun ψ => asymSliceObsTrunc g K ψ * Ω ψ) :=
    asymSliceObsTruncMulCLM_coeFn g hK Ω
  have hintegrand_ae : (fun ψ => (MK ψ) * (MK ψ)) =ᵐ[volume]
      (fun ψ => (asymSliceObsTrunc g K ψ) ^ 2 * (Ω ψ) ^ 2) := by
    filter_upwards [hcoe] with ψ hψ
    rw [hψ]; ring
  have hnormSq' : ‖MK‖ ^ 2 = ∫ ψ, (asymSliceObsTrunc g K ψ) ^ 2 * (Ω ψ) ^ 2 ∂volume := by
    rw [hnormSq]; exact integral_congr_ae hintegrand_ae
  -- Step 4: bound by the linear integrand (pointwise A_K² ≤ A_linear²).
  have hpointwise : ∀ ψ, (asymSliceObsTrunc g K ψ) ^ 2 * (Ω ψ) ^ 2 ≤
      (asymSliceObsLinear g ψ) ^ 2 * (Ω ψ) ^ 2 := by
    intro ψ
    have habs : |asymSliceObsTrunc g K ψ| ≤ |asymSliceObsLinear g ψ| :=
      asymSliceObsTrunc_abs_le_linear g hK.le ψ
    have hsq : (asymSliceObsTrunc g K ψ) ^ 2 ≤ (asymSliceObsLinear g ψ) ^ 2 := by
      rw [sq_abs (asymSliceObsTrunc g K ψ) |>.symm, sq_abs (asymSliceObsLinear g ψ) |>.symm]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  -- The integrand on the LHS is integrable (dominated by hInt).
  have hMK_aestronglyMeas :
      AEStronglyMeasurable
        (fun ψ => (asymSliceObsTrunc g K ψ) ^ 2 * (Ω ψ) ^ 2) volume :=
    (((asymSliceObsTrunc_measurable g K).pow_const 2).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable Ω).pow 2))
  have hMK_int : Integrable (fun ψ => (asymSliceObsTrunc g K ψ) ^ 2 * (Ω ψ) ^ 2) volume := by
    refine hInt.mono' hMK_aestronglyMeas ?_
    refine Filter.Eventually.of_forall (fun ψ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact hpointwise ψ
  have hbound : ∫ ψ, (asymSliceObsTrunc g K ψ) ^ 2 * (Ω ψ) ^ 2 ∂volume
      ≤ ∫ ψ, (asymSliceObsLinear g ψ) ^ 2 * (Ω ψ) ^ 2 ∂volume :=
    integral_mono hMK_int hInt hpointwise
  -- Chain everything.
  calc ‖MK - (@inner ℝ _ _ Ω MK) • Ω‖ ^ 2
      ≤ ‖MK‖ ^ 2 := hcontract_sq
    _ = ∫ ψ, (asymSliceObsTrunc g K ψ) ^ 2 * (Ω ψ) ^ 2 ∂volume := hnormSq'
    _ ≤ ∫ ψ, (asymSliceObsLinear g ψ) ^ 2 * (Ω ψ) ^ 2 ∂volume := hbound

end Pphi2
