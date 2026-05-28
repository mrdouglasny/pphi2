/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Smooth-Interaction Lower Bound on the Isotropic Z_Nt × Z_Ns Lattice

Port of `Pphi2/NelsonEstimate/RoughErrorBound.lean:164–376` (the canonical-joint
smooth-interaction lower bound + its dynamical-cutoff `-(M/2)` form) to the
isotropic rectangular lattice.  This is **UNIT 2** of the §2 port toward
discharging `asymChaosCutoffDecomposition`.

## Main results

* `asymCanonicalSmoothInteraction_lower_bound_log_uniform` —
  `∃ C > 0` so that for every `(Nt, Ns, a)` with `Nt·a = Lt`, `Ns·a = Ls`,
  every `T > 0`, and every `η : AsymCanonicalJoint Nt Ns`,
  `-(C·(1+|log T|)^k) ≤ asymCanonicalSmoothInteraction Nt Ns a mass T P η`
  where `k = degreeCutoffPower P`. Uniform in `(Nt, Ns, a)` at fixed `(Lt, Ls)`.

* `asymCanonicalSmoothInteraction_lower_bound_at_cutoff_uniform` — at the
  dynamical-cutoff scale `T(M) = degreeDynamicalCutoffScale P C M`, the lower
  bound takes the canonical `-(M/2)` form (for `M ≥ 2C`). This is the input the
  Nelson `asymChaosCutoffDecomposition` engine needs.

## Method

Mirrors the square `canonicalSmoothInteraction_lower_bound_log_uniform_in_aN`
(`RoughErrorBound.lean:164`). The asym `asymCanonicalSmoothInteraction` def is
already in the per-site form
`a² · Σ_x wickPolynomial P c_S (φ_S x)`, so no `latticeSmoothInteraction`
bridge is needed. Substitutions:

* `L^d` → `Lt * Ls`
* `a^d · |Λ| = L^d`  → `a² · |AsymLatticeSites Nt Ns| = Lt * Ls`
* `smoothWickConstant_le_log_uniform_in_aN` → `asymSmoothWickConstant_le_log_uniform`
  (proved in `AsymCovarianceBoundsGJ.lean`).

References: Glimm-Jaffe Ch. 8, Simon V.12.
-/

import Pphi2.NelsonEstimate.AsymCovarianceBoundsGJ
import Pphi2.NelsonEstimate.DynamicalCutoff
import Pphi2.WickOrdering.WickPolynomial

noncomputable section

open GaussianField

namespace Pphi2

open Finset

/-! ### Local helpers -/

/-- Asym canonical-eigenvalue positivity (mirrors the inline proof used in
`asymCanonicalSmoothWeight_eq_integral_Ioi`). -/
private lemma asymCanonicalEigenvalue_pos_local
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (_ha : 0 < a) (hmass : 0 < mass)
    (m : AsymCanonicalMode Nt Ns) :
    0 < asymCanonicalEigenvalue Nt Ns a mass m := by
  unfold asymCanonicalEigenvalue
  have h1 := latticeEigenvalue1d_nonneg Nt a (m.1 : ℕ)
  have h2 := latticeEigenvalue1d_nonneg Ns a (m.2 : ℕ)
  nlinarith [sq_pos_of_pos hmass]

/-- The asym smooth Wick-constant is non-negative. -/
private lemma asymSmoothWickConstant_nonneg
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) :
    0 ≤ asymSmoothWickConstant Nt Ns a mass T := by
  unfold asymSmoothWickConstant
  have ha2_pos : (0 : ℝ) < a ^ 2 := by positivity
  refine mul_nonneg (inv_nonneg.mpr ha2_pos.le) ?_
  refine mul_nonneg (by positivity) ?_
  refine Finset.sum_nonneg fun m₁ _ => Finset.sum_nonneg fun m₂ _ => ?_
  -- asymCanonicalSmoothWeight = exp(-T·λ)/λ ≥ 0, since exp > 0 and λ > 0.
  unfold asymCanonicalSmoothWeight
  have hlam : 0 < asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂) :=
    asymCanonicalEigenvalue_pos_local Nt Ns a mass ha hmass (m₁, m₂)
  exact div_nonneg (Real.exp_pos _).le hlam.le

/-- Volume identity on the rectangular lattice: `a² · (Nt · Ns) = Lt · Ls`. -/
private lemma asym_volume_eq
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a Lt Ls : ℝ) (hvolt : (Nt : ℝ) * a = Lt) (hvols : (Ns : ℝ) * a = Ls) :
    a ^ 2 * (Fintype.card (AsymLatticeSites Nt Ns) : ℝ) = Lt * Ls := by
  have hcard_nat : Fintype.card (AsymLatticeSites Nt Ns) = Nt * Ns := by
    simp [AsymLatticeSites]
  have hcard : (Fintype.card (AsymLatticeSites Nt Ns) : ℝ) = (Nt : ℝ) * (Ns : ℝ) := by
    rw [hcard_nat]; push_cast; ring
  calc a ^ 2 * (Fintype.card (AsymLatticeSites Nt Ns) : ℝ)
      = a ^ 2 * ((Nt : ℝ) * (Ns : ℝ)) := by rw [hcard]
    _ = ((Nt : ℝ) * a) * ((Ns : ℝ) * a) := by ring
    _ = Lt * Ls := by rw [hvolt, hvols]

/-! ### Main results -/

/-- **Uniform-in-`(Nt, Ns, a)` smooth-side classical lower bound on the
rectangular lattice.** At fixed periods `Lt, Ls` and mass `mass`, the smooth
interaction admits a polylogarithmic lower bound with a constant depending
only on `(Lt, Ls, mass, P)`, not on `(Nt, Ns, a)` separately. Uses the proved
heterogeneous heat-kernel bound `asymSmoothWickConstant_le_log_uniform` and
the generic Wick-polynomial pointwise lower bound `wickPolynomial_lower_bound_general`. -/
theorem asymCanonicalSmoothInteraction_lower_bound_log_uniform
    (P : InteractionPolynomial)
    (mass Lt Ls : ℝ) (hLt : 0 < Lt) (hLs : 0 < Ls) (hmass : 0 < mass) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (_ha : 0 < a),
        (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
        ∀ (T : ℝ), 0 < T →
        ∀ (η : AsymCanonicalJoint Nt Ns),
          -(C * (1 + |Real.log T|) ^ Pphi2.DynamicalCutoff.degreeCutoffPower P) ≤
            asymCanonicalSmoothInteraction Nt Ns a mass T P η := by
  obtain ⟨A, B, hA_nn, hB_nn, hABound⟩ :=
    asymSmoothWickConstant_le_log_uniform mass Lt Ls hLt hLs hmass
  obtain ⟨A0, hA0_nn, hpoly_lb⟩ := wickPolynomial_lower_bound_general P
  let K : ℝ := A + B
  let C : ℝ :=
    Lt * Ls * A0 * (1 + K ^ Pphi2.DynamicalCutoff.degreeCutoffPower P) + 1
  refine ⟨C, by positivity, ?_⟩
  intro Nt Ns hNt hNs a ha hvolt hvols T hT η
  -- Smooth-constant non-negativity and upper bound.
  have hc_S_nn : 0 ≤ asymSmoothWickConstant Nt Ns a mass T :=
    asymSmoothWickConstant_nonneg Nt Ns a mass ha hmass T
  have hu_one : 1 ≤ 1 + |Real.log T| := by
    linarith [abs_nonneg (Real.log T)]
  have hA_le : A ≤ A * (1 + |Real.log T|) := by
    simpa using mul_le_mul_of_nonneg_left hu_one hA_nn
  have h_cS_bound :
      asymSmoothWickConstant Nt Ns a mass T ≤ K * (1 + |Real.log T|) := by
    calc
      asymSmoothWickConstant Nt Ns a mass T
          ≤ A + B * (1 + |Real.log T|) := hABound Nt Ns a ha hvolt hvols T hT
      _ ≤ A * (1 + |Real.log T|) + B * (1 + |Real.log T|) := by linarith
      _ = K * (1 + |Real.log T|) := by simp [K]; ring
  -- Volume identity.
  have hvol_pow :
      a ^ 2 * (Fintype.card (AsymLatticeSites Nt Ns) : ℝ) = Lt * Ls :=
    asym_volume_eq Nt Ns a Lt Ls hvolt hvols
  -- Per-site lower bound, summed and scaled by a².
  have h_lower :
      -(Lt * Ls * A0 *
          (1 + asymSmoothWickConstant Nt Ns a mass T ^
            Pphi2.DynamicalCutoff.degreeCutoffPower P)) ≤
        a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
          wickPolynomial P (asymSmoothWickConstant Nt Ns a mass T)
            (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x) := by
    have h_site :
        ∀ x : AsymLatticeSites Nt Ns,
          -(A0 * (1 + asymSmoothWickConstant Nt Ns a mass T ^
              Pphi2.DynamicalCutoff.degreeCutoffPower P)) ≤
            wickPolynomial P (asymSmoothWickConstant Nt Ns a mass T)
              (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x) := by
      intro x
      simpa [Pphi2.DynamicalCutoff.degreeCutoffPower] using
        hpoly_lb (asymSmoothWickConstant Nt Ns a mass T)
          (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x) hc_S_nn
    have h_sum_const :
        -((Fintype.card (AsymLatticeSites Nt Ns) : ℝ) *
            (A0 * (1 + asymSmoothWickConstant Nt Ns a mass T ^
              Pphi2.DynamicalCutoff.degreeCutoffPower P))) ≤
          ∑ x : AsymLatticeSites Nt Ns,
            wickPolynomial P (asymSmoothWickConstant Nt Ns a mass T)
              (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x) := by
      calc
        ∑ x : AsymLatticeSites Nt Ns,
            wickPolynomial P (asymSmoothWickConstant Nt Ns a mass T)
              (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x)
            ≥ ∑ _x : AsymLatticeSites Nt Ns,
                (-(A0 * (1 + asymSmoothWickConstant Nt Ns a mass T ^
                  Pphi2.DynamicalCutoff.degreeCutoffPower P))) :=
              Finset.sum_le_sum fun x _ => h_site x
        _ = (Fintype.card (AsymLatticeSites Nt Ns) : ℝ) *
              (-(A0 * (1 + asymSmoothWickConstant Nt Ns a mass T ^
                Pphi2.DynamicalCutoff.degreeCutoffPower P))) := by
              simp [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        _ = _ := by ring
    have ha_pow_nonneg : 0 ≤ a ^ 2 := by positivity
    have h_scaled := mul_le_mul_of_nonneg_left h_sum_const ha_pow_nonneg
    have hscaled_eq :
        a ^ 2 *
            -(↑(Fintype.card (AsymLatticeSites Nt Ns)) *
                (A0 *
                  (1 + asymSmoothWickConstant Nt Ns a mass T ^
                    Pphi2.DynamicalCutoff.degreeCutoffPower P))) =
          -(Lt * Ls * A0 *
              (1 + asymSmoothWickConstant Nt Ns a mass T ^
                Pphi2.DynamicalCutoff.degreeCutoffPower P)) := by
      calc
        a ^ 2 *
            -(↑(Fintype.card (AsymLatticeSites Nt Ns)) *
                (A0 *
                  (1 + asymSmoothWickConstant Nt Ns a mass T ^
                    Pphi2.DynamicalCutoff.degreeCutoffPower P)))
            = -(a ^ 2 * ↑(Fintype.card (AsymLatticeSites Nt Ns)) *
                (A0 *
                  (1 + asymSmoothWickConstant Nt Ns a mass T ^
                    Pphi2.DynamicalCutoff.degreeCutoffPower P))) := by ring
        _ = -(Lt * Ls * A0 *
              (1 + asymSmoothWickConstant Nt Ns a mass T ^
                Pphi2.DynamicalCutoff.degreeCutoffPower P)) := by
              rw [hvol_pow]; ring
    rw [hscaled_eq] at h_scaled
    exact h_scaled
  -- Inflate the (1 + c_S^k) factor to (1 + K^k)·(1+|log T|)^k.
  have hu_pow_one :
      1 ≤ (1 + |Real.log T|) ^ Pphi2.DynamicalCutoff.degreeCutoffPower P := by
    have := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hu_one
      (Pphi2.DynamicalCutoff.degreeCutoffPower P)
    simpa using this
  have hpow_bound :
      1 + asymSmoothWickConstant Nt Ns a mass T ^
            Pphi2.DynamicalCutoff.degreeCutoffPower P ≤
        (1 + K ^ Pphi2.DynamicalCutoff.degreeCutoffPower P) *
          (1 + |Real.log T|) ^ Pphi2.DynamicalCutoff.degreeCutoffPower P := by
    have hpow :
        asymSmoothWickConstant Nt Ns a mass T ^
            Pphi2.DynamicalCutoff.degreeCutoffPower P ≤
          (K * (1 + |Real.log T|)) ^
            Pphi2.DynamicalCutoff.degreeCutoffPower P := by
      exact pow_le_pow_left₀ hc_S_nn h_cS_bound _
    calc
      1 + asymSmoothWickConstant Nt Ns a mass T ^
            Pphi2.DynamicalCutoff.degreeCutoffPower P
          ≤ 1 + (K * (1 + |Real.log T|)) ^
              Pphi2.DynamicalCutoff.degreeCutoffPower P := by linarith
      _ = 1 + K ^ Pphi2.DynamicalCutoff.degreeCutoffPower P *
            (1 + |Real.log T|) ^ Pphi2.DynamicalCutoff.degreeCutoffPower P := by
              rw [mul_pow]
      _ ≤ (1 + |Real.log T|) ^ Pphi2.DynamicalCutoff.degreeCutoffPower P +
            K ^ Pphi2.DynamicalCutoff.degreeCutoffPower P *
              (1 + |Real.log T|) ^ Pphi2.DynamicalCutoff.degreeCutoffPower P := by
              linarith
      _ = (1 + K ^ Pphi2.DynamicalCutoff.degreeCutoffPower P) *
            (1 + |Real.log T|) ^ Pphi2.DynamicalCutoff.degreeCutoffPower P := by ring
  -- Chain through to the desired C.
  have h_sum :
      -(Lt * Ls * A0 * (1 + K ^ Pphi2.DynamicalCutoff.degreeCutoffPower P) *
          (1 + |Real.log T|) ^ Pphi2.DynamicalCutoff.degreeCutoffPower P) ≤
        a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
          wickPolynomial P (asymSmoothWickConstant Nt Ns a mass T)
            (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x) := by
    have h_chain :
        -(Lt * Ls * A0 * (1 + K ^ Pphi2.DynamicalCutoff.degreeCutoffPower P) *
            (1 + |Real.log T|) ^ Pphi2.DynamicalCutoff.degreeCutoffPower P) ≤
          -(Lt * Ls * A0 *
            (1 + asymSmoothWickConstant Nt Ns a mass T ^
              Pphi2.DynamicalCutoff.degreeCutoffPower P)) := by
      apply neg_le_neg
      have hpref_nonneg : 0 ≤ Lt * Ls * A0 := by positivity
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hpow_bound hpref_nonneg
    exact le_trans h_chain h_lower
  have hC_ge :
      Lt * Ls * A0 * (1 + K ^ Pphi2.DynamicalCutoff.degreeCutoffPower P) ≤ C := by
    simp [C]
  have h_sum' :
      -(C * (1 + |Real.log T|) ^ Pphi2.DynamicalCutoff.degreeCutoffPower P) ≤
        a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
          wickPolynomial P (asymSmoothWickConstant Nt Ns a mass T)
            (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x) := by
    have h_chain :
        -(C * (1 + |Real.log T|) ^ Pphi2.DynamicalCutoff.degreeCutoffPower P) ≤
          -(Lt * Ls * A0 * (1 + K ^ Pphi2.DynamicalCutoff.degreeCutoffPower P) *
            (1 + |Real.log T|) ^ Pphi2.DynamicalCutoff.degreeCutoffPower P) := by
      apply neg_le_neg
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hC_ge
          (show 0 ≤ (1 + |Real.log T|) ^
            Pphi2.DynamicalCutoff.degreeCutoffPower P by positivity)
    exact le_trans h_chain h_sum
  -- Unfold asymCanonicalSmoothInteraction.
  unfold asymCanonicalSmoothInteraction
  exact h_sum'

/-- **The `-(M/2)` form at the dynamical-cutoff scale.** This is the input the
Nelson chaos-decomposition engine consumes: at `T(M) = degreeDynamicalCutoffScale P C M`
the smooth interaction is bounded below by `-(M/2)` for all `M ≥ 2C`. -/
theorem asymCanonicalSmoothInteraction_lower_bound_at_cutoff_uniform
    (P : InteractionPolynomial)
    (mass Lt Ls : ℝ) (hLt : 0 < Lt) (hLs : 0 < Ls) (hmass : 0 < mass) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (_ha : 0 < a),
        (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
        ∀ (M : ℝ), 2 * C ≤ M →
        ∀ (η : AsymCanonicalJoint Nt Ns),
          -(M / 2) ≤
            asymCanonicalSmoothInteraction Nt Ns a mass
              (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M) P η := by
  obtain ⟨C, hC_pos, hbound⟩ :=
    asymCanonicalSmoothInteraction_lower_bound_log_uniform P mass Lt Ls hLt hLs hmass
  refine ⟨C, hC_pos, ?_⟩
  intro Nt Ns hNt hNs a ha hvolt hvols M hM η
  have hT_pos :
      0 < Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M :=
    Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale_pos P C M
  have h_smooth :=
    hbound Nt Ns a ha hvolt hvols
      (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M) hT_pos η
  have h_cutoff :
      C * (1 + |Real.log
            (Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale P C M)|) ^
          Pphi2.DynamicalCutoff.degreeCutoffPower P ≤ M / 2 :=
    Pphi2.DynamicalCutoff.degreeDynamicalCutoffScale_log_pow_le P C M hC_pos hM
  linarith

end Pphi2

end
