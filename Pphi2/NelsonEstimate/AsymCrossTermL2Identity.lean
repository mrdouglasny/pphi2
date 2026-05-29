/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Wick L² inner-product identity for asym smooth/rough cross terms

Discharge of the per-cross-term L² bound `asymCanonicalCrossTerm_l2_sq_le`
(`AsymRoughErrorVariance.lean:144`) — the only remaining documented sorry
on the `cylinder-isotropic-lattice` branch toward `asymChaosCutoffDecomposition`.

The genuine analytical content is the Wick L² identity

  ∫ (CrossTerm_{k,j})² dη
    = (a²)² · j! · (k−j)! · Σ_{x,y} C_S(x,y)^j · C_R(x,y)^(k−j)

where C_S, C_R are the smooth/rough covariances. This sits on top of three
fully proved upstream identities:

  * `wickPower_two_site_pi_gaussianReal_eq_diag` (FieldDecomposition.lean:3236,
    made public in this session) — the index-polymorphic Wick L² identity over
    a standard-Gaussian product measure.
  * `gaussian-hilbert/HermitePolynomials.hermiteMulti_orthogonality` — the
    bedrock multivariate Hermite orthogonality.
  * The asym FieldDecomposition pushforward identity `pushforward_eq_GFF`.

All asym-side work is mechanical translation that plugs the asym mode
index `Fin Nt × Fin Ns` into the index-polymorphic helpers.

## Structure

  * §1 `asymCanonical{Smooth,Rough}Gamma` defs — linear coefficients such
       that `φ_S(η, x) = Σ_m γ_x(m) · η(m)`.
  * §2 Site-variance identity `Σ_m γ_x(m)² = asymSmoothWickConstant` via
       translation invariance of the smooth diagonal (mirrors the proved
       `wickConstantAsym_eq_variance`).
  * §3 `asymCanonicalSmoothCovariance` def and the cross-pair identity
       `Σ_m γ_x(m) · γ_y(m) = asymCanonicalSmoothCovariance(x, y)`.
  * §4 The 6 `_two_site_marginal_*` lemmas (thin wrappers around the public
       generic helpers).
  * §5 The cross-term L² covSum identity.
  * §6 `|asymCanonicalSmoothCovariance| ≤ asymSmoothWickConstant`.
  * §7 Unified rough-covariance row-sum (case-split p = 1, 2, ≥ 3).
  * §8 Discharge `asymCanonicalCrossTerm_l2_sq_le`.
-/

import Pphi2.AsymTorus.AsymWickVariance
import Pphi2.AsymTorus.AsymWickMean
import Pphi2.NelsonEstimate.AsymRoughCovarianceHigherP
import Pphi2.NelsonEstimate.WickBinomial
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section

open GaussianField MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Pphi2

/-! ## Cross-term definitions

These are moved here so the cross-term L² identity can be proved in the same
module without creating a circular import with `AsymRoughErrorVariance`. -/

/-- The rough Wick subtraction constant for the asym smooth/rough split. -/
def asymCanonicalRoughWickConstant (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) : ℝ :=
  wickConstantAsym Nt Ns a mass - asymSmoothWickConstant Nt Ns a mass T

/-- Per-`(k,j)` smooth/rough cross term in the asym rough-error expansion. -/
def asymCanonicalCrossTerm (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (η : AsymCanonicalJoint Nt Ns) (k j : ℕ) : ℝ :=
  a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
    wickMonomial j (asymSmoothWickConstant Nt Ns a mass T)
      (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x) *
    wickMonomial (k - j) (asymCanonicalRoughWickConstant Nt Ns a mass T)
      (asymCanonicalRoughFieldFunction Nt Ns a mass T η x)

/-! ## §1 Asym gamma coefficients

`γ_x(m) = (√(a²))⁻¹ · asymCanonicalSmoothModeCoeff(x, m)` (smooth side),
and the rough analog. This is exactly the coefficient pulled out of the
linear `φ_S(η_S, x) = Σ_m γ_x(m) · η_S(m)` form. -/

/-- Smooth gamma coefficient on the rectangular lattice. -/
def asymCanonicalSmoothGamma (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (x : AsymLatticeSites Nt Ns)
    (m : AsymCanonicalMode Nt Ns) : ℝ :=
  (Real.sqrt (a ^ 2))⁻¹ * asymCanonicalSmoothModeCoeff Nt Ns a mass T x m

/-- Rough gamma coefficient on the rectangular lattice. -/
def asymCanonicalRoughGamma (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (x : AsymLatticeSites Nt Ns)
    (m : AsymCanonicalMode Nt Ns) : ℝ :=
  (Real.sqrt (a ^ 2))⁻¹ * asymCanonicalRoughModeCoeff Nt Ns a mass T x m

/-- The smooth field slice as a linear combination of the first-factor std
Gaussian coordinates, with coefficients `asymCanonicalSmoothGamma`. -/
theorem asymCanonicalSmoothFieldFunctionOfFst_eq_sum_gamma
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (ηS : AsymCanonicalMode Nt Ns → ℝ)
    (x : AsymLatticeSites Nt Ns) :
    asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS x =
      ∑ m : AsymCanonicalMode Nt Ns,
        asymCanonicalSmoothGamma Nt Ns a mass T x m * ηS m := by
  unfold asymCanonicalSmoothFieldFunctionOfFst asymCanonicalSmoothGamma
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro m hm
  ring

/-- The rough field slice as a linear combination of the second-factor std
Gaussian coordinates, with coefficients `asymCanonicalRoughGamma`. -/
theorem asymCanonicalRoughFieldFunctionOfSnd_eq_sum_gamma
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (ηR : AsymCanonicalMode Nt Ns → ℝ)
    (x : AsymLatticeSites Nt Ns) :
    asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR x =
      ∑ m : AsymCanonicalMode Nt Ns,
        asymCanonicalRoughGamma Nt Ns a mass T x m * ηR m := by
  unfold asymCanonicalRoughFieldFunctionOfSnd asymCanonicalRoughGamma
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro m hm
  ring

/-! ## §2 Smooth/rough covariance kernels and diagonal identities -/

/-- Smooth covariance kernel of the asym canonical field split. -/
noncomputable def asymCanonicalSmoothCovariance
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (x y : AsymLatticeSites Nt Ns) : ℝ :=
  (a ^ 2 : ℝ)⁻¹ *
    ∑ m : AsymCanonicalMode Nt Ns,
      asymCanonicalSmoothWeight Nt Ns a mass T m *
        asymCanonicalBasis Nt Ns m x *
        asymCanonicalBasis Nt Ns m y /
        asymCanonicalNormSq Nt Ns m

private def fin1Site {N : ℕ} [NeZero N] (z : ZMod N) : FinLatticeSites 1 N :=
  zmodToFin1 N z

private def fin1FunEquiv (N : ℕ) : (Fin 1 → Fin N) ≃ Fin N where
  toFun f := f 0
  invFun m := fun _ => m
  left_inv f := by
    funext i
    fin_cases i
    rfl
  right_inv m := rfl

private lemma sum_fun_fin1_eq_sum {α : Type*} [AddCommMonoid α]
    (N : ℕ) [NeZero N] (F : (Fin 1 → Fin N) → α) :
    ∑ m : Fin 1 → Fin N, F m = ∑ m : Fin N, F (fun _ => m) := by
  refine Fintype.sum_equiv (fin1FunEquiv N) F (fun m => F (fun _ => m)) ?_
  intro m
  exact congrArg F ((fin1FunEquiv N).left_inv m).symm

private lemma asymCanonicalEigenvalue_pos
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (_ha : 0 < a) (hmass : 0 < mass)
    (m : AsymCanonicalMode Nt Ns) :
    0 < asymCanonicalEigenvalue Nt Ns a mass m := by
  unfold asymCanonicalEigenvalue
  have h1 := latticeEigenvalue1d_nonneg Nt a m.1
  have h2 := latticeEigenvalue1d_nonneg Ns a m.2
  nlinarith [sq_pos_of_pos hmass]

private lemma asymCanonicalSmoothWeight_nonneg
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (m : AsymCanonicalMode Nt Ns) :
    0 ≤ asymCanonicalSmoothWeight Nt Ns a mass T m := by
  unfold asymCanonicalSmoothWeight
  exact div_nonneg (le_of_lt (Real.exp_pos _))
    (asymCanonicalEigenvalue_pos Nt Ns a mass ha hmass m).le

private lemma asymCanonicalRoughWeight_nonneg
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T) (m : AsymCanonicalMode Nt Ns) :
    0 ≤ asymCanonicalRoughWeight Nt Ns a mass T m := by
  unfold asymCanonicalRoughWeight
  have hLam := asymCanonicalEigenvalue_pos Nt Ns a mass ha hmass m
  have hExp : Real.exp (-T * asymCanonicalEigenvalue Nt Ns a mass m) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith
  have hNum : 0 ≤ 1 - Real.exp (-T * asymCanonicalEigenvalue Nt Ns a mass m) := by
    linarith
  exact div_nonneg hNum hLam.le

private def asymHeatKernelMatrix
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a t : ℝ) (x y : AsymLatticeSites Nt Ns) : ℝ :=
  latticeHeatKernelMatrix 1 Nt a t (fin1Site x.1) (fin1Site y.1) *
    latticeHeatKernelMatrix 1 Ns a t (fin1Site x.2) (fin1Site y.2)

private lemma oneDim_heatKernel_entry_eq_sum
    (N : ℕ) [NeZero N] (a : ℝ) (ha : a ≠ 0) (t : ℝ)
    (x y : ZMod N) :
    latticeHeatKernelMatrix 1 N a t (fin1Site x) (fin1Site y) =
      ∑ m : Fin N,
        Real.exp (-t * latticeEigenvalue1d N a m) *
          latticeFourierBasisFun N m x *
          latticeFourierBasisFun N m y /
          latticeFourierNormSq N m := by
  have hbase :=
    latticeHeatKernel_entry_eq_eigenvalue_average
      (d := 1) (N := N) (a := a) ha t (fin1Site x) (fin1Site y)
  rw [hbase, sum_fun_fin1_eq_sum N]
  refine Finset.sum_congr rfl ?_
  intro m hm
  simp [fin1Site, zmodToFin1, latticeFourierProductBasisFun, latticeFourierProductNormSq]

private lemma asymHeatKernel_entry_eq_eigenvalue_average
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a : ℝ) (ha : a ≠ 0) (t : ℝ)
    (x y : AsymLatticeSites Nt Ns) :
    asymHeatKernelMatrix Nt Ns a t x y =
      ∑ m : AsymCanonicalMode Nt Ns,
        Real.exp (-t * (latticeEigenvalue1d Nt a m.1 + latticeEigenvalue1d Ns a m.2)) *
          asymCanonicalBasis Nt Ns m x *
          asymCanonicalBasis Nt Ns m y /
          asymCanonicalNormSq Nt Ns m := by
  unfold asymHeatKernelMatrix
  rw [oneDim_heatKernel_entry_eq_sum Nt a ha t x.1 y.1,
    oneDim_heatKernel_entry_eq_sum Ns a ha t x.2 y.2]
  rw [Finset.sum_mul_sum]
  rw [← Fintype.sum_prod_type']
  refine Finset.sum_congr rfl ?_
  intro m hm
  rcases m with ⟨m₁, m₂⟩
  rw [show Real.exp (-t * (latticeEigenvalue1d Nt a m₁ + latticeEigenvalue1d Ns a m₂)) =
      Real.exp (-t * latticeEigenvalue1d Nt a m₁) *
        Real.exp (-t * latticeEigenvalue1d Ns a m₂) by
        rw [show -t * (latticeEigenvalue1d Nt a m₁ + latticeEigenvalue1d Ns a m₂) =
            -t * latticeEigenvalue1d Nt a m₁ + -t * latticeEigenvalue1d Ns a m₂ by ring,
          Real.exp_add]]
  simp [asymCanonicalBasis, asymCanonicalNormSq, div_eq_mul_inv]
  ring

private lemma asymHeatKernel_diagonal_eq_average
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a : ℝ) (ha : 0 < a) (t : ℝ) (x : AsymLatticeSites Nt Ns) :
    asymHeatKernelMatrix Nt Ns a t x x =
      (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) *
        ((∑ m₁ : Fin Nt, Real.exp (-t * latticeEigenvalue1d Nt a m₁)) *
          ∑ m₂ : Fin Ns, Real.exp (-t * latticeEigenvalue1d Ns a m₂)) := by
  unfold asymHeatKernelMatrix
  have ht :=
    heatKernel_diagonal_mass_weighted_eq_eigenvalue_average
      (d := 1) (N := Nt) (a := a) ha (mass := 0) (t := t) (fin1Site x.1)
  have hs :=
    heatKernel_diagonal_mass_weighted_eq_eigenvalue_average
      (d := 1) (N := Ns) (a := a) ha (mass := 0) (t := t) (fin1Site x.2)
  have ht' : latticeHeatKernelMatrix 1 Nt a t (fin1Site x.1) (fin1Site x.1) =
      (1 / Fintype.card (FinLatticeSites 1 Nt) : ℝ) *
        ∑ m, Real.exp (-t * canonicalEigenvalue 1 Nt a 0 m) := by
    simpa using ht
  have hs' : latticeHeatKernelMatrix 1 Ns a t (fin1Site x.2) (fin1Site x.2) =
      (1 / Fintype.card (FinLatticeSites 1 Ns) : ℝ) *
        ∑ m, Real.exp (-t * canonicalEigenvalue 1 Ns a 0 m) := by
    simpa using hs
  rw [ht', hs']
  have hsum_t :
      ∑ m : Fin 1 → Fin Nt, Real.exp (-t * canonicalEigenvalue 1 Nt a 0 m) =
        ∑ m : Fin Nt, Real.exp (-t * latticeEigenvalue1d Nt a m) := by
    rw [sum_fun_fin1_eq_sum Nt]
    refine Finset.sum_congr rfl ?_
    intro m hm
    simp [canonicalEigenvalue]
  have hsum_s :
      ∑ m : Fin 1 → Fin Ns, Real.exp (-t * canonicalEigenvalue 1 Ns a 0 m) =
        ∑ m : Fin Ns, Real.exp (-t * latticeEigenvalue1d Ns a m) := by
    rw [sum_fun_fin1_eq_sum Ns]
    refine Finset.sum_congr rfl ?_
    intro m hm
    simp [canonicalEigenvalue]
  rw [hsum_t, hsum_s]
  simp [AsymLatticeSites]
  ring

private lemma asymCanonicalSmoothWeight_eq_integral_Ioi
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (_ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (m : AsymCanonicalMode Nt Ns) :
    asymCanonicalSmoothWeight Nt Ns a mass T m =
      ∫ t in Set.Ioi T,
        Real.exp (-t * asymCanonicalEigenvalue Nt Ns a mass m) := by
  unfold asymCanonicalSmoothWeight
  rw [schwinger_smooth_Ioi (asymCanonicalEigenvalue Nt Ns a mass m)
    (asymCanonicalEigenvalue_pos Nt Ns a mass (by positivity) hmass m) T]

private lemma asymCanonicalSmoothWeight_family_sum_eq_average
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (x : AsymLatticeSites Nt Ns) :
    ∑ m : AsymCanonicalMode Nt Ns,
      asymCanonicalSmoothWeight Nt Ns a mass T m *
        asymCanonicalBasis Nt Ns m x *
        asymCanonicalBasis Nt Ns m x /
        asymCanonicalNormSq Nt Ns m =
      (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) *
        ∑ m : AsymCanonicalMode Nt Ns, asymCanonicalSmoothWeight Nt Ns a mass T m := by
  let c : AsymCanonicalMode Nt Ns → ℝ := fun m =>
    asymCanonicalBasis Nt Ns m x * asymCanonicalBasis Nt Ns m x /
      asymCanonicalNormSq Nt Ns m
  have h_int_base :
      ∀ m : AsymCanonicalMode Nt Ns,
        IntegrableOn
          (fun t : ℝ => Real.exp (-t * asymCanonicalEigenvalue Nt Ns a mass m))
          (Set.Ioi T) := by
    intro m
    have hLam := asymCanonicalEigenvalue_pos Nt Ns a mass ha hmass m
    have h := integrableOn_exp_mul_Ioi (a := (-(asymCanonicalEigenvalue Nt Ns a mass m) : ℝ))
      (by linarith) T
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have h_int_coeff :
      ∀ m : AsymCanonicalMode Nt Ns,
        IntegrableOn
          (fun t : ℝ =>
            Real.exp (-t * asymCanonicalEigenvalue Nt Ns a mass m) * c m)
          (Set.Ioi T) := by
    intro m
    simpa [c, mul_assoc, mul_left_comm, mul_comm] using
      (h_int_base m).mul_const (c m)
  have hstart :
      ∑ m : AsymCanonicalMode Nt Ns,
        asymCanonicalSmoothWeight Nt Ns a mass T m *
          asymCanonicalBasis Nt Ns m x *
          asymCanonicalBasis Nt Ns m x /
          asymCanonicalNormSq Nt Ns m =
      ∑ m : AsymCanonicalMode Nt Ns, asymCanonicalSmoothWeight Nt Ns a mass T m * c m := by
    refine Finset.sum_congr rfl ?_
    intro m hm
    simp [c]
    ring
  rw [hstart]
  calc
    ∑ m : AsymCanonicalMode Nt Ns, asymCanonicalSmoothWeight Nt Ns a mass T m * c m
      = ∑ m : AsymCanonicalMode Nt Ns,
          ∫ t in Set.Ioi T,
            Real.exp (-t * asymCanonicalEigenvalue Nt Ns a mass m) * c m := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              calc
                asymCanonicalSmoothWeight Nt Ns a mass T m * c m
                  = c m * asymCanonicalSmoothWeight Nt Ns a mass T m := by ring
                _ = c m *
                    ∫ t in Set.Ioi T,
                      Real.exp (-t * asymCanonicalEigenvalue Nt Ns a mass m) := by
                        rw [asymCanonicalSmoothWeight_eq_integral_Ioi
                          Nt Ns a mass ha hmass T m]
                _ = ∫ t in Set.Ioi T,
                    c m * Real.exp (-t * asymCanonicalEigenvalue Nt Ns a mass m) := by
                        rw [integral_const_mul]
                _ = ∫ t in Set.Ioi T,
                    Real.exp (-t * asymCanonicalEigenvalue Nt Ns a mass m) * c m := by
                        apply integral_congr_ae
                        filter_upwards with t
                        ring
    _ = ∫ t in Set.Ioi T,
          ∑ m : AsymCanonicalMode Nt Ns,
            Real.exp (-t * asymCanonicalEigenvalue Nt Ns a mass m) * c m := by
              rw [integral_finset_sum]
              intro m hm
              exact h_int_coeff m
    _ = ∫ t in Set.Ioi T,
          Real.exp (-t * mass ^ 2) *
            ∑ m : AsymCanonicalMode Nt Ns,
              Real.exp (-t * (latticeEigenvalue1d Nt a m.1 + latticeEigenvalue1d Ns a m.2)) *
                c m := by
              apply integral_congr_ae
              filter_upwards with t
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro m hm
              rw [show -t * asymCanonicalEigenvalue Nt Ns a mass m =
                  -t * mass ^ 2 +
                    (-t * (latticeEigenvalue1d Nt a m.1 + latticeEigenvalue1d Ns a m.2)) by
                    simp [asymCanonicalEigenvalue]; ring,
                Real.exp_add]
              ring
    _ = ∫ t in Set.Ioi T,
          Real.exp (-t * mass ^ 2) * asymHeatKernelMatrix Nt Ns a t x x := by
              apply integral_congr_ae
              filter_upwards with t
              calc
                Real.exp (-t * mass ^ 2) *
                    ∑ m : AsymCanonicalMode Nt Ns,
                      Real.exp (-t * (latticeEigenvalue1d Nt a m.1 +
                        latticeEigenvalue1d Ns a m.2)) * c m
                  = Real.exp (-t * mass ^ 2) *
                      ∑ m : AsymCanonicalMode Nt Ns,
                        Real.exp (-t * (latticeEigenvalue1d Nt a m.1 +
                          latticeEigenvalue1d Ns a m.2)) *
                          (asymCanonicalBasis Nt Ns m x *
                            asymCanonicalBasis Nt Ns m x /
                            asymCanonicalNormSq Nt Ns m) := by
                              simp [c]
                _ = Real.exp (-t * mass ^ 2) * asymHeatKernelMatrix Nt Ns a t x x := by
                      congr 1
                      calc
                        ∑ m : AsymCanonicalMode Nt Ns,
                            Real.exp (-t * (latticeEigenvalue1d Nt a m.1 +
                              latticeEigenvalue1d Ns a m.2)) *
                              (asymCanonicalBasis Nt Ns m x *
                                asymCanonicalBasis Nt Ns m x /
                                asymCanonicalNormSq Nt Ns m)
                          =
                            ∑ m : AsymCanonicalMode Nt Ns,
                              Real.exp (-t * (latticeEigenvalue1d Nt a m.1 +
                                latticeEigenvalue1d Ns a m.2)) *
                                asymCanonicalBasis Nt Ns m x *
                                asymCanonicalBasis Nt Ns m x /
                                asymCanonicalNormSq Nt Ns m := by
                                  refine Finset.sum_congr rfl ?_
                                  intro m hm
                                  ring
                        _ = asymHeatKernelMatrix Nt Ns a t x x := by
                              exact (asymHeatKernel_entry_eq_eigenvalue_average
                                Nt Ns a (ne_of_gt ha) t x x).symm
    _ = ∫ t in Set.Ioi T,
          (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) *
            ∑ m : AsymCanonicalMode Nt Ns,
              Real.exp (-t * asymCanonicalEigenvalue Nt Ns a mass m) := by
              apply integral_congr_ae
              filter_upwards with t
              rw [asymHeatKernel_diagonal_eq_average Nt Ns a ha t x]
              rw [show Real.exp (-t * mass ^ 2) *
                  ((1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) *
                    ((∑ m₁ : Fin Nt, Real.exp (-t * latticeEigenvalue1d Nt a m₁)) *
                      ∑ m₂ : Fin Ns, Real.exp (-t * latticeEigenvalue1d Ns a m₂))) =
                  (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) *
                    (Real.exp (-t * mass ^ 2) *
                      ((∑ m₁ : Fin Nt, Real.exp (-t * latticeEigenvalue1d Nt a m₁)) *
                        ∑ m₂ : Fin Ns, Real.exp (-t * latticeEigenvalue1d Ns a m₂))) by ring]
              have htrace :
                  Real.exp (-t * mass ^ 2) *
                      ((∑ m₁ : Fin Nt, Real.exp (-t * latticeEigenvalue1d Nt a m₁)) *
                        ∑ m₂ : Fin Ns, Real.exp (-t * latticeEigenvalue1d Ns a m₂)) =
                    ∑ m : AsymCanonicalMode Nt Ns,
                      Real.exp (-t * asymCanonicalEigenvalue Nt Ns a mass m) := by
                calc
                  Real.exp (-t * mass ^ 2) *
                      ((∑ m₁ : Fin Nt, Real.exp (-t * latticeEigenvalue1d Nt a m₁)) *
                        ∑ m₂ : Fin Ns, Real.exp (-t * latticeEigenvalue1d Ns a m₂))
                    = (Real.exp (-t * mass ^ 2) *
                        ∑ m₁ : Fin Nt, Real.exp (-t * latticeEigenvalue1d Nt a m₁)) *
                        ∑ m₂ : Fin Ns, Real.exp (-t * latticeEigenvalue1d Ns a m₂) := by
                          ring
                  _ = ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
                        Real.exp (-t * asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂)) := by
                          exact (asym_heat_kernel_trace_factorization Nt Ns a mass t).symm
                  _ = ∑ m : AsymCanonicalMode Nt Ns,
                        Real.exp (-t * asymCanonicalEigenvalue Nt Ns a mass m) := by
                        exact (Fintype.sum_prod_type'
                          (f := fun m₁ : Fin Nt => fun m₂ : Fin Ns =>
                            Real.exp (-t * asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂)))).symm
              exact congrArg ((1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) * ·) htrace
    _ = (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) *
          ∫ t in Set.Ioi T,
            ∑ m : AsymCanonicalMode Nt Ns,
              Real.exp (-t * asymCanonicalEigenvalue Nt Ns a mass m) := by
                rw [integral_const_mul]
    _ = (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) *
          ∑ m : AsymCanonicalMode Nt Ns,
            ∫ t in Set.Ioi T,
              Real.exp (-t * asymCanonicalEigenvalue Nt Ns a mass m) := by
                congr 1
                rw [integral_finset_sum]
                intro m hm
                exact h_int_base m
    _ = (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) *
          ∑ m : AsymCanonicalMode Nt Ns, asymCanonicalSmoothWeight Nt Ns a mass T m := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro m hm
            rw [asymCanonicalSmoothWeight_eq_integral_Ioi Nt Ns a mass ha hmass T m]

private theorem asymCanonicalFullCovariance_diag_eq_wickConstantAsym
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T) (x : AsymLatticeSites Nt Ns) :
    (a ^ 2 : ℝ)⁻¹ *
      ∑ m : AsymCanonicalMode Nt Ns,
        asymCanonicalBasis Nt Ns m x *
          asymCanonicalBasis Nt Ns m x /
          (asymCanonicalEigenvalue Nt Ns a mass m * asymCanonicalNormSq Nt Ns m) =
      wickConstantAsym Nt Ns a mass := by
  have hsum :=
    asymCanonicalSumFieldFunction_covariance Nt Ns a mass ha hmass T hT x x
  have hgj :
      ∫ η : AsymCanonicalJoint Nt Ns,
          asymCanonicalSumFieldFunction Nt Ns a mass T η x *
            asymCanonicalSumFieldFunction Nt Ns a mass T η x
        ∂(asymCanonicalJointMeasure Nt Ns) =
      GaussianField.covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass)
        (asymLatticeDelta Nt Ns x) (asymLatticeDelta Nt Ns x) := by
    simpa [asymLatticeDelta] using
      asymCanonicalSumFieldFunction_covariance_eq_GJ Nt Ns a mass ha hmass T hT x x
  have hwick :
      GaussianField.covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass)
          (asymLatticeDelta Nt Ns x) (asymLatticeDelta Nt Ns x) =
        wickConstantAsym Nt Ns a mass := by
    simpa [GaussianField.covariance] using
      (wickConstantAsym_eq_variance Nt Ns a mass ha hmass x).symm
  exact hsum.symm.trans (hgj.trans hwick)

private theorem asymCanonicalSmoothCovariance_diag_eq_asymSmoothWickConstant
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (x : AsymLatticeSites Nt Ns) :
    asymCanonicalSmoothCovariance Nt Ns a mass T x x =
      asymSmoothWickConstant Nt Ns a mass T := by
  unfold asymCanonicalSmoothCovariance asymSmoothWickConstant
  rw [asymCanonicalSmoothWeight_family_sum_eq_average Nt Ns a mass ha hmass T x]
  congr 1
  congr 1
  exact Fintype.sum_prod_type'
    (f := fun m₁ : Fin Nt => fun m₂ : Fin Ns =>
      asymCanonicalSmoothWeight Nt Ns a mass T (m₁, m₂))

/-- The smooth gamma coefficients have total variance `asymSmoothWickConstant`. -/
theorem asymCanonicalSmoothGamma_sq_sum_eq_asymSmoothWickConstant
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (x : AsymLatticeSites Nt Ns) :
    ∑ m : AsymCanonicalMode Nt Ns, (asymCanonicalSmoothGamma Nt Ns a mass T x m) ^ 2 =
      asymSmoothWickConstant Nt Ns a mass T := by
  have ha_sq_pos : (0 : ℝ) < a ^ 2 := pow_pos ha 2
  calc
    ∑ m : AsymCanonicalMode Nt Ns, (asymCanonicalSmoothGamma Nt Ns a mass T x m) ^ 2
      = ∑ m : AsymCanonicalMode Nt Ns,
          (a ^ 2 : ℝ)⁻¹ *
            (asymCanonicalSmoothWeight Nt Ns a mass T m *
              asymCanonicalBasis Nt Ns m x *
              asymCanonicalBasis Nt Ns m x /
              asymCanonicalNormSq Nt Ns m) := by
                refine Finset.sum_congr rfl ?_
                intro m hm
                have hC :
                    0 ≤ asymCanonicalSmoothWeight Nt Ns a mass T m /
                      asymCanonicalNormSq Nt Ns m := by
                  apply div_nonneg
                  · exact asymCanonicalSmoothWeight_nonneg Nt Ns a mass ha hmass T m
                  · exact (mul_nonneg
                      (le_of_lt (latticeFourierNormSq_pos Nt m.1 m.1.isLt))
                      (le_of_lt (latticeFourierNormSq_pos Ns m.2 m.2.isLt)))
                have hSq :
                    Real.sqrt
                        (asymCanonicalSmoothWeight Nt Ns a mass T m /
                          asymCanonicalNormSq Nt Ns m) *
                      Real.sqrt
                        (asymCanonicalSmoothWeight Nt Ns a mass T m /
                          asymCanonicalNormSq Nt Ns m) =
                    asymCanonicalSmoothWeight Nt Ns a mass T m /
                      asymCanonicalNormSq Nt Ns m :=
                  Real.mul_self_sqrt hC
                unfold asymCanonicalSmoothGamma asymCanonicalSmoothModeCoeff
                rw [sq]
                calc
                  ((Real.sqrt (a ^ 2))⁻¹ *
                      (Real.sqrt
                          (asymCanonicalSmoothWeight Nt Ns a mass T m /
                            asymCanonicalNormSq Nt Ns m) *
                        asymCanonicalBasis Nt Ns m x)) *
                      ((Real.sqrt (a ^ 2))⁻¹ *
                        (Real.sqrt
                            (asymCanonicalSmoothWeight Nt Ns a mass T m /
                              asymCanonicalNormSq Nt Ns m) *
                          asymCanonicalBasis Nt Ns m x))
                      =
                    ((Real.sqrt (a ^ 2))⁻¹ * (Real.sqrt (a ^ 2))⁻¹) *
                      (Real.sqrt
                          (asymCanonicalSmoothWeight Nt Ns a mass T m /
                            asymCanonicalNormSq Nt Ns m) *
                        Real.sqrt
                          (asymCanonicalSmoothWeight Nt Ns a mass T m /
                            asymCanonicalNormSq Nt Ns m)) *
                      (asymCanonicalBasis Nt Ns m x *
                        asymCanonicalBasis Nt Ns m x) := by
                          ring
                  _ = (a ^ 2 : ℝ)⁻¹ *
                      (asymCanonicalSmoothWeight Nt Ns a mass T m /
                        asymCanonicalNormSq Nt Ns m) *
                      (asymCanonicalBasis Nt Ns m x *
                        asymCanonicalBasis Nt Ns m x) := by
                        rw [← mul_inv, ← Real.sqrt_mul (le_of_lt ha_sq_pos),
                          Real.sqrt_mul_self (le_of_lt ha_sq_pos), hSq]
                  _ = (a ^ 2 : ℝ)⁻¹ *
                      (asymCanonicalSmoothWeight Nt Ns a mass T m *
                        asymCanonicalBasis Nt Ns m x *
                        asymCanonicalBasis Nt Ns m x /
                        asymCanonicalNormSq Nt Ns m) := by
                          ring
    _ = (a ^ 2 : ℝ)⁻¹ *
        ∑ m : AsymCanonicalMode Nt Ns,
          asymCanonicalSmoothWeight Nt Ns a mass T m *
            asymCanonicalBasis Nt Ns m x *
            asymCanonicalBasis Nt Ns m x /
            asymCanonicalNormSq Nt Ns m := by
              rw [← Finset.mul_sum]
    _ = asymSmoothWickConstant Nt Ns a mass T := by
        exact asymCanonicalSmoothCovariance_diag_eq_asymSmoothWickConstant
          Nt Ns a mass ha hmass T x

/-! ## §3 Cross-pair identities `Σ_m γ_x(m)γ_y(m) = C(x,y)` -/

/-- The smooth covariance is the dot product of the smooth gamma coefficients. -/
theorem asymCanonicalSmoothCovariance_eq_sum_gamma_mul_gamma
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (x y : AsymLatticeSites Nt Ns) :
    asymCanonicalSmoothCovariance Nt Ns a mass T x y =
      ∑ m : AsymCanonicalMode Nt Ns,
        asymCanonicalSmoothGamma Nt Ns a mass T x m *
          asymCanonicalSmoothGamma Nt Ns a mass T y m := by
  have ha_sq_pos : (0 : ℝ) < a ^ 2 := pow_pos ha 2
  calc
    asymCanonicalSmoothCovariance Nt Ns a mass T x y
      = ∑ m : AsymCanonicalMode Nt Ns,
          (a ^ 2 : ℝ)⁻¹ *
            (asymCanonicalSmoothWeight Nt Ns a mass T m *
              asymCanonicalBasis Nt Ns m x *
              asymCanonicalBasis Nt Ns m y /
              asymCanonicalNormSq Nt Ns m) := by
              unfold asymCanonicalSmoothCovariance
              rw [← Finset.mul_sum]
    _ = ∑ m : AsymCanonicalMode Nt Ns,
          asymCanonicalSmoothGamma Nt Ns a mass T x m *
            asymCanonicalSmoothGamma Nt Ns a mass T y m := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              have hC :
                  0 ≤ asymCanonicalSmoothWeight Nt Ns a mass T m /
                    asymCanonicalNormSq Nt Ns m := by
                apply div_nonneg
                · exact asymCanonicalSmoothWeight_nonneg Nt Ns a mass ha hmass T m
                · exact (mul_nonneg
                    (le_of_lt (latticeFourierNormSq_pos Nt m.1 m.1.isLt))
                    (le_of_lt (latticeFourierNormSq_pos Ns m.2 m.2.isLt)))
              have hSq :
                  Real.sqrt
                      (asymCanonicalSmoothWeight Nt Ns a mass T m /
                        asymCanonicalNormSq Nt Ns m) *
                    Real.sqrt
                      (asymCanonicalSmoothWeight Nt Ns a mass T m /
                        asymCanonicalNormSq Nt Ns m) =
                  asymCanonicalSmoothWeight Nt Ns a mass T m /
                    asymCanonicalNormSq Nt Ns m :=
                Real.mul_self_sqrt hC
              unfold asymCanonicalSmoothGamma asymCanonicalSmoothModeCoeff
              symm
              calc
                ((Real.sqrt (a ^ 2))⁻¹ *
                    (Real.sqrt
                        (asymCanonicalSmoothWeight Nt Ns a mass T m /
                          asymCanonicalNormSq Nt Ns m) *
                      asymCanonicalBasis Nt Ns m x)) *
                    ((Real.sqrt (a ^ 2))⁻¹ *
                      (Real.sqrt
                          (asymCanonicalSmoothWeight Nt Ns a mass T m /
                            asymCanonicalNormSq Nt Ns m) *
                        asymCanonicalBasis Nt Ns m y))
                    =
                  ((Real.sqrt (a ^ 2))⁻¹ * (Real.sqrt (a ^ 2))⁻¹) *
                    (Real.sqrt
                        (asymCanonicalSmoothWeight Nt Ns a mass T m /
                          asymCanonicalNormSq Nt Ns m) *
                      Real.sqrt
                        (asymCanonicalSmoothWeight Nt Ns a mass T m /
                          asymCanonicalNormSq Nt Ns m)) *
                    (asymCanonicalBasis Nt Ns m x *
                      asymCanonicalBasis Nt Ns m y) := by
                        ring
                _ = (a ^ 2 : ℝ)⁻¹ *
                    (asymCanonicalSmoothWeight Nt Ns a mass T m /
                      asymCanonicalNormSq Nt Ns m) *
                    (asymCanonicalBasis Nt Ns m x *
                      asymCanonicalBasis Nt Ns m y) := by
                        rw [← mul_inv, ← Real.sqrt_mul (le_of_lt ha_sq_pos),
                          Real.sqrt_mul_self (le_of_lt ha_sq_pos), hSq]
                _ = (a ^ 2 : ℝ)⁻¹ *
                    (asymCanonicalSmoothWeight Nt Ns a mass T m *
                      asymCanonicalBasis Nt Ns m x *
                      asymCanonicalBasis Nt Ns m y /
                      asymCanonicalNormSq Nt Ns m) := by
                        ring

/-- The rough covariance is the dot product of the rough gamma coefficients. -/
theorem asymCanonicalRoughCovariance_eq_sum_gamma_mul_gamma
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T) (x y : AsymLatticeSites Nt Ns) :
    asymCanonicalRoughCovariance Nt Ns a mass T x y =
      ∑ m : AsymCanonicalMode Nt Ns,
        asymCanonicalRoughGamma Nt Ns a mass T x m *
          asymCanonicalRoughGamma Nt Ns a mass T y m := by
  have ha_sq_pos : (0 : ℝ) < a ^ 2 := pow_pos ha 2
  calc
    asymCanonicalRoughCovariance Nt Ns a mass T x y
      = ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
          (a ^ 2 : ℝ)⁻¹ *
            (asymCanonicalRoughWeight Nt Ns a mass T (m₁, m₂) *
              asymCanonicalBasis Nt Ns (m₁, m₂) x *
              asymCanonicalBasis Nt Ns (m₁, m₂) y /
              asymCanonicalNormSq Nt Ns (m₁, m₂)) := by
              unfold asymCanonicalRoughCovariance
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro m₁ hm₁
              rw [Finset.mul_sum]
    _ = ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
          asymCanonicalRoughGamma Nt Ns a mass T x (m₁, m₂) *
            asymCanonicalRoughGamma Nt Ns a mass T y (m₁, m₂) := by
              refine Finset.sum_congr rfl ?_
              intro m₁ hm₁
              refine Finset.sum_congr rfl ?_
              intro m₂ hm₂
              have hC :
                  0 ≤ asymCanonicalRoughWeight Nt Ns a mass T (m₁, m₂) /
                    asymCanonicalNormSq Nt Ns (m₁, m₂) := by
                apply div_nonneg
                · exact asymCanonicalRoughWeight_nonneg Nt Ns a mass ha hmass T hT (m₁, m₂)
                · exact (mul_nonneg
                    (le_of_lt (latticeFourierNormSq_pos Nt m₁ m₁.isLt))
                    (le_of_lt (latticeFourierNormSq_pos Ns m₂ m₂.isLt)))
              have hSq :
                  Real.sqrt
                      (asymCanonicalRoughWeight Nt Ns a mass T (m₁, m₂) /
                        asymCanonicalNormSq Nt Ns (m₁, m₂)) *
                    Real.sqrt
                      (asymCanonicalRoughWeight Nt Ns a mass T (m₁, m₂) /
                        asymCanonicalNormSq Nt Ns (m₁, m₂)) =
                  asymCanonicalRoughWeight Nt Ns a mass T (m₁, m₂) /
                    asymCanonicalNormSq Nt Ns (m₁, m₂) :=
                Real.mul_self_sqrt hC
              unfold asymCanonicalRoughGamma asymCanonicalRoughModeCoeff
              symm
              calc
                ((Real.sqrt (a ^ 2))⁻¹ *
                    (Real.sqrt
                        (asymCanonicalRoughWeight Nt Ns a mass T (m₁, m₂) /
                          asymCanonicalNormSq Nt Ns (m₁, m₂)) *
                      asymCanonicalBasis Nt Ns (m₁, m₂) x)) *
                    ((Real.sqrt (a ^ 2))⁻¹ *
                      (Real.sqrt
                          (asymCanonicalRoughWeight Nt Ns a mass T (m₁, m₂) /
                            asymCanonicalNormSq Nt Ns (m₁, m₂)) *
                        asymCanonicalBasis Nt Ns (m₁, m₂) y))
                    =
                  ((Real.sqrt (a ^ 2))⁻¹ * (Real.sqrt (a ^ 2))⁻¹) *
                    (Real.sqrt
                        (asymCanonicalRoughWeight Nt Ns a mass T (m₁, m₂) /
                          asymCanonicalNormSq Nt Ns (m₁, m₂)) *
                      Real.sqrt
                        (asymCanonicalRoughWeight Nt Ns a mass T (m₁, m₂) /
                          asymCanonicalNormSq Nt Ns (m₁, m₂))) *
                    (asymCanonicalBasis Nt Ns (m₁, m₂) x *
                      asymCanonicalBasis Nt Ns (m₁, m₂) y) := by
                        ring
                _ = (a ^ 2 : ℝ)⁻¹ *
                    (asymCanonicalRoughWeight Nt Ns a mass T (m₁, m₂) /
                      asymCanonicalNormSq Nt Ns (m₁, m₂)) *
                    (asymCanonicalBasis Nt Ns (m₁, m₂) x *
                      asymCanonicalBasis Nt Ns (m₁, m₂) y) := by
                        rw [← mul_inv, ← Real.sqrt_mul (le_of_lt ha_sq_pos),
                          Real.sqrt_mul_self (le_of_lt ha_sq_pos), hSq]
                _ = (a ^ 2 : ℝ)⁻¹ *
                    (asymCanonicalRoughWeight Nt Ns a mass T (m₁, m₂) *
                      asymCanonicalBasis Nt Ns (m₁, m₂) x *
                      asymCanonicalBasis Nt Ns (m₁, m₂) y /
                      asymCanonicalNormSq Nt Ns (m₁, m₂)) := by
                        ring
    _ = ∑ m : AsymCanonicalMode Nt Ns,
          asymCanonicalRoughGamma Nt Ns a mass T x m *
            asymCanonicalRoughGamma Nt Ns a mass T y m := by
              simpa using
                (Fintype.sum_prod_type'
                  (f := fun m₁ m₂ =>
                    asymCanonicalRoughGamma Nt Ns a mass T x (m₁, m₂) *
                      asymCanonicalRoughGamma Nt Ns a mass T y (m₁, m₂))).symm

private theorem asymCanonicalRoughCovariance_diag_eq_asymCanonicalRoughWickConstant
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T) (x : AsymLatticeSites Nt Ns) :
    asymCanonicalRoughCovariance Nt Ns a mass T x x =
      asymCanonicalRoughWickConstant Nt Ns a mass T := by
  have hfull := asymCanonicalFullCovariance_diag_eq_wickConstantAsym
    Nt Ns a mass ha hmass T hT x
  have hsmooth := asymCanonicalSmoothCovariance_diag_eq_asymSmoothWickConstant
    Nt Ns a mass ha hmass T x
  have hsplit :
      asymCanonicalSmoothCovariance Nt Ns a mass T x x +
        asymCanonicalRoughCovariance Nt Ns a mass T x x =
      wickConstantAsym Nt Ns a mass := by
    unfold asymCanonicalSmoothCovariance asymCanonicalRoughCovariance
    calc
      (a ^ 2 : ℝ)⁻¹ *
          ∑ m : AsymCanonicalMode Nt Ns,
            asymCanonicalSmoothWeight Nt Ns a mass T m *
              asymCanonicalBasis Nt Ns m x *
              asymCanonicalBasis Nt Ns m x /
              asymCanonicalNormSq Nt Ns m +
        (a ^ 2 : ℝ)⁻¹ *
          ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
            asymCanonicalRoughWeight Nt Ns a mass T (m₁, m₂) *
              asymCanonicalBasis Nt Ns (m₁, m₂) x *
              asymCanonicalBasis Nt Ns (m₁, m₂) x /
              asymCanonicalNormSq Nt Ns (m₁, m₂)
        =
        (a ^ 2 : ℝ)⁻¹ *
          (∑ m : AsymCanonicalMode Nt Ns,
            asymCanonicalSmoothWeight Nt Ns a mass T m *
              asymCanonicalBasis Nt Ns m x *
              asymCanonicalBasis Nt Ns m x /
              asymCanonicalNormSq Nt Ns m
          + ∑ m : AsymCanonicalMode Nt Ns,
              asymCanonicalRoughWeight Nt Ns a mass T m *
                asymCanonicalBasis Nt Ns m x *
                asymCanonicalBasis Nt Ns m x /
                asymCanonicalNormSq Nt Ns m) := by
          rw [show ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
              asymCanonicalRoughWeight Nt Ns a mass T (m₁, m₂) *
                asymCanonicalBasis Nt Ns (m₁, m₂) x *
                asymCanonicalBasis Nt Ns (m₁, m₂) x /
                asymCanonicalNormSq Nt Ns (m₁, m₂)
              =
              ∑ m : AsymCanonicalMode Nt Ns,
                asymCanonicalRoughWeight Nt Ns a mass T m *
                  asymCanonicalBasis Nt Ns m x *
                  asymCanonicalBasis Nt Ns m x /
                  asymCanonicalNormSq Nt Ns m by
              exact (Fintype.sum_prod_type'
                (f := fun m₁ : Fin Nt => fun m₂ : Fin Ns =>
                  asymCanonicalRoughWeight Nt Ns a mass T (m₁, m₂) *
                    asymCanonicalBasis Nt Ns (m₁, m₂) x *
                    asymCanonicalBasis Nt Ns (m₁, m₂) x /
                    asymCanonicalNormSq Nt Ns (m₁, m₂))).symm]
          ring
      _ = (a ^ 2 : ℝ)⁻¹ *
          ∑ m : AsymCanonicalMode Nt Ns,
            (asymCanonicalSmoothWeight Nt Ns a mass T m +
                asymCanonicalRoughWeight Nt Ns a mass T m) *
              (asymCanonicalBasis Nt Ns m x *
                asymCanonicalBasis Nt Ns m x /
                asymCanonicalNormSq Nt Ns m) := by
          congr 1
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro m hm
          ring
      _ = (a ^ 2 : ℝ)⁻¹ *
          ∑ m : AsymCanonicalMode Nt Ns,
            (asymCanonicalEigenvalue Nt Ns a mass m)⁻¹ *
              (asymCanonicalBasis Nt Ns m x *
                asymCanonicalBasis Nt Ns m x /
                asymCanonicalNormSq Nt Ns m) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro m hm
          rw [asymCanonicalSmoothWeight_add_roughWeight]
      _ = (a ^ 2 : ℝ)⁻¹ *
          ∑ m : AsymCanonicalMode Nt Ns,
            asymCanonicalBasis Nt Ns m x *
              asymCanonicalBasis Nt Ns m x /
              (asymCanonicalEigenvalue Nt Ns a mass m *
                asymCanonicalNormSq Nt Ns m) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro m hm
          field_simp
      _ = wickConstantAsym Nt Ns a mass := hfull
  unfold asymCanonicalRoughWickConstant
  linarith

/-- The rough gamma coefficients have total variance `wickConstantAsym - asymSmoothWickConstant`. -/
theorem asymCanonicalRoughGamma_sq_sum_eq_asymCanonicalRoughWickConstant
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T) (x : AsymLatticeSites Nt Ns) :
    ∑ m : AsymCanonicalMode Nt Ns, (asymCanonicalRoughGamma Nt Ns a mass T x m) ^ 2 =
      asymCanonicalRoughWickConstant Nt Ns a mass T := by
  have hdiag :=
    asymCanonicalRoughCovariance_eq_sum_gamma_mul_gamma
      Nt Ns a mass ha hmass T hT x x
  rw [show (∑ m : AsymCanonicalMode Nt Ns,
      asymCanonicalRoughGamma Nt Ns a mass T x m *
        asymCanonicalRoughGamma Nt Ns a mass T x m) =
      ∑ m : AsymCanonicalMode Nt Ns, (asymCanonicalRoughGamma Nt Ns a mass T x m) ^ 2 by
        refine Finset.sum_congr rfl ?_
        intro m hm
        rw [sq]] at hdiag
  exact hdiag.symm.trans
    (asymCanonicalRoughCovariance_diag_eq_asymCanonicalRoughWickConstant
      Nt Ns a mass ha hmass T hT x)

/-! ## §4 Two-site marginal Wick identities -/

/-- Smooth two-site Wick pairing is integrable under the smooth marginal. -/
theorem asymCanonicalSmoothWickPower_two_site_marginal_integrable
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (n m : ℕ) (x y : AsymLatticeSites Nt Ns) :
    Integrable
      (fun ηS : AsymCanonicalMode Nt Ns → ℝ =>
        wickMonomial n (asymSmoothWickConstant Nt Ns a mass T)
          (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS x) *
        wickMonomial m (asymSmoothWickConstant Nt Ns a mass T)
          (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS y))
      (Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) := by
  let γ_x : AsymCanonicalMode Nt Ns → ℝ := asymCanonicalSmoothGamma Nt Ns a mass T x
  let γ_y : AsymCanonicalMode Nt Ns → ℝ := asymCanonicalSmoothGamma Nt Ns a mass T y
  refine (wickPower_two_site_pi_gaussianReal_integrable
      (γ_x := γ_x) (γ_y := γ_y) n m).congr ?_
  filter_upwards with ηS
  calc
    wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ηS j) *
        wickMonomial m (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * ηS j)
      =
        wickMonomial n (asymSmoothWickConstant Nt Ns a mass T)
          (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS x) *
        wickMonomial m (asymSmoothWickConstant Nt Ns a mass T)
          (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS y) := by
            symm
            calc
              wickMonomial n (asymSmoothWickConstant Nt Ns a mass T)
                  (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS x) *
                wickMonomial m (asymSmoothWickConstant Nt Ns a mass T)
                  (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS y)
                =
                  wickMonomial n (∑ j, (γ_x j) ^ 2)
                    (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS x) *
                  wickMonomial m (asymSmoothWickConstant Nt Ns a mass T)
                    (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS y) := by
                      rw [show asymSmoothWickConstant Nt Ns a mass T = ∑ j, (γ_x j) ^ 2 from by
                        simpa [γ_x] using
                          (asymCanonicalSmoothGamma_sq_sum_eq_asymSmoothWickConstant
                            Nt Ns a mass ha hmass T x).symm]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ηS j) *
                  wickMonomial m (asymSmoothWickConstant Nt Ns a mass T)
                    (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS y) := by
                      rw [show asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS x =
                        ∑ j, γ_x j * ηS j from by
                        simpa [γ_x] using
                          asymCanonicalSmoothFieldFunctionOfFst_eq_sum_gamma
                            Nt Ns a mass T ηS x]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ηS j) *
                  wickMonomial m (∑ j, (γ_y j) ^ 2)
                    (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS y) := by
                      rw [show asymSmoothWickConstant Nt Ns a mass T = ∑ j, (γ_y j) ^ 2 from by
                        simpa [γ_y] using
                          (asymCanonicalSmoothGamma_sq_sum_eq_asymSmoothWickConstant
                            Nt Ns a mass ha hmass T y).symm]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ηS j) *
                  wickMonomial m (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * ηS j) := by
                      rw [show asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS y =
                        ∑ j, γ_y j * ηS j from by
                        simpa [γ_y] using
                          asymCanonicalSmoothFieldFunctionOfFst_eq_sum_gamma
                            Nt Ns a mass T ηS y]

/-- Rough two-site Wick pairing is integrable under the rough marginal. -/
theorem asymCanonicalRoughWickPower_two_site_marginal_integrable
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T) (n m : ℕ) (x y : AsymLatticeSites Nt Ns) :
    Integrable
      (fun ηR : AsymCanonicalMode Nt Ns → ℝ =>
        wickMonomial n (asymCanonicalRoughWickConstant Nt Ns a mass T)
          (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR x) *
        wickMonomial m (asymCanonicalRoughWickConstant Nt Ns a mass T)
          (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR y))
      (Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) := by
  let γ_x : AsymCanonicalMode Nt Ns → ℝ := asymCanonicalRoughGamma Nt Ns a mass T x
  let γ_y : AsymCanonicalMode Nt Ns → ℝ := asymCanonicalRoughGamma Nt Ns a mass T y
  refine (wickPower_two_site_pi_gaussianReal_integrable
      (γ_x := γ_x) (γ_y := γ_y) n m).congr ?_
  filter_upwards with ηR
  calc
    wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ηR j) *
        wickMonomial m (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * ηR j)
      =
        wickMonomial n (asymCanonicalRoughWickConstant Nt Ns a mass T)
          (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR x) *
        wickMonomial m (asymCanonicalRoughWickConstant Nt Ns a mass T)
          (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR y) := by
            symm
            calc
              wickMonomial n (asymCanonicalRoughWickConstant Nt Ns a mass T)
                  (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR x) *
                wickMonomial m (asymCanonicalRoughWickConstant Nt Ns a mass T)
                  (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR y)
                =
                  wickMonomial n (∑ j, (γ_x j) ^ 2)
                    (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR x) *
                  wickMonomial m (asymCanonicalRoughWickConstant Nt Ns a mass T)
                    (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR y) := by
                      rw [show asymCanonicalRoughWickConstant Nt Ns a mass T = ∑ j, (γ_x j) ^ 2 from by
                        simpa [γ_x] using
                          (asymCanonicalRoughGamma_sq_sum_eq_asymCanonicalRoughWickConstant
                            Nt Ns a mass ha hmass T hT x).symm]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ηR j) *
                  wickMonomial m (asymCanonicalRoughWickConstant Nt Ns a mass T)
                    (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR y) := by
                      rw [show asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR x =
                        ∑ j, γ_x j * ηR j from by
                        simpa [γ_x] using
                          asymCanonicalRoughFieldFunctionOfSnd_eq_sum_gamma
                            Nt Ns a mass T ηR x]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ηR j) *
                  wickMonomial m (∑ j, (γ_y j) ^ 2)
                    (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR y) := by
                      rw [show asymCanonicalRoughWickConstant Nt Ns a mass T = ∑ j, (γ_y j) ^ 2 from by
                        simpa [γ_y] using
                          (asymCanonicalRoughGamma_sq_sum_eq_asymCanonicalRoughWickConstant
                            Nt Ns a mass ha hmass T hT y).symm]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ηR j) *
                  wickMonomial m (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * ηR j) := by
                      rw [show asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR y =
                        ∑ j, γ_y j * ηR j from by
                        simpa [γ_y] using
                          asymCanonicalRoughFieldFunctionOfSnd_eq_sum_gamma
                            Nt Ns a mass T ηR y]

/-- Smooth two-site Wick pairing is orthogonal across different degrees. -/
theorem asymCanonicalSmoothWickPower_two_site_marginal_eq_zero_of_ne
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (n m : ℕ) (hnm : n ≠ m) (x y : AsymLatticeSites Nt Ns) :
    ∫ ηS : AsymCanonicalMode Nt Ns → ℝ,
      wickMonomial n (asymSmoothWickConstant Nt Ns a mass T)
        (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS x) *
      wickMonomial m (asymSmoothWickConstant Nt Ns a mass T)
        (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS y)
      ∂(Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) = 0 := by
  let γ_x : AsymCanonicalMode Nt Ns → ℝ := asymCanonicalSmoothGamma Nt Ns a mass T x
  let γ_y : AsymCanonicalMode Nt Ns → ℝ := asymCanonicalSmoothGamma Nt Ns a mass T y
  calc
    ∫ ηS : AsymCanonicalMode Nt Ns → ℝ,
        wickMonomial n (asymSmoothWickConstant Nt Ns a mass T)
          (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS x) *
        wickMonomial m (asymSmoothWickConstant Nt Ns a mass T)
          (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS y)
      ∂(Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1))
      =
        ∫ ηS : AsymCanonicalMode Nt Ns → ℝ,
          wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ηS j) *
            wickMonomial m (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * ηS j)
          ∂(Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) := by
            apply integral_congr_ae
            filter_upwards with ηS
            calc
              wickMonomial n (asymSmoothWickConstant Nt Ns a mass T)
                  (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS x) *
                wickMonomial m (asymSmoothWickConstant Nt Ns a mass T)
                  (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS y)
                =
                  wickMonomial n (∑ j, (γ_x j) ^ 2)
                    (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS x) *
                  wickMonomial m (asymSmoothWickConstant Nt Ns a mass T)
                    (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS y) := by
                      rw [show asymSmoothWickConstant Nt Ns a mass T = ∑ j, (γ_x j) ^ 2 from by
                        simpa [γ_x] using
                          (asymCanonicalSmoothGamma_sq_sum_eq_asymSmoothWickConstant
                            Nt Ns a mass ha hmass T x).symm]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ηS j) *
                  wickMonomial m (asymSmoothWickConstant Nt Ns a mass T)
                    (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS y) := by
                      rw [show asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS x =
                        ∑ j, γ_x j * ηS j from by
                        simpa [γ_x] using
                          asymCanonicalSmoothFieldFunctionOfFst_eq_sum_gamma
                            Nt Ns a mass T ηS x]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ηS j) *
                  wickMonomial m (∑ j, (γ_y j) ^ 2)
                    (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS y) := by
                      rw [show asymSmoothWickConstant Nt Ns a mass T = ∑ j, (γ_y j) ^ 2 from by
                        simpa [γ_y] using
                          (asymCanonicalSmoothGamma_sq_sum_eq_asymSmoothWickConstant
                            Nt Ns a mass ha hmass T y).symm]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ηS j) *
                  wickMonomial m (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * ηS j) := by
                      rw [show asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS y =
                        ∑ j, γ_y j * ηS j from by
                        simpa [γ_y] using
                          asymCanonicalSmoothFieldFunctionOfFst_eq_sum_gamma
                            Nt Ns a mass T ηS y]
    _ = 0 :=
      wickPower_two_site_pi_gaussianReal_eq_zero_of_ne
        (γ_x := γ_x) (γ_y := γ_y) hnm

/-- Rough two-site Wick pairing is orthogonal across different degrees. -/
theorem asymCanonicalRoughWickPower_two_site_marginal_eq_zero_of_ne
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T) (n m : ℕ) (hnm : n ≠ m) (x y : AsymLatticeSites Nt Ns) :
    ∫ ηR : AsymCanonicalMode Nt Ns → ℝ,
      wickMonomial n (asymCanonicalRoughWickConstant Nt Ns a mass T)
        (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR x) *
      wickMonomial m (asymCanonicalRoughWickConstant Nt Ns a mass T)
        (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR y)
      ∂(Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) = 0 := by
  let γ_x : AsymCanonicalMode Nt Ns → ℝ := asymCanonicalRoughGamma Nt Ns a mass T x
  let γ_y : AsymCanonicalMode Nt Ns → ℝ := asymCanonicalRoughGamma Nt Ns a mass T y
  calc
    ∫ ηR : AsymCanonicalMode Nt Ns → ℝ,
        wickMonomial n (asymCanonicalRoughWickConstant Nt Ns a mass T)
          (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR x) *
        wickMonomial m (asymCanonicalRoughWickConstant Nt Ns a mass T)
          (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR y)
      ∂(Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1))
      =
        ∫ ηR : AsymCanonicalMode Nt Ns → ℝ,
          wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ηR j) *
            wickMonomial m (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * ηR j)
          ∂(Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) := by
            apply integral_congr_ae
            filter_upwards with ηR
            calc
              wickMonomial n (asymCanonicalRoughWickConstant Nt Ns a mass T)
                  (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR x) *
                wickMonomial m (asymCanonicalRoughWickConstant Nt Ns a mass T)
                  (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR y)
                =
                  wickMonomial n (∑ j, (γ_x j) ^ 2)
                    (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR x) *
                  wickMonomial m (asymCanonicalRoughWickConstant Nt Ns a mass T)
                    (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR y) := by
                      rw [show asymCanonicalRoughWickConstant Nt Ns a mass T = ∑ j, (γ_x j) ^ 2 from by
                        simpa [γ_x] using
                          (asymCanonicalRoughGamma_sq_sum_eq_asymCanonicalRoughWickConstant
                            Nt Ns a mass ha hmass T hT x).symm]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ηR j) *
                  wickMonomial m (asymCanonicalRoughWickConstant Nt Ns a mass T)
                    (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR y) := by
                      rw [show asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR x =
                        ∑ j, γ_x j * ηR j from by
                        simpa [γ_x] using
                          asymCanonicalRoughFieldFunctionOfSnd_eq_sum_gamma
                            Nt Ns a mass T ηR x]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ηR j) *
                  wickMonomial m (∑ j, (γ_y j) ^ 2)
                    (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR y) := by
                      rw [show asymCanonicalRoughWickConstant Nt Ns a mass T = ∑ j, (γ_y j) ^ 2 from by
                        simpa [γ_y] using
                          (asymCanonicalRoughGamma_sq_sum_eq_asymCanonicalRoughWickConstant
                            Nt Ns a mass ha hmass T hT y).symm]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ηR j) *
                  wickMonomial m (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * ηR j) := by
                      rw [show asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR y =
                        ∑ j, γ_y j * ηR j from by
                        simpa [γ_y] using
                          asymCanonicalRoughFieldFunctionOfSnd_eq_sum_gamma
                            Nt Ns a mass T ηR y]
    _ = 0 :=
      wickPower_two_site_pi_gaussianReal_eq_zero_of_ne
        (γ_x := γ_x) (γ_y := γ_y) hnm

/-- Smooth two-site Wick pairing on the diagonal is `n! * C_S(x,y)^n`. -/
theorem asymCanonicalSmoothWickPower_two_site_marginal_eq_diag
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (n : ℕ) (x y : AsymLatticeSites Nt Ns) :
    ∫ ηS : AsymCanonicalMode Nt Ns → ℝ,
      wickMonomial n (asymSmoothWickConstant Nt Ns a mass T)
        (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS x) *
      wickMonomial n (asymSmoothWickConstant Nt Ns a mass T)
        (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS y)
      ∂(Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) =
    (n.factorial : ℝ) * (asymCanonicalSmoothCovariance Nt Ns a mass T x y) ^ n := by
  let γ_x : AsymCanonicalMode Nt Ns → ℝ := asymCanonicalSmoothGamma Nt Ns a mass T x
  let γ_y : AsymCanonicalMode Nt Ns → ℝ := asymCanonicalSmoothGamma Nt Ns a mass T y
  calc
    ∫ ηS : AsymCanonicalMode Nt Ns → ℝ,
        wickMonomial n (asymSmoothWickConstant Nt Ns a mass T)
          (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS x) *
        wickMonomial n (asymSmoothWickConstant Nt Ns a mass T)
          (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS y)
      ∂(Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1))
      =
        ∫ ηS : AsymCanonicalMode Nt Ns → ℝ,
          wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ηS j) *
            wickMonomial n (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * ηS j)
          ∂(Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) := by
            apply integral_congr_ae
            filter_upwards with ηS
            calc
              wickMonomial n (asymSmoothWickConstant Nt Ns a mass T)
                  (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS x) *
                wickMonomial n (asymSmoothWickConstant Nt Ns a mass T)
                  (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS y)
                =
                  wickMonomial n (∑ j, (γ_x j) ^ 2)
                    (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS x) *
                  wickMonomial n (asymSmoothWickConstant Nt Ns a mass T)
                    (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS y) := by
                      rw [show asymSmoothWickConstant Nt Ns a mass T = ∑ j, (γ_x j) ^ 2 from by
                        simpa [γ_x] using
                          (asymCanonicalSmoothGamma_sq_sum_eq_asymSmoothWickConstant
                            Nt Ns a mass ha hmass T x).symm]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ηS j) *
                  wickMonomial n (asymSmoothWickConstant Nt Ns a mass T)
                    (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS y) := by
                      rw [show asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS x =
                        ∑ j, γ_x j * ηS j from by
                        simpa [γ_x] using
                          asymCanonicalSmoothFieldFunctionOfFst_eq_sum_gamma
                            Nt Ns a mass T ηS x]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ηS j) *
                  wickMonomial n (∑ j, (γ_y j) ^ 2)
                    (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS y) := by
                      rw [show asymSmoothWickConstant Nt Ns a mass T = ∑ j, (γ_y j) ^ 2 from by
                        simpa [γ_y] using
                          (asymCanonicalSmoothGamma_sq_sum_eq_asymSmoothWickConstant
                            Nt Ns a mass ha hmass T y).symm]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ηS j) *
                  wickMonomial n (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * ηS j) := by
                      rw [show asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS y =
                        ∑ j, γ_y j * ηS j from by
                        simpa [γ_y] using
                          asymCanonicalSmoothFieldFunctionOfFst_eq_sum_gamma
                            Nt Ns a mass T ηS y]
    _ = (n.factorial : ℝ) * (∑ j, γ_x j * γ_y j) ^ n :=
      wickPower_two_site_pi_gaussianReal_eq_diag (γ_x := γ_x) (γ_y := γ_y) n
    _ = (n.factorial : ℝ) * (asymCanonicalSmoothCovariance Nt Ns a mass T x y) ^ n := by
      congr 2
      symm
      simpa [γ_x, γ_y] using
        asymCanonicalSmoothCovariance_eq_sum_gamma_mul_gamma
          Nt Ns a mass ha hmass T x y

/-- Rough two-site Wick pairing on the diagonal is `n! * C_R(x,y)^n`. -/
theorem asymCanonicalRoughWickPower_two_site_marginal_eq_diag
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T) (n : ℕ) (x y : AsymLatticeSites Nt Ns) :
    ∫ ηR : AsymCanonicalMode Nt Ns → ℝ,
      wickMonomial n (asymCanonicalRoughWickConstant Nt Ns a mass T)
        (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR x) *
      wickMonomial n (asymCanonicalRoughWickConstant Nt Ns a mass T)
        (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR y)
      ∂(Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) =
    (n.factorial : ℝ) * (asymCanonicalRoughCovariance Nt Ns a mass T x y) ^ n := by
  let γ_x : AsymCanonicalMode Nt Ns → ℝ := asymCanonicalRoughGamma Nt Ns a mass T x
  let γ_y : AsymCanonicalMode Nt Ns → ℝ := asymCanonicalRoughGamma Nt Ns a mass T y
  calc
    ∫ ηR : AsymCanonicalMode Nt Ns → ℝ,
        wickMonomial n (asymCanonicalRoughWickConstant Nt Ns a mass T)
          (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR x) *
        wickMonomial n (asymCanonicalRoughWickConstant Nt Ns a mass T)
          (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR y)
      ∂(Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1))
      =
        ∫ ηR : AsymCanonicalMode Nt Ns → ℝ,
          wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ηR j) *
            wickMonomial n (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * ηR j)
          ∂(Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1)) := by
            apply integral_congr_ae
            filter_upwards with ηR
            calc
              wickMonomial n (asymCanonicalRoughWickConstant Nt Ns a mass T)
                  (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR x) *
                wickMonomial n (asymCanonicalRoughWickConstant Nt Ns a mass T)
                  (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR y)
                =
                  wickMonomial n (∑ j, (γ_x j) ^ 2)
                    (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR x) *
                  wickMonomial n (asymCanonicalRoughWickConstant Nt Ns a mass T)
                    (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR y) := by
                      rw [show asymCanonicalRoughWickConstant Nt Ns a mass T = ∑ j, (γ_x j) ^ 2 from by
                        simpa [γ_x] using
                          (asymCanonicalRoughGamma_sq_sum_eq_asymCanonicalRoughWickConstant
                            Nt Ns a mass ha hmass T hT x).symm]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ηR j) *
                  wickMonomial n (asymCanonicalRoughWickConstant Nt Ns a mass T)
                    (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR y) := by
                      rw [show asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR x =
                        ∑ j, γ_x j * ηR j from by
                        simpa [γ_x] using
                          asymCanonicalRoughFieldFunctionOfSnd_eq_sum_gamma
                            Nt Ns a mass T ηR x]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ηR j) *
                  wickMonomial n (∑ j, (γ_y j) ^ 2)
                    (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR y) := by
                      rw [show asymCanonicalRoughWickConstant Nt Ns a mass T = ∑ j, (γ_y j) ^ 2 from by
                        simpa [γ_y] using
                          (asymCanonicalRoughGamma_sq_sum_eq_asymCanonicalRoughWickConstant
                            Nt Ns a mass ha hmass T hT y).symm]
              _ =
                  wickMonomial n (∑ j, (γ_x j) ^ 2) (∑ j, γ_x j * ηR j) *
                  wickMonomial n (∑ j, (γ_y j) ^ 2) (∑ j, γ_y j * ηR j) := by
                      rw [show asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR y =
                        ∑ j, γ_y j * ηR j from by
                        simpa [γ_y] using
                          asymCanonicalRoughFieldFunctionOfSnd_eq_sum_gamma
                            Nt Ns a mass T ηR y]
    _ = (n.factorial : ℝ) * (∑ j, γ_x j * γ_y j) ^ n :=
      wickPower_two_site_pi_gaussianReal_eq_diag (γ_x := γ_x) (γ_y := γ_y) n
    _ = (n.factorial : ℝ) * (asymCanonicalRoughCovariance Nt Ns a mass T x y) ^ n := by
      congr 2
      symm
      simpa [γ_x, γ_y] using
        asymCanonicalRoughCovariance_eq_sum_gamma_mul_gamma
          Nt Ns a mass ha hmass T hT x y

/-! ## §5 Cross-term L² identity -/

/-- The asym cross-term L² norm squares to a smooth/rough covariance double sum. -/
theorem asymCanonicalCrossTerm_l2_sq_eq_covSum
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T) (k j : ℕ) :
    ∫ η, (asymCanonicalCrossTerm Nt Ns a mass T η k j) ^ 2
        ∂(asymCanonicalJointMeasure Nt Ns) =
      ((a ^ 2) * (a ^ 2)) * ((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
        ∑ x : AsymLatticeSites Nt Ns,
          ∑ y : AsymLatticeSites Nt Ns,
            asymCanonicalSmoothCovariance Nt Ns a mass T x y ^ j *
              asymCanonicalRoughCovariance Nt Ns a mass T x y ^ (k - j) := by
  let cS := asymSmoothWickConstant Nt Ns a mass T
  let cR := asymCanonicalRoughWickConstant Nt Ns a mass T
  let μS : Measure (AsymCanonicalMode Nt Ns → ℝ) :=
    Measure.pi (fun _ : AsymCanonicalMode Nt Ns => ProbabilityTheory.gaussianReal 0 1)
  let μR : Measure (AsymCanonicalMode Nt Ns → ℝ) :=
    Measure.pi (fun _ : AsymCanonicalMode Nt Ns => ProbabilityTheory.gaussianReal 0 1)
  let term : AsymLatticeSites Nt Ns → AsymLatticeSites Nt Ns → AsymCanonicalJoint Nt Ns → ℝ :=
    fun x y η =>
      (wickMonomial j cS (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x) *
          wickMonomial j cS (asymCanonicalSmoothFieldFunction Nt Ns a mass T η y)) *
        (wickMonomial (k - j) cR (asymCanonicalRoughFieldFunction Nt Ns a mass T η x) *
          wickMonomial (k - j) cR (asymCanonicalRoughFieldFunction Nt Ns a mass T η y))
  have h_term_int :
      ∀ x y, Integrable (term x y) (asymCanonicalJointMeasure Nt Ns) := by
    intro x y
    rw [asymCanonicalJointMeasure]
    let f : (AsymCanonicalMode Nt Ns → ℝ) → ℝ := fun ηS =>
      wickMonomial j cS (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS x) *
        wickMonomial j cS (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS y)
    let g : (AsymCanonicalMode Nt Ns → ℝ) → ℝ := fun ηR =>
      wickMonomial (k - j) cR (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR x) *
        wickMonomial (k - j) cR (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR y)
    have hf : Integrable f μS := by
      simpa [f, μS, cS] using
        (asymCanonicalSmoothWickPower_two_site_marginal_integrable
          Nt Ns a mass ha hmass T j j x y)
    have hg : Integrable g μR := by
      simpa [g, μR, cR] using
        (asymCanonicalRoughWickPower_two_site_marginal_integrable
          Nt Ns a mass ha hmass T hT (k - j) (k - j) x y)
    simpa [term, AsymCanonicalJoint, f, g, μS, μR, cS, cR,
      mul_assoc, mul_left_comm, mul_comm] using
      (Integrable.mul_prod (μ := μS) (ν := μR) hf hg)
  have h_expand :
      ∀ η : AsymCanonicalJoint Nt Ns,
        (asymCanonicalCrossTerm Nt Ns a mass T η k j) ^ 2 =
          ((a ^ 2) * (a ^ 2)) * ∑ x : AsymLatticeSites Nt Ns,
            ∑ y : AsymLatticeSites Nt Ns, term x y η := by
    intro η
    rw [sq]
    unfold asymCanonicalCrossTerm term
    rw [show
      (a ^ 2 * ∑ x,
          wickMonomial j (asymSmoothWickConstant Nt Ns a mass T)
              (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x) *
            wickMonomial (k - j) (asymCanonicalRoughWickConstant Nt Ns a mass T)
              (asymCanonicalRoughFieldFunction Nt Ns a mass T η x)) *
        (a ^ 2 * ∑ x,
          wickMonomial j (asymSmoothWickConstant Nt Ns a mass T)
              (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x) *
            wickMonomial (k - j) (asymCanonicalRoughWickConstant Nt Ns a mass T)
              (asymCanonicalRoughFieldFunction Nt Ns a mass T η x)) =
      ((a ^ 2) * (a ^ 2)) *
      ((∑ x,
          wickMonomial j (asymSmoothWickConstant Nt Ns a mass T)
              (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x) *
            wickMonomial (k - j) (asymCanonicalRoughWickConstant Nt Ns a mass T)
              (asymCanonicalRoughFieldFunction Nt Ns a mass T η x)) *
        (∑ x,
          wickMonomial j (asymSmoothWickConstant Nt Ns a mass T)
              (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x) *
            wickMonomial (k - j) (asymCanonicalRoughWickConstant Nt Ns a mass T)
              (asymCanonicalRoughFieldFunction Nt Ns a mass T η x))) by
      ring]
    rw [Finset.sum_mul_sum]
    simp [cS, cR, mul_assoc, mul_left_comm]
  simp_rw [h_expand]
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_finset_sum _ (fun x _ =>
    MeasureTheory.integrable_finset_sum _ (fun y _ => h_term_int x y))]
  have hxy :
      ∀ x y,
        ∫ η, term x y η ∂(asymCanonicalJointMeasure Nt Ns) =
          ((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
            (asymCanonicalSmoothCovariance Nt Ns a mass T x y ^ j *
              asymCanonicalRoughCovariance Nt Ns a mass T x y ^ (k - j)) := by
    intro x y
    have h_factor :
        ∫ η, term x y η ∂(asymCanonicalJointMeasure Nt Ns) =
          (∫ ηS, wickMonomial j cS (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS x) *
              wickMonomial j cS (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS y) ∂μS) *
          (∫ ηR,
              wickMonomial (k - j) cR
                (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR x) *
              wickMonomial (k - j) cR
                (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR y) ∂μR) := by
      rw [asymCanonicalJointMeasure]
      simpa [term, AsymCanonicalJoint, μS, μR, cS, cR,
        mul_assoc, mul_left_comm, mul_comm] using
        (integral_prod_mul
          (μ := μS) (ν := μR)
          (f := fun ηS =>
            wickMonomial j cS (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS x) *
              wickMonomial j cS (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS y))
          (g := fun ηR =>
            wickMonomial (k - j) cR (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR x) *
              wickMonomial (k - j) cR (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR y)))
    rw [h_factor]
    rw [asymCanonicalSmoothWickPower_two_site_marginal_eq_diag
      Nt Ns a mass ha hmass T j x y]
    rw [asymCanonicalRoughWickPower_two_site_marginal_eq_diag
      Nt Ns a mass ha hmass T hT (k - j) x y]
    ring
  calc
    ((a ^ 2) * (a ^ 2)) *
        ∑ x : AsymLatticeSites Nt Ns,
          ∫ η, ∑ y : AsymLatticeSites Nt Ns, term x y η ∂(asymCanonicalJointMeasure Nt Ns)
      = ((a ^ 2) * (a ^ 2)) *
          ∑ x : AsymLatticeSites Nt Ns,
            ∑ y : AsymLatticeSites Nt Ns,
              ∫ η, term x y η ∂(asymCanonicalJointMeasure Nt Ns) := by
                congr 1
                refine Finset.sum_congr rfl ?_
                intro x hx
                rw [MeasureTheory.integral_finset_sum _ (fun y _ => h_term_int x y)]
    _ = ((a ^ 2) * (a ^ 2)) *
          ∑ x : AsymLatticeSites Nt Ns,
            ∑ y : AsymLatticeSites Nt Ns,
              (((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
                (asymCanonicalSmoothCovariance Nt Ns a mass T x y ^ j *
                  asymCanonicalRoughCovariance Nt Ns a mass T x y ^ (k - j))) := by
                    congr 1
                    refine Finset.sum_congr rfl ?_
                    intro x hx
                    refine Finset.sum_congr rfl ?_
                    intro y hy
                    rw [hxy x y]
    _ = ((a ^ 2) * (a ^ 2)) *
          (((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
            ∑ x : AsymLatticeSites Nt Ns,
              ∑ y : AsymLatticeSites Nt Ns,
                (asymCanonicalSmoothCovariance Nt Ns a mass T x y ^ j *
                  asymCanonicalRoughCovariance Nt Ns a mass T x y ^ (k - j))) := by
                    have hfactor :
                        ∑ x : AsymLatticeSites Nt Ns,
                          ∑ y : AsymLatticeSites Nt Ns,
                            ((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
                              (asymCanonicalSmoothCovariance Nt Ns a mass T x y ^ j *
                                asymCanonicalRoughCovariance Nt Ns a mass T x y ^ (k - j)) =
                          ((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
                          ∑ x : AsymLatticeSites Nt Ns,
                            ∑ y : AsymLatticeSites Nt Ns,
                              (asymCanonicalSmoothCovariance Nt Ns a mass T x y ^ j *
                                asymCanonicalRoughCovariance Nt Ns a mass T x y ^ (k - j)) := by
                          simp [Finset.mul_sum, mul_assoc, mul_comm]
                    rw [hfactor]
    _ = ((a ^ 2) * (a ^ 2)) * ((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
          ∑ x : AsymLatticeSites Nt Ns,
            ∑ y : AsymLatticeSites Nt Ns,
              (asymCanonicalSmoothCovariance Nt Ns a mass T x y ^ j *
                asymCanonicalRoughCovariance Nt Ns a mass T x y ^ (k - j)) := by
                  ring

/-- The square of an asym cross term is integrable under the joint Gaussian law. -/
theorem asymCanonicalCrossTerm_sq_integrable
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T) (k j : ℕ) :
    Integrable
      (fun η : AsymCanonicalJoint Nt Ns =>
        (asymCanonicalCrossTerm Nt Ns a mass T η k j) ^ 2)
      (asymCanonicalJointMeasure Nt Ns) := by
  let cS := asymSmoothWickConstant Nt Ns a mass T
  let cR := asymCanonicalRoughWickConstant Nt Ns a mass T
  let μS : Measure (AsymCanonicalMode Nt Ns → ℝ) :=
    Measure.pi (fun _ : AsymCanonicalMode Nt Ns => ProbabilityTheory.gaussianReal 0 1)
  let μR : Measure (AsymCanonicalMode Nt Ns → ℝ) :=
    Measure.pi (fun _ : AsymCanonicalMode Nt Ns => ProbabilityTheory.gaussianReal 0 1)
  let term : AsymLatticeSites Nt Ns → AsymLatticeSites Nt Ns → AsymCanonicalJoint Nt Ns → ℝ :=
    fun x y η =>
      (wickMonomial j cS (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x) *
          wickMonomial j cS (asymCanonicalSmoothFieldFunction Nt Ns a mass T η y)) *
        (wickMonomial (k - j) cR (asymCanonicalRoughFieldFunction Nt Ns a mass T η x) *
          wickMonomial (k - j) cR (asymCanonicalRoughFieldFunction Nt Ns a mass T η y))
  have h_term_int :
      ∀ x y, Integrable (term x y) (asymCanonicalJointMeasure Nt Ns) := by
    intro x y
    rw [asymCanonicalJointMeasure]
    let f : (AsymCanonicalMode Nt Ns → ℝ) → ℝ := fun ηS =>
      wickMonomial j cS (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS x) *
        wickMonomial j cS (asymCanonicalSmoothFieldFunctionOfFst Nt Ns a mass T ηS y)
    let g : (AsymCanonicalMode Nt Ns → ℝ) → ℝ := fun ηR =>
      wickMonomial (k - j) cR (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR x) *
        wickMonomial (k - j) cR (asymCanonicalRoughFieldFunctionOfSnd Nt Ns a mass T ηR y)
    have hf : Integrable f μS := by
      simpa [f, μS, cS] using
        (asymCanonicalSmoothWickPower_two_site_marginal_integrable
          Nt Ns a mass ha hmass T j j x y)
    have hg : Integrable g μR := by
      simpa [g, μR, cR] using
        (asymCanonicalRoughWickPower_two_site_marginal_integrable
          Nt Ns a mass ha hmass T hT (k - j) (k - j) x y)
    simpa [term, AsymCanonicalJoint, f, g, μS, μR, cS, cR,
      mul_assoc, mul_left_comm, mul_comm] using
      (Integrable.mul_prod (μ := μS) (ν := μR) hf hg)
  have h_expand :
      ∀ η : AsymCanonicalJoint Nt Ns,
        (asymCanonicalCrossTerm Nt Ns a mass T η k j) ^ 2 =
          ((a ^ 2) * (a ^ 2)) * ∑ x : AsymLatticeSites Nt Ns,
            ∑ y : AsymLatticeSites Nt Ns, term x y η := by
    intro η
    rw [sq]
    unfold asymCanonicalCrossTerm term
    rw [show
      (a ^ 2 * ∑ x,
          wickMonomial j (asymSmoothWickConstant Nt Ns a mass T)
              (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x) *
            wickMonomial (k - j) (asymCanonicalRoughWickConstant Nt Ns a mass T)
              (asymCanonicalRoughFieldFunction Nt Ns a mass T η x)) *
        (a ^ 2 * ∑ x,
          wickMonomial j (asymSmoothWickConstant Nt Ns a mass T)
              (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x) *
            wickMonomial (k - j) (asymCanonicalRoughWickConstant Nt Ns a mass T)
              (asymCanonicalRoughFieldFunction Nt Ns a mass T η x)) =
      ((a ^ 2) * (a ^ 2)) *
      ((∑ x,
          wickMonomial j (asymSmoothWickConstant Nt Ns a mass T)
              (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x) *
            wickMonomial (k - j) (asymCanonicalRoughWickConstant Nt Ns a mass T)
              (asymCanonicalRoughFieldFunction Nt Ns a mass T η x)) *
        (∑ x,
          wickMonomial j (asymSmoothWickConstant Nt Ns a mass T)
              (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x) *
            wickMonomial (k - j) (asymCanonicalRoughWickConstant Nt Ns a mass T)
              (asymCanonicalRoughFieldFunction Nt Ns a mass T η x))) by
      ring]
    rw [Finset.sum_mul_sum]
    simp [cS, cR, mul_assoc, mul_left_comm]
  have h_sum_int :
      Integrable
        (fun η : AsymCanonicalJoint Nt Ns =>
          ∑ x : AsymLatticeSites Nt Ns,
            ∑ y : AsymLatticeSites Nt Ns, term x y η)
        (asymCanonicalJointMeasure Nt Ns) := by
    refine MeasureTheory.integrable_finset_sum _ ?_
    intro x hx
    exact MeasureTheory.integrable_finset_sum _ (fun y _ => h_term_int x y)
  rw [show
    (fun η : AsymCanonicalJoint Nt Ns =>
      (asymCanonicalCrossTerm Nt Ns a mass T η k j) ^ 2) =
      (fun η : AsymCanonicalJoint Nt Ns =>
        ((a ^ 2) * (a ^ 2)) * ∑ x : AsymLatticeSites Nt Ns,
          ∑ y : AsymLatticeSites Nt Ns, term x y η) by
      funext η
      exact h_expand η]
  exact h_sum_int.const_mul ((a ^ 2) * (a ^ 2))

/-! ## §6 Smooth covariance absolute bound -/

/-- The smooth covariance is bounded by its diagonal variance. -/
theorem abs_asymCanonicalSmoothCovariance_le_asymSmoothWickConstant
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (x y : AsymLatticeSites Nt Ns) :
    |asymCanonicalSmoothCovariance Nt Ns a mass T x y| ≤
      asymSmoothWickConstant Nt Ns a mass T := by
  let γ_x : AsymCanonicalMode Nt Ns → ℝ := asymCanonicalSmoothGamma Nt Ns a mass T x
  let γ_y : AsymCanonicalMode Nt Ns → ℝ := asymCanonicalSmoothGamma Nt Ns a mass T y
  have h_cs :
      (∑ m : AsymCanonicalMode Nt Ns, γ_x m * γ_y m) ^ 2 ≤
        (∑ m : AsymCanonicalMode Nt Ns, (γ_x m) ^ 2) *
          ∑ m : AsymCanonicalMode Nt Ns, (γ_y m) ^ 2 := by
    simpa [γ_x, γ_y] using
      (Finset.sum_mul_sq_le_sq_mul_sq
        (R := ℝ) (Finset.univ : Finset (AsymCanonicalMode Nt Ns)) γ_x γ_y)
  have hx :
      ∑ m : AsymCanonicalMode Nt Ns, (γ_x m) ^ 2 =
        asymSmoothWickConstant Nt Ns a mass T := by
    simpa [γ_x] using
      asymCanonicalSmoothGamma_sq_sum_eq_asymSmoothWickConstant
        Nt Ns a mass ha hmass T x
  have hy :
      ∑ m : AsymCanonicalMode Nt Ns, (γ_y m) ^ 2 =
        asymSmoothWickConstant Nt Ns a mass T := by
    simpa [γ_y] using
      asymCanonicalSmoothGamma_sq_sum_eq_asymSmoothWickConstant
        Nt Ns a mass ha hmass T y
  have h_nonneg : 0 ≤ asymSmoothWickConstant Nt Ns a mass T := by
    rw [← hx]
    exact Finset.sum_nonneg fun m hm => sq_nonneg (γ_x m)
  have h_sq :
      (∑ m : AsymCanonicalMode Nt Ns, γ_x m * γ_y m) ^ 2 ≤
        asymSmoothWickConstant Nt Ns a mass T *
          asymSmoothWickConstant Nt Ns a mass T := by
    simpa [hx, hy] using h_cs
  have h_abs :
      |∑ m : AsymCanonicalMode Nt Ns, γ_x m * γ_y m| ≤
        asymSmoothWickConstant Nt Ns a mass T := by
    have h_abs_sq :
        |∑ m : AsymCanonicalMode Nt Ns, γ_x m * γ_y m| ^ 2 ≤
          |asymSmoothWickConstant Nt Ns a mass T| ^ 2 := by
      simpa [sq_abs, pow_two] using h_sq
    have := (sq_le_sq).mp h_abs_sq
    simpa [abs_of_nonneg h_nonneg] using this
  rw [show asymCanonicalSmoothCovariance Nt Ns a mass T x y =
      ∑ m : AsymCanonicalMode Nt Ns, γ_x m * γ_y m from by
      simpa [γ_x, γ_y] using
        asymCanonicalSmoothCovariance_eq_sum_gamma_mul_gamma
          Nt Ns a mass ha hmass T x y]
  exact h_abs

/-! ## §7 Unified rough covariance row-sum bound -/

/-- Uniform `O(T)` row-sum bound for any rough covariance power `m ≥ 1`. -/
theorem asymCanonicalRoughCovariance_pow_sum_le_uniform
    (mass Lt Ls : ℝ) (hLt : 0 < Lt) (hLs : 0 < Ls) (hmass : 0 < mass)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ C_m : ℝ, 0 < C_m ∧
      ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (_ha : 0 < a),
        (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls → ∀ (T : ℝ), 0 < T →
        ∀ (x : AsymLatticeSites Nt Ns),
          a ^ 2 * ∑ y : AsymLatticeSites Nt Ns,
            |asymCanonicalRoughCovariance Nt Ns a mass T x y| ^ m ≤ C_m * T := by
  by_cases hm1 : m = 1
  · rcases asymCanonicalRoughCovariance_pow_one_sum_le_uniform
      mass Lt Ls hLt hLs hmass with ⟨C1, hC1_pos, hC1⟩
    refine ⟨C1, hC1_pos, ?_⟩
    intro Nt Ns _ _ a ha hvolt hvols T hT x
    simpa [hm1] using hC1 Nt Ns a ha hvolt hvols T hT x
  by_cases hm2 : m = 2
  · rcases asymCanonicalRoughCovariance_pow_two_sum_le_uniform
      mass Lt Ls hLt hLs hmass with ⟨C2, hC2_pos, hC2⟩
    refine ⟨C2, hC2_pos, ?_⟩
    intro Nt Ns _ _ a ha hvolt hvols T hT x
    simpa [hm2] using hC2 Nt Ns a ha hvolt hvols T hT x
  · have hm3 : 3 ≤ m := by omega
    exact asymCanonicalRoughCovariance_pow_sum_le_uniform_of_three_le
      mass Lt Ls hLt hLs hmass m hm3

/-! ## §8 Per-cross-term L² bound -/

/-- Uniform asym per-cross-term L² bound. -/
theorem asymCanonicalCrossTerm_l2_sq_le
    (mass Lt Ls : ℝ) (hLt : 0 < Lt) (hLs : 0 < Ls) (hmass : 0 < mass)
    (k j : ℕ) (hkj : 1 ≤ k - j) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (_ha : 0 < a),
        (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
        ∀ (T : ℝ), 0 < T →
        ∃ _hf : MeasureTheory.MemLp
            (fun η : AsymCanonicalJoint Nt Ns =>
              asymCanonicalCrossTerm Nt Ns a mass T η k j)
            2
            (asymCanonicalJointMeasure Nt Ns),
          ∫ η, (asymCanonicalCrossTerm Nt Ns a mass T η k j) ^ 2
            ∂(asymCanonicalJointMeasure Nt Ns) ≤
            K * T * (1 + |Real.log T|) ^ j := by
  rcases asymSmoothWickConstant_le_log_uniform mass Lt Ls hLt hLs hmass with
    ⟨A, B, hA, hB, h_smooth_uniform⟩
  rcases asymCanonicalRoughCovariance_pow_sum_le_uniform mass Lt Ls hLt hLs hmass (k - j) hkj with
    ⟨C_m, hC_m_pos, h_rough_uniform⟩
  let K : ℝ := ((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
    (Lt * Ls) * (A + B + 1) ^ j * C_m
  refine ⟨K, ?_, ?_⟩
  · have hfacj : 0 < (j.factorial : ℝ) := by positivity
    have hfacr : 0 < (((k - j).factorial : ℝ)) := by positivity
    have hvol : 0 < Lt * Ls := by positivity
    have hAB1 : 0 < A + B + 1 := by linarith
    have hpow : 0 < (A + B + 1) ^ j := pow_pos hAB1 j
    dsimp [K]
    positivity
  · intro Nt Ns _ _ a ha hvolt hvols T hT
    have hmeas_fun :
        Measurable
          (fun η : AsymCanonicalJoint Nt Ns => asymCanonicalCrossTerm Nt Ns a mass T η k j) := by
      unfold asymCanonicalCrossTerm
      refine measurable_const.mul ?_
      have hterm :
          ∀ x : AsymLatticeSites Nt Ns,
            Measurable (fun η : AsymCanonicalJoint Nt Ns =>
              wickMonomial j (asymSmoothWickConstant Nt Ns a mass T)
                  (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x) *
                wickMonomial (k - j) (asymCanonicalRoughWickConstant Nt Ns a mass T)
                  (asymCanonicalRoughFieldFunction Nt Ns a mass T η x)) := by
        intro x
        let f : AsymCanonicalJoint Nt Ns → ℝ := fun η =>
          wickMonomial j (asymSmoothWickConstant Nt Ns a mass T)
            (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x)
        let g : AsymCanonicalJoint Nt Ns → ℝ := fun η =>
          wickMonomial (k - j) (asymCanonicalRoughWickConstant Nt Ns a mass T)
            (asymCanonicalRoughFieldFunction Nt Ns a mass T η x)
        have hf : Measurable f := by
          dsimp [f]
          exact (wickMonomial_continuous j (asymSmoothWickConstant Nt Ns a mass T)).measurable.comp
            (asymCanonicalSmoothFieldFunction_pointwise_measurable Nt Ns a mass T x)
        have hg : Measurable g := by
          dsimp [g]
          exact
            (wickMonomial_continuous
              (k - j) (asymCanonicalRoughWickConstant Nt Ns a mass T)).measurable.comp
            (asymCanonicalRoughFieldFunction_pointwise_measurable Nt Ns a mass T x)
        simpa [f, g] using hf.mul hg
      have hsum :
          ∀ s : Finset (AsymLatticeSites Nt Ns),
            Measurable (fun η : AsymCanonicalJoint Nt Ns =>
              s.sum fun x =>
                wickMonomial j (asymSmoothWickConstant Nt Ns a mass T)
                    (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x) *
                  wickMonomial (k - j) (asymCanonicalRoughWickConstant Nt Ns a mass T)
                    (asymCanonicalRoughFieldFunction Nt Ns a mass T η x)) := by
        intro s
        refine Finset.induction_on s ?_ ?_
        · simp
        · intro x s hx hs
          simpa [Finset.sum_insert, hx] using (hterm x).add hs
      simpa using hsum Finset.univ
    have hmeas :
        AEStronglyMeasurable
          (fun η : AsymCanonicalJoint Nt Ns => asymCanonicalCrossTerm Nt Ns a mass T η k j)
          (asymCanonicalJointMeasure Nt Ns) :=
      hmeas_fun.aestronglyMeasurable
    have h_card_nat : Fintype.card (AsymLatticeSites Nt Ns) = Nt * Ns := by
      simp [AsymLatticeSites]
    have h_card :
        (Fintype.card (AsymLatticeSites Nt Ns) : ℝ) = (Nt : ℝ) * (Ns : ℝ) := by
      rw [h_card_nat]
      norm_num
    have h_vol :
        a ^ 2 * (Fintype.card (AsymLatticeSites Nt Ns) : ℝ) = Lt * Ls := by
      rw [h_card]
      calc
        a ^ 2 * ((Nt : ℝ) * (Ns : ℝ)) = ((Nt : ℝ) * a) * ((Ns : ℝ) * a) := by ring
        _ = Lt * Ls := by rw [hvolt, hvols]
    have hsmooth_nonneg : 0 ≤ asymSmoothWickConstant Nt Ns a mass T := by
      unfold asymSmoothWickConstant
      have ha2_pos : 0 < a ^ 2 := pow_pos ha 2
      have hsum_nonneg :
          0 ≤ ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
            asymCanonicalSmoothWeight Nt Ns a mass T (m₁, m₂) := by
        refine Finset.sum_nonneg ?_
        intro m₁ hm₁
        refine Finset.sum_nonneg ?_
        intro m₂ hm₂
        exact asymCanonicalSmoothWeight_nonneg Nt Ns a mass ha hmass T (m₁, m₂)
      apply mul_nonneg (le_of_lt (inv_pos.mpr ha2_pos))
      apply mul_nonneg
      · positivity
      · exact hsum_nonneg
    have h_log_nonneg : 0 ≤ 1 + |Real.log T| := by positivity
    have h_log_one : 1 ≤ 1 + |Real.log T| := by
      linarith [abs_nonneg (Real.log T)]
    have h_smooth_linear :
        asymSmoothWickConstant Nt Ns a mass T ≤
          (A + B + 1) * (1 + |Real.log T|) := by
      have hbase := h_smooth_uniform Nt Ns a ha hvolt hvols T hT
      calc
        asymSmoothWickConstant Nt Ns a mass T ≤ A + B * (1 + |Real.log T|) := hbase
        _ ≤ A * (1 + |Real.log T|) + B * (1 + |Real.log T|) := by
          nlinarith [hA, h_log_one]
        _ = (A + B) * (1 + |Real.log T|) := by ring
        _ ≤ (A + B + 1) * (1 + |Real.log T|) := by
          nlinarith [h_log_nonneg]
    have h_smooth_pow :
        asymSmoothWickConstant Nt Ns a mass T ^ j ≤
          (A + B + 1) ^ j * (1 + |Real.log T|) ^ j := by
      calc
        asymSmoothWickConstant Nt Ns a mass T ^ j ≤
            ((A + B + 1) * (1 + |Real.log T|)) ^ j :=
          pow_le_pow_left₀ hsmooth_nonneg h_smooth_linear j
        _ = (A + B + 1) ^ j * (1 + |Real.log T|) ^ j := by
          rw [mul_pow]
    have h_abs_sum :
        ∑ x : AsymLatticeSites Nt Ns,
          ∑ y : AsymLatticeSites Nt Ns,
            asymCanonicalSmoothCovariance Nt Ns a mass T x y ^ j *
              asymCanonicalRoughCovariance Nt Ns a mass T x y ^ (k - j)
        ≤
        ∑ x : AsymLatticeSites Nt Ns,
          ∑ y : AsymLatticeSites Nt Ns,
            |asymCanonicalSmoothCovariance Nt Ns a mass T x y| ^ j *
              |asymCanonicalRoughCovariance Nt Ns a mass T x y| ^ (k - j) := by
      refine Finset.sum_le_sum ?_
      intro x hx
      refine Finset.sum_le_sum ?_
      intro y hy
      simpa [abs_mul, abs_pow] using
        (le_abs_self
          (asymCanonicalSmoothCovariance Nt Ns a mass T x y ^ j *
            asymCanonicalRoughCovariance Nt Ns a mass T x y ^ (k - j)))
    have h_summand_bound :
        ∀ x y : AsymLatticeSites Nt Ns,
          |asymCanonicalSmoothCovariance Nt Ns a mass T x y| ^ j *
              |asymCanonicalRoughCovariance Nt Ns a mass T x y| ^ (k - j)
            ≤
          asymSmoothWickConstant Nt Ns a mass T ^ j *
            |asymCanonicalRoughCovariance Nt Ns a mass T x y| ^ (k - j) := by
      intro x y
      have hxy :=
        abs_asymCanonicalSmoothCovariance_le_asymSmoothWickConstant
          Nt Ns a mass ha hmass T x y
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg _) hxy j)
        (pow_nonneg (abs_nonneg _) _)
    have h_sum_bound :
        ∑ x : AsymLatticeSites Nt Ns,
          ∑ y : AsymLatticeSites Nt Ns,
            |asymCanonicalSmoothCovariance Nt Ns a mass T x y| ^ j *
              |asymCanonicalRoughCovariance Nt Ns a mass T x y| ^ (k - j)
        ≤
        asymSmoothWickConstant Nt Ns a mass T ^ j *
          ∑ x : AsymLatticeSites Nt Ns,
            ∑ y : AsymLatticeSites Nt Ns,
              |asymCanonicalRoughCovariance Nt Ns a mass T x y| ^ (k - j) := by
      calc
        ∑ x : AsymLatticeSites Nt Ns,
            ∑ y : AsymLatticeSites Nt Ns,
              |asymCanonicalSmoothCovariance Nt Ns a mass T x y| ^ j *
                |asymCanonicalRoughCovariance Nt Ns a mass T x y| ^ (k - j)
          ≤
            ∑ x : AsymLatticeSites Nt Ns,
              ∑ y : AsymLatticeSites Nt Ns,
                (asymSmoothWickConstant Nt Ns a mass T ^ j *
                  |asymCanonicalRoughCovariance Nt Ns a mass T x y| ^ (k - j)) := by
              refine Finset.sum_le_sum ?_
              intro x hx
              refine Finset.sum_le_sum ?_
              intro y hy
              exact h_summand_bound x y
        _ = asymSmoothWickConstant Nt Ns a mass T ^ j *
              ∑ x : AsymLatticeSites Nt Ns,
                ∑ y : AsymLatticeSites Nt Ns,
                  |asymCanonicalRoughCovariance Nt Ns a mass T x y| ^ (k - j) := by
              simp [Finset.mul_sum, mul_comm]
    have h_rough_sum :
        a ^ 2 *
          ∑ x : AsymLatticeSites Nt Ns,
            (a ^ 2 *
              ∑ y : AsymLatticeSites Nt Ns,
                |asymCanonicalRoughCovariance Nt Ns a mass T x y| ^ (k - j))
        ≤
        (Lt * Ls) * (C_m * T) := by
      have h_inner :
          ∑ x : AsymLatticeSites Nt Ns,
            (a ^ 2 *
              ∑ y : AsymLatticeSites Nt Ns,
                |asymCanonicalRoughCovariance Nt Ns a mass T x y| ^ (k - j))
          ≤
          ∑ x : AsymLatticeSites Nt Ns, C_m * T := by
        refine Finset.sum_le_sum ?_
        intro x hx
        exact h_rough_uniform Nt Ns a ha hvolt hvols T hT x
      calc
        a ^ 2 *
            ∑ x : AsymLatticeSites Nt Ns,
              (a ^ 2 *
                ∑ y : AsymLatticeSites Nt Ns,
                  |asymCanonicalRoughCovariance Nt Ns a mass T x y| ^ (k - j))
          ≤
            a ^ 2 * ∑ x : AsymLatticeSites Nt Ns, C_m * T := by
              gcongr
        _ = (a ^ 2 * (Fintype.card (AsymLatticeSites Nt Ns) : ℝ)) * (C_m * T) := by
              simp [mul_assoc, mul_comm]
        _ = (Lt * Ls) * (C_m * T) := by rw [h_vol]
    have h_sq_int :
        Integrable
          (fun η : AsymCanonicalJoint Nt Ns =>
            (asymCanonicalCrossTerm Nt Ns a mass T η k j) ^ 2)
          (asymCanonicalJointMeasure Nt Ns) := by
      exact asymCanonicalCrossTerm_sq_integrable Nt Ns a mass ha hmass T hT k j
    let hf : MeasureTheory.MemLp
        (fun η : AsymCanonicalJoint Nt Ns =>
          asymCanonicalCrossTerm Nt Ns a mass T η k j)
        2
        (asymCanonicalJointMeasure Nt Ns) :=
      (memLp_two_iff_integrable_sq hmeas).mpr h_sq_int
    refine ⟨hf, ?_⟩
    calc
      ∫ η, (asymCanonicalCrossTerm Nt Ns a mass T η k j) ^ 2
          ∂(asymCanonicalJointMeasure Nt Ns)
        = ((a ^ 2) * (a ^ 2)) * ((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
            ∑ x : AsymLatticeSites Nt Ns,
              ∑ y : AsymLatticeSites Nt Ns,
                asymCanonicalSmoothCovariance Nt Ns a mass T x y ^ j *
                  asymCanonicalRoughCovariance Nt Ns a mass T x y ^ (k - j) := by
            simpa using
              asymCanonicalCrossTerm_l2_sq_eq_covSum Nt Ns a mass ha hmass T hT k j
      _ ≤ ((a ^ 2) * (a ^ 2)) * ((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
            ∑ x : AsymLatticeSites Nt Ns,
              ∑ y : AsymLatticeSites Nt Ns,
                (|asymCanonicalSmoothCovariance Nt Ns a mass T x y| ^ j *
                  |asymCanonicalRoughCovariance Nt Ns a mass T x y| ^ (k - j)) := by
            gcongr
      _ ≤ ((a ^ 2) * (a ^ 2)) * ((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
            (asymSmoothWickConstant Nt Ns a mass T ^ j *
              ∑ x : AsymLatticeSites Nt Ns,
                ∑ y : AsymLatticeSites Nt Ns,
                  |asymCanonicalRoughCovariance Nt Ns a mass T x y| ^ (k - j)) := by
            gcongr
      _ = ((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
            (asymSmoothWickConstant Nt Ns a mass T ^ j) *
            (a ^ 2 *
              ∑ x : AsymLatticeSites Nt Ns,
                (a ^ 2 *
                  ∑ y : AsymLatticeSites Nt Ns,
                    |asymCanonicalRoughCovariance Nt Ns a mass T x y| ^ (k - j))) := by
            simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      _ ≤ ((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
            (asymSmoothWickConstant Nt Ns a mass T ^ j) *
            ((Lt * Ls) * (C_m * T)) := by
            gcongr
      _ ≤ ((j.factorial : ℝ) * ((k - j).factorial : ℝ)) *
            ((A + B + 1) ^ j * (1 + |Real.log T|) ^ j) *
            ((Lt * Ls) * (C_m * T)) := by
            gcongr
      _ = K * T * (1 + |Real.log T|) ^ j := by
            dsimp [K]
            ring

end Pphi2

end
