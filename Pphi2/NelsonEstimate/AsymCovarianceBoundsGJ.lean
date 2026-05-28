/- 
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Glimm-Jaffe covariance bounds on the isotropic rectangular lattice

This file ports the next square Nelson layer from
`Pphi2/NelsonEstimate/HeatKernelBound.lean`,
`Pphi2/NelsonEstimate/CovarianceBoundsGJ.lean`, and the interaction
definitions from `RoughErrorBound.lean` to the isotropic heterogeneous
lattice `Z_Nt × Z_Ns`.

The key simplification is that the rectangular dispersion splits:

`λ_(m₁,m₂) = λ_t(m₁) + λ_s(m₂) + mass²`,

so the heat-kernel trace factorizes into a product of two 1D traces.
-/

import Pphi2.NelsonEstimate.AsymFieldDecomposition
import Pphi2.NelsonEstimate.FieldDecomposition
import Pphi2.NelsonEstimate.HeatKernelBound
import Lattice.FKG
import MarkovSemigroups.Matrix.HeatKernel
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Prod

noncomputable section

open MeasureTheory ProbabilityTheory GaussianField
open scoped BigOperators

namespace Pphi2

/-- Smooth Wick constant for the asym canonical field split. -/
def asymSmoothWickConstant (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) : ℝ :=
  (a ^ 2 : ℝ)⁻¹ *
    ((1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) *
      ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
        asymCanonicalSmoothWeight Nt Ns a mass T (m₁, m₂))

/-- Rough covariance kernel of the asym canonical field split. -/
def asymCanonicalRoughCovariance (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (x y : AsymLatticeSites Nt Ns) : ℝ :=
  (a ^ 2 : ℝ)⁻¹ *
    ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
      asymCanonicalRoughWeight Nt Ns a mass T (m₁, m₂) *
        asymCanonicalBasis Nt Ns (m₁, m₂) x *
        asymCanonicalBasis Nt Ns (m₁, m₂) y /
        asymCanonicalNormSq Nt Ns (m₁, m₂)

/-- Wick-polynomial interaction evaluated at the smooth asym field. -/
def asymCanonicalSmoothInteraction (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (P : InteractionPolynomial)
    (η : AsymCanonicalJoint Nt Ns) : ℝ :=
  a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
    wickPolynomial P (asymSmoothWickConstant Nt Ns a mass T)
      (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x)

/-- Wick-polynomial interaction evaluated at the full asym field. -/
def asymCanonicalFullInteractionJoint (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (P : InteractionPolynomial)
    (η : AsymCanonicalJoint Nt Ns) : ℝ :=
  a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
    wickPolynomial P (wickConstantAsym Nt Ns a mass)
      (asymCanonicalSumFieldFunction Nt Ns a mass T η x)

/-- Rough-field Wick error on the asym canonical joint space. -/
def asymCanonicalRoughError (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (P : InteractionPolynomial)
    (η : AsymCanonicalJoint Nt Ns) : ℝ :=
  asymCanonicalFullInteractionJoint Nt Ns a mass T P η -
    asymCanonicalSmoothInteraction Nt Ns a mass T P η

private def fin1Site {N : ℕ} [NeZero N] (z : ZMod N) : FinLatticeSites 1 N :=
  zmodToFin1 N z

private lemma zmod_sum_eq_fin_sum {α : Type*} [AddCommMonoid α]
    (N : ℕ) [NeZero N] (g : ℕ → α) :
    ∑ z : ZMod N, g (ZMod.val z) = ∑ k : Fin N, g k := by
  exact Fintype.sum_bijective
    (fun (x : ZMod N) =>
      (⟨ZMod.val x, ZMod.val_lt x⟩ : Fin N))
    ⟨fun a b h => ZMod.val_injective N (Fin.mk.inj h),
     fun ⟨n, hn⟩ =>
      ⟨(n : ZMod N), by
        ext
        exact ZMod.val_natCast_of_lt hn⟩⟩
    _ _ (fun _ => rfl)

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

private lemma sum_fin_exp_latticeEigenvalue1d_eq_range
    (N : ℕ) [NeZero N] (a t : ℝ) :
    (∑ m : Fin N, Real.exp (-t * latticeEigenvalue1d N a m)) =
      ∑ k ∈ Finset.range N,
        Real.exp (-t * (4 * Real.sin (Real.pi * (k : ℝ) / N) ^ 2 / a ^ 2)) := by
  calc
    (∑ m : Fin N, Real.exp (-t * latticeEigenvalue1d N a m))
      = ∑ z : ZMod N,
          Real.exp (-t * ((4 / a ^ 2) * Real.sin (Real.pi * (ZMod.val z : ℝ) / N) ^ 2)) := by
            symm
            simpa using
              (sum_rawFrequency_eq_sum_latticeEigenvalue1d (N := N) (a := a)
                (F := fun x : ℝ => Real.exp (-t * x)))
    _ = ∑ k : Fin N,
          Real.exp (-t * ((4 / a ^ 2) * Real.sin (Real.pi * (k : ℝ) / N) ^ 2)) := by
            convert zmod_sum_eq_fin_sum N
              (fun k =>
                Real.exp (-t * ((4 / a ^ 2) * Real.sin (Real.pi * (k : ℝ) / N) ^ 2)))
              using 1
    _ = ∑ k ∈ Finset.range N,
          Real.exp (-t * (4 * Real.sin (Real.pi * (k : ℝ) / N) ^ 2 / a ^ 2)) := by
            rw [← Fin.sum_univ_eq_sum_range]
            refine Finset.sum_congr rfl ?_
            intro k hk
            congr 1
            ring

private lemma one_add_inv_sqrt_sq_le_two_mul_one_add_inv
    (s : ℝ) (hs : 0 < s) :
    (1 + 1 / Real.sqrt s) ^ 2 ≤ 2 * (1 + 1 / s) := by
  set u : ℝ := 1 / Real.sqrt s
  have hu_sq : u ^ 2 = 1 / s := by
    have hsqrt : Real.sqrt s ≠ 0 := by positivity
    have hsqrt_sq : (Real.sqrt s) ^ 2 = s := by
      rw [Real.sq_sqrt (show 0 ≤ s by linarith)]
    calc
      u ^ 2 = (1 / Real.sqrt s) ^ 2 := by simp [u]
      _ = 1 / ((Real.sqrt s) ^ 2) := by field_simp [hsqrt]
      _ = 1 / s := by rw [hsqrt_sq]
  have h2u : 2 * u ≤ u ^ 2 + 1 := by
    have hnn : 0 ≤ (u - 1) ^ 2 := sq_nonneg _
    nlinarith
  calc
    (1 + 1 / Real.sqrt s) ^ 2 = (1 + u) ^ 2 := by simp [u]
    _ = 1 + 2 * u + u ^ 2 := by ring
    _ ≤ 1 + (u ^ 2 + 1) + u ^ 2 := by gcongr
    _ = 2 * (1 + u ^ 2) := by ring
    _ = 2 * (1 + 1 / s) := by rw [hu_sq]

private def asymHeatKernelMatrix (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
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
  rw [hbase]
  rw [sum_fun_fin1_eq_sum N]
  refine Finset.sum_congr rfl ?_
  intro m hm
  simp [fin1Site, zmodToFin1, latticeFourierProductBasisFun, latticeFourierProductNormSq]

private lemma asymHeatKernel_entry_eq_eigenvalue_average
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a : ℝ) (ha : a ≠ 0) (t : ℝ)
    (x y : AsymLatticeSites Nt Ns) :
    asymHeatKernelMatrix Nt Ns a t x y =
      ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
        Real.exp (-t * (latticeEigenvalue1d Nt a m₁ + latticeEigenvalue1d Ns a m₂)) *
          asymCanonicalBasis Nt Ns (m₁, m₂) x *
          asymCanonicalBasis Nt Ns (m₁, m₂) y /
          asymCanonicalNormSq Nt Ns (m₁, m₂) := by
  unfold asymHeatKernelMatrix
  rw [oneDim_heatKernel_entry_eq_sum Nt a ha t x.1 y.1,
    oneDim_heatKernel_entry_eq_sum Ns a ha t x.2 y.2]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl ?_
  intro m₁ hm₁
  refine Finset.sum_congr rfl ?_
  intro m₂ hm₂
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
  have hcard_t : (Fintype.card (FinLatticeSites 1 Nt) : ℝ) = Nt := by
    simp [FinLatticeSites]
  have hcard_s : (Fintype.card (FinLatticeSites 1 Ns) : ℝ) = Ns := by
    simp [FinLatticeSites]
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
  rw [hcard_t, hcard_s, hsum_t, hsum_s]
  simp [AsymLatticeSites]
  ring

private lemma asymHeatKernel_row_sum_eq_one
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a : ℝ) (ha : 0 < a) (t : ℝ) (x : AsymLatticeSites Nt Ns) :
    ∑ y : AsymLatticeSites Nt Ns, asymHeatKernelMatrix Nt Ns a t x y = 1 := by
  have hrow_t :
      ∑ z : ZMod Nt, latticeHeatKernelMatrix 1 Nt a t (fin1Site x.1) (fin1Site z) = 1 := by
    have h :=
      heatKernel_row_sum_eq_one (d := 1) (N := Nt) (a := a) ha t (fin1Site x.1)
    simpa [sum_fin1_eq_sum_zmod] using h
  have hrow_s :
      ∑ z : ZMod Ns, latticeHeatKernelMatrix 1 Ns a t (fin1Site x.2) (fin1Site z) = 1 := by
    have h :=
      heatKernel_row_sum_eq_one (d := 1) (N := Ns) (a := a) ha t (fin1Site x.2)
    simpa [sum_fin1_eq_sum_zmod] using h
  rw [sum_factor_asym]
  simp [asymHeatKernelMatrix]
  calc
    (∑ a₁ : ZMod Nt, ∑ b : ZMod Ns,
      latticeHeatKernelMatrix 1 Nt a t (fin1Site x.1) (fin1Site a₁) *
        latticeHeatKernelMatrix 1 Ns a t (fin1Site x.2) (fin1Site b))
      = (∑ z : ZMod Nt, latticeHeatKernelMatrix 1 Nt a t (fin1Site x.1) (fin1Site z)) *
          ∑ z : ZMod Ns, latticeHeatKernelMatrix 1 Ns a t (fin1Site x.2) (fin1Site z) := by
            rw [← Fintype.sum_mul_sum]
    _ = 1 := by
          rw [hrow_t, hrow_s]
          ring

private lemma oneDim_heatKernel_nonneg
    (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a) (t : ℝ) (ht : 0 ≤ t)
    (x y : ZMod N) :
    0 ≤ latticeHeatKernelMatrix 1 N a t (fin1Site x) (fin1Site y) := by
  have hZ : MatrixSemigroup.IsZMatrix (negLaplacianMatrix 1 N a) := by
    intro u v huv
    have hoff :=
      massOperator_offDiag_nonpos 1 N a 1 ha (by norm_num : 0 < (1 : ℝ)) u v huv
    simpa [negLaplacianMatrix, massOperatorMatrix, massOperatorEntry, massOperator,
      finLatticeDelta, huv] using hoff
  simpa [latticeHeatKernelMatrix] using
    MatrixSemigroup.heat_kernel_entrywise_nonneg (negLaplacianMatrix 1 N a) hZ t ht
      (fin1Site x) (fin1Site y)

private lemma asymHeatKernel_nonneg
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a : ℝ) (ha : 0 < a) (t : ℝ) (ht : 0 ≤ t)
    (x y : AsymLatticeSites Nt Ns) :
    0 ≤ asymHeatKernelMatrix Nt Ns a t x y := by
  unfold asymHeatKernelMatrix
  exact mul_nonneg
    (oneDim_heatKernel_nonneg Nt a ha t ht x.1 y.1)
    (oneDim_heatKernel_nonneg Ns a ha t ht x.2 y.2)

private lemma asymHeatKernel_row_pairing_eq_diagonal
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a s t : ℝ) (x : AsymLatticeSites Nt Ns) :
    ∑ y : AsymLatticeSites Nt Ns,
      asymHeatKernelMatrix Nt Ns a s x y *
        asymHeatKernelMatrix Nt Ns a t x y =
      asymHeatKernelMatrix Nt Ns a (s + t) x x := by
  have hpair_t :
      ∑ z : ZMod Nt,
        latticeHeatKernelMatrix 1 Nt a s (fin1Site x.1) (fin1Site z) *
          latticeHeatKernelMatrix 1 Nt a t (fin1Site x.1) (fin1Site z) =
        latticeHeatKernelMatrix 1 Nt a (s + t) (fin1Site x.1) (fin1Site x.1) := by
    have h :=
      heatKernel_row_pairing_eq_diagonal (d := 1) (N := Nt) a s t (fin1Site x.1)
    simpa [sum_fin1_eq_sum_zmod] using h
  have hpair_s :
      ∑ z : ZMod Ns,
        latticeHeatKernelMatrix 1 Ns a s (fin1Site x.2) (fin1Site z) *
          latticeHeatKernelMatrix 1 Ns a t (fin1Site x.2) (fin1Site z) =
        latticeHeatKernelMatrix 1 Ns a (s + t) (fin1Site x.2) (fin1Site x.2) := by
    have h :=
      heatKernel_row_pairing_eq_diagonal (d := 1) (N := Ns) a s t (fin1Site x.2)
    simpa [sum_fin1_eq_sum_zmod] using h
  rw [sum_factor_asym]
  simp [asymHeatKernelMatrix]
  calc
    (∑ a₁ : ZMod Nt, ∑ b : ZMod Ns,
      latticeHeatKernelMatrix 1 Nt a s (fin1Site x.1) (fin1Site a₁) *
          latticeHeatKernelMatrix 1 Ns a s (fin1Site x.2) (fin1Site b) *
        (latticeHeatKernelMatrix 1 Nt a t (fin1Site x.1) (fin1Site a₁) *
          latticeHeatKernelMatrix 1 Ns a t (fin1Site x.2) (fin1Site b)))
      = ∑ a₁ : ZMod Nt, ∑ b : ZMod Ns,
          (latticeHeatKernelMatrix 1 Nt a s (fin1Site x.1) (fin1Site a₁) *
            latticeHeatKernelMatrix 1 Nt a t (fin1Site x.1) (fin1Site a₁)) *
          (latticeHeatKernelMatrix 1 Ns a s (fin1Site x.2) (fin1Site b) *
            latticeHeatKernelMatrix 1 Ns a t (fin1Site x.2) (fin1Site b)) := by
            refine Finset.sum_congr rfl ?_
            intro a₁ ha₁
            refine Finset.sum_congr rfl ?_
            intro b hb
            ring
    _ = (∑ z : ZMod Nt,
          latticeHeatKernelMatrix 1 Nt a s (fin1Site x.1) (fin1Site z) *
            latticeHeatKernelMatrix 1 Nt a t (fin1Site x.1) (fin1Site z)) *
        ∑ z : ZMod Ns,
          latticeHeatKernelMatrix 1 Ns a s (fin1Site x.2) (fin1Site z) *
            latticeHeatKernelMatrix 1 Ns a t (fin1Site x.2) (fin1Site z) := by
            rw [← Fintype.sum_mul_sum]
    _ = asymHeatKernelMatrix Nt Ns a (s + t) x x := by
            rw [hpair_t, hpair_s]
            rfl

/-- Heat-kernel trace over the rectangular dispersion. -/
theorem asym_heat_kernel_trace_factorization
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass t : ℝ) :
    (∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
      Real.exp (-t * asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂))) =
      Real.exp (-t * mass ^ 2) *
        (∑ m₁ : Fin Nt, Real.exp (-t * latticeEigenvalue1d Nt a m₁)) *
        ∑ m₂ : Fin Ns, Real.exp (-t * latticeEigenvalue1d Ns a m₂) := by
  calc
    (∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
        Real.exp (-t * asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂)))
      = ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
          Real.exp (-t * mass ^ 2) *
            (Real.exp (-t * latticeEigenvalue1d Nt a m₁) *
              Real.exp (-t * latticeEigenvalue1d Ns a m₂)) := by
                refine Finset.sum_congr rfl ?_
                intro m₁ hm₁
                refine Finset.sum_congr rfl ?_
                intro m₂ hm₂
                rw [show -t * asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂) =
                    -t * mass ^ 2 +
                      (-t * latticeEigenvalue1d Nt a m₁ + -t * latticeEigenvalue1d Ns a m₂) by
                      simp [asymCanonicalEigenvalue]; ring]
                rw [Real.exp_add, Real.exp_add]
    _ = ∑ m₁ : Fin Nt,
          Real.exp (-t * mass ^ 2) *
            ∑ m₂ : Fin Ns,
              Real.exp (-t * latticeEigenvalue1d Nt a m₁) *
                Real.exp (-t * latticeEigenvalue1d Ns a m₂) := by
            refine Finset.sum_congr rfl ?_
            intro m₁ hm₁
            rw [Finset.mul_sum]
    _ = Real.exp (-t * mass ^ 2) *
          (∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
            Real.exp (-t * latticeEigenvalue1d Nt a m₁) *
              Real.exp (-t * latticeEigenvalue1d Ns a m₂)) := by
            rw [← Finset.mul_sum]
    _ = Real.exp (-t * mass ^ 2) *
          ((∑ m₁ : Fin Nt, Real.exp (-t * latticeEigenvalue1d Nt a m₁)) *
            ∑ m₂ : Fin Ns, Real.exp (-t * latticeEigenvalue1d Ns a m₂)) := by
            rw [Fintype.sum_mul_sum]
    _ = Real.exp (-t * mass ^ 2) *
          (∑ m₁ : Fin Nt, Real.exp (-t * latticeEigenvalue1d Nt a m₁)) *
            ∑ m₂ : Fin Ns, Real.exp (-t * latticeEigenvalue1d Ns a m₂) := by
            ring

private lemma exp_mul_one_add_inv_sqrt_sq_le_const_div
    (μ t : ℝ) (hμ : 0 < μ) (ht : 0 < t) :
    Real.exp (-t * μ) * (1 + 1 / Real.sqrt t) ^ 2 ≤
      (2 * (1 + 1 / μ)) / t := by
  have hμt_pos : 0 < t * μ := by positivity
  have hμt_le_exp : t * μ ≤ Real.exp (t * μ) := by
    exact le_trans (by linarith) (Real.add_one_le_exp (t * μ))
  have hexp_le_inv : Real.exp (-t * μ) ≤ 1 / (t * μ) := by
    have hdiv := one_div_le_one_div_of_le hμt_pos hμt_le_exp
    simpa [one_div, Real.exp_neg, mul_comm] using hdiv
  have ht_mul_exp_le_inv : t * Real.exp (-t * μ) ≤ 1 / μ := by
    have hmul := mul_le_mul_of_nonneg_left hexp_le_inv ht.le
    rwa [show t * (1 / (t * μ)) = 1 / μ by field_simp [ht.ne', hμ.ne']] at hmul
  have hsqrt :
      (1 + 1 / Real.sqrt t) ^ 2 ≤ 2 * (1 + 1 / t) :=
    one_add_inv_sqrt_sq_le_two_mul_one_add_inv t ht
  calc
    Real.exp (-t * μ) * (1 + 1 / Real.sqrt t) ^ 2
      ≤ Real.exp (-t * μ) * (2 * (1 + 1 / t)) := by gcongr
    _ = (2 / t) * (t * Real.exp (-t * μ) + Real.exp (-t * μ)) := by
          field_simp [ht.ne']
    _ ≤ (2 / t) * (1 / μ + 1) := by
          have hexp_le_one : Real.exp (-t * μ) ≤ 1 := by
            apply Real.exp_le_one_iff.mpr
            nlinarith
          gcongr
    _ = (2 * (1 + 1 / μ)) / t := by
          field_simp [ht.ne', hμ.ne']
          ring

/-- Nonuniform rectangular heat-kernel trace bound. -/
theorem asym_heat_kernel_trace_bound
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, 0 < C ∧
      (∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
        Real.exp (-t * asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂))) ≤ C / t := by
  obtain ⟨Ct, hCt_pos, hCt⟩ := heat_kernel_1d_bound Nt a ha t ht
  obtain ⟨Cs, hCs_pos, hCs⟩ := heat_kernel_1d_bound Ns a ha t ht
  refine ⟨Ct * Cs * (2 * (1 + 1 / mass ^ 2)), by positivity, ?_⟩
  rw [asym_heat_kernel_trace_factorization]
  have hμ : 0 < mass ^ 2 := by positivity
  calc
    Real.exp (-t * mass ^ 2) *
        (∑ m₁ : Fin Nt, Real.exp (-t * latticeEigenvalue1d Nt a m₁)) *
        ∑ m₂ : Fin Ns, Real.exp (-t * latticeEigenvalue1d Ns a m₂)
      ≤ Real.exp (-t * mass ^ 2) *
          (Ct * (1 + 1 / Real.sqrt t)) *
          (Cs * (1 + 1 / Real.sqrt t)) := by
            gcongr
            · rw [sum_fin_exp_latticeEigenvalue1d_eq_range Nt a t]
              exact hCt
            · rw [sum_fin_exp_latticeEigenvalue1d_eq_range Ns a t]
              exact hCs
    _ = (Ct * Cs) * (Real.exp (-t * mass ^ 2) * (1 + 1 / Real.sqrt t) ^ 2) := by ring
    _ ≤ (Ct * Cs) * ((2 * (1 + 1 / mass ^ 2)) / t) := by
          gcongr
          exact exp_mul_one_add_inv_sqrt_sq_le_const_div (mass ^ 2) t hμ ht
    _ = (Ct * Cs * (2 * (1 + 1 / mass ^ 2))) / t := by ring

/-- `(Nt*a, Ns*a)`-uniform rectangular heat-kernel trace bound. -/
theorem asym_heat_kernel_trace_bound_uniform
    (Lt Ls : ℝ) (hLt : 0 < Lt) (hLs : 0 < Ls) (mass : ℝ) (_hmass : 0 < mass) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (_ha : 0 < a),
        (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
        ∀ t : ℝ, 0 < t →
          (∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
            Real.exp (-t * asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂))) ≤
            C * (1 + 1 / Real.sqrt t) ^ 2 * Real.exp (-t * mass ^ 2) := by
  obtain ⟨Ct, hCt_pos, hCt⟩ := heat_kernel_1d_bound_uniform Lt hLt
  obtain ⟨Cs, hCs_pos, hCs⟩ := heat_kernel_1d_bound_uniform Ls hLs
  refine ⟨Ct * Cs, by positivity, ?_⟩
  intro Nt Ns hNt hNs a ha hvolt hvols t ht
  rw [asym_heat_kernel_trace_factorization]
  calc
    Real.exp (-t * mass ^ 2) *
        (∑ m₁ : Fin Nt, Real.exp (-t * latticeEigenvalue1d Nt a m₁)) *
        ∑ m₂ : Fin Ns, Real.exp (-t * latticeEigenvalue1d Ns a m₂)
      ≤ Real.exp (-t * mass ^ 2) *
          (Ct * (1 + 1 / Real.sqrt t)) *
          (Cs * (1 + 1 / Real.sqrt t)) := by
            gcongr
            · rw [sum_fin_exp_latticeEigenvalue1d_eq_range Nt a t]
              exact hCt Nt a ha hvolt t ht
            · rw [sum_fin_exp_latticeEigenvalue1d_eq_range Ns a t]
              exact hCs Ns a ha hvols t ht
    _ = (Ct * Cs) * (1 + 1 / Real.sqrt t) ^ 2 * Real.exp (-t * mass ^ 2) := by ring

private lemma asymHeatKernel_diagonal_mass_weighted_eq_eigenvalue_average
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass t : ℝ) (ha : 0 < a) (x : AsymLatticeSites Nt Ns) :
    Real.exp (-t * mass ^ 2) * asymHeatKernelMatrix Nt Ns a t x x =
      (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) *
        ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
          Real.exp (-t * asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂)) := by
  rw [asym_heat_kernel_trace_factorization]
  rw [asymHeatKernel_diagonal_eq_average Nt Ns a ha t x]
  simp [AsymLatticeSites]
  ring

private lemma prefactor_eq_rect_inv_area
    (Lt Ls : ℝ) (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a : ℝ) (ha : 0 < a) (hvolt : (Nt : ℝ) * a = Lt) (hvols : (Ns : ℝ) * a = Ls) :
    (a ^ 2 : ℝ)⁻¹ * (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) = Lt⁻¹ * Ls⁻¹ := by
  have hcard_nat : Fintype.card (AsymLatticeSites Nt Ns) = Nt * Ns := by
    simp [AsymLatticeSites]
  have hcard : (Fintype.card (AsymLatticeSites Nt Ns) : ℝ) = (Nt : ℝ) * (Ns : ℝ) := by
    rw [hcard_nat]
    norm_num
  have harea : a ^ 2 * (Fintype.card (AsymLatticeSites Nt Ns) : ℝ) = Lt * Ls := by
    calc
      a ^ 2 * (Fintype.card (AsymLatticeSites Nt Ns) : ℝ)
        = a ^ 2 * ((Nt : ℝ) * (Ns : ℝ)) := by rw [hcard]
      _ = ((Nt : ℝ) * a) * ((Ns : ℝ) * a) := by ring
      _ = Lt * Ls := by rw [hvolt, hvols]
  have ha2_ne : (a ^ 2 : ℝ) ≠ 0 := by positivity
  have hcard_ne : ((Fintype.card (AsymLatticeSites Nt Ns) : ℝ)) ≠ 0 := by
    rw [hcard]
    exact mul_ne_zero
      (Nat.cast_ne_zero.mpr (NeZero.ne Nt))
      (Nat.cast_ne_zero.mpr (NeZero.ne Ns))
  calc
    (a ^ 2 : ℝ)⁻¹ * (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ)
      = 1 / (a ^ 2 * (Fintype.card (AsymLatticeSites Nt Ns) : ℝ)) := by
          field_simp [ha2_ne, hcard_ne]
    _ = 1 / (Lt * Ls) := by rw [harea]
    _ = Lt⁻¹ * Ls⁻¹ := by
          rw [one_div, mul_inv_rev]
          ring

private lemma asymCanonicalSmoothWeight_eq_integral_Ioi
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (_ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (m₁ : Fin Nt) (m₂ : Fin Ns) :
    asymCanonicalSmoothWeight Nt Ns a mass T (m₁, m₂) =
      ∫ t in Set.Ioi T,
        Real.exp (-t * asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂)) := by
  unfold asymCanonicalSmoothWeight
  rw [schwinger_smooth_Ioi (asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂))
    (by
      unfold asymCanonicalEigenvalue
      have h1 := latticeEigenvalue1d_nonneg Nt a m₁
      have h2 := latticeEigenvalue1d_nonneg Ns a m₂
      nlinarith [sq_pos_of_pos hmass]) T]

private lemma integrableOn_inv_Ioc (T : ℝ) (hT : 0 < T) :
    IntegrableOn (fun s : ℝ => 1 / s) (Set.Ioc T 1) := by
  refine MeasureTheory.Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne ?_ (M := 1 / T) ?_
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hspos : 0 < s := lt_trans hT hs.1
    have hle : 1 / s ≤ 1 / T := by
      gcongr
      exact hs.1.le
    have hnonneg : 0 ≤ (1 / s : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hle

private lemma integrableOn_inv_mul_exp_Ioi (μ T : ℝ) (hμ : 0 < μ) (hT : 0 < T) :
    IntegrableOn (fun s : ℝ => (1 / s) * Real.exp (-s * μ)) (Set.Ioi T) := by
  let g : ℝ → ℝ := fun s => (1 / T) * Real.exp (-s * μ)
  have hg_int : IntegrableOn g (Set.Ioi T) := by
    have hbase := integrableOn_exp_mul_Ioi (a := (-μ : ℝ)) (by linarith) T
    simpa [g, mul_comm, mul_left_comm, mul_assoc] using hbase.const_mul (1 / T)
  have hg_sm :
      AEStronglyMeasurable
        (fun s : ℝ => (1 / s) * Real.exp (-s * μ))
        (volume.restrict (Set.Ioi T)) := by
    fun_prop
  refine MeasureTheory.Integrable.mono' hg_int hg_sm ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hspos : 0 < s := lt_trans hT hs
  have hle : s⁻¹ ≤ T⁻¹ := by
    have : 1 / s ≤ 1 / T := by
      gcongr
      exact hs.le
    simpa [one_div] using this
  have hexp : 0 ≤ Real.exp (-(s * μ)) := (Real.exp_pos _).le
  have hnonneg : 0 ≤ (1 / s : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnonneg (by simpa [neg_mul] using hexp))]
  simp only [g, one_div, neg_mul, ge_iff_le]
  exact mul_le_mul_of_nonneg_right hle hexp

/-- Polylogarithmic smooth Wick-constant bound on the rectangular lattice. -/
theorem asymSmoothWickConstant_le_log_uniform
    (mass Lt Ls : ℝ) (hLt : 0 < Lt) (hLs : 0 < Ls) (hmass : 0 < mass) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (_ha : 0 < a),
        (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
        ∀ T : ℝ, 0 < T →
          asymSmoothWickConstant Nt Ns a mass T ≤ A + B * (1 + |Real.log T|) := by
  obtain ⟨C, hC_pos, hC⟩ :=
    asym_heat_kernel_trace_bound_uniform Lt Ls hLt hLs mass hmass
  refine ⟨2 * (Lt⁻¹ * Ls⁻¹) * C * (2 / mass ^ 2 + 1), 2 * (Lt⁻¹ * Ls⁻¹) * C, ?_, ?_, ?_⟩
  · positivity
  · positivity
  intro Nt Ns hNt hNs a ha hvolt hvols T hT
  have hmass_sq_pos : 0 < mass ^ 2 := sq_pos_of_pos hmass
  have hlam_pos : ∀ (m₁ : Fin Nt) (m₂ : Fin Ns),
      0 < asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂) := by
    intro m₁ m₂
    unfold asymCanonicalEigenvalue
    have h1 := latticeEigenvalue1d_nonneg Nt a m₁
    have h2 := latticeEigenvalue1d_nonneg Ns a m₂
    nlinarith [sq_pos_of_pos hmass]
  have hsummand_int : ∀ (m₁ : Fin Nt) (m₂ : Fin Ns),
      IntegrableOn
        (fun s : ℝ => Real.exp (-s * asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂)))
        (Set.Ioi T) := by
    intro m₁ m₂
    have hbase := integrableOn_exp_mul_Ioi
      (a := (-(asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂)) : ℝ))
      (by have := hlam_pos m₁ m₂; linarith) T
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbase
  have hinner_int : ∀ (m₁ : Fin Nt),
      IntegrableOn
        (fun s : ℝ =>
          ∑ m₂ : Fin Ns, Real.exp (-s * asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂)))
        (Set.Ioi T) := fun m₁ =>
    MeasureTheory.integrable_finset_sum Finset.univ (fun m₂ _ => hsummand_int m₁ m₂)
  have hsum_int :
      IntegrableOn
        (fun s : ℝ =>
          ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
            Real.exp (-s * asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂)))
        (Set.Ioi T) :=
    MeasureTheory.integrable_finset_sum Finset.univ (fun m₁ _ => hinner_int m₁)
  have hswap :
      ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
          (∫ s in Set.Ioi T,
            Real.exp (-s * asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂)))
        = ∫ s in Set.Ioi T,
            ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
              Real.exp (-s * asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂)) := by
    rw [MeasureTheory.integral_finset_sum Finset.univ (fun m₁ _ => hinner_int m₁)]
    refine Finset.sum_congr rfl ?_
    intro m₁ _
    rw [MeasureTheory.integral_finset_sum Finset.univ (fun m₂ _ => hsummand_int m₁ m₂)]
  have hsmooth_repr :
      asymSmoothWickConstant Nt Ns a mass T
        = (Lt⁻¹ * Ls⁻¹) *
            ∫ s in Set.Ioi T,
              ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
                Real.exp (-s * asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂)) := by
    unfold asymSmoothWickConstant
    have hsum_eq :
        (∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
            asymCanonicalSmoothWeight Nt Ns a mass T (m₁, m₂))
          = ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
              ∫ s in Set.Ioi T,
                Real.exp (-s * asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂)) := by
      refine Finset.sum_congr rfl ?_
      intro m₁ _
      refine Finset.sum_congr rfl ?_
      intro m₂ _
      exact asymCanonicalSmoothWeight_eq_integral_Ioi Nt Ns a mass ha hmass T m₁ m₂
    rw [hsum_eq, hswap, ← mul_assoc,
      prefactor_eq_rect_inv_area Lt Ls Nt Ns a ha hvolt hvols]
  have hexp_int :
      IntegrableOn (fun s : ℝ => Real.exp (-s * mass ^ 2)) (Set.Ioi T) := by
    have hbase := integrableOn_exp_mul_Ioi (a := (-mass ^ 2 : ℝ)) (by linarith) T
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbase
  have hinvexp_int :
      IntegrableOn (fun s : ℝ => (1 / s) * Real.exp (-s * mass ^ 2)) (Set.Ioi T) :=
    integrableOn_inv_mul_exp_Ioi (mass ^ 2) T hmass_sq_pos hT
  have hmajorant_int :
      IntegrableOn
        (fun s : ℝ => 2 * C * (1 + 1 / s) * Real.exp (-s * mass ^ 2)) (Set.Ioi T) := by
    have hadd :
        IntegrableOn
          (fun s : ℝ => Real.exp (-s * mass ^ 2) + (1 / s) * Real.exp (-s * mass ^ 2))
          (Set.Ioi T) := hexp_int.add hinvexp_int
    have hscaled := hadd.const_mul (2 * C)
    refine MeasureTheory.IntegrableOn.congr_fun hscaled ?_ measurableSet_Ioi
    intro s hs
    ring
  have htrace_le :
      (∫ s in Set.Ioi T,
        ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
          Real.exp (-s * asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂)))
        ≤ ∫ s in Set.Ioi T, 2 * C * (1 + 1 / s) * Real.exp (-s * mass ^ 2) := by
    apply MeasureTheory.setIntegral_mono_on hsum_int hmajorant_int measurableSet_Ioi
    intro s hs
    have hspos : 0 < s := lt_trans hT hs
    have hsqrt : (1 + 1 / Real.sqrt s) ^ 2 ≤ 2 * (1 + 1 / s) :=
      one_add_inv_sqrt_sq_le_two_mul_one_add_inv s hspos
    calc
      ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
          Real.exp (-s * asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂))
        ≤ C * (1 + 1 / Real.sqrt s) ^ 2 * Real.exp (-s * mass ^ 2) :=
          hC Nt Ns a ha hvolt hvols s hspos
      _ ≤ C * (2 * (1 + 1 / s)) * Real.exp (-s * mass ^ 2) := by gcongr
      _ = 2 * C * (1 + 1 / s) * Real.exp (-s * mass ^ 2) := by ring
  have hexp_le :
      ∫ s in Set.Ioi T, Real.exp (-s * mass ^ 2) ≤ 1 / mass ^ 2 := by
    have hexp_eq :
        ∫ s in Set.Ioi T, Real.exp (-s * mass ^ 2) =
          Real.exp (-T * mass ^ 2) / mass ^ 2 :=
      (schwinger_smooth_Ioi (mass ^ 2) hmass_sq_pos T).symm
    rw [hexp_eq]
    have hle_one : Real.exp (-T * mass ^ 2) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith
    exact div_le_div_of_nonneg_right hle_one hmass_sq_pos.le
  have hinvexp_le :
      ∫ s in Set.Ioi T, (1 / s) * Real.exp (-s * mass ^ 2)
        ≤ |Real.log T| + 1 / mass ^ 2 := by
    by_cases hT1 : T ≤ 1
    · have hsplit : Set.Ioi T = Set.Ioc T 1 ∪ Set.Ioi 1 := by
        ext s; simp [hT1]
      have hleft_int :
          IntegrableOn (fun s : ℝ => (1 / s) * Real.exp (-s * mass ^ 2)) (Set.Ioc T 1) :=
        hinvexp_int.mono_set (fun s hs => hs.1)
      have hright_int :
          IntegrableOn (fun s : ℝ => (1 / s) * Real.exp (-s * mass ^ 2)) (Set.Ioi 1) :=
        hinvexp_int.mono_set (fun s hs => hT1.trans_lt hs)
      rw [hsplit, MeasureTheory.setIntegral_union
        (show Disjoint (Set.Ioc T 1) (Set.Ioi 1) by
          refine Set.disjoint_left.mpr ?_
          intro s hs1 hs2
          exact not_lt_of_ge hs1.2 hs2)
        measurableSet_Ioi hleft_int hright_int]
      have hleft_le :
          ∫ s in Set.Ioc T 1, (1 / s) * Real.exp (-s * mass ^ 2) ≤ |Real.log T| := by
        calc
          ∫ s in Set.Ioc T 1, (1 / s) * Real.exp (-s * mass ^ 2)
            ≤ ∫ s in Set.Ioc T 1, (1 / s : ℝ) := by
                apply MeasureTheory.setIntegral_mono_on hleft_int
                  (integrableOn_inv_Ioc T hT) measurableSet_Ioc
                intro s hs
                have hspos : 0 < s := lt_trans hT hs.1
                have hexp_le_one : Real.exp (-s * mass ^ 2) ≤ 1 := by
                  apply Real.exp_le_one_iff.mpr
                  nlinarith [sq_nonneg mass]
                have hnonneg : 0 ≤ (1 / s : ℝ) := by positivity
                simpa using mul_le_mul_of_nonneg_left hexp_le_one hnonneg
          _ = ∫ s in T..1, (1 / s : ℝ) := by
                rw [intervalIntegral.integral_of_le hT1]
          _ = Real.log (1 / T) := by
                simpa using integral_one_div_of_pos hT (by norm_num : (0 : ℝ) < 1)
          _ = |Real.log T| := by
                have hlog : Real.log T ≤ 0 := Real.log_nonpos hT.le hT1
                have hlog_inv : Real.log (1 / T) = -Real.log T := by
                  rw [one_div]; simp [Real.log_inv]
                rw [hlog_inv, abs_of_nonpos hlog]
      have hright_le :
          ∫ s in Set.Ioi 1, (1 / s) * Real.exp (-s * mass ^ 2) ≤ 1 / mass ^ 2 := by
        calc
          ∫ s in Set.Ioi 1, (1 / s) * Real.exp (-s * mass ^ 2)
            ≤ ∫ s in Set.Ioi 1, Real.exp (-s * mass ^ 2) := by
                apply MeasureTheory.setIntegral_mono_on hright_int
                  (hexp_int.mono_set (fun s hs => hT1.trans_lt hs)) measurableSet_Ioi
                intro s hs
                have hsone : 1 < s := hs
                have hle : 1 / s ≤ (1 : ℝ) := by
                  have hspos : 0 < s := by linarith
                  rw [div_le_iff₀ hspos]; linarith
                have hnonneg : 0 ≤ Real.exp (-s * mass ^ 2) := (Real.exp_pos _).le
                simpa using mul_le_mul_of_nonneg_right hle hnonneg
          _ = Real.exp (-(mass ^ 2)) / mass ^ 2 := by
                simpa [one_mul] using
                  (schwinger_smooth_Ioi (mass ^ 2) hmass_sq_pos 1).symm
          _ ≤ 1 / mass ^ 2 := by
                have hle_one : Real.exp (-(mass ^ 2)) ≤ 1 := by
                  apply Real.exp_le_one_iff.mpr
                  nlinarith [sq_nonneg mass]
                exact div_le_div_of_nonneg_right hle_one hmass_sq_pos.le
      exact add_le_add hleft_le hright_le
    · have hT1 : 1 < T := lt_of_not_ge hT1
      calc
        ∫ s in Set.Ioi T, (1 / s) * Real.exp (-s * mass ^ 2)
          ≤ ∫ s in Set.Ioi T, Real.exp (-s * mass ^ 2) := by
              apply MeasureTheory.setIntegral_mono_on hinvexp_int hexp_int measurableSet_Ioi
              intro s hs
              have hsT : T < s := hs
              have hsone : 1 < s := lt_trans hT1 hsT
              have hle : 1 / s ≤ (1 : ℝ) := by
                have hspos : 0 < s := by linarith
                rw [div_le_iff₀ hspos]; linarith
              have hnonneg : 0 ≤ Real.exp (-s * mass ^ 2) := (Real.exp_pos _).le
              simpa using mul_le_mul_of_nonneg_right hle hnonneg
        _ ≤ 1 / mass ^ 2 := hexp_le
        _ ≤ |Real.log T| + 1 / mass ^ 2 := by
              nlinarith [abs_nonneg (Real.log T)]
  have hmajorant_eval :
      ∫ s in Set.Ioi T, 2 * C * (1 + 1 / s) * Real.exp (-s * mass ^ 2)
        ≤ 2 * C * (1 / mass ^ 2) + 2 * C * (|Real.log T| + 1 / mass ^ 2) := by
    have hsplit :
        ∫ s in Set.Ioi T, 2 * C * (Real.exp (-s * mass ^ 2) +
            (1 / s) * Real.exp (-s * mass ^ 2))
          =
        (2 * C) * (∫ s in Set.Ioi T, Real.exp (-s * mass ^ 2)) +
          (2 * C) * (∫ s in Set.Ioi T, (1 / s) * Real.exp (-s * mass ^ 2)) := by
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_add hexp_int hinvexp_int]
      ring
    calc
      ∫ s in Set.Ioi T, 2 * C * (1 + 1 / s) * Real.exp (-s * mass ^ 2)
        = ∫ s in Set.Ioi T, 2 * C * (Real.exp (-s * mass ^ 2) +
            (1 / s) * Real.exp (-s * mass ^ 2)) := by
              apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
              intro s hs
              ring
      _ = (2 * C) * (∫ s in Set.Ioi T, Real.exp (-s * mass ^ 2)) +
            (2 * C) * (∫ s in Set.Ioi T, (1 / s) * Real.exp (-s * mass ^ 2)) := hsplit
      _ ≤ (2 * C) * (1 / mass ^ 2) + (2 * C) * (|Real.log T| + 1 / mass ^ 2) := by
            gcongr
  calc
    asymSmoothWickConstant Nt Ns a mass T
      = (Lt⁻¹ * Ls⁻¹) *
          ∫ s in Set.Ioi T,
            ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
              Real.exp (-s * asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂)) := hsmooth_repr
    _ ≤ (Lt⁻¹ * Ls⁻¹) *
          ∫ s in Set.Ioi T, 2 * C * (1 + 1 / s) * Real.exp (-s * mass ^ 2) :=
            mul_le_mul_of_nonneg_left htrace_le (by positivity)
    _ ≤ (Lt⁻¹ * Ls⁻¹) *
          (2 * C * (1 / mass ^ 2) + 2 * C * (|Real.log T| + 1 / mass ^ 2)) := by
            gcongr
    _ = 2 * (Lt⁻¹ * Ls⁻¹) * C * (2 / mass ^ 2 + |Real.log T|) := by ring
    _ ≤ 2 * (Lt⁻¹ * Ls⁻¹) * C * (2 / mass ^ 2 + 1) +
          (2 * (Lt⁻¹ * Ls⁻¹) * C) * (1 + |Real.log T|) := by
            have hB_nonneg : 0 ≤ 2 * (Lt⁻¹ * Ls⁻¹) * C := by positivity
            nlinarith [abs_nonneg (Real.log T), hB_nonneg]

end Pphi2
