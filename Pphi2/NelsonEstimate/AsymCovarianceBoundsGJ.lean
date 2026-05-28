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

/-- The asym rectangular dispersion has a strictly positive mass gap. -/
private lemma asymCanonicalEigenvalue_pos
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (_ha : 0 < a) (hmass : 0 < mass)
    (m : AsymCanonicalMode Nt Ns) :
    0 < asymCanonicalEigenvalue Nt Ns a mass m := by
  unfold asymCanonicalEigenvalue
  have h1 := latticeEigenvalue1d_nonneg Nt a m.1
  have h2 := latticeEigenvalue1d_nonneg Ns a m.2
  nlinarith [sq_pos_of_pos hmass]

/-- Rough covariance eigenvalue bound `(1 - e^{-T λ}) / λ ≤ T`. -/
private lemma asymCanonicalRoughWeight_le_T
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (_hT : 0 ≤ T) (m : AsymCanonicalMode Nt Ns)
    (ha : 0 < a) (hmass : 0 < mass) :
    asymCanonicalRoughWeight Nt Ns a mass T m ≤ T := by
  unfold asymCanonicalRoughWeight
  have hev := asymCanonicalEigenvalue_pos Nt Ns a mass ha hmass m
  rw [div_le_iff₀ hev]
  have h := Real.add_one_le_exp (-(T * asymCanonicalEigenvalue Nt Ns a mass m))
  have hexp :
      Real.exp (-(T * asymCanonicalEigenvalue Nt Ns a mass m)) =
        Real.exp (-T * asymCanonicalEigenvalue Nt Ns a mass m) := by
    ring_nf
  rw [hexp] at h
  linarith

/-- Rough covariance eigenvalue bound `(1 - e^{-T λ}) / λ ≤ λ⁻¹`. -/
private lemma asymCanonicalRoughWeight_le_inv
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (m : AsymCanonicalMode Nt Ns)
    (ha : 0 < a) (hmass : 0 < mass) :
    asymCanonicalRoughWeight Nt Ns a mass T m ≤
      (asymCanonicalEigenvalue Nt Ns a mass m)⁻¹ := by
  unfold asymCanonicalRoughWeight
  have hev := asymCanonicalEigenvalue_pos Nt Ns a mass ha hmass m
  rw [inv_eq_one_div]
  apply div_le_div_of_nonneg_right ?_ hev.le
  linarith [Real.exp_nonneg (-T * asymCanonicalEigenvalue Nt Ns a mass m)]

/-- Schwinger representation of the asym rough covariance eigenvalue. -/
private lemma asymCanonicalRoughWeight_eq_integral_Icc
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T) (m : AsymCanonicalMode Nt Ns) :
    asymCanonicalRoughWeight Nt Ns a mass T m =
      ∫ t in Set.Icc 0 T,
        Real.exp (-t * asymCanonicalEigenvalue Nt Ns a mass m) := by
  simpa [asymCanonicalRoughWeight] using
    (schwinger_rough (asymCanonicalEigenvalue Nt Ns a mass m)
      (asymCanonicalEigenvalue_pos Nt Ns a mass ha hmass m) T hT.le)

/-- The asym rough covariance is a Schwinger integral of the spatial heat kernel. -/
private lemma asymCanonicalRoughCovariance_eq_integral_Icc_heatKernel
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T)
    (x y : AsymLatticeSites Nt Ns) :
    asymCanonicalRoughCovariance Nt Ns a mass T x y =
      (a ^ 2 : ℝ)⁻¹ *
        ∫ t in Set.Icc 0 T,
          Real.exp (-t * mass ^ 2) *
            asymHeatKernelMatrix Nt Ns a t x y := by
  have h_int_coeff :
      ∀ m₁ : Fin Nt, ∀ m₂ : Fin Ns,
        IntegrableOn
          (fun t : ℝ =>
            (Real.exp (-t * mass ^ 2) *
              Real.exp (-t * (latticeEigenvalue1d Nt a m₁ + latticeEigenvalue1d Ns a m₂))) *
              (asymCanonicalBasis Nt Ns (m₁, m₂) x *
                asymCanonicalBasis Nt Ns (m₁, m₂) y /
                asymCanonicalNormSq Nt Ns (m₁, m₂)))
          (Set.Icc 0 T) := by
    intro m₁ m₂
    have hcont : Continuous (fun t : ℝ =>
      (Real.exp (-t * mass ^ 2) *
        Real.exp (-t * (latticeEigenvalue1d Nt a m₁ + latticeEigenvalue1d Ns a m₂))) *
        (asymCanonicalBasis Nt Ns (m₁, m₂) x *
          asymCanonicalBasis Nt Ns (m₁, m₂) y /
          asymCanonicalNormSq Nt Ns (m₁, m₂))) := by
      fun_prop
    exact hcont.integrableOn_Icc
  unfold asymCanonicalRoughCovariance
  calc
    (a ^ 2 : ℝ)⁻¹ *
        ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
          asymCanonicalRoughWeight Nt Ns a mass T (m₁, m₂) *
            asymCanonicalBasis Nt Ns (m₁, m₂) x *
            asymCanonicalBasis Nt Ns (m₁, m₂) y /
            asymCanonicalNormSq Nt Ns (m₁, m₂)
      = (a ^ 2 : ℝ)⁻¹ *
          ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
            ∫ t in Set.Icc 0 T,
              (Real.exp (-t * mass ^ 2) *
                Real.exp (-t * (latticeEigenvalue1d Nt a m₁ + latticeEigenvalue1d Ns a m₂))) *
                (asymCanonicalBasis Nt Ns (m₁, m₂) x *
                  asymCanonicalBasis Nt Ns (m₁, m₂) y /
                  asymCanonicalNormSq Nt Ns (m₁, m₂)) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro m₁ hm₁
            refine Finset.sum_congr rfl ?_
            intro m₂ hm₂
            calc
              asymCanonicalRoughWeight Nt Ns a mass T (m₁, m₂) *
                  asymCanonicalBasis Nt Ns (m₁, m₂) x *
                  asymCanonicalBasis Nt Ns (m₁, m₂) y /
                  asymCanonicalNormSq Nt Ns (m₁, m₂)
                = (asymCanonicalBasis Nt Ns (m₁, m₂) x *
                    asymCanonicalBasis Nt Ns (m₁, m₂) y /
                    asymCanonicalNormSq Nt Ns (m₁, m₂)) *
                    asymCanonicalRoughWeight Nt Ns a mass T (m₁, m₂) := by ring
              _ = (asymCanonicalBasis Nt Ns (m₁, m₂) x *
                    asymCanonicalBasis Nt Ns (m₁, m₂) y /
                    asymCanonicalNormSq Nt Ns (m₁, m₂)) *
                    ∫ t in Set.Icc 0 T,
                      Real.exp (-t * asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂)) := by
                        rw [asymCanonicalRoughWeight_eq_integral_Icc Nt Ns a mass ha hmass T hT
                          (m₁, m₂)]
              _ = ∫ t in Set.Icc 0 T,
                    (asymCanonicalBasis Nt Ns (m₁, m₂) x *
                      asymCanonicalBasis Nt Ns (m₁, m₂) y /
                      asymCanonicalNormSq Nt Ns (m₁, m₂)) *
                      Real.exp (-t * asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂)) := by
                        rw [integral_const_mul]
              _ = ∫ t in Set.Icc 0 T,
                    (Real.exp (-t * mass ^ 2) *
                      Real.exp (-t * (latticeEigenvalue1d Nt a m₁ +
                        latticeEigenvalue1d Ns a m₂))) *
                      (asymCanonicalBasis Nt Ns (m₁, m₂) x *
                        asymCanonicalBasis Nt Ns (m₁, m₂) y /
                        asymCanonicalNormSq Nt Ns (m₁, m₂)) := by
                        apply integral_congr_ae
                        filter_upwards with t
                        rw [show -t * asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂) =
                            -t * mass ^ 2 +
                              (-t * (latticeEigenvalue1d Nt a m₁ +
                                latticeEigenvalue1d Ns a m₂)) by
                              simp [asymCanonicalEigenvalue]; ring]
                        rw [Real.exp_add]
                        ring
    _ = (a ^ 2 : ℝ)⁻¹ *
          ∫ t in Set.Icc 0 T,
            ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
              (Real.exp (-t * mass ^ 2) *
                Real.exp (-t * (latticeEigenvalue1d Nt a m₁ + latticeEigenvalue1d Ns a m₂))) *
                (asymCanonicalBasis Nt Ns (m₁, m₂) x *
                  asymCanonicalBasis Nt Ns (m₁, m₂) y /
                  asymCanonicalNormSq Nt Ns (m₁, m₂)) := by
              congr 1
              symm
              rw [MeasureTheory.integral_finset_sum Finset.univ]
              · refine Finset.sum_congr rfl ?_
                intro m₁ hm₁
                rw [MeasureTheory.integral_finset_sum Finset.univ]
                intro m₂ hm₂
                exact h_int_coeff m₁ m₂
              · intro m₁ hm₁
                exact MeasureTheory.integrable_finset_sum Finset.univ
                  (fun m₂ _ => h_int_coeff m₁ m₂)
    _ = (a ^ 2 : ℝ)⁻¹ *
          ∫ t in Set.Icc 0 T,
            Real.exp (-t * mass ^ 2) *
              ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
                Real.exp (-t * (latticeEigenvalue1d Nt a m₁ + latticeEigenvalue1d Ns a m₂)) *
                  (asymCanonicalBasis Nt Ns (m₁, m₂) x *
                    asymCanonicalBasis Nt Ns (m₁, m₂) y /
                    asymCanonicalNormSq Nt Ns (m₁, m₂)) := by
              congr 1
              apply integral_congr_ae
              filter_upwards with t
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro m₁ hm₁
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro m₂ hm₂
              ring
    _ = (a ^ 2 : ℝ)⁻¹ *
          ∫ t in Set.Icc 0 T,
            Real.exp (-t * mass ^ 2) * asymHeatKernelMatrix Nt Ns a t x y := by
              congr 1
              apply integral_congr_ae
              filter_upwards with t
              rw [asymHeatKernel_entry_eq_eigenvalue_average Nt Ns a (ne_of_gt ha) t x y]
              congr 1
              refine Finset.sum_congr rfl ?_
              intro m₁ hm₁
              refine Finset.sum_congr rfl ?_
              intro m₂ hm₂
              ring

/-- The asym canonical rough covariance is entrywise nonnegative. -/
private lemma asymCanonicalRoughCovariance_nonneg
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (ha : 0 < a) (hmass : 0 < mass) (hT : 0 < T)
    (x y : AsymLatticeSites Nt Ns) :
    0 ≤ asymCanonicalRoughCovariance Nt Ns a mass T x y := by
  rw [asymCanonicalRoughCovariance_eq_integral_Icc_heatKernel Nt Ns a mass ha hmass T hT x y]
  apply mul_nonneg
  · positivity
  · refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t htIcc
    exact mul_nonneg (by positivity)
      (asymHeatKernel_nonneg Nt Ns a ha t htIcc.1 x y)

/-- Diagonal asym heat-kernel bound from the rectangular trace bound. -/
private lemma asymHeatKernel_diagonal_mass_weighted_le_uniform
    (mass Lt Ls : ℝ) (hLt : 0 < Lt) (hLs : 0 < Ls) (hmass : 0 < mass) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (_ha : 0 < a),
        (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
        ∀ (u : ℝ), 0 < u → ∀ (x : AsymLatticeSites Nt Ns),
          Real.exp (-u * mass ^ 2) * asymHeatKernelMatrix Nt Ns a u x x ≤
            (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) *
              (C * (1 + 1 / Real.sqrt u) ^ 2 * Real.exp (-u * mass ^ 2)) := by
  obtain ⟨C, hC_pos, hC⟩ :=
    asym_heat_kernel_trace_bound_uniform Lt Ls hLt hLs mass hmass
  refine ⟨C, hC_pos, ?_⟩
  intro Nt Ns hNt hNs a ha hvolt hvols u hu x
  calc
    Real.exp (-u * mass ^ 2) * asymHeatKernelMatrix Nt Ns a u x x
      = (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) *
          ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
            Real.exp (-u * asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂)) := by
              simpa using
                (asymHeatKernel_diagonal_mass_weighted_eq_eigenvalue_average
                  Nt Ns a mass u ha x)
    _ ≤ (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) *
          (C * (1 + 1 / Real.sqrt u) ^ 2 * Real.exp (-u * mass ^ 2)) := by
            gcongr
            exact hC Nt Ns a ha hvolt hvols u hu

private lemma integral_one_div_sqrt_eq_two :
    (∫ u in (0 : ℝ)..1, (1 : ℝ) / Real.sqrt u) = 2 := by
  calc
    (∫ u in (0 : ℝ)..1, (1 : ℝ) / Real.sqrt u)
      = ∫ u in (0 : ℝ)..1, u ^ ((-1 : ℝ) / 2) := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards with u hu
          have hu0 : 0 < u := by
            simpa using hu.1
          have hpow : (u ^ ((1 : ℝ) / 2))⁻¹ = u ^ (-((1 : ℝ) / 2)) := by
            simpa using (Real.rpow_neg (le_of_lt hu0) ((1 : ℝ) / 2)).symm
          have hneg : -((1 : ℝ) / 2) = ((-1 : ℝ) / 2) := by
            ring
          rw [show (1 / Real.sqrt u : ℝ) = (u ^ ((1 : ℝ) / 2))⁻¹ by
            simp [one_div, Real.sqrt_eq_rpow], hpow, hneg]
    _ = 2 := by
          rw [integral_rpow]
          · norm_num
          · left
            norm_num

private lemma unitSquare_inv_add_integral_eq_two_log_two :
    (∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, (1 : ℝ) / (u + v)) =
      2 * Real.log 2 := by
  have hinner : ∀ u ∈ Set.Ioc (0 : ℝ) 1,
      (∫ v in (0 : ℝ)..1, (1 : ℝ) / (u + v)) = Real.log (u + 1) - Real.log u := by
    intro u hu
    have hshift := intervalIntegral.integral_comp_add_left
      (f := fun x : ℝ => (1 : ℝ) / x) (a := (0 : ℝ)) (b := 1) u
    have hshift' :
        (∫ v in (0 : ℝ)..1, (1 : ℝ) / (u + v)) = ∫ x in u..u + 1, (1 : ℝ) / x := by
      convert hshift using 1
      simp
    rw [hshift']
    have hu1 : 0 < u + 1 := by
      nlinarith [hu.1]
    rw [integral_one_div_of_pos hu.1 hu1]
    have hu_ne : u + 1 ≠ 0 := ne_of_gt hu1
    rw [Real.log_div hu_ne hu.1.ne']
  have hlogshift_int :
      IntervalIntegrable (fun u : ℝ => Real.log (u + 1)) MeasureSpace.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    have hcont : ContinuousOn (fun u : ℝ => u + 1) (Set.uIcc (0 : ℝ) 1) := by
      fun_prop
    refine Real.continuousOn_log.comp hcont ?_
    intro u hu
    have hu0 : 0 ≤ u := by
      simpa using hu.1
    have : 0 < u + 1 := by
      nlinarith
    exact ne_of_gt this
  have hshiftlog :
      (∫ u in (0 : ℝ)..1, Real.log (u + 1)) = ∫ x in (1 : ℝ)..2, Real.log x := by
    convert
      (intervalIntegral.integral_comp_add_left (f := Real.log) (a := (0 : ℝ)) (b := 1) 1) using 1
    · ring_nf
    · ring_nf
  calc
    (∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, (1 : ℝ) / (u + v))
      = ∫ u in (0 : ℝ)..1, (Real.log (u + 1) - Real.log u) := by
          apply intervalIntegral.integral_congr_ae'
          · filter_upwards with u hu
            exact hinner u hu
          · simp
    _ = (∫ u in (0 : ℝ)..1, Real.log (u + 1)) - ∫ u in (0 : ℝ)..1, Real.log u := by
          rw [intervalIntegral.integral_sub hlogshift_int intervalIntegral.intervalIntegrable_log']
    _ = (∫ x in (1 : ℝ)..2, Real.log x) - ∫ u in (0 : ℝ)..1, Real.log u := by
          rw [hshiftlog]
    _ = 2 * Real.log 2 := by
          rw [integral_log, integral_log_from_zero]
          ring_nf
          simp

private lemma unitSquare_inv_add_integral_le_two :
    (∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, (1 : ℝ) / (u + v)) ≤ 2 := by
  rw [unitSquare_inv_add_integral_eq_two_log_two]
  have hlog2_le_one : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  nlinarith

private lemma squareIntegral_inv_add_scale (T : ℝ) (hT : 0 < T) :
    (∫ s in (0 : ℝ)..T, ∫ t in (0 : ℝ)..T, (1 : ℝ) / (s + t)) =
      T * ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, (1 : ℝ) / (u + v) := by
  have hinner_scale : ∀ u : ℝ,
      (∫ t in (0 : ℝ)..T, (1 : ℝ) / (T * u + t)) =
        ∫ v in (0 : ℝ)..1, (1 : ℝ) / (u + v) := by
    intro u
    have h := intervalIntegral.smul_integral_comp_mul_left
      (f := fun x : ℝ => (1 : ℝ) / (T * u + x)) (a := (0 : ℝ)) (b := 1) T
    rw [smul_eq_mul] at h
    have hscale :
        (∫ t in (0 : ℝ)..T, (1 : ℝ) / (T * u + t)) =
          T * ∫ v in (0 : ℝ)..1, (1 : ℝ) / (T * u + T * v) := by
      convert h.symm using 1
      simp [add_comm]
    calc
      (∫ t in (0 : ℝ)..T, (1 : ℝ) / (T * u + t))
        = T * ∫ v in (0 : ℝ)..1, (1 : ℝ) / (T * u + T * v) := by
            rw [hscale]
      _ = ∫ v in (0 : ℝ)..1, (1 : ℝ) / (u + v) := by
            rw [← intervalIntegral.integral_const_mul]
            apply intervalIntegral.integral_congr_ae
            filter_upwards with v hv
            have hTv : T * (T * u + T * v)⁻¹ = (u + v)⁻¹ := by
              field_simp [hT.ne']
            simpa [one_div] using hTv
  have houter := intervalIntegral.smul_integral_comp_mul_left
    (f := fun x : ℝ => ∫ t in (0 : ℝ)..T, (1 : ℝ) / (x + t)) (a := (0 : ℝ)) (b := 1) T
  rw [smul_eq_mul] at houter
  calc
    (∫ s in (0 : ℝ)..T, ∫ t in (0 : ℝ)..T, (1 : ℝ) / (s + t))
      = T * ∫ u in (0 : ℝ)..1, (∫ t in (0 : ℝ)..T, (1 : ℝ) / (T * u + t)) := by
          simpa [hT.le, add_comm] using houter.symm
    _ = T * ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, (1 : ℝ) / (u + v) := by
          congr 1
          apply intervalIntegral.integral_congr_ae
          filter_upwards with u hu
          exact hinner_scale u

private lemma squareIntegral_inv_add_le_two_mul
    (T : ℝ) (hT : 0 < T) :
    (∫ s in (0 : ℝ)..T, ∫ t in (0 : ℝ)..T, (1 : ℝ) / (s + t)) ≤ 2 * T := by
  rw [squareIntegral_inv_add_scale T hT]
  calc
    T * ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, (1 : ℝ) / (u + v)
      ≤ T * 2 := by
          gcongr
          exact unitSquare_inv_add_integral_le_two
    _ = 2 * T := by ring

private lemma squareIntegral_exp_neg_le_div
    (μ T : ℝ) (hμ : 0 < μ) (hT : 0 < T) :
    (∫ s in (0 : ℝ)..T, ∫ t in (0 : ℝ)..T, Real.exp (-(s + t) * μ)) ≤ T / μ := by
  set A : ℝ := ∫ t in (0 : ℝ)..T, Real.exp (-t * μ)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact intervalIntegral.integral_nonneg hT.le (fun t ht => by positivity)
  have hA_le_inv : A ≤ 1 / μ := by
    dsimp [A]
    rw [← schwinger_rough_interval μ hμ T hT.le]
    apply div_le_div_of_nonneg_right
    · have hexp_nonneg : 0 ≤ Real.exp (-T * μ) := by positivity
      linarith
    · exact hμ.le
  have hA_le_T : A ≤ T := by
    dsimp [A]
    have hleft : IntervalIntegrable (fun t : ℝ => Real.exp (-t * μ)) volume 0 T := by
      exact (Real.continuous_exp.comp (continuous_neg.mul continuous_const)).intervalIntegrable _ _
    have hright : IntervalIntegrable (fun _t : ℝ => (1 : ℝ)) volume 0 T := by
      exact continuous_const.intervalIntegrable _ _
    calc
      (∫ t in (0 : ℝ)..T, Real.exp (-t * μ)) ≤ ∫ t in (0 : ℝ)..T, (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on hT.le hleft hright
        intro t ht
        have hnonneg : 0 ≤ t := ht.1
        have hle_one : Real.exp (-t * μ) ≤ 1 := by
          apply Real.exp_le_one_iff.mpr
          nlinarith [hμ, hnonneg]
        simpa using hle_one
      _ = T := by simp
  have hinner : ∀ s : ℝ,
      (∫ t in (0 : ℝ)..T, Real.exp (-(s + t) * μ)) = Real.exp (-s * μ) * A := by
    intro s
    dsimp [A]
    calc
      (∫ t in (0 : ℝ)..T, Real.exp (-(s + t) * μ))
        = ∫ t in (0 : ℝ)..T, Real.exp (-s * μ) * Real.exp (-t * μ) := by
            apply intervalIntegral.integral_congr_ae
            filter_upwards with t ht
            rw [show -(s + t) * μ = -s * μ + -t * μ by ring, Real.exp_add]
      _ = Real.exp (-s * μ) * ∫ t in (0 : ℝ)..T, Real.exp (-t * μ) := by
            rw [intervalIntegral.integral_const_mul]
  rw [show (∫ s in (0 : ℝ)..T, ∫ t in (0 : ℝ)..T, Real.exp (-(s + t) * μ))
      = ∫ s in (0 : ℝ)..T, Real.exp (-s * μ) * A by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with s hs
      exact hinner s]
  rw [intervalIntegral.integral_mul_const]
  have hAexp : ∫ s in (0 : ℝ)..T, Real.exp (-s * μ) = A := by rfl
  rw [hAexp]
  calc
    A * A ≤ A * (1 / μ) := by gcongr
    _ ≤ T * (1 / μ) := by gcongr
    _ = T / μ := by ring

private lemma one_div_sqrt_integrableOn_Icc
    (T : ℝ) (hT : 0 < T) :
    IntegrableOn (fun s : ℝ => 1 / Real.sqrt s) (Set.Icc 0 T) volume := by
  have hpow : IntegrableOn (fun s : ℝ => s ^ ((-1 : ℝ) / 2)) (Set.Icc 0 T) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hT.le]
    simpa using intervalIntegral.intervalIntegrable_rpow' (by norm_num : -1 < ((-1 : ℝ) / 2))
  refine hpow.congr_fun ?_ measurableSet_Icc
  intro s hs
  have hs0 : 0 ≤ s := hs.1
  by_cases hspos : 0 < s
  · have hpow' : (s ^ ((1 : ℝ) / 2))⁻¹ = s ^ (-((1 : ℝ) / 2)) := by
      simpa using (Real.rpow_neg hs0 ((1 : ℝ) / 2)).symm
    have hneg : -((1 : ℝ) / 2) = ((-1 : ℝ) / 2) := by ring
    have hsqrt : (1 / Real.sqrt s : ℝ) = s ^ ((-1 : ℝ) / 2) := by
      rw [show (1 / Real.sqrt s : ℝ) = (s ^ ((1 : ℝ) / 2))⁻¹ by
        simp [one_div, Real.sqrt_eq_rpow]]
      rw [hpow', hneg]
    simpa using hsqrt.symm
  · have hs_eq : s = 0 := by linarith
    simp [hs_eq]

private lemma one_div_sqrt_integrable_Ioc
    (T : ℝ) (hT : 0 < T) :
    Integrable (fun s : ℝ => 1 / Real.sqrt s) (volume.restrict (Set.Ioc 0 T)) := by
  simpa [IntegrableOn] using
    (one_div_sqrt_integrableOn_Icc T hT).mono_set Set.Ioc_subset_Icc_self

private lemma integrable_inv_add_Ioc
    (T : ℝ) (hT : 0 < T) :
    Integrable
      (fun p : ℝ × ℝ => 1 / (p.1 + p.2 : ℝ))
      ((volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T))) := by
  have hdom : Integrable
      (fun p : ℝ × ℝ => (1 / Real.sqrt p.1) * (1 / Real.sqrt p.2))
      ((volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T))) := by
    simpa using
      Integrable.mul_prod
        (one_div_sqrt_integrable_Ioc T hT)
        (one_div_sqrt_integrable_Ioc T hT)
  have hpos :
      ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T))),
        0 < p.1 ∧ 0 < p.2 := by
    have hpos_restrict :
        ∀ᵐ p : ℝ × ℝ ∂((volume.prod volume).restrict (Set.Ioc 0 T ×ˢ Set.Ioc 0 T)),
          0 < p.1 ∧ 0 < p.2 := by
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
      exact ⟨hp.1.1, hp.2.1⟩
    simpa [Measure.prod_restrict] using hpos_restrict
  refine Integrable.mono' hdom ?_ ?_
  · simpa [one_div] using
      (((measurable_fst.add measurable_snd :
          Measurable fun p : ℝ × ℝ => p.1 + p.2).inv).aestronglyMeasurable)
  · filter_upwards [hpos] with p hp
    rcases p with ⟨s, t⟩
    have hs : 0 < s := hp.1
    have ht : 0 < t := hp.2
    have hs0 : 0 ≤ s := hs.le
    have ht0 : 0 ≤ t := ht.le
    have hsum_pos : 0 < s + t := add_pos hs ht
    have hAMGM : 2 * (Real.sqrt s * Real.sqrt t) ≤ s + t := by
      nlinarith [sq_nonneg (Real.sqrt s - Real.sqrt t), Real.sq_sqrt hs0, Real.sq_sqrt ht0]
    have hden_pos : 0 < 2 * (Real.sqrt s * Real.sqrt t) := by positivity
    have hinv : 1 / (s + t) ≤ 1 / (2 * (Real.sqrt s * Real.sqrt t)) := by
      exact one_div_le_one_div_of_le hden_pos hAMGM
    have hhalf :
        1 / (2 * (Real.sqrt s * Real.sqrt t)) ≤
          (1 / Real.sqrt s) * (1 / Real.sqrt t) := by
      have hsqrt_ne : Real.sqrt s ≠ 0 := by positivity
      have htsqrt_ne : Real.sqrt t ≠ 0 := by positivity
      have hA_nonneg : 0 ≤ (1 / Real.sqrt s) * (1 / Real.sqrt t) := by positivity
      calc
        1 / (2 * (Real.sqrt s * Real.sqrt t))
            = (1 / 2) * ((1 / Real.sqrt s) * (1 / Real.sqrt t)) := by
                field_simp [hsqrt_ne, htsqrt_ne]
        _ ≤ (1 / Real.sqrt s) * (1 / Real.sqrt t) := by
            nlinarith
    rw [Real.norm_of_nonneg (one_div_nonneg.2 hsum_pos.le)]
    exact hinv.trans hhalf

private lemma integrable_inv_add_mul_exp_Ioc
    (μ T : ℝ) (hμ : 0 ≤ μ) (hT : 0 < T) :
    Integrable
      (fun p : ℝ × ℝ => (1 / (p.1 + p.2 : ℝ)) * Real.exp (-(p.1 + p.2) * μ))
      ((volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T))) := by
  have hdom := integrable_inv_add_Ioc T hT
  have hpos :
      ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T))),
        0 < p.1 + p.2 := by
    have hpos_restrict :
        ∀ᵐ p : ℝ × ℝ ∂((volume.prod volume).restrict (Set.Ioc 0 T ×ˢ Set.Ioc 0 T)),
          0 < p.1 + p.2 := by
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
      exact add_pos hp.1.1 hp.2.1
    simpa [Measure.prod_restrict] using hpos_restrict
  refine Integrable.mono' hdom ?_ ?_
  · have hmeas :
        AEStronglyMeasurable
          (fun p : ℝ × ℝ => (p.1 + p.2)⁻¹ * Real.exp (-(p.1 + p.2) * μ))
          ((volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T))) := by
        have hmeas' : Measurable
            (fun p : ℝ × ℝ => (p.1 + p.2)⁻¹ * Real.exp (-(p.1 + p.2) * μ)) :=
          (((measurable_fst.add measurable_snd).inv).mul
            ((((measurable_fst.add measurable_snd).neg).mul_const μ).exp))
        exact hmeas'.aestronglyMeasurable
    simpa [one_div] using hmeas
  · filter_upwards [hpos] with p hp
    have hexp_le : Real.exp (-(p.1 + p.2) * μ) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith
    calc
      ‖1 / (p.1 + p.2) * Real.exp (-(p.1 + p.2) * μ)‖
        = (1 / (p.1 + p.2)) * Real.exp (-(p.1 + p.2) * μ) := by
            rw [Real.norm_of_nonneg]
            positivity
      _ ≤ (1 / (p.1 + p.2)) * 1 := by gcongr
      _ = 1 / (p.1 + p.2) := by ring

private lemma ioc_prod_exp_integral_le
    (μ T : ℝ) (hμ : 0 < μ) (hT : 0 < T) :
    ∫ p, Real.exp (-(p.1 + p.2) * μ)
      ∂((volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T)))
      ≤ T / μ := by
  have hmeasure :
      ((volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T))) =
        ((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T))) := by
    simp [restrict_Ioc_eq_restrict_Icc]
  have hcont : Continuous (fun p : ℝ × ℝ => Real.exp (-(p.1 + p.2) * μ)) := by
    fun_prop
  have hOn : IntegrableOn (fun p : ℝ × ℝ => Real.exp (-(p.1 + p.2) * μ))
      (Set.Icc 0 T ×ˢ Set.Icc 0 T) (volume.prod volume) := by
    exact hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hInt :
      Integrable (fun p : ℝ × ℝ => Real.exp (-(p.1 + p.2) * μ))
        ((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T))) := by
    simpa [IntegrableOn, Measure.prod_restrict, Set.Icc_prod_Icc] using hOn
  have hprod :
      ∫ p, Real.exp (-(p.1 + p.2) * μ)
        ∂((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T))) =
      ∫ s in Set.Icc 0 T, ∫ t in Set.Icc 0 T, Real.exp (-(s + t) * μ) := by
    simpa [Measure.prod_restrict, Set.Icc_prod_Icc, add_comm, add_left_comm, add_assoc] using
      (MeasureTheory.integral_prod (fun p : ℝ × ℝ => Real.exp (-(p.1 + p.2) * μ)) hInt)
  have hconvert :
      (∫ s in Set.Icc 0 T, ∫ t in Set.Icc 0 T, Real.exp (-(s + t) * μ)) =
        ∫ s in (0 : ℝ)..T, ∫ t in (0 : ℝ)..T, Real.exp (-(s + t) * μ) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT.le]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hs
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT.le]
  rw [hmeasure, hprod, hconvert]
  exact squareIntegral_exp_neg_le_div μ T hμ hT

private lemma ioc_prod_inv_add_integral_le
    (T : ℝ) (hT : 0 < T) :
    ∫ p, (1 / (p.1 + p.2 : ℝ))
      ∂((volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T)))
      ≤ 2 * T := by
  have hmeasure :
      ((volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T))) =
        ((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T))) := by
    simp [restrict_Ioc_eq_restrict_Icc]
  have hInt :
      Integrable (fun p : ℝ × ℝ => (1 / (p.1 + p.2 : ℝ)))
        ((volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T))) := by
    exact integrable_inv_add_Ioc T hT
  have hInt' :
      Integrable (fun p : ℝ × ℝ => (1 / (p.1 + p.2 : ℝ)))
        ((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T))) := by
    rw [← hmeasure]
    exact hInt
  have hprod :
      ∫ p, (1 / (p.1 + p.2 : ℝ))
        ∂((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T))) =
      ∫ s in Set.Icc 0 T, ∫ t in Set.Icc 0 T, (1 / (s + t : ℝ)) := by
    simpa [Measure.prod_restrict, Set.Icc_prod_Icc, add_comm] using
      (MeasureTheory.integral_prod (fun p : ℝ × ℝ => (1 / (p.1 + p.2 : ℝ))) hInt')
  have hconvert :
      (∫ s in Set.Icc 0 T, ∫ t in Set.Icc 0 T, (1 / (s + t : ℝ))) =
        ∫ s in (0 : ℝ)..T, ∫ t in (0 : ℝ)..T, (1 / (s + t : ℝ)) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT.le]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hs
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT.le]
  rw [hmeasure, hprod, hconvert]
  exact squareIntegral_inv_add_le_two_mul T hT

private lemma ioc_prod_inv_add_mul_exp_integral_le
    (μ T : ℝ) (hμ : 0 < μ) (hT : 0 < T) :
    ∫ p, ((1 / (p.1 + p.2 : ℝ)) * Real.exp (-(p.1 + p.2) * μ))
      ∂((volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T)))
      ≤ 2 * T := by
  let ν : Measure (ℝ × ℝ) :=
    (volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T))
  have hIntF :
      Integrable (fun p : ℝ × ℝ => (1 / (p.1 + p.2 : ℝ)) * Real.exp (-(p.1 + p.2) * μ)) ν := by
    simpa [ν] using integrable_inv_add_mul_exp_Ioc μ T hμ.le hT
  have hIntG :
      Integrable (fun p : ℝ × ℝ => (1 / (p.1 + p.2 : ℝ))) ν := by
    simpa [ν] using integrable_inv_add_Ioc T hT
  have hpos :
      ∀ᵐ p : ℝ × ℝ ∂ν, 0 < p.1 + p.2 := by
    have hpos_restrict :
        ∀ᵐ p : ℝ × ℝ ∂((volume.prod volume).restrict (Set.Ioc 0 T ×ˢ Set.Ioc 0 T)),
          0 < p.1 + p.2 := by
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
      exact add_pos hp.1.1 hp.2.1
    simpa [ν, Measure.prod_restrict] using hpos_restrict
  have hmono :
      (fun p : ℝ × ℝ => (1 / (p.1 + p.2 : ℝ)) * Real.exp (-(p.1 + p.2) * μ))
        ≤ᵐ[ν]
      (fun p : ℝ × ℝ => (1 / (p.1 + p.2 : ℝ))) := by
    filter_upwards [hpos] with p hp
    have hexp_le : Real.exp (-(p.1 + p.2) * μ) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith
    calc
      (1 / (p.1 + p.2 : ℝ)) * Real.exp (-(p.1 + p.2) * μ)
        ≤ (1 / (p.1 + p.2 : ℝ)) * 1 := by gcongr
      _ = (1 / (p.1 + p.2 : ℝ)) := by ring
  calc
    ∫ p, ((1 / (p.1 + p.2 : ℝ)) * Real.exp (-(p.1 + p.2) * μ)) ∂ν
      ≤ ∫ p, (1 / (p.1 + p.2 : ℝ)) ∂ν := by
          exact MeasureTheory.integral_mono_ae hIntF hIntG hmono
    _ ≤ 2 * T := by
          simpa [ν] using ioc_prod_inv_add_integral_le T hT

private lemma asymCanonicalRoughCovariance_sq_row_sum_eq_double_integral
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T)
    (x : AsymLatticeSites Nt Ns) :
    a ^ 2 * ∑ y : AsymLatticeSites Nt Ns,
      (asymCanonicalRoughCovariance Nt Ns a mass T x y) ^ 2 =
      (a ^ 2 : ℝ)⁻¹ *
        ∫ s in Set.Icc 0 T,
          ∫ t in Set.Icc 0 T,
            Real.exp (-(s + t) * mass ^ 2) *
              asymHeatKernelMatrix Nt Ns a (s + t) x x := by
  let I : Set ℝ := Set.Icc 0 T
  let F : AsymLatticeSites Nt Ns → ℝ → ℝ := fun y s =>
    Real.exp (-s * mass ^ 2) * asymHeatKernelMatrix Nt Ns a s x y
  have ha2_pos : (0 : ℝ) < a ^ 2 := pow_pos ha 2
  have hCov :
      ∀ y : AsymLatticeSites Nt Ns,
        asymCanonicalRoughCovariance Nt Ns a mass T x y =
          (a ^ 2 : ℝ)⁻¹ * ∫ s in I, F y s := by
    intro y
    simpa [I, F] using asymCanonicalRoughCovariance_eq_integral_Icc_heatKernel
      Nt Ns a mass ha hmass T hT x y
  have hprod :
      ∀ y : AsymLatticeSites Nt Ns,
        (∫ s in I, F y s) * ∫ t in I, F y t =
          ∫ p in I ×ˢ I, F y p.1 * F y p.2 ∂(volume.prod volume) := by
    intro y
    symm
    simpa [I, F] using
      (MeasureTheory.setIntegral_prod_mul (μ := volume) (ν := volume) (f := F y) (g := F y) I I)
  have hF_int :
      ∀ y : AsymLatticeSites Nt Ns,
        Integrable (F y) (volume.restrict I) := by
    intro y
    have hcont : Continuous (fun t : ℝ =>
      Real.exp (-t * mass ^ 2) * asymHeatKernelMatrix Nt Ns a t x y) := by
      have hExp : Continuous (fun t : ℝ => Real.exp (-t * mass ^ 2)) := by
        fun_prop
      have hEntry : Continuous (fun t : ℝ => asymHeatKernelMatrix Nt Ns a t x y) := by
        have hEq :
            (fun t : ℝ => asymHeatKernelMatrix Nt Ns a t x y) =
              (fun t : ℝ =>
                ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
                  Real.exp (-t * (latticeEigenvalue1d Nt a m₁ + latticeEigenvalue1d Ns a m₂)) *
                    asymCanonicalBasis Nt Ns (m₁, m₂) x *
                    asymCanonicalBasis Nt Ns (m₁, m₂) y /
                    asymCanonicalNormSq Nt Ns (m₁, m₂)) := by
          funext t
          rw [asymHeatKernel_entry_eq_eigenvalue_average Nt Ns a (ne_of_gt ha) t x y]
        rw [hEq]
        refine continuous_finset_sum _ ?_
        intro m₁ hm₁
        refine continuous_finset_sum _ ?_
        intro m₂ hm₂
        have hMode :
            Continuous
              (fun t : ℝ =>
                Real.exp (-t * (latticeEigenvalue1d Nt a m₁ + latticeEigenvalue1d Ns a m₂))) := by
          fun_prop
        have hConst :
            Continuous
              (fun _ : ℝ =>
                asymCanonicalBasis Nt Ns (m₁, m₂) x *
                  asymCanonicalBasis Nt Ns (m₁, m₂) y /
                  asymCanonicalNormSq Nt Ns (m₁, m₂)) := continuous_const
        simpa [mul_assoc, div_eq_mul_inv] using hMode.mul hConst
      exact hExp.mul hEntry
    simpa [I, F] using hcont.integrableOn_Icc
  have hprod_int :
      ∀ y : AsymLatticeSites Nt Ns,
        Integrable
          (fun p : ℝ × ℝ => F y p.1 * F y p.2)
          ((volume.restrict I).prod (volume.restrict I)) := by
    intro y
    exact (hF_int y).mul_prod (hF_int y)
  have hsum_int :
      Integrable
        (fun p : ℝ × ℝ => ∑ y : AsymLatticeSites Nt Ns, F y p.1 * F y p.2)
        ((volume.restrict I).prod (volume.restrict I)) := by
    exact integrable_finset_sum _ (fun y _ => hprod_int y)
  have hcollapse :
      (fun p : ℝ × ℝ => ∑ y : AsymLatticeSites Nt Ns, F y p.1 * F y p.2)
        =ᵐ[((volume.restrict I).prod (volume.restrict I))]
      (fun p : ℝ × ℝ =>
        Real.exp (-(p.1 + p.2) * mass ^ 2) *
          asymHeatKernelMatrix Nt Ns a (p.1 + p.2) x x) := by
    filter_upwards [] with p
    calc
      ∑ y : AsymLatticeSites Nt Ns, F y p.1 * F y p.2
        = ∑ y : AsymLatticeSites Nt Ns,
            (Real.exp (-p.1 * mass ^ 2) * Real.exp (-p.2 * mass ^ 2)) *
              (asymHeatKernelMatrix Nt Ns a p.1 x y *
                asymHeatKernelMatrix Nt Ns a p.2 x y) := by
                  refine Finset.sum_congr rfl ?_
                  intro y hy
                  simp [F]
                  ring
      _ = (Real.exp (-p.1 * mass ^ 2) * Real.exp (-p.2 * mass ^ 2)) *
            ∑ y : AsymLatticeSites Nt Ns,
              asymHeatKernelMatrix Nt Ns a p.1 x y *
                asymHeatKernelMatrix Nt Ns a p.2 x y := by
                  rw [Finset.mul_sum]
      _ = (Real.exp (-p.1 * mass ^ 2) * Real.exp (-p.2 * mass ^ 2)) *
            asymHeatKernelMatrix Nt Ns a (p.1 + p.2) x x := by
                  rw [asymHeatKernel_row_pairing_eq_diagonal Nt Ns a p.1 p.2 x]
      _ = Real.exp (-(p.1 + p.2) * mass ^ 2) *
            asymHeatKernelMatrix Nt Ns a (p.1 + p.2) x x := by
                  rw [← Real.exp_add]
                  congr 1
                  ring_nf
  have hdiag_int :
      Integrable
        (fun p : ℝ × ℝ =>
          Real.exp (-(p.1 + p.2) * mass ^ 2) *
            asymHeatKernelMatrix Nt Ns a (p.1 + p.2) x x)
        ((volume.restrict I).prod (volume.restrict I)) := by
    exact hsum_int.congr hcollapse
  calc
    a ^ 2 * ∑ y : AsymLatticeSites Nt Ns,
        (asymCanonicalRoughCovariance Nt Ns a mass T x y) ^ 2
      = ∑ y : AsymLatticeSites Nt Ns,
          a ^ 2 * (asymCanonicalRoughCovariance Nt Ns a mass T x y) ^ 2 := by
            rw [Finset.mul_sum]
    _ = ∑ y : AsymLatticeSites Nt Ns,
          (a ^ 2 : ℝ)⁻¹ * ((∫ s in I, F y s) * ∫ t in I, F y t) := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            rw [hCov y]
            field_simp [ne_of_gt ha2_pos]
    _ = (a ^ 2 : ℝ)⁻¹ *
          ∑ y : AsymLatticeSites Nt Ns, ((∫ s in I, F y s) * ∫ t in I, F y t) := by
            rw [← Finset.mul_sum]
    _ = (a ^ 2 : ℝ)⁻¹ *
          ∑ y : AsymLatticeSites Nt Ns,
            ∫ p in I ×ˢ I, F y p.1 * F y p.2 ∂(volume.prod volume) := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro y hy
              rw [hprod y]
    _ = (a ^ 2 : ℝ)⁻¹ *
          ∫ p,
            ∑ y : AsymLatticeSites Nt Ns, F y p.1 * F y p.2
          ∂((volume.restrict I).prod (volume.restrict I)) := by
              congr 1
              rw [← Measure.prod_restrict I I]
              symm
              rw [MeasureTheory.integral_finset_sum]
              intro y hy
              exact hprod_int y
    _ = (a ^ 2 : ℝ)⁻¹ *
          ∫ p,
            Real.exp (-(p.1 + p.2) * mass ^ 2) *
              asymHeatKernelMatrix Nt Ns a (p.1 + p.2) x x
          ∂((volume.restrict I).prod (volume.restrict I)) := by
              congr 1
              exact MeasureTheory.integral_congr_ae hcollapse
    _ = (a ^ 2 : ℝ)⁻¹ *
          ∫ s in I,
            ∫ t in I,
              Real.exp (-(s + t) * mass ^ 2) *
                asymHeatKernelMatrix Nt Ns a (s + t) x x := by
                  congr 1
                  exact MeasureTheory.integral_prod _ hdiag_int

/-- The asym rough covariance row sum is `O(T)` uniformly at fixed `Lt = Nt*a`, `Ls = Ns*a`. -/
theorem asymCanonicalRoughCovariance_pow_one_sum_le_uniform
    (mass Lt Ls : ℝ) (_hLt : 0 < Lt) (_hLs : 0 < Ls) (hmass : 0 < mass) :
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (_ha : 0 < a),
      (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls → ∀ (T : ℝ), 0 < T → ∀ (x : AsymLatticeSites Nt Ns),
        a ^ 2 * ∑ y : AsymLatticeSites Nt Ns, |asymCanonicalRoughCovariance Nt Ns a mass T x y| ≤
          C1 * T := by
  refine ⟨1, by positivity, ?_⟩
  intro Nt Ns hNt hNs a ha hvolt hvols T hT x
  have ha2_ne : (a ^ 2 : ℝ) ≠ 0 := by positivity
  have h_abs :
      a ^ 2 * ∑ y : AsymLatticeSites Nt Ns, |asymCanonicalRoughCovariance Nt Ns a mass T x y|
        = a ^ 2 * ∑ y : AsymLatticeSites Nt Ns,
            asymCanonicalRoughCovariance Nt Ns a mass T x y := by
    congr 1
    refine Finset.sum_congr rfl ?_
    intro y hy
    rw [abs_of_nonneg]
    exact asymCanonicalRoughCovariance_nonneg Nt Ns a mass T ha hmass hT x y
  have hEntryCont :
      ∀ y : AsymLatticeSites Nt Ns,
        Continuous (fun t : ℝ =>
          Real.exp (-t * mass ^ 2) * asymHeatKernelMatrix Nt Ns a t x y) := by
    intro y
    have hExp : Continuous (fun t : ℝ => Real.exp (-t * mass ^ 2)) := by
      fun_prop
    have hEntry : Continuous (fun t : ℝ => asymHeatKernelMatrix Nt Ns a t x y) := by
      have hEq :
          (fun t : ℝ => asymHeatKernelMatrix Nt Ns a t x y) =
            (fun t : ℝ =>
              ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
                Real.exp (-t * (latticeEigenvalue1d Nt a m₁ + latticeEigenvalue1d Ns a m₂)) *
                  asymCanonicalBasis Nt Ns (m₁, m₂) x *
                  asymCanonicalBasis Nt Ns (m₁, m₂) y /
                  asymCanonicalNormSq Nt Ns (m₁, m₂)) := by
        funext t
        rw [asymHeatKernel_entry_eq_eigenvalue_average Nt Ns a (ne_of_gt ha) t x y]
      rw [hEq]
      refine continuous_finset_sum _ ?_
      intro m₁ hm₁
      refine continuous_finset_sum _ ?_
      intro m₂ hm₂
      have hMode :
          Continuous (fun t : ℝ =>
            Real.exp (-t * (latticeEigenvalue1d Nt a m₁ + latticeEigenvalue1d Ns a m₂))) := by
        fun_prop
      have hConst :
          Continuous (fun _ : ℝ =>
            asymCanonicalBasis Nt Ns (m₁, m₂) x *
              asymCanonicalBasis Nt Ns (m₁, m₂) y /
              asymCanonicalNormSq Nt Ns (m₁, m₂)) := continuous_const
      simpa [mul_assoc, div_eq_mul_inv] using hMode.mul hConst
    exact hExp.mul hEntry
  have hEntryInt :
      ∀ y : AsymLatticeSites Nt Ns,
        IntegrableOn
          (fun t : ℝ => Real.exp (-t * mass ^ 2) * asymHeatKernelMatrix Nt Ns a t x y)
          (Set.Icc 0 T) := by
    intro y
    exact (hEntryCont y).integrableOn_Icc
  have hsum :
      a ^ 2 * ∑ y : AsymLatticeSites Nt Ns, asymCanonicalRoughCovariance Nt Ns a mass T x y
        = ∫ t in Set.Icc 0 T,
            Real.exp (-t * mass ^ 2) *
              ∑ y : AsymLatticeSites Nt Ns, asymHeatKernelMatrix Nt Ns a t x y := by
    calc
      a ^ 2 * ∑ y : AsymLatticeSites Nt Ns, asymCanonicalRoughCovariance Nt Ns a mass T x y
        = a ^ 2 * ∑ y : AsymLatticeSites Nt Ns,
            ((a ^ 2 : ℝ)⁻¹ *
              ∫ t in Set.Icc 0 T,
                Real.exp (-t * mass ^ 2) * asymHeatKernelMatrix Nt Ns a t x y) := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro y hy
              rw [asymCanonicalRoughCovariance_eq_integral_Icc_heatKernel
                Nt Ns a mass ha hmass T hT x y]
      _ = ∑ y : AsymLatticeSites Nt Ns,
            ∫ t in Set.Icc 0 T,
              Real.exp (-t * mass ^ 2) * asymHeatKernelMatrix Nt Ns a t x y := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl ?_
                intro y hy
                have hscal : a ^ 2 * (a ^ 2 : ℝ)⁻¹ = 1 := by
                  field_simp [ha2_ne]
                calc
                  a ^ 2 *
                      ((a ^ 2 : ℝ)⁻¹ *
                        ∫ t in Set.Icc 0 T,
                          Real.exp (-t * mass ^ 2) * asymHeatKernelMatrix Nt Ns a t x y)
                    = (a ^ 2 * (a ^ 2 : ℝ)⁻¹) *
                        ∫ t in Set.Icc 0 T,
                          Real.exp (-t * mass ^ 2) * asymHeatKernelMatrix Nt Ns a t x y := by
                            ring
                  _ = ∫ t in Set.Icc 0 T,
                        Real.exp (-t * mass ^ 2) * asymHeatKernelMatrix Nt Ns a t x y := by
                            rw [hscal, one_mul]
      _ = ∫ t in Set.Icc 0 T,
            ∑ y : AsymLatticeSites Nt Ns,
              Real.exp (-t * mass ^ 2) * asymHeatKernelMatrix Nt Ns a t x y := by
                rw [MeasureTheory.integral_finset_sum]
                intro y hy
                exact hEntryInt y
      _ = ∫ t in Set.Icc 0 T,
            Real.exp (-t * mass ^ 2) *
              ∑ y : AsymLatticeSites Nt Ns, asymHeatKernelMatrix Nt Ns a t x y := by
                apply integral_congr_ae
                filter_upwards with t
                rw [Finset.mul_sum]
  have hexp_int :
      ∫ t in Set.Icc 0 T, Real.exp (-t * mass ^ 2)
        = (1 - Real.exp (-T * mass ^ 2)) / (mass ^ 2) := by
    symm
    exact schwinger_rough (mass ^ 2) (by positivity) T hT.le
  have hexp_le : ∫ t in Set.Icc 0 T, Real.exp (-t * mass ^ 2) ≤ T := by
    rw [hexp_int]
    have haux : 1 - Real.exp (-(T * mass ^ 2)) ≤ T * mass ^ 2 := by
      linarith [Real.add_one_le_exp (-(T * mass ^ 2))]
    have haux' : 1 - Real.exp (-T * mass ^ 2) ≤ T * mass ^ 2 := by
      simpa using haux
    have hmass2_pos : 0 < mass ^ 2 := by positivity
    rw [div_le_iff₀ hmass2_pos]
    exact haux'
  rw [h_abs, hsum]
  calc
    ∫ t in Set.Icc 0 T, Real.exp (-t * mass ^ 2) *
        ∑ y : AsymLatticeSites Nt Ns, asymHeatKernelMatrix Nt Ns a t x y
      = ∫ t in Set.Icc 0 T, Real.exp (-t * mass ^ 2) * 1 := by
          apply integral_congr_ae
          filter_upwards with t
          rw [asymHeatKernel_row_sum_eq_one Nt Ns a ha t x]
    _ = ∫ t in Set.Icc 0 T, Real.exp (-t * mass ^ 2) := by simp
    _ ≤ T := hexp_le
    _ = 1 * T := by ring

/-- The asym rough covariance square row sum is `O(T)` uniformly at fixed rectangular volume. -/
theorem asymCanonicalRoughCovariance_pow_two_sum_le_uniform
    (mass Lt Ls : ℝ) (hLt : 0 < Lt) (hLs : 0 < Ls) (hmass : 0 < mass) :
    ∃ C2 : ℝ, 0 < C2 ∧ ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (_ha : 0 < a),
      (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls → ∀ (T : ℝ), 0 < T → ∀ (x : AsymLatticeSites Nt Ns),
        a ^ 2 * ∑ y : AsymLatticeSites Nt Ns,
            |asymCanonicalRoughCovariance Nt Ns a mass T x y| ^ 2 ≤
          C2 * T := by
  obtain ⟨C, hC_pos, hCdiag⟩ :=
    asymHeatKernel_diagonal_mass_weighted_le_uniform mass Lt Ls hLt hLs hmass
  refine ⟨2 * (Lt⁻¹ * Ls⁻¹) * C * (1 / mass ^ 2 + 2), by positivity, ?_⟩
  intro Nt Ns hNt hNs a ha hvolt hvols T hT x
  have hsq_abs :
      a ^ 2 * ∑ y : AsymLatticeSites Nt Ns, |asymCanonicalRoughCovariance Nt Ns a mass T x y| ^ 2
        = a ^ 2 * ∑ y : AsymLatticeSites Nt Ns,
            (asymCanonicalRoughCovariance Nt Ns a mass T x y) ^ 2 := by
    congr 1
    refine Finset.sum_congr rfl ?_
    intro y hy
    rw [sq_abs]
  let f : ℝ × ℝ → ℝ := fun p =>
    Real.exp (-(p.1 + p.2) * mass ^ 2) * asymHeatKernelMatrix Nt Ns a (p.1 + p.2) x x
  let g : ℝ × ℝ → ℝ := fun p =>
    2 * C * (1 + 1 / (p.1 + p.2)) * Real.exp (-(p.1 + p.2) * mass ^ 2)
  let ν : Measure (ℝ × ℝ) :=
    (volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T))
  have hmeasure :
      ((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T))) = ν := by
    simp [ν, restrict_Ioc_eq_restrict_Icc]
  have hf_cont : Continuous f := by
    let card : ℝ := (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ)
    have hEq :
        f = fun p : ℝ × ℝ =>
          card * ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
            Real.exp (-(p.1 + p.2) * asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂)) := by
      funext p
      simpa [card, f] using
        (asymHeatKernel_diagonal_mass_weighted_eq_eigenvalue_average
          Nt Ns a mass (p.1 + p.2) ha x)
    have hCont :
        Continuous (fun p : ℝ × ℝ =>
          card * ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
            Real.exp (-(p.1 + p.2) * asymCanonicalEigenvalue Nt Ns a mass (m₁, m₂))) := by
      fun_prop
    rw [hEq]
    exact hCont
  have hfOn :
      IntegrableOn f (Set.Icc 0 T ×ˢ Set.Icc 0 T) (volume.prod volume) := by
    exact hf_cont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hfIntIcc :
      Integrable f ((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T))) := by
    simpa [IntegrableOn, Measure.prod_restrict, Set.Icc_prod_Icc] using hfOn
  have hfInt : Integrable f ν := by
    rw [← hmeasure]
    exact hfIntIcc
  have hprodIcc :
      ∫ p, f p ∂((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T))) =
        ∫ s in Set.Icc 0 T, ∫ t in Set.Icc 0 T, f (s, t) := by
    simpa [Measure.prod_restrict, Set.Icc_prod_Icc, add_comm, add_left_comm, add_assoc] using
      (MeasureTheory.integral_prod f hfIntIcc)
  have hprod :
      ∫ s in Set.Icc 0 T, ∫ t in Set.Icc 0 T, f (s, t) = ∫ p, f p ∂ν := by
    rw [← hmeasure]
    exact hprodIcc.symm
  have hgExpInt :
      Integrable (fun p : ℝ × ℝ => Real.exp (-(p.1 + p.2) * mass ^ 2)) ν := by
    have hcont : Continuous (fun p : ℝ × ℝ => Real.exp (-(p.1 + p.2) * mass ^ 2)) := by
      fun_prop
    have hOn :
        IntegrableOn (fun p : ℝ × ℝ => Real.exp (-(p.1 + p.2) * mass ^ 2))
          (Set.Icc 0 T ×ˢ Set.Icc 0 T) (volume.prod volume) := by
      exact hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have hIntIcc :
        Integrable (fun p : ℝ × ℝ => Real.exp (-(p.1 + p.2) * mass ^ 2))
          ((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T))) := by
      simpa [IntegrableOn, Measure.prod_restrict, Set.Icc_prod_Icc] using hOn
    rw [← hmeasure]
    exact hIntIcc
  have hgInvExpInt :
      Integrable (fun p : ℝ × ℝ =>
        ((1 / (p.1 + p.2 : ℝ)) * Real.exp (-(p.1 + p.2) * mass ^ 2))) ν := by
    simpa [ν] using integrable_inv_add_mul_exp_Ioc (mass ^ 2) T (by positivity) hT
  have hgInt : Integrable g ν := by
    have hsum :
        Integrable (fun p : ℝ × ℝ =>
          Real.exp (-(p.1 + p.2) * mass ^ 2) +
            ((1 / (p.1 + p.2 : ℝ)) * Real.exp (-(p.1 + p.2) * mass ^ 2))) ν := by
      exact hgExpInt.add hgInvExpInt
    have hEq :
        g = fun p : ℝ × ℝ =>
          (2 * C) *
            (Real.exp (-(p.1 + p.2) * mass ^ 2) +
              ((1 / (p.1 + p.2 : ℝ)) * Real.exp (-(p.1 + p.2) * mass ^ 2))) := by
      funext p
      dsimp [g]
      ring
    rw [hEq]
    exact hsum.const_mul (2 * C)
  have hScaledInt :
      Integrable (fun p : ℝ × ℝ => (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) * g p) ν := by
    exact hgInt.const_mul _
  have hpos :
      ∀ᵐ p : ℝ × ℝ ∂ν, 0 < p.1 ∧ 0 < p.2 := by
    have hpos_restrict :
        ∀ᵐ p : ℝ × ℝ ∂((volume.prod volume).restrict (Set.Ioc 0 T ×ˢ Set.Ioc 0 T)),
          0 < p.1 ∧ 0 < p.2 := by
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
      exact ⟨hp.1.1, hp.2.1⟩
    simpa [ν, Measure.prod_restrict] using hpos_restrict
  have hfg :
      f ≤ᵐ[ν] (fun p : ℝ × ℝ => (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) * g p) := by
    filter_upwards [hpos] with p hp
    rcases p with ⟨s, t⟩
    have hst : 0 < s + t := add_pos hp.1 hp.2
    have hdiag := hCdiag Nt Ns a ha hvolt hvols (s + t) hst x
    have hsqrt :
        (1 + 1 / Real.sqrt (s + t)) ^ 2 ≤ 2 * (1 + 1 / (s + t)) :=
      one_add_inv_sqrt_sq_le_two_mul_one_add_inv (s + t) hst
    calc
      f (s, t)
        ≤ (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) *
            (C * (1 + 1 / Real.sqrt (s + t)) ^ 2 * Real.exp (-(s + t) * mass ^ 2)) := by
              simpa [f] using hdiag
      _ ≤ (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) *
            (C * (2 * (1 + 1 / (s + t))) * Real.exp (-(s + t) * mass ^ 2)) := by
              gcongr
      _ = (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) * g (s, t) := by
            dsimp [g]
            ring
  have hgBound :
      ∫ p, g p ∂ν ≤ 2 * C * (1 / mass ^ 2 + 2) * T := by
    have hEq :
        g = fun p : ℝ × ℝ =>
          (2 * C) *
            (Real.exp (-(p.1 + p.2) * mass ^ 2) +
              ((1 / (p.1 + p.2 : ℝ)) * Real.exp (-(p.1 + p.2) * mass ^ 2))) := by
      funext p
      dsimp [g]
      ring
    rw [hEq, integral_const_mul, integral_add hgExpInt hgInvExpInt]
    calc
      (2 * C) *
          (∫ p, Real.exp (-(p.1 + p.2) * mass ^ 2) ∂ν +
            ∫ p, ((1 / (p.1 + p.2 : ℝ)) * Real.exp (-(p.1 + p.2) * mass ^ 2)) ∂ν)
        ≤ (2 * C) * (T / mass ^ 2 + 2 * T) := by
            gcongr
            · simpa [ν] using ioc_prod_exp_integral_le (mass ^ 2) T (by positivity) hT
            · simpa [ν] using ioc_prod_inv_add_mul_exp_integral_le (mass ^ 2) T (by positivity) hT
      _ = 2 * C * (1 / mass ^ 2 + 2) * T := by ring
  rw [hsq_abs,
    asymCanonicalRoughCovariance_sq_row_sum_eq_double_integral Nt Ns a mass ha hmass T hT x]
  rw [hprod]
  calc
    (a ^ 2 : ℝ)⁻¹ * ∫ p, f p ∂ν
      ≤ (a ^ 2 : ℝ)⁻¹ * ∫ p, (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) * g p ∂ν := by
          apply mul_le_mul_of_nonneg_left
            (MeasureTheory.integral_mono_ae hfInt hScaledInt hfg)
          positivity
    _ = (((a ^ 2 : ℝ)⁻¹) * (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ)) * ∫ p, g p ∂ν := by
          rw [integral_const_mul]
          ring
    _ = Lt⁻¹ * Ls⁻¹ * ∫ p, g p ∂ν := by
          rw [prefactor_eq_rect_inv_area Lt Ls Nt Ns a ha hvolt hvols]
    _ ≤ Lt⁻¹ * Ls⁻¹ * (2 * C * (1 / mass ^ 2 + 2) * T) := by
          exact mul_le_mul_of_nonneg_left hgBound (by positivity)
    _ = (2 * (Lt⁻¹ * Ls⁻¹) * C * (1 / mass ^ 2 + 2)) * T := by ring

end Pphi2
