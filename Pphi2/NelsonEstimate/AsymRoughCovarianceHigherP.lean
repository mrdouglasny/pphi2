/- 
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Higher-`L^p` bounds for the asym rough covariance

This file ports the square `m ≥ 3` rough-covariance row-sum estimate to the
isotropic rectangular lattice `Z_Nt × Z_Ns`.

The only new critical-path result is
`asymCanonicalRoughCovariance_pow_sum_le_uniform_of_three_le`, proved via the
same `PiLp`-valued Minkowski argument as the square file, with the rectangular
heat-kernel trace factorization supplying the slice bound.
-/

import Pphi2.NelsonEstimate.AsymCovarianceBoundsGJ
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

open MeasureTheory ProbabilityTheory GaussianField
open scoped BigOperators

namespace Pphi2

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
  rw [show (∑ y : AsymLatticeSites Nt Ns, asymHeatKernelMatrix Nt Ns a t x y) =
      ∑ a₁ : ZMod Nt, ∑ b : ZMod Ns, asymHeatKernelMatrix Nt Ns a t x (a₁, b) by
        simpa [AsymLatticeSites] using
          (Fintype.sum_prod_type (f := fun y : ZMod Nt × ZMod Ns =>
            asymHeatKernelMatrix Nt Ns a t x y))]
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
  rw [show (∑ y : AsymLatticeSites Nt Ns,
      asymHeatKernelMatrix Nt Ns a s x y * asymHeatKernelMatrix Nt Ns a t x y) =
      ∑ a₁ : ZMod Nt, ∑ b : ZMod Ns,
        asymHeatKernelMatrix Nt Ns a s x (a₁, b) *
          asymHeatKernelMatrix Nt Ns a t x (a₁, b) by
        simpa [AsymLatticeSites] using
          (Fintype.sum_prod_type (f := fun y : ZMod Nt × ZMod Ns =>
            asymHeatKernelMatrix Nt Ns a s x y * asymHeatKernelMatrix Nt Ns a t x y))]
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

private lemma asymHeatKernel_entry_sq_le_diagonal_mul_diagonal
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a t : ℝ) (x y : AsymLatticeSites Nt Ns) :
    asymHeatKernelMatrix Nt Ns a t x y ^ 2 ≤
      asymHeatKernelMatrix Nt Ns a t x x *
        asymHeatKernelMatrix Nt Ns a t y y := by
  let r : ℝ := t / 2
  have hsymm :
      ∀ u v : AsymLatticeSites Nt Ns,
        asymHeatKernelMatrix Nt Ns a r u v =
          asymHeatKernelMatrix Nt Ns a r v u := by
    intro u v
    unfold asymHeatKernelMatrix
    have ht1 :
        Matrix.transpose (latticeHeatKernelMatrix 1 Nt a r) = latticeHeatKernelMatrix 1 Nt a r := by
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
      exact (latticeHeatKernelMatrix_isHermitian 1 Nt a r).eq
    have ht2 :
        Matrix.transpose (latticeHeatKernelMatrix 1 Ns a r) = latticeHeatKernelMatrix 1 Ns a r := by
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
      exact (latticeHeatKernelMatrix_isHermitian 1 Ns a r).eq
    have hentry1 :
        latticeHeatKernelMatrix 1 Nt a r (fin1Site u.1) (fin1Site v.1) =
          latticeHeatKernelMatrix 1 Nt a r (fin1Site v.1) (fin1Site u.1) := by
      simpa [Matrix.transpose_apply] using
        (congr_fun (congr_fun ht1 (fin1Site u.1)) (fin1Site v.1)).symm
    have hentry2 :
        latticeHeatKernelMatrix 1 Ns a r (fin1Site u.2) (fin1Site v.2) =
          latticeHeatKernelMatrix 1 Ns a r (fin1Site v.2) (fin1Site u.2) := by
      simpa [Matrix.transpose_apply] using
        (congr_fun (congr_fun ht2 (fin1Site u.2)) (fin1Site v.2)).symm
    calc
      asymHeatKernelMatrix Nt Ns a r u v
        = latticeHeatKernelMatrix 1 Nt a r (fin1Site u.1) (fin1Site v.1) *
            latticeHeatKernelMatrix 1 Ns a r (fin1Site u.2) (fin1Site v.2) := by
              rfl
      _ = latticeHeatKernelMatrix 1 Nt a r (fin1Site v.1) (fin1Site u.1) *
            latticeHeatKernelMatrix 1 Ns a r (fin1Site v.2) (fin1Site u.2) := by
              rw [hentry1, hentry2]
      _ = asymHeatKernelMatrix Nt Ns a r v u := by
              rfl
  have hxy :
      asymHeatKernelMatrix Nt Ns a t x y =
        ∑ z : AsymLatticeSites Nt Ns,
          asymHeatKernelMatrix Nt Ns a r x z *
            asymHeatKernelMatrix Nt Ns a r y z := by
    calc
      asymHeatKernelMatrix Nt Ns a t x y
        = asymHeatKernelMatrix Nt Ns a (r + r) x y := by
            congr 1
            dsimp [r]
            ring
      _ = ∑ z : AsymLatticeSites Nt Ns,
            asymHeatKernelMatrix Nt Ns a r x z *
              asymHeatKernelMatrix Nt Ns a r z y := by
            rw [show asymHeatKernelMatrix Nt Ns a (r + r) x y =
                latticeHeatKernelMatrix 1 Nt a (r + r) (fin1Site x.1) (fin1Site y.1) *
                  latticeHeatKernelMatrix 1 Ns a (r + r) (fin1Site x.2) (fin1Site y.2) by rfl]
            rw [latticeHeatKernelMatrix_semigroup (d := 1) (N := Nt) a r r,
              latticeHeatKernelMatrix_semigroup (d := 1) (N := Ns) a r r]
            simp [Matrix.mul_apply]
            rw [show (∑ zt : FinLatticeSites 1 Nt,
                latticeHeatKernelMatrix 1 Nt a r (fin1Site x.1) zt *
                  latticeHeatKernelMatrix 1 Nt a r zt (fin1Site y.1)) *
                ∑ zs : FinLatticeSites 1 Ns,
                  latticeHeatKernelMatrix 1 Ns a r (fin1Site x.2) zs *
                    latticeHeatKernelMatrix 1 Ns a r zs (fin1Site y.2)
                = ∑ zt : FinLatticeSites 1 Nt, ∑ zs : FinLatticeSites 1 Ns,
                    (latticeHeatKernelMatrix 1 Nt a r (fin1Site x.1) zt *
                      latticeHeatKernelMatrix 1 Nt a r zt (fin1Site y.1)) *
                    (latticeHeatKernelMatrix 1 Ns a r (fin1Site x.2) zs *
                      latticeHeatKernelMatrix 1 Ns a r zs (fin1Site y.2)) by
                  rw [← Fintype.sum_mul_sum]]
            rw [sum_fin1_eq_sum_zmod (f := fun zt : FinLatticeSites 1 Nt =>
              ∑ zs : FinLatticeSites 1 Ns,
                (latticeHeatKernelMatrix 1 Nt a r (fin1Site x.1) zt *
                  latticeHeatKernelMatrix 1 Nt a r zt (fin1Site y.1)) *
                (latticeHeatKernelMatrix 1 Ns a r (fin1Site x.2) zs *
                  latticeHeatKernelMatrix 1 Ns a r zs (fin1Site y.2)))]
            simp [fin1Site]
            calc
              ∑ zt : ZMod Nt,
                  ∑ zs : FinLatticeSites 1 Ns,
                    (latticeHeatKernelMatrix 1 Nt a r (fin1Site x.1) (fin1Site zt) *
                      latticeHeatKernelMatrix 1 Nt a r (fin1Site zt) (fin1Site y.1)) *
                    (latticeHeatKernelMatrix 1 Ns a r (fin1Site x.2) zs *
                      latticeHeatKernelMatrix 1 Ns a r zs (fin1Site y.2))
                  = ∑ zt : ZMod Nt, ∑ zs : ZMod Ns,
                      (latticeHeatKernelMatrix 1 Nt a r (fin1Site x.1) (fin1Site zt) *
                        latticeHeatKernelMatrix 1 Nt a r (fin1Site zt) (fin1Site y.1)) *
                      (latticeHeatKernelMatrix 1 Ns a r (fin1Site x.2) (fin1Site zs) *
                        latticeHeatKernelMatrix 1 Ns a r (fin1Site zs) (fin1Site y.2)) := by
                    refine Finset.sum_congr rfl ?_
                    intro zt hzt
                    rw [sum_fin1_eq_sum_zmod (f := fun zs : FinLatticeSites 1 Ns =>
                      (latticeHeatKernelMatrix 1 Nt a r (fin1Site x.1) (fin1Site zt) *
                        latticeHeatKernelMatrix 1 Nt a r (fin1Site zt) (fin1Site y.1)) *
                      (latticeHeatKernelMatrix 1 Ns a r (fin1Site x.2) zs *
                        latticeHeatKernelMatrix 1 Ns a r zs (fin1Site y.2)))]
                    simpa [fin1Site, zmodToFin1]
              _ = ∑ z : AsymLatticeSites Nt Ns,
                    asymHeatKernelMatrix Nt Ns a r x z * asymHeatKernelMatrix Nt Ns a r z y := by
                    simpa [AsymLatticeSites, asymHeatKernelMatrix,
                      mul_assoc, mul_left_comm, mul_comm]
                      using (Fintype.sum_prod_type' (f := fun zt : ZMod Nt => fun zs : ZMod Ns =>
                        asymHeatKernelMatrix Nt Ns a r x (zt, zs) *
                          asymHeatKernelMatrix Nt Ns a r (zt, zs) y)).symm
      _ = ∑ z : AsymLatticeSites Nt Ns,
            asymHeatKernelMatrix Nt Ns a r x z *
              asymHeatKernelMatrix Nt Ns a r y z := by
            refine Finset.sum_congr rfl ?_
            intro z hz
            rw [hsymm z y]
  rw [hxy]
  calc
    (∑ z : AsymLatticeSites Nt Ns,
        asymHeatKernelMatrix Nt Ns a r x z *
          asymHeatKernelMatrix Nt Ns a r y z) ^ 2
      ≤ (∑ z : AsymLatticeSites Nt Ns, asymHeatKernelMatrix Nt Ns a r x z ^ 2) *
          ∑ z : AsymLatticeSites Nt Ns, asymHeatKernelMatrix Nt Ns a r y z ^ 2 := by
            simpa using
              (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ)
                (fun z => asymHeatKernelMatrix Nt Ns a r x z)
                (fun z => asymHeatKernelMatrix Nt Ns a r y z))
    _ = asymHeatKernelMatrix Nt Ns a t x x *
          asymHeatKernelMatrix Nt Ns a t y y := by
            have hxx :
                ∑ z : AsymLatticeSites Nt Ns, asymHeatKernelMatrix Nt Ns a r x z ^ 2 =
                  asymHeatKernelMatrix Nt Ns a t x x := by
              calc
                ∑ z : AsymLatticeSites Nt Ns, asymHeatKernelMatrix Nt Ns a r x z ^ 2
                  = ∑ z : AsymLatticeSites Nt Ns,
                      asymHeatKernelMatrix Nt Ns a r x z *
                        asymHeatKernelMatrix Nt Ns a r x z := by
                          simp_rw [pow_two]
                _ = asymHeatKernelMatrix Nt Ns a (r + r) x x := by
                      rw [asymHeatKernel_row_pairing_eq_diagonal Nt Ns a r r x]
                _ = asymHeatKernelMatrix Nt Ns a t x x := by
                      congr 1
                      dsimp [r]
                      ring
            have hyy :
                ∑ z : AsymLatticeSites Nt Ns, asymHeatKernelMatrix Nt Ns a r y z ^ 2 =
                  asymHeatKernelMatrix Nt Ns a t y y := by
              calc
                ∑ z : AsymLatticeSites Nt Ns, asymHeatKernelMatrix Nt Ns a r y z ^ 2
                  = ∑ z : AsymLatticeSites Nt Ns,
                      asymHeatKernelMatrix Nt Ns a r y z *
                        asymHeatKernelMatrix Nt Ns a r y z := by
                          simp_rw [pow_two]
                _ = asymHeatKernelMatrix Nt Ns a (r + r) y y := by
                      rw [asymHeatKernel_row_pairing_eq_diagonal Nt Ns a r r y]
                _ = asymHeatKernelMatrix Nt Ns a t y y := by
                      congr 1
                      dsimp [r]
                      ring
            rw [hxx, hyy]

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
    positivity
  have hmul :
      (a ^ 2 : ℝ)⁻¹ * (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ)
        = 1 / (a ^ 2 * (Fintype.card (AsymLatticeSites Nt Ns) : ℝ)) := by
    field_simp [ha2_ne, hcard_ne]
  rw [hmul, harea]
  have hNt_nat : 0 < Nt := Nat.pos_of_ne_zero (by exact NeZero.ne Nt)
  have hNs_nat : 0 < Ns := Nat.pos_of_ne_zero (by exact NeZero.ne Ns)
  have hNt_pos : 0 < (Nt : ℝ) := by exact_mod_cast hNt_nat
  have hNs_pos : 0 < (Ns : ℝ) := by exact_mod_cast hNs_nat
  have hLt_ne : Lt ≠ 0 := by
    intro hLt0
    rw [hLt0] at hvolt
    nlinarith
  have hLs_ne : Ls ≠ 0 := by
    intro hLs0
    rw [hLs0] at hvols
    nlinarith
  field_simp [hLt_ne, hLs_ne]

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

private lemma asymHeatKernel_entry_mass_weighted_le_div
    (mass Lt Ls : ℝ) (hLt : 0 < Lt) (hLs : 0 < Ls) (hmass : 0 < mass) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (_ha : 0 < a),
        (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
        ∀ (t : ℝ), 0 < t → ∀ (x y : AsymLatticeSites Nt Ns),
          (a ^ 2 : ℝ)⁻¹ * Real.exp (-t * mass ^ 2) *
              asymHeatKernelMatrix Nt Ns a t x y ≤
            B / t := by
  obtain ⟨C, hC_pos, hCdiag⟩ :=
    asymHeatKernel_diagonal_mass_weighted_le_uniform mass Lt Ls hLt hLs hmass
  refine ⟨2 * Lt⁻¹ * Ls⁻¹ * C * (1 + 1 / mass ^ 2), by positivity, ?_⟩
  intro Nt Ns hNt hNs a ha hvolt hvols t ht x y
  let pxy : ℝ :=
    (a ^ 2 : ℝ)⁻¹ * Real.exp (-t * mass ^ 2) * asymHeatKernelMatrix Nt Ns a t x y
  let pxx : ℝ :=
    (a ^ 2 : ℝ)⁻¹ * Real.exp (-t * mass ^ 2) * asymHeatKernelMatrix Nt Ns a t x x
  let pyy : ℝ :=
    (a ^ 2 : ℝ)⁻¹ * Real.exp (-t * mass ^ 2) * asymHeatKernelMatrix Nt Ns a t y y
  have hxy_nonneg : 0 ≤ pxy := by
    dsimp [pxy]
    exact mul_nonneg (by positivity)
      (asymHeatKernel_nonneg Nt Ns a ha t ht.le x y)
  have hsq :
      pxy ^ 2 ≤ pxx * pyy := by
    have hentry := asymHeatKernel_entry_sq_le_diagonal_mul_diagonal Nt Ns a t x y
    calc
      pxy ^ 2
        = (((a ^ 2 : ℝ)⁻¹ * Real.exp (-t * mass ^ 2)) ^ 2) *
            asymHeatKernelMatrix Nt Ns a t x y ^ 2 := by
              dsimp [pxy]
              ring
      _ ≤ (((a ^ 2 : ℝ)⁻¹ * Real.exp (-t * mass ^ 2)) ^ 2) *
            (asymHeatKernelMatrix Nt Ns a t x x *
              asymHeatKernelMatrix Nt Ns a t y y) := by
                gcongr
      _ = pxx * pyy := by
            dsimp [pxx, pyy]
            ring
  have hxx :
      pxx ≤ (2 * Lt⁻¹ * Ls⁻¹ * C * (1 + 1 / mass ^ 2)) / t := by
    have hdiag := hCdiag Nt Ns a ha hvolt hvols t ht x
    calc
      pxx
        ≤ ((a ^ 2 : ℝ)⁻¹ * (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ)) *
            (C * (1 + 1 / Real.sqrt t) ^ 2 * Real.exp (-t * mass ^ 2)) := by
              simpa [pxx, mul_assoc, mul_left_comm, mul_comm] using
                mul_le_mul_of_nonneg_left hdiag (by positivity : 0 ≤ (a ^ 2 : ℝ)⁻¹)
      _ = Lt⁻¹ * Ls⁻¹ * (C * (1 + 1 / Real.sqrt t) ^ 2 * Real.exp (-t * mass ^ 2)) := by
            rw [prefactor_eq_rect_inv_area Lt Ls Nt Ns a ha hvolt hvols]
      _ = Lt⁻¹ * Ls⁻¹ * C * (Real.exp (-t * mass ^ 2) * (1 + 1 / Real.sqrt t) ^ 2) := by ring
      _ ≤ Lt⁻¹ * Ls⁻¹ * C * ((2 * (1 + 1 / mass ^ 2)) / t) := by
            gcongr
            exact exp_mul_one_add_inv_sqrt_sq_le_const_div (mass ^ 2) t (by positivity) ht
      _ = (2 * Lt⁻¹ * Ls⁻¹ * C * (1 + 1 / mass ^ 2)) / t := by
            field_simp [ht.ne']
  have hyy :
      pyy ≤ (2 * Lt⁻¹ * Ls⁻¹ * C * (1 + 1 / mass ^ 2)) / t := by
    have hdiag := hCdiag Nt Ns a ha hvolt hvols t ht y
    calc
      pyy
        ≤ ((a ^ 2 : ℝ)⁻¹ * (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ)) *
            (C * (1 + 1 / Real.sqrt t) ^ 2 * Real.exp (-t * mass ^ 2)) := by
              simpa [pyy, mul_assoc, mul_left_comm, mul_comm] using
                mul_le_mul_of_nonneg_left hdiag (by positivity : 0 ≤ (a ^ 2 : ℝ)⁻¹)
      _ = Lt⁻¹ * Ls⁻¹ * (C * (1 + 1 / Real.sqrt t) ^ 2 * Real.exp (-t * mass ^ 2)) := by
            rw [prefactor_eq_rect_inv_area Lt Ls Nt Ns a ha hvolt hvols]
      _ = Lt⁻¹ * Ls⁻¹ * C * (Real.exp (-t * mass ^ 2) * (1 + 1 / Real.sqrt t) ^ 2) := by ring
      _ ≤ Lt⁻¹ * Ls⁻¹ * C * ((2 * (1 + 1 / mass ^ 2)) / t) := by
            gcongr
            exact exp_mul_one_add_inv_sqrt_sq_le_const_div (mass ^ 2) t (by positivity) ht
      _ = (2 * Lt⁻¹ * Ls⁻¹ * C * (1 + 1 / mass ^ 2)) / t := by
            field_simp [ht.ne']
  have hxx_nonneg : 0 ≤ pxx := by
    dsimp [pxx]
    exact mul_nonneg (by positivity)
      (asymHeatKernel_nonneg Nt Ns a ha t ht.le x x)
  have hyy_nonneg : 0 ≤ pyy := by
    dsimp [pyy]
    exact mul_nonneg (by positivity)
      (asymHeatKernel_nonneg Nt Ns a ha t ht.le y y)
  nlinarith [hsq, hxx, hyy, hxy_nonneg, hxx_nonneg, hyy_nonneg]

private lemma asymHeatKernel_entry_mass_weighted_continuous
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a)
    (x y : AsymLatticeSites Nt Ns) :
    Continuous (fun t : ℝ =>
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

private lemma asymHeatKernel_entry_mass_weighted_integrableOn_Icc
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a)
    (x y : AsymLatticeSites Nt Ns) (T : ℝ) :
    IntegrableOn
      (fun t : ℝ => Real.exp (-t * mass ^ 2) * asymHeatKernelMatrix Nt Ns a t x y)
      (Set.Icc 0 T) := by
  exact (asymHeatKernel_entry_mass_weighted_continuous Nt Ns a mass ha x y).integrableOn_Icc

private lemma asymCanonicalEigenvalue_pos
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (_ha : 0 < a) (hmass : 0 < mass)
    (m : AsymCanonicalMode Nt Ns) :
    0 < asymCanonicalEigenvalue Nt Ns a mass m := by
  unfold asymCanonicalEigenvalue
  have h1 := latticeEigenvalue1d_nonneg Nt a m.1
  have h2 := latticeEigenvalue1d_nonneg Ns a m.2
  nlinarith [sq_pos_of_pos hmass]

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

private lemma rpow_two_div_nat_mul_nat
    (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha : 0 < a) :
    (a ^ (2 / (m : ℝ))) ^ (m : ℝ) = a ^ 2 := by
  have hm_ne : (m : ℝ) ≠ 0 := by positivity
  have hmul : (2 / (m : ℝ)) * (m : ℝ) = 2 := by
    field_simp [hm_ne]
  calc
    (a ^ (2 / (m : ℝ))) ^ (m : ℝ)
      = a ^ ((2 / (m : ℝ)) * (m : ℝ)) := by
          rw [← Real.rpow_mul (le_of_lt ha)]
    _ = a ^ 2 := by
          rw [hmul]
          simp

private lemma div_pow_nat_sub_one_rpow_inv_eq
    (m : ℕ) (hm : 1 ≤ m) (B t : ℝ) (hB : 0 ≤ B) (ht : 0 < t) :
    (((B / t) ^ (m - 1 : ℕ) : ℝ) ^ ((m : ℝ)⁻¹)) =
      B ^ (1 - (m : ℝ)⁻¹) * t ^ ((m : ℝ)⁻¹ - 1) := by
  have hm_ne : (m : ℝ) ≠ 0 := by positivity
  have hBt_nonneg : 0 ≤ B / t := by positivity
  have hm_sub : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    norm_num [Nat.cast_sub hm]
  calc
    (((B / t) ^ (m - 1 : ℕ) : ℝ) ^ ((m : ℝ)⁻¹))
      = (B / t) ^ (((m - 1 : ℕ) : ℝ) * (m : ℝ)⁻¹) := by
          rw [show ((B / t) ^ (m - 1 : ℕ) : ℝ) = (B / t) ^ (((m - 1 : ℕ) : ℝ)) by
            rw [Real.rpow_natCast]]
          rw [← Real.rpow_mul hBt_nonneg]
    _ = (B / t) ^ (1 - (m : ℝ)⁻¹) := by
          congr 1
          rw [hm_sub]
          field_simp [hm_ne]
    _ = (B * t⁻¹) ^ (1 - (m : ℝ)⁻¹) := by rw [div_eq_mul_inv]
    _ = B ^ (1 - (m : ℝ)⁻¹) * (t⁻¹) ^ (1 - (m : ℝ)⁻¹) := by
          rw [Real.mul_rpow hB (inv_nonneg.mpr ht.le)]
    _ = B ^ (1 - (m : ℝ)⁻¹) * (t ^ (1 - (m : ℝ)⁻¹))⁻¹ := by
          rw [Real.inv_rpow (le_of_lt ht)]
    _ = B ^ (1 - (m : ℝ)⁻¹) * t ^ ((m : ℝ)⁻¹ - 1) := by
          congr 1
          rw [← Real.rpow_neg (le_of_lt ht)]
          congr 1
          ring

private lemma integral_rpow_inv_nat_sub_one
    (m : ℕ) (hm : 1 ≤ m) (T : ℝ) (hT : 0 < T) :
    (∫ t in (0 : ℝ)..T, t ^ ((m : ℝ)⁻¹ - 1)) = (m : ℝ) * T ^ ((m : ℝ)⁻¹) := by
  have hm0 : m ≠ 0 := by omega
  calc
    (∫ t in (0 : ℝ)..T, t ^ ((m : ℝ)⁻¹ - 1))
      = (T ^ (((m : ℝ)⁻¹ - 1) + 1) - (0 : ℝ) ^ (((m : ℝ)⁻¹ - 1) + 1)) /
          (((m : ℝ)⁻¹ - 1) + 1) := by
            rw [integral_rpow]
            left
            have h_inv_pos : 0 < (m : ℝ)⁻¹ := by positivity
            linarith
    _ = (T ^ ((m : ℝ)⁻¹) - 0 ^ ((m : ℝ)⁻¹)) / ((m : ℝ)⁻¹) := by ring_nf
    _ = T ^ ((m : ℝ)⁻¹) / ((m : ℝ)⁻¹) := by
          rw [Real.zero_rpow (by positivity : (m : ℝ)⁻¹ ≠ 0), sub_zero]
    _ = (m : ℝ) * T ^ ((m : ℝ)⁻¹) := by
          field_simp [Nat.cast_ne_zero.mpr hm0]

private lemma rpow_inv_nat_sub_one_integrableOn_Icc
    (m : ℕ) (hm : 1 ≤ m) (T : ℝ) (hT : 0 < T) :
    IntegrableOn (fun t : ℝ => t ^ ((m : ℝ)⁻¹ - 1)) (Set.Icc 0 T) volume := by
  rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hT.le]
  refine intervalIntegral.intervalIntegrable_rpow' ?_
  have h_inv_pos : 0 < (m : ℝ)⁻¹ := by positivity
  linarith

private lemma asym_rough_heatKernel_slice_weighted_pow_sum_le
    (mass Lt Ls : ℝ) (hLt : 0 < Lt) (hLs : 0 < Ls) (hmass : 0 < mass)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (_ha : 0 < a)
        (_hvolt : (Nt : ℝ) * a = Lt) (_hvols : (Ns : ℝ) * a = Ls)
        (t : ℝ) (_ht : 0 < t) (x : AsymLatticeSites Nt Ns),
        ∑ y : AsymLatticeSites Nt Ns,
          ‖a ^ (2 / (m : ℝ)) *
              ((a ^ 2 : ℝ)⁻¹ * Real.exp (-t * mass ^ 2) *
                asymHeatKernelMatrix Nt Ns a t x y)‖ ^ (m : ℝ)
          ≤ ((B / t) ^ (m - 1 : ℕ) : ℝ) := by
  obtain ⟨B, hB_pos, hB⟩ :=
    asymHeatKernel_entry_mass_weighted_le_div mass Lt Ls hLt hLs hmass
  refine ⟨B, hB_pos, ?_⟩
  intro Nt Ns hNt hNs a ha hvolt hvols t ht x
  let α : ℝ := a ^ (2 / (m : ℝ))
  let g : AsymLatticeSites Nt Ns → ℝ := fun y =>
    (a ^ 2 : ℝ)⁻¹ * Real.exp (-t * mass ^ 2) * asymHeatKernelMatrix Nt Ns a t x y
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    positivity
  have hg_nonneg : ∀ y : AsymLatticeSites Nt Ns, 0 ≤ g y := by
    intro y
    dsimp [g]
    exact mul_nonneg (by positivity)
      (asymHeatKernel_nonneg Nt Ns a ha t ht.le x y)
  have hBg : ∀ y : AsymLatticeSites Nt Ns, g y ≤ B / t := by
    intro y
    simpa [g] using hB Nt Ns a ha hvolt hvols t ht x y
  have hpow_term :
      ∀ y : AsymLatticeSites Nt Ns,
        g y ^ (m : ℝ) ≤ ((B / t) ^ (m - 1 : ℕ) : ℝ) * g y := by
    intro y
    have hpow :
        g y ^ (m - 1 : ℕ) ≤ (B / t) ^ (m - 1 : ℕ) := by
      exact pow_le_pow_left₀ (hg_nonneg y) (hBg y) (m - 1)
    calc
      g y ^ (m : ℝ) = g y ^ m := by rw [Real.rpow_natCast]
      _ = g y ^ (m - 1) * g y := by
            have hm1 : m = (m - 1) + 1 := by omega
            rw [hm1, pow_add]
            simp
      _ ≤ (B / t) ^ (m - 1) * g y := by
            gcongr
            exact hg_nonneg y
  have hrow :
      a ^ 2 * ∑ y : AsymLatticeSites Nt Ns, g y = Real.exp (-t * mass ^ 2) := by
    calc
      a ^ 2 * ∑ y : AsymLatticeSites Nt Ns, g y
        = a ^ 2 * ∑ y : AsymLatticeSites Nt Ns,
            ((a ^ 2 : ℝ)⁻¹ * Real.exp (-t * mass ^ 2) *
              asymHeatKernelMatrix Nt Ns a t x y) := by
                simp [g]
      _ = ∑ y : AsymLatticeSites Nt Ns,
            Real.exp (-t * mass ^ 2) * asymHeatKernelMatrix Nt Ns a t x y := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro y hy
              have ha2_ne : (a ^ 2 : ℝ) ≠ 0 := by positivity
              calc
                a ^ 2 *
                    ((a ^ 2 : ℝ)⁻¹ * Real.exp (-t * mass ^ 2) *
                      asymHeatKernelMatrix Nt Ns a t x y)
                  = (a ^ 2 * (a ^ 2 : ℝ)⁻¹) *
                      (Real.exp (-t * mass ^ 2) * asymHeatKernelMatrix Nt Ns a t x y) := by ring
                _ = Real.exp (-t * mass ^ 2) * asymHeatKernelMatrix Nt Ns a t x y := by
                      field_simp [ha2_ne]
      _ = Real.exp (-t * mass ^ 2) *
            ∑ y : AsymLatticeSites Nt Ns, asymHeatKernelMatrix Nt Ns a t x y := by
              rw [Finset.mul_sum]
      _ = Real.exp (-t * mass ^ 2) * 1 := by
            rw [asymHeatKernel_row_sum_eq_one Nt Ns a ha t x]
      _ = Real.exp (-t * mass ^ 2) := by ring
  have hsum_g :
      a ^ 2 * ∑ y : AsymLatticeSites Nt Ns, g y ^ (m : ℝ) ≤ ((B / t) ^ (m - 1 : ℕ) : ℝ) := by
    have hsum_le :
        ∑ y : AsymLatticeSites Nt Ns, g y ^ (m : ℝ) ≤
          ∑ y : AsymLatticeSites Nt Ns, ((B / t) ^ (m - 1 : ℕ) : ℝ) * g y := by
      exact Finset.sum_le_sum (fun y hy => hpow_term y)
    have hexp_le_one : Real.exp (-t * mass ^ 2) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith
    calc
      a ^ 2 * ∑ y : AsymLatticeSites Nt Ns, g y ^ (m : ℝ)
        ≤ a ^ 2 *
            ∑ y : AsymLatticeSites Nt Ns, ((B / t) ^ (m - 1 : ℕ) : ℝ) * g y := by
            gcongr
      _ = a ^ 2 * (((B / t) ^ (m - 1 : ℕ) : ℝ) * ∑ y : AsymLatticeSites Nt Ns, g y) := by
            congr 1
            rw [Finset.mul_sum]
      _ = ((B / t) ^ (m - 1 : ℕ) : ℝ) * (a ^ 2 * ∑ y : AsymLatticeSites Nt Ns, g y) := by
            ring
      _ = ((B / t) ^ (m - 1 : ℕ) : ℝ) * Real.exp (-t * mass ^ 2) := by rw [hrow]
      _ ≤ ((B / t) ^ (m - 1 : ℕ) : ℝ) * 1 := by
            gcongr
      _ = ((B / t) ^ (m - 1 : ℕ) : ℝ) := by ring
  have hsum_alpha :
      ∑ y : AsymLatticeSites Nt Ns, ‖α * g y‖ ^ (m : ℝ) =
        a ^ 2 * ∑ y : AsymLatticeSites Nt Ns, g y ^ (m : ℝ) := by
    calc
      ∑ y : AsymLatticeSites Nt Ns, ‖α * g y‖ ^ (m : ℝ)
        = ∑ y : AsymLatticeSites Nt Ns, α ^ (m : ℝ) * g y ^ (m : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            have hgy : 0 ≤ g y := hg_nonneg y
            have hmul_nonneg : 0 ≤ α * g y := mul_nonneg hα_nonneg hgy
            rw [Real.norm_of_nonneg hmul_nonneg, Real.mul_rpow hα_nonneg hgy]
      _ = a ^ 2 * ∑ y : AsymLatticeSites Nt Ns, g y ^ (m : ℝ) := by
            rw [rpow_two_div_nat_mul_nat m hm a ha, Finset.mul_sum]
  calc
    ∑ y : AsymLatticeSites Nt Ns, ‖α * g y‖ ^ (m : ℝ)
      = a ^ 2 * ∑ y : AsymLatticeSites Nt Ns, g y ^ (m : ℝ) := hsum_alpha
    _ ≤ ((B / t) ^ (m - 1 : ℕ) : ℝ) := hsum_g

theorem asymCanonicalRoughCovariance_pow_sum_le_uniform_of_three_le
    (mass Lt Ls : ℝ) (hLt : 0 < Lt) (hLs : 0 < Ls) (hmass : 0 < mass)
    (m : ℕ) (hm : 3 ≤ m) :
    ∃ C_m : ℝ, 0 < C_m ∧
      ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (_ha : 0 < a),
        (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls → ∀ (T : ℝ), 0 < T →
        ∀ (x : AsymLatticeSites Nt Ns),
          a ^ 2 * ∑ y : AsymLatticeSites Nt Ns,
            |asymCanonicalRoughCovariance Nt Ns a mass T x y| ^ m ≤ C_m * T := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨B, hB_pos, hB_slice⟩ :=
    asym_rough_heatKernel_slice_weighted_pow_sum_le mass Lt Ls hLt hLs hmass m hm1
  let A : ℝ := B ^ (1 - (m : ℝ)⁻¹)
  let C_m : ℝ := (A * (m : ℝ)) ^ (m : ℝ)
  refine ⟨C_m, ?_, ?_⟩
  · dsimp [C_m, A]
    positivity
  · intro Nt Ns hNt hNs a ha hvolt hvols T hT x
    haveI : Fact (1 ≤ (m : ENNReal)) := ⟨by exact_mod_cast hm1⟩
    let α : ℝ := a ^ (2 / (m : ℝ))
    let μ : Measure ℝ := volume.restrict (Set.Ioc 0 T)
    let F : ℝ → PiLp (m : ENNReal) (fun _ : AsymLatticeSites Nt Ns => ℝ) :=
      fun s => WithLp.toLp (m : ENNReal) (fun y =>
        α * ((a ^ 2 : ℝ)⁻¹ * Real.exp (-s * mass ^ 2) *
          asymHeatKernelMatrix Nt Ns a s x y))
    have hm_pos : 0 < (m : ℝ) := by positivity
    have hm_ne : (m : ℝ) ≠ 0 := by positivity
    have hα_nonneg : 0 ≤ α := by
      dsimp [α]
      positivity
    have hcoord_int :
        ∀ y : AsymLatticeSites Nt Ns, Integrable (fun s => F s y) μ := by
      intro y
      have hIcc :
          IntegrableOn
            (fun s : ℝ =>
              Real.exp (-s * mass ^ 2) * asymHeatKernelMatrix Nt Ns a s x y)
            (Set.Icc 0 T) volume := by
        exact asymHeatKernel_entry_mass_weighted_integrableOn_Icc Nt Ns a mass ha x y T
      have hIoc :
          IntegrableOn
            (fun s : ℝ =>
              Real.exp (-s * mass ^ 2) * asymHeatKernelMatrix Nt Ns a s x y)
            (Set.Ioc 0 T) volume := by
        exact (integrableOn_Icc_iff_integrableOn_Ioc
          (f := fun s : ℝ =>
            Real.exp (-s * mass ^ 2) * asymHeatKernelMatrix Nt Ns a s x y)).mp hIcc
      have hBase :
          Integrable
            (fun s : ℝ =>
              Real.exp (-s * mass ^ 2) * asymHeatKernelMatrix Nt Ns a s x y) μ := by
        simpa [μ] using hIoc
      convert hBase.const_mul ((a ^ 2 : ℝ)⁻¹ * α) using 1
      funext s
      ring
    have hF_int : Integrable (μ := μ) F := by
      exact Integrable.of_eval_piLp (f := F) hcoord_int
    let v : PiLp (m : ENNReal) (fun _ : AsymLatticeSites Nt Ns => ℝ) := ∫ s, F s ∂μ
    have hcov_coord :
        ∀ y : AsymLatticeSites Nt Ns,
          α * asymCanonicalRoughCovariance Nt Ns a mass T x y = ∫ s, F s y ∂μ := by
      intro y
      rw [asymCanonicalRoughCovariance_eq_integral_Icc_heatKernel
        Nt Ns a mass ha hmass T hT x y]
      dsimp [μ, F]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      calc
        α * ((a ^ 2 : ℝ)⁻¹ *
            ∫ s in Set.Ioc 0 T,
              Real.exp (-s * mass ^ 2) * asymHeatKernelMatrix Nt Ns a s x y)
          = (α * (a ^ 2 : ℝ)⁻¹) *
              ∫ s in Set.Ioc 0 T,
                Real.exp (-s * mass ^ 2) * asymHeatKernelMatrix Nt Ns a s x y := by
                  ring
        _ = ∫ s in Set.Ioc 0 T,
              (α * (a ^ 2 : ℝ)⁻¹) *
                (Real.exp (-s * mass ^ 2) * asymHeatKernelMatrix Nt Ns a s x y) := by
                  rw [integral_const_mul]
        _ = ∫ s in Set.Ioc 0 T,
              α * ((a ^ 2 : ℝ)⁻¹ * Real.exp (-s * mass ^ 2) *
                asymHeatKernelMatrix Nt Ns a s x y) := by
                  apply integral_congr_ae
                  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
                  ring
    have hv_coord :
        ∀ y : AsymLatticeSites Nt Ns,
          v y = α * asymCanonicalRoughCovariance Nt Ns a mass T x y := by
      intro y
      dsimp [v]
      rw [eval_integral_piLp (μ := μ) (f := F) hcoord_int y]
      exact (hcov_coord y).symm
    have hnorm_bound_ae :
        ∀ᵐ s ∂μ, ‖F s‖ ≤ A * s ^ ((m : ℝ)⁻¹ - 1) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hs_pos : 0 < s := hs.1
      have hsum_slice := hB_slice Nt Ns a ha hvolt hvols s hs_pos x
      have hsum_F :
          ∑ y : AsymLatticeSites Nt Ns, ‖F s y‖ ^ (m : ℝ) ≤ (B / s) ^ (m - 1 : ℕ) := by
        simpa [F] using hsum_slice
      have hnorm_eq :
          ‖F s‖ = (∑ y : AsymLatticeSites Nt Ns, ‖F s y‖ ^ (m : ℝ)) ^ (1 / (m : ℝ)) := by
        simpa using
          (PiLp.norm_eq_sum (p := (m : ENNReal))
            (β := fun _ : AsymLatticeSites Nt Ns => ℝ) (by simpa using hm_pos) (F s))
      have hsum_nonneg : 0 ≤ ∑ y : AsymLatticeSites Nt Ns, ‖F s y‖ ^ (m : ℝ) := by
        positivity
      have hrpow_le :
          (∑ y : AsymLatticeSites Nt Ns, ‖F s y‖ ^ (m : ℝ)) ^ (1 / (m : ℝ))
            ≤ (((B / s) ^ (m - 1 : ℕ) : ℝ)) ^ (1 / (m : ℝ)) := by
        exact Real.rpow_le_rpow hsum_nonneg hsum_F (by positivity)
      calc
        ‖F s‖
          = (∑ y : AsymLatticeSites Nt Ns, ‖F s y‖ ^ (m : ℝ)) ^ (1 / (m : ℝ)) := hnorm_eq
        _ ≤ (((B / s) ^ (m - 1 : ℕ) : ℝ)) ^ (1 / (m : ℝ)) := hrpow_le
        _ = A * s ^ ((m : ℝ)⁻¹ - 1) := by
              dsimp [A]
              simpa [one_div] using
                (div_pow_nat_sub_one_rpow_inv_eq m hm1 B s hB_pos.le hs_pos)
    let g : ℝ → ℝ := fun s => A * s ^ ((m : ℝ)⁻¹ - 1)
    have hg_int : Integrable g μ := by
      have hIcc :
          IntegrableOn (fun s : ℝ => s ^ ((m : ℝ)⁻¹ - 1)) (Set.Icc 0 T) volume := by
        exact rpow_inv_nat_sub_one_integrableOn_Icc m hm1 T hT
      have hIoc :
          IntegrableOn (fun s : ℝ => s ^ ((m : ℝ)⁻¹ - 1)) (Set.Ioc 0 T) volume := by
        exact (integrableOn_Icc_iff_integrableOn_Ioc
          (f := fun s : ℝ => s ^ ((m : ℝ)⁻¹ - 1))).mp hIcc
      simpa [g, μ] using hIoc.const_mul A
    have hnorm_le : ‖v‖ ≤ ∫ s, g s ∂μ := by
      dsimp [v]
      exact norm_integral_le_of_norm_le hg_int hnorm_bound_ae
    have hg_eval : ∫ s, g s ∂μ = A * ((m : ℝ) * T ^ ((m : ℝ)⁻¹)) := by
      dsimp [g, μ]
      rw [← MeasureTheory.integral_Icc_eq_integral_Ioc, integral_const_mul]
      have hbase :
          ∫ a : ℝ in Set.Icc 0 T, a ^ ((m : ℝ)⁻¹ - 1) ∂volume =
            (m : ℝ) * T ^ ((m : ℝ)⁻¹) := by
        calc
          ∫ a : ℝ in Set.Icc 0 T, a ^ ((m : ℝ)⁻¹ - 1) ∂volume
            = ∫ a : ℝ in Set.Ioc 0 T, a ^ ((m : ℝ)⁻¹ - 1) ∂volume := by
                rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
          _ = ∫ a in (0 : ℝ)..T, a ^ ((m : ℝ)⁻¹ - 1) := by
                rw [← intervalIntegral.integral_of_le hT.le]
          _ = (m : ℝ) * T ^ ((m : ℝ)⁻¹) := integral_rpow_inv_nat_sub_one m hm1 T hT
      exact congrArg (fun u : ℝ => A * u) hbase
    have hnorm_le' : ‖v‖ ≤ A * ((m : ℝ) * T ^ ((m : ℝ)⁻¹)) := by
      rwa [hg_eval] at hnorm_le
    have hsum_v :
        ∑ y : AsymLatticeSites Nt Ns, ‖v y‖ ^ (m : ℝ) =
          a ^ 2 * ∑ y : AsymLatticeSites Nt Ns,
            |asymCanonicalRoughCovariance Nt Ns a mass T x y| ^ m := by
      calc
        ∑ y : AsymLatticeSites Nt Ns, ‖v y‖ ^ (m : ℝ)
          = ∑ y : AsymLatticeSites Nt Ns,
              ‖α * asymCanonicalRoughCovariance Nt Ns a mass T x y‖ ^ (m : ℝ) := by
                refine Finset.sum_congr rfl ?_
                intro y hy
                rw [hv_coord y]
        _ = ∑ y : AsymLatticeSites Nt Ns,
              α ^ (m : ℝ) * |asymCanonicalRoughCovariance Nt Ns a mass T x y| ^ m := by
                refine Finset.sum_congr rfl ?_
                intro y hy
                rw [norm_mul, Real.norm_of_nonneg hα_nonneg, Real.norm_eq_abs,
                  Real.mul_rpow hα_nonneg (abs_nonneg _), Real.rpow_natCast,
                  Real.rpow_natCast]
        _ = a ^ 2 * ∑ y : AsymLatticeSites Nt Ns,
              |asymCanonicalRoughCovariance Nt Ns a mass T x y| ^ m := by
                rw [rpow_two_div_nat_mul_nat m hm1 a ha, Finset.mul_sum]
    have hnorm_eq :
        ‖v‖ = (∑ y : AsymLatticeSites Nt Ns, ‖v y‖ ^ (m : ℝ)) ^ (1 / (m : ℝ)) := by
      simpa using
        (PiLp.norm_eq_sum (p := (m : ENNReal))
          (β := fun _ : AsymLatticeSites Nt Ns => ℝ) (by simpa using hm_pos) v)
    have hsum_eq_norm :
        ∑ y : AsymLatticeSites Nt Ns, ‖v y‖ ^ (m : ℝ) = ‖v‖ ^ (m : ℝ) := by
      have hsum_nonneg : 0 ≤ ∑ y : AsymLatticeSites Nt Ns, ‖v y‖ ^ (m : ℝ) := by
        positivity
      calc
        ∑ y : AsymLatticeSites Nt Ns, ‖v y‖ ^ (m : ℝ)
          = ((∑ y : AsymLatticeSites Nt Ns, ‖v y‖ ^ (m : ℝ)) ^ (1 / (m : ℝ))) ^ (m : ℝ) := by
              symm
              simpa [one_div] using Real.rpow_inv_rpow hsum_nonneg hm_ne
        _ = ‖v‖ ^ (m : ℝ) := by rw [← hnorm_eq]
    have hpow_bound :
        ‖v‖ ^ (m : ℝ) ≤ (A * ((m : ℝ) * T ^ ((m : ℝ)⁻¹))) ^ (m : ℝ) := by
      exact Real.rpow_le_rpow (by positivity) hnorm_le' (by positivity)
    have hscalar :
        (A * ((m : ℝ) * T ^ ((m : ℝ)⁻¹))) ^ (m : ℝ) = C_m * T := by
      dsimp [C_m]
      calc
        (A * ((m : ℝ) * T ^ ((m : ℝ)⁻¹))) ^ (m : ℝ)
          = ((A * (m : ℝ)) * T ^ ((m : ℝ)⁻¹)) ^ (m : ℝ) := by
              congr 1
              ring_nf
        _ = (A * (m : ℝ)) ^ (m : ℝ) * (T ^ ((m : ℝ)⁻¹)) ^ (m : ℝ) := by
              rw [Real.mul_rpow (by positivity) (by positivity)]
        _ = (A * (m : ℝ)) ^ (m : ℝ) * T := by
              rw [Real.rpow_inv_rpow hT.le hm_ne]
        _ = C_m * T := by rfl
    calc
      a ^ 2 * ∑ y : AsymLatticeSites Nt Ns,
          |asymCanonicalRoughCovariance Nt Ns a mass T x y| ^ m
        = ∑ y : AsymLatticeSites Nt Ns, ‖v y‖ ^ (m : ℝ) := by
            symm
            exact hsum_v
      _ = ‖v‖ ^ (m : ℝ) := hsum_eq_norm
      _ ≤ (A * ((m : ℝ) * T ^ ((m : ℝ)⁻¹))) ^ (m : ℝ) := hpow_bound
      _ = C_m * T := hscalar

end Pphi2
