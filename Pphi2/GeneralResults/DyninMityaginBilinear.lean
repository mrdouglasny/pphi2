/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dynin-Mityagin Bilinear Convergence

Abstract extension theorem for symmetric bilinear forms on a
`DyninMityaginSpace`, proved from:

1. basiswise convergence,
2. a uniform eventual polynomial bound on basis pairs,
3. the Schauder expansion and coefficient decay of the DM basis.

This is the generic ambient theorem behind torus and continuum-limit arguments:
once the deep analytic input is reduced to basis vectors, the full convergence on
arbitrary test functions is a reusable functional-analytic consequence.
-/

import Nuclear.NuclearSpace
import Mathlib.Analysis.Normed.Group.Tannery

noncomputable section

open Filter

namespace GaussianField

section

variable {α E : Type*}
variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [DyninMityaginSpace E]
variable {l : Filter α}

/-- Summability of `|coeff m f| * (1 + m)^r` from the DM coefficient decay axiom. -/
theorem summable_coeff_mul_pow (f : E) (r : ℕ) :
    Summable (fun m : ℕ => |DyninMityaginSpace.coeff m f| * (1 + (m : ℝ)) ^ r) := by
  obtain ⟨C_d, hC_d, s_d, hdecay⟩ := DyninMityaginSpace.coeff_decay (E := E) (r + 2)
  apply Summable.of_nonneg_of_le
      (fun m => mul_nonneg (abs_nonneg _) (by positivity))
  · intro m
    calc |DyninMityaginSpace.coeff m f| * (1 + (m : ℝ)) ^ r
        = (|DyninMityaginSpace.coeff m f| * (1 + (m : ℝ)) ^ (r + 2)) /
            (1 + (m : ℝ)) ^ 2 := by
            rw [pow_add]
            field_simp
      _ ≤ (C_d * (s_d.sup DyninMityaginSpace.p) f) / (1 + (m : ℝ)) ^ 2 :=
          div_le_div_of_nonneg_right (hdecay f m) (by positivity)
      _ = C_d * (s_d.sup DyninMityaginSpace.p) f * (1 / (1 + (m : ℝ)) ^ 2) := by
          ring
  · exact
      (((Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective
          Nat.succ_injective).congr (fun m => by
            simp [Nat.succ_eq_add_one]
            ring)).mul_left _

/-- Extend basiswise convergence of symmetric right-continuous bilinear forms to
arbitrary vectors in a `DyninMityaginSpace`.

The hypotheses encode the ambient functional analysis rather than any specific
Fourier or lattice model:

- `B_seq n f` and `B f` are continuous linear maps in the right argument,
- the bilinear forms are symmetric,
- basis-pair values converge pointwise,
- basis-pair values satisfy a polynomial bound eventually in `n`.

The conclusion is the full convergence `B_seq n f g → B f g` for arbitrary
`f, g`. -/
theorem tendsto_of_symmetric_basis_tendsto
    (B_seq : α → E → E →L[ℝ] ℝ)
    (B : E → E →L[ℝ] ℝ)
    (h_symm_seq : ∀ n f g, B_seq n f g = B_seq n g f)
    (h_symm : ∀ f g, B f g = B g f)
    (h_basis_bound : ∃ C : ℝ, 0 < C ∧ ∃ s_left s_right : ℕ,
      ∀ᶠ n in l, ∀ i j,
        |B_seq n (DyninMityaginSpace.basis i) (DyninMityaginSpace.basis j)| ≤
          C * (1 + (i : ℝ)) ^ s_left * (1 + (j : ℝ)) ^ s_right)
    (h_basis_tendsto : ∀ i j,
      Tendsto
        (fun n => B_seq n (DyninMityaginSpace.basis i) (DyninMityaginSpace.basis j))
        l
        (nhds (B (DyninMityaginSpace.basis i) (DyninMityaginSpace.basis j))))
    (f g : E) :
    Tendsto (fun n => B_seq n f g) l (nhds (B f g)) := by
  obtain ⟨C, hC_pos, s_left, s_right, h_bound_eventually⟩ := h_basis_bound
  have h_right_basis_bound :
      ∀ f : E, ∃ C_f : ℝ, 0 < C_f ∧
        ∀ᶠ n in l, ∀ j,
          |B_seq n f (DyninMityaginSpace.basis j)| ≤ C_f * (1 + (j : ℝ)) ^ s_left := by
    intro f
    set sum_f : ℝ := ∑' i : ℕ, |DyninMityaginSpace.coeff i f| * (1 + (i : ℝ)) ^ s_right
    have hsum_f : Summable
        (fun i : ℕ => |DyninMityaginSpace.coeff i f| * (1 + (i : ℝ)) ^ s_right) :=
      summable_coeff_mul_pow f s_right
    have hsum_f_nonneg : 0 ≤ sum_f := by
      exact tsum_nonneg (fun _ => by positivity)
    refine ⟨C * sum_f + 1, by nlinarith [hC_pos, hsum_f_nonneg], ?_⟩
    filter_upwards [h_bound_eventually] with n hn j
    have h_expand :
        B_seq n f (DyninMityaginSpace.basis j) =
          ∑' i : ℕ,
            DyninMityaginSpace.coeff i f *
              B_seq n (DyninMityaginSpace.basis j) (DyninMityaginSpace.basis i) := by
      rw [h_symm_seq n f (DyninMityaginSpace.basis j)]
      simpa using DyninMityaginSpace.expansion (B_seq n (DyninMityaginSpace.basis j)) f
    rw [h_expand]
    set a : ℕ → ℝ := fun i =>
      DyninMityaginSpace.coeff i f *
        B_seq n (DyninMityaginSpace.basis j) (DyninMityaginSpace.basis i)
    set b : ℕ → ℝ := fun i =>
      |DyninMityaginSpace.coeff i f| *
        (C * (1 + (j : ℝ)) ^ s_left * (1 + (i : ℝ)) ^ s_right)
    have hb_sum : Summable b :=
      (hsum_f.mul_left (C * (1 + (j : ℝ)) ^ s_left)).congr (fun i => by
        simp [b]
        ring)
    have ha_sum : Summable a := by
      exact Summable.of_norm_bounded hb_sum (fun i => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hn j i) (abs_nonneg _))
    have h_pw : ∀ i, |a i| ≤ b i := by
      intro i
      simp only [a, b]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hn j i) (abs_nonneg _)
    have ha_norm_sum : Summable (fun i : ℕ => ‖a i‖) :=
      Summable.of_norm_bounded hb_sum (fun i => by
        simpa [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)] using h_pw i)
    have ha_abs_sum : Summable (fun i : ℕ => |a i|) :=
      ha_norm_sum.congr fun i => by rw [Real.norm_eq_abs]
    have h1 : |∑' i, a i| ≤ ∑' i, |a i| := by
      have := norm_tsum_le_tsum_norm ha_norm_sum
      simpa only [Real.norm_eq_abs] using this
    have h2 : ∑' i, |a i| ≤ ∑' i, b i := by
      exact Summable.tsum_le_tsum h_pw ha_abs_sum hb_sum
    have h3 : ∑' i, b i = C * (1 + (j : ℝ)) ^ s_left * sum_f := by
      show ∑' i, b i = _
      simp_rw [show ∀ i, b i =
          C * (1 + (j : ℝ)) ^ s_left *
            (|DyninMityaginSpace.coeff i f| * (1 + (i : ℝ)) ^ s_right) from
        fun i => by
          simp [b]
          ring]
      exact tsum_mul_left
    have hpow_nonneg : 0 ≤ (1 + (j : ℝ)) ^ s_left := by positivity
    have hconst : C * sum_f ≤ C * sum_f + 1 := by linarith
    calc
      |∑' i, a i| ≤ ∑' i, |a i| := h1
      _ ≤ ∑' i, b i := h2
      _ = C * (1 + (j : ℝ)) ^ s_left * sum_f := h3
      _ = (C * sum_f) * (1 + (j : ℝ)) ^ s_left := by ring
      _ ≤ (C * sum_f + 1) * (1 + (j : ℝ)) ^ s_left :=
        mul_le_mul_of_nonneg_right hconst hpow_nonneg
  have h_right_basis_tendsto :
      ∀ f : E, ∀ j : ℕ,
        Tendsto
          (fun n => B_seq n f (DyninMityaginSpace.basis j))
          l
          (nhds (B f (DyninMityaginSpace.basis j))) := by
    intro f j
    have h_expand_seq :
        ∀ n,
          B_seq n f (DyninMityaginSpace.basis j) =
            ∑' i : ℕ,
              DyninMityaginSpace.coeff i f *
                B_seq n (DyninMityaginSpace.basis j) (DyninMityaginSpace.basis i) := by
      intro n
      rw [h_symm_seq n f (DyninMityaginSpace.basis j)]
      simpa using DyninMityaginSpace.expansion (B_seq n (DyninMityaginSpace.basis j)) f
    have h_expand_lim :
        B f (DyninMityaginSpace.basis j) =
          ∑' i : ℕ,
            DyninMityaginSpace.coeff i f *
              B (DyninMityaginSpace.basis j) (DyninMityaginSpace.basis i) := by
      rw [h_symm f (DyninMityaginSpace.basis j)]
      simpa using DyninMityaginSpace.expansion (B (DyninMityaginSpace.basis j)) f
    simp_rw [h_expand_seq]
    rw [h_expand_lim]
    apply tendsto_tsum_of_dominated_convergence
      (bound := fun i : ℕ =>
        |DyninMityaginSpace.coeff i f| *
          (C * (1 + (j : ℝ)) ^ s_left * (1 + (i : ℝ)) ^ s_right))
    · exact (summable_coeff_mul_pow f s_right).mul_left (C * (1 + (j : ℝ)) ^ s_left) |>.congr
        (fun i => by ring)
    · intro i
      apply Tendsto.const_mul
      exact h_basis_tendsto j i
    · filter_upwards [h_bound_eventually] with n hn i
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hn j i) (abs_nonneg _)
  have h_expand_g :
      ∀ n,
        B_seq n f g =
          ∑' j : ℕ,
            DyninMityaginSpace.coeff j g *
              B_seq n f (DyninMityaginSpace.basis j) := by
    intro n
    simpa using DyninMityaginSpace.expansion (B_seq n f) g
  have h_expand_lim_g :
      B f g =
        ∑' j : ℕ,
          DyninMityaginSpace.coeff j g *
            B f (DyninMityaginSpace.basis j) := by
    simpa using DyninMityaginSpace.expansion (B f) g
  obtain ⟨C_f, hC_f_pos, hC_f_bound⟩ := h_right_basis_bound f
  simp_rw [h_expand_g]
  rw [h_expand_lim_g]
  apply tendsto_tsum_of_dominated_convergence
    (bound := fun j : ℕ =>
      |DyninMityaginSpace.coeff j g| * (C_f * (1 + (j : ℝ)) ^ s_left))
  · exact (summable_coeff_mul_pow g s_left).mul_left C_f |>.congr (fun j => by ring)
  · intro j
    apply Tendsto.const_mul
    exact h_right_basis_tendsto f j
  · filter_upwards [hC_f_bound] with n hn j
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hn j) (abs_nonneg _)

end

end GaussianField
