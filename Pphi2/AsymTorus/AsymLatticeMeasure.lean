/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Heterogeneous isotropic lattice measures (Z_Nt × Z_Ns)

The Gaussian (and, downstream, interacting) P(φ)₂ measures on the *heterogeneous* lattice
`AsymLatticeField Nt Ns = ZMod Nt × ZMod Ns → ℝ` with a **single isotropic spacing `a`**
(`a = Lt/Nt = Ls/Ns`). This is the metric-correct replacement for the square
`FinLatticeField 2 N` + geometric-mean-spacing construction: the covariance is
`latticeCovarianceAsymGJ` from gaussian-field, whose lattice→continuum limit is the correct
rectangular-torus Green's function (`lattice_green_tendsto_continuum_asym`), so the rectangle
`Nt ≠ Ns` is carried by the boundary condition, not a distorted metric.

## Main definitions

- `latticeGaussianMeasureAsym` — centered GJ-normalized Gaussian measure on
  `Configuration (AsymLatticeField Nt Ns)`, covariance `latticeCovarianceAsymGJ`.

## Design

Mirrors gaussian-field's square `latticeGaussianMeasure`, with `FinLatticeField d N`
replaced by `AsymLatticeField Nt Ns` and the isotropic covariance. The cell area is `a²`
and the volume `Nt·Ns·a² = Lt·Ls`, so the `d = 2` Glimm–Jaffe normalisation factor is
`(a²)^{-1/2} = 1/a` (built into `latticeCovarianceAsymGJ`).
-/

import Lattice.AsymCovariance

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

/-! ## DyninMityaginSpace instance for the heterogeneous lattice field

`AsymLatticeField Nt Ns ≅ ℝ^(Nt·Ns)` is trivially nuclear. Port of gaussian-field's
`finLatticeField_dyninMityaginSpace`, generic over the finite index type — only the Fintype
structure of `AsymLatticeSites Nt Ns` is used. Needed so `GaussianField.measure` /
`measure_isProbability` apply on the heterogeneous lattice. -/

/-- Enumeration of heterogeneous lattice sites via Fintype. -/
private noncomputable def asymLatticeSiteEnum (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    AsymLatticeSites Nt Ns ≃ Fin (Fintype.card (AsymLatticeSites Nt Ns)) :=
  Fintype.equivFin _

/-- The m-th basis vector: delta at the m-th site (or zero if `m ≥ |sites|`). -/
def asymLatticeBasisVec (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (m : ℕ) :
    AsymLatticeField Nt Ns :=
  if h : m < Fintype.card (AsymLatticeSites Nt Ns) then
    asymLatticeDelta Nt Ns ((asymLatticeSiteEnum Nt Ns).symm ⟨m, h⟩)
  else 0

/-- The m-th coefficient: evaluation at the m-th site (or zero if `m ≥ |sites|`). -/
def asymLatticeCoeffCLM (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (m : ℕ) :
    AsymLatticeField Nt Ns →L[ℝ] ℝ :=
  if h : m < Fintype.card (AsymLatticeSites Nt Ns) then
    { toLinearMap :=
      { toFun := fun f => f ((asymLatticeSiteEnum Nt Ns).symm ⟨m, h⟩)
        map_add' := fun _ _ => rfl
        map_smul' := fun r f => by simp [smul_eq_mul] }
      cont := continuous_apply _ }
  else 0

/-- The sup-norm seminorm on the heterogeneous lattice field. -/
def asymLatticeSeminorm (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    Seminorm ℝ (AsymLatticeField Nt Ns) where
  toFun f := Finset.univ.sup' Finset.univ_nonempty (fun x => ‖f x‖₊)
  map_zero' := by simp
  add_le' f g := by
    apply Finset.sup'_le _ _ (fun x hx => ?_)
    calc (↑‖(f + g) x‖₊ : ℝ)
        ≤ ↑‖f x‖₊ + ↑‖g x‖₊ := by exact_mod_cast nnnorm_add_le (f x) (g x)
      _ ≤ _ := add_le_add
          (Finset.le_sup' (fun y => (↑‖f y‖₊ : ℝ)) hx)
          (Finset.le_sup' (fun y => (↑‖g y‖₊ : ℝ)) hx)
  neg' f := by simp [Pi.neg_apply, nnnorm_neg]
  smul' r f := by
    simp only [Pi.smul_apply, smul_eq_mul, nnnorm_mul, NNReal.coe_mul]
    simp only [show (↑‖r‖₊ : ℝ) = ‖r‖ from rfl]
    have := Finset.comp_sup'_eq_sup'_comp (s := Finset.univ)
      Finset.univ_nonempty (f := fun x => (↑‖f x‖₊ : ℝ)) (g := (‖r‖ * ·))
      (fun _ _ => mul_max_of_nonneg _ _ (norm_nonneg r))
    simp only [Function.comp] at this
    exact this.symm

/-- The DyninMityaginSpace instance for heterogeneous lattice fields (delta basis,
point evaluations as coefficients; `f = ∑_x f(x)·δ_x`). -/
noncomputable instance asymLatticeField_dyninMityaginSpace (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    DyninMityaginSpace (AsymLatticeField Nt Ns) where
  ι := Unit
  p := fun _ => asymLatticeSeminorm Nt Ns
  h_countable := inferInstance
  h_completeSpace := by
    have heq : (IsTopologicalAddGroup.rightUniformSpace (AsymLatticeField Nt Ns)) =
        (Pi.uniformSpace (fun _ : AsymLatticeSites Nt Ns => ℝ)) :=
      IsUniformAddGroup.rightUniformSpace_eq
    exact heq ▸ inferInstance
  h_with := by
    rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf]
    simp only [iInf_const]
    have hfun : ⇑(asymLatticeSeminorm Nt Ns) = (norm : AsymLatticeField Nt Ns → ℝ) := by
      ext f; unfold asymLatticeSeminorm
      change (Finset.univ.sup' Finset.univ_nonempty fun x => (↑‖f x‖₊ : ℝ)) = ‖f‖
      rw [Pi.norm_def]
      have h1 : Finset.univ.sup' Finset.univ_nonempty
            (fun x : AsymLatticeSites Nt Ns => (↑‖f x‖₊ : ℝ)) =
          ↑(Finset.univ.sup' Finset.univ_nonempty
            (fun x : AsymLatticeSites Nt Ns => ‖f x‖₊)) :=
        (Finset.comp_sup'_eq_sup'_comp Finset.univ_nonempty
          (g := NNReal.toReal)
          (fun a b => NNReal.coe_mono.map_sup a b)).symm
      rw [h1]
      exact congrArg NNReal.toReal
        (Finset.sup'_eq_sup Finset.univ_nonempty (fun x : AsymLatticeSites Nt Ns => ‖f x‖₊))
    rw [hfun, comap_norm_nhds_zero]
  basis := asymLatticeBasisVec Nt Ns
  coeff := asymLatticeCoeffCLM Nt Ns
  expansion := fun φ f => by
    set C := Fintype.card (AsymLatticeSites Nt Ns) with hC_def
    have hvanish : ∀ m, ¬(m < C) →
        (asymLatticeCoeffCLM Nt Ns m) f * φ (asymLatticeBasisVec Nt Ns m) = 0 := by
      intro m hm
      unfold asymLatticeCoeffCLM asymLatticeBasisVec
      simp only [show ¬(m < Fintype.card (AsymLatticeSites Nt Ns)) from hm, dite_false,
        ContinuousLinearMap.zero_apply, map_zero, mul_zero]
    rw [tsum_eq_sum (s := Finset.range C) (fun m hm => by
      simp only [Finset.mem_range, not_lt] at hm
      exact hvanish m (not_lt.mpr hm))]
    have : ∀ m ∈ Finset.range C,
        (asymLatticeCoeffCLM Nt Ns m) f * φ (asymLatticeBasisVec Nt Ns m) =
        φ ((asymLatticeCoeffCLM Nt Ns m) f • asymLatticeBasisVec Nt Ns m) := by
      intro m _
      rw [map_smul, smul_eq_mul]
    rw [Finset.sum_congr rfl this, ← map_sum]
    congr 1
    ext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    obtain ⟨⟨m, hm⟩, rfl⟩ := (asymLatticeSiteEnum Nt Ns).symm.surjective x
    have hmain : (Finset.range C).sum
        (fun b => (asymLatticeCoeffCLM Nt Ns b) f *
          asymLatticeBasisVec Nt Ns b ((asymLatticeSiteEnum Nt Ns).symm ⟨m, hm⟩)) =
        (asymLatticeCoeffCLM Nt Ns m) f *
          asymLatticeBasisVec Nt Ns m ((asymLatticeSiteEnum Nt Ns).symm ⟨m, hm⟩) := by
      apply Finset.sum_eq_single
      · intro b hb hbm
        have hblt : b < Fintype.card (AsymLatticeSites Nt Ns) := Finset.mem_range.mp hb
        simp only [asymLatticeBasisVec, asymLatticeDelta, hblt, dite_true]
        rw [if_neg]
        · ring
        · intro heq
          exact hbm ((Fin.val_eq_of_eq ((asymLatticeSiteEnum Nt Ns).symm.injective heq)).symm)
      · intro hm'
        exact absurd (Finset.mem_range.mpr hm) hm'
    rw [hmain]
    have hm' : m < Nt * Ns := by
      rwa [show Fintype.card (AsymLatticeSites Nt Ns) = Nt * Ns from by simp] at hm
    simp [asymLatticeCoeffCLM, asymLatticeBasisVec, asymLatticeDelta, hm']
  basis_growth := fun _ => ⟨1, one_pos, 0, fun m => by
    simp only [pow_zero, mul_one]
    unfold asymLatticeSeminorm asymLatticeBasisVec
    by_cases h : m < Fintype.card (AsymLatticeSites Nt Ns)
    · simp only [h, dite_true]
      apply Finset.sup'_le Finset.univ_nonempty
      intro x _
      simp only [asymLatticeDelta]
      split_ifs with heq
      · simp
      · simp
    · simp only [h, dite_false]
      simp⟩
  coeff_decay := fun k => ⟨(1 + Fintype.card (AsymLatticeSites Nt Ns) : ℝ) ^ k,
    by positivity, {()}, fun f m => by
    simp only [Finset.sup_singleton]
    unfold asymLatticeCoeffCLM asymLatticeSeminorm
    by_cases h : m < Fintype.card (AsymLatticeSites Nt Ns)
    · simp only [h, dite_true, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
      set y := (asymLatticeSiteEnum Nt Ns).symm ⟨m, h⟩
      set sem := Finset.univ.sup' Finset.univ_nonempty (fun x => (↑‖f x‖₊ : ℝ)) with sem_def
      have hnorm_le : (↑‖f y‖₊ : ℝ) ≤ sem :=
        Finset.le_sup' (fun x => (↑‖f x‖₊ : ℝ)) (Finset.mem_univ y)
      have hcoeff : |f y| ≤ sem := by
        calc |f y| = ‖f y‖ := (Real.norm_eq_abs _).symm
          _ ≤ sem := by exact_mod_cast hnorm_le
      have hpow : (1 + (m : ℝ)) ^ k ≤
          (1 + (Fintype.card (AsymLatticeSites Nt Ns) : ℝ)) ^ k := by gcongr
      have hsem_nn : 0 ≤ sem := le_trans (by positivity) hnorm_le
      calc |f y| * (1 + ↑m) ^ k
          ≤ sem * (1 + ↑(Fintype.card (AsymLatticeSites Nt Ns))) ^ k :=
            mul_le_mul hcoeff hpow (by positivity) hsem_nn
        _ = (1 + ↑(Fintype.card (AsymLatticeSites Nt Ns))) ^ k * sem := by ring
    · simp only [h, dite_false, ContinuousLinearMap.zero_apply, abs_zero, zero_mul]
      positivity⟩

/-- The centered Gaussian measure on the heterogeneous isotropic lattice
`ZMod Nt × ZMod Ns` (**Glimm–Jaffe-aligned normalisation**).

Constructed via `GaussianField.measure` from the GJ-aligned isotropic covariance CLM
`latticeCovarianceAsymGJ`. Has covariance kernel `a^{-2} Q⁻¹` (cell area `a²`), so the
lattice two-point function converges to the rectangular continuum Green's function on
`T_{Lt,Ls}` as `a → 0` (`Nt, Ns → ∞`, `Nt/Ns = Lt/Ls`). -/
noncomputable def latticeGaussianMeasureAsym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    @Measure (Configuration (AsymLatticeField Nt Ns)) instMeasurableSpaceConfiguration :=
  GaussianField.measure (latticeCovarianceAsymGJ Nt Ns a mass ha hmass)

/-- The heterogeneous lattice Gaussian measure is a probability measure. -/
instance latticeGaussianMeasureAsym_isProbability (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    @IsProbabilityMeasure (Configuration (AsymLatticeField Nt Ns))
      instMeasurableSpaceConfiguration
      (latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
  unfold latticeGaussianMeasureAsym
  exact GaussianField.measure_isProbability (latticeCovarianceAsymGJ Nt Ns a mass ha hmass)

end Pphi2

end
