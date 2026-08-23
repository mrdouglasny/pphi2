/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.AsymTorus.AsymFreeSpectral
import Pphi2.AsymTorus.AsymVarianceAssembly
import Pphi2.AsymTorus.AsymSignedSplit
import GaussianField.DensityAsym

/-!
# Entrywise nonnegativity of the free lattice covariance (asym torus)

The free covariance on the asymmetric lattice is `(a²)⁻¹·⟨f, Q⁻¹g⟩` with
`Q = -Δ_a + m²`. `Q` is a **Stieltjes matrix**: symmetric positive definite with
nonpositive off-diagonal entries (the neighbor hopping `-1/a²`), hence `Q⁻¹ ≥ 0`
entrywise. We prove the quadratic-form consequence directly via the classical
maximum-principle truncation argument (series-free equivalent of the
Neumann/random-walk expansion `Q⁻¹ = Σ_k D⁻¹(A D⁻¹)^k`): if `Qu = g` with
`g ≥ 0`, testing `Qu = g` against `u₋ = max(-u,0)` gives
`0 ≤ ⟨u₋,g⟩ = ⟨u₋,Qu₊⟩ - ⟨u₋,Qu₋⟩ ≤ -⟨u₋,Qu₋⟩`, so `u₋ = 0` by positive
definiteness (the cross term is `≤ 0` since off-diagonal `Q ≤ 0` and
`u₊·u₋ = 0` sitewise).

## Main results

- `massOperatorMatrixAsym_offdiag_nonpos` — `Q` has nonpositive off-diagonal
  entries (`Z`-matrix property), for every `Nt, Ns` (degenerate small tori
  included: hopping that wraps onto the diagonal only helps).
- `massOperatorAsym_solution_nonneg` — the maximum principle: `Qu = g`, `g ≥ 0`
  sitewise ⟹ `u ≥ 0` sitewise.
- `latticeCovarianceAsymGJ_pairing_nonneg` — **the kernel positivity**: for
  sitewise `0 ≤ f, g`, `0 ≤ covariance (latticeCovarianceAsymGJ) f g`.
- `asymFreeVariance_posPart_add_negPart_le` — the split-variance consequence:
  `Var_free(f₊) + Var_free(f₋) ≤ Var_free(|f|)` (the cross term
  `2·Cov_free(f₊,f₋)` is nonnegative).
- `asymInteracting_expMoment_absForm_thresholded` — the `|f|`-form exp-moment
  corollary: signed-split Layer A + thresholded Layer B2 + kernel positivity
  give `∫ e^{|⟨ω,f⟩|} dμ_int ≤ 2·exp(C·Var_free(|f|))` under the Stage-C
  thresholds. This is the honest `|f|`-seminorm restatement target flagged in
  `AXIOM_AUDIT.md` (2026-07-13).

## References

Berman-Plemmons, *Nonnegative Matrices in the Mathematical Sciences*, Ch. 6
(M-matrices); Glimm-Jaffe §7.1 (lattice covariance positivity via random walk).
-/

noncomputable section

open MeasureTheory GaussianField

namespace Pphi2

/-! ## The mass operator is a Z-matrix -/

/-- Sitewise nonnegativity of the lattice delta. -/
private lemma asymLatticeDelta_nonneg {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]
    (y z : AsymLatticeSites Nt Ns) : 0 ≤ asymLatticeDelta Nt Ns y z := by
  unfold asymLatticeDelta
  split <;> norm_num

/-- **Z-matrix property**: the off-diagonal entries of the asym mass operator
matrix `Q = -Δ_a + m²` are nonpositive — they consist only of the neighbor
hopping `-1/a²` terms. Holds for all `Nt, Ns ≥ 1` (on degenerate tori a hopping
term can wrap onto the diagonal, which only removes mass from the off-diagonal
entry). -/
theorem massOperatorMatrixAsym_offdiag_nonpos (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) {x y : AsymLatticeSites Nt Ns} (hxy : x ≠ y) :
    massOperatorMatrixAsym Nt Ns a mass x y ≤ 0 := by
  have hδx : asymLatticeDelta Nt Ns y x = 0 := by
    unfold asymLatticeDelta
    simp [hxy]
  show massOperatorEntryAsym Nt Ns a mass x y ≤ 0
  unfold massOperatorEntryAsym
  simp only [massOperatorAsym, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
    smul_eq_mul]
  have hlap : (finiteLaplacianAsym Nt Ns a (asymLatticeDelta Nt Ns y)) x =
      finiteLaplacianAsymFun Nt Ns a (asymLatticeDelta Nt Ns y) x := rfl
  rw [hlap]
  unfold finiteLaplacianAsymFun
  rw [hδx]
  have h1 := asymLatticeDelta_nonneg y ((x.1 + 1, x.2) : AsymLatticeSites Nt Ns)
  have h2 := asymLatticeDelta_nonneg y ((x.1 - 1, x.2) : AsymLatticeSites Nt Ns)
  have h3 := asymLatticeDelta_nonneg y ((x.1, x.2 + 1) : AsymLatticeSites Nt Ns)
  have h4 := asymLatticeDelta_nonneg y ((x.1, x.2 - 1) : AsymLatticeSites Nt Ns)
  have ha2 : (0 : ℝ) ≤ a⁻¹ ^ 2 := sq_nonneg _
  nlinarith

/-! ## The maximum principle -/

/-- **Maximum principle for the lattice mass operator** (Stieltjes matrix inverse
positivity, quadratic-form form): if `Qu = g` sitewise with `g ≥ 0`, then
`u ≥ 0`. Test `Qu = g` against `u₋ = max(-u, 0)`: the cross term `⟨u₋, Qu₊⟩`
is nonpositive (off-diagonal `Q ≤ 0`; diagonal killed by `u₊·u₋ = 0`), so
`0 ≤ ⟨u₋, g⟩ ≤ -⟨u₋, Qu₋⟩` forces `u₋ = 0` by positive definiteness. -/
theorem massOperatorAsym_solution_nonneg (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    {u g : AsymLatticeField Nt Ns}
    (hMu : massOperatorAsym Nt Ns a mass u = g)
    (hg : ∀ z, 0 ≤ g z) : ∀ x, 0 ≤ u x := by
  classical
  set M := massOperatorAsym Nt Ns a mass with hM_def
  set up : AsymLatticeField Nt Ns := fun z => max (u z) 0 with hup_def
  set um : AsymLatticeField Nt Ns := fun z => max (-(u z)) 0 with hum_def
  have hup_nn : ∀ z, 0 ≤ up z := fun z => le_max_right _ _
  have hum_nn : ∀ z, 0 ≤ um z := fun z => le_max_right _ _
  have hdisj : ∀ z, um z * up z = 0 := by
    intro z
    rcases le_total (u z) 0 with h | h
    · have hz : up z = 0 := max_eq_right h
      rw [hz, mul_zero]
    · have hz : um z = 0 := max_eq_right (by linarith : -(u z) ≤ (0 : ℝ))
      rw [hz, zero_mul]
  have hsplit : u = up - um := by
    funext z
    simp only [Pi.sub_apply, hup_def, hum_def]
    rcases le_total (u z) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith : (0 : ℝ) ≤ -(u z))]
      ring
    · rw [max_eq_left h, max_eq_right (by linarith : -(u z) ≤ (0 : ℝ))]
      ring
  -- The negative part vanishes.
  have hum_zero : um = 0 := by
    by_contra hne
    have hQpos : 0 < ∑ z, um z * (M um) z :=
      massOperatorAsym_pos_def Nt Ns a mass ha hmass um hne
    have hpair_g : (0 : ℝ) ≤ ∑ z, um z * g z :=
      Finset.sum_nonneg fun z _ => mul_nonneg (hum_nn z) (hg z)
    -- Cross term `⟨u₋, Q u₊⟩ ≤ 0`.
    have hcross : ∑ z, um z * (M up) z ≤ 0 := by
      have hexp : ∀ z, (M up) z =
          ∑ w, massOperatorMatrixAsym Nt Ns a mass z w * up w := by
        intro z
        rw [hM_def, massOperatorAsym_eq_matrix_mulVec Nt Ns a mass up z]
        rfl
      calc ∑ z, um z * (M up) z
          = ∑ z, ∑ w, um z * (massOperatorMatrixAsym Nt Ns a mass z w * up w) := by
            refine Finset.sum_congr rfl fun z _ => ?_
            rw [hexp z, Finset.mul_sum]
        _ ≤ 0 := by
            refine Finset.sum_nonpos fun z _ => Finset.sum_nonpos fun w _ => ?_
            by_cases hzw : z = w
            · subst hzw
              rcases mul_eq_zero.mp (hdisj z) with h | h
              · simp [h]
              · simp [h]
            · have hM_np : massOperatorMatrixAsym Nt Ns a mass z w ≤ 0 :=
                massOperatorMatrixAsym_offdiag_nonpos Nt Ns a mass hzw
              have hinner : massOperatorMatrixAsym Nt Ns a mass z w * up w ≤ 0 :=
                mul_nonpos_iff.mpr (Or.inr ⟨hM_np, hup_nn w⟩)
              exact mul_nonpos_iff.mpr (Or.inl ⟨hum_nn z, hinner⟩)
    -- Decompose `⟨u₋, g⟩ = ⟨u₋, Qu₊⟩ − ⟨u₋, Qu₋⟩`.
    have hdecomp : ∑ z, um z * g z =
        (∑ z, um z * (M up) z) - ∑ z, um z * (M um) z := by
      rw [← hMu]
      have hMsplit : M u = M up - M um := by
        rw [hsplit, map_sub]
      rw [hMsplit, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp only [Pi.sub_apply]
      ring
    linarith
  -- Conclude sitewise nonnegativity.
  intro x
  have hx := congrFun hum_zero x
  simp only [hum_def, Pi.zero_apply] at hx
  have hle := le_max_left (-(u x)) (0 : ℝ)
  rw [hx] at hle
  linarith

/-! ## The spectral Green operator -/

/-- The inverse `Q⁻¹g` of the mass operator, in spectral form:
`(Q⁻¹g)(y) = Σ_k λ_k⁻¹·c_k(g)·e_k(y)`. -/
def asymMassGreen (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ)
    (g : AsymLatticeField Nt Ns) : AsymLatticeField Nt Ns :=
  fun y => ∑ k : AsymLatticeSites Nt Ns,
    (massEigenvaluesAsym Nt Ns a mass k)⁻¹ * asymModeCoeff Nt Ns a mass k g *
      (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) y

/-- Mode coefficients of the spectral Green operator: `c_k(Q⁻¹g) = λ_k⁻¹·c_k(g)`. -/
theorem asymModeCoeff_asymMassGreen (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (g : AsymLatticeField Nt Ns) (k : AsymLatticeSites Nt Ns) :
    asymModeCoeff Nt Ns a mass k (asymMassGreen Nt Ns a mass g) =
      (massEigenvaluesAsym Nt Ns a mass k)⁻¹ * asymModeCoeff Nt Ns a mass k g := by
  unfold asymModeCoeff asymMassGreen
  calc
    ∑ x : AsymLatticeSites Nt Ns,
        (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x *
        ∑ l : AsymLatticeSites Nt Ns,
          (massEigenvaluesAsym Nt Ns a mass l)⁻¹ *
            (∑ x' : AsymLatticeSites Nt Ns,
              (massEigenvectorBasisAsym Nt Ns a mass l : EuclideanSpace ℝ _) x' * g x') *
            (massEigenvectorBasisAsym Nt Ns a mass l : EuclideanSpace ℝ _) x
      = ∑ l : AsymLatticeSites Nt Ns,
          (massEigenvaluesAsym Nt Ns a mass l)⁻¹ *
            (∑ x' : AsymLatticeSites Nt Ns,
              (massEigenvectorBasisAsym Nt Ns a mass l : EuclideanSpace ℝ _) x' * g x') *
            ∑ x : AsymLatticeSites Nt Ns,
              (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x *
              (massEigenvectorBasisAsym Nt Ns a mass l : EuclideanSpace ℝ _) x := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        exact Finset.sum_congr rfl fun x _ => by ring
    _ = (massEigenvaluesAsym Nt Ns a mass k)⁻¹ *
          ∑ x' : AsymLatticeSites Nt Ns,
            (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x' * g x' := by
        simp_rw [massEigenvectorBasisAsym_orthogonal Nt Ns a mass]
        rw [Finset.sum_congr rfl fun l _ => by
          rw [mul_ite, mul_one, mul_zero]]
        simp [eq_comm]

/-- The spectral Green operator inverts the mass operator: `Q(Q⁻¹g) = g`. -/
theorem massOperatorAsym_asymMassGreen (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (g : AsymLatticeField Nt Ns) :
    massOperatorAsym Nt Ns a mass (asymMassGreen Nt Ns a mass g) = g := by
  funext y
  have hexpand := sum_asymModeCoeff_mul_eigenvector Nt Ns a mass
    (massOperatorAsym Nt Ns a mass (asymMassGreen Nt Ns a mass g)) y
  have hg_expand := sum_asymModeCoeff_mul_eigenvector Nt Ns a mass g y
  rw [← hexpand]
  conv_rhs => rw [← hg_expand]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  have hlam : massEigenvaluesAsym Nt Ns a mass k ≠ 0 :=
    (massOperatorMatrixAsym_eigenvalues_pos Nt Ns a mass ha hmass k).ne'
  have h1 : asymModeCoeff Nt Ns a mass k
      (massOperatorAsym Nt Ns a mass (asymMassGreen Nt Ns a mass g)) =
      massEigenvaluesAsym Nt Ns a mass k *
        asymModeCoeff Nt Ns a mass k (asymMassGreen Nt Ns a mass g) :=
    massOperatorAsym_eigenCoeff_eq_eigenvalues_mul_eigenCoeff Nt Ns a mass _ k
  rw [h1, asymModeCoeff_asymMassGreen, ← mul_assoc, mul_inv_cancel₀ hlam, one_mul]

/-- The spectral Green operator preserves sitewise nonnegativity (maximum
principle applied to the spectral solution of `Qu = g`). -/
theorem asymMassGreen_nonneg (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (g : AsymLatticeField Nt Ns) (hg : ∀ z, 0 ≤ g z) :
    ∀ x, 0 ≤ asymMassGreen Nt Ns a mass g x :=
  massOperatorAsym_solution_nonneg Nt Ns a mass ha hmass
    (massOperatorAsym_asymMassGreen Nt Ns a mass ha hmass g) hg

/-! ## Kernel positivity of the free covariance -/

/-- **Entrywise nonnegativity of the free lattice covariance** (pairing form):
for sitewise nonnegative `f, g`, the GJ covariance pairing is nonnegative,
`0 ≤ covariance (latticeCovarianceAsymGJ) f g = (a²)⁻¹·⟨f, Q⁻¹g⟩`.
Combines the spectral form of the covariance with the maximum principle for
`Q⁻¹g` and Parseval. -/
theorem latticeCovarianceAsymGJ_pairing_nonneg (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f g : AsymLatticeField Nt Ns) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    0 ≤ GaussianField.covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass) f g := by
  rw [lattice_covariance_AsymGJ_eq_spectral Nt Ns a mass ha hmass f g]
  set u : AsymLatticeField Nt Ns := asymMassGreen Nt Ns a mass g with hu_def
  have hu : ∀ x, 0 ≤ u x := asymMassGreen_nonneg Nt Ns a mass ha hmass g hg
  have hspec : ∑ k : AsymLatticeSites Nt Ns,
      (massEigenvaluesAsym Nt Ns a mass k)⁻¹ *
      (∑ x, (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * f x) *
      (∑ x, (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * g x) =
      ∑ x : AsymLatticeSites Nt Ns, f x * u x := by
    rw [← massEigenbasisAsym_sum_mul_sum_eq_site_inner Nt Ns a mass f u]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hck : (∑ x, (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * u x) =
        (massEigenvaluesAsym Nt Ns a mass k)⁻¹ *
        (∑ x, (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * g x) :=
      asymModeCoeff_asymMassGreen Nt Ns a mass g k
    rw [hck]
    ring
  rw [hspec]
  exact mul_nonneg (inv_nonneg.mpr (sq_nonneg a))
    (Finset.sum_nonneg fun x _ => mul_nonneg (hf x) (hu x))

/-- Cross-moment form of the kernel positivity: for sitewise nonnegative `f, g`,
`0 ≤ ∫ ⟨ω,f⟩·⟨ω,g⟩ dμ_free`. -/
theorem asymFreeCrossMoment_nonneg (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f g : AsymLatticeField Nt Ns) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    0 ≤ ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω f) * (ω g) ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
  rw [latticeGaussianMeasureAsym_cross_moment Nt Ns a mass ha hmass f g]
  exact latticeCovarianceAsymGJ_pairing_nonneg Nt Ns a mass ha hmass f g hf hg

/-! ## The split-variance consequence -/

/-- **Split free variance is dominated by the `|f|`-variance**:
`Var_free(f₊) + Var_free(f₋) ≤ Var_free(|f|)` with `f₊ = max f 0`,
`f₋ = max (-f) 0`. Pure bilinearity from the kernel positivity:
`Var(|f|) = Var(f₊) + Var(f₋) + 2·Cov(f₊,f₋)` and `Cov(f₊,f₋) ≥ 0`. -/
theorem asymFreeVariance_posPart_add_negPart_le (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (f : AsymLatticeField Nt Ns) :
    (∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω (fun x => max (f x) 0)) ^ 2
        ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) +
      (∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω (fun x => max (-(f x)) 0)) ^ 2
        ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) ≤
    ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω (fun x => |f x|)) ^ 2
        ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
  set fp : AsymLatticeField Nt Ns := fun x => max (f x) 0 with hfp_def
  set fm : AsymLatticeField Nt Ns := fun x => max (-(f x)) 0 with hfm_def
  have hfp_nn : ∀ x, 0 ≤ fp x := fun x => le_max_right _ _
  have hfm_nn : ∀ x, 0 ≤ fm x := fun x => le_max_right _ _
  have habs : (fun x => |f x|) = fp + fm := by
    funext x
    simp only [Pi.add_apply, hfp_def, hfm_def]
    rcases le_total (f x) 0 with h | h
    · rw [abs_of_nonpos h, max_eq_right h,
        max_eq_left (by linarith : (0 : ℝ) ≤ -(f x))]
      ring
    · rw [abs_of_nonneg h, max_eq_left h,
        max_eq_right (by linarith : -(f x) ≤ (0 : ℝ))]
      ring
  -- Second moments as covariance pairings.
  have hVar : ∀ h : AsymLatticeField Nt Ns,
      ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω h) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) =
      GaussianField.covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass) h h := by
    intro h
    simp_rw [sq]
    exact latticeGaussianMeasureAsym_cross_moment Nt Ns a mass ha hmass h h
  rw [hVar fp, hVar fm, habs, hVar (fp + fm)]
  -- Bilinear expansion of the covariance.
  have hbilin : GaussianField.covariance
      (latticeCovarianceAsymGJ Nt Ns a mass ha hmass) (fp + fm) (fp + fm) =
      GaussianField.covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass) fp fp +
      2 * GaussianField.covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass) fp fm +
      GaussianField.covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass) fm fm := by
    unfold GaussianField.covariance
    rw [map_add]
    exact real_inner_add_add_self _ _
  have hcross : 0 ≤ GaussianField.covariance
      (latticeCovarianceAsymGJ Nt Ns a mass ha hmass) fp fm :=
    latticeCovarianceAsymGJ_pairing_nonneg Nt Ns a mass ha hmass fp fm hfp_nn hfm_nn
  rw [hbilin]
  linarith

/-! ## The `|f|`-form exp-moment corollary (thresholded) -/

/-- **`|f|`-form exp-moment bound, thresholded.** Composing the signed-split
Layer A bound (`asymInteracting_expMoment_of_signed`), the thresholded Layer B2
variance comparison (`asymInteractingVariance_le_freeVariance_lattice_thresholded`)
and the kernel positivity (`asymFreeVariance_posPart_add_negPart_le`):
at fixed `Ls = Ns·a`, there are `C, L₀, a₀ > 0` such that for all lattices with
`a ≤ a₀`, `Nt·a ≥ L₀`, and every (signed) lattice test function `f`,

`∫ e^{|⟨ω,f⟩|} dμ_int ≤ 2·exp(C·Var_free(|f|))`.

This theorem inherits `P.n = 4` from the Layer A and FSS inputs.

This is the honest `|f|`-seminorm form of the pre-2026-07-13 conclusion
`C·Var_free(f)` — the split variances collapse into the single `|f|`-variance
via `Var_free(f₊) + Var_free(f₋) ≤ Var_free(|f|)`. -/
theorem asymInteracting_expMoment_absForm_thresholded
    (P : InteractionPolynomial) (hP : P.n = 4) (mass : ℝ) (hmass : 0 < mass)
    (Ls : ℝ) (hLs : 0 < Ls) :
    ∃ C L₀ a₀ : ℝ, 0 < C ∧ 0 < L₀ ∧ 0 < a₀ ∧
      ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
        (Ns : ℝ) * a = Ls → a ≤ a₀ → L₀ ≤ (Nt : ℝ) * a →
        ∀ f : AsymLatticeField Nt Ns,
          Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
              Real.exp (|ω f|))
            (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ∧
          ∫ ω : Configuration (AsymLatticeField Nt Ns), Real.exp (|ω f|)
              ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ≤
          2 * Real.exp (C *
            ∫ ω : Configuration (AsymLatticeField Nt Ns),
              (ω (fun x => |f x|)) ^ 2
              ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) := by
  obtain ⟨C, L₀, a₀, hC, hL₀, ha₀, hB⟩ :=
    asymInteractingVariance_le_freeVariance_lattice_thresholded P hP mass hmass Ls hLs
  refine ⟨C, L₀, a₀, hC, hL₀, ha₀, ?_⟩
  intro Nt Ns _ _ a ha hvols haa hLta f
  obtain ⟨hint, hbound⟩ :=
    asymInteracting_expMoment_of_signed Nt Ns P hP mass hmass a ha f
  refine ⟨hint, hbound.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  set fp : AsymLatticeField Nt Ns := fun x => max (f x) 0
  set fm : AsymLatticeField Nt Ns := fun x => max (-(f x)) 0
  -- Layer B2 (thresholded) at `f₊` and `f₋`.
  have hBp := hB Nt Ns a ha hvols haa hLta fp
  have hBm := hB Nt Ns a ha hvols haa hLta fm
  -- Kernel positivity: split free variances collapse into the `|f|`-variance.
  have hsplit := asymFreeVariance_posPart_add_negPart_le Nt Ns a mass ha hmass f
  calc (∫ ω : Configuration (AsymLatticeField Nt Ns),
          (ω fp) ^ 2 ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass)) +
        (∫ ω : Configuration (AsymLatticeField Nt Ns),
          (ω fm) ^ 2 ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass))
      ≤ C * (∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω fp) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) +
        C * (∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω fm) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) :=
        add_le_add hBp hBm
    _ = C * ((∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω fp) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) +
          (∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω fm) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass))) := by
        ring
    _ ≤ C * ∫ ω : Configuration (AsymLatticeField Nt Ns),
          (ω (fun x => |f x|)) ^ 2
          ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) :=
        mul_le_mul_of_nonneg_left hsplit hC.le

/-! ## The torus-level `|f|`-form exp-moment (Piece-5 pushforward) -/

/-- **Torus-level `|f|`-form exp-moment bound, thresholded.** This inherits
`P.n = 4` from the lattice theorem. The honest thresholded
`|f|`-seminorm restatement of the legacy torus axiom
`asymInteracting_expMoment_volume_uniform` (`AsymContinuumLimit.lean`): there are
`K, C, L₀, a₀ > 0` — depending only on `(P, mass, Ls)`, uniform in the time period `Lt`
and the lattice `(Nt, Ns, a)` — such that for every asymmetric torus with `Nt·a = Lt ≥ L₀`,
`Ns·a = Ls`, `a ≤ a₀`, and every (signed) torus test function `f`,

`∫ e^{|ω f|} dμ̃_int ≤ K · exp(C · Var_free(|g|))`,    `g = asymLatticeTestFnIso f`,

where `Var_free(|g|)` is the free lattice second moment at the **sitewise absolute value**
of the pulled-back lattice test vector. Compared to the legacy axiom the differences are
(i) the `(a₀, L₀)` Stage-C thresholds and (ii) the `|g|`-seminorm on the right (the exact
`C·Var_free(g)` form for signed `g` is not recoverable from the signed split — cross-term
cancellation; see `AXIOM_AUDIT.md` 2026-07-13).

Proved from the lattice theorem `asymInteracting_expMoment_absForm_thresholded` by the
same Piece-5 pushforward + pairing argument as
`asymInteractingVariance_le_freeVariance_torus_thresholded` (push the torus interacting
measure back along `asymTorusEmbedLiftIso` via `integral_map`/`integrable_map_measure`
and rewrite the torus pairing as the lattice pairing against `asymLatticeTestFnIso`),
applied to the exp-integrand instead of the square. -/
theorem asymInteracting_expMoment_volume_uniform_absForm_thresholded
    (P : InteractionPolynomial) (hP : P.n = 4) (mass : ℝ) (hmass : 0 < mass)
    (Ls : ℝ) [Fact (0 < Ls)] :
    ∃ K C L₀ a₀ : ℝ, 0 < K ∧ 0 < C ∧ 0 < L₀ ∧ 0 < a₀ ∧
      ∀ (Lt : ℝ) [Fact (0 < Lt)]
        (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
        (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls → a ≤ a₀ → L₀ ≤ Lt →
        ∀ f : AsymTorusTestFunction Lt Ls,
          Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
              Real.exp (|ω f|))
            (asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) ∧
          ∫ ω : Configuration (AsymTorusTestFunction Lt Ls), Real.exp (|ω f|)
              ∂(asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) ≤
          K * Real.exp (C * ∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω (fun x => |asymLatticeTestFnIso Lt Ls Nt Ns a f x|)) ^ 2
            ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) := by
  obtain ⟨C, L₀, a₀, hC, hL₀, ha₀, hLat⟩ :=
    asymInteracting_expMoment_absForm_thresholded P hP mass hmass Ls Fact.out
  refine ⟨2, C, L₀, a₀, by norm_num, hC, hL₀, ha₀, ?_⟩
  intro Lt _hLt Nt Ns _ _ a ha hvolt hvols haa hLtb f
  have hLta' : L₀ ≤ (Nt : ℝ) * a := by rw [hvolt]; exact hLtb
  set μ_int := interactingLatticeMeasureAsym Nt Ns P a mass ha hmass
  set ι := asymTorusEmbedLiftIso Lt Ls Nt Ns a
  set g := asymLatticeTestFnIso Lt Ls Nt Ns a f with hg_def
  have hι_meas : AEMeasurable ι μ_int :=
    (asymTorusEmbedLiftIso_measurable Lt Ls Nt Ns a).aemeasurable
  have h_eval : ∀ ω : Configuration (AsymLatticeField Nt Ns), (ι ω) f = ω g :=
    fun ω => asymTorusEmbedLiftIso_eval_eq Lt Ls Nt Ns a f ω
  have hmeas_lhs : AEStronglyMeasurable
      (fun ω : Configuration (AsymTorusTestFunction Lt Ls) => Real.exp (|ω f|))
      (Measure.map ι μ_int) :=
    (Real.measurable_exp.comp (configuration_eval_measurable f).abs).aestronglyMeasurable
  have h_pushforward : asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass =
      Measure.map ι μ_int := rfl
  rw [h_pushforward, integrable_map_measure hmeas_lhs hι_meas, integral_map hι_meas hmeas_lhs]
  simp_rw [Function.comp_def, h_eval]
  exact hLat Nt Ns a ha hvols haa hLta' g

end Pphi2

end
