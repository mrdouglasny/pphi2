/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Asym cylinder transfer operator: energy levels + mass gap (Layer B1, Phase 3)

Asym analogues of the square energy-level + spectral-gap structures
(`Pphi2/TransferMatrix/Positivity.lean` + `SpectralGap.lean` proved part).
Defines the lattice Hamiltonian `H = -(1/a) log T_asym` and its spectral
data (ground / first-excited energies, mass gap) from the asym
spectral decomposition.

Direct port of the square — same proofs, with `transferOperatorCLM` ⟶
`asymTransferOperatorCLM` and the corresponding `_eigenvalues_pos` /
`_ground_simple_spectral` swap from Phase 2.

## Main declarations

* `AsymTransferGroundExcitedData` — bundled spectral data with
  distinguished ground/first-excited indices.
* `asymTransferGroundExcitedData` — noncomputable choice (via
  `asymTransferOperator_ground_simple_spectral`).
* `asymTransferGroundEigenvalue`, `asymTransferFirstExcitedEigenvalue`.
* `asymGroundEnergyLevel`, `asymFirstExcitedEnergyLevel`.
* `asymEnergyLevel_gap` — `E₀ < E₁`.
* `asymMassGap`, `asymMassGap_pos`.
* `asymSpectral_gap_pos` — alias of `asymMassGap_pos`, for consistency
  with the square's API. The analogue of the open
  `spectral_gap_uniform` axiom is **not** ported here (that's Layer B2,
  out of scope for Phase 3).
-/

import Pphi2.AsymTorus.AsymJentzsch

noncomputable section

open GaussianField Real MeasureTheory

namespace Pphi2

variable (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]

/-! ## Chosen spectral data -/

/-- A packaged spectral decomposition with distinguished ground and
first-excited indices, for the asym cylinder transfer operator. -/
structure AsymTransferGroundExcitedData (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) where
  ι : Type*
  b : HilbertBasis ι ℝ (L2SpatialField Ns)
  eigenval : ι → ℝ
  i₀ : ι
  i₁ : ι
  h_eigen : ∀ i, (asymTransferOperatorCLM Nt Ns P a mass ha hmass :
      L2SpatialField Ns →ₗ[ℝ] L2SpatialField Ns) (b i) = eigenval i • b i
  h_sum : ∀ x, HasSum (fun i => (eigenval i * @inner ℝ _ _ (b i) x) • b i)
      (asymTransferOperatorCLM Nt Ns P a mass ha hmass x)
  hi_ne : i₁ ≠ i₀
  hlt : eigenval i₁ < eigenval i₀
  /-- `i₀` is the Perron-Frobenius top: it strictly dominates every other
  eigenvalue in absolute value, so the ground vector/eigenvalue are genuinely
  the spectral top (not merely above one excited level). -/
  htop : ∀ i, i ≠ i₀ → |eigenval i| < eigenval i₀

/-- A noncomputable choice of asym spectral data with distinguished
ground/first-excited indices. -/
noncomputable def asymTransferGroundExcitedData (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    AsymTransferGroundExcitedData Nt Ns P a mass ha hmass := by
  classical
  exact Classical.choice <| by
    rcases asymTransferOperator_ground_simple_spectral Nt Ns P a mass ha hmass with
      ⟨ι, b, eigenval, i₀, i₁, h_eigen, h_sum, hi_ne, hlt, htop⟩
    exact ⟨{
        ι := ι
        b := b
        eigenval := eigenval
        i₀ := i₀
        i₁ := i₁
        h_eigen := h_eigen
        h_sum := h_sum
        hi_ne := hi_ne
        hlt := hlt
        htop := htop
      }⟩

/-- Ground-state eigenvalue `λ₀` of the asym cylinder transfer operator. -/
noncomputable def asymTransferGroundEigenvalue (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) : ℝ :=
  let d := asymTransferGroundExcitedData Nt Ns P a mass ha hmass
  d.eigenval d.i₀

/-- First excited eigenvalue `λ₁` of the asym cylinder transfer operator. -/
noncomputable def asymTransferFirstExcitedEigenvalue
    (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) : ℝ :=
  let d := asymTransferGroundExcitedData Nt Ns P a mass ha hmass
  d.eigenval d.i₁

/-- Ground energy level `E₀ = -(1/a) log λ₀` for the asym cylinder Hamiltonian. -/
def asymGroundEnergyLevel (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) : ℝ :=
  -(1 / a) * Real.log (asymTransferGroundEigenvalue Nt Ns P a mass ha hmass)

/-- First excited energy level `E₁ = -(1/a) log λ₁` for the asym cylinder Hamiltonian. -/
def asymFirstExcitedEnergyLevel (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) : ℝ :=
  -(1 / a) * Real.log (asymTransferFirstExcitedEigenvalue Nt Ns P a mass ha hmass)

/-- The asym ground state energy is strictly less than the first excited:
`E₀ < E₁` (Perron-Frobenius). -/
theorem asymEnergyLevel_gap (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    asymGroundEnergyLevel Nt Ns P a mass ha hmass <
      asymFirstExcitedEnergyLevel Nt Ns P a mass ha hmass := by
  unfold asymGroundEnergyLevel asymFirstExcitedEnergyLevel
  classical
  let d := asymTransferGroundExcitedData Nt Ns P a mass ha hmass
  have hlam0 : 0 < d.eigenval d.i₀ :=
    asymTransferOperator_eigenvalues_pos Nt Ns P a mass ha hmass d.b d.eigenval d.h_eigen d.i₀
  have hlam1 : 0 < d.eigenval d.i₁ :=
    asymTransferOperator_eigenvalues_pos Nt Ns P a mass ha hmass d.b d.eigenval d.h_eigen d.i₁
  have ha_neg : -(1 / a) < 0 := by linarith [div_pos one_pos ha]
  have hlog : Real.log (d.eigenval d.i₁) < Real.log (d.eigenval d.i₀) :=
    Real.log_lt_log hlam1 d.hlt
  change -(1 / a) * Real.log (d.eigenval d.i₀) < -(1 / a) * Real.log (d.eigenval d.i₁)
  exact mul_lt_mul_of_neg_left hlog ha_neg

/-- The asym cylinder mass gap `m_phys = E₁ - E₀`. -/
def asymMassGap (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) : ℝ :=
  asymFirstExcitedEnergyLevel Nt Ns P a mass ha hmass -
    asymGroundEnergyLevel Nt Ns P a mass ha hmass

/-- The asym cylinder mass gap is strictly positive (at fixed `Nt, Ns, a, mass`).

This is Phase 3's main output. The **uniformity** of this gap as
`a → 0`, `Nt, Ns → ∞` is Layer B2 (chessboard / Fröhlich-Simon-Spencer);
not in scope here. The square's analogue `spectral_gap_uniform` is
itself still an open axiom in pphi2's `TransferMatrix/SpectralGap.lean`. -/
theorem asymMassGap_pos (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    0 < asymMassGap Nt Ns P a mass ha hmass := by
  unfold asymMassGap
  linarith [asymEnergyLevel_gap Nt Ns P a mass ha hmass]

/-- Alias of `asymMassGap_pos` matching the square's `spectral_gap_pos`
API (`SpectralGap.lean:65`). -/
theorem asymSpectral_gap_pos (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    0 < asymMassGap Nt Ns P a mass ha hmass :=
  asymMassGap_pos Nt Ns P a mass ha hmass

end Pphi2

end
