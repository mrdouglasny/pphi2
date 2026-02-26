/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Transfer Matrix: Hamiltonian and Energy Levels

Defines the lattice Hamiltonian H = -(1/a) log T and its spectral properties
(ground/first-excited energies, mass gap) from spectral decomposition data.

## Main results

- `groundEnergyLevel` — E₀ = -(1/a) log λ₀
- `firstExcitedEnergyLevel` — E₁ = -(1/a) log λ₁
- `energyLevel_gap` — E₀ < E₁ (strict gap, from Perron-Frobenius)
- `massGap` — Physical mass gap m = E₁ - E₀
- `massGap_pos` — The mass gap is strictly positive

## Mathematical background

The transfer matrix T = e^{-aH} is a compact self-adjoint operator on L²(ℝ^Ns)
with strictly positive eigenvalues, and Perron-Frobenius gives a simple largest
eigenvalue λ₀ and a first excited level λ₁ < λ₀ (see `L2Operator.lean`).

The lattice Hamiltonian H = -(1/a) log T has discrete spectrum with
E₀ = -(1/a) log λ₀ and E₁ = -(1/a) log λ₁ satisfying E₀ < E₁.

The mass gap m = E₁ - E₀ > 0 is the fundamental physical quantity controlling
exponential decay of correlations.

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1 (Transfer matrix)
- Simon, *The P(φ)₂ Euclidean QFT*, §III.2 (Positivity)
- Reed-Simon, *Methods of Modern Mathematical Physics IV*, §XIII.12
-/

import Pphi2.TransferMatrix.L2Operator

noncomputable section

open GaussianField Real MeasureTheory

namespace Pphi2

variable (Ns : ℕ) [NeZero Ns]

/-! ## Hamiltonian

The transfer matrix is T = e^{-aH} where H is the lattice Hamiltonian.
The eigenvalues of H are Eₙ = -(1/a) log λₙ. -/

/-! ## Chosen spectral data -/

/-- A packaged spectral decomposition with distinguished ground and first-excited indices. -/
structure TransferGroundExcitedData (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) where
  ι : Type*
  b : HilbertBasis ι ℝ (L2SpatialField Ns)
  eigenval : ι → ℝ
  i₀ : ι
  i₁ : ι
  h_eigen : ∀ i, (transferOperatorCLM Ns P a mass ha hmass :
      L2SpatialField Ns →ₗ[ℝ] L2SpatialField Ns) (b i) = eigenval i • b i
  h_sum : ∀ x, HasSum (fun i => (eigenval i * @inner ℝ _ _ (b i) x) • b i)
      (transferOperatorCLM Ns P a mass ha hmass x)
  hi_ne : i₁ ≠ i₀
  hlt : eigenval i₁ < eigenval i₀
  hmax : ∀ i : ι, i ≠ i₀ → eigenval i ≤ eigenval i₁

/-- A noncomputable choice of spectral data with distinguished ground/first-excited indices. -/
noncomputable def transferGroundExcitedData (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    TransferGroundExcitedData Ns P a mass ha hmass := by
  classical
  exact Classical.choice <| by
    rcases transferOperator_ground_simple_spectral Ns P a mass ha hmass with
      ⟨ι, b, eigenval, i₀, i₁, h_eigen, h_sum, hi_ne, hlt, hmax⟩
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
        hmax := hmax
      }⟩

/-- Ground-state eigenvalue λ₀ from spectral data. -/
noncomputable def transferGroundEigenvalue (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) : ℝ :=
  let d := transferGroundExcitedData Ns P a mass ha hmass
  d.eigenval d.i₀

/-- First excited eigenvalue λ₁ from spectral data. -/
noncomputable def transferFirstExcitedEigenvalue (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) : ℝ :=
  let d := transferGroundExcitedData Ns P a mass ha hmass
  d.eigenval d.i₁

/-- Ground energy level `E₀ = -(1/a) log λ₀`. -/
def groundEnergyLevel (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) : ℝ :=
  -(1 / a) * Real.log (transferGroundEigenvalue Ns P a mass ha hmass)

/-- First excited energy level `E₁ = -(1/a) log λ₁`. -/
def firstExcitedEnergyLevel (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) : ℝ :=
  -(1 / a) * Real.log (transferFirstExcitedEigenvalue Ns P a mass ha hmass)

/-- The ground state energy E₀ < E₁ (strict gap).

This is equivalent to `λ₀ > λ₁`, from Perron-Frobenius on spectral data. -/
theorem energyLevel_gap (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    groundEnergyLevel Ns P a mass ha hmass < firstExcitedEnergyLevel Ns P a mass ha hmass := by
  unfold groundEnergyLevel firstExcitedEnergyLevel
  classical
  let d := transferGroundExcitedData Ns P a mass ha hmass
  have hlam0 : 0 < d.eigenval d.i₀ :=
    transferOperator_eigenvalues_pos Ns P a mass ha hmass d.b d.eigenval d.h_eigen d.i₀
  have hlam1 : 0 < d.eigenval d.i₁ :=
    transferOperator_eigenvalues_pos Ns P a mass ha hmass d.b d.eigenval d.h_eigen d.i₁
  -- -(1/a) log λ₀ < -(1/a) log λ₁ because λ₀ > λ₁ > 0 and -(1/a) < 0
  have ha_neg : -(1 / a) < 0 := by linarith [div_pos one_pos ha]
  have hlog : Real.log (d.eigenval d.i₁) < Real.log (d.eigenval d.i₀) :=
    Real.log_lt_log hlam1 d.hlt
  change -(1 / a) * Real.log (d.eigenval d.i₀) < -(1 / a) * Real.log (d.eigenval d.i₁)
  exact mul_lt_mul_of_neg_left hlog ha_neg

/-- The mass gap: `m_phys = E₁ - E₀ > 0`. -/
def massGap (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) : ℝ :=
  firstExcitedEnergyLevel Ns P a mass ha hmass - groundEnergyLevel Ns P a mass ha hmass

/-- The mass gap is strictly positive. -/
theorem massGap_pos (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    0 < massGap Ns P a mass ha hmass := by
  unfold massGap
  linarith [energyLevel_gap Ns P a mass ha hmass]

end Pphi2

end
