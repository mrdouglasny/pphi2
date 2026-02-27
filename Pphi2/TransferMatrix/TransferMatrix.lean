/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Transfer Matrix for Lattice P(Φ)₂

Defines the transfer matrix T for the lattice field theory by decomposing
the action across time slices. On a lattice `{0,...,Nt-1} × {0,...,Ns-1}`,
the Boltzmann weight factorizes as a product of transfer matrix kernels.

## Main definitions

- `SpatialField` — field on one time slice: `Fin Ns → ℝ`
- `spatialAction` — single-site spatial action h_a(ψ)
- `transferKernel` — the integral kernel T(ψ, ψ')

## Mathematical background

The key idea: decompose the lattice action across time slices.
On a 2D lattice `{0,...,Nt-1} × {0,...,Ns-1}` with periodic BC in space:

  `S_a[φ] = Σ_{t=0}^{Nt-1} [ ½ Σ_x (φ(t+1,x) - φ(t,x))²
                              + a · h_a(φ(t,·)) ]`

where the spatial action for a single time-slice field `ψ : Fin Ns → ℝ` is:

  `h_a(ψ) = ½ Σ_{x} a⁻²(ψ(x+1) - ψ(x))² + Σ_x (½m²ψ(x)² + :P(ψ(x)):)`

The transfer matrix kernel is:

  `T(ψ, ψ') = exp(-½ Σ_x (ψ(x) - ψ'(x))² - ½a · h_a(ψ) - ½a · h_a(ψ'))`

Note: we absorb half of h_a into each side to make T symmetric.

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1, §19.2
- Simon, *The P(φ)₂ Euclidean QFT*, §III.1
-/

import Pphi2.InteractingMeasure.LatticeAction
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section

open GaussianField Real MeasureTheory

namespace Pphi2

/-! ## Spatial field type

For P(Φ)₂ (d=2), the spatial dimension is 1 and a time slice has Ns sites. -/

/-- Field on a single spatial time slice: `Fin Ns → ℝ`.

For P(Φ)₂ in d=2, the "spatial" lattice is 1-dimensional with Ns sites
and periodic boundary conditions. -/
abbrev SpatialField (Ns : ℕ) := Fin Ns → ℝ

variable (Ns : ℕ) [NeZero Ns]

/-! ## Spatial action

The spatial part of the lattice action, acting on a single time-slice field. -/

/-- Spatial kinetic energy: `½ Σ_x a⁻²(ψ(x+1) - ψ(x))²`.

The discrete gradient squared on a periodic 1D lattice of Ns sites with
lattice spacing a. -/
def spatialKinetic (a : ℝ) (ψ : SpatialField Ns) : ℝ :=
  (1 / 2) * ∑ x : Fin Ns, a⁻¹ ^ 2 * (ψ (x + 1) - ψ x) ^ 2

/-- Spatial potential energy: `Σ_x (½m²ψ(x)² + :P(ψ(x)):_c)`.

The on-site potential including mass term and Wick-ordered interaction. -/
def spatialPotential (P : InteractionPolynomial) (_a mass : ℝ)
    (c : ℝ) (ψ : SpatialField Ns) : ℝ :=
  ∑ x : Fin Ns, ((1 / 2) * mass ^ 2 * ψ x ^ 2 +
    wickPolynomial P c (ψ x))

/-- The full spatial action for one time slice:

  `h_a(ψ) = spatialKinetic + spatialPotential`

This is the "Hamiltonian density" in the transfer matrix formalism. -/
def spatialAction (P : InteractionPolynomial) (a mass : ℝ)
    (c : ℝ) (ψ : SpatialField Ns) : ℝ :=
  spatialKinetic Ns a ψ + spatialPotential Ns P a mass c ψ

/-! ## Time-coupling term

The nearest-neighbor coupling between adjacent time slices. -/

/-- Time-coupling between adjacent time-slice fields:

  `K(ψ, ψ') = ½ Σ_x (ψ(x) - ψ'(x))²`

This is the kinetic energy in the time direction (with a=1 in time units,
i.e., the time lattice spacing is absorbed into T). -/
def timeCoupling (ψ ψ' : SpatialField Ns) : ℝ :=
  (1 / 2) * ∑ x : Fin Ns, (ψ x - ψ' x) ^ 2

/-- The time coupling is nonneg. -/
theorem timeCoupling_nonneg (ψ ψ' : SpatialField Ns) :
    0 ≤ timeCoupling Ns ψ ψ' := by
  let _ := (inferInstance : NeZero Ns)
  unfold timeCoupling
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro x _
  exact sq_nonneg _

/-- The time coupling vanishes iff ψ = ψ'. -/
theorem timeCoupling_eq_zero_iff (ψ ψ' : SpatialField Ns) :
    timeCoupling Ns ψ ψ' = 0 ↔ ψ = ψ' := by
  let _ := (inferInstance : NeZero Ns)
  unfold timeCoupling
  rw [mul_eq_zero]
  constructor
  · intro h
    rcases h with h | h
    · norm_num at h
    · ext x
      have := Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (ψ i - ψ' i)) |>.mp h
      have hx := this x (Finset.mem_univ x)
      rwa [sq_eq_zero_iff, sub_eq_zero] at hx
  · intro h
    right
    apply Finset.sum_eq_zero
    intro x _
    rw [h]
    simp

/-! ## Transfer matrix kernel -/

/-- The transfer matrix kernel:

  `T(ψ, ψ') = exp(-K(ψ,ψ') - ½a · h_a(ψ) - ½a · h_a(ψ'))`

where K is the time coupling and h_a is the spatial action.

The factor of ½ in front of each h_a makes T symmetric: `T(ψ, ψ') = T(ψ', ψ)`.
This corresponds to the "symmetric split" of the action across the time link. -/
def transferKernel (P : InteractionPolynomial) (a mass : ℝ) :
    SpatialField Ns → SpatialField Ns → ℝ :=
  let c := wickConstant 1 Ns a mass  -- d=1 spatial, Ns sites
  fun ψ ψ' =>
    Real.exp (-(timeCoupling Ns ψ ψ'
      + (a / 2) * spatialAction Ns P a mass c ψ
      + (a / 2) * spatialAction Ns P a mass c ψ'))

/-- The transfer kernel is strictly positive everywhere. -/
theorem transferKernel_pos (P : InteractionPolynomial) (a mass : ℝ)
    (ψ ψ' : SpatialField Ns) :
    0 < transferKernel Ns P a mass ψ ψ' :=
  Real.exp_pos _

/-- The transfer kernel is symmetric: `T(ψ, ψ') = T(ψ', ψ)`.

This follows from the symmetric split: the kernel has the form
`exp(-K(ψ,ψ') - ½a·h(ψ) - ½a·h(ψ'))` where `K(ψ,ψ') = K(ψ',ψ)`. -/
theorem transferKernel_symmetric (P : InteractionPolynomial) (a mass : ℝ)
    (ψ ψ' : SpatialField Ns) :
    transferKernel Ns P a mass ψ ψ' = transferKernel Ns P a mass ψ' ψ := by
  simp only [transferKernel]
  congr 1
  -- The exponent: -(K(ψ,ψ') + ½a·h(ψ) + ½a·h(ψ')) is symmetric
  -- because K(ψ,ψ') = K(ψ',ψ) and the h terms swap.
  simp only [timeCoupling]
  have : ∀ x : Fin Ns, (ψ x - ψ' x) ^ 2 = (ψ' x - ψ x) ^ 2 :=
    fun x => by ring
  simp_rw [this]
  ring

/-! ## Action decomposition

The full lattice partition function factorizes as a trace of the transfer matrix.

For a 2D lattice with Nt time slices and periodic BC in time:

  `Z = ∫ Π_t dψ_t · T(ψ_0,ψ_1) · T(ψ_1,ψ_2) · ... · T(ψ_{Nt-1},ψ_0)`
  `= Tr(T^{Nt})`

where T acts on L²(ℝ^Ns, dψ) as an integral operator with kernel T(ψ,ψ').
This trace formula follows from iterating the transfer matrix across all
Nt time slices with periodic boundary conditions.

The formal statement requires trace class operators on L²(ℝ^Ns), which is
set up in L2Operator.lean via `transferOperatorCLM`. The trace formula
itself is a standard identity but not formalized here. -/

end Pphi2

end
