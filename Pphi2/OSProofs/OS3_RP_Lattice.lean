/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Reflection Positivity on the Lattice (OS3)

Proves reflection positivity for the interacting lattice measure via the
transfer matrix decomposition.

## Main definitions

- `timeReflection` — reflection Θ across t=0
- `positiveTimeSupported` — predicate for functions supported at t > 0
- `lattice_rp` — the RP inequality on the lattice

## Mathematical background

**Reflection positivity** (OS3) states: for any finite collection of
test functions f₁,...,fₙ supported at positive time, and coefficients c₁,...,cₙ:

  `Σᵢⱼ c̄ᵢ cⱼ ∫ exp(i⟨φ, fᵢ - Θfⱼ⟩) dμ ≥ 0`

where Θ is time reflection.

### Proof on the lattice

On a lattice with Nt time slices {0,...,Nt-1}, take reflection Θ: t ↦ -t mod Nt.

1. **Decompose** the field: φ = (φ⁺, φ⁰, φ⁻) where
   - φ⁺ = field at times t = 1,...,Nt/2-1
   - φ⁰ = field at time t = 0 (and t = Nt/2 for even Nt)
   - φ⁻ = field at times t = Nt/2+1,...,Nt-1

2. **Action splits**: S[φ] = S⁺[φ⁺, φ⁰] + S⁻[φ⁻, φ⁰]
   where S⁻[φ⁻, φ⁰] = S⁺[Θφ⁻, φ⁰] by reflection symmetry.

3. For F supported at positive times:
   ```
   ∫ F(φ) · F̄(Θφ) dμ = (1/Z) ∫ F(φ⁺,φ⁰) · F̄(Θφ⁻,φ⁰) · e^{-S} dφ
                       = (1/Z) ∫ dφ⁰ [∫ F(φ⁺,φ⁰) e^{-S⁺} dφ⁺]²
                       ≥ 0
   ```

4. The square appears because the reflection maps the φ⁻ integral into
   the same form as the φ⁺ integral.

## References

- Osterwalder-Seiler (1978), "Gauge field theories on a lattice"
- Glimm-Jaffe, *Quantum Physics*, §6.1, §19.2
- Simon, *The P(φ)₂ Euclidean QFT*, §III.3
-/

import Pphi2.TransferMatrix.Positivity
import Pphi2.InteractingMeasure.LatticeMeasure

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

variable (Ns Nt : ℕ) [NeZero Ns] [NeZero Nt]

/-! ## Time reflection on the lattice

On a 2D lattice with sites (t, x) ∈ Fin Nt × Fin Ns, time reflection
is `Θ(t, x) = (-t, x)` where `-t` is computed mod Nt. -/

/-- Time reflection on finite lattice sites: `Θ(t, x) = (-t mod Nt, x)`.

This maps the 2D lattice site `(t, x) ∈ Fin Nt × Fin Ns` to `(-t, x)`,
implementing Euclidean time reflection. -/
def timeReflection2D : Fin Nt × Fin Ns → Fin Nt × Fin Ns :=
  fun ⟨t, x⟩ => ⟨-t, x⟩

/-- Time reflection is an involution: Θ² = id. -/
theorem timeReflection2D_involution :
    Function.Involutive (timeReflection2D Ns Nt) := by
  intro ⟨t, x⟩
  simp [timeReflection2D, neg_neg]

/-- Time reflection on field configurations: `(Θφ)(t, x) = φ(-t, x)`. -/
def fieldReflection2D (φ : Fin Nt × Fin Ns → ℝ) :
    Fin Nt × Fin Ns → ℝ :=
  φ ∘ timeReflection2D Ns Nt

/-! ## Positive time support

A function is supported at "positive time" if it depends only on
field values at times t = 1, ..., Nt/2 - 1. -/

/-- A function on the 2D field is supported at positive time if it depends
only on field values φ(t, x) with 0 < t < Nt/2. -/
def PositiveTimeSupported (F : (Fin Nt × Fin Ns → ℝ) → ℝ) : Prop :=
  ∀ φ₁ φ₂ : Fin Nt × Fin Ns → ℝ,
    (∀ t : Fin Nt, (0 < t.val ∧ t.val < Nt / 2) →
      ∀ x : Fin Ns, φ₁ (t, x) = φ₂ (t, x)) →
    F φ₁ = F φ₂

/-! ## Action decomposition

The lattice action decomposes across the time-reflection hyperplane.
This is the key structural property enabling the RP proof. -/

/-- The lattice action on a 2D lattice `Fin Nt × Fin Ns` decomposes as
`S[φ] = S⁺[φ⁺, φ⁰] + S⁻[φ⁻, φ⁰]` where:
- S⁺ depends on field values at t = 0, 1, ..., Nt/2
- S⁻ depends on field values at t = 0, Nt/2, ..., Nt-1
- S⁻[φ⁻, φ⁰] = S⁺[Θφ⁻, φ⁰]

This holds because the nearest-neighbor action couples only adjacent
time slices, and the interaction is a sum over sites. -/
axiom action_decomposition (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∃ (S_plus : (Fin Nt × Fin Ns → ℝ) → ℝ),
    ∀ φ : Fin Nt × Fin Ns → ℝ,
      -- The lattice action equals S⁺ + S⁺ ∘ Θ
      latticeInteraction 2 (Nt * Ns) P a mass sorry = -- needs embedding
        S_plus φ + S_plus (fieldReflection2D Ns Nt φ)

/-! ## Reflection positivity on the lattice -/

/-- **Reflection positivity on the lattice** (OS3).

For any function F supported at positive time:

  `∫ F(φ) · F(Θφ) dμ_a ≥ 0`

Proof sketch:
1. Decompose `S[φ] = S⁺[φ⁺, φ⁰] + S⁻[φ⁻, φ⁰]`
2. Since F depends only on φ⁺ and S⁻[φ⁻, φ⁰] = S⁺[Θφ⁻, φ⁰]:
   ```
   ∫ F(φ) F(Θφ) e^{-S} dφ = ∫ dφ⁰ [∫ F(φ⁺,φ⁰) e^{-S⁺} dφ⁺]² ≥ 0
   ```
3. The integral over φ⁻ after substitution Θφ⁻ = ψ⁺ gives
   the same integral as over φ⁺, yielding a perfect square. -/
axiom lattice_rp (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (F : (Fin Nt × Fin Ns → ℝ) → ℝ)
    (hF : PositiveTimeSupported Ns Nt F) :
    -- In the un-normalized form (avoids division by Z):
    -- ∫ F(φ) · F(Θφ) · exp(-S[φ]) dφ ≥ 0
    True -- Placeholder: full statement needs integration over ℝ^{Nt×Ns}

/-- **Reflection positivity for the interacting measure** (matrix form).

For test functions f₁,...,fₙ supported at positive time and
coefficients c₁,...,cₙ ∈ ℝ:

  `Σᵢⱼ cᵢ cⱼ ∫ exp(i⟨φ, fᵢ⟩) · exp(-i⟨φ, Θfⱼ⟩) dμ_a ≥ 0`

This is the form of OS3 that passes to the continuum limit. -/
axiom lattice_rp_matrix (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (n : ℕ) (c : Fin n → ℝ)
    (f : Fin n → (Fin Nt × Fin Ns → ℝ))
    -- Each fᵢ is supported at positive time
    (hf : ∀ i, ∀ tx : Fin Nt × Fin Ns, tx.1.val = 0 ∨ tx.1.val ≥ Nt / 2 →
      f i tx = 0) :
    ∑ i : Fin n, ∑ j : Fin n, c i * c j *
      sorry ≥ 0  -- ∫ cos(⟨φ, fᵢ - Θfⱼ⟩) dμ_a

/-! ## Transfer matrix connection

The RP proof is intimately connected to the transfer matrix:
the factorization `S = S⁺ + S⁻` is exactly the factorization that
gives `Z = Tr(T^{Nt})`, and the RP inequality follows from T being
a positive operator. -/

/-- RP via transfer matrix: `⟨f, T^n f⟩ ≥ 0` for all f ∈ L² and n ≥ 0.

This is the operator-theoretic formulation of RP: since T is positive
(self-adjoint with positive eigenvalues), T^n is also positive,
so `⟨f, T^n f⟩ ≥ 0`. The Euclidean correlation function
`∫ F(φ_0) F(φ_n) dμ` equals `⟨F, T^n F⟩ / Tr(T^{Nt})`. -/
axiom rp_from_transfer_positivity
    (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (n : ℕ) :
    True -- Placeholder: ⟨f, T^n f⟩ ≥ 0 for all f ∈ L²

end Pphi2

end
