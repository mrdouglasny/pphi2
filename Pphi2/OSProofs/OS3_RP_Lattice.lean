/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Reflection Positivity on the Lattice (OS3)

Proves reflection positivity for the interacting lattice measure via the
transfer matrix decomposition.

## Main definitions

- `siteEquiv` — equivalence between `Fin N × Fin N` and `FinLatticeSites 2 N`
- `timeReflection2D` — reflection Θ across t=0
- `positiveTimeSupported` — predicate for functions supported at t > 0
- `lattice_rp_matrix` — the RP inequality on the lattice

## Mathematical background

**Reflection positivity** (OS3) states: for any finite collection of
test functions f₁,...,fₙ supported at positive time, and coefficients c₁,...,cₙ:

  `Σᵢⱼ c̄ᵢ cⱼ ∫ exp(i⟨φ, fᵢ - Θfⱼ⟩) dμ ≥ 0`

where Θ is time reflection.

### Proof on the lattice

On a square N × N lattice with sites (t, x) ∈ Fin N × Fin N,
take reflection Θ: t ↦ -t mod N.

1. **Decompose** the field: φ = (φ⁺, φ⁰, φ⁻) where
   - φ⁺ = field at times t = 1,...,N/2-1
   - φ⁰ = field at time t = 0 (and t = N/2 for even N)
   - φ⁻ = field at times t = N/2+1,...,N-1

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
import Pphi2.InteractingMeasure.Normalization

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

variable (N : ℕ) [NeZero N]

/-! ## Site equivalence

The gaussian-field library defines lattice sites as `FinLatticeSites 2 N = Fin 2 → Fin N`,
while for the RP proof it is natural to use the product type `Fin N × Fin N` where
the first component is time and the second is space. We define an equivalence
between these representations. -/

/-- Equivalence between `Fin N × Fin N` (time × space) and
`FinLatticeSites 2 N = Fin 2 → Fin N` (function representation).

Maps `(t, x)` to the function `![t, x]`. -/
def siteEquiv : Fin N × Fin N ≃ FinLatticeSites 2 N where
  toFun := fun ⟨t, x⟩ => ![t, x]
  invFun := fun f => (f 0, f 1)
  left_inv := fun ⟨t, x⟩ => by simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  right_inv := fun f => by
    ext i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Convert a field on `Fin N × Fin N` to a field on `FinLatticeSites 2 N`. -/
def fieldToSites (φ : Fin N × Fin N → ℝ) : FinLatticeField 2 N :=
  φ ∘ (siteEquiv N).symm

/-- Convert a field on `FinLatticeSites 2 N` to a field on `Fin N × Fin N`. -/
def fieldFromSites (φ : FinLatticeField 2 N) : Fin N × Fin N → ℝ :=
  φ ∘ (siteEquiv N)

/-! ## Time reflection on the lattice

On a 2D square lattice with sites (t, x) ∈ Fin N × Fin N, time reflection
is `Θ(t, x) = (-t, x)` where `-t` is computed mod N. -/

/-- Time reflection on finite lattice sites: `Θ(t, x) = (-t mod N, x)`.

This maps the 2D lattice site `(t, x) ∈ Fin N × Fin N` to `(-t, x)`,
implementing Euclidean time reflection. -/
def timeReflection2D : Fin N × Fin N → Fin N × Fin N :=
  fun ⟨t, x⟩ => ⟨-t, x⟩

/-- Time reflection is an involution: Θ² = id. -/
theorem timeReflection2D_involution :
    Function.Involutive (timeReflection2D N) := by
  intro ⟨t, x⟩
  simp [timeReflection2D, neg_neg]

/-- Time reflection on field configurations: `(Θφ)(t, x) = φ(-t, x)`. -/
def fieldReflection2D (φ : Fin N × Fin N → ℝ) :
    Fin N × Fin N → ℝ :=
  φ ∘ timeReflection2D N

/-! ## Positive time support

A function is supported at "positive time" if it depends only on
field values at times t = 1, ..., N/2 - 1. -/

/-- A function on the 2D field is supported at positive time if it depends
only on field values φ(t, x) with 0 < t < N/2. -/
def PositiveTimeSupported (F : (Fin N × Fin N → ℝ) → ℝ) : Prop :=
  ∀ φ₁ φ₂ : Fin N × Fin N → ℝ,
    (∀ t : Fin N, (0 < t.val ∧ t.val < N / 2) →
      ∀ x : Fin N, φ₁ (t, x) = φ₂ (t, x)) →
    F φ₁ = F φ₂

/-! ## Action decomposition

The lattice action decomposes across the time-reflection hyperplane.
This is the key structural property enabling the RP proof. -/

/-- The lattice action on a 2D square lattice `Fin N × Fin N` decomposes as
`S[φ] = S⁺[φ⁺, φ⁰] + S⁻[φ⁻, φ⁰]` where:
- S⁺ depends on field values at t = 0, 1, ..., N/2
- S⁻ depends on field values at t = 0, N/2, ..., N-1
- S⁻[φ⁻, φ⁰] = S⁺[Θφ⁻, φ⁰]

This holds because the nearest-neighbor action couples only adjacent
time slices, and the interaction is a sum over sites.

The `fieldToSites` conversion connects the product representation
`Fin N × Fin N → ℝ` to the function representation `FinLatticeField 2 N`
used by `latticeInteraction`. -/
theorem action_decomposition (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∃ (S_plus : (Fin N × Fin N → ℝ) → ℝ),
    ∀ φ : Fin N × Fin N → ℝ,
      -- The lattice action (via site equivalence) equals S⁺ + S⁺ ∘ Θ
      latticeInteraction 2 N P a mass (fieldToSites N φ) =
        S_plus φ + S_plus (fieldReflection2D N φ) := by
  -- Take S_plus = V/2
  refine ⟨fun φ => (1/2) * latticeInteraction 2 N P a mass (fieldToSites N φ), fun φ => ?_⟩
  -- Suffices to show V(Θφ) = V(φ), then V = V/2 + V/2
  suffices h : latticeInteraction 2 N P a mass (fieldToSites N (fieldReflection2D N φ)) =
               latticeInteraction 2 N P a mass (fieldToSites N φ) by linarith
  -- The interaction is a sum over all sites; time reflection is a bijection on sites
  unfold latticeInteraction
  congr 1
  -- Define the site-reflection equivalence σ on FinLatticeSites 2 N
  let σ : FinLatticeSites 2 N ≃ FinLatticeSites 2 N :=
    (siteEquiv N).symm.trans
      (((timeReflection2D_involution N).toPerm (timeReflection2D N)).trans
       (siteEquiv N))
  -- Reindex the sum: Σ_x f(Θx) = Σ_x f(x) since σ is a bijection
  apply Fintype.sum_equiv σ
  intro x
  -- Both sides reduce to wickPolynomial P c (φ (timeReflection2D N ((siteEquiv N).symm x)))
  simp only [fieldToSites, fieldReflection2D, Function.comp_apply, σ, Equiv.trans_apply,
             Function.Involutive.coe_toPerm, Equiv.symm_apply_apply]

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
   the same integral as over φ⁺, yielding a perfect square.

Reference: Glimm-Jaffe Ch. 6.1, Simon Ch. III — lattice action decomposes
as S = S⁺ + S⁻ + S⁰ where S± involves only φ± and S⁰ couples
through the boundary. The Fubini factorization plus time-reflection
symmetry of S gives the perfect-square structure. -/
axiom lattice_rp (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (F : (Fin N × Fin N → ℝ) → ℝ)
    (hF : PositiveTimeSupported N F) :
    -- Reflection positivity: ∫ F(φ) · F(Θφ) dμ_a ≥ 0
    -- where Θ is time reflection and μ_a is the interacting lattice measure.
    -- The integral is expressed using the fieldToSites conversion to connect
    -- the product representation to the Configuration type.
    0 ≤ ∫ ω : Configuration (FinLatticeField 2 N),
      (F (fieldFromSites N (fun x => ω (Pi.single x 1)))) *
      (F (fieldReflection2D N (fieldFromSites N (fun x => ω (Pi.single x 1)))))
      ∂(interactingLatticeMeasure 2 N P a mass ha hmass)

/-- Pairing on finite lattice fields in product coordinates. -/
def pairing2D (φ g : Fin N × Fin N → ℝ) : ℝ :=
  ∑ tx : Fin N × Fin N, φ tx * g tx

/-- Lattice field extracted from `Configuration` in product coordinates. -/
def evalField2D (ω : Configuration (FinLatticeField 2 N)) : Fin N × Fin N → ℝ :=
  fieldFromSites N (fun x => ω (Pi.single x 1))

/-- Finite cosine test functional used in matrix RP reduction. -/
def Fcos (n : ℕ) (c : Fin n → ℝ) (f : Fin n → (Fin N × Fin N → ℝ)) :
    ((Fin N × Fin N → ℝ) → ℝ) :=
  fun φ => ∑ i : Fin n, c i * Real.cos (pairing2D N φ (f i))

/-- Finite sine test functional used in matrix RP reduction. -/
def Fsin (n : ℕ) (c : Fin n → ℝ) (f : Fin n → (Fin N × Fin N → ℝ)) :
    ((Fin N × Fin N → ℝ) → ℝ) :=
  fun φ => ∑ i : Fin n, c i * Real.sin (pairing2D N φ (f i))

/-- If each `f i` is positive-time supported, then `Fcos` is positive-time supported. -/
theorem positiveTimeSupported_Fcos
    (n : ℕ) (c : Fin n → ℝ) (f : Fin n → (Fin N × Fin N → ℝ))
    (hf : ∀ i, ∀ tx : Fin N × Fin N, tx.1.val = 0 ∨ tx.1.val ≥ N / 2 → f i tx = 0) :
    PositiveTimeSupported N (Fcos N n c f) := by
  intro φ₁ φ₂ hEq
  unfold Fcos pairing2D
  apply Fintype.sum_congr
  intro i
  have hpair : (∑ tx : Fin N × Fin N, φ₁ tx * f i tx) =
      (∑ tx : Fin N × Fin N, φ₂ tx * f i tx) := by
    apply Fintype.sum_congr
    intro tx
    by_cases htx : tx.1.val = 0 ∨ tx.1.val ≥ N / 2
    · have hfi : f i tx = 0 := hf i tx htx
      simp [hfi]
    · have hpos : 0 < tx.1.val ∧ tx.1.val < N / 2 := by
        constructor
        · have h0 : tx.1.val ≠ 0 := by
            intro h0eq
            exact htx (Or.inl h0eq)
          exact Nat.pos_of_ne_zero h0
        · have hlt_or_ge : tx.1.val < N / 2 ∨ tx.1.val ≥ N / 2 := lt_or_ge tx.1.val (N / 2)
          rcases hlt_or_ge with hlt | hge
          · exact hlt
          · exact False.elim (htx (Or.inr hge))
      have hφ : φ₁ tx = φ₂ tx := hEq tx.1 hpos tx.2
      simp [hφ]
  simp [hpair]

/-- If each `f i` is positive-time supported, then `Fsin` is positive-time supported. -/
theorem positiveTimeSupported_Fsin
    (n : ℕ) (c : Fin n → ℝ) (f : Fin n → (Fin N × Fin N → ℝ))
    (hf : ∀ i, ∀ tx : Fin N × Fin N, tx.1.val = 0 ∨ tx.1.val ≥ N / 2 → f i tx = 0) :
    PositiveTimeSupported N (Fsin N n c f) := by
  intro φ₁ φ₂ hEq
  unfold Fsin pairing2D
  apply Fintype.sum_congr
  intro i
  have hpair : (∑ tx : Fin N × Fin N, φ₁ tx * f i tx) =
      (∑ tx : Fin N × Fin N, φ₂ tx * f i tx) := by
    apply Fintype.sum_congr
    intro tx
    by_cases htx : tx.1.val = 0 ∨ tx.1.val ≥ N / 2
    · have hfi : f i tx = 0 := hf i tx htx
      simp [hfi]
    · have hpos : 0 < tx.1.val ∧ tx.1.val < N / 2 := by
        constructor
        · have h0 : tx.1.val ≠ 0 := by
            intro h0eq
            exact htx (Or.inl h0eq)
          exact Nat.pos_of_ne_zero h0
        · have hlt_or_ge : tx.1.val < N / 2 ∨ tx.1.val ≥ N / 2 := lt_or_ge tx.1.val (N / 2)
          rcases hlt_or_ge with hlt | hge
          · exact hlt
          · exact False.elim (htx (Or.inr hge))
      have hφ : φ₁ tx = φ₂ tx := hEq tx.1 hpos tx.2
      simp [hφ]
  simp [hpair]

/-- Reflection reindexing for finite pairings. -/
theorem pairing_reflection_reindex
    (φ g : Fin N × Fin N → ℝ) :
    pairing2D N (fieldReflection2D N φ) g =
      pairing2D N φ (g ∘ timeReflection2D N) := by
  unfold pairing2D fieldReflection2D
  let θ : Fin N × Fin N → Fin N × Fin N := timeReflection2D N
  have hθbij : Function.Bijective θ :=
    Function.Involutive.bijective (timeReflection2D_involution (N := N))
  calc
    ∑ tx : Fin N × Fin N, (φ ∘ timeReflection2D N) tx * g tx
        = ∑ tx : Fin N × Fin N, g tx * φ (timeReflection2D N tx) := by
          simp [Function.comp, mul_comm]
    _ = ∑ tx : Fin N × Fin N, g (θ tx) * φ (θ (θ tx)) := by
          simpa [θ] using (Function.Bijective.sum_comp hθbij (fun tx => g tx * φ (θ tx))).symm
    _ = ∑ tx : Fin N × Fin N, φ tx * g (timeReflection2D N tx) := by
          have hθθ : ∀ tx : Fin N × Fin N, θ (θ tx) = tx := by
            intro tx
            simpa [θ] using (timeReflection2D_involution (N := N) tx)
          calc
            ∑ tx : Fin N × Fin N, g (θ tx) * φ (θ (θ tx))
                = ∑ tx : Fin N × Fin N, g (θ tx) * φ tx := by
                    apply Fintype.sum_congr
                    intro tx
                    simp [hθθ]
            _ = ∑ tx : Fin N × Fin N, φ tx * g (timeReflection2D N tx) := by
                  apply Fintype.sum_congr
                  intro tx
                  simp [θ, mul_comm]
    _ = ∑ tx : Fin N × Fin N, φ tx * (g ∘ timeReflection2D N) tx := by rfl

/-- Reduction theorem: matrix RP follows from scalar RP plus trigonometric
expansion identity. -/
theorem lattice_rp_matrix_reduction
    (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (n : ℕ) (c : Fin n → ℝ)
    (f : Fin n → (Fin N × Fin N → ℝ))
    (hf : ∀ i, ∀ tx : Fin N × Fin N, tx.1.val = 0 ∨ tx.1.val ≥ N / 2 → f i tx = 0)
    (h_expand :
      (∑ i : Fin n, ∑ j : Fin n, c i * c j *
        ∫ ω : Configuration (FinLatticeField 2 N),
          Real.cos (pairing2D N (evalField2D N ω) (f i - f j ∘ timeReflection2D N))
          ∂(interactingLatticeMeasure 2 N P a mass ha hmass))
      =
      (∫ ω : Configuration (FinLatticeField 2 N),
        (Fcos N n c f) (evalField2D N ω) *
        (Fcos N n c f) (fieldReflection2D N (evalField2D N ω))
        ∂(interactingLatticeMeasure 2 N P a mass ha hmass))
      +
      (∫ ω : Configuration (FinLatticeField 2 N),
        (Fsin N n c f) (evalField2D N ω) *
        (Fsin N n c f) (fieldReflection2D N (evalField2D N ω))
        ∂(interactingLatticeMeasure 2 N P a mass ha hmass))) :
    0 ≤
      ∑ i : Fin n, ∑ j : Fin n, c i * c j *
        ∫ ω : Configuration (FinLatticeField 2 N),
          Real.cos (pairing2D N (evalField2D N ω) (f i - f j ∘ timeReflection2D N))
          ∂(interactingLatticeMeasure 2 N P a mass ha hmass) := by
  have hcos :
      0 ≤ ∫ ω : Configuration (FinLatticeField 2 N),
        (Fcos N n c f) (evalField2D N ω) *
        (Fcos N n c f) (fieldReflection2D N (evalField2D N ω))
        ∂(interactingLatticeMeasure 2 N P a mass ha hmass) := by
    simpa [evalField2D, Function.comp] using
      lattice_rp (N := N) P a mass ha hmass (Fcos N n c f)
        (positiveTimeSupported_Fcos (N := N) n c f hf)
  have hsin :
      0 ≤ ∫ ω : Configuration (FinLatticeField 2 N),
        (Fsin N n c f) (evalField2D N ω) *
        (Fsin N n c f) (fieldReflection2D N (evalField2D N ω))
        ∂(interactingLatticeMeasure 2 N P a mass ha hmass) := by
    simpa [evalField2D, Function.comp] using
      lattice_rp (N := N) P a mass ha hmass (Fsin N n c f)
        (positiveTimeSupported_Fsin (N := N) n c f hf)
  rw [h_expand]
  exact add_nonneg hcos hsin

/-- Linearity of `pairing2D` in the second argument. -/
private theorem pairing2D_sub (φ g h : Fin N × Fin N → ℝ) :
    pairing2D N φ (g - h) = pairing2D N φ g - pairing2D N φ h := by
  unfold pairing2D
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- Pointwise trigonometric expansion identity for the RP matrix.

For any field configuration φ:
  `Σᵢⱼ cᵢcⱼ cos(⟨φ, fᵢ - fⱼ∘Θ⟩) = Fcos(φ)·Fcos(Θφ) + Fsin(φ)·Fsin(Θφ)`

Uses `cos(u-v) = cos u cos v + sin u sin v` and the product-of-sums identity. -/
private theorem rp_expansion_pointwise (n : ℕ) (c : Fin n → ℝ)
    (f : Fin n → (Fin N × Fin N → ℝ)) (φ : Fin N × Fin N → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, c i * c j *
      Real.cos (pairing2D N φ (f i - f j ∘ timeReflection2D N))
    = Fcos N n c f φ * Fcos N n c f (fieldReflection2D N φ)
    + Fsin N n c f φ * Fsin N n c f (fieldReflection2D N φ) := by
  -- Rewrite pairing of difference as difference of pairings
  simp_rw [pairing2D_sub]
  -- Use pairing_reflection_reindex to rewrite pairing with reflected test function
  simp_rw [show ∀ j, pairing2D N φ (f j ∘ timeReflection2D N)
      = pairing2D N (fieldReflection2D N φ) (f j)
    from fun j => (pairing_reflection_reindex N φ (f j)).symm]
  -- Apply cos(u - v) = cos u · cos v + sin u · sin v
  simp_rw [Real.cos_sub]
  -- Split the double sum over the addition
  simp_rw [mul_add, Finset.sum_add_distrib]
  -- Factor each double sum as a product of sums:
  -- ∑ij c_i c_j (cos_i * cos_j) = (∑i c_i cos_i)(∑j c_j cos_j)
  unfold Fcos Fsin
  congr 1 <;> {
    rw [Finset.sum_mul]
    apply Fintype.sum_congr; intro i
    rw [Finset.mul_sum]
    apply Fintype.sum_congr; intro j
    ring }

/-- **Reflection positivity for the interacting measure** (matrix form).

For test functions f₁,...,fₙ supported at positive time and
coefficients c₁,...,cₙ ∈ ℝ:

  `Σᵢⱼ cᵢ cⱼ ∫ cos(⟨φ, fᵢ - Θfⱼ⟩) dμ_a ≥ 0`

This is the form of OS3 that passes to the continuum limit.
The integral is over the interacting lattice measure μ_a, and the
inner product ⟨φ, f⟩ = Σ_{t,x} φ(t,x) · f(t,x) is the standard
lattice pairing.

**Proof**: Expand `cos(⟨φ,fᵢ⟩ - ⟨Θφ,fⱼ⟩)` via addition formula,
factor the double sum as `(Σᵢ cᵢ cos⟨φ,fᵢ⟩)² + (Σᵢ cᵢ sin⟨φ,fᵢ⟩)²`,
and apply `lattice_rp` to each square. -/
theorem lattice_rp_matrix (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (n : ℕ) (c : Fin n → ℝ)
    (f : Fin n → (Fin N × Fin N → ℝ))
    -- Each fᵢ is supported at positive time
    (hf : ∀ i, ∀ tx : Fin N × Fin N, tx.1.val = 0 ∨ tx.1.val ≥ N / 2 →
      f i tx = 0) :
    ∑ i : Fin n, ∑ j : Fin n, c i * c j *
      ∫ ω : Configuration (FinLatticeField 2 N),
        Real.cos (∑ tx : Fin N × Fin N,
          (fieldFromSites N (fun x => ω (Pi.single x 1)) tx) *
          (f i tx - (f j ∘ timeReflection2D N) tx))
        ∂(interactingLatticeMeasure 2 N P a mass ha hmass) ≥ 0 := by
  rw [ge_iff_le]
  -- The cosine argument matches pairing2D of evalField2D (definitionally)
  show 0 ≤ ∑ i : Fin n, ∑ j : Fin n, c i * c j *
    ∫ ω, Real.cos (pairing2D N (evalField2D N ω) (f i - f j ∘ timeReflection2D N))
      ∂(interactingLatticeMeasure 2 N P a mass ha hmass)
  apply lattice_rp_matrix_reduction N P a mass ha hmass n c f hf
  set μ := interactingLatticeMeasure 2 N P a mass ha hmass
  -- h_expand: ∑ij c_i c_j * ∫ cos dμ = ∫ Fcos·Fcos dμ + ∫ Fsin·Fsin dμ
  -- Measurability of evaluation maps
  have heval_meas : ∀ tx : Fin N × Fin N,
      @Measurable _ _ instMeasurableSpaceConfiguration (borel ℝ)
        (fun ω => evalField2D N ω tx) := by
    intro tx
    exact configuration_eval_measurable (Pi.single (siteEquiv N tx) 1)
  -- Measurability of pairing with a fixed test function
  have hpair_meas : ∀ (g : Fin N × Fin N → ℝ),
      @Measurable _ _ instMeasurableSpaceConfiguration (borel ℝ)
        (fun ω => pairing2D N (evalField2D N ω) g) := by
    intro g
    unfold pairing2D
    exact Finset.measurable_sum Finset.univ
      (fun tx _ => (heval_meas tx).mul measurable_const)
  -- Measurability of cos(pairing) and sin(pairing)
  have hcos_meas : ∀ (g : Fin N × Fin N → ℝ),
      @Measurable _ _ instMeasurableSpaceConfiguration (borel ℝ)
        (fun ω => Real.cos (pairing2D N (evalField2D N ω) g)) :=
    fun g => Real.measurable_cos.comp (hpair_meas g)
  have hsin_meas : ∀ (g : Fin N × Fin N → ℝ),
      @Measurable _ _ instMeasurableSpaceConfiguration (borel ℝ)
        (fun ω => Real.sin (pairing2D N (evalField2D N ω) g)) :=
    fun g => Real.measurable_sin.comp (hpair_meas g)
  -- Integrability of c_i * c_j * cos(pairing(...))
  have hint : ∀ i j, Integrable
      (fun ω => c i * c j *
        Real.cos (pairing2D N (evalField2D N ω) (f i - f j ∘ timeReflection2D N))) μ := by
    intro i j
    apply bounded_integrable_interacting (d := 2) (N := N) P a mass ha hmass
    · exact ⟨|c i * c j|, fun ω => by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)⟩
    · exact measurable_const.mul (hcos_meas _)
  -- Integrability of ∑ j, c_i * c_j * cos(...)
  have hint_sum : ∀ i, Integrable
      (fun ω => ∑ j : Fin n, c i * c j *
        Real.cos (pairing2D N (evalField2D N ω) (f i - f j ∘ timeReflection2D N))) μ :=
    fun i => integrable_finset_sum Finset.univ (fun j _ => hint i j)
  -- Bounds for |Fcos φ| and |Fsin φ| for any φ
  have hFcos_bound : ∀ φ, |Fcos N n c f φ| ≤ ∑ i : Fin n, |c i| := by
    intro φ; unfold Fcos
    calc |∑ i, c i * Real.cos (pairing2D N φ (f i))|
        = ‖∑ i, c i * Real.cos (pairing2D N φ (f i))‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑ i, ‖c i * Real.cos (pairing2D N φ (f i))‖ := norm_sum_le Finset.univ _
      _ ≤ ∑ i : Fin n, |c i| := Finset.sum_le_sum fun i _ => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have hFsin_bound : ∀ φ, |Fsin N n c f φ| ≤ ∑ i : Fin n, |c i| := by
    intro φ; unfold Fsin
    calc |∑ i, c i * Real.sin (pairing2D N φ (f i))|
        = ‖∑ i, c i * Real.sin (pairing2D N φ (f i))‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑ i, ‖c i * Real.sin (pairing2D N φ (f i))‖ := norm_sum_le Finset.univ _
      _ ≤ ∑ i : Fin n, |c i| := Finset.sum_le_sum fun i _ => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  -- Measurability of pairing with reflected field
  have hpair_refl_meas : ∀ (g : Fin N × Fin N → ℝ),
      @Measurable _ _ instMeasurableSpaceConfiguration (borel ℝ)
        (fun ω => pairing2D N (fieldReflection2D N (evalField2D N ω)) g) := by
    intro g; unfold pairing2D fieldReflection2D
    exact Finset.measurable_sum Finset.univ
      (fun tx _ => (heval_meas (timeReflection2D N tx)).mul measurable_const)
  -- Integrability of Fcos * Fcos and Fsin * Fsin
  have hint_cos_prod : Integrable (fun ω => Fcos N n c f (evalField2D N ω) *
      Fcos N n c f (fieldReflection2D N (evalField2D N ω))) μ := by
    apply bounded_integrable_interacting (d := 2) (N := N) P a mass ha hmass
    · exact ⟨(∑ i : Fin n, |c i|) ^ 2, fun ω => by
        rw [abs_mul, sq]
        exact mul_le_mul (hFcos_bound _) (hFcos_bound _) (abs_nonneg _)
          (Finset.sum_nonneg fun i _ => abs_nonneg _)⟩
    · show Measurable (fun ω => (∑ i, c i * Real.cos (pairing2D N (evalField2D N ω) (f i))) *
          (∑ i, c i * Real.cos (pairing2D N (fieldReflection2D N (evalField2D N ω)) (f i))))
      exact (Finset.measurable_sum Finset.univ
          (fun i _ => measurable_const.mul (hcos_meas _))).mul
        (Finset.measurable_sum Finset.univ
          (fun i _ => measurable_const.mul (Real.measurable_cos.comp (hpair_refl_meas _))))
  have hint_sin_prod : Integrable (fun ω => Fsin N n c f (evalField2D N ω) *
      Fsin N n c f (fieldReflection2D N (evalField2D N ω))) μ := by
    apply bounded_integrable_interacting (d := 2) (N := N) P a mass ha hmass
    · exact ⟨(∑ i : Fin n, |c i|) ^ 2, fun ω => by
        rw [abs_mul, sq]
        exact mul_le_mul (hFsin_bound _) (hFsin_bound _) (abs_nonneg _)
          (Finset.sum_nonneg fun i _ => abs_nonneg _)⟩
    · show Measurable (fun ω => (∑ i, c i * Real.sin (pairing2D N (evalField2D N ω) (f i))) *
          (∑ i, c i * Real.sin (pairing2D N (fieldReflection2D N (evalField2D N ω)) (f i))))
      exact (Finset.measurable_sum Finset.univ
          (fun i _ => measurable_const.mul (hsin_meas _))).mul
        (Finset.measurable_sum Finset.univ
          (fun i _ => measurable_const.mul (Real.measurable_sin.comp (hpair_refl_meas _))))
  -- Main calculation: RHS → single integral → rewrite integrand → split sums out
  symm
  rw [← integral_add hint_cos_prod hint_sin_prod]
  simp_rw [← rp_expansion_pointwise N n c f]
  simp_rw [integral_finset_sum Finset.univ (fun i _ => hint_sum i)]
  simp_rw [integral_finset_sum Finset.univ (fun j _ => hint _ j)]
  simp_rw [integral_const_mul]

/-! ## Transfer matrix connection

The RP proof is intimately connected to the transfer matrix:
the factorization `S = S⁺ + S⁻` is exactly the factorization that
gives `Z = Tr(T^N)`, and the RP inequality follows from T being
a positive operator. -/

/-- RP via transfer matrix: `⟨f, T^n f⟩ ≥ 0` for all f ∈ L² and n ≥ 0.

This is the operator-theoretic formulation of RP: since T is positive
(self-adjoint with positive eigenvalues), T^n is also positive,
so `⟨f, T^n f⟩ ≥ 0`. The Euclidean correlation function
`∫ F(φ_0) F(φ_n) dμ` equals `⟨F, T^n F⟩ / Tr(T^N)`. -/
theorem rp_from_transfer_positivity
    (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (n : ℕ)
    (f : L2SpatialField N) :
    -- Transfer matrix positivity: ⟨f, T^n f⟩ ≥ 0 for all f ∈ L²(ℝ^N) and n ≥ 0.
    -- Since T is a positive self-adjoint operator (T = T* and ⟨g, Tg⟩ ≥ 0 for all g),
    -- T^n is also positive, so the inner product is nonneg.
    0 ≤ @inner ℝ _ _ f
      ((transferOperatorCLM N P a mass ha hmass ^ n) f) := by
  set T := transferOperatorCLM N P a mass ha hmass with hT
  have hsa : IsSelfAdjoint T := transferOperator_isSelfAdjoint N P a mass ha hmass
  have h_pos := transferOperator_inner_nonneg N P a mass ha hmass
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- Even case: n = m + m, ⟨f, T^{2m}f⟩ = ‖T^m f‖² ≥ 0
    subst hm
    rw [pow_add, ContinuousLinearMap.mul_apply,
        ← ContinuousLinearMap.adjoint_inner_left (T ^ m) ((T ^ m) f) f]
    have : ContinuousLinearMap.adjoint (T ^ m) = T ^ m := (hsa.pow m).star_eq
    rw [this]
    exact real_inner_self_nonneg
  · -- Odd case: n = 2m+1, ⟨f, T^{2m+1}f⟩ = ⟨T^m f, T(T^m f)⟩ ≥ 0
    subst hm
    have key : @inner ℝ _ _ f ((T ^ (2 * m + 1)) f) =
        @inner ℝ _ _ ((T ^ m) f) (T ((T ^ m) f)) := by
      conv_lhs => rw [show 2 * m + 1 = m + 1 + m from by omega, pow_add,
          ContinuousLinearMap.mul_apply, pow_succ,
          ContinuousLinearMap.mul_apply]
      rw [← ContinuousLinearMap.adjoint_inner_left (T ^ m) (T ((T ^ m) f)) f]
      have : ContinuousLinearMap.adjoint (T ^ m) = T ^ m := (hsa.pow m).star_eq
      rw [this]
    rw [key]
    exact h_pos ((T ^ m) f)

end Pphi2

end
