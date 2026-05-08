/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Reflection Positivity on the Lattice (OS3)

Proves reflection positivity for the interacting lattice measure via the
transfer matrix decomposition.

## Main definitions

- `siteEquiv` — equivalence between `ZMod N × ZMod N` and `FinLatticeSites 2 N`
- `timeReflection2D` — reflection Θ across t=0
- `positiveTimeSupported` — predicate for functions supported at t > 0
- `lattice_rp_matrix` — the RP inequality on the lattice

## Mathematical background

**Reflection positivity** (OS3) states: for any finite collection of
test functions f₁,...,fₙ supported at positive time, and coefficients c₁,...,cₙ:

  `Σᵢⱼ c̄ᵢ cⱼ ∫ exp(i⟨φ, fᵢ - Θfⱼ⟩) dμ ≥ 0`

where Θ is time reflection.

### Proof on the lattice

On a square N × N lattice with sites (t, x) ∈ ZMod N × ZMod N,
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
import Lattice.Symmetry

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

variable (N : ℕ)

/-! ## Site equivalence

The gaussian-field library defines lattice sites as `FinLatticeSites 2 N = Fin 2 → Fin N`,
while for the RP proof it is natural to use the product type `ZMod N × ZMod N` where
the first component is time and the second is space. We define an equivalence
between these representations. -/

/-- Equivalence between `ZMod N × ZMod N` (time × space) and
`FinLatticeSites 2 N = Fin 2 → Fin N` (function representation).

Maps `(t, x)` to the function `![t, x]`. -/
def siteEquiv : ZMod N × ZMod N ≃ FinLatticeSites 2 N where
  toFun := fun ⟨t, x⟩ => ![t, x]
  invFun := fun f => (f 0, f 1)
  left_inv := fun ⟨t, x⟩ => rfl
  right_inv := fun f => by
    ext i
    fin_cases i <;> rfl

/-- Convert a field on `ZMod N × ZMod N` to a field on `FinLatticeSites 2 N`. -/
def fieldToSites (φ : ZMod N × ZMod N → ℝ) : FinLatticeField 2 N :=
  φ ∘ (siteEquiv N).symm

/-- Convert a field on `FinLatticeSites 2 N` to a field on `ZMod N × ZMod N`. -/
def fieldFromSites (φ : FinLatticeField 2 N) : ZMod N × ZMod N → ℝ :=
  φ ∘ (siteEquiv N)

/-! ## Time reflection on the lattice

On a 2D square lattice with sites (t, x) ∈ ZMod N × ZMod N, time reflection
is `Θ(t, x) = (-t, x)` where `-t` is computed mod N. -/

/-- Time reflection on finite lattice sites: `Θ(t, x) = (-t mod N, x)`.

This maps the 2D lattice site `(t, x) ∈ ZMod N × ZMod N` to `(-t, x)`,
implementing Euclidean time reflection. -/
def timeReflection2D : ZMod N × ZMod N → ZMod N × ZMod N :=
  fun ⟨t, x⟩ => ⟨-t, x⟩

/-- Time reflection is an involution: Θ² = id. -/
theorem timeReflection2D_involution :
    Function.Involutive (timeReflection2D N) := by
  intro ⟨t, x⟩
  simp [timeReflection2D, neg_neg]

/-- Time reflection on field configurations: `(Θφ)(t, x) = φ(-t, x)`. -/
def fieldReflection2D (φ : ZMod N × ZMod N → ℝ) :
    ZMod N × ZMod N → ℝ :=
  φ ∘ timeReflection2D N

/-! ## Positive time support

A function is supported at "positive time" if it depends only on
field values at times t = 1, ..., N/2 - 1. -/

/-- A function on the 2D field is supported at positive time if it depends
only on field values φ(t, x) with 0 < t < N/2. -/
def PositiveTimeSupported (F : (ZMod N × ZMod N → ℝ) → ℝ) : Prop :=
  ∀ φ₁ φ₂ : ZMod N × ZMod N → ℝ,
    (∀ t : ZMod N, (0 < t.val ∧ t.val < N / 2) →
      ∀ x : ZMod N, φ₁ (t, x) = φ₂ (t, x)) →
    F φ₁ = F φ₂

/-! ## Action decomposition

The lattice action decomposes across the time-reflection hyperplane.
This is the key structural property enabling the RP proof. -/

variable [NeZero N]

/-- The lattice action on a 2D square lattice `ZMod N × ZMod N` decomposes as
`S[φ] = S⁺[φ⁺, φ⁰] + S⁻[φ⁻, φ⁰]` where:
- S⁺ depends on field values at t = 0, 1, ..., N/2
- S⁻ depends on field values at t = 0, N/2, ..., N-1
- S⁻[φ⁻, φ⁰] = S⁺[Θφ⁻, φ⁰]

This holds because the nearest-neighbor action couples only adjacent
time slices, and the interaction is a sum over sites.

The `fieldToSites` conversion connects the product representation
`ZMod N × ZMod N → ℝ` to the function representation `FinLatticeField 2 N`
used by `latticeInteraction`. -/
theorem action_decomposition (P : InteractionPolynomial) (a mass : ℝ)
    (_ha : 0 < a) (_hmass : 0 < mass) :
    ∃ (S_plus : (ZMod N × ZMod N → ℝ) → ℝ),
    ∀ φ : ZMod N × ZMod N → ℝ,
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

/-- Lattice field extracted from `Configuration` in product coordinates. -/
def evalField2D (ω : Configuration (FinLatticeField 2 N)) : ZMod N × ZMod N → ℝ :=
  fieldFromSites N (fun x => ω (Pi.single x 1))

/-! ## Time-slice interaction decomposition

The interaction V = a² Σ_x v(φ(x)) is a sum of single-site functions.
We decompose this sum based on the time coordinate into:
- V₊: sum over positive-time sites (0 < t.val < N/2)
- V₀: sum over boundary sites (complement of S₊ ∪ Θ(S₊))
- V₋: sum over negative-time sites (in Θ(S₊))

This decomposition satisfies V = V₊ + V₀ + V₋ and V₋(φ) = V₊(Θφ),
which is the key algebraic input for reducing the interacting RP to
Gaussian RP with a boundary weight. -/

/-- A function depends only on boundary sites (sites not in S₊ ∪ Θ(S₊),
where S₊ = {(t,x) : 0 < t.val < N/2}). -/
def BoundarySupported (w : (ZMod N × ZMod N → ℝ) → ℝ) : Prop :=
  ∀ φ₁ φ₂ : ZMod N × ZMod N → ℝ,
    (∀ tx : ZMod N × ZMod N,
      ¬(0 < tx.1.val ∧ tx.1.val < N / 2) →
      ¬(0 < (-tx.1 : ZMod N).val ∧ (-tx.1 : ZMod N).val < N / 2) →
      φ₁ tx = φ₂ tx) →
    w φ₁ = w φ₂

/-- Positive-time part of the Wick interaction:
`V₊(φ) = a² Σ_{(t,x) : 0 < t < N/2} :P(φ(t,x)):`. -/
private def positiveTimeInteraction (P : InteractionPolynomial) (a mass : ℝ) :
    (ZMod N × ZMod N → ℝ) → ℝ :=
  fun φ => a ^ 2 * (Finset.univ.filter (fun tx : ZMod N × ZMod N =>
    0 < tx.1.val ∧ tx.1.val < N / 2)).sum
    (fun tx => wickPolynomial P (wickConstant 2 N a mass) (φ tx))

/-- Boundary part of the Wick interaction:
`V₀(φ) = a² Σ_{(t,x) : t ∉ S₊ ∪ Θ(S₊)} :P(φ(t,x)):`. -/
private def boundaryTimeInteraction (P : InteractionPolynomial) (a mass : ℝ) :
    (ZMod N × ZMod N → ℝ) → ℝ :=
  fun φ => a ^ 2 * (Finset.univ.filter (fun tx : ZMod N × ZMod N =>
    ¬(0 < tx.1.val ∧ tx.1.val < N / 2) ∧
    ¬(0 < (-tx.1 : ZMod N).val ∧ (-tx.1 : ZMod N).val < N / 2))).sum
    (fun tx => wickPolynomial P (wickConstant 2 N a mass) (φ tx))

/-- Negative-time part of the Wick interaction:
`V₋(φ) = a² Σ_{(t,x) : t ∈ Θ(S₊)} :P(φ(t,x)):`. -/
private def negativeTimeInteraction (P : InteractionPolynomial) (a mass : ℝ) :
    (ZMod N × ZMod N → ℝ) → ℝ :=
  fun φ => a ^ 2 * (Finset.univ.filter (fun tx : ZMod N × ZMod N =>
    0 < (-tx.1 : ZMod N).val ∧ (-tx.1 : ZMod N).val < N / 2)).sum
    (fun tx => wickPolynomial P (wickConstant 2 N a mass) (φ tx))

/-- S₊ and Θ(S₊) are disjoint: no site has both 0 < t.val < N/2 and
0 < (-t).val < N/2. -/
private theorem positiveTime_negativeTime_disjoint
    (tx : ZMod N × ZMod N) :
    ¬((0 < tx.1.val ∧ tx.1.val < N / 2) ∧
      (0 < (-tx.1 : ZMod N).val ∧ (-tx.1 : ZMod N).val < N / 2)) := by
  intro ⟨⟨h1, h2⟩, ⟨_, h4⟩⟩
  -- t.val > 0 and t.val < N/2, and (-t).val > 0 and (-t).val < N/2
  -- For t ≠ 0: (-t).val = N - t.val
  have hne : (tx.1 : ZMod N) ≠ 0 := by
    intro h; rw [h, ZMod.val_zero] at h1; omega
  haveI : NeZero (tx.1 : ZMod N) := ⟨hne⟩
  have hval : (-tx.1 : ZMod N).val = N - tx.1.val := ZMod.val_neg_of_ne_zero tx.1
  rw [hval] at h4
  -- h2: t.val < N/2 and h4: N - t.val < N/2, so N < N. Contradiction.
  omega

/-- The interaction decomposes as V = V₊ + V₀ + V₋ when expressed via evalField2D.
This is a partition of the site sum: S₊, S₀, Θ(S₊) partition all sites of
ZMod N × ZMod N. -/
private theorem interactionFunctional_decomposition (P : InteractionPolynomial)
    (a mass : ℝ) (ω : Configuration (FinLatticeField 2 N)) :
    interactionFunctional 2 N P a mass ω =
      positiveTimeInteraction N P a mass (evalField2D N ω) +
      boundaryTimeInteraction N P a mass (evalField2D N ω) +
      negativeTimeInteraction N P a mass (evalField2D N ω) := by
  -- Reindex the sum via siteEquiv: FinLatticeSites 2 N ≅ ZMod N × ZMod N
  unfold interactionFunctional positiveTimeInteraction boundaryTimeInteraction
    negativeTimeInteraction
  -- Factor out a^2 and work with the sums
  rw [← mul_add, ← mul_add]
  congr 1
  -- Reindex: Σ_{x : FinLatticeSites} f(x) = Σ_{tx : ZMod N × ZMod N} f(siteEquiv tx)
  rw [show ∑ x : FinLatticeSites 2 N,
      wickPolynomial P (wickConstant 2 N a mass)
        (ω (finLatticeDelta 2 N x)) =
    ∑ tx : ZMod N × ZMod N,
      wickPolynomial P (wickConstant 2 N a mass) (evalField2D N ω tx) from by
    apply Fintype.sum_equiv (siteEquiv N).symm
    intro x
    simp only [evalField2D, fieldFromSites, Function.comp_apply,
      Equiv.apply_symm_apply]
    congr 2; ext y; simp [finLatticeDelta, Pi.single, Function.update]]
  -- Three-way sum partition: Σ_all = Σ_{S₊} + Σ_{S₀} + Σ_{Θ(S₊)}
  set v := fun tx : ZMod N × ZMod N =>
    wickPolynomial P (wickConstant 2 N a mass) (evalField2D N ω tx)
  set Cplus := fun tx : ZMod N × ZMod N =>
    0 < tx.1.val ∧ tx.1.val < N / 2
  set Cminus := fun tx : ZMod N × ZMod N =>
    0 < (-tx.1 : ZMod N).val ∧ (-tx.1 : ZMod N).val < N / 2
  -- Split: Σ_all = Σ_{Cplus} + Σ_{¬Cplus}
  have h1 := (Finset.sum_filter_add_sum_filter_not Finset.univ Cplus v).symm
  -- Split: Σ_{¬Cplus} = Σ_{Cminus ∧ ¬Cplus} + Σ_{¬Cminus ∧ ¬Cplus}
  have h2 : (Finset.univ.filter (fun tx => ¬Cplus tx)).sum v =
    ((Finset.univ.filter (fun tx => ¬Cplus tx)).filter Cminus).sum v +
    ((Finset.univ.filter (fun tx => ¬Cplus tx)).filter (fun tx => ¬Cminus tx)).sum v :=
    (Finset.sum_filter_add_sum_filter_not _ Cminus v).symm
  -- Cminus ∧ ¬Cplus = Cminus (since Cplus ∧ Cminus is impossible)
  have h3 : (Finset.univ.filter (fun tx => ¬Cplus tx)).filter Cminus =
    Finset.univ.filter Cminus := by
    ext tx; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun ⟨_, h⟩ => h
    · exact fun h => ⟨fun hc => positiveTime_negativeTime_disjoint N tx ⟨hc, h⟩, h⟩
  -- ¬Cminus ∧ ¬Cplus = ¬Cplus ∧ ¬Cminus (just reorder)
  have h4 : (Finset.univ.filter (fun tx => ¬Cplus tx)).filter (fun tx => ¬Cminus tx) =
    Finset.univ.filter (fun tx => ¬Cplus tx ∧ ¬Cminus tx) := by
    ext tx; simp [Finset.mem_filter]
  rw [h1, h2, h3, h4]
  ring

/-- The negative-time interaction equals the positive-time interaction on the
reflected field: V₋(φ) = V₊(Θφ). This is the site-relabeling argument:
Θ bijects S₊ to Θ(S₊), so Σ_{t ∈ Θ(S₊)} v(φ(t)) = Σ_{t ∈ S₊} v(φ(Θt)) = V₊(Θφ). -/
private theorem negativeTime_eq_positiveTime_reflected (P : InteractionPolynomial)
    (a mass : ℝ) (φ : ZMod N × ZMod N → ℝ) :
    negativeTimeInteraction N P a mass φ =
      positiveTimeInteraction N P a mass (fieldReflection2D N φ) := by
  unfold negativeTimeInteraction positiveTimeInteraction fieldReflection2D
  congr 1
  -- Reindex: Σ_{tx ∈ filter(C₋)} v(φ(tx)) = Σ_{tx ∈ filter(C₊)} v(φ(Θ(tx)))
  -- using the bijection Θ: S₊ → Θ(S₊)
  set c := wickConstant 2 N a mass
  set v := fun t : ℝ => wickPolynomial P c t
  set Cplus := fun tx : ZMod N × ZMod N =>
    0 < tx.1.val ∧ tx.1.val < N / 2
  set Cminus := fun tx : ZMod N × ZMod N =>
    0 < (-tx.1 : ZMod N).val ∧ (-tx.1 : ZMod N).val < N / 2
  -- The time reflection as an equiv on ZMod N × ZMod N
  let θ : ZMod N × ZMod N ≃ ZMod N × ZMod N :=
    (timeReflection2D_involution N).toPerm (timeReflection2D N)
  -- θ maps Cplus to Cminus
  have hθ_map : ∀ tx, Cplus tx → Cminus (θ tx) := by
    intro ⟨t, x⟩ ⟨h1, h2⟩
    simp only [θ, Function.Involutive.coe_toPerm, timeReflection2D, Cminus]
    simp only [neg_neg]
    exact ⟨h1, h2⟩
  -- θ maps Cminus to Cplus
  have hθ_inv : ∀ tx, Cminus tx → Cplus (θ tx) := by
    intro ⟨t, x⟩ ⟨h1, h2⟩
    simp only [θ, Function.Involutive.coe_toPerm, timeReflection2D, Cplus]
    exact ⟨h1, h2⟩
  -- θ bijects filter(Cplus) to filter(Cminus)
  have hθ_bij : Finset.image θ (Finset.univ.filter Cplus) = Finset.univ.filter Cminus := by
    ext tx; simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨tx', hC, rfl⟩; exact hθ_map tx' hC
    · intro hC; exact ⟨θ tx, hθ_inv tx hC, by
        show θ (θ tx) = tx
        exact timeReflection2D_involution N tx⟩
  -- Rewrite using sum_image
  rw [← hθ_bij]
  rw [Finset.sum_image (fun _ _ _ _ heq => θ.injective heq)]
  apply Finset.sum_congr rfl
  intro tx _
  simp only [θ, Function.Involutive.coe_toPerm, timeReflection2D, Function.comp_apply]

/-- `exp(-V₊)` is positive-time supported: it depends only on field values
at sites (t,x) with 0 < t.val < N/2. -/
private theorem positiveTimeInteraction_supported (P : InteractionPolynomial)
    (a mass : ℝ) :
    PositiveTimeSupported N
      (fun φ => Real.exp (-(positiveTimeInteraction N P a mass φ))) := by
  intro φ₁ φ₂ hEq
  change Real.exp (-(positiveTimeInteraction N P a mass φ₁)) =
       Real.exp (-(positiveTimeInteraction N P a mass φ₂))
  congr 1; congr 1
  change positiveTimeInteraction N P a mass φ₁ = positiveTimeInteraction N P a mass φ₂
  unfold positiveTimeInteraction
  congr 1
  apply Finset.sum_congr rfl
  intro tx htx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at htx
  congr 1
  exact hEq tx.1 htx tx.2

/-- `exp(-V₀)` is boundary-supported: it depends only on field values at
sites not in S₊ ∪ Θ(S₊). -/
private theorem boundaryTimeInteraction_boundarySupported (P : InteractionPolynomial)
    (a mass : ℝ) :
    BoundarySupported N
      (fun φ => Real.exp (-(boundaryTimeInteraction N P a mass φ))) := by
  intro φ₁ φ₂ hEq
  change Real.exp (-(boundaryTimeInteraction N P a mass φ₁)) =
       Real.exp (-(boundaryTimeInteraction N P a mass φ₂))
  congr 1; congr 1
  change boundaryTimeInteraction N P a mass φ₁ = boundaryTimeInteraction N P a mass φ₂
  unfold boundaryTimeInteraction
  congr 1
  apply Finset.sum_congr rfl
  intro tx htx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at htx
  congr 1
  exact hEq tx htx.1 htx.2

omit [NeZero N] in
/-- Product of positive-time-supported functions is positive-time supported. -/
private theorem mul_positiveTimeSupported
    (F G : (ZMod N × ZMod N → ℝ) → ℝ)
    (hF : PositiveTimeSupported N F) (hG : PositiveTimeSupported N G) :
    PositiveTimeSupported N (fun φ => F φ * G φ) := by
  intro φ₁ φ₂ hEq
  change F φ₁ * G φ₁ = F φ₂ * G φ₂
  rw [hF φ₁ φ₂ hEq, hG φ₁ φ₂ hEq]

/-! ## Precision matrix block structure -/

/-- Sites in S₊ and Θ(S₊) have zero precision matrix coupling.

The mass operator Q = -Δ_a + m² has nearest-neighbor structure:
Q_{xy} ≠ 0 only if x and y differ by ±eᵢ in one coordinate.
For x ∈ S₊ (0 < (x 0).val < N/2) and y ∈ Θ(S₊) ((y 0).val > N/2),
their time coordinates differ by ≥ 2, so Q_{xy} = 0.

This is the key combinatorial input for reflection positivity: the
precision matrix has no coupling between the positive-time and
negative-time field variables. -/
theorem massOperator_cross_block_zero
    (a mass : ℝ) (x y : FinLatticeSites 2 N)
    (hx : 0 < (x 0).val ∧ (x 0).val < N / 2)
    (hy : 0 < (-(y 0) : ZMod N).val ∧ (-(y 0) : ZMod N).val < N / 2) :
    massOperatorEntry 2 N a mass x y = 0 := by
  -- Derive (y 0).val > N/2
  have hy0_ne : (y 0 : ZMod N) ≠ 0 := by
    intro h; rw [h, neg_zero, ZMod.val_zero] at hy; omega
  haveI : NeZero (y 0 : ZMod N) := ⟨hy0_ne⟩
  have hy_val : (y 0).val > N / 2 := by
    have := ZMod.val_neg_of_ne_zero (y 0); omega
  -- x ≠ y
  have hxy_ne : x ≠ y := by
    intro h; have := congr_fun h 0; rw [this] at hx; omega
  -- Reduce: massOperatorEntry = -(Δ(δ_y))(x) since m²·δ_y(x) = 0
  simp only [massOperatorEntry, massOperator, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
    finLatticeDelta, if_neg hxy_ne, mul_zero, add_zero]
  -- Need Fact (1 < N) for val_one
  have hN : 1 < N := by have := ZMod.val_lt (x 0); omega
  haveI : Fact (1 < N) := ⟨hN⟩
  -- Show Laplacian at non-neighbor is 0
  change -(finiteLaplacianFun 2 N a (finLatticeDelta 2 N y) x) = 0
  rw [neg_eq_zero]; unfold finiteLaplacianFun
  simp only [finLatticeDelta, if_neg hxy_ne, mul_zero, sub_zero]
  -- Forward shifts x + eᵢ miss y (time coord stays ≤ N/2)
  have h_fwd : ∀ i : Fin 2, (fun j => if j = i then x j + 1 else x j) ≠ y := by
    intro i heq; fin_cases i
    · have h0 : x 0 + 1 = y 0 := by have := congr_fun heq 0; simpa using this
      have : (x 0 + 1).val ≤ N / 2 := by
        rw [ZMod.val_add_of_lt (by rw [ZMod.val_one N]; omega), ZMod.val_one N]; omega
      rw [h0] at this; omega
    · have h0 : x 0 = y 0 := by have := congr_fun heq 0; simpa using this
      rw [h0] at hx; omega
  -- Backward shifts x - eᵢ miss y (time coord stays < N/2)
  have h_bwd : ∀ i : Fin 2, (fun j => if j = i then x j - 1 else x j) ≠ y := by
    intro i heq; fin_cases i
    · have h0 : x 0 - 1 = y 0 := by have := congr_fun heq 0; simpa using this
      have : (x 0 - 1).val < N / 2 := by
        rw [ZMod.val_sub (by rw [ZMod.val_one N]; omega), ZMod.val_one N]; omega
      rw [h0] at this; omega
    · have h0 : x 0 = y 0 := by have := congr_fun heq 0; simpa using this
      rw [h0] at hx; omega
  -- All terms in the Laplacian sum are 0
  have : ∀ i : Fin 2,
      (if (fun j => if j = i then x j + 1 else x j) = y then (1 : ℝ) else 0) +
      (if (fun j => if j = i then x j - 1 else x j) = y then (1 : ℝ) else 0) = 0 := by
    intro i; rw [if_neg (h_fwd i), if_neg (h_bwd i), add_zero]
  simp_rw [this, Finset.sum_const_zero, mul_zero]

/-- The block-zero property is symmetric: Q_{yx} = 0 for y ∈ Θ(S₊), x ∈ S₊. -/
theorem massOperator_cross_block_zero_symm
    (a mass : ℝ) (x y : FinLatticeSites 2 N)
    (hx : 0 < (x 0).val ∧ (x 0).val < N / 2)
    (hy : 0 < (-(y 0) : ZMod N).val ∧ (-(y 0) : ZMod N).val < N / 2) :
    massOperatorEntry 2 N a mass y x = 0 := by
  have hsymm : massOperatorEntry 2 N a mass y x = massOperatorEntry 2 N a mass x y := by
    change massOperatorMatrix 2 N a mass y x = massOperatorMatrix 2 N a mass x y
    have h := massOperatorMatrix_isHermitian 2 N a mass
    have := congr_fun (congr_fun h y) x
    simp [Matrix.conjTranspose] at this; linarith
  rw [hsymm]; exact massOperator_cross_block_zero N a mass x y hx hy

/-- The mass operator matrix is invariant under negation of both arguments:
`Q(-x, -y) = Q(x, y)`. Follows from Laplacian reflection invariance
(`negLaplacianMatrix_neg_invariant`) plus the mass diagonal being
invariant under `(-x = -y) ↔ (x = y)`. -/
private theorem massOperatorMatrix_neg_invariant
    (a mass : ℝ) (x y : FinLatticeSites 2 N) :
    massOperatorMatrix 2 N a mass (-x) (-y) =
    massOperatorMatrix 2 N a mass x y := by
  -- Q = (-Δ) + m²·I, so Q(x,y) = (-Δ)(x,y) + m²·δ(x,y)
  -- Both terms are invariant under (x,y) → (-x,-y).
  simp only [massOperatorMatrix, massOperatorEntry, massOperator,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  · -- Laplacian part: reuse negLaplacianMatrix_neg_invariant
    have h := negLaplacianMatrix_neg_invariant 2 N a x y
    simp only [negLaplacianMatrix, massOperatorMatrix, massOperatorEntry, massOperator,
      sq, mul_zero, zero_smul, add_zero, ContinuousLinearMap.neg_apply,
      Pi.neg_apply] at h
    linarith
  · -- Mass diagonal: m² * δ_{-y}(-x) = m² * δ_y(x), since (-x = -y) ↔ (x = y)
    congr 1; simp only [finLatticeDelta]
    simp only [neg_inj]

/-- The mass operator matrix is invariant under time negation:
`Q(timeNeg x, timeNeg y) = Q(x, y)` where `timeNeg` negates only coordinate 0.

This follows from the Laplacian stencil being symmetric: for the time direction
(i=0), the ±e₀ stencil terms swap under time negation (sum unchanged); for spatial
directions, terms are unaffected. Combined with the mass diagonal being invariant
under the injective map `timeNeg`. -/
private theorem massOperatorMatrix_timeNeg_invariant
    (a mass : ℝ) (x y : FinLatticeSites 2 N) :
    massOperatorMatrix 2 N a mass
      (fun i => if i = (0 : Fin 2) then -(x i) else x i)
      (fun i => if i = (0 : Fin 2) then -(y i) else y i) =
    massOperatorMatrix 2 N a mass x y := by
  simp only [massOperatorMatrix, massOperatorEntry, massOperator,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  · -- Laplacian part: stencil sum is invariant under time negation
    simp only [finiteLaplacian, finiteLaplacianLM, ContinuousLinearMap.coe_mk',
      LinearMap.coe_mk, AddHom.coe_mk, finiteLaplacianFun]
    congr 1; congr 1
    apply Finset.sum_congr rfl
    intro i _
    -- For each stencil direction i, the sum δ(x+eᵢ=y) + δ(x-eᵢ=y) is invariant:
    -- i=0: the ±e₀ terms swap (sum unchanged by commutativity)
    -- i=1: terms are identical
    -- Unfold finLatticeDelta and convert function equalities to pointwise
    simp only [finLatticeDelta, funext_iff, Fin.forall_fin_two]
    -- Use fin_cases to split on stencil direction
    fin_cases i
    · -- i = 0 (time direction): ±e₀ terms swap (sum unchanged by commutativity)
      simp only [Fin.isValue]
      norm_num
      -- Goal: (if -x₀+1=-y₀ ∧ ... then 1 else 0) + (if -x₀-1=-y₀ ∧ ... then 1 else 0)
      --     = (if x₀+1=y₀ ∧ ... then 1 else 0) + (if x₀-1=y₀ ∧ ... then 1 else 0)
      -- The conditions are equivalent with ±1 swapped:
      -- -x₀+1 = -y₀ ↔ x₀-1 = y₀  and  -x₀-1 = -y₀ ↔ x₀+1 = y₀
      have h1 : (-x 0 + 1 = -y 0 ∧ x 1 = y 1) ↔ (x 0 - 1 = y 0 ∧ x 1 = y 1) := by
        constructor <;> intro ⟨ha, hb⟩ <;> exact ⟨by linear_combination -ha, hb⟩
      have h2 : (-x 0 - 1 = -y 0 ∧ x 1 = y 1) ↔ (x 0 + 1 = y 0 ∧ x 1 = y 1) := by
        constructor <;> intro ⟨ha, hb⟩ <;> exact ⟨by linear_combination -ha, hb⟩
      simp only [h1, h2]
      ring
    · -- i = 1 (spatial direction): terms unchanged
      simp only [Fin.isValue]
      norm_num
  · -- Mass diagonal: δ_{ty}(tx) = δ_y(x) by injectivity of time negation
    congr 1; simp only [finLatticeDelta]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (by ext i; have := congr_fun h1 i; fin_cases i <;> simp_all) h2
    · exact absurd (by subst h2; rfl) h1
    · rfl

/-- At a positive-time site x ∈ S₊, the mass operator `(Qφ)(x)` depends only on
field values at non-negative-time sites (i.e., S₊ ∪ B). This follows from
`massOperator_cross_block_zero`: `Q(x,y) = 0` for `y ∈ S₋`. -/
private theorem massOperator_indep_of_negativeTime
    (a mass : ℝ) (x : FinLatticeSites 2 N)
    (hx : 0 < (x 0).val ∧ (x 0).val < N / 2)
    (φ₁ φ₂ : FinLatticeField 2 N)
    (h : ∀ y, ¬(0 < (-(y 0) : ZMod N).val ∧ (-(y 0) : ZMod N).val < N / 2) →
      φ₁ y = φ₂ y) :
    (massOperator 2 N a mass φ₁) x = (massOperator 2 N a mass φ₂) x := by
  rw [massOperator_eq_matrix_mulVec, massOperator_eq_matrix_mulVec]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : 0 < (-(y 0) : ZMod N).val ∧ (-(y 0) : ZMod N).val < N / 2
  · -- y ∈ S₋: Q(x,y) = 0 by block-zero
    have hzero := massOperator_cross_block_zero N a mass x y hx hy
    change massOperatorMatrix 2 N a mass x y * φ₁ y =
           massOperatorMatrix 2 N a mass x y * φ₂ y
    simp [massOperatorMatrix, hzero]
  · -- y ∉ S₋: φ₁(y) = φ₂(y) by hypothesis
    rw [h y hy]

/-- At a negative-time site x ∈ S₋, the mass operator `(Qφ)(x)` depends only on
field values at non-positive-time sites (i.e., S₋ ∪ B). This follows from
`massOperator_cross_block_zero_symm`: `Q(x,y) = 0` for `y ∈ S₊`. -/
private theorem massOperator_indep_of_positiveTime
    (a mass : ℝ) (x : FinLatticeSites 2 N)
    (hx : 0 < (-(x 0) : ZMod N).val ∧ (-(x 0) : ZMod N).val < N / 2)
    (φ₁ φ₂ : FinLatticeField 2 N)
    (h : ∀ y, ¬(0 < (y 0).val ∧ (y 0).val < N / 2) → φ₁ y = φ₂ y) :
    (massOperator 2 N a mass φ₁) x = (massOperator 2 N a mass φ₂) x := by
  rw [massOperator_eq_matrix_mulVec, massOperator_eq_matrix_mulVec]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : 0 < (y 0).val ∧ (y 0).val < N / 2
  · -- y ∈ S₊: Q(x,y) = 0 by block-zero-symm
    have hzero := massOperator_cross_block_zero_symm N a mass y x hy hx
    change massOperatorMatrix 2 N a mass x y * φ₁ y =
           massOperatorMatrix 2 N a mass x y * φ₂ y
    simp [massOperatorMatrix, hzero]
  · -- y ∉ S₊: φ₁(y) = φ₂(y) by hypothesis
    rw [h y hy]

/-! ## Reflection positivity on the lattice -/

/-- **Second Fubini + COV + perfect square for Gaussian RP (factored form).**

After factoring `G(u)` out of the inner integral, shows the RP integral is ≥ 0.

## Irreducible mathematical content

The conclusion is that the specific Gaussian-weighted integral is ≥ 0. The
**only** genuinely mathematical step is the **COV identity**:

  `∫ v₋, GΘ(0,(v₋,v₀))·exp(-½C(v₋,v₀)) dv₋`
  `  = exp(-½C((0,v₀))) · ∫ u', G(u',(0,v₀))·exp(-½A(u',(0,v₀))) du'`

This identity expresses the time-reflection symmetry of the Gaussian measure
on the negative-time sector — after the substitution `v₋ = σ·u'` where
`σ : isNT ≃ isPT` is site-level time reflection:

- The integrand `GΘ(0,(v₋,v₀))` becomes `G(u',(0,v₀))` because
  `fieldReflection2D` turns S₋ values into S₊ values (and S₊ values into 0),
  then `G` only sees S₊ values by `PositiveTimeSupported`.
- The quadratic form `C(v₋,v₀)` becomes `A(u',(0,v₀)) + C((0,v₀))`, by
  `massOperatorMatrix_timeNeg_invariant` (proved in this file): the mass
  operator matrix `Q` satisfies `Q(θx,θy) = Q(x,y)` for `θ` the site-level
  time negation, so `⟨φ_R(σ·u', v₀), Q(φ_R(σ·u', v₀))⟩ = ⟨Θφ_R, Q(Θφ_R)⟩`
  where `Θφ_R` is the field with `u'` at S₊, `0` at S₋, `v₀` at B. The
  quadratic form of that field decomposes as `A(u',(0,v₀)) + C((0,v₀))`
  because S₊-S₋ cross terms vanish by `massOperator_cross_block_zero`.

Substituting these back, the outer integral becomes
`∫ u, G(u,0) · ∫ v₀ · exp(-½C_BB(v₀)) · w(v₀) · exp(-½A(u,v₀)) ·`
`∫ u', G(u',(0,v₀))·exp(-½A(u',(0,v₀))) du' · du dv₀`,
which after Fubini swap `u ↔ v₀` and collecting factors becomes a positive
measure against a **perfect square**:

  `∫ v₀ w(v₀)·exp(-½C_BB(v₀)) · [∫ u G(u,0)·exp(-½A(u,(0,v₀))) du]² ≥ 0`.

## Proof plumbing

1. **Second Fubini**: Split `v = (v₋, v₀)` via `MeasurableEquiv.piEquivPiSubtypeProd`
   on the `isNT` predicate, reducing `∫ v` to `∫ v₀ ∫ v₋`.
2. **Factor out**: `w(v₀)` and `exp(-½A(u,v₀))` don't depend on `v₋`
   (`hw_boundary`, `hA_indep`), so pull out of the `v₋`-integral.
3. **COV identity** (irreducible step above), via
   `volume_preserving_piCongrLeft` + site-level `isNT ≃ isPT` + `Q`-invariance.
4. **Fubini swap**: Exchange `u ↔ v₀` integration order via `integral_integral_swap`.
5. **Perfect square**: `integral_nonneg` + `mul_nonneg` + `sq_nonneg`.

Steps (1, 2, 4, 5) are measure-theoretic plumbing. Step (3) is the real mathematical
content and relies on `massOperatorMatrix_timeNeg_invariant` (already proved
here, line 502) plus the site-level time-reflection bijection.

Reference: Glimm-Jaffe Ch. 6.1, Osterwalder-Seiler (1978) §3. -/
private axiom gaussian_rp_cov_perfect_square
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (isPT : FinLatticeSites 2 N → Prop) [DecidablePred isPT]
    (hisPT : isPT = fun s => 0 < (s 0).val ∧ (s 0).val < N / 2)
    (e : (FinLatticeSites 2 N → ℝ) ≃ᵐ
      ({s // isPT s} → ℝ) × ({s // ¬isPT s} → ℝ))
    (G w : (ZMod N × ZMod N → ℝ) → ℝ)
    (A_quad : ({s // isPT s} → ℝ) → ({s // ¬isPT s} → ℝ) → ℝ)
    (C_quad : ({s // ¬isPT s} → ℝ) → ℝ)
    (hG_dep : ∀ u v₁ v₂,
      G (fieldFromSites N (e.symm (u, v₁))) =
      G (fieldFromSites N (e.symm (u, v₂))))
    (hGR_dep : ∀ u₁ u₂ v,
      G (fieldReflection2D N (fieldFromSites N (e.symm (u₁, v)))) =
      G (fieldReflection2D N (fieldFromSites N (e.symm (u₂, v)))))
    (hw_dep : ∀ u₁ u₂ v,
      w (fieldFromSites N (e.symm (u₁, v))) =
      w (fieldFromSites N (e.symm (u₂, v))))
    (hw_nonneg : ∀ φ, 0 ≤ w φ)
    (hw_boundary : BoundarySupported N w)
    (hA_indep : ∀ u v₁ v₂,
      (∀ s : {s // ¬isPT s},
        ¬(0 < (-(s.1 0) : ZMod N).val ∧ (-(s.1 0) : ZMod N).val < N / 2) →
        v₁ s = v₂ s) →
      A_quad u v₁ = A_quad u v₂)
    (hC_def : ∀ v, C_quad v =
      ∑ x, (fun x => if h : isPT x then (0 : ℝ) else v ⟨x, h⟩) x *
        (massOperator 2 N a mass
          (fun x => if h : isPT x then (0 : ℝ) else v ⟨x, h⟩)) x)
    (hAC_sum : ∀ u v, A_quad u v + C_quad v =
      ∑ x, (e.symm (u, v)) x *
        (massOperator 2 N a mass (e.symm (u, v))) x) :
    0 ≤ ∫ u, G (fieldFromSites N (e.symm (u, (0 : {s // ¬isPT s} → ℝ)))) *
      ∫ v, G (fieldReflection2D N (fieldFromSites N (e.symm ((0 : {s // isPT s} → ℝ), v)))) *
        w (fieldFromSites N (e.symm ((0 : {s // isPT s} → ℝ), v))) *
        Real.exp (-(a^2 / 2) * A_quad u v) *
        Real.exp (-(a^2 / 2) * C_quad v)

/-- **Perfect square for block-zero Gaussian integral (Fubini + COV step).**

After the first Fubini decomposition `φ = (u, v)` and density factorization
`ρ = exp(-½A) · exp(-½C)`, this theorem proves Gaussian RP:

  `0 ≤ ∫ u ∫ v, G(u) · GΘ(v) · w(v) · exp(-½A(u,v)) · exp(-½C(v))`

**Proof**: Uses `hG_dep` to factor `G(u)` out of the inner integral via
`integral_const_mul`, then applies `gaussian_rp_cov_perfect_square`.

Reference: Glimm-Jaffe Ch. 6.1, Osterwalder-Seiler (1978) §3. -/
private theorem gaussian_rp_perfect_square
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (isPT : FinLatticeSites 2 N → Prop) [DecidablePred isPT]
    (hisPT : isPT = fun s => 0 < (s 0).val ∧ (s 0).val < N / 2)
    (e : (FinLatticeSites 2 N → ℝ) ≃ᵐ
      ({s // isPT s} → ℝ) × ({s // ¬isPT s} → ℝ))
    (G w : (ZMod N × ZMod N → ℝ) → ℝ)
    (A_quad : ({s // isPT s} → ℝ) → ({s // ¬isPT s} → ℝ) → ℝ)
    (C_quad : ({s // ¬isPT s} → ℝ) → ℝ)
    (hG_dep : ∀ u v₁ v₂,
      G (fieldFromSites N (e.symm (u, v₁))) =
      G (fieldFromSites N (e.symm (u, v₂))))
    (hGR_dep : ∀ u₁ u₂ v,
      G (fieldReflection2D N (fieldFromSites N (e.symm (u₁, v)))) =
      G (fieldReflection2D N (fieldFromSites N (e.symm (u₂, v)))))
    (hw_dep : ∀ u₁ u₂ v,
      w (fieldFromSites N (e.symm (u₁, v))) =
      w (fieldFromSites N (e.symm (u₂, v))))
    (hw_nonneg : ∀ φ, 0 ≤ w φ)
    (hw_boundary : BoundarySupported N w)
    (hA_indep : ∀ u v₁ v₂,
      (∀ s : {s // ¬isPT s},
        ¬(0 < (-(s.1 0) : ZMod N).val ∧ (-(s.1 0) : ZMod N).val < N / 2) →
        v₁ s = v₂ s) →
      A_quad u v₁ = A_quad u v₂)
    -- Connection to mass operator (enables COV proof via Q-invariance under θ)
    (hC_def : ∀ v, C_quad v =
      ∑ x, (fun x => if h : isPT x then (0 : ℝ) else v ⟨x, h⟩) x *
        (massOperator 2 N a mass
          (fun x => if h : isPT x then (0 : ℝ) else v ⟨x, h⟩)) x)
    (hAC_sum : ∀ u v, A_quad u v + C_quad v =
      ∑ x, (e.symm (u, v)) x *
        (massOperator 2 N a mass (e.symm (u, v))) x) :
    0 ≤ ∫ u, ∫ v,
      G (fieldFromSites N (e.symm (u, v))) *
      G (fieldReflection2D N (fieldFromSites N (e.symm (u, v)))) *
      w (fieldFromSites N (e.symm (u, v))) *
      (Real.exp (-(a^2 / 2) * A_quad u v) * Real.exp (-(a^2 / 2) * C_quad v)) := by
  -- === Step 1: Simplify using dependency hypotheses ===
  -- G(u,v) depends only on u, GΘ(u,v) depends only on v, w(u,v) depends only on v
  have hG_rw : ∀ u v, G (fieldFromSites N (e.symm (u, v))) =
      G (fieldFromSites N (e.symm (u, 0))) := fun u v => hG_dep u v 0
  have hGR_rw : ∀ u v, G (fieldReflection2D N (fieldFromSites N (e.symm (u, v)))) =
      G (fieldReflection2D N (fieldFromSites N (e.symm (0, v)))) := fun u v => hGR_dep u 0 v
  have hw_rw : ∀ u v, w (fieldFromSites N (e.symm (u, v))) =
      w (fieldFromSites N (e.symm (0, v))) := fun u v => hw_dep u 0 v
  simp_rw [hG_rw, hGR_rw, hw_rw]
  -- === Step 2: Factor G(u) out of inner integral ===
  -- The integrand is: G(u,0) * GΘ(0,v) * w(0,v) * exp(-½A(u,v)) * exp(-½C(v))
  -- Rearrange to: G(u,0) * (GΘ(0,v) * w(0,v) * exp(-½A(u,v)) * exp(-½C(v)))
  have hrw : ∀ u v,
      G (fieldFromSites N (e.symm (u, (0 : {s // ¬isPT s} → ℝ)))) *
      G (fieldReflection2D N (fieldFromSites N (e.symm ((0 : {s // isPT s} → ℝ), v)))) *
      w (fieldFromSites N (e.symm ((0 : {s // isPT s} → ℝ), v))) *
      (Real.exp (-(a^2 / 2) * A_quad u v) * Real.exp (-(a^2 / 2) * C_quad v)) =
    G (fieldFromSites N (e.symm (u, (0 : {s // ¬isPT s} → ℝ)))) *
      (G (fieldReflection2D N (fieldFromSites N (e.symm ((0 : {s // isPT s} → ℝ), v)))) *
       w (fieldFromSites N (e.symm ((0 : {s // isPT s} → ℝ), v))) *
       Real.exp (-(a^2 / 2) * A_quad u v) *
       Real.exp (-(a^2 / 2) * C_quad v)) := fun u v => by ring
  simp_rw [hrw, integral_const_mul]
  -- === Step 3: Apply the COV + perfect square axiom ===
  -- Goal is: 0 ≤ ∫ u, G(u,0) * ∫ v, GΘ(0,v) * w(0,v) * exp(-½A(u,v)) * exp(-½C(v))
  -- This is exactly the conclusion of gaussian_rp_cov_perfect_square.
  exact gaussian_rp_cov_perfect_square N a mass ha hmass isPT hisPT e G w A_quad C_quad
    hG_dep hGR_dep hw_dep hw_nonneg hw_boundary hA_indep hC_def hAC_sum

/-- **Core Gaussian reflection positivity with boundary weight.**

For any G positive-time supported and w ≥ 0 boundary-supported:

  `∫ G(φ) · G(Θφ) · w(φ) · ρ(φ) dφ ≥ 0`

where ρ is the Gaussian density.

**Proof strategy** (partially formalized):
1. **Block-zero** (proved: `massOperator_cross_block_zero`): The precision
   matrix Q = -Δ_a + m² has Q_{xy} = 0 for x ∈ S₊, y ∈ Θ(S₊).
2. **Quadratic form decomposition**: ⟨φ,Qφ⟩ = q₊(φ₊,φ₀) + q₀(φ₀) + q₋(φ₋,φ₀)
   with no φ₊·φ₋ cross terms (follows from step 1).
3. **Fubini**: Decompose ∫ dφ = ∫ dφ₊ ∫ dφ₀ ∫ dφ₋ using the product
   structure of Lebesgue measure on the finite-dimensional space.
4. **Change of variables**: φ₋ ↦ Θφ₋ in the inner integral, using the
   reflection symmetry q₋(φ₋,φ₀) = q₊(Θφ₋,φ₀).
5. **Perfect square**: The integral becomes ∫ w(φ₀)·ρ₀(φ₀)·[∫ G·ρ₊ dφ₊]² dφ₀ ≥ 0.

Steps 3-5 require finite-dimensional Fubini (`Equiv.piEquivPiSubtypeProd`
+ `integral_prod`) which is available in Mathlib but needs significant
infrastructure connecting it to the lattice field setup.

Reference: Glimm-Jaffe Ch. 6.1, Osterwalder-Seiler (1978). -/
theorem gaussian_density_rp (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (G : (ZMod N × ZMod N → ℝ) → ℝ)
    (hG : PositiveTimeSupported N G)
    (w : (ZMod N × ZMod N → ℝ) → ℝ)
    (hw_nonneg : ∀ φ, 0 ≤ w φ)
    (hw_boundary : BoundarySupported N w) :
    0 ≤ ∫ φ : FinLatticeField 2 N,
      G (fieldFromSites N φ) *
      G (fieldReflection2D N (fieldFromSites N φ)) *
      w (fieldFromSites N φ) *
      gaussianDensity 2 N a mass φ := by
  -- Handle non-integrable case: Bochner integral returns 0 by convention
  by_cases hint : Integrable (fun φ : FinLatticeField 2 N =>
      G (fieldFromSites N φ) *
      G (fieldReflection2D N (fieldFromSites N φ)) *
      w (fieldFromSites N φ) *
      gaussianDensity 2 N a mass φ)
  · -- Integrable case: Fubini + block-zero factorization + perfect square
    -- Step 1: Site predicate and Fubini equivalence
    let isPT : FinLatticeSites 2 N → Prop :=
      fun s => 0 < (s 0).val ∧ (s 0).val < N / 2
    haveI : DecidablePred isPT := fun _ => instDecidableAnd
    let e := MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : FinLatticeSites 2 N => ℝ) isPT
    have hmp : MeasurePreserving e volume (volume.prod volume) :=
      volume_preserving_piEquivPiSubtypeProd _ isPT
    -- Step 2: Change of variables via e
    -- ∫ F(φ) dφ = ∫ F(e.symm(u, v)) d(u, v) = ∫ du ∫ dv F(e.symm(u, v))
    have hFe : Integrable (fun y => G (fieldFromSites N (e.symm y)) *
        G (fieldReflection2D N (fieldFromSites N (e.symm y))) *
        w (fieldFromSites N (e.symm y)) *
        gaussianDensity 2 N a mass (e.symm y)) (volume.prod volume) := by
      simpa [Function.comp] using
        hmp.symm.integrable_comp_of_integrable (g := fun φ =>
          G (fieldFromSites N φ) * G (fieldReflection2D N (fieldFromSites N φ)) *
          w (fieldFromSites N φ) * gaussianDensity 2 N a mass φ) hint
    have hFubini : ∫ φ, G (fieldFromSites N φ) *
        G (fieldReflection2D N (fieldFromSites N φ)) *
        w (fieldFromSites N φ) * gaussianDensity 2 N a mass φ =
        ∫ u : ({s // isPT s} → ℝ),
          ∫ v : ({s // ¬isPT s} → ℝ),
            G (fieldFromSites N (e.symm (u, v))) *
            G (fieldReflection2D N (fieldFromSites N (e.symm (u, v)))) *
            w (fieldFromSites N (e.symm (u, v))) *
            gaussianDensity 2 N a mass (e.symm (u, v)) := by
      calc ∫ φ, G (fieldFromSites N φ) *
              G (fieldReflection2D N (fieldFromSites N φ)) *
              w (fieldFromSites N φ) * gaussianDensity 2 N a mass φ
          = ∫ y, G (fieldFromSites N (e.symm y)) *
              G (fieldReflection2D N (fieldFromSites N (e.symm y))) *
              w (fieldFromSites N (e.symm y)) *
              gaussianDensity 2 N a mass (e.symm y) := by
            simpa [Function.comp] using
              (hmp.symm.integral_comp e.symm.measurableEmbedding _).symm
        _ = ∫ u, ∫ v, G (fieldFromSites N (e.symm (u, v))) *
              G (fieldReflection2D N (fieldFromSites N (e.symm (u, v)))) *
              w (fieldFromSites N (e.symm (u, v))) *
              gaussianDensity 2 N a mass (e.symm (u, v)) :=
            integral_prod _ hFe
    rw [hFubini]
    -- Step 3: G(fieldFromSites(e.symm(u, v))) depends only on u
    have hG_dep : ∀ u v1 v2,
        G (fieldFromSites N (e.symm (u, v1))) =
        G (fieldFromSites N (e.symm (u, v2))) := by
      intro u v1 v2
      apply hG
      intro t ht x
      simp only [fieldFromSites, Function.comp_apply, e,
        MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
      have hpt : isPT ((siteEquiv N) (t, x)) := by
        change 0 < (![t, x] 0).val ∧ (![t, x] 0).val < N / 2
        simp only [Matrix.cons_val_zero]; exact ht
      rw [dif_pos hpt, dif_pos hpt]
    -- Step 4: G(fieldReflection2D(fieldFromSites(e.symm(u, v)))) depends only on v
    have hGR_dep : ∀ u1 u2 v,
        G (fieldReflection2D N (fieldFromSites N (e.symm (u1, v)))) =
        G (fieldReflection2D N (fieldFromSites N (e.symm (u2, v)))) := by
      intro u1 u2 v
      apply hG
      intro t ht x
      simp only [fieldReflection2D, fieldFromSites, timeReflection2D, Function.comp_apply, e,
        MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
      have hnt : ¬isPT ((siteEquiv N) (-t, x)) := by
        change ¬(0 < (![-t, x] 0).val ∧ (![-t, x] 0).val < N / 2)
        simp only [Matrix.cons_val_zero]
        exact fun h => positiveTime_negativeTime_disjoint N (t, x) ⟨ht, h⟩
      rw [dif_neg hnt, dif_neg hnt]
    -- Step 5: w(fieldFromSites(e.symm(u, v))) depends only on v
    have hw_dep : ∀ u1 u2 v,
        w (fieldFromSites N (e.symm (u1, v))) =
        w (fieldFromSites N (e.symm (u2, v))) := by
      intro u1 u2 v
      apply hw_boundary
      intro tx hpt hnt
      simp only [fieldFromSites, Function.comp_apply, e,
        MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
      -- tx is a boundary site: ¬isPT and ¬isNT, so isPT(siteEquiv tx) is false
      have h_not_isPT : ¬isPT ((siteEquiv N) tx) := by
        change ¬(0 < (![tx.1, tx.2] 0).val ∧ (![tx.1, tx.2] 0).val < N / 2)
        simp only [Matrix.cons_val_zero]; exact hpt
      rw [dif_neg h_not_isPT, dif_neg h_not_isPT]
    -- Step 6: Density factorization via field decomposition.
    -- Decompose φ = φ_S (positive-time part) + φ_R (rest).
    -- By linearity + self-adjointness of Q + block-zero:
    --   q(φ) = ⟨φ_S,Qφ_S⟩ + 2⟨φ_S,Qφ_R⟩ + ⟨φ_R,Qφ_R⟩ = A(u,v₀) + C(v)
    -- where A depends on u and boundary values, C depends on v only.
    -- So ρ = exp(-½A) · exp(-½C) factors.
    --
    -- Then: second Fubini on v → (v₋, v₀), factor integrals,
    -- change of variables θ on v₋ using Q(θx,θy)=Q(x,y),
    -- conclude I = ∫ w·exp(-½BB)·[∫ G·exp(-½A)]² ≥ 0.
    -- Step 6a: The quadratic form Σ_x φ(x)·(Qφ)(x) at positive-time sites
    -- is independent of negative-time field values.
    have hq_plus_indep : ∀ u (v₁ v₂ : {s // ¬isPT s} → ℝ),
        (∀ s : {s // ¬isPT s},
          ¬(0 < (-(s.1 0) : ZMod N).val ∧ (-(s.1 0) : ZMod N).val < N / 2) →
          v₁ s = v₂ s) →
        (∑ x ∈ Finset.univ.filter isPT,
          (e.symm (u, v₁)) x * (massOperator 2 N a mass (e.symm (u, v₁))) x) =
        (∑ x ∈ Finset.univ.filter isPT,
          (e.symm (u, v₂)) x * (massOperator 2 N a mass (e.symm (u, v₂))) x) := by
      intro u v₁ v₂ hv
      apply Finset.sum_congr rfl
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      -- φ(x) is the same for both (x ∈ S₊, so value comes from u)
      have hφ_eq : (e.symm (u, v₁)) x = (e.symm (u, v₂)) x := by
        simp only [e, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply, dif_pos hx]
      -- (Qφ)(x) is the same by massOperator_indep_of_negativeTime
      have hQ_eq : (massOperator 2 N a mass (e.symm (u, v₁))) x =
          (massOperator 2 N a mass (e.symm (u, v₂))) x := by
        apply massOperator_indep_of_negativeTime N a mass x hx
        intro y hy
        simp only [e, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
        by_cases hyp : isPT y
        · rw [dif_pos hyp, dif_pos hyp]
        · rw [dif_neg hyp, dif_neg hyp]
          exact hv ⟨y, hyp⟩ hy
      rw [hφ_eq, hQ_eq]
    -- === Step 6b: Density factorization ===
    -- Define restricted fields: φ_S (positive-time part) and φ_R (complement)
    let φ_S_of : ({s // isPT s} → ℝ) → FinLatticeField 2 N :=
      fun u x => if h : isPT x then u ⟨x, h⟩ else 0
    let φ_R_of : ({s // ¬isPT s} → ℝ) → FinLatticeField 2 N :=
      fun v x => if h : isPT x then 0 else v ⟨x, h⟩
    -- φ = φ_S + φ_R
    have h_decomp : ∀ u v, e.symm (u, v) = φ_S_of u + φ_R_of v := by
      intro u v; ext x; simp only [φ_S_of, φ_R_of, Pi.add_apply, e,
        MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
      split <;> simp
    -- Q(φ_S + φ_R) = Q(φ_S) + Q(φ_R) by linearity
    have h_Q_add : ∀ u v, massOperator 2 N a mass (e.symm (u, v)) =
        massOperator 2 N a mass (φ_S_of u) + massOperator 2 N a mass (φ_R_of v) := by
      intro u v; rw [h_decomp]; exact map_add (massOperator 2 N a mass) _ _
    -- Cross-term symmetry: ⟨φ_R, Qφ_S⟩ = ⟨φ_S, Qφ_R⟩
    have h_cross_symm : ∀ u v,
        ∑ x, φ_R_of v x * (massOperator 2 N a mass (φ_S_of u)) x =
        ∑ x, φ_S_of u x * (massOperator 2 N a mass (φ_R_of v)) x := by
      intro u v
      rw [massOperator_selfAdjoint 2 N a mass (φ_R_of v) (φ_S_of u)]
      congr 1; ext x; ring
    -- q = ⟨φ_S,Qφ_S⟩ + 2⟨φ_S,Qφ_R⟩ + ⟨φ_R,Qφ_R⟩
    have h_q_three : ∀ u v,
        ∑ x, (e.symm (u, v)) x * (massOperator 2 N a mass (e.symm (u, v))) x =
        (∑ x, φ_S_of u x * (massOperator 2 N a mass (φ_S_of u)) x) +
        2 * (∑ x, φ_S_of u x * (massOperator 2 N a mass (φ_R_of v)) x) +
        (∑ x, φ_R_of v x * (massOperator 2 N a mass (φ_R_of v)) x) := by
      intro u v
      conv_lhs => rw [h_decomp u v]
      simp only [map_add, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
      linarith [h_cross_symm u v]
    -- Define C(v) = ⟨φ_R, Q(φ_R)⟩ and A(u,v) = q - C
    let C_quad : ({s // ¬isPT s} → ℝ) → ℝ := fun v =>
      ∑ x, φ_R_of v x * (massOperator 2 N a mass (φ_R_of v)) x
    let A_quad : ({s // isPT s} → ℝ) → ({s // ¬isPT s} → ℝ) → ℝ := fun u v =>
      (∑ x, (e.symm (u, v)) x * (massOperator 2 N a mass (e.symm (u, v))) x) -
        C_quad v
    -- Factor the Gaussian density: ρ = exp(-(a²/2)·A) * exp(-(a²/2)·C).
    -- Under GJ-aligned normalisation, gaussianDensity has the (a^d/2) prefactor
    -- (here d = 2). The factoring `-(a²/2)·Σ = -(a²/2)·(Σ - C) + -(a²/2)·C`
    -- is structurally the same as before, just with `a²/2` in place of `1/2`.
    have h_factor : ∀ u v, gaussianDensity 2 N a mass (e.symm (u, v)) =
        Real.exp (-(a^2 / 2) * A_quad u v) * Real.exp (-(a^2 / 2) * C_quad v) := by
      intro u v; simp only [gaussianDensity, A_quad]
      rw [show -(a^2 / 2 : ℝ) *
        ∑ x, (e.symm (u, v)) x * (massOperator 2 N a mass (e.symm (u, v))) x =
        -(a^2 / 2) * (∑ x, (e.symm (u, v)) x *
          (massOperator 2 N a mass (e.symm (u, v))) x - C_quad v) +
        -(a^2 / 2) * C_quad v from by ring]
      exact Real.exp_add _ _
    -- A = ⟨φ_S,Qφ_S⟩ + 2⟨φ_S,Qφ_R⟩ (the complement-complement term cancels)
    have hA_eq : ∀ u v, A_quad u v =
        (∑ x, φ_S_of u x * (massOperator 2 N a mass (φ_S_of u)) x) +
        2 * (∑ x, φ_S_of u x * (massOperator 2 N a mass (φ_R_of v)) x) := by
      intro u v; simp only [A_quad, C_quad]; linarith [h_q_three u v]
    -- === Step 6c: A depends only on (u, v₀) ===
    -- The cross term ⟨φ_S, Q(φ_R)⟩ is independent of negative-time values:
    -- For x ∈ S₊: (Q(φ_R))(x) depends only on boundary values by block-zero
    -- (massOperator_indep_of_negativeTime). For x ∉ S₊: φ_S(x) = 0.
    have hA_indep : ∀ u (v₁ v₂ : {s // ¬isPT s} → ℝ),
        (∀ s : {s // ¬isPT s},
          ¬(0 < (-(s.1 0) : ZMod N).val ∧ (-(s.1 0) : ZMod N).val < N / 2) →
          v₁ s = v₂ s) →
        A_quad u v₁ = A_quad u v₂ := by
      intro u v₁ v₂ hv
      rw [hA_eq, hA_eq]; congr 1; congr 1
      -- Goal: cross term is the same for v₁ and v₂
      apply Finset.sum_congr rfl; intro x _
      by_cases hx : isPT x
      · -- x ∈ S₊: (Q(φ_R v))(x) is independent of v₋ by block-zero
        congr 1
        apply massOperator_indep_of_negativeTime N a mass x hx
        intro y hy; simp only [φ_R_of]
        by_cases hyp : isPT y
        · simp [dif_pos hyp]
        · simp only [dif_neg hyp]; exact hv ⟨y, hyp⟩ hy
      · -- x ∉ S₊: φ_S(x) = 0, so both sides are 0
        simp [φ_S_of, dif_neg hx]
    -- === Step 6d-e: Second Fubini, change of variables, perfect square ===
    simp_rw [h_factor]
    exact gaussian_rp_perfect_square N a mass ha hmass isPT rfl e G w A_quad C_quad
      hG_dep hGR_dep hw_dep hw_nonneg hw_boundary hA_indep
      (fun v => rfl) (fun u v => sub_add_cancel _ _)
  · -- Non-integrable: integral = 0 by Bochner convention, and 0 ≤ 0
    rw [integral_undef hint]

/-- **Core Gaussian RP as a measure integral.**

Derived from `gaussian_density_rp` via the density bridge:
  `∫ F(evalMap ω) dμ = (∫ F · ρ dφ) / (∫ ρ dφ)`

The numerator ≥ 0 by `gaussian_density_rp` and the denominator > 0
by `gaussianDensity_integral_pos`, so the ratio ≥ 0. -/
theorem gaussian_rp_with_boundary_weight (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (G : (ZMod N × ZMod N → ℝ) → ℝ)
    (hG : PositiveTimeSupported N G)
    (w : (ZMod N × ZMod N → ℝ) → ℝ)
    (hw_nonneg : ∀ φ, 0 ≤ w φ)
    (hw_boundary : BoundarySupported N w) :
    0 ≤ ∫ ω : Configuration (FinLatticeField 2 N),
      (G (evalField2D N ω)) *
      (G (fieldReflection2D N (evalField2D N ω))) *
      (w (evalField2D N ω))
      ∂(latticeGaussianMeasure 2 N a mass ha hmass) := by
  -- evalField2D N ω = fieldFromSites N (evalMap 2 N ω) by definition
  have heval : ∀ ω : Configuration (FinLatticeField 2 N),
      evalField2D N ω = fieldFromSites N (evalMap 2 N ω) := by
    intro ω; simp only [evalField2D]; congr 1; funext x
    simp only [evalMap]; congr 1; ext y
    simp [finLatticeDelta, Pi.single_apply, eq_comm]
  simp_rw [heval]
  -- Apply the density bridge: ∫ F(evalMap ω) dμ = (∫ F·ρ dφ) / (∫ ρ dφ)
  set F : FinLatticeField 2 N → ℝ := fun φ =>
    G (fieldFromSites N φ) * G (fieldReflection2D N (fieldFromSites N φ)) *
      w (fieldFromSites N φ) with hF_def
  change 0 ≤ ∫ ω, F (evalMap 2 N ω) ∂(latticeGaussianMeasure 2 N a mass ha hmass)
  rw [latticeGaussianMeasure_density_integral' 2 N a mass ha hmass]
  -- Ratio ≥ 0: numerator ≥ 0 from gaussian_density_rp, denominator > 0
  apply div_nonneg
  · exact gaussian_density_rp N a mass ha hmass G hG w hw_nonneg hw_boundary
  · exact le_of_lt (gaussianDensity_integral_pos 2 N a mass ha hmass)

/-- **Reflection positivity for the interacting lattice measure** (OS3).

For any function F supported at positive time:

  `∫ F(φ) · F(Θφ) dμ_a ≥ 0`

**Proof**: Decompose V = V₊ + V₀ + V₋ where V₊ sums over positive-time
sites, V₀ over boundary, V₋ over negative-time. Since V₋(φ) = V₊(Θφ)
(site relabeling), the Boltzmann weight factors as:

  `exp(-V) = exp(-V₊(φ)) · exp(-V₀(φ)) · exp(-V₊(Θφ))`

Setting G(φ) = F(φ)·exp(-V₊(φ)) (positive-time supported) and
w(φ) = exp(-V₀(φ)) (boundary-supported, nonneg), the integral becomes

  `(1/Z) ∫ G(φ)·G(Θφ)·w(φ) dμ_GFF ≥ 0`

by `gaussian_rp_with_boundary_weight`.

Reference: Glimm-Jaffe Ch. 6.1, Simon Ch. III.3. -/
theorem lattice_rp (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (F : (ZMod N × ZMod N → ℝ) → ℝ)
    (hF : PositiveTimeSupported N F) :
    0 ≤ ∫ ω : Configuration (FinLatticeField 2 N),
      (F (fieldFromSites N (fun x => ω (Pi.single x 1)))) *
      (F (fieldReflection2D N (fieldFromSites N (fun x => ω (Pi.single x 1)))))
      ∂(interactingLatticeMeasure 2 N P a mass ha hmass) := by
  -- Setup notation
  set mu_GFF := latticeGaussianMeasure 2 N a mass ha hmass
  set bw := boltzmannWeight 2 N P a mass
  set Vp := positiveTimeInteraction N P a mass
  set Vb := boundaryTimeInteraction N P a mass
  -- The integrand uses evalField2D N ω (definitional)
  change 0 ≤ ∫ ω, F (evalField2D N ω) *
    F (fieldReflection2D N (evalField2D N ω))
    ∂(interactingLatticeMeasure 2 N P a mass ha hmass)
  -- Step 1: Unfold interacting measure = (1/Z) · mu_GFF.withDensity(bw)
  unfold interactingLatticeMeasure
  rw [integral_smul_measure]
  -- 0 ≤ c.toReal • ∫ ... where c = (ofReal Z)⁻¹, c.toReal ≥ 0
  apply mul_nonneg ENNReal.toReal_nonneg
  -- Step 2: Rewrite withDensity integral as ∫ bw * f dmu_GFF
  set bw_nn := fun ω : Configuration (FinLatticeField 2 N) => Real.toNNReal (bw ω)
  have hbw_nn_meas : Measurable bw_nn :=
    Measurable.real_toNNReal
      ((interactionFunctional_measurable 2 N P a mass).neg.exp)
  -- ENNReal.ofReal = ↑ ∘ Real.toNNReal (definitional)
  change 0 ≤ ∫ ω, _ ∂(mu_GFF.withDensity (fun ω => ↑(bw_nn ω)))
  rw [integral_withDensity_eq_integral_smul hbw_nn_meas]
  simp_rw [NNReal.smul_def, smul_eq_mul]
  -- Simplify ↑(bw_nn ω) = bw ω
  have hbw_simp : ∀ ω : Configuration (FinLatticeField 2 N),
      (bw_nn ω : ℝ) = bw ω := fun ω =>
    Real.coe_toNNReal _ (le_of_lt (boltzmannWeight_pos 2 N P a mass ω))
  simp_rw [hbw_simp]
  -- Step 3: Factor bw * F * F∘Θ as G * G∘Θ * w
  set G := fun phi : ZMod N × ZMod N → ℝ =>
    F phi * Real.exp (-(Vp phi))
  set w := fun phi : ZMod N × ZMod N → ℝ =>
    Real.exp (-(Vb phi))
  suffices h_factor : ∀ ω : Configuration (FinLatticeField 2 N),
      bw ω * (F (evalField2D N ω) * F (fieldReflection2D N (evalField2D N ω))) =
      G (evalField2D N ω) * G (fieldReflection2D N (evalField2D N ω)) *
      w (evalField2D N ω) by
    simp_rw [h_factor]
    -- Step 4: Apply the Gaussian RP axiom
    exact gaussian_rp_with_boundary_weight N a mass ha hmass G
      (mul_positiveTimeSupported N F _ hF
        (positiveTimeInteraction_supported N P a mass))
      w (fun phi => le_of_lt (Real.exp_pos _))
      (boundaryTimeInteraction_boundarySupported N P a mass)
  -- Prove the integrand factorization
  intro ω
  set phi := evalField2D N ω
  -- bw ω = exp(-V(ω)) where V = Vp + Vb + Vn
  have h_decomp := interactionFunctional_decomposition N P a mass ω
  -- Vn(phi) = Vp(Θphi)
  have h_refl := negativeTime_eq_positiveTime_reflected N P a mass phi
  -- Expand bw = exp(-V) = exp(-(Vp + Vb + Vn))
  simp only [bw, boltzmannWeight, h_decomp, neg_add, Real.exp_add]
  -- Substitute Vn = Vp∘Θ
  rw [h_refl]
  -- Algebraic rearrangement: exp(-Vp)·exp(-Vb)·exp(-Vp∘Θ) · F · F∘Θ
  -- = (F·exp(-Vp)) · (F∘Θ·exp(-Vp∘Θ)) · exp(-Vb)
  simp only [G, w, phi]
  ring

/-- Pairing on finite lattice fields in product coordinates. -/
def pairing2D (φ g : ZMod N × ZMod N → ℝ) : ℝ :=
  ∑ tx : ZMod N × ZMod N, φ tx * g tx

/-- Finite cosine test functional used in matrix RP reduction. -/
def Fcos (n : ℕ) (c : Fin n → ℝ) (f : Fin n → (ZMod N × ZMod N → ℝ)) :
    ((ZMod N × ZMod N → ℝ) → ℝ) :=
  fun φ => ∑ i : Fin n, c i * Real.cos (pairing2D N φ (f i))

/-- Finite sine test functional used in matrix RP reduction. -/
def Fsin (n : ℕ) (c : Fin n → ℝ) (f : Fin n → (ZMod N × ZMod N → ℝ)) :
    ((ZMod N × ZMod N → ℝ) → ℝ) :=
  fun φ => ∑ i : Fin n, c i * Real.sin (pairing2D N φ (f i))

/-- If each `f i` is positive-time supported, then `Fcos` is positive-time supported. -/
theorem positiveTimeSupported_Fcos
    (n : ℕ) (c : Fin n → ℝ) (f : Fin n → (ZMod N × ZMod N → ℝ))
    (hf : ∀ i, ∀ tx : ZMod N × ZMod N, tx.1.val = 0 ∨ tx.1.val ≥ N / 2 → f i tx = 0) :
    PositiveTimeSupported N (Fcos N n c f) := by
  intro φ₁ φ₂ hEq
  unfold Fcos pairing2D
  apply Fintype.sum_congr
  intro i
  have hpair : (∑ tx : ZMod N × ZMod N, φ₁ tx * f i tx) =
      (∑ tx : ZMod N × ZMod N, φ₂ tx * f i tx) := by
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
    (n : ℕ) (c : Fin n → ℝ) (f : Fin n → (ZMod N × ZMod N → ℝ))
    (hf : ∀ i, ∀ tx : ZMod N × ZMod N, tx.1.val = 0 ∨ tx.1.val ≥ N / 2 → f i tx = 0) :
    PositiveTimeSupported N (Fsin N n c f) := by
  intro φ₁ φ₂ hEq
  unfold Fsin pairing2D
  apply Fintype.sum_congr
  intro i
  have hpair : (∑ tx : ZMod N × ZMod N, φ₁ tx * f i tx) =
      (∑ tx : ZMod N × ZMod N, φ₂ tx * f i tx) := by
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
    (φ g : ZMod N × ZMod N → ℝ) :
    pairing2D N (fieldReflection2D N φ) g =
      pairing2D N φ (g ∘ timeReflection2D N) := by
  unfold pairing2D fieldReflection2D
  let θ : ZMod N × ZMod N → ZMod N × ZMod N := timeReflection2D N
  have hθbij : Function.Bijective θ :=
    Function.Involutive.bijective (timeReflection2D_involution (N := N))
  calc
    ∑ tx : ZMod N × ZMod N, (φ ∘ timeReflection2D N) tx * g tx
        = ∑ tx : ZMod N × ZMod N, g tx * φ (timeReflection2D N tx) := by
          simp [Function.comp, mul_comm]
    _ = ∑ tx : ZMod N × ZMod N, g (θ tx) * φ (θ (θ tx)) := by
          simpa [θ] using (Function.Bijective.sum_comp hθbij (fun tx => g tx * φ (θ tx))).symm
    _ = ∑ tx : ZMod N × ZMod N, φ tx * g (timeReflection2D N tx) := by
          have hθθ : ∀ tx : ZMod N × ZMod N, θ (θ tx) = tx := by
            intro tx
            simpa [θ] using (timeReflection2D_involution (N := N) tx)
          calc
            ∑ tx : ZMod N × ZMod N, g (θ tx) * φ (θ (θ tx))
                = ∑ tx : ZMod N × ZMod N, g (θ tx) * φ tx := by
                    apply Fintype.sum_congr
                    intro tx
                    simp [hθθ]
            _ = ∑ tx : ZMod N × ZMod N, φ tx * g (timeReflection2D N tx) := by
                  apply Fintype.sum_congr
                  intro tx
                  simp [θ, mul_comm]
    _ = ∑ tx : ZMod N × ZMod N, φ tx * (g ∘ timeReflection2D N) tx := by rfl

/-- Reduction theorem: matrix RP follows from scalar RP plus trigonometric
expansion identity. -/
theorem lattice_rp_matrix_reduction
    (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (n : ℕ) (c : Fin n → ℝ)
    (f : Fin n → (ZMod N × ZMod N → ℝ))
    (hf : ∀ i, ∀ tx : ZMod N × ZMod N, tx.1.val = 0 ∨ tx.1.val ≥ N / 2 → f i tx = 0)
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
private theorem pairing2D_sub (φ g h : ZMod N × ZMod N → ℝ) :
    pairing2D N φ (g - h) = pairing2D N φ g - pairing2D N φ h := by
  unfold pairing2D
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- Pointwise trigonometric expansion identity for the RP matrix.

For any field configuration φ:
  `Σᵢⱼ cᵢcⱼ cos(⟨φ, fᵢ - fⱼ∘Θ⟩) = Fcos(φ)·Fcos(Θφ) + Fsin(φ)·Fsin(Θφ)`

Uses `cos(u-v) = cos u cos v + sin u sin v` and the product-of-sums identity. -/
private theorem rp_expansion_pointwise (n : ℕ) (c : Fin n → ℝ)
    (f : Fin n → (ZMod N × ZMod N → ℝ)) (φ : ZMod N × ZMod N → ℝ) :
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
    (f : Fin n → (ZMod N × ZMod N → ℝ))
    -- Each fᵢ is supported at positive time
    (hf : ∀ i, ∀ tx : ZMod N × ZMod N, tx.1.val = 0 ∨ tx.1.val ≥ N / 2 →
      f i tx = 0) :
    ∑ i : Fin n, ∑ j : Fin n, c i * c j *
      ∫ ω : Configuration (FinLatticeField 2 N),
        Real.cos (∑ tx : ZMod N × ZMod N,
          (fieldFromSites N (fun x => ω (Pi.single x 1)) tx) *
          (f i tx - (f j ∘ timeReflection2D N) tx))
        ∂(interactingLatticeMeasure 2 N P a mass ha hmass) ≥ 0 := by
  rw [ge_iff_le]
  -- The cosine argument matches pairing2D of evalField2D (definitionally)
  change 0 ≤ ∑ i : Fin n, ∑ j : Fin n, c i * c j *
    ∫ ω, Real.cos (pairing2D N (evalField2D N ω) (f i - f j ∘ timeReflection2D N))
      ∂(interactingLatticeMeasure 2 N P a mass ha hmass)
  apply lattice_rp_matrix_reduction N P a mass ha hmass n c f hf
  set μ := interactingLatticeMeasure 2 N P a mass ha hmass
  -- h_expand: ∑ij c_i c_j * ∫ cos dμ = ∫ Fcos·Fcos dμ + ∫ Fsin·Fsin dμ
  -- Measurability of evaluation maps
  have heval_meas : ∀ tx : ZMod N × ZMod N,
      @Measurable _ _ instMeasurableSpaceConfiguration (borel ℝ)
        (fun ω => evalField2D N ω tx) := by
    intro tx
    exact configuration_eval_measurable (Pi.single (siteEquiv N tx) 1)
  -- Measurability of pairing with a fixed test function
  have hpair_meas : ∀ (g : ZMod N × ZMod N → ℝ),
      @Measurable _ _ instMeasurableSpaceConfiguration (borel ℝ)
        (fun ω => pairing2D N (evalField2D N ω) g) := by
    intro g
    unfold pairing2D
    exact Finset.measurable_sum Finset.univ
      (fun tx _ => (heval_meas tx).mul measurable_const)
  -- Measurability of cos(pairing) and sin(pairing)
  have hcos_meas : ∀ (g : ZMod N × ZMod N → ℝ),
      @Measurable _ _ instMeasurableSpaceConfiguration (borel ℝ)
        (fun ω => Real.cos (pairing2D N (evalField2D N ω) g)) :=
    fun g => Real.measurable_cos.comp (hpair_meas g)
  have hsin_meas : ∀ (g : ZMod N × ZMod N → ℝ),
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
  have hpair_refl_meas : ∀ (g : ZMod N × ZMod N → ℝ),
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
    · change Measurable (fun ω => (∑ i, c i * Real.cos (pairing2D N (evalField2D N ω) (f i))) *
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
    · change Measurable (fun ω => (∑ i, c i * Real.sin (pairing2D N (evalField2D N ω) (f i))) *
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
