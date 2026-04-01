/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Embedding Lattice Fields into the Continuum

Defines the embedding `ι_a : FinLatticeField d N → S'(ℝ^d)` that maps
lattice fields to tempered distributions, and the pushforward measures.

## Main definitions

- `latticeEmbed` — the embedding ι_a
- `continuumMeasure` — pushforward `(ι_a)_* μ_a` on S'(ℝ²)

## Mathematical background

The embedding sends a lattice field `φ : FinLatticeSites d N → ℝ` to the
tempered distribution defined by:

  `(ι_a φ)(f) = a^d · Σ_{x ∈ Λ} φ(x) · f(a · x)`

for Schwartz functions `f ∈ S(ℝ^d)`. Here `a · x` denotes the physical
position of lattice site x (each component multiplied by the lattice spacing a).

This is a continuous linear functional on S(ℝ^d) because:
1. The sum is finite (|Λ| = N^d terms).
2. Each `f(a·x)` is well-defined for Schwartz f.
3. The map f ↦ (ι_a φ)(f) is linear and continuous (finite sum of evaluations).

The pushforward `(ι_a)_* μ_a` is then a probability measure on
`Configuration(S(ℝ^d)) = S'(ℝ^d)`.

## References

- Glimm-Jaffe, *Quantum Physics*, §19.4 (Continuum limit)
- Simon, *The P(φ)₂ Euclidean QFT*, §V
-/

import Pphi2.InteractingMeasure.LatticeMeasure
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

section ContinuumTestFunctionDefs

variable (d : ℕ)

/-! ## Continuum test function and distribution spaces

For the continuum limit, the test function space is the Schwartz space
S(ℝ^d), and distributions live in S'(ℝ^d) = Configuration(S(ℝ^d)).

We use Mathlib's `SchwartzMap` for S(ℝ^d). -/

/-- The Schwartz space S(ℝ^d) as the continuum test function space.

Elements are smooth rapidly decaying functions f : ℝ^d → ℝ.
For d=2 this is the test function space for P(Φ)₂. -/
abbrev ContinuumTestFunction :=
  SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ

/-- Translation of a Schwartz function by `v ∈ ℝ^d`: `(τ_v f)(x) = f(x - v)`.

This is a continuous linear map on S(ℝ^d), constructed via
`SchwartzMap.compCLMOfAntilipschitz` with the isometry `x ↦ x - v`. -/
noncomputable def schwartzTranslate (v : EuclideanSpace ℝ (Fin d)) :
    ContinuumTestFunction d →L[ℝ] ContinuumTestFunction d :=
  SchwartzMap.compCLMOfAntilipschitz ℝ
    (show (fun x : EuclideanSpace ℝ (Fin d) => x - v).HasTemperateGrowth from
      ((ContinuousLinearMap.id ℝ _).hasTemperateGrowth).sub
        (Function.HasTemperateGrowth.const v))
    (show AntilipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin d) => x - v) from
      fun x y => by simp [edist_sub_right])

end ContinuumTestFunctionDefs

/-! ## Low-level continuum reflection data for `d = 2`

These definitions live here rather than in `OSAxioms.lean` because the
construction predicate `IsPphi2Limit` needs to record reflection positivity of
the approximating measures without importing the full OS axiom layer. -/

/-- Spacetime for `P(Φ)₂`: Euclidean `ℝ²`. -/
abbrev SpaceTime2 := EuclideanSpace ℝ (Fin 2)

/-- Real Schwartz test functions on `ℝ²`. -/
abbrev TestFunction2 := ContinuumTestFunction 2

/-- Tempered distributions on `ℝ²`. -/
abbrev FieldConfig2 := Configuration (ContinuumTestFunction 2)

/-- Time reflection on `ℝ²`: `(t, x) ↦ (-t, x)`. -/
def timeReflection2 (p : SpaceTime2) : SpaceTime2 :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm
    (fun i => if i = 0 then -(WithLp.equiv 2 (Fin 2 → ℝ) p) i
              else (WithLp.equiv 2 (Fin 2 → ℝ) p) i)

/-- Time reflection is an involution. -/
theorem timeReflection2_involution (p : SpaceTime2) :
    timeReflection2 (timeReflection2 p) = p := by
  simp only [timeReflection2]
  ext i
  simp
  split <;> simp

/-- Time reflection as a linear map on spacetime. -/
def timeReflectionLinear : SpaceTime2 →ₗ[ℝ] SpaceTime2 where
  toFun := timeReflection2
  map_add' p q := by
    ext i
    simp [timeReflection2, WithLp.equiv, Equiv.symm]
    split <;> ring
  map_smul' c p := by
    ext i
    simp [timeReflection2, WithLp.equiv, Equiv.symm, smul_eq_mul]

/-- Time reflection as a continuous linear equivalence. -/
noncomputable def timeReflectionCLE : SpaceTime2 ≃L[ℝ] SpaceTime2 :=
  (LinearEquiv.ofInvolutive timeReflectionLinear
    timeReflection2_involution).toContinuousLinearEquiv

/-- Pullback of time reflection on real test functions. -/
noncomputable def compTimeReflection2 : TestFunction2 →L[ℝ] TestFunction2 :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ timeReflectionCLE

/-- Pointwise evaluation of reflected test functions. -/
theorem compTimeReflection2_apply (f : TestFunction2) (p : SpaceTime2) :
    compTimeReflection2 f p = f (timeReflection2 p) := rfl

/-- A spacetime point has positive time if its first coordinate is positive. -/
def hasPositiveTime2 (p : SpaceTime2) : Prop :=
  (WithLp.equiv 2 (Fin 2 → ℝ) p) 0 > 0

/-- Real Schwartz functions supported in the positive-time half-space. -/
def positiveTimeSubmodule2 : Submodule ℝ TestFunction2 where
  carrier := { f : TestFunction2 | tsupport f ⊆ { p | hasPositiveTime2 p } }
  zero_mem' := by
    simp only [Set.mem_setOf_eq, tsupport]
    exact (closure_minimal Function.support_zero.subset isClosed_empty).trans (Set.empty_subset _)
  add_mem' := fun {f g} hf hg =>
    (tsupport_add f g).trans (Set.union_subset hf hg)
  smul_mem' := fun c f hf =>
    (tsupport_smul_subset_right (fun _ : SpaceTime2 => c) f).trans hf

/-- Positive-time Schwartz test functions on `ℝ²`. -/
abbrev PositiveTimeTestFunction2 := positiveTimeSubmodule2

section LatticeEmbedding

variable (d : ℕ)

/-! ## Signed representative for ZMod N

For the lattice-to-continuum embedding, we use centered coordinates so that
the embedding commutes with time reflection (negation of the 0th coordinate).
`signedVal x` gives the representative of `x ∈ ZMod N` in `{-⌊N/2⌋, ..., ⌊(N-1)/2⌋}`. -/

variable (N : ℕ) [NeZero N]

/-- Centered/signed representative of an element of `ZMod N`.
Maps to `{-⌊N/2⌋, ..., ⌊(N-1)/2⌋}` for odd N. -/
def signedVal (n : ZMod N) : ℤ :=
  if (ZMod.val n : ℤ) ≤ (N : ℤ) / 2 then (ZMod.val n : ℤ) else (ZMod.val n : ℤ) - (N : ℤ)

/-- Key property: `signedVal` is odd for odd N.
`signedVal(-x) = -signedVal(x)` when N is odd. -/
theorem signedVal_neg (hN : Odd N) (x : ZMod N) :
    signedVal N (-x) = -signedVal N x := by
  unfold signedVal
  by_cases hx : x = 0
  · subst hx; simp [show (0 : ℤ) ≤ (N : ℤ) / 2 from by omega]
  · rw [ZMod.neg_val, if_neg hx]
    have hv_lt := ZMod.val_lt x
    have hv_pos : 0 < ZMod.val x := by
      rcases Nat.eq_zero_or_pos (ZMod.val x) with h | h
      · exact absurd ((ZMod.val_eq_zero x).mp h) hx
      · exact h
    obtain ⟨k, hk⟩ := hN
    simp only [Nat.cast_sub hv_lt.le]
    split_ifs <;> omega

/-! ## Physical position of a lattice site -/

/-- Physical position of a lattice site using **centered coordinates**.

Maps `x ∈ (ZMod N)^d` to `(a · signedVal(x₁), ..., a · signedVal(x_d)) ∈ ℝ^d`.
This uses `signedVal` (centered representatives) so that the embedding commutes
with time reflection: `physicalPosition a (Θx) = Θ(physicalPosition a x)` for odd N. -/
def physicalPosition (a : ℝ) (x : FinLatticeSites d N) :
    EuclideanSpace ℝ (Fin d) :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm (fun i => a * (signedVal N (x i) : ℝ))

/-! ## The lattice-to-continuum embedding -/

/-- Evaluate a Schwartz function at the physical position of a lattice site.

  `evalAtSite a f x = f(a · x)`

where `a · x` is the physical position of lattice site x. -/
def evalAtSite (a : ℝ) (f : ContinuumTestFunction d) (x : FinLatticeSites d N) : ℝ :=
  f (physicalPosition d N a x)

/-- The lattice-to-continuum embedding sends a lattice field φ to
a tempered distribution `ι_a(φ) ∈ S'(ℝ^d)` defined by:

  `(ι_a φ)(f) = a^d · Σ_{x ∈ Λ} φ(x) · f(a · x)`

This is a finite Riemann sum approximation to `∫ φ(x) f(x) dx`.

We define this as a function from `FinLatticeField d N` to `ℝ`-valued
functions on `ContinuumTestFunction d`. The full CLM structure (making it
an element of `Configuration (ContinuumTestFunction d)`) requires verifying
continuity in the Schwartz topology, which we axiomatize. -/
def latticeEmbedEval (a : ℝ) (φ : FinLatticeField d N)
    (f : ContinuumTestFunction d) : ℝ :=
  a ^ d * ∑ x : FinLatticeSites d N, φ x * evalAtSite d N a f x

/-- The embedding is linear in φ for each f. -/
theorem latticeEmbedEval_linear_phi (a : ℝ) (f : ContinuumTestFunction d)
    (φ₁ φ₂ : FinLatticeField d N) (c₁ c₂ : ℝ) :
    latticeEmbedEval d N a (c₁ • φ₁ + c₂ • φ₂) f =
    c₁ * latticeEmbedEval d N a φ₁ f + c₂ * latticeEmbedEval d N a φ₂ f := by
  -- Bilinearity: expand (c₁φ₁ + c₂φ₂)(x) = c₁·φ₁(x) + c₂·φ₂(x) in the sum,
  -- split, factor out a^d and cᵢ.
  simp only [latticeEmbedEval, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have : ∀ x : FinLatticeSites d N,
      (c₁ * φ₁ x + c₂ * φ₂ x) * evalAtSite d N a f x =
      c₁ * (φ₁ x * evalAtSite d N a f x) + c₂ * (φ₂ x * evalAtSite d N a f x) :=
    fun x => by ring
  simp_rw [this, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  congr 1
  · congr 1
    ext i
    ring
  · congr 1
    ext i
    ring

/-- The embedding is linear in f for each φ. -/
theorem latticeEmbedEval_linear_f (a : ℝ) (φ : FinLatticeField d N)
    (f₁ f₂ : ContinuumTestFunction d) (c₁ c₂ : ℝ) :
    latticeEmbedEval d N a φ (c₁ • f₁ + c₂ • f₂) =
    c₁ * latticeEmbedEval d N a φ f₁ + c₂ * latticeEmbedEval d N a φ f₂ := by
  simp only [latticeEmbedEval, evalAtSite]
  simp [SchwartzMap.add_apply, SchwartzMap.smul_apply, Finset.sum_add_distrib,
        Finset.mul_sum, mul_add, mul_left_comm]

/-- The full embedding as a continuous linear map from `FinLatticeField d N`
to `Configuration (ContinuumTestFunction d)`.

For each lattice field φ, the map `f ↦ a^d Σ_x φ(x) f(a·x)` is a continuous
linear functional on S(ℝ^d):
- Linearity: from `latticeEmbedEval_linear_f`
- Continuity: bounded by `(a^d · Σ|φ(x)|) · seminorm(0,0)(f)`, since point
  evaluation on Schwartz space is bounded by the sup-norm seminorm.

Constructed via `SchwartzMap.mkCLMtoNormedSpace`. -/
def latticeEmbed (a : ℝ) (ha : 0 < a) (φ : FinLatticeField d N) :
    Configuration (ContinuumTestFunction d) :=
  SchwartzMap.mkCLMtoNormedSpace
    (latticeEmbedEval d N a φ)
    (fun f g => by
      change latticeEmbedEval d N a φ (f + g) =
        latticeEmbedEval d N a φ f + latticeEmbedEval d N a φ g
      simp only [latticeEmbedEval, evalAtSite, SchwartzMap.add_apply]
      rw [← mul_add, ← Finset.sum_add_distrib]
      congr 1; apply Finset.sum_congr rfl; intro x _; ring)
    (fun r f => by
      change latticeEmbedEval d N a φ (r • f) = r * latticeEmbedEval d N a φ f
      simp only [latticeEmbedEval, evalAtSite, SchwartzMap.smul_apply, smul_eq_mul]
      conv_rhs => rw [← mul_assoc, mul_comm r, mul_assoc, Finset.mul_sum]
      congr 1; apply Finset.sum_congr rfl; intro x _; ring)
    ⟨{(0, 0)}, a ^ d * ∑ x : FinLatticeSites d N, |φ x|,
      mul_nonneg (pow_nonneg (le_of_lt ha) _) (Finset.sum_nonneg (fun x _ => abs_nonneg _)),
      fun f => by
        simp only [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply]
        simp only [latticeEmbedEval, evalAtSite, Real.norm_eq_abs]
        calc |a ^ d * ∑ x, φ x * f (physicalPosition d N a x)|
            ≤ a ^ d * ∑ x, |φ x| * |f (physicalPosition d N a x)| := by
              rw [abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt ha) _)]
              gcongr
              exact le_trans (Finset.abs_sum_le_sum_abs _ _)
                (Finset.sum_le_sum (fun x _ => le_of_eq (abs_mul _ _)))
          _ ≤ a ^ d * ∑ x, |φ x| * SchwartzMap.seminorm ℝ 0 0 f := by
              gcongr with x _
              have h := SchwartzMap.le_seminorm ℝ 0 0 f (physicalPosition d N a x)
              simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
              exact h
          _ = (a ^ d * ∑ x, |φ x|) * SchwartzMap.seminorm ℝ 0 0 f := by
              rw [← Finset.sum_mul]; ring⟩

/-- The embedding agrees with the evaluation formula. -/
theorem latticeEmbed_eval (a : ℝ) (ha : 0 < a)
    (φ : FinLatticeField d N) (f : ContinuumTestFunction d) :
    (latticeEmbed d N a ha φ) f = latticeEmbedEval d N a φ f :=
  rfl

/-- The embedding is measurable (needed for pushforward measure).

This holds because for each test function f, the map φ ↦ (ι_a φ)(f) is
linear in φ (hence continuous on the finite-dimensional space), and a map
into the weak-* dual is measurable when each evaluation is measurable. -/
theorem latticeEmbed_measurable (a : ℝ) (ha : 0 < a) :
    Measurable (latticeEmbed d N a ha) := by
  apply configuration_measurable_of_eval_measurable
  intro f
  -- Goal: Measurable (fun φ => (latticeEmbed d N a ha φ) f)
  -- By latticeEmbed_eval, this is fun φ => a^d * Σ_x φ(x) * f(a·x)
  -- which is continuous (hence measurable) in φ
  change Measurable (fun φ => latticeEmbedEval d N a φ f)
  exact (continuous_const.mul (continuous_finset_sum _ (fun x _ =>
    ((continuous_apply x).mul continuous_const)))).measurable

/-- Lift the embedding to Configuration space: compose with the canonical
evaluation map `Configuration (FinLatticeField d N) → FinLatticeField d N → ℝ`
to get `Configuration (FinLatticeField d N) → Configuration (ContinuumTestFunction d)`.

Since `Configuration E = WeakDual ℝ E`, an element `ω ∈ Configuration E`
is a continuous linear functional on E. We extract field values via
`ω(Pi.single x 1)` (evaluating ω on the basis vector at site x) and
apply the lattice embedding: `(latticeEmbedLift ω)(f) = a^d Σ_x ω(e_x) f(a·x)`. -/
def latticeEmbedLift (a : ℝ) (ha : 0 < a)
    (ω : Configuration (FinLatticeField d N)) :
    Configuration (ContinuumTestFunction d) :=
  latticeEmbed d N a ha (fun x => ω (Pi.single x 1))

/-- The lifted embedding is measurable.

Each evaluation `ω ↦ (latticeEmbedLift ω)(f)` is a finite sum of measurable
functions `ω ↦ ω(Pi.single x 1)` (measurable by `configuration_eval_measurable`)
multiplied by constants, hence measurable. -/
theorem latticeEmbedLift_measurable (a : ℝ) (ha : 0 < a) :
    Measurable (latticeEmbedLift d N a ha) := by
  apply configuration_measurable_of_eval_measurable
  intro f
  -- Goal: Measurable (fun ω => (latticeEmbedLift d N a ha ω) f)
  -- By definition, this is fun ω => latticeEmbedEval d N a (fun x => ω (Pi.single x 1)) f
  -- = fun ω => a^d * Σ_x ω(Pi.single x 1) * f(a·x)
  change Measurable (fun (ω : Configuration (FinLatticeField d N)) =>
    (latticeEmbed d N a ha (fun x => ω (Pi.single x 1))) f)
  -- Unfolds to: a^d * Σ_x ω(Pi.single x 1) * f(a·x) — measurable in ω
  exact measurable_const.mul (Finset.measurable_sum _ fun x _ =>
    (configuration_eval_measurable (Pi.single x 1)).mul measurable_const)

/-! ## Pushforward measures on S'(ℝ^d) -/

/-- The continuum-embedded measure: pushforward of the interacting lattice
measure μ_a under the lifted embedding.

  `ν_a = (ι̃_a)_* μ_a`

This is a probability measure on `Configuration (ContinuumTestFunction d)` = S'(ℝ^d). -/
def continuumMeasure (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    Measure (Configuration (ContinuumTestFunction d)) :=
  Measure.map (latticeEmbedLift d N a ha)
    (interactingLatticeMeasure d N P a mass ha hmass)

/-- The continuum-embedded measure is a probability measure.

This follows from:
1. The interacting lattice measure is a probability measure
   (by `interactingLatticeMeasure_isProbability`).
2. Pushforward preserves total mass. -/
theorem continuumMeasure_isProbability (P : InteractionPolynomial)
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    IsProbabilityMeasure (continuumMeasure d N P a mass ha hmass) := by
  unfold continuumMeasure
  have := interactingLatticeMeasure_isProbability d N P a mass ha hmass
  exact Measure.isProbabilityMeasure_map
    (latticeEmbedLift_measurable d N a ha).aemeasurable

end LatticeEmbedding

/-! ## P(φ)₂ continuum limit predicate -/

/-- **Marker predicate**: μ is a `P(Φ)₂` continuum limit measure on `S'(ℝ²)`.

A probability measure `μ` satisfies `IsPphi2Limit` if it is presented together
with a sequence of continuum-embedded approximating measures `νₖ` whose moment
and characteristic functionals converge to those of `μ`, whose bounded
continuous observables converge weakly to `μ`, and whose reflection-positive
matrices are already nonnegative. We also record the standard `Z₂` symmetry
`Measure.map Neg.neg μ = μ`.

The definition is mirrored in `Bridge.lean` by `IsPphi2ContinuumLimit`, which
uses the type aliases `FieldConfig` and `TestFun` for the same `d = 2`
configuration space. This is the minimal extra structure needed to prove
`os3_for_continuum_limit` without importing the full OS axiom layer into
`Embedding.lean`. -/
def IsPphi2Limit
    (μ : Measure FieldConfig2)
    (_P : InteractionPolynomial) (_mass : ℝ) : Prop :=
  ∃ (a : ℕ → ℝ) (ν : ℕ → Measure FieldConfig2),
    (∀ k, IsProbabilityMeasure (ν k)) ∧
    Filter.Tendsto a Filter.atTop (nhds 0) ∧
    (∀ k, 0 < a k) ∧
    (∀ (n : ℕ) (f : Fin n → TestFunction2),
      Filter.Tendsto
        (fun k => ∫ ω : FieldConfig2, ∏ i, ω (f i) ∂(ν k))
        Filter.atTop
        (nhds (∫ ω : FieldConfig2, ∏ i, ω (f i) ∂μ))) ∧
    Measure.map
      (Neg.neg : FieldConfig2 → FieldConfig2) μ = μ ∧
    -- Characteristic functional convergence: Z_{ν_k}[f] → Z_μ[f] for all f.
    -- This is the standard definition of weak convergence on nuclear spaces
    -- (Bochner-Minlos / Lévy continuity). It follows from moment convergence
    -- plus uniform exponential bounds, but is cleaner to include directly.
    (∀ (f : TestFunction2),
      Filter.Tendsto
        (fun k => ∫ ω : FieldConfig2,
          Complex.exp (Complex.I * ↑(ω f)) ∂(ν k))
        Filter.atTop
        (nhds (∫ ω : FieldConfig2,
          Complex.exp (Complex.I * ↑(ω f)) ∂μ))) ∧
    -- Lattice translation invariance: for any translation vector v, the
    -- characteristic functional of ν_k is eventually invariant under τ_v.
    -- This holds because the lattice spacings a_k → 0 can be chosen so that
    -- for any v, v is eventually a lattice vector (e.g., dyadic a_k = 2^{-k}).
    -- Inherited from `latticeMeasure_translation_invariant` via embedding.
    (∀ (v : SpaceTime2) (f : TestFunction2),
      ∀ᶠ k in Filter.atTop,
        ∫ ω : FieldConfig2,
          Complex.exp (Complex.I * ↑(ω f)) ∂(ν k) =
        ∫ ω : FieldConfig2,
          Complex.exp (Complex.I * ↑(ω (schwartzTranslate 2 v f))) ∂(ν k)) ∧
    -- Weak convergence for bounded continuous functions:
    -- ∫ g dν_k → ∫ g dμ for all bounded continuous g : Configuration → ℝ.
    -- This follows from Prokhorov's theorem (`prokhorov_configuration`).
    (∀ (g : FieldConfig2 → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Filter.Tendsto (fun k => ∫ ω, g ω ∂(ν k))
        Filter.atTop (nhds (∫ ω, g ω ∂μ))) ∧
    -- Reflection positivity for the approximating continuum measures.
    (∀ (k : ℕ) (n : ℕ) (f : Fin n → PositiveTimeTestFunction2) (c : Fin n → ℝ),
      0 ≤ ∑ i, ∑ j, c i * c j *
        (∫ ω : FieldConfig2,
          Complex.exp (Complex.I * ↑(ω ((f i : TestFunction2) -
            compTimeReflection2 (f j : TestFunction2)))) ∂(ν k)).re)

end Pphi2

end
