/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Field Decomposition Sketch — `(φ_S, φ_R)` Joint Gaussian Setup

Sketch of the genuine Glimm–Jaffe field decomposition for the bridge
discharge. Defines the structure that captures `(φ_S, φ_R)` as
independent Gaussian fields with covariances `C_S(T), C_R(T)`, and
shows how the lattice `LatticeRoughErrorSetup` can be built from
such a structure.

## Status

**Sketch / structural file.** Defines the API surface that the
field-decomposition Phase 1 work needs to populate. The actual
construction (joint measure, pushforward identity, chaos analysis
of E_R) is not built here — only the interface. See
`docs/polynomial-chaos-exp-moment-bridge-proof-plan.md` for the
mathematical plan.

## Why this structural file?

The plan-revision recognized that the simpler Wick-constant
decomposition cannot achieve uniform-in-N L² bounds. The genuine
bridge discharge needs:

* A joint measure `μ_S × μ_R` on a doubled space, with two
  independent Gaussian fields of covariances `C_S(T), C_R(T)`.
* The pushforward identity: under the addition map
  `(φ_S, φ_R) ↦ φ_S + φ_R`, the joint measure pushes to the lattice
  GFF `latticeGaussianMeasure`.
* Chaos analysis of the Wick-binomial-expanded
  `E_R = V(φ_S + φ_R) - V_S(φ_S)`, leveraging the fact that every
  term contains at least one φ_R factor.
* L² bounds via `roughCovariance_sq_summable`, controlling
  `‖C_R‖²_HS ≤ L^d · T · c_a` uniformly in N.

This file isolates the structural interface so the missing pieces
are explicit.

## Main definitions (sketch)

* `FieldDecomposition d N a mass`: bundle of the joint Gaussian
  structure (two independent Gaussian fields with covariances
  `C_S(T), C_R(T)`) plus the pushforward identity.

## Main theorems (planned)

* `latticeRoughErrorSetup_of_fieldDecomp`: from a
  `FieldDecomposition`, construct the
  `LatticeRoughErrorSetup` that the existing abstract bridge
  derivation (`bridgeAxiom_of_setup_real`) consumes.

The construction uses:
- The smooth-side bound `smooth_interaction_lower_bound_log_uniform`
  (already a theorem) applied to V_S(φ_S).
- The chaos analysis on the Wick-binomial expansion of E_R.
- The L² bound via `roughCovariance_sq_summable`.
- `chaos_neg_tail_bound` (already a theorem) for the rough tail.
- `lintegral_layer_cake_lt_top_of_eventual_decay` (already a
  theorem) for the integrability hypothesis.

## References

- pphi2/docs/polynomial-chaos-exp-moment-bridge-proof-plan.md
  (revised 2026-05-09).
- Glimm-Jaffe, *Quantum Physics*, Ch. 8.
- Simon, *P(φ)₂ Euclidean QFT*, Ch. V.
-/

import Pphi2.NelsonEstimate.LatticeBridge
import Pphi2.NelsonEstimate.LatticeSetup
import Pphi2.NelsonEstimate.CovarianceSplit
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import GaussianField.Hypercontractive

noncomputable section

namespace Pphi2

open MeasureTheory GaussianField

variable (d N : ℕ) [NeZero N] (a mass : ℝ)

/-- **Bundle of the field-decomposition setup at cutoff scale `T`.**

A `FieldDecomposition T` packages:
- A joint measure on a "doubled" Gaussian space (the smooth and
  rough fields' Gaussian phase-space).
- The smooth and rough field maps from the joint variables to
  `Configuration (FinLatticeField d N)`.
- The pushforward identity: under addition `(φ_S, φ_R) ↦ φ_S + φ_R`,
  the joint measure pushes to the lattice GFF.

In the canonical realization (per the plan):
- The doubled space is `(FinLatticeSites d N → ℝ) × (FinLatticeSites d N → ℝ)`,
  with the product measure `Measure.pi (gaussianReal 0 1) ×
  Measure.pi (gaussianReal 0 1)`.
- `φ_S(η_S)(x) := Σ_k √(C_S(T,k)) · e_k(x) · η_S(k)`.
- `φ_R(η_R)(x) := Σ_k √(C_R(T,k)) · e_k(x) · η_R(k)`.
- The pushforward equals the GFF by characteristic-function
  uniqueness (the variances `C_S + C_R = C` match).

This file leaves the `FieldDecomposition` structure abstract — its
concrete construction is the substantive Phase 1 work. The fields
required match those needed by `LatticeRoughErrorSetup` once the
addition pushforward is in hand. -/
structure FieldDecomposition (T : ℝ) where
  /-- The "doubled" Gaussian space type carrying the joint
  variables `(η_S, η_R)`. In the canonical realization, this is
  `(FinLatticeSites d N → ℝ) × (FinLatticeSites d N → ℝ)`. -/
  Joint : Type
  /-- Measurable space structure on the joint type. -/
  jointMeasurable : MeasurableSpace Joint
  /-- The joint Gaussian measure (product of two `stdGaussianFin n`'s
  in the canonical realization). -/
  μ_joint : @Measure Joint jointMeasurable
  /-- The joint measure is a probability measure. -/
  jointProbability : @IsProbabilityMeasure Joint jointMeasurable μ_joint
  /-- The smooth field: from joint variables to a configuration. -/
  φ_S : Joint → Configuration (FinLatticeField d N)
  /-- The rough field similarly. -/
  φ_R : Joint → Configuration (FinLatticeField d N)
  /-- Both field maps are measurable. -/
  φ_S_measurable :
    @Measurable Joint (Configuration (FinLatticeField d N)) jointMeasurable
      instMeasurableSpaceConfiguration φ_S
  φ_R_measurable :
    @Measurable Joint (Configuration (FinLatticeField d N)) jointMeasurable
      instMeasurableSpaceConfiguration φ_R
  /-- **Pushforward identity:** `(η_S, η_R) ↦ φ_S(η_S) + φ_R(η_R)`
  pushes the joint measure to the lattice GFF.
  Requires `0 < a, 0 < mass` for the GFF to be defined; these are
  implicit hypotheses on `(a, mass)` in the consumers. -/
  pushforward_eq_GFF :
    ∀ (ha : 0 < a) (hmass : 0 < mass),
    @Measure.map Joint (Configuration (FinLatticeField d N))
        jointMeasurable instMeasurableSpaceConfiguration
        (fun ξ => φ_S ξ + φ_R ξ) μ_joint =
      latticeGaussianMeasure d N a mass ha hmass

/-! ## Phase 1 work that remains (revised 2026-05-09 per Gemini review)

To complete the bridge discharge, the following remain:

1. **Construct a canonical `FieldDecomposition T`** for each `T > 0`,
   using:
   - The gaussian-field theorems
     `gffOrthonormalProj_pushforward_eq_stdGaussian`,
     `gffOrthonormalCoord_independent` (now theorems).
   - `Measure.pi` for the product structure on the **doubled
     2|Λ|-dimensional Gaussian** (one copy for `η_S`, one for `η_R`).
   - Spectral decomposition: φ_S, φ_R as linear combinations of the
     η_S, η_R variables weighted by `√(smoothCovEigenvalue T k)`,
     `√(roughCovEigenvalue T k)`.

2. **Pushforward identity proof**: by characteristic-function
   uniqueness, since `C_S(T, k) + C_R(T, k) = (a^d λ_k)^{-1}` (per
   `covariance_split` in CovarianceSplit.lean) and `gaussianReal` is
   characterized by its variance.

3. **Wick binomial expansion of `V(φ_S + φ_R)`**: apply
   `wickMonomial_pow_sum_expansion` (theorem in gaussian-field) at
   each lattice site to expand `:φ(x)^n:_{c_S+c_R}` into the
   bivariate Wick binomial terms.

4. **Joint chaos membership of `E_R`** (⚠ critical correction):
   `E_R = V(φ_S + φ_R) - V_S(φ_S)` is a polynomial of total degree
   `≤ deg P` in the JOINT `2|Λ|`-dimensional Gaussian variables
   `(η_S, η_R)` taken together — NOT in `η_R` conditional on `η_S`.
   This means `E_R ∈ wienerChaosLE (2|Λ|) (deg P)` of the JOINT
   standard Gaussian. The chaos analysis is **unconditional** on
   the joint space; no `condexp`, no conditional Janson, no Fubini
   integration of conditional bounds.

   Why: a conditional approach would have the L² norm of E_R
   conditional on φ_S be a *random variable* depending on `φ_S`
   (since cross-terms like `4 :φ_S³:_{c_S} φ_R` contribute
   `16 c_R · φ_S^6` to the conditional variance). Applying Janson
   conditionally then yields a tail bound where `φ_S` appears in the
   denominator of the exponent — analytically intractable.

5. **L² bound on `E_R`** (joint, deterministic):
   `‖E_R‖²_{L²(μ_joint)} ≤ K · T^δ` for some `K` depending on
   `(L, c_a)` but not on `N`. Computed via:
   - Wick orthogonality on the joint Gaussian gives a sum over
     multi-indices with rough Wick monomials;
   - At least one `:φ_R^k:_{c_R}` factor per term contributes
     `‖C_R‖²_HS^k`;
   - `roughCovariance_sq_summable` bounds `‖C_R‖²_HS ≤ |Λ| · T · a^d · c_a
     = L^d · T · c_a` uniformly in N.

6. **Apply Janson 5.10 unconditionally** on the joint `2|Λ|`-dim
   Gaussian to `E_R - E_joint[E_R] = E_R` (already centered):
   `μ_joint{|E_R| > λ ‖E_R‖_{L²(joint)}} ≤ 2 exp(-c_d λ^{2/deg P})`.
   Combined with the L² bound: with `λ = M / (2 √(K T^δ))`,
   `μ_joint{E_R ≤ -M/2} ≤ 2 exp(-c (M/(2√(K T^δ)))^{2/deg P})`.

7. **Pushforward to GFF, smooth-side bound, layer-cake assembly**:
   - The pushforward identity `(η_S, η_R) ↦ φ_S + φ_R` translates
     joint events to GFF events.
   - Smooth-side bound `V_S(φ_S) ≥ -M/2` is **deterministic**
     (pointwise on `Joint`), from `smooth_interaction_lower_bound_log_uniform`.
   - The set inclusion `{V ≤ -M} ⊆ {E_R ≤ -M/2}` is therefore a
     pointwise set-theoretic subset on the joint space. The
     unconditional joint tail bound flows directly into
     `expSqNeg_lintegral_le_of_dynamical_cutoff` via the pushforward.
   - Apply `chaos_neg_tail_bound`,
     `lintegral_layer_cake_lt_top_of_eventual_decay`, and
     `bridgeAxiom_of_setup_real` to assemble.

## ⚠ Volume constraint (Phase 3 fix per Gemini review)

The current `polynomial_chaos_exp_moment_bridge` axiom signature
`∀ a > 0, ∀ N` is **mathematically false** without a volume
constraint: the Wick polynomial `:φ⁴:_{c_a} = φ⁴ - 6c_a φ² + 3c_a²`
has minimum `-6 c_a²`, so `V_min = a^d · |Λ| · (-6 c_a²) =
-L^d · 6 c_a² → -∞` as `c_a → ∞`. The integral
`∫ exp(-2V) dμ` cannot be uniformly bounded over arbitrary `(a, N)`
since the physical volume `L = aN` is unbounded.

The Nelson exp-moment bound is an *extensive* quantity:
`E[exp(-V_a)] ≤ exp(K · L^d)` where `K` depends on the regime but
the volume factor `L^d` is essential. A uniform-in-volume `K` cannot
exist.

**Required Phase 3 fixes** (mandatory, not just recommended):
- Add `haN : a * N ≤ L` (or equivalently `(a * N)^d ≤ L^d`) to the
  hypotheses, fixing a finite physical volume `L`.
- Restrict `0 < a ≤ 1` (the UV regime).
- Allow `K` to depend on `L` (and `mass`, `P`).

The corrected signature:
```lean
theorem polynomial_chaos_exp_moment_bridge
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (L : ℝ) (hL : 0 < L) :
    ∃ (K : ℝ), 0 < K ∧
    ∀ (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1),
    ∀ (N : ℕ) [NeZero N] (haN : a * N ≤ L),
    ∫ ω, (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2
        ∂(latticeGaussianMeasure d N a mass ha hmass) ≤ K
```

The downstream consumers (`nelson_exponential_estimate_lattice`,
the asymmetric-torus variants) typically work at fixed `L` with
`a = L/N`, so the volume constraint is satisfied trivially in those
applications. -/

/-! ## Canonical realization (in progress) -/

section Canonical

variable [Fintype (ZMod N)]

/-- The canonical doubled-Gaussian phase space:
`(FinLatticeSites d N → ℝ) × (FinLatticeSites d N → ℝ)`. The first
component holds the smooth-side coordinates `η_S`, the second the
rough-side `η_R`. -/
abbrev CanonicalJoint (d N : ℕ) [NeZero N] : Type :=
  (FinLatticeSites d N → ℝ) × (FinLatticeSites d N → ℝ)

/-- The canonical joint measure: product of two i.i.d. standard
Gaussian product-measures, one on each component. -/
noncomputable def canonicalJointMeasure (d N : ℕ) [NeZero N]
    [Fintype (ZMod N)] :
    Measure (CanonicalJoint d N) :=
  Measure.prod
    (Measure.pi (fun _ : FinLatticeSites d N => ProbabilityTheory.gaussianReal 0 1))
    (Measure.pi (fun _ : FinLatticeSites d N => ProbabilityTheory.gaussianReal 0 1))

/-- The canonical smooth-side **field function** at cutoff `T`. Maps
each `(η_S, η_R) ∈ CanonicalJoint d N` to a function on lattice sites:
`x ↦ (a^d)^{-1/2} · Σ_k √(C_S(T, k')) · e_k(x) · η_S(k)`,
where `C_S(T, k')` is the smooth covariance eigenvalue at the integer
mode index `k'` corresponding to the lattice site index `k` via
`Fintype.equivFin (FinLatticeSites d N)`.

The `(a^d)^{-1/2}` prefactor implements the Glimm–Jaffe alignment: the
per-mode variance becomes `(a^d)⁻¹ · C_S(T,k')`, so that
`Var(φ_S(δ_x)) + Var(φ_R(δ_x)) = (a^d λ_k)⁻¹`, matching the GJ-aligned
GFF covariance `(a^d)⁻¹ M_a⁻¹` per `lattice_covariance_GJ_eq_spectral`.

This is a **field**, not a configuration: the `Configuration` type
is `WeakDual` (continuous linear functionals), and lifting this field
to a Configuration uses the standard pairing
`⟨g, f⟩ := Σ_x g(x) · f(x)` (see `latticeFieldToConfig` below). -/
noncomputable def canonicalSmoothFieldFunction (d N : ℕ) [NeZero N]
    [Fintype (ZMod N)] (a mass T : ℝ) (η : CanonicalJoint d N) :
    FinLatticeSites d N → ℝ :=
  fun x =>
    (Real.sqrt (a^d))⁻¹ *
    ∑ k : FinLatticeSites d N,
      Real.sqrt (smoothCovEigenvalue d N a mass T
        (Fintype.equivFin (FinLatticeSites d N) k)) *
      ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) *
      η.1 k

/-- The canonical rough-side field function at cutoff `T`. The same
`(a^d)^{-1/2}` GJ-alignment factor is included as in the smooth case. -/
noncomputable def canonicalRoughFieldFunction (d N : ℕ) [NeZero N]
    [Fintype (ZMod N)] (a mass T : ℝ) (η : CanonicalJoint d N) :
    FinLatticeSites d N → ℝ :=
  fun x =>
    (Real.sqrt (a^d))⁻¹ *
    ∑ k : FinLatticeSites d N,
      Real.sqrt (roughCovEigenvalue d N a mass T
        (Fintype.equivFin (FinLatticeSites d N) k)) *
      ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) *
      η.2 k

/-- The canonical sum field: `φ(x) = φ_S(x) + φ_R(x)`. As a field
function (`FinLatticeSites d N → ℝ`), the sum is pointwise. -/
noncomputable def canonicalSumFieldFunction (d N : ℕ) [NeZero N]
    [Fintype (ZMod N)] (a mass T : ℝ) (η : CanonicalJoint d N) :
    FinLatticeSites d N → ℝ :=
  fun x =>
    canonicalSmoothFieldFunction d N a mass T η x +
      canonicalRoughFieldFunction d N a mass T η x

/-- **Decomposition identity** (deterministic, by definition). -/
theorem canonicalSumFieldFunction_eq_smooth_plus_rough
    (d N : ℕ) [NeZero N] (a mass T : ℝ) (η : CanonicalJoint d N)
    (x : FinLatticeSites d N) :
    canonicalSumFieldFunction d N a mass T η x =
      canonicalSmoothFieldFunction d N a mass T η x +
        canonicalRoughFieldFunction d N a mass T η x :=
  rfl

/-- Lift a field `φ : FinLatticeField d N` to a `Configuration` via
the standard pairing `f ↦ Σ_x f(x) · φ(x)`. Re-implementation of the
`private def liftToConfig` in gaussian-field's `Lattice/FKG.lean`. -/
def latticeFieldToConfig (d N : ℕ) [NeZero N] (φ : FinLatticeField d N) :
    Configuration (FinLatticeField d N) :=
  { toFun := fun f => ∑ x : FinLatticeSites d N, f x * φ x
    map_add' := fun f g => by
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    map_smul' := fun r f => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
        Finset.mul_sum, mul_assoc]
    cont := continuous_finset_sum _ (fun i _ =>
      (continuous_apply i).mul continuous_const) }

@[simp] theorem latticeFieldToConfig_apply
    (d N : ℕ) [NeZero N] (φ : FinLatticeField d N)
    (f : FinLatticeField d N) :
    (latticeFieldToConfig d N φ) f =
      ∑ x : FinLatticeSites d N, f x * φ x := rfl

/-- The canonical smooth-side configuration: lift of the smooth field
function. -/
noncomputable def canonicalSmoothConfig (d N : ℕ) [NeZero N]
    (a mass T : ℝ) (η : CanonicalJoint d N) :
    Configuration (FinLatticeField d N) :=
  latticeFieldToConfig d N (canonicalSmoothFieldFunction d N a mass T η)

/-- The canonical rough-side configuration. -/
noncomputable def canonicalRoughConfig (d N : ℕ) [NeZero N]
    (a mass T : ℝ) (η : CanonicalJoint d N) :
    Configuration (FinLatticeField d N) :=
  latticeFieldToConfig d N (canonicalRoughFieldFunction d N a mass T η)

/-! ### Linearity of the canonical field functions -/

/-- The smooth field function is additive in η. -/
theorem canonicalSmoothFieldFunction_add
    (d N : ℕ) [NeZero N] (a mass T : ℝ)
    (η₁ η₂ : CanonicalJoint d N) (x : FinLatticeSites d N) :
    canonicalSmoothFieldFunction d N a mass T (η₁ + η₂) x =
      canonicalSmoothFieldFunction d N a mass T η₁ x +
        canonicalSmoothFieldFunction d N a mass T η₂ x := by
  unfold canonicalSmoothFieldFunction
  show (Real.sqrt (a^d))⁻¹ * ∑ k, _ * _ * (η₁ + η₂).1 k =
    (Real.sqrt (a^d))⁻¹ * _ + (Real.sqrt (a^d))⁻¹ * _
  rw [show (η₁ + η₂).1 = η₁.1 + η₂.1 from rfl]
  simp_rw [Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib, mul_add]

/-- The smooth field function is `ℝ`-homogeneous in η. -/
theorem canonicalSmoothFieldFunction_smul
    (d N : ℕ) [NeZero N] (a mass T : ℝ) (c : ℝ)
    (η : CanonicalJoint d N) (x : FinLatticeSites d N) :
    canonicalSmoothFieldFunction d N a mass T (c • η) x =
      c * canonicalSmoothFieldFunction d N a mass T η x := by
  unfold canonicalSmoothFieldFunction
  show (Real.sqrt (a^d))⁻¹ * ∑ k, _ * _ * (c • η).1 k =
    c * ((Real.sqrt (a^d))⁻¹ * ∑ k, _)
  rw [show (c • η).1 = c • η.1 from rfl]
  simp_rw [Pi.smul_apply, smul_eq_mul]
  rw [show ∀ S : ℝ, c * ((Real.sqrt (a^d))⁻¹ * S) =
    (Real.sqrt (a^d))⁻¹ * (c * S) by intro S; ring]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  ring

/-- The rough field function is additive in η. -/
theorem canonicalRoughFieldFunction_add
    (d N : ℕ) [NeZero N] (a mass T : ℝ)
    (η₁ η₂ : CanonicalJoint d N) (x : FinLatticeSites d N) :
    canonicalRoughFieldFunction d N a mass T (η₁ + η₂) x =
      canonicalRoughFieldFunction d N a mass T η₁ x +
        canonicalRoughFieldFunction d N a mass T η₂ x := by
  unfold canonicalRoughFieldFunction
  show (Real.sqrt (a^d))⁻¹ * ∑ k, _ * _ * (η₁ + η₂).2 k =
    (Real.sqrt (a^d))⁻¹ * _ + (Real.sqrt (a^d))⁻¹ * _
  rw [show (η₁ + η₂).2 = η₁.2 + η₂.2 from rfl]
  simp_rw [Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib, mul_add]

/-- The rough field function is `ℝ`-homogeneous in η. -/
theorem canonicalRoughFieldFunction_smul
    (d N : ℕ) [NeZero N] (a mass T : ℝ) (c : ℝ)
    (η : CanonicalJoint d N) (x : FinLatticeSites d N) :
    canonicalRoughFieldFunction d N a mass T (c • η) x =
      c * canonicalRoughFieldFunction d N a mass T η x := by
  unfold canonicalRoughFieldFunction
  show (Real.sqrt (a^d))⁻¹ * ∑ k, _ * _ * (c • η).2 k =
    c * ((Real.sqrt (a^d))⁻¹ * ∑ k, _)
  rw [show (c • η).2 = c • η.2 from rfl]
  simp_rw [Pi.smul_apply, smul_eq_mul]
  rw [show ∀ S : ℝ, c * ((Real.sqrt (a^d))⁻¹ * S) =
    (Real.sqrt (a^d))⁻¹ * (c * S) by intro S; ring]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  ring

/-! ### Measurability of the canonical field functions -/

/-- The smooth field function evaluated at a fixed site `x` is
measurable in `η`. It's a finite sum of `c_k · η.1(k)` over the
modes `k`, each of which is a continuous (hence measurable) linear
combination of the joint variables. -/
theorem canonicalSmoothFieldFunction_pointwise_measurable
    (d N : ℕ) [NeZero N] (a mass T : ℝ) (x : FinLatticeSites d N) :
    haveI : Fintype (FinLatticeSites d N) := Pi.instFintype
    Measurable (fun η : CanonicalJoint d N =>
      canonicalSmoothFieldFunction d N a mass T η x) := by
  unfold canonicalSmoothFieldFunction
  refine Measurable.const_mul ?_ _
  apply Finset.measurable_sum
  intro k _
  -- Each term: c_k * η.1(k), where c_k is constant in η.
  -- Measurability: η.1 is the first projection (measurable), then
  -- evaluation at k is measurable (component projection of Pi).
  have hπ₁ : Measurable (fun η : CanonicalJoint d N => η.1) := measurable_fst
  have hcomp : Measurable (fun η : CanonicalJoint d N => η.1 k) :=
    (measurable_pi_apply k).comp hπ₁
  exact hcomp.const_mul _

/-- The rough field function similarly. -/
theorem canonicalRoughFieldFunction_pointwise_measurable
    (d N : ℕ) [NeZero N] (a mass T : ℝ) (x : FinLatticeSites d N) :
    haveI : Fintype (FinLatticeSites d N) := Pi.instFintype
    Measurable (fun η : CanonicalJoint d N =>
      canonicalRoughFieldFunction d N a mass T η x) := by
  unfold canonicalRoughFieldFunction
  refine Measurable.const_mul ?_ _
  apply Finset.measurable_sum
  intro k _
  have hπ₂ : Measurable (fun η : CanonicalJoint d N => η.2) := measurable_snd
  have hcomp : Measurable (fun η : CanonicalJoint d N => η.2 k) :=
    (measurable_pi_apply k).comp hπ₂
  exact hcomp.const_mul _

/-- **Configuration-level decomposition identity.**
The configuration sum `canonicalSmoothConfig + canonicalRoughConfig`
equals the lift of the field-function sum, by linearity of
`latticeFieldToConfig`. -/
theorem canonicalSmoothConfig_add_canonicalRoughConfig_eq_lift_sum
    (d N : ℕ) [NeZero N] (a mass T : ℝ) (η : CanonicalJoint d N) :
    canonicalSmoothConfig d N a mass T η + canonicalRoughConfig d N a mass T η =
      latticeFieldToConfig d N (canonicalSumFieldFunction d N a mass T η) := by
  -- Both sides applied to f give Σ_x f(x) · (φ_S + φ_R)(x).
  apply ContinuousLinearMap.ext
  intro f
  show (canonicalSmoothConfig d N a mass T η) f +
      (canonicalRoughConfig d N a mass T η) f =
    (latticeFieldToConfig d N (canonicalSumFieldFunction d N a mass T η)) f
  simp only [canonicalSmoothConfig, canonicalRoughConfig,
    latticeFieldToConfig_apply, canonicalSumFieldFunction,
    canonicalSmoothFieldFunction, canonicalRoughFieldFunction]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]

/-! ### Pointwise spectral identity at the canonical decomposition

By the covariance split `C_S(T,k) + C_R(T,k) = (latticeEigenvalue k)⁻¹`
(per `covariance_split` in `CovarianceSplit.lean`), the sum
`canonicalSumFieldFunction` realizes a Gaussian field whose covariance
matches the lattice GFF — the basis for the pushforward identity.

The pointwise spectral form:
`canonicalSumFieldFunction(η)(x) = Σ_k [√(C_S(k')) · η_S(k) + √(C_R(k')) · η_R(k)] · e_k(x)`

For each `k`, the per-mode coefficient `√(C_S) η_S + √(C_R) η_R` is a
linear combination of two independent N(0,1) variables, hence
Gaussian with variance `C_S + C_R = (λ_k)⁻¹`. The full field is
Gaussian with covariance kernel
`Σ_k λ_k⁻¹ · e_k(x) e_k(y) = M_a^{-1}(x, y)`, matching the
GFF spectral covariance per `lattice_covariance_eq_spectral`.

The pushforward identity (`canonicalJointMeasure ⤳ latticeGaussianMeasure`)
then follows by characteristic-function uniqueness.

The detailed proof requires:
1. Linearity of `canonicalSumFieldFunction` in η (immediate by
   distributing sums).
2. Gaussian distribution of `Σ_k (√(C_S) η_S(k) + √(C_R) η_R(k)) · e_k(x)`
   under `canonicalJointMeasure`, with explicit covariance.
3. Comparison with `latticeGaussianFieldLaw_fourier` (in gaussian-field).

These steps are the substantive Phase 1 work that the abstract
chain consumes. -/

/-! ### Variance computation: covariance of `canonicalSumFieldFunction`

The key payoff of the canonical realization: the covariance of
`canonicalSumFieldFunction` under `canonicalJointMeasure` matches
the GJ-aligned GFF covariance pointwise, providing the input to the
pushforward identity (deferred).

Concretely, for sites `x, y : FinLatticeSites d N`:
```
  ∫ canonicalSumFieldFunction(η)(x) * canonicalSumFieldFunction(η)(y)
      ∂(canonicalJointMeasure d N)
  = (a^d)⁻¹ · Σ_k (latticeEigenvalue d N a mass k)⁻¹
              · e_k(x) · e_k(y)
```
which by `lattice_covariance_GJ_eq_spectral` equals
`GaussianField.covariance (latticeCovarianceGJ d N a mass ha hmass) δ_x δ_y`,
i.e. the GJ-aligned GFF two-point function. -/

section Variance

open ProbabilityTheory MeasureTheory

variable (d N : ℕ) [NeZero N] [Fintype (ZMod N)] (a mass : ℝ)

/-- **Mean of a single coordinate** under `Measure.pi (gaussianReal 0 1)`.
Pulls back through `measurePreserving_eval` to the marginal mean. -/
private lemma pi_gaussian_eval_integral_zero {I : Type*} [Fintype I] (k : I) :
    ∫ η : I → ℝ, η k
      ∂(Measure.pi (fun _ : I => gaussianReal 0 1)) = 0 := by
  rw [integral_eval]
  exact integral_id_gaussianReal

/-- **Second moment of a single coordinate** under `Measure.pi (gaussianReal 0 1)`.
Pulls back through `integral_comp_eval` to `integral_sq_gaussianReal`. -/
private lemma pi_gaussian_eval_integral_sq {I : Type*} [Fintype I] (k : I) :
    ∫ η : I → ℝ, (η k) ^ 2
      ∂(Measure.pi (fun _ : I => gaussianReal 0 1)) = 1 := by
  have h_meas_sq : Measurable (fun x : ℝ => x ^ 2) := by fun_prop
  have h_eq : ∫ η : I → ℝ, (η k) ^ 2
      ∂(Measure.pi (fun _ : I => gaussianReal 0 1)) =
      ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) := by
    have := integral_comp_eval (μ := fun _ : I => gaussianReal 0 1)
      (i := k) (f := fun x : ℝ => x ^ 2) h_meas_sq.aestronglyMeasurable
    convert this using 1
  rw [h_eq, integral_sq_gaussianReal 1]
  norm_num

/-- **Cross-moment of two distinct coordinates vanishes** under
`Measure.pi (gaussianReal 0 1)`. The projections at distinct indices
are independent (`iIndepFun_pi` on the identity maps), and each has
mean zero. -/
private lemma pi_gaussian_eval_cross_zero {I : Type*} [Fintype I]
    {k l : I} (hkl : k ≠ l) :
    ∫ η : I → ℝ, η k * η l
      ∂(Measure.pi (fun _ : I => gaussianReal 0 1)) = 0 := by
  -- The pi-marginals at k and l are independent, both with mean zero.
  haveI : ∀ i : I, IsProbabilityMeasure
      ((fun _ : I => gaussianReal 0 1) i) := by
    intro i; infer_instance
  have h_indep_id : iIndepFun (fun (i : I) η => (id : ℝ → ℝ) (η i))
      (Measure.pi (fun _ : I => gaussianReal 0 1)) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have h_indep_kl : IndepFun (fun η : I → ℝ => η k) (fun η : I → ℝ => η l)
      (Measure.pi (fun _ : I => gaussianReal 0 1)) :=
    h_indep_id.indepFun hkl
  have h_meas_k : AEStronglyMeasurable (fun η : I → ℝ => η k)
      (Measure.pi (fun _ : I => gaussianReal 0 1)) :=
    (measurable_pi_apply k).aestronglyMeasurable
  have h_meas_l : AEStronglyMeasurable (fun η : I → ℝ => η l)
      (Measure.pi (fun _ : I => gaussianReal 0 1)) :=
    (measurable_pi_apply l).aestronglyMeasurable
  rw [h_indep_kl.integral_fun_mul_eq_mul_integral h_meas_k h_meas_l]
  rw [pi_gaussian_eval_integral_zero, pi_gaussian_eval_integral_zero]
  ring

/-- **Cross-moment of two coordinates** under `Measure.pi (gaussianReal 0 1)`:
the standard Kronecker delta from i.i.d. standard Gaussians. -/
private lemma pi_gaussian_eval_cross {I : Type*} [Fintype I] [DecidableEq I] (k l : I) :
    ∫ η : I → ℝ, η k * η l
      ∂(Measure.pi (fun _ : I => gaussianReal 0 1)) =
    (if k = l then (1 : ℝ) else 0) := by
  by_cases h : k = l
  · subst h
    simp only [if_true]
    have h_sq : (fun η : I → ℝ => η k * η k) = (fun η : I → ℝ => (η k) ^ 2) := by
      funext η; ring
    rw [h_sq, pi_gaussian_eval_integral_sq]
  · simp only [if_neg h]
    exact pi_gaussian_eval_cross_zero h

/-- **Cross-moment identity for a finite product of i.i.d. standard
Gaussians.** For any finite indexing type `I` and any two functions
`p, q : I → ℝ`, the bilinear integral
```
  ∫ η : I → ℝ, (∑ k, p k * η k) * (∑ l, q l * η l)
      ∂(Measure.pi (fun _ : I => gaussianReal 0 1))
  = ∑ k, p k * q k
```

This is the standard Plancherel/Parseval identity for i.i.d. `N(0,1)`
random variables: the covariance matrix of `(η_k)_{k ∈ I}` is the
identity, so for linear combinations `X = Σ p_k η_k` and `Y = Σ q_l η_l`,
the inner product of the coefficient vectors gives the cross-expectation. -/
theorem pi_gaussian_bilinear_moment {I : Type*} [Fintype I]
    (p q : I → ℝ) :
    ∫ η : I → ℝ, (∑ k, p k * η k) * (∑ l, q l * η l)
      ∂(Measure.pi (fun _ : I => gaussianReal 0 1)) =
      ∑ k, p k * q k := by
  classical
  -- Per-coordinate L² membership, used to certify the double-sum integrand as L¹.
  have h_memLp : ∀ k : I, MemLp (fun η : I → ℝ => η k) 2
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
    intro k
    have h : MemLp (id ∘ (fun η : I → ℝ => η k)) 2
        (Measure.pi (fun _ : I => gaussianReal 0 1)) :=
      MemLp.comp_measurePreserving IsGaussian.memLp_two_id
        (measurePreserving_eval (μ := fun _ : I => gaussianReal 0 1) k)
    exact h
  -- Distribute the product of sums.
  have h_distrib : ∀ η : I → ℝ,
      (∑ k, p k * η k) * (∑ l, q l * η l) =
      ∑ k, ∑ l, (p k * q l) * (η k * η l) := by
    intro η
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    ring
  simp_rw [h_distrib]
  -- Move the outer sum out of the integral.
  rw [integral_finset_sum]
  swap
  · intro k _
    refine integrable_finset_sum _ (fun l _ => ?_)
    refine Integrable.const_mul ?_ _
    exact MemLp.integrable_mul (h_memLp k) (h_memLp l)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  -- Move the inner sum out of the integral.
  rw [integral_finset_sum]
  swap
  · intro l _
    refine Integrable.const_mul ?_ _
    exact MemLp.integrable_mul (h_memLp k) (h_memLp l)
  -- Pull the constant `p k * q l` out, apply the cross-moment identity.
  simp_rw [integral_const_mul]
  simp_rw [pi_gaussian_eval_cross]
  -- The double sum collapses on the diagonal.
  rw [Finset.sum_eq_single k]
  · simp
  · intro l _ hlk
    rw [if_neg (Ne.symm hlk)]
    ring
  · intro h
    exact (h (Finset.mem_univ k)).elim

/-- Integrability of the bilinear integrand in `pi_gaussian_bilinear_moment`. -/
private lemma pi_gaussian_bilinear_integrable {I : Type*} [Fintype I]
    (p q : I → ℝ) :
    Integrable (fun η : I → ℝ => (∑ k, p k * η k) * (∑ l, q l * η l))
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
  classical
  have h_memLp : ∀ k : I, MemLp (fun η : I → ℝ => η k) 2
      (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
    intro k
    have h : MemLp (id ∘ (fun η : I → ℝ => η k)) 2
        (Measure.pi (fun _ : I => gaussianReal 0 1)) :=
      MemLp.comp_measurePreserving IsGaussian.memLp_two_id
        (measurePreserving_eval (μ := fun _ : I => gaussianReal 0 1) k)
    exact h
  have h_distrib : ∀ η : I → ℝ,
      (∑ k, p k * η k) * (∑ l, q l * η l) =
      ∑ k, ∑ l, (p k * q l) * (η k * η l) := by
    intro η
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    ring
  rw [show (fun η : I → ℝ => (∑ k, p k * η k) * (∑ l, q l * η l)) =
      fun η : I → ℝ => ∑ k, ∑ l, (p k * q l) * (η k * η l) from funext h_distrib]
  refine integrable_finset_sum _ (fun k _ => ?_)
  refine integrable_finset_sum _ (fun l _ => ?_)
  refine Integrable.const_mul ?_ _
  exact MemLp.integrable_mul (h_memLp k) (h_memLp l)

/-- Integrability of the smooth marginal field at a fixed site. -/
private lemma canonicalSmoothFieldFunction_marginal_integrable
    [Fintype (ZMod N)] (T : ℝ) (x : FinLatticeSites d N) :
    Integrable (fun η_S : FinLatticeSites d N → ℝ =>
      (Real.sqrt (a^d))⁻¹ *
      ∑ k : FinLatticeSites d N,
        Real.sqrt (smoothCovEigenvalue d N a mass T
          (Fintype.equivFin (FinLatticeSites d N) k)) *
        ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) *
        η_S k)
      (Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1)) := by
  have h_sum : Integrable (fun η_S : FinLatticeSites d N → ℝ =>
      ∑ k : FinLatticeSites d N,
        Real.sqrt (smoothCovEigenvalue d N a mass T
          (Fintype.equivFin (FinLatticeSites d N) k)) *
        ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) *
        η_S k)
      (Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1)) := by
    refine integrable_finset_sum _ (fun k _ => ?_)
    have h_int : Integrable (fun η_S : FinLatticeSites d N → ℝ => η_S k)
        (Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1)) := by
      exact integrable_eval IsGaussian.integrable_id
    convert h_int.const_mul (Real.sqrt (smoothCovEigenvalue d N a mass T
      (Fintype.equivFin (FinLatticeSites d N) k)) *
      ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x))
  exact h_sum.const_mul _

/-- Integrability of the rough marginal field at a fixed site. -/
private lemma canonicalRoughFieldFunction_marginal_integrable
    [Fintype (ZMod N)] (T : ℝ) (x : FinLatticeSites d N) :
    Integrable (fun η_R : FinLatticeSites d N → ℝ =>
      (Real.sqrt (a^d))⁻¹ *
      ∑ k : FinLatticeSites d N,
        Real.sqrt (roughCovEigenvalue d N a mass T
          (Fintype.equivFin (FinLatticeSites d N) k)) *
        ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) *
        η_R k)
      (Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1)) := by
  have h_sum : Integrable (fun η_R : FinLatticeSites d N → ℝ =>
      ∑ k : FinLatticeSites d N,
        Real.sqrt (roughCovEigenvalue d N a mass T
          (Fintype.equivFin (FinLatticeSites d N) k)) *
        ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) *
        η_R k)
      (Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1)) := by
    refine integrable_finset_sum _ (fun k _ => ?_)
    have h_int : Integrable (fun η_R : FinLatticeSites d N → ℝ => η_R k)
        (Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1)) := by
      exact integrable_eval IsGaussian.integrable_id
    convert h_int.const_mul (Real.sqrt (roughCovEigenvalue d N a mass T
      (Fintype.equivFin (FinLatticeSites d N) k)) *
      ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x))
  exact h_sum.const_mul _

/-- **Marginal mean of `canonicalSmoothFieldFunction`** evaluated at a
single site is zero (under the smooth-side `Measure.pi gaussianReal 0 1`).

This is the linear combination of mean-zero i.i.d. Gaussians; each
`∫ η_k dμ = 0` by `pi_gaussian_eval_integral_zero`. -/
private lemma canonicalSmoothFieldFunction_marginal_integral_zero
    [Fintype (ZMod N)] (T : ℝ) (x : FinLatticeSites d N) :
    ∫ η_S : FinLatticeSites d N → ℝ,
      (Real.sqrt (a^d))⁻¹ *
      ∑ k : FinLatticeSites d N,
        Real.sqrt (smoothCovEigenvalue d N a mass T
          (Fintype.equivFin (FinLatticeSites d N) k)) *
        ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) *
        η_S k
      ∂(Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1)) = 0 := by
  -- Apply `pi_gaussian_bilinear_moment` with `q ≡ 0` (so `∑ p_k q_k = 0`).
  -- Concretely, the integrand has the form
  --   `c · (∑ p_k η_S k)` where p_k = √(C_S(k')) · e_k(x).
  -- We compute `∫ ∑ p_k η_S k dμ = ∑ p_k · 0 = 0`.
  rw [integral_const_mul]
  rw [integral_finset_sum]
  swap
  · intro k _
    have h_int : Integrable (fun η_S : FinLatticeSites d N → ℝ => η_S k)
        (Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1)) := by
      exact integrable_eval IsGaussian.integrable_id
    -- `c_k * η_S k = c_k * (η_S k)` — the constant on the left.
    convert h_int.const_mul (Real.sqrt (smoothCovEigenvalue d N a mass T
      (Fintype.equivFin (FinLatticeSites d N) k)) *
      ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x))
  have h_zero : ∀ k : FinLatticeSites d N,
      ∫ η_S : FinLatticeSites d N → ℝ,
        Real.sqrt (smoothCovEigenvalue d N a mass T
          (Fintype.equivFin (FinLatticeSites d N) k)) *
        ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) *
        η_S k
        ∂(Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1)) = 0 := by
    intro k
    rw [show (fun η_S : FinLatticeSites d N → ℝ =>
        Real.sqrt (smoothCovEigenvalue d N a mass T
          (Fintype.equivFin (FinLatticeSites d N) k)) *
          ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) *
          η_S k) =
        fun η_S : FinLatticeSites d N → ℝ =>
        (Real.sqrt (smoothCovEigenvalue d N a mass T
          (Fintype.equivFin (FinLatticeSites d N) k)) *
          ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x)) * η_S k from rfl]
    rw [integral_const_mul, pi_gaussian_eval_integral_zero, mul_zero]
  -- Inner sum is zero by `h_zero` applied at every site (modulo
  -- a typeclass-resolution discrepancy on `Fintype (ZMod N)`,
  -- bridged by `convert`).
  refine mul_eq_zero_of_right _ ?_
  refine Finset.sum_eq_zero fun k _ => ?_
  exact h_zero k

/-- The rough-side analogue. -/
private lemma canonicalRoughFieldFunction_marginal_integral_zero
    [Fintype (ZMod N)] (T : ℝ) (y : FinLatticeSites d N) :
    ∫ η_R : FinLatticeSites d N → ℝ,
      (Real.sqrt (a^d))⁻¹ *
      ∑ k : FinLatticeSites d N,
        Real.sqrt (roughCovEigenvalue d N a mass T
          (Fintype.equivFin (FinLatticeSites d N) k)) *
        ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) y) *
        η_R k
      ∂(Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1)) = 0 := by
  rw [integral_const_mul]
  rw [integral_finset_sum]
  swap
  · intro k _
    have h_int : Integrable (fun η_R : FinLatticeSites d N → ℝ => η_R k)
        (Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1)) := by
      exact integrable_eval IsGaussian.integrable_id
    convert h_int.const_mul (Real.sqrt (roughCovEigenvalue d N a mass T
      (Fintype.equivFin (FinLatticeSites d N) k)) *
      ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) y))
  have h_zero : ∀ k : FinLatticeSites d N,
      ∫ η_R : FinLatticeSites d N → ℝ,
        Real.sqrt (roughCovEigenvalue d N a mass T
          (Fintype.equivFin (FinLatticeSites d N) k)) *
        ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) y) *
        η_R k
        ∂(Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1)) = 0 := by
    intro k
    rw [show (fun η_R : FinLatticeSites d N → ℝ =>
        Real.sqrt (roughCovEigenvalue d N a mass T
          (Fintype.equivFin (FinLatticeSites d N) k)) *
          ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) y) *
          η_R k) =
        fun η_R : FinLatticeSites d N → ℝ =>
        (Real.sqrt (roughCovEigenvalue d N a mass T
          (Fintype.equivFin (FinLatticeSites d N) k)) *
          ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) y)) * η_R k from rfl]
    rw [integral_const_mul, pi_gaussian_eval_integral_zero, mul_zero]
  -- Inner sum is zero by `h_zero` applied at every site (modulo
  -- a typeclass-resolution discrepancy on `Fintype (ZMod N)`,
  -- bridged by `convert`).
  refine mul_eq_zero_of_right _ ?_
  refine Finset.sum_eq_zero fun k _ => ?_
  exact h_zero k

/-- **Cross-moment of smooth and rough fields vanishes.**

Under `canonicalJointMeasure`, the smooth field depends only on
`η.1` and the rough field only on `η.2`, and the two components are
independent (it is a `Measure.prod`). Each marginal is mean zero
(linear in i.i.d. mean-zero Gaussians), so the cross-expectation is
the product `0 · 0 = 0`. -/
theorem canonicalSmoothRough_cross_moment_zero
    (T : ℝ) (x y : FinLatticeSites d N) :
    ∫ η : CanonicalJoint d N,
      canonicalSmoothFieldFunction d N a mass T η x *
        canonicalRoughFieldFunction d N a mass T η y
      ∂(canonicalJointMeasure d N) = 0 := by
  rw [canonicalJointMeasure]
  simp only [canonicalSmoothFieldFunction, canonicalRoughFieldFunction]
  have h_factor :
      ∫ η : CanonicalJoint d N,
        ((Real.sqrt (a^d))⁻¹ *
            ∑ k : FinLatticeSites d N,
              Real.sqrt (smoothCovEigenvalue d N a mass T
                (Fintype.equivFin (FinLatticeSites d N) k)) *
              ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) *
              η.1 k) *
          ((Real.sqrt (a^d))⁻¹ *
            ∑ k : FinLatticeSites d N,
              Real.sqrt (roughCovEigenvalue d N a mass T
                (Fintype.equivFin (FinLatticeSites d N) k)) *
              ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) y) *
              η.2 k)
        ∂(Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1)).prod
          (Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1)) =
      (∫ η_S : FinLatticeSites d N → ℝ,
        (Real.sqrt (a^d))⁻¹ *
          ∑ k : FinLatticeSites d N,
            Real.sqrt (smoothCovEigenvalue d N a mass T
              (Fintype.equivFin (FinLatticeSites d N) k)) *
            ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) *
            η_S k
        ∂(Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1))) *
      (∫ η_R : FinLatticeSites d N → ℝ,
        (Real.sqrt (a^d))⁻¹ *
          ∑ k : FinLatticeSites d N,
            Real.sqrt (roughCovEigenvalue d N a mass T
              (Fintype.equivFin (FinLatticeSites d N) k)) *
            ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) y) *
            η_R k
        ∂(Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1))) := by
    simpa [CanonicalJoint] using
      (integral_prod_mul
        (μ := Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1))
        (ν := Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1))
        (f := fun η_S : FinLatticeSites d N → ℝ =>
          (Real.sqrt (a^d))⁻¹ *
            ∑ k : FinLatticeSites d N,
              Real.sqrt (smoothCovEigenvalue d N a mass T
                (Fintype.equivFin (FinLatticeSites d N) k)) *
              ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) *
              η_S k)
        (g := fun η_R : FinLatticeSites d N → ℝ =>
          (Real.sqrt (a^d))⁻¹ *
            ∑ k : FinLatticeSites d N,
              Real.sqrt (roughCovEigenvalue d N a mass T
                (Fintype.equivFin (FinLatticeSites d N) k)) *
              ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) y) *
              η_R k))
  rw [h_factor, canonicalSmoothFieldFunction_marginal_integral_zero,
    canonicalRoughFieldFunction_marginal_integral_zero]
  ring


/-- `smoothCovEigenvalue` is nonneg. -/
private lemma smoothCovEigenvalue_nonneg
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T) (m : ℕ) :
    0 ≤ smoothCovEigenvalue d N a mass T m := by
  exact le_of_lt (smoothCovEigenvalue_pos d N a mass T hT m ha hmass)

/-- `roughCovEigenvalue` is nonneg when `T ≥ 0`. -/
private lemma roughCovEigenvalue_nonneg
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T) (m : ℕ) :
    0 ≤ roughCovEigenvalue d N a mass T m := by
  exact le_of_lt (roughCovEigenvalue_pos d N a mass T hT m ha hmass)

/-- **Smooth-smooth self-moment.**
`∫ φ_S(x) · φ_S(y) dμ_joint = (a^d)⁻¹ · Σ_k C_S(k') · e_k(x) · e_k(y)`. -/
private lemma canonicalSmoothFieldFunction_self_moment
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (x y : FinLatticeSites d N) :
    ∫ η : CanonicalJoint d N,
      canonicalSmoothFieldFunction d N a mass T η x *
        canonicalSmoothFieldFunction d N a mass T η y
      ∂(canonicalJointMeasure d N) =
    (a^d : ℝ)⁻¹ *
      ∑ k : FinLatticeSites d N,
        smoothCovEigenvalue d N a mass T
          (Fintype.equivFin (FinLatticeSites d N) k) *
        ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) *
        ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) y) := by
  rw [canonicalJointMeasure]
  simp only [canonicalSmoothFieldFunction]
  have h_fst :=
    integral_fun_fst (E := ℝ)
      (μ := Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1))
      (ν := Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1))
      (f := fun η_S : FinLatticeSites d N → ℝ =>
        ((Real.sqrt (a^d))⁻¹ *
          ∑ k : FinLatticeSites d N,
            Real.sqrt (smoothCovEigenvalue d N a mass T
              (Fintype.equivFin (FinLatticeSites d N) k)) *
            ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) *
            η_S k) *
        ((Real.sqrt (a^d))⁻¹ *
          ∑ k : FinLatticeSites d N,
            Real.sqrt (smoothCovEigenvalue d N a mass T
              (Fintype.equivFin (FinLatticeSites d N) k)) *
            ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) y) *
            η_S k))
  simp at h_fst
  rw [h_fst]
  have ha_d_pos : (0 : ℝ) < a^d := pow_pos ha d
  have hsqrt_sq : (Real.sqrt (a^d))⁻¹ * (Real.sqrt (a^d))⁻¹ = (a^d : ℝ)⁻¹ := by
    rw [← mul_inv, ← Real.sqrt_mul (le_of_lt ha_d_pos),
        Real.sqrt_mul_self (le_of_lt ha_d_pos)]
  have h_rewrite : ∀ η_S : FinLatticeSites d N → ℝ,
      ((Real.sqrt (a^d))⁻¹ *
        ∑ k : FinLatticeSites d N,
          Real.sqrt (smoothCovEigenvalue d N a mass T
            (Fintype.equivFin (FinLatticeSites d N) k)) *
          ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) *
          η_S k) *
      ((Real.sqrt (a^d))⁻¹ *
        ∑ k : FinLatticeSites d N,
          Real.sqrt (smoothCovEigenvalue d N a mass T
            (Fintype.equivFin (FinLatticeSites d N) k)) *
          ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) y) *
          η_S k) =
      (a^d : ℝ)⁻¹ *
        ((∑ k : FinLatticeSites d N,
            (Real.sqrt (smoothCovEigenvalue d N a mass T
              (Fintype.equivFin (FinLatticeSites d N) k)) *
              ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x)) *
              η_S k) *
        (∑ l : FinLatticeSites d N,
            (Real.sqrt (smoothCovEigenvalue d N a mass T
              (Fintype.equivFin (FinLatticeSites d N) l)) *
              ((massEigenvectorBasis d N a mass l : EuclideanSpace ℝ _) y)) *
              η_S l)) := by
    intro η_S
    rw [show ∀ A B C D : ℝ, (A * B) * (C * D) = (A * C) * (B * D) by intros; ring,
      hsqrt_sq]
  simp_rw [h_rewrite, integral_const_mul]
  rw [pi_gaussian_bilinear_moment
    (p := fun k => Real.sqrt (smoothCovEigenvalue d N a mass T
      (Fintype.equivFin (FinLatticeSites d N) k)) *
      ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x))
    (q := fun l => Real.sqrt (smoothCovEigenvalue d N a mass T
      (Fintype.equivFin (FinLatticeSites d N) l)) *
      ((massEigenvectorBasis d N a mass l : EuclideanSpace ℝ _) y))]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hC : 0 ≤ smoothCovEigenvalue d N a mass T
      (Fintype.equivFin (FinLatticeSites d N) k) :=
    smoothCovEigenvalue_nonneg d N a mass ha hmass T hT _
  have h_sq : Real.sqrt (smoothCovEigenvalue d N a mass T
      (Fintype.equivFin (FinLatticeSites d N) k)) *
      Real.sqrt (smoothCovEigenvalue d N a mass T
        (Fintype.equivFin (FinLatticeSites d N) k)) =
      smoothCovEigenvalue d N a mass T
        (Fintype.equivFin (FinLatticeSites d N) k) :=
    Real.mul_self_sqrt hC
  linear_combination
    ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) *
      ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) y) * h_sq

/-- **Rough-rough self-moment.** Analogous to the smooth-smooth case. -/
private lemma canonicalRoughFieldFunction_self_moment
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (x y : FinLatticeSites d N) :
    ∫ η : CanonicalJoint d N,
      canonicalRoughFieldFunction d N a mass T η x *
        canonicalRoughFieldFunction d N a mass T η y
      ∂(canonicalJointMeasure d N) =
    (a^d : ℝ)⁻¹ *
      ∑ k : FinLatticeSites d N,
        roughCovEigenvalue d N a mass T
          (Fintype.equivFin (FinLatticeSites d N) k) *
        ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) *
        ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) y) := by
  rw [canonicalJointMeasure]
  simp only [canonicalRoughFieldFunction]
  have h_snd :=
    integral_fun_snd (E := ℝ)
      (μ := Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1))
      (ν := Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1))
      (f := fun η_R : FinLatticeSites d N → ℝ =>
        ((Real.sqrt (a^d))⁻¹ *
          ∑ k : FinLatticeSites d N,
            Real.sqrt (roughCovEigenvalue d N a mass T
              (Fintype.equivFin (FinLatticeSites d N) k)) *
            ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) *
            η_R k) *
        ((Real.sqrt (a^d))⁻¹ *
          ∑ k : FinLatticeSites d N,
            Real.sqrt (roughCovEigenvalue d N a mass T
              (Fintype.equivFin (FinLatticeSites d N) k)) *
            ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) y) *
            η_R k))
  simp at h_snd
  rw [h_snd]
  have ha_d_pos : (0 : ℝ) < a^d := pow_pos ha d
  have hsqrt_sq : (Real.sqrt (a^d))⁻¹ * (Real.sqrt (a^d))⁻¹ = (a^d : ℝ)⁻¹ := by
    rw [← mul_inv, ← Real.sqrt_mul (le_of_lt ha_d_pos),
        Real.sqrt_mul_self (le_of_lt ha_d_pos)]
  have h_rewrite : ∀ η_R : FinLatticeSites d N → ℝ,
      ((Real.sqrt (a^d))⁻¹ *
        ∑ k : FinLatticeSites d N,
          Real.sqrt (roughCovEigenvalue d N a mass T
            (Fintype.equivFin (FinLatticeSites d N) k)) *
          ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) *
          η_R k) *
      ((Real.sqrt (a^d))⁻¹ *
        ∑ k : FinLatticeSites d N,
          Real.sqrt (roughCovEigenvalue d N a mass T
            (Fintype.equivFin (FinLatticeSites d N) k)) *
          ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) y) *
          η_R k) =
      (a^d : ℝ)⁻¹ *
        ((∑ k : FinLatticeSites d N,
            (Real.sqrt (roughCovEigenvalue d N a mass T
              (Fintype.equivFin (FinLatticeSites d N) k)) *
              ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x)) *
              η_R k) *
        (∑ l : FinLatticeSites d N,
            (Real.sqrt (roughCovEigenvalue d N a mass T
              (Fintype.equivFin (FinLatticeSites d N) l)) *
              ((massEigenvectorBasis d N a mass l : EuclideanSpace ℝ _) y)) *
              η_R l)) := by
    intro η_R
    rw [show ∀ A B C D : ℝ, (A * B) * (C * D) = (A * C) * (B * D) by intros; ring,
      hsqrt_sq]
  simp_rw [h_rewrite, integral_const_mul]
  rw [pi_gaussian_bilinear_moment
    (p := fun k => Real.sqrt (roughCovEigenvalue d N a mass T
      (Fintype.equivFin (FinLatticeSites d N) k)) *
      ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x))
    (q := fun l => Real.sqrt (roughCovEigenvalue d N a mass T
      (Fintype.equivFin (FinLatticeSites d N) l)) *
      ((massEigenvectorBasis d N a mass l : EuclideanSpace ℝ _) y))]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hC : 0 ≤ roughCovEigenvalue d N a mass T
      (Fintype.equivFin (FinLatticeSites d N) k) :=
    roughCovEigenvalue_nonneg (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT _
  have h_sq : Real.sqrt (roughCovEigenvalue d N a mass T
      (Fintype.equivFin (FinLatticeSites d N) k)) *
      Real.sqrt (roughCovEigenvalue d N a mass T
        (Fintype.equivFin (FinLatticeSites d N) k)) =
      roughCovEigenvalue d N a mass T
        (Fintype.equivFin (FinLatticeSites d N) k) :=
    Real.mul_self_sqrt hC
  linear_combination
    ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) *
      ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) y) * h_sq

/-- **Cross-moment swap (rough × smooth = 0).** -/
private lemma canonicalRoughSmooth_cross_moment_zero
    (T : ℝ) (x y : FinLatticeSites d N) :
    ∫ η : CanonicalJoint d N,
      canonicalRoughFieldFunction d N a mass T η x *
        canonicalSmoothFieldFunction d N a mass T η y
      ∂(canonicalJointMeasure d N) = 0 := by
  have h_swap : ∀ η : CanonicalJoint d N,
      canonicalRoughFieldFunction d N a mass T η x *
        canonicalSmoothFieldFunction d N a mass T η y =
      canonicalSmoothFieldFunction d N a mass T η y *
        canonicalRoughFieldFunction d N a mass T η x := fun _ => mul_comm _ _
  rw [integral_congr_ae (Filter.Eventually.of_forall h_swap)]
  exact canonicalSmoothRough_cross_moment_zero d N a mass T y x

/-- **The covariance of `canonicalSumFieldFunction` matches the GJ-aligned
GFF spectral covariance.** -/
theorem canonicalSumFieldFunction_covariance
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (x y : FinLatticeSites d N) :
    ∫ η : CanonicalJoint d N,
      canonicalSumFieldFunction d N a mass T η x *
        canonicalSumFieldFunction d N a mass T η y
      ∂(canonicalJointMeasure d N) =
    (a^d : ℝ)⁻¹ *
      ∑ k : FinLatticeSites d N,
        (latticeEigenvalue d N a mass
          (Fintype.equivFin (FinLatticeSites d N) k))⁻¹ *
        ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) *
        ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) y) := by
  -- Use the additive structure of `canonicalSumFieldFunction = φ_S + φ_R`
  -- and split via the self-moment + cross-moment lemmas.
  -- Combine using `covariance_split: λ_k⁻¹ = C_S + C_R`.
  have h_ss := canonicalSmoothFieldFunction_self_moment
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x y
  have h_rr := canonicalRoughFieldFunction_self_moment
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x y
  have h_sr := canonicalSmoothRough_cross_moment_zero
    (d := d) (N := N) (a := a) (mass := mass) T x y
  have h_rs := canonicalRoughSmooth_cross_moment_zero
    (d := d) (N := N) (a := a) (mass := mass) T x y
  -- Step 1: Distribute (φ_S + φ_R)(x) · (φ_S + φ_R)(y) = ss + sr + rs + rr
  -- via the integrand decomposition
  have h_eq : ∀ η : CanonicalJoint d N,
      canonicalSumFieldFunction d N a mass T η x *
        canonicalSumFieldFunction d N a mass T η y =
      canonicalSmoothFieldFunction d N a mass T η x *
        canonicalSmoothFieldFunction d N a mass T η y +
      (canonicalSmoothFieldFunction d N a mass T η x *
        canonicalRoughFieldFunction d N a mass T η y +
      (canonicalRoughFieldFunction d N a mass T η x *
        canonicalSmoothFieldFunction d N a mass T η y +
      canonicalRoughFieldFunction d N a mass T η x *
        canonicalRoughFieldFunction d N a mass T η y)) := by
    intro η
    show (canonicalSmoothFieldFunction d N a mass T η x +
          canonicalRoughFieldFunction d N a mass T η x) *
         (canonicalSmoothFieldFunction d N a mass T η y +
          canonicalRoughFieldFunction d N a mass T η y) = _
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall h_eq)]
  -- Step 2: Integrability of each term via L² (Cauchy-Schwarz).
  -- L² integrability of each field function: it's a finite linear combination
  -- of N(0,1) random variables, hence L² under the joint measure.
  have h_smooth_memLp : ∀ z : FinLatticeSites d N,
      MemLp (fun η : CanonicalJoint d N =>
        canonicalSmoothFieldFunction d N a mass T η z) 2
        (canonicalJointMeasure d N) := by
    intro z
    unfold canonicalSmoothFieldFunction
    refine MemLp.const_mul ?_ _
    refine memLp_finset_sum _ (fun k _ => ?_)
    refine MemLp.const_mul ?_ _
    -- η ↦ η.1 k is L² under canonicalJointMeasure (which is μ.prod μ where each μ_i is gaussianReal 0 1).
    rw [canonicalJointMeasure]
    have h : MemLp (fun η_S : FinLatticeSites d N → ℝ => η_S k) 2
        (Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1)) :=
      MemLp.comp_measurePreserving IsGaussian.memLp_two_id
        (measurePreserving_eval (μ := fun _ : FinLatticeSites d N => gaussianReal 0 1) k)
    exact h.comp_measurePreserving
      (μ := (Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1)).prod
        (Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1)))
      (measurePreserving_fst)
  have h_rough_memLp : ∀ z : FinLatticeSites d N,
      MemLp (fun η : CanonicalJoint d N =>
        canonicalRoughFieldFunction d N a mass T η z) 2
        (canonicalJointMeasure d N) := by
    intro z
    unfold canonicalRoughFieldFunction
    refine MemLp.const_mul ?_ _
    refine memLp_finset_sum _ (fun k _ => ?_)
    refine MemLp.const_mul ?_ _
    rw [canonicalJointMeasure]
    have h : MemLp (fun η_R : FinLatticeSites d N → ℝ => η_R k) 2
        (Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1)) :=
      MemLp.comp_measurePreserving IsGaussian.memLp_two_id
        (measurePreserving_eval (μ := fun _ : FinLatticeSites d N => gaussianReal 0 1) k)
    exact h.comp_measurePreserving
      (μ := (Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1)).prod
        (Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1)))
      (measurePreserving_snd)
  have h_ssM := h_smooth_memLp x
  have h_ssM' := h_smooth_memLp y
  have h_rrM := h_rough_memLp x
  have h_rrM' := h_rough_memLp y
  have h_ss_int : Integrable (fun η : CanonicalJoint d N =>
      canonicalSmoothFieldFunction d N a mass T η x *
        canonicalSmoothFieldFunction d N a mass T η y)
      (canonicalJointMeasure d N) := MemLp.integrable_mul h_ssM h_ssM'
  have h_sr_int : Integrable (fun η : CanonicalJoint d N =>
      canonicalSmoothFieldFunction d N a mass T η x *
        canonicalRoughFieldFunction d N a mass T η y)
      (canonicalJointMeasure d N) := MemLp.integrable_mul h_ssM h_rrM'
  have h_rs_int : Integrable (fun η : CanonicalJoint d N =>
      canonicalRoughFieldFunction d N a mass T η x *
        canonicalSmoothFieldFunction d N a mass T η y)
      (canonicalJointMeasure d N) := MemLp.integrable_mul h_rrM h_ssM'
  have h_rr_int : Integrable (fun η : CanonicalJoint d N =>
      canonicalRoughFieldFunction d N a mass T η x *
        canonicalRoughFieldFunction d N a mass T η y)
      (canonicalJointMeasure d N) := MemLp.integrable_mul h_rrM h_rrM'
  -- Step 3: Apply integral_add to split.
  have e1 := integral_add h_ss_int (h_sr_int.add (h_rs_int.add h_rr_int))
  have e2 := integral_add h_sr_int (h_rs_int.add h_rr_int)
  have e3 := integral_add h_rs_int h_rr_int
  simp only [Pi.add_apply] at e1 e2 e3
  rw [e1, e2, e3]
  -- Step 4: substitute self-moment and cross-moment values.
  rw [h_ss, h_sr, h_rs, h_rr]
  -- Step 5: Combine via covariance_split.
  rw [zero_add, zero_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have h_split := covariance_split d N a mass T
    (Fintype.equivFin (FinLatticeSites d N) k)
  linear_combination
    -((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) *
      ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) y) * h_split

/-- **Bridge lemma:** the matrix-eigenvalue indexing matches the
integer-indexed analytic formula.

The matrix `massMatrixHerm d N a mass` has eigenvalues equal to the
analytic formula `latticeLaplacianEigenvalue d N a m + mass²`. The two
indexings — the matrix's `(Matrix.IsHermitian.eigenvalues)` ordering
indexed by `FinLatticeSites d N` versus the explicit integer-indexed
formula — agree under the canonical `Fintype.equivFin` enumeration.

This is mathematically obvious (both are formulas for eigenvalues of the
same matrix in its diagonal DFT basis), but the formal identity is not
yet stated in `gaussian-field`. Deferring its proof to a follow-up
commit there. -/
private lemma massEigenvalues_eq_latticeEigenvalue
    (a mass : ℝ) (k : FinLatticeSites d N) :
    massEigenvalues d N a mass k =
      latticeEigenvalue d N a mass (Fintype.equivFin (FinLatticeSites d N) k) := by
  sorry

/-- **GJ-covariance form of the variance theorem.**

The covariance under `canonicalJointMeasure` matches the abstract
`GaussianField.covariance (latticeCovarianceGJ ...)` evaluated at the
indicators `δ_x, δ_y`. This is the form directly comparable with
`lattice_cross_moment` (which gives the same expression for
`latticeGaussianMeasure`), and is the input to the pushforward
identity. -/
theorem canonicalSumFieldFunction_covariance_eq_GJ
    (ha : 0 < a) (hmass : 0 < mass) (T : ℝ) (hT : 0 < T)
    (x y : FinLatticeSites d N) :
    let δ_x : FinLatticeField d N := fun z => if z = x then 1 else 0
    let δ_y : FinLatticeField d N := fun z => if z = y then 1 else 0
    ∫ η : CanonicalJoint d N,
      canonicalSumFieldFunction d N a mass T η x *
        canonicalSumFieldFunction d N a mass T η y
      ∂(canonicalJointMeasure d N) =
    GaussianField.covariance (latticeCovarianceGJ d N a mass ha hmass) δ_x δ_y := by
  -- LHS via the proved variance theorem:
  --   (a^d)⁻¹ · Σ_k (latticeEigenvalue (Fintype.equivFin k))⁻¹ · e_k(x) · e_k(y)
  -- RHS via `lattice_covariance_GJ_eq_spectral`:
  --   (a^d)⁻¹ · Σ_k (massEigenvalues k)⁻¹ · ⟨e_k, δ_x⟩ · ⟨e_k, δ_y⟩
  -- Bridge via `massEigenvalues_eq_latticeEigenvalue` and
  -- `⟨e_k, δ_x⟩ = e_k(x)` (indicator collapse).
  -- Strategy: combine the proved `canonicalSumFieldFunction_covariance` with
  -- `lattice_covariance_GJ_eq_spectral` and the indicator identity
  -- `⟨e_k, δ_x⟩ = e_k(x)`. The eigenvalue indexing bridge
  -- `massEigenvalues_eq_latticeEigenvalue` is in place above. The remaining
  -- obstruction is a `Pi.instFintype` instance-resolution mismatch between
  -- the bracket-introduced `[Fintype (ZMod N)]` (used by the variance
  -- theorem after the section variable was added) and the global
  -- `ZMod.fintype N` (used by `lattice_covariance_GJ_eq_spectral` from
  -- gaussian-field). The two instances are subsingleton-equal but the
  -- finals haven't found a clean Lean-level cast for the resulting double
  -- sums — deferred to a follow-up that reformulates the gaussian-field
  -- spectral lemma to take an explicit `[Fintype (ZMod N)]` bracket.
  sorry

end Variance

end Canonical

end Pphi2
