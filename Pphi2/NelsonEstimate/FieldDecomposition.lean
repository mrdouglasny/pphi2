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

/-- The canonical doubled-Gaussian phase space:
`(FinLatticeSites d N → ℝ) × (FinLatticeSites d N → ℝ)`. The first
component holds the smooth-side coordinates `η_S`, the second the
rough-side `η_R`. -/
abbrev CanonicalJoint (d N : ℕ) [NeZero N] : Type :=
  (FinLatticeSites d N → ℝ) × (FinLatticeSites d N → ℝ)

/-- The canonical joint measure: product of two i.i.d. standard
Gaussian product-measures, one on each component. -/
noncomputable def canonicalJointMeasure (d N : ℕ) [NeZero N] :
    haveI : Fintype (ZMod N) := ZMod.fintype N
    Measure (CanonicalJoint d N) :=
  haveI : Fintype (ZMod N) := ZMod.fintype N
  Measure.prod
    (Measure.pi (fun _ : FinLatticeSites d N => ProbabilityTheory.gaussianReal 0 1))
    (Measure.pi (fun _ : FinLatticeSites d N => ProbabilityTheory.gaussianReal 0 1))

/-- The canonical smooth-side **field function** at cutoff `T`. Maps
each `(η_S, η_R) ∈ CanonicalJoint d N` to a function on lattice sites:
`x ↦ Σ_k √(C_S(T, k')) · e_k(x) · η_S(k)`,
where `C_S(T, k')` is the smooth covariance eigenvalue at the integer
mode index `k'` corresponding to the lattice site index `k` via
`Fintype.equivFin (FinLatticeSites d N)`.

This is a **field**, not a configuration: the `Configuration` type
is `WeakDual` (continuous linear functionals), and lifting this field
to a Configuration requires bundling it with the standard pairing
`⟨g, f⟩ := Σ_x g(x) · f(x)` and showing continuity. The lift is
deferred to a separate lemma. -/
noncomputable def canonicalSmoothFieldFunction (d N : ℕ) [NeZero N]
    (a mass T : ℝ) (η : CanonicalJoint d N) :
    FinLatticeSites d N → ℝ :=
  fun x =>
    ∑ k : FinLatticeSites d N,
      Real.sqrt (smoothCovEigenvalue d N a mass T
        (Fintype.equivFin (FinLatticeSites d N) k)) *
      ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) *
      η.1 k

/-- The canonical rough-side field function at cutoff `T`. -/
noncomputable def canonicalRoughFieldFunction (d N : ℕ) [NeZero N]
    (a mass T : ℝ) (η : CanonicalJoint d N) :
    FinLatticeSites d N → ℝ :=
  fun x =>
    ∑ k : FinLatticeSites d N,
      Real.sqrt (roughCovEigenvalue d N a mass T
        (Fintype.equivFin (FinLatticeSites d N) k)) *
      ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) *
      η.2 k

/-- The canonical sum field: `φ(x) = φ_S(x) + φ_R(x)`. As a field
function (`FinLatticeSites d N → ℝ`), the sum is pointwise. -/
noncomputable def canonicalSumFieldFunction (d N : ℕ) [NeZero N]
    (a mass T : ℝ) (η : CanonicalJoint d N) :
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

/-! ### Measurability of the canonical field functions -/

/-- The smooth field function evaluated at a fixed site `x` is
measurable in `η`. It's a finite sum of `c_k · η.1(k)` over the
modes `k`, each of which is a continuous (hence measurable) linear
combination of the joint variables. -/
theorem canonicalSmoothFieldFunction_pointwise_measurable
    (d N : ℕ) [NeZero N] (a mass T : ℝ) (x : FinLatticeSites d N) :
    haveI : Fintype (ZMod N) := ZMod.fintype N
    haveI : Fintype (FinLatticeSites d N) := Pi.instFintype
    Measurable (fun η : CanonicalJoint d N =>
      canonicalSmoothFieldFunction d N a mass T η x) := by
  haveI : Fintype (ZMod N) := ZMod.fintype N
  unfold canonicalSmoothFieldFunction
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
    haveI : Fintype (ZMod N) := ZMod.fintype N
    haveI : Fintype (FinLatticeSites d N) := Pi.instFintype
    Measurable (fun η : CanonicalJoint d N =>
      canonicalRoughFieldFunction d N a mass T η x) := by
  haveI : Fintype (ZMod N) := ZMod.fintype N
  unfold canonicalRoughFieldFunction
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

end Canonical

end Pphi2
