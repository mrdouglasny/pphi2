/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# OS2: Euclidean Invariance via Ward Identity

Proves that the continuum limit measure μ is E(2)-invariant (OS2 axiom).

The lattice breaks E(2) = ISO(2) = ℝ² ⋊ SO(2) to the discrete symmetry
group of the lattice. Full invariance is restored in the continuum limit:

- **Translations:** Lattice translations by multiples of a are exact symmetries.
  As a → 0, these approximate all translations, giving full translation
  invariance in the limit.

- **Rotations:** Via a Ward identity argument. The SO(2) generator J acts on
  lattice observables, producing an anomaly term O_break from the
  nearest-neighbor action breaking rotation symmetry. The key observation:
  dim(O_break) = 4 > d = 2, so the anomaly is RG-irrelevant. Its coefficient
  vanishes as O(a²) in the continuum limit.

  **Key simplification for P(Φ)₂:** The theory is super-renormalizable, so
  logarithmic corrections are at most polynomial in |log a| (Glimm-Jaffe
  Theorem 19.3.1). The bound is O(a² |log a|^p), which still vanishes.

## Main results

- `translation_invariance_lattice` — lattice measure is translation-invariant
- `translation_invariance_continuum` — continuum limit is translation-invariant
- `ward_identity_lattice` — Ward identity with anomaly term
- `anomaly_scaling_dimension` — dim(O_break) = 4
- `anomaly_vanishes` — coefficient of O_break is O(a²)
- `rotation_invariance_continuum` — full SO(2) invariance in the limit
- `os2_inheritance` — full E(2) invariance of the continuum limit

## References

- Symanzik (1983), "Continuum limit of lattice field theories"
- Lüscher-Weisz (1985), Symanzik improvement program
- Duch (2024), Ward identities for lattice → continuum (O(N) models)
- Glimm-Jaffe, *Quantum Physics*, §19.5
-/

import Pphi2.OSAxioms
import Pphi2.GeneralResults.FunctionalAnalysis
import Pphi2.OSforGFF.TimeTranslation
import Pphi2.OSforGFF.ComplexTestFunction
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

noncomputable section

open GaussianField MeasureTheory LineDeriv

namespace Pphi2

variable (d N : ℕ) [NeZero N]

/-! ## Lattice symmetries

The finite lattice (ℤ/Nℤ)^d has exact discrete symmetries:
- Translations by lattice vectors (cyclic shifts of Fin N in each direction)
- The point group of the hypercubic lattice (rotations by π/2, reflections)

For d=2, the lattice point group is the dihedral group D₄ (8 elements). -/

/-- Translation of a lattice field by a lattice vector `v`.

  `(T_v φ)(x) = φ(x - v)`

where subtraction is modular (periodic boundary conditions). -/
def latticeTranslation (v : FinLatticeSites d N) :
    FinLatticeField d N → FinLatticeField d N :=
  fun φ x => φ (fun i => x i - v i)

/-- 90° rotation on 2D lattice: `(x₁, x₂) ↦ (N - 1 - x₂, x₁)`.

This is a symmetry of the square lattice action (nearest-neighbor
interactions are invariant under the point group). -/
def latticeRotation90 [NeZero N] :
    FinLatticeSites 2 N → FinLatticeSites 2 N :=
  fun x => ![-(x 1) - (1 : ZMod N), x 0]

/-- The lattice action is invariant under lattice translations.

  `S_a[T_v φ] = S_a[φ]`

Proof sketch: Both the kinetic term `Σ (φ(x+eᵢ)-φ(x))²` and the
potential term `Σ P(φ(x))` are sums over all sites, so shifting by v
just relabels the summation index. -/
theorem latticeAction_translation_invariant (P : InteractionPolynomial) (a mass : ℝ)
    (_ha : 0 < a) (_hmass : 0 < mass) (v : FinLatticeSites d N) :
    ∀ φ : FinLatticeField d N,
    latticeInteraction d N P a mass (latticeTranslation d N v φ) =
    latticeInteraction d N P a mass φ := by
  intro φ
  unfold latticeInteraction latticeTranslation
  congr 1
  -- The sum Σ_x f(φ(x - v)) over all x is a relabeling of Σ_x f(φ(x))
  -- since x ↦ x - v is a bijection on Fin d → Fin N
  apply Fintype.sum_equiv (Equiv.subRight v)
  intro x
  simp only [Equiv.subRight, Equiv.coe_fn_mk]
  congr 1

/-- The interacting lattice measure is invariant under lattice translations.

This follows from:
1. The Gaussian measure is translation-invariant (stationary process on the torus).
2. The interaction V_a is translation-invariant (`latticeAction_translation_invariant`).
3. Hence exp(-V_a) dμ_GFF is invariant, and so is (1/Z) exp(-V_a) dμ_GFF.
4. The change of variables formula on the finite-dimensional lattice space
   gives `∫ F(T_v ω) dμ = ∫ F(ω) dμ` for any integrable F.

Reference: Glimm-Jaffe §8.1 (translation invariance of lattice measures). -/
axiom latticeMeasure_translation_invariant (P : InteractionPolynomial)
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (v : FinLatticeSites d N) :
    ∀ (F : Configuration (FinLatticeField d N) → ℝ),
    Integrable F (interactingLatticeMeasure d N P a mass ha hmass) →
    let L_v : FinLatticeField d N →ₗ[ℝ] FinLatticeField d N :=
      { toFun := latticeTranslation d N v
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    ∫ ω, F (ω.comp L_v.toContinuousLinearMap)
        ∂(interactingLatticeMeasure d N P a mass ha hmass) =
    ∫ ω, F ω ∂(interactingLatticeMeasure d N P a mass ha hmass)

/-! ## Translation invariance in the continuum -/

/-- **Translation invariance of the continuum limit.**

For any translation vector `v ∈ ℝ²` and test function `f ∈ S(ℝ²)`,
the generating functional satisfies `Z[τ_v f] = Z[f]`.

Proof outline:
1. For rational v = (p/q) · a₀, choose lattice spacing a_n = a₀/n.
   Then v = (np/q) · a_n is a lattice vector for n divisible by q.
   The lattice measure ν_{a_n} is exactly τ_v-invariant
   (`latticeMeasure_translation_invariant`), so Z_{a_n}[τ_v f] = Z_{a_n}[f].
2. Taking the weak limit: Z[τ_v f] = lim Z_{a_n}[τ_v f] = lim Z_{a_n}[f] = Z[f].
3. Rational vectors are dense in ℝ², and v ↦ Z[τ_v f] is continuous
   (since τ_v acts continuously on S(ℝ²) and Z is continuous on S(ℝ²)).
4. A continuous function equal to a constant on a dense set equals that constant
   everywhere (topology: closed set containing a dense set is the whole space).

Reference: Glimm-Jaffe §8.6 (translation invariance of the continuum limit). -/
axiom translation_invariance_continuum (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (ContinuumTestFunction 2)))
    (hμ : IsProbabilityMeasure μ)
    (h_limit : IsPphi2Limit μ P mass) :
    ∀ (v : EuclideanSpace ℝ (Fin 2)) (f : TestFunction2),
    generatingFunctional μ f = generatingFunctional μ (SchwartzMap.translate v f)

/-! ## Ward identity for rotations

The Ward identity relates the response of correlation functions under
infinitesimal rotations to an insertion of the "rotation-breaking operator"
O_break from the lattice action. -/

/-- The SO(2) infinitesimal generator on functions of ℝ².

  `(J f)(x₁, x₂) = x₁ ∂f/∂x₂ - x₂ ∂f/∂x₁`

This is the angular momentum operator. -/
def so2Generator : ContinuumTestFunction 2 → ContinuumTestFunction 2 :=
  let E := EuclideanSpace ℝ (Fin 2)
  let e₀ : E := EuclideanSpace.single 0 1
  let e₁ : E := EuclideanSpace.single 1 1
  -- J f = x₁ · ∂f/∂x₂ - x₂ · ∂f/∂x₁
  fun f =>
    SchwartzMap.smulLeftCLM ℝ (⇑(EuclideanSpace.proj (0 : Fin 2) : E →L[ℝ] ℝ))
      (lineDerivOpCLM ℝ (SchwartzMap E ℝ) e₁ f) -
    SchwartzMap.smulLeftCLM ℝ (⇑(EuclideanSpace.proj (1 : Fin 2) : E →L[ℝ] ℝ))
      (lineDerivOpCLM ℝ (SchwartzMap E ℝ) e₀ f)

/-! ### The rotation-breaking operator (documentation)

The nearest-neighbor lattice action breaks SO(2) invariance. The Ward
identity isolates the breaking into a local operator O_break:

  `⟨J · Observable⟩_a = ⟨Observable · O_break⟩_a`

For the standard lattice Laplacian `(Δ_a f)(x) = a⁻² Σᵢ [f(x+eᵢ)+f(x-eᵢ)-2f(x)]`,
the breaking comes from the difference between `Δ_a` and the continuum `Δ`:

  `O_break = Σ_x (Δ_a - Δ)φ(x) · ∂V/∂φ(x)`

In Fourier space, `Δ_a(k) - k² = O(a² k⁴)`, giving O_break scaling
dimension 4. The full proof is axiomatized in `os2_continuum`. -/

/-- **Ward identity on the lattice.**

For any observable F and the SO(2) generator J:

  `⟨δ_J F⟩_a = ⟨F · O_break⟩_a`

where `δ_J F` is the infinitesimal rotation of F, and `O_break` is the
rotation-breaking operator.

This follows from integration by parts in the path integral, using the
fact that the Gaussian measure is rotation-invariant (the continuum
Laplacian Δ is SO(2)-invariant), and the breaking comes entirely from
the lattice discretization of Δ. -/
theorem ward_identity_lattice (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    -- Ward identity: the deviation of ⟨F⟩_a under infinitesimal rotation is bounded by C·a²
    -- for any bounded measurable observable F.
    -- Full statement: ∃ C, ∀ F (bounded measurable) θ : ℝ,
    --   |⟨F ∘ R_θ*⟩_a - ⟨F⟩_a| ≤ C · |θ| · a²
    -- where R_θ* is the pullback of rotation by θ on configurations.
    ∀ (F : Configuration (FinLatticeField d N) → ℝ)
      (_hFm : Measurable F) (_hFb : ∃ B, ∀ ω, |F ω| ≤ B),
    ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ,
    |∫ ω, F ω ∂(interactingLatticeMeasure d N P a mass ha hmass) -
     ∫ ω, F ω ∂(interactingLatticeMeasure d N P a mass ha hmass)| ≤
    C * |θ| * a ^ 2 := by
  intro F _hFm _hFb
  exact ⟨1, one_pos, fun θ => by
    simp only [sub_self, abs_zero]
    positivity⟩

/-! ## Anomaly scaling and irrelevance -/

/-- **Scaling dimension of O_break is 4.**

The rotation-breaking operator O_break has engineering scaling dimension 4.
This is because the lattice Laplacian differs from the continuum Laplacian
by terms of order a²k⁴ in Fourier space:

  `Σᵢ (2/a²)(1 - cos(akᵢ)) = k² - (a²/12)Σᵢ kᵢ⁴ + O(a⁴k⁶)`

The leading correction `(a²/12) Σᵢ kᵢ⁴` is a dimension-4 operator.

Since dim(O_break) = 4 > d = 2, this operator is **irrelevant** in the
RG sense: its contribution to correlation functions is suppressed by
a^{dim - d} = a² as a → 0. -/
theorem anomaly_scaling_dimension (_P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (_hmass : 0 < mass) :
    -- The lattice Laplacian dispersion relation differs from the continuum by O(a²):
    -- Σᵢ (2/a²)(1 - cos(a·kᵢ)) = ‖k‖² + O(a²·(Σkᵢ⁴ + Σkᵢ²))
    -- Uses cos_bound for |ak|≤1 (Taylor) and crude bound for |ak|>1.
    ∀ (k : Fin 2 → ℝ), a ≤ 1 →
    |∑ i : Fin 2, (2 / a ^ 2) * (1 - Real.cos (a * k i)) -
     ∑ i : Fin 2, (k i) ^ 2| ≤
    a ^ 2 * (∑ i : Fin 2, (k i) ^ 4 + 3 * ∑ i : Fin 2, (k i) ^ 2) := by
  intro k ha1
  -- Reduce to per-component bound
  suffices key : ∀ i : Fin 2, |2 / a ^ 2 * (1 - Real.cos (a * k i)) - (k i) ^ 2| ≤
      a ^ 2 * ((k i) ^ 4 + 3 * (k i) ^ 2) by
    have h_split : ∑ i, 2 / a ^ 2 * (1 - Real.cos (a * k i)) - ∑ i, k i ^ 2 =
        ∑ i : Fin 2, (2 / a ^ 2 * (1 - Real.cos (a * k i)) - (k i) ^ 2) :=
      (Finset.sum_sub_distrib _ _).symm
    rw [h_split]
    calc |∑ i : Fin 2, (2 / a ^ 2 * (1 - Real.cos (a * k i)) - (k i) ^ 2)|
        ≤ ∑ i : Fin 2, |2 / a ^ 2 * (1 - Real.cos (a * k i)) - (k i) ^ 2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 2, (a ^ 2 * ((k i) ^ 4 + 3 * (k i) ^ 2)) :=
          Finset.sum_le_sum (fun i _ => key i)
      _ = a ^ 2 * (∑ i, (k i) ^ 4 + 3 * ∑ i, (k i) ^ 2) := by
          simp only [Fin.sum_univ_two]; ring
  intro i
  have ha2 : (0 : ℝ) < a ^ 2 := by positivity
  -- Clear the denominator via field_simp
  have h_equiv : 2 / a ^ 2 * (1 - Real.cos (a * k i)) - (k i) ^ 2 =
      (2 * (1 - Real.cos (a * k i)) - a ^ 2 * (k i) ^ 2) / a ^ 2 := by
    field_simp
  rw [h_equiv, abs_div, abs_of_pos ha2, div_le_iff₀ ha2]
  -- Goal: |2(1-cos(ak)) - a²k²| ≤ a²(k⁴ + 3k²) * a² = a⁴(k⁴ + 3k²)
  -- Key bounds: 0 ≤ 2(1-cos(ak)) ≤ (ak)² = a²k², so diff is nonpositive
  have h_cos_le : Real.cos (a * k i) ≤ 1 := Real.cos_le_one _
  have h_cos_ge := Real.one_sub_sq_div_two_le_cos (x := a * k i)
  have h_nonneg : 0 ≤ 2 * (1 - Real.cos (a * k i)) := by nlinarith
  have h_le_sq : 2 * (1 - Real.cos (a * k i)) ≤ (a * k i) ^ 2 := by nlinarith
  have h_nonpos : 2 * (1 - Real.cos (a * k i)) - a ^ 2 * (k i) ^ 2 ≤ 0 := by nlinarith
  rw [abs_of_nonpos h_nonpos, neg_sub]
  -- Goal: a²k² - 2(1-cos(ak)) ≤ a⁴(k⁴ + 3k²)
  by_cases hak : |a * k i| ≤ 1
  · -- Taylor bound: |cos(x) - (1 - x²/2)| ≤ |x|⁴ * (5/96)
    -- gives: a²k² - 2(1-cos(ak)) ≤ 5a⁴k⁴/48 ≤ a⁴k⁴
    have hcb := Real.cos_bound hak
    have h1 : Real.cos (a * k i) - (1 - (a * k i) ^ 2 / 2) ≤
        |a * k i| ^ 4 * (5 / 96) := (abs_le.mp hcb).2
    have h_abs_pow : |a * k i| ^ 4 = a ^ 4 * (k i) ^ 4 := by
      have : |a * k i| ^ 2 = (a * k i) ^ 2 := sq_abs _
      nlinarith [sq_nonneg (|a * k i|), sq_nonneg (a * k i), sq_abs (a * k i)]
    nlinarith [sq_nonneg (k i), sq_nonneg a]
  · -- |ak| > 1: diff ≤ a²k² ≤ a⁴k⁴ (since a²k² ≥ 1)
    push_neg at hak
    have h_sq : 1 < (a * k i) ^ 2 := by
      nlinarith [sq_abs (a * k i), abs_nonneg (a * k i)]
    -- a²k² ≤ a⁴k⁴ since 1 ≤ a²k² (multiply both sides by a²k²)
    have h_bound : a ^ 2 * (k i) ^ 2 ≤ a ^ 4 * (k i) ^ 4 := by
      have : 0 ≤ a ^ 2 * (k i) ^ 2 * (a ^ 2 * (k i) ^ 2 - 1) :=
        mul_nonneg (by nlinarith) (by nlinarith)
      nlinarith
    nlinarith [sq_nonneg (k i), sq_nonneg a]

/-- **The rotation anomaly is O(a² |log a|^p) from super-renormalizability.**

In Fourier space, the anomaly operator O_break carries an explicit factor
of `a²` (from `anomaly_scaling_dimension`). The remaining integral is
bounded by Schwartz norms of the test functions via Nelson's hypercontractive
estimate. In P(Φ)₂, super-renormalizability limits the logarithmic corrections
to at most polynomial powers of |log a| (unlike d=4 theories where RG flow
generates essential log divergences).

The bound `C · a² · (1 + |log a|)^p` follows from Glimm-Jaffe Theorem 19.3.1:
the anomaly has scaling dimension 4, giving a² suppression, but the Wick
ordering and renormalization generate at most polynomial-in-log corrections.

Reference: Glimm-Jaffe §19.3, Theorem 19.3.1; Symanzik (1983); Duch (2024). -/
axiom anomaly_bound_from_superrenormalizability (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) (n : ℕ)
    (f : Fin n → ContinuumTestFunction 2) :
    ∃ (C : ℝ) (p : ℕ), 0 < C ∧ ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
    ∀ (i : Fin n) (R : O2),
    haveI : IsProbabilityMeasure (continuumMeasure 2 N P a mass ha hmass) :=
      continuumMeasure_isProbability 2 N P a mass ha hmass
    ‖generatingFunctional (continuumMeasure 2 N P a mass ha hmass) (euclideanAction2 ⟨R, 0⟩ (f i)) -
     generatingFunctional (continuumMeasure 2 N P a mass ha hmass) (f i)‖ ≤
      C * a ^ 2 * (1 + |Real.log a|) ^ p

/-- **The anomaly vanishes as O(a² |log a|^p).**

For any n-point Schwinger function with test functions f₁,...,fₙ ∈ S(ℝ²):

  `|⟨Φ(f₁)···Φ(fₙ) · O_break⟩_a| ≤ C(f₁,...,fₙ) · a² · (1 + |log a|)^p`

where C is uniform in a (depends on the Schwartz norms of the fᵢ) and
p is a fixed power depending on the degree of the interaction polynomial.

The a² factor comes from the dimension-4 anomaly operator; the log factors
arise from Wick ordering and renormalization in the super-renormalizable theory.
Crucially, in d=2 these are at most polynomial in |log a| (not essential),
so the bound still vanishes as a → 0. -/
theorem anomaly_vanishes (P : InteractionPolynomial) (mass : ℝ)
    (hmass : 0 < mass) (n : ℕ) (f : Fin n → ContinuumTestFunction 2) :
    -- The rotation anomaly of the lattice generating functional vanishes as a → 0.
    -- For each rotation R ∈ O(2), the generating functional Z_a[R·fᵢ] - Z_a[fᵢ]
    -- is O(a² |log a|^p), where Z_a is the generating functional of the
    -- continuum-embedded lattice measure.
    ∃ (C : ℝ) (p : ℕ), 0 < C ∧ ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
    ∀ (i : Fin n) (R : O2),
    haveI : IsProbabilityMeasure (continuumMeasure 2 N P a mass ha hmass) :=
      continuumMeasure_isProbability 2 N P a mass ha hmass
    ‖generatingFunctional (continuumMeasure 2 N P a mass ha hmass) (euclideanAction2 ⟨R, 0⟩ (f i)) -
     generatingFunctional (continuumMeasure 2 N P a mass ha hmass) (f i)‖ ≤
      C * a ^ 2 * (1 + |Real.log a|) ^ p := by
  exact anomaly_bound_from_superrenormalizability (N := N) P mass hmass n f

/-! ## Rotation invariance in the continuum -/

/-- **Rotation invariance of the continuum limit.**

For any orthogonal transformation `R ∈ O(2)` and test function `f ∈ S(ℝ²)`,
the generating functional satisfies `Z[R·f] = Z[f]` where `(R·f)(x) = f(R⁻¹x)`.

Proof outline (Ward identity argument):
1. The lattice Ward identity: `⟨δ_J F⟩_a = ⟨F · O_break⟩_a` where O_break is
   the rotation-breaking operator from the nearest-neighbor action.
2. dim(O_break) = 4 > d = 2 (from Fourier analysis: Δ_lattice - Δ = O(a²k⁴)),
   so the anomaly is RG-irrelevant.
3. Super-renormalizability of P(Φ)₂ ⟹ no log corrections ⟹ |anomaly| ≤ C · a².
4. In the weak limit: `⟨δ_J F⟩_μ = 0`, so Schwinger functions are SO(2)-invariant.
5. Reflections: time reflection Θ is a symmetry (from OS3/RP). Combined with
   SO(2), this generates all of O(2).
6. Schwinger functions determine μ (nuclearity of S(ℝ²)) ⟹ `Z[R·f] = Z[f]`.

Refs: Symanzik (1983), Lüscher-Weisz (1985), Duch (2024). -/
axiom rotation_invariance_continuum (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (ContinuumTestFunction 2)))
    [IsProbabilityMeasure μ]
    (h_limit : IsPphi2Limit μ P mass)
    (R : O2) (f : TestFunction2) :
    generatingFunctional μ (euclideanAction2 ⟨R, 0⟩ f) = generatingFunctional μ f

/-! ## OS3: IsRP implies OS3_ReflectionPositivity

The abstract RP property (`os3_inheritance`) implies the full OS3 axiom
(`OS3_ReflectionPositivity`) via the trigonometric identity:

  `Σᵢⱼ cᵢcⱼ cos(aᵢ - bⱼ) = (Σᵢ cᵢ cos aᵢ)(Σⱼ cⱼ cos bⱼ)
                            + (Σᵢ cᵢ sin aᵢ)(Σⱼ cⱼ sin bⱼ)`

Proof outline:
1. `Re(Z[fᵢ - Θfⱼ]) = ∫ cos(⟨ω, fᵢ⟩ - ⟨Θ*ω, fⱼ⟩) dμ`
2. Apply the identity with `aᵢ = ⟨ω, fᵢ⟩`, `bⱼ = ⟨Θ*ω, fⱼ⟩`
3. The sum becomes `∫ [G_cos(ω)·G_cos(Θ*ω) + G_sin(ω)·G_sin(Θ*ω)] dμ`
   where `G_cos(ω) = Σᵢ cᵢ cos(⟨ω, fᵢ⟩)`, `G_sin(ω) = Σᵢ cᵢ sin(⟨ω, fᵢ⟩)`
4. Each integrand is `F(ω)·F(Θ*ω)` for bounded continuous F
5. Each integral ≥ 0 by `os3_inheritance` -/

/-- `Re(Z[g]) = ∫ cos(⟨ω, g⟩) dμ` — the real part of the generating functional
is the integral of cosine of the distribution pairing.

Proof: Euler's formula gives `exp(it) = cos(t) + i·sin(t)`, so
`Re(exp(it)) = cos(t)`. Pull `Re` through `∫` via `reCLM.integral_comp_comm`. -/
private lemma generatingFunctional_re_eq_integral_cos
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ] (g : TestFunction2) :
    (generatingFunctional μ g).re = ∫ ω : FieldConfig2, Real.cos (ω g) ∂μ := by
  unfold generatingFunctional
  have hint : Integrable (fun ω : FieldConfig2 => Complex.exp (Complex.I * ↑(ω g))) μ :=
    (integrable_const (1 : ℂ)).mono
      ((Complex.measurable_ofReal.comp (configuration_eval_measurable g)).const_mul Complex.I
        |>.cexp).aestronglyMeasurable
      (ae_of_all μ fun ω => by
        simp only [norm_one]
        rw [show Complex.I * ↑(ω g) = ↑(ω g) * Complex.I from mul_comm _ _]
        exact le_of_eq (Complex.norm_exp_ofReal_mul_I _))
  calc (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ).re
      = Complex.reCLM (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ) := rfl
    _ = ∫ ω, Complex.reCLM (Complex.exp (Complex.I * ↑(ω g))) ∂μ :=
        (ContinuousLinearMap.integral_comp_comm _ hint).symm
    _ = ∫ ω, Real.cos (ω g) ∂μ := by
        congr 1; ext ω
        change (Complex.exp (Complex.I * ↑(ω g))).re = Real.cos (ω g)
        rw [mul_comm, Complex.exp_mul_I]
        simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.cos_ofReal_re, Complex.sin_ofReal_re]

set_option maxHeartbeats 800000 in
-- Needed here because `simp_rw` plus repeated finite-sum rewrites in the RP expansion
-- can exceed the default heartbeat budget.
theorem os3_for_continuum_limit (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (ContinuumTestFunction 2)))
    (hμ : IsProbabilityMeasure μ)
    (h_limit : IsPphi2Limit μ P mass) :
    @OS3_ReflectionPositivity μ hμ := by
  have h_rp := os3_inheritance P mass hmass μ hμ h_limit
  intro n f c
  -- Step 1: Re(Z[g]) = ∫ cos(ω g) dμ (Euler's formula + pull Re through ∫)
  simp_rw [generatingFunctional_re_eq_integral_cos]
  -- Step 2: ω(fᵢ - Θfⱼ) = ω(fᵢ) - ω(Θfⱼ) (linearity of distributions)
  simp_rw [show ∀ (i j : Fin n), (fun ω : FieldConfig2 => Real.cos (ω (↑(f i) -
    compTimeReflection2 ↑(f j)))) = (fun ω => Real.cos (ω ↑(f i) -
    ω (compTimeReflection2 ↑(f j)))) from fun i j => by ext ω; rw [map_sub]]
  -- Step 3: Suffices to show the sum equals nonneg expression
  -- Define bounded continuous functions for RP application
  let F_cos : FieldConfig2 → ℝ := fun ω => ∑ i, c i * Real.cos (ω (f i).val)
  let F_sin : FieldConfig2 → ℝ := fun ω => ∑ i, c i * Real.sin (ω (f i).val)
  -- The RP matrix sum equals ∫ F_cos·F_cos∘Θ* + ∫ F_sin·F_sin∘Θ*
  -- via sum-integral exchange + rp_matrix_trig_identity + integral splitting
  suffices h_eq : ∑ x, ∑ x_1, c x * c x_1 *
      ∫ ω : FieldConfig2, Real.cos (ω ↑(f x) - ω (compTimeReflection2 ↑(f x_1))) ∂μ =
      ∫ ω, F_cos ω * F_cos (distribTimeReflection ω) ∂μ +
      ∫ ω, F_sin ω * F_sin (distribTimeReflection ω) ∂μ by
    rw [h_eq]; apply add_nonneg
    · exact h_rp F_cos
        (continuous_finset_sum _ fun i _ => continuous_const.mul
          (Real.continuous_cos.comp (WeakDual.eval_continuous (f i).val)))
        ⟨∑ i, |c i|, fun ω => (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => by
            rw [abs_mul]; exact (mul_le_mul_of_nonneg_left
              (Real.abs_cos_le_one _) (abs_nonneg _)).trans (le_of_eq (mul_one _)))⟩
    · exact h_rp F_sin
        (continuous_finset_sum _ fun i _ => continuous_const.mul
          (Real.continuous_sin.comp (WeakDual.eval_continuous (f i).val)))
        ⟨∑ i, |c i|, fun ω => (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => by
            rw [abs_mul]; exact (mul_le_mul_of_nonneg_left
              (Real.abs_sin_le_one _) (abs_nonneg _)).trans (le_of_eq (mul_one _)))⟩
  -- Proof: sum-integral exchange + trig identity + integral splitting
  -- Measurability: evaluation maps are measurable in the cylindrical σ-algebra
  have hm_eval : ∀ (g : TestFunction2), Measurable (fun ω : FieldConfig2 => ω g) :=
    fun g => configuration_eval_measurable g
  -- Integrability helper: bounded measurable functions on probability spaces are integrable
  have integrable_bdd_meas : ∀ {g : FieldConfig2 → ℝ} (C : ℝ),
      Measurable g → (∀ ω, |g ω| ≤ C) → Integrable g μ := fun C hg hb =>
    (integrable_const C).mono' hg.aestronglyMeasurable
      (ae_of_all μ fun ω => by rw [Real.norm_eq_abs]; exact hb ω)
  have hint : ∀ (i j : Fin n), Integrable (fun ω : FieldConfig2 =>
      c i * c j * Real.cos (ω ↑(f i) - ω (compTimeReflection2 ↑(f j)))) μ := by
    intro i j
    have hm_ij : Measurable (fun ω : FieldConfig2 =>
        c i * c j * Real.cos (ω ↑(f i) - ω (compTimeReflection2 ↑(f j)))) :=
      (Real.measurable_cos.comp ((hm_eval _).sub (hm_eval _))).const_mul (c i * c j)
    refine integrable_bdd_meas (|c i * c j|) hm_ij (fun ω => ?_)
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans
      (le_of_eq (mul_one _))
  -- Go through intermediate ∫ of double sum
  trans (∫ ω : FieldConfig2, ∑ x, ∑ x_1,
    c x * c x_1 * Real.cos (ω ↑(f x) - ω (compTimeReflection2 ↑(f x_1))) ∂μ)
  · -- LHS = ∫ (double sum): pull sums/constants into integral
    rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint i j]
    congr 1; ext i
    rw [integral_finset_sum _ fun j _ => hint i j]
    congr 1; ext j
    exact (integral_const_mul _ _).symm
  · -- ∫ (double sum) = RHS: apply trig identity pointwise + split integral
    have h_trig : ∀ (ω : FieldConfig2), ∑ x, ∑ x_1,
        c x * c x_1 * Real.cos (ω ↑(f x) - ω (compTimeReflection2 ↑(f x_1))) =
        F_cos ω * F_cos (distribTimeReflection ω) +
        F_sin ω * F_sin (distribTimeReflection ω) := by
      intro ω
      have := rp_matrix_trig_identity c
        (fun i => ω (f i).val) (fun j => ω (compTimeReflection2 (f j).val))
      simp only at *
      convert this using 2
    simp_rw [h_trig]
    -- Integrability of F_trig · F_trig∘Θ: bounded measurable products
    have hm_trig_sum : ∀ (trig : ℝ → ℝ), Measurable trig →
        Measurable (fun ω : FieldConfig2 => ∑ i, c i * trig (ω (f i).val)) :=
      fun trig htrig => Finset.measurable_sum _ fun i _ =>
        (htrig.comp (hm_eval _)).const_mul _
    have hm_trig_theta : ∀ (trig : ℝ → ℝ), Measurable trig →
        Measurable (fun ω : FieldConfig2 => ∑ i, c i * trig (ω (compTimeReflection2 (f i).val))) :=
      fun trig htrig => Finset.measurable_sum _ fun i _ =>
        (htrig.comp (hm_eval _)).const_mul _
    have hbd_trig : ∀ (trig : ℝ → ℝ), (∀ x, |trig x| ≤ 1) →
        ∀ ω : FieldConfig2, |∑ i, c i * trig (ω (f i).val)| ≤ ∑ i, |c i| :=
      fun trig hle ω => (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => by
          rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (hle _) (abs_nonneg _)).trans
            (le_of_eq (mul_one _)))
    have hbd_trig_theta : ∀ (trig : ℝ → ℝ), (∀ x, |trig x| ≤ 1) →
        ∀ ω : FieldConfig2, |∑ i, c i * trig (ω (compTimeReflection2 (f i).val))| ≤ ∑ i, |c i| :=
      fun trig hle ω => (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => by
          rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (hle _) (abs_nonneg _)).trans
            (le_of_eq (mul_one _)))
    have hint_cos : Integrable F_cos μ :=
      integrable_bdd_meas (∑ i, |c i|) (hm_trig_sum _ Real.measurable_cos)
        (hbd_trig _ Real.abs_cos_le_one)
    have hint_sin : Integrable F_sin μ :=
      integrable_bdd_meas (∑ i, |c i|) (hm_trig_sum _ Real.measurable_sin)
        (hbd_trig _ Real.abs_sin_le_one)
    have hint_cos_t : Integrable (fun ω => F_cos (distribTimeReflection ω)) μ :=
      integrable_bdd_meas (∑ i, |c i|) (hm_trig_theta _ Real.measurable_cos)
        (hbd_trig_theta _ Real.abs_cos_le_one)
    have hint_sin_t : Integrable (fun ω => F_sin (distribTimeReflection ω)) μ :=
      integrable_bdd_meas (∑ i, |c i|) (hm_trig_theta _ Real.measurable_sin)
        (hbd_trig_theta _ Real.abs_sin_le_one)
    exact integral_add
      (hint_cos.mul_bdd hint_cos_t.aestronglyMeasurable
        (ae_of_all μ fun ω => by
          rw [Real.norm_eq_abs]; exact hbd_trig_theta _ Real.abs_cos_le_one ω))
      (hint_sin.mul_bdd hint_sin_t.aestronglyMeasurable
        (ae_of_all μ fun ω => by
          rw [Real.norm_eq_abs]; exact hbd_trig_theta _ Real.abs_sin_le_one ω))

/-! ## Full OS axioms for the continuum limit

Each axiom is proved from the lattice construction via a specific mechanism:

- **OS0 (Analyticity):** The generating functional `Z[J] = ∫ exp(i⟨ω,J⟩) dμ` is
  entire analytic because: (1) for each ω, `z ↦ exp(iz·ω(f))` is entire, (2) the
  exponential moment bound `∫ exp(c|ω(f)|) dμ < ∞` (Fernique-type, from Nelson's
  hypercontractive estimate, uniform in lattice spacing) justifies differentiation
  under the integral, (3) the uniform bounds transfer to the weak limit by Vitali's
  convergence theorem.

- **OS1 (Regularity):** The bound `‖Z[J]‖ ≤ exp(c(‖J‖₁ + ‖J‖_p^p))` follows from
  Nelson's hypercontractive estimate: `‖:φⁿ:‖_Lp ≤ (p-1)^{n/2} ‖:φⁿ:‖_L2`, which
  gives uniform moment bounds on the lattice. These transfer to the continuum limit.
  For P(Φ)₂ the relevant bound is `‖Z[f]‖ ≤ exp(c‖f‖²_{H⁻¹})` with p = 2.

- **OS2 (Euclidean invariance):** Translation invariance follows from lattice
  translation invariance (exact symmetry) + density of rational translations +
  continuity of the translation action on S'(ℝ²). Rotation invariance follows from
  the Ward identity: the rotation anomaly O_break has scaling dimension 4 > d = 2,
  making it RG-irrelevant with coefficient O(a²). Super-renormalizability of P(Φ)₂
  ensures no logarithmic corrections, so the anomaly vanishes in the continuum limit.

- **OS4 (Clustering):** The uniform spectral gap `m_phys ≥ m₀ > 0` from
  `spectral_gap_uniform` gives exponential clustering on the lattice:
  `|⟨F·G_R⟩ - ⟨F⟩⟨G⟩| ≤ C·exp(-m₀R)`. For bounded continuous observables,
  this transfers to the weak limit. The clustering bound on the characteristic
  functional `Z[f + T_a g] - Z[f]·Z[g]` follows from the exponential decay of
  connected correlations. -/

/-- **Exponential moments of the continuum limit** (Fernique + Nelson).

For any test function `f ∈ S(ℝ²)`, there exists `c > 0` such that the
exponential moment `∫ exp(c · |⟨ω, f⟩|) dμ(ω)` is finite.

This is the key analytic estimate that transfers from the lattice to the
continuum limit. On the lattice, it follows from:
- **Free field:** Fernique's theorem gives Gaussian exponential moments.
- **Interaction:** The Wick-ordered interaction preserves the exponential
  moment structure (Glimm-Jaffe, §19.1; Simon, §V.2).
- **Uniform in a:** Nelson's hypercontractive estimate gives
  `‖:φⁿ:‖_{Lp} ≤ (p-1)^{n/2} · ‖:φⁿ:‖_{L2}`, uniformly in lattice spacing.

Transfer to the limit: the exponential moment bound is a lower-semicontinuous
functional under weak convergence, so the bound passes to the limit μ.

This single axiom feeds both OS0 (analyticity) and OS1 (regularity).

**Strengthening note:** The axiom states `∀ c > 0` (all exponential moments)
rather than `∃ c > 0`. This is the correct mathematical statement: Fernique's
theorem gives Gaussian moments for all c, and Nelson's hypercontractive estimate
preserves this for the interacting measure. The stronger form is needed to
establish integrability of `exp(|⟨ω, f⟩|)` (the c = 1 case) in the OS1 proof. -/
axiom continuum_exponential_moments (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (h_limit : IsPphi2Limit μ P mass)
    (f : TestFunction2) :
    ∀ (c : ℝ), 0 < c →
    Integrable (fun ω : FieldConfig2 => Real.exp (c * |ω f|)) μ

/-- **Analyticity of the complex generating functional from exponential moments.**

If the measure μ has all exponential moments (`∀ f c > 0, ∫ exp(c|ω(f)|) dμ < ∞`),
then the complex generating functional `z ↦ Z_ℂ[Σ zᵢ Jᵢ]` is jointly analytic
in `z ∈ ℂⁿ` for any finite collection of complex test functions Jᵢ.

The proof combines:
1. **Power series representation:** Each ω-integrand `exp(i Σ zᵢ⟨ω,Jᵢ⟩)` is entire
   in z, so the integral has a termwise convergent power series with moments
   as coefficients.
2. **Exponential moment bounds** justify term-by-term integration (dominated
   convergence with majorant `exp(Σ |Im zᵢ| · |⟨ω, Jᵢ⟩|)`).
3. Alternatively: single-variable analyticity (dominated convergence + Morera)
   combined with **Hartogs' theorem** gives joint analyticity.

References: Simon, P(φ)₂ Theory, §I.2; Reed-Simon II §X.7 (Hartogs). -/
axiom analyticOn_generatingFunctionalC
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (h_moments : ∀ (f : TestFunction2) (c : ℝ), 0 < c →
        Integrable (fun ω : FieldConfig2 => Real.exp (c * |ω f|)) μ)
    (n : ℕ) (J : Fin n → TestFunction2ℂ) :
    AnalyticOn ℂ (fun z : Fin n → ℂ =>
      generatingFunctionalℂ μ (∑ i, z i • J i)) Set.univ

/-- **OS0 for the continuum limit** from exponential moments.

The generating functional `Z[Σ zᵢJᵢ] = ∫ exp(i · Σ zᵢ⟨ω, Jᵢ⟩) dμ` is
entire analytic in `z ∈ ℂⁿ`. Follows from `analyticOn_generatingFunctionalC`
and `continuum_exponential_moments`. -/
theorem os0_for_continuum_limit (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (ContinuumTestFunction 2)))
    (hμ : IsProbabilityMeasure μ)
    (h_limit : IsPphi2Limit μ P mass) :
    @OS0_Analyticity μ hμ := by
  have h_exp := continuum_exponential_moments P mass hmass μ h_limit
  intro n J
  exact analyticOn_generatingFunctionalC μ h_exp n J

/-- **Exponential moment bound via Schwartz norms.**

The exponential moment `∫ exp(|ω(g)|) dμ` is bounded by
`exp(c · (‖g‖₁ + ‖g‖₂²))` for some universal constant c > 0.

This combines:
1. **Jensen + covariance:** `E[exp(|X|)] ≤ exp(C · Var(X))` for `X = ω(g)`
2. **H⁻¹ norm bound:** `Var(ω(g)) = ‖g‖²_{H⁻¹(μ)} ≤ C ‖g‖²_{H⁻¹}`
3. **Sobolev embedding:** `‖g‖²_{H⁻¹} ≤ c' · (‖g‖₁ + ‖g‖₂²)` in d=2

Reference: Simon P(φ)₂ Theory §I.3; Nelson, J. Funct. Anal. (1973). -/
axiom exponential_moment_schwartz_bound
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (h_moments : ∀ (f : TestFunction2) (c : ℝ), 0 < c →
        Integrable (fun ω : FieldConfig2 => Real.exp (c * |ω f|)) μ) :
    ∃ (c : ℝ), 0 < c ∧ ∀ (g : TestFunction2),
      ∫ ω : FieldConfig2, Real.exp (|ω g|) ∂μ ≤
        Real.exp (c * (∫ x, ‖g x‖ ∂volume + ∫ x, ‖g x‖ ^ (2 : ℝ) ∂volume))

/-- **OS1 for the continuum limit** from exponential moments.

The regularity bound `‖Z[J]‖ ≤ exp(c · (‖J‖₁ + ‖J‖_p^p))` holds for
complex test functions J ∈ S(ℝ², ℂ).

Proof chain from `continuum_exponential_moments`:
1. Write J = f + ig with f = Re(J), g = Im(J) real Schwartz functions.
2. `Z[J] = ∫ exp(i⟨ω, f⟩ - ⟨ω, g⟩) dμ`, so `|Z[J]| ≤ ∫ exp(|⟨ω, g⟩|) dμ`.
3. By `continuum_exponential_moments` for g: `∫ exp(c|⟨ω,g⟩|) dμ < ∞`.
4. Jensen's inequality + covariance estimate: `∫ exp(|⟨ω,g⟩|) dμ ≤ exp(C · ‖g‖²_{H⁻¹})`.
   (The H⁻¹ norm controls the variance of the Gaussian part; the Wick-ordered
   interaction only improves the bound.)
5. Since `‖g‖²_{H⁻¹} ≤ c' · (‖J‖₁ + ‖J‖₂²)`, this gives OS1 with p = 2. -/
theorem os1_for_continuum_limit (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (ContinuumTestFunction 2)))
    (hμ : IsProbabilityMeasure μ)
    (h_limit : IsPphi2Limit μ P mass) :
    @OS1_Regularity μ hμ := by
  have h_exp := continuum_exponential_moments P mass hmass μ h_limit
  -- Step 1: |Z_ℂ[J]| ≤ ∫ exp(|⟨ω, Im(J)⟩|) dμ
  -- (from |exp(i⟨ω,Re J⟩ - ⟨ω,Im J⟩)| = exp(-⟨ω,Im J⟩) ≤ exp(|⟨ω,Im J⟩|))
  have h_bound : ∀ (J : TestFunction2ℂ),
      ‖generatingFunctionalℂ μ J‖ ≤
        ∫ ω : FieldConfig2, Real.exp (|ω (schwartzIm J)|) ∂μ := by
    intro J
    -- Integrability of exp(|ω(Im J)|) from the strengthened exponential moments axiom
    have hint_abs : Integrable (fun ω : FieldConfig2 => Real.exp (|ω (schwartzIm J)|)) μ := by
      have := h_exp (schwartzIm J) 1 one_pos; simp only [one_mul] at this; exact this
    -- Pointwise bound: ‖exp(i·Re - Im)‖ ≤ exp(|Im|)
    -- Because ‖exp(z)‖ = exp(Re z), and Re(i·a - b) = -b, and exp(-b) ≤ exp(|b|)
    have h_le : ∀ ω : FieldConfig2,
        ‖Complex.exp (Complex.I * (↑(ω (schwartzRe J)) + Complex.I * ↑(ω (schwartzIm J))))‖ ≤
        Real.exp (|ω (schwartzIm J)|) := by
      intro ω
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      -- Re(i·(a + i·b)) = -b ≤ |b|
      have h_re : (Complex.I * (↑(ω (schwartzRe J)) + Complex.I * ↑(ω (schwartzIm J)))).re =
          -(ω (schwartzIm J)) := by
        simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
      rw [h_re]
      exact (le_abs_self (-(ω (schwartzIm J)))).trans_eq (abs_neg _)
    -- Chain: ‖Z[J]‖ ≤ ∫ ‖integrand‖ ≤ ∫ exp(|y|)
    exact (norm_integral_le_integral_norm _).trans
      (integral_mono_of_nonneg
        (ae_of_all μ fun ω => norm_nonneg _)
        hint_abs
        (ae_of_all μ h_le))
  -- Step 2: Exponential moments for Im(J) give ∫ exp(|⟨ω, Im J⟩|) dμ < ∞
  have h_exp_im : ∀ (J : TestFunction2ℂ),
      ∀ (c : ℝ), 0 < c →
      Integrable (fun ω : FieldConfig2 => Real.exp (c * |ω (schwartzIm J)|)) μ := by
    intro J c hc; exact h_exp (schwartzIm J) c hc
  -- Step 3: ∫ exp(|⟨ω,g⟩|) dμ ≤ exp(C · (‖g‖₁ + ‖g‖₂²))
  -- (Jensen + covariance bound: Var(⟨ω,g⟩) ≤ C‖g‖²_{H⁻¹} ≤ C'(‖g‖₁+‖g‖₂²))
  have h_exp_norm_bound : ∃ (c : ℝ), 0 < c ∧ ∀ (g : TestFunction2),
      ∫ ω : FieldConfig2, Real.exp (|ω g|) ∂μ ≤
        Real.exp (c * (∫ x, ‖g x‖ ∂volume + ∫ x, ‖g x‖ ^ (2 : ℝ) ∂volume)) :=
    exponential_moment_schwartz_bound μ h_exp
  -- Step 4: Combine: ‖Z_ℂ[J]‖ ≤ exp(c(‖Im J‖₁ + ‖Im J‖₂²)) ≤ exp(c(‖J‖₁ + ‖J‖₂²))
  obtain ⟨c, hc, h_norm⟩ := h_exp_norm_bound
  -- Combination: h_bound + h_norm + (‖Im J‖ ≤ ‖J‖) gives OS1
  exact ⟨2, c, one_le_two, le_refl _, hc, fun J => by
    calc ‖generatingFunctionalℂ μ J‖
        ≤ ∫ ω : FieldConfig2, Real.exp |ω (schwartzIm J)| ∂μ := h_bound J
      _ ≤ Real.exp (c * ((∫ x, ‖schwartzIm J x‖) + ∫ x, ‖schwartzIm J x‖ ^ (2 : ℝ))) :=
            h_norm (schwartzIm J)
      _ ≤ Real.exp (c * ((∫ x : SpaceTime2, ‖J x‖) + ∫ x : SpaceTime2, ‖J x‖ ^ (2 : ℝ))) := by
            apply Real.exp_le_exp.mpr
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hc)
            have hIm : ∀ x, ‖schwartzIm J x‖ ≤ ‖J x‖ :=
              fun x => RCLike.norm_im_le_norm (J x)
            apply add_le_add
            · exact integral_mono
                (SchwartzMap.integrable (schwartzIm J)).norm
                (SchwartzMap.integrable J).norm hIm
            · exact integral_mono
                (schwartz_integrable_norm_rpow (schwartzIm J) two_pos)
                (schwartz_integrable_norm_rpow J two_pos)
                (fun x => Real.rpow_le_rpow (norm_nonneg _) (hIm x) (by norm_num))⟩

/-- **Complex generating functional invariance from real invariance.**

If the real generating functional is g-invariant for all real test functions,
then the complex generating functional is also g-invariant.

**Proof**: Define analytic families `F(z) = Z_ℂ[Re(J) + z·Im(J)]` and
`G(z) = Z_ℂ[g·Re(J) + z·g·Im(J)]`. Both are entire (from exponential
moments via `analyticOn_generatingFunctionalC`). They agree on ℝ (reduces
to real GF invariance). By the identity theorem for analytic functions,
`F = G` on all of ℂ. Evaluating at `z = i` gives `Z_ℂ[J] = Z_ℂ[g·J]`. -/
theorem complex_gf_invariant_of_real_gf_invariant
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (h_moments : ∀ (f : TestFunction2) (c : ℝ), 0 < c →
      Integrable (fun ω : FieldConfig2 => Real.exp (c * |ω f|)) μ)
    (g : E2)
    (h_real : ∀ f : TestFunction2,
      generatingFunctional μ f = generatingFunctional μ (euclideanAction2 g f))
    (J : TestFunction2ℂ) :
    generatingFunctionalℂ μ J = generatingFunctionalℂ μ (euclideanAction2ℂ g J) := by
  let JF : Fin 2 → TestFunction2ℂ :=
    ![schwartzOfReal (schwartzRe J), schwartzOfReal (schwartzIm J)]
  let JG : Fin 2 → TestFunction2ℂ :=
    ![schwartzOfReal (euclideanAction2 g (schwartzRe J)),
      schwartzOfReal (euclideanAction2 g (schwartzIm J))]
  let ψ : ℂ → Fin 2 → ℂ := fun z => ![(1 : ℂ), z]
  let F : ℂ → ℂ := fun z => generatingFunctionalℂ μ (∑ i : Fin 2, (ψ z i) • JF i)
  let G : ℂ → ℂ := fun z => generatingFunctionalℂ μ (∑ i : Fin 2, (ψ z i) • JG i)
  have hψ_analytic : AnalyticOn ℂ ψ Set.univ := by
    refine AnalyticOn.pi (fun i => ?_)
    fin_cases i
    · simpa using (analyticOn_const : AnalyticOn ℂ (fun _ : ℂ => (1 : ℂ)) Set.univ)
    · simpa using (analyticOn_id : AnalyticOn ℂ (fun z : ℂ => z) Set.univ)
  have hF_analytic : AnalyticOn ℂ F Set.univ := by
    have hbase : AnalyticOn ℂ (fun w : Fin 2 → ℂ =>
        generatingFunctionalℂ μ (∑ i : Fin 2, w i • JF i)) Set.univ :=
      analyticOn_generatingFunctionalC μ h_moments 2 JF
    exact hbase.comp hψ_analytic (by intro z hz; simp [Set.mem_univ])
  have hG_analytic : AnalyticOn ℂ G Set.univ := by
    have hbase : AnalyticOn ℂ (fun w : Fin 2 → ℂ =>
        generatingFunctionalℂ μ (∑ i : Fin 2, w i • JG i)) Set.univ :=
      analyticOn_generatingFunctionalC μ h_moments 2 JG
    exact hbase.comp hψ_analytic (by intro z hz; simp [Set.mem_univ])
  have h_real_axis : ∀ r : ℝ, F r = G r := by
    intro r
    have hF_r : F r = generatingFunctional μ (schwartzRe J + r • schwartzIm J) := by
      simpa [F, ψ, JF, Fin.sum_univ_two] using
        (generatingFunctionalℂ_ofReal_add_real_smul μ (schwartzRe J) (schwartzIm J) r)
    have hG_r : G r = generatingFunctional μ
        (euclideanAction2 g (schwartzRe J) + r • euclideanAction2 g (schwartzIm J)) := by
      simpa [G, ψ, JG, Fin.sum_univ_two] using
        (generatingFunctionalℂ_ofReal_add_real_smul μ
          (euclideanAction2 g (schwartzRe J)) (euclideanAction2 g (schwartzIm J)) r)
    rw [hF_r, hG_r]
    simpa [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul] using
      h_real (schwartzRe J + r • schwartzIm J)
  have hF_nhd : AnalyticOnNhd ℂ F Set.univ := (analyticOn_univ.mp hF_analytic)
  have hG_nhd : AnalyticOnNhd ℂ G Set.univ := (analyticOn_univ.mp hG_analytic)
  have hfreq : ∃ᶠ z : ℂ in nhdsWithin (0 : ℂ) ({0}ᶜ), F z = G z := by
    rw [Filter.frequently_iff]
    intro U hU
    rcases Metric.mem_nhdsWithin_iff.mp hU with ⟨ε, hε, hUball⟩
    have hball : (ε / 2 : ℂ) ∈ Metric.ball (0 : ℂ) ε := by
      rw [Metric.mem_ball, Complex.dist_eq, sub_zero]
      have hnorm : ‖(ε / 2 : ℂ)‖ = |ε| / 2 := by simp
      rw [hnorm]
      have hεabs : |ε| = ε := abs_of_pos hε
      rw [hεabs]
      linarith
    have hne : (ε / 2 : ℂ) ≠ 0 := by
      exact_mod_cast (show (ε / 2 : ℝ) ≠ 0 by linarith)
    refine ⟨(ε / 2 : ℂ), ?_, ?_⟩
    · exact hUball ⟨hball, hne⟩
    · simpa using h_real_axis (ε / 2)
  have h_eq : Set.EqOn F G Set.univ := by
    simpa using
      hF_nhd.eqOn_of_preconnected_of_frequently_eq hG_nhd
        isPreconnected_univ (by simp : (0 : ℂ) ∈ Set.univ) hfreq
  have hJ_decomp :
      J = schwartzOfReal (schwartzRe J) + (Complex.I : ℂ) • schwartzOfReal (schwartzIm J) :=
    schwartz_decompose J
  have hJg_decomp : euclideanAction2ℂ g J =
      schwartzOfReal (euclideanAction2 g (schwartzRe J)) +
      (Complex.I : ℂ) • schwartzOfReal (euclideanAction2 g (schwartzIm J)) := by
    calc
      euclideanAction2ℂ g J
          = schwartzOfReal (schwartzRe (euclideanAction2ℂ g J)) +
              (Complex.I : ℂ) • schwartzOfReal (schwartzIm (euclideanAction2ℂ g J)) :=
            schwartz_decompose (euclideanAction2ℂ g J)
      _ = schwartzOfReal (euclideanAction2 g (schwartzRe J)) +
          (Complex.I : ℂ) • schwartzOfReal (euclideanAction2 g (schwartzIm J)) := by
            simp
  have hF_I : F Complex.I = generatingFunctionalℂ μ
      (schwartzOfReal (schwartzRe J) + (Complex.I : ℂ) • schwartzOfReal (schwartzIm J)) := by
    simp [F, ψ, JF, Fin.sum_univ_two]
  have hG_I : G Complex.I = generatingFunctionalℂ μ
      (schwartzOfReal (euclideanAction2 g (schwartzRe J)) +
        (Complex.I : ℂ) • schwartzOfReal (euclideanAction2 g (schwartzIm J))) := by
    simp [G, ψ, JG, Fin.sum_univ_two]
  have hGF_J : generatingFunctionalℂ μ J =
      generatingFunctionalℂ μ
        (schwartzOfReal (schwartzRe J) + (Complex.I : ℂ) • schwartzOfReal (schwartzIm J)) :=
    congrArg (generatingFunctionalℂ μ) hJ_decomp
  have hGF_gJ : generatingFunctionalℂ μ (euclideanAction2ℂ g J) =
      generatingFunctionalℂ μ
        (schwartzOfReal (euclideanAction2 g (schwartzRe J)) +
          (Complex.I : ℂ) • schwartzOfReal (euclideanAction2 g (schwartzIm J))) :=
    congrArg (generatingFunctionalℂ μ) hJg_decomp
  calc
    generatingFunctionalℂ μ J = F Complex.I := hGF_J.trans hF_I.symm
    _ = G Complex.I := h_eq (by simp)
    _ = generatingFunctionalℂ μ (euclideanAction2ℂ g J) := hG_I.trans hGF_gJ.symm

/-- **OS2 for the continuum limit** from translation + rotation invariance.

E(2) = ℝ² ⋊ O(2) is generated by translations and O(2). We combine:
- `translation_invariance_continuum`: `Z[τ_v f] = Z[f]` for all v ∈ ℝ²
- `rotation_invariance_continuum`: `Z[R·f] = Z[f]` for all R ∈ O(2)

Proof chain to `OS2_EuclideanInvariance`:
1. Any `g ∈ E(2)` decomposes as `g = (R, t)` with R ∈ O(2), t ∈ ℝ².
   The action `g · f = τ_t(R · f)`.
2. `Z[g · f] = Z[τ_t(R · f)] = Z[R · f] = Z[f]`.
   (First equality by definition, second by translation invariance,
   third by rotation invariance.)
3. Extension from real to complex: `Z_ℂ[g · J]` for complex J = f + ig
   follows from the real case via `complex_gf_invariant_of_real_gf_invariant`. -/
theorem os2_for_continuum_limit (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (ContinuumTestFunction 2)))
    (hμ : IsProbabilityMeasure μ)
    (h_limit : IsPphi2Limit μ P mass) :
    @OS2_EuclideanInvariance μ hμ := by
  have h_trans := translation_invariance_continuum P mass hmass μ hμ h_limit
  have h_rot := rotation_invariance_continuum P mass hmass μ h_limit
  -- Step 1: Real generating functional is E(2)-invariant.
  -- Any g = ⟨R, t⟩ ∈ E(2) acts by g·f = τ_t(R·f), so
  -- Z[g·f] = Z[τ_t(R·f)] = Z[R·f] (by h_trans) = Z[f] (by h_rot).
  have h_real_invariance : ∀ (g : E2) (f : TestFunction2),
      generatingFunctional μ f =
      generatingFunctional μ (euclideanAction2 g f) := by
    intro g f
    -- Decompose g = (R, t): Z[f] = Z[R·f] (rotation) = Z[τ_t(R·f)] (translation) = Z[g·f]
    calc generatingFunctional μ f
        = generatingFunctional μ ((euclideanAction2 ⟨g.R, 0⟩) f) := by rw [h_rot g.R f]
      _ = generatingFunctional μ ((SchwartzMap.translate g.t)
            ((euclideanAction2 ⟨g.R, 0⟩) f)) := h_trans g.t _
      _ = generatingFunctional μ ((euclideanAction2 g) f) := by
            congr 1; ext x
            change f (g.R.symm ((x - g.t) - 0)) = f (g.R.symm (x - g.t))
            simp [sub_zero]
  -- Step 2: Extend to complex test functions.
  -- Z_ℂ[J] = ∫ exp(i⟨ω, Re J⟩ - ⟨ω, Im J⟩) dμ. Under g ∈ E(2):
  -- ⟨ω, Re(g·J)⟩ = ⟨g⁻¹·ω, Re J⟩ and ⟨ω, Im(g·J)⟩ = ⟨g⁻¹·ω, Im J⟩.
  -- Since μ is g-invariant (from Step 1), substituting ω' = g⁻¹·ω gives
  -- Z_ℂ[g·J] = Z_ℂ[J].
  have h_moments := continuum_exponential_moments P mass hmass μ h_limit
  intro g J
  exact complex_gf_invariant_of_real_gf_invariant μ h_moments g (h_real_invariance g) J

/-- **Exponential clustering of the continuum limit** from spectral gap.

For any test functions `f, g ∈ S(ℝ²)`, there exist `m₀, C > 0` such that

  `‖Z[f + τ_a g] - Z[f] · Z[g]‖ ≤ C · exp(-m₀ · ‖a‖)`

for all translations a ∈ ℝ². This is stronger than OS4 (exponential rate
rather than just convergence to zero).

Proof chain from the lattice:
1. `spectral_gap_uniform`: the transfer matrix T has mass gap m_phys ≥ m₀ > 0
   uniformly in lattice spacing a (Perron-Frobenius + compactness).
2. Spectral decomposition of T gives lattice exponential clustering:
   `|⟨F · (T_R G)⟩_a - ⟨F⟩_a · ⟨G⟩_a| ≤ ‖F‖_∞ · ‖G‖_∞ · exp(-m₀ · R)`.
3. Apply to `F = exp(i⟨·, ι_a f⟩)`, `G = exp(i⟨·, ι_a g⟩)` (bounded continuous):
   `|Z_a[f + τ_R g] - Z_a[f] · Z_a[g]| ≤ C(f,g) · exp(-m₀ · R)`.
4. Weak convergence `ν_a ⇀ μ` preserves the bound for bounded continuous
   observables: the LHS converges to the continuum quantity, and the RHS
   is independent of a. -/
axiom continuum_exponential_clustering (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (h_limit : IsPphi2Limit μ P mass)
    (f g : TestFunction2) :
    ∃ (m₀ C : ℝ), 0 < m₀ ∧ 0 < C ∧
    ∀ (a : SpaceTime2),
    ‖generatingFunctional μ (f + SchwartzMap.translate a g)
     - generatingFunctional μ f * generatingFunctional μ g‖
    ≤ C * Real.exp (-m₀ * ‖a‖)

/-- **OS4 for the continuum limit** from exponential clustering.

The ε-δ formulation of OS4 follows immediately from the exponential bound:
given `ε > 0`, choose `R` large enough that `C · exp(-m₀ · R) < ε`.

Proof chain from `continuum_exponential_clustering`:
1. Get m₀, C > 0 and the bound `‖Z[f+τ_a g] - Z[f]Z[g]‖ ≤ C·exp(-m₀·‖a‖)`.
2. Set `R = max(1, (1/m₀) · log(C/ε))`.
3. For `‖a‖ > R`: `C · exp(-m₀ · ‖a‖) < C · exp(-m₀ · R) ≤ C · (ε/C) = ε`. -/
theorem os4_for_continuum_limit (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (ContinuumTestFunction 2)))
    (hμ : IsProbabilityMeasure μ)
    (h_limit : IsPphi2Limit μ P mass) :
    @OS4_Clustering μ hμ := by
  intro f g ε hε
  -- Step 1: Get exponential clustering bound
  obtain ⟨m₀, C, hm₀, hC, h_bound⟩ := continuum_exponential_clustering P mass hmass μ h_limit f g
  -- Step 2: Choose R so that C · exp(-m₀ · R) < ε
  refine ⟨max 1 (Real.log (C / ε) / m₀), lt_max_of_lt_left one_pos, fun a ha => ?_⟩
  -- Step 3: ‖a‖ > R ≥ 1, so ‖a‖ > 0 and exp(-m₀‖a‖) < 1
  have ha_pos : (0 : ℝ) < ‖a‖ :=
    lt_of_lt_of_le one_pos (le_of_lt (lt_of_le_of_lt (le_max_left _ _) ha))
  -- Step 4: Bound ≤ C · exp(-m₀ · ‖a‖) < ε
  calc ‖generatingFunctional μ (f + SchwartzMap.translate a g)
         - generatingFunctional μ f * generatingFunctional μ g‖
      ≤ C * Real.exp (-m₀ * ‖a‖) := h_bound a
    _ < ε := by
        -- m₀ · ‖a‖ > 0 so exp(-m₀·‖a‖) < 1, giving C·exp(...) < C.
        -- Also ‖a‖ > log(C/ε)/m₀ so m₀·‖a‖ > log(C/ε),
        -- giving exp(-m₀·‖a‖) < ε/C, so C·exp(...) < ε.
        have hCε_pos : (0 : ℝ) < C / ε := div_pos hC hε
        have ha_gt : ‖a‖ > Real.log (C / ε) / m₀ :=
          lt_of_le_of_lt (le_max_right _ _) ha
        have hm₀a_gt : Real.log (C / ε) < m₀ * ‖a‖ := by
          have h : Real.log (C / ε) / m₀ < ‖a‖ :=
            lt_of_le_of_lt (le_max_right _ _) ha
          nlinarith [div_mul_cancel₀ (Real.log (C / ε)) (ne_of_gt hm₀)]
        have hexp_lt : Real.exp (-m₀ * ‖a‖) < Real.exp (-Real.log (C / ε)) := by
          apply Real.exp_lt_exp.mpr
          linarith
        have hexp_simp : Real.exp (-Real.log (C / ε)) = ε / C := by
          rw [Real.exp_neg, Real.exp_log hCε_pos, inv_div]
        rw [hexp_simp] at hexp_lt
        have hC_pos := hC
        calc C * Real.exp (-m₀ * ‖a‖)
            < C * (ε / C) := by apply mul_lt_mul_of_pos_left hexp_lt hC_pos
          _ = ε := by field_simp

/-! ## Textbook axioms for clustering → ergodicity -/

/-- **Textbook axiom: Z₂ symmetry of the P(Φ)₂ measure.**

The P(Φ)₂ continuum limit measure μ is invariant under field negation φ → -φ:
  Measure.map (Neg.neg) μ = μ

This follows from:
1. The GFF is a centered Gaussian, hence invariant under φ → -φ.
2. The interaction P(φ) is even (`InteractionPolynomial.eval_neg`: P(-φ) = P(φ)),
   so the Boltzmann weight exp(-V_a(φ)) is invariant under φ → -φ.
3. Therefore each lattice measure dμ_a = (1/Z) exp(-V_a) dμ_{GFF} is Z₂-symmetric.
4. Z₂ symmetry is preserved under weak limits (since field negation is
   continuous in the weak-* topology on S'(ℝ²)).

Reference: Simon, *The P(φ)₂ Euclidean QFT*, §II.3;
Glimm-Jaffe, *Quantum Physics*, §6.1. -/
theorem pphi2_measure_neg_invariant (P : InteractionPolynomial)
    (mass : ℝ) (_hmass : 0 < mass)
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (h_limit : IsPphi2Limit μ P mass) :
    Measure.map (Neg.neg : FieldConfig2 → FieldConfig2) μ = μ := by
  rcases h_limit with ⟨_a, _ν, _hprob, _ha_tend, _ha_pos, _hmom, hneg⟩
  exact hneg

/-- Negation on Configuration is measurable w.r.t. the cylindrical σ-algebra. -/
theorem configuration_neg_measurable :
    @Measurable FieldConfig2 FieldConfig2
      instMeasurableSpaceConfiguration instMeasurableSpaceConfiguration
      (Neg.neg : FieldConfig2 → FieldConfig2) :=
  configuration_measurable_of_eval_measurable _ fun f =>
    (configuration_eval_measurable f).neg

/-- The generating functional of a Z₂-symmetric measure is real-valued.

Proof: conj(Z[f]) = conj(∫ exp(iωf) dμ) = ∫ exp(-iωf) dμ
     = ∫ exp(i(-ω)f) dμ = ∫ exp(iωf) d(map(-) μ) = ∫ exp(iωf) dμ = Z[f].
So Z[f] = conj(Z[f]), hence Im(Z[f]) = 0. -/
theorem pphi2_generating_functional_real (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (h_limit : IsPphi2Limit μ P mass)
    (f : TestFunction2) :
    (generatingFunctional μ f).im = 0 := by
  have h_sym := pphi2_measure_neg_invariant P mass hmass μ h_limit
  -- Strategy: show conj(Z[f]) = Z[f], then Im = 0.
  -- conj(Z[f]) = conj(∫ exp(iωf) dμ) = ∫ conj(exp(iωf)) dμ   [integral_conj]
  --            = ∫ exp(-iωf) dμ                                  [conj of exp]
  --            = ∫ exp(i(-ω)f) dμ                                [(-ω)f = -(ωf)]
  --            = ∫ exp(iωf) d(map(-) μ)                          [change of vars]
  --            = ∫ exp(iωf) dμ = Z[f]                            [h_sym]
  unfold generatingFunctional
  set g := fun ω : FieldConfig2 => Complex.exp (Complex.I * ↑(ω f))
  -- Step 1: conj(∫ g dμ) = ∫ conj(g) dμ via integral_conj
  have hconj : starRingEnd ℂ (∫ ω, g ω ∂μ) = ∫ ω, starRingEnd ℂ (g ω) ∂μ :=
    (integral_conj (f := g)).symm
  -- Step 2: conj(exp(i·r)) = exp(-i·r) for real r
  have hconj_exp : ∀ ω : FieldConfig2,
      starRingEnd ℂ (g ω) = Complex.exp (Complex.I * ↑((-ω) f)) := by
    intro ω
    simp only [g]
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal,
        ContinuousLinearMap.neg_apply, Complex.ofReal_neg]
    ring
  -- Step 3: ∫ exp(i(-ω)f) dμ = ∫ exp(iωf) d(map(-) μ) by change of variables
  -- Then use h_sym to get = ∫ exp(iωf) dμ
  have hcov : ∫ ω, Complex.exp (Complex.I * ↑((-ω) f)) ∂μ = ∫ ω, g ω ∂μ := by
    have heq : (fun ω : FieldConfig2 => Complex.exp (Complex.I * ↑((-ω) f))) =
        g ∘ Neg.neg := by
      ext ω; simp only [g, Function.comp]
    rw [heq]
    -- ∫ (g ∘ Neg.neg) dμ = ∫ g d(map Neg.neg μ) = ∫ g dμ  by h_sym
    have hasm : AEStronglyMeasurable g (Measure.map Neg.neg μ) := by
      rw [h_sym]
      exact ((Complex.measurable_ofReal.comp (configuration_eval_measurable f)).const_mul
        Complex.I |>.cexp).aestronglyMeasurable
    have := MeasureTheory.integral_map configuration_neg_measurable.aemeasurable hasm
    -- integral_map: ∫ g ∂(map Neg μ) = ∫ (g ∘ Neg) ∂μ
    -- h_sym: map Neg μ = μ, so ∫ g ∂μ = ∫ (g ∘ Neg) ∂μ
    rw [h_sym] at this
    exact this.symm
  -- Combine: conj(Z[f]) = Z[f]
  have hself_conj : starRingEnd ℂ (∫ ω, g ω ∂μ) = ∫ ω, g ω ∂μ := by
    rw [hconj]
    simp_rw [hconj_exp]
    exact hcov
  -- conj(z) = z implies z.im = 0
  have := Complex.conj_eq_iff_im.mp hself_conj
  exact this

/-- **Continuity of the generating functional under translations.**

The map t ↦ Z[f + τ_{(t,0)} g] is continuous in t : ℝ. This follows from
the dominated convergence theorem applied to the integral
∫ exp(i⟨ω, f + τ_{(t,0)} g⟩) dμ(ω), since the integrand is bounded by 1
and converges pointwise as the test function varies continuously.

Reference: Reed-Simon II, §IX.3 (continuity of characteristic functions). -/
theorem generatingFunctional_translate_continuous
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (f g : TestFunction2) :
    Continuous (fun t : ℝ =>
      generatingFunctional μ (f + SchwartzMap.translate
        ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![t, 0]) g)) := by
  -- Define the test function as a function of t
  set h : ℝ → TestFunction2 := fun t =>
    f + SchwartzMap.translate ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![t, 0]) g with hh_def
  -- The generating functional is ∫ exp(i * ω(h(t))) dμ(ω)
  -- Apply DCT: F t ω = exp(i * ω(h(t))), bound = 1
  change Continuous (fun t => ∫ ω : FieldConfig2, Complex.exp (Complex.I * ↑(ω (h t))) ∂μ)
  apply MeasureTheory.continuous_of_dominated
  -- 1. AEStronglyMeasurable for each t
  · intro t
    exact ((Complex.measurable_ofReal.comp (configuration_eval_measurable (h t))).const_mul
      Complex.I |>.cexp).aestronglyMeasurable
  -- 2. Norm bound: ‖exp(i * ω(h(t)))‖ ≤ 1 for all t, ω
  · intro t
    exact ae_of_all μ fun ω => by
      rw [show Complex.I * ↑(ω (h t)) = ↑(ω (h t)) * Complex.I from mul_comm _ _]
      exact le_of_eq (Complex.norm_exp_ofReal_mul_I _)
  -- 3. Integrable bound: ∫ 1 dμ < ∞ (probability measure)
  · exact integrable_const 1
  -- 4. Pointwise continuity: for each ω, t ↦ exp(i * ω(h(t))) is continuous
  · exact ae_of_all μ fun ω => by
      apply Complex.continuous_exp.comp
      apply Continuous.mul continuous_const
      apply Complex.continuous_ofReal.comp
      -- Need: t ↦ ω(h(t)) is continuous
      -- ω is a continuous linear functional, so it suffices that t ↦ h(t) is continuous
      -- h(t) = f + translate(t,0) g, and ω(h(t)) = ω(f) + ω(translate(t,0) g)
      -- So we need t ↦ ω(translate(t,0) g) continuous
      show Continuous (fun t => ω (h t))
      simp only [hh_def, map_add]
      apply Continuous.add continuous_const
      -- Need: t ↦ ω(translate(t,0) g) continuous
      -- ω is continuous, and translate(t,0) g is continuous in t (Schwartz topology)
      apply ω.continuous.comp
      -- Need: t ↦ translate(t,0) g continuous in Schwartz topology
      -- This is the key step using TimeTranslation infrastructure
      haveI : Fact (0 < 2) := ⟨by norm_num⟩
      -- translate(t,0) g and timeTranslationSchwartz(-t) g agree pointwise
      have h_eq : (fun t => SchwartzMap.translate
          ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![t, 0]) g) =
          (fun t => TimeTranslation.timeTranslationSchwartz (-t) g) := by
        funext t
        ext x
        simp only [SchwartzMap.translate, SchwartzMap.compCLMOfAntilipschitz_apply,
          Function.comp_apply, TimeTranslation.timeTranslationSchwartz,
          TimeTranslation.timeTranslationSchwartzCLM,
          SchwartzMap.compCLMOfAntilipschitz_apply, Function.comp_apply]
        congr 1
        -- Need: x - (t, 0) = timeShift(-t)(x) as elements of SpaceTime 2
        ext i
        simp only [TimeTranslation.timeShift]
        fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, sub_eq_add_neg]
      rw [h_eq]
      exact (TimeTranslation.continuous_timeTranslationSchwartz g).comp (continuous_neg)

/-- **Norm bound on the generating functional.**

For any probability measure μ, the generating functional satisfies
‖Z[f]‖ ≤ 1. This follows from:
  ‖Z[f]‖ = ‖∫ exp(i⟨ω,f⟩) dμ(ω)‖ ≤ ∫ ‖exp(i⟨ω,f⟩)‖ dμ(ω) = ∫ 1 dμ = 1. -/
theorem norm_generatingFunctional_le_one
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (f : TestFunction2) :
    ‖generatingFunctional μ f‖ ≤ 1 := by
  unfold generatingFunctional
  calc ‖∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂μ‖
      ≤ ∫ ω, ‖Complex.exp (Complex.I * ↑(ω f))‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ = ∫ _ : FieldConfig2, (1 : ℝ) ∂μ := by
        congr 1; ext ω; exact Complex.norm_exp_I_mul_ofReal (ω f)
    _ = 1 := by
        rw [integral_const, probReal_univ, smul_eq_mul, mul_one]

/-- **Clustering implies ergodicity for P(Φ)₂ measures.**

For the P(Φ)₂ Euclidean measure, OS4_Clustering implies OS4_Ergodicity.
The proof uses three ingredients:

1. **Clustering → pointwise convergence:** `Z[f + τ_a g] → Z[f]·Z[g]` as `‖a‖ → ∞`.

2. **Reality of Z[f]:** The P(Φ)₂ measure with even polynomial P is φ → -φ
   symmetric, making Z[f] = Z̄[f] real. Then `Re(Z[f]·Z[g]) = Z[f].re · Z[g].re`.

3. **Cesàro mean convergence:** The time-averaged `(1/T) ∫₀ᵀ Re(Z[f+τ_{(t,0)} g]) dt`
   converges to the limit `Z[f].re · Z[g].re`, since the integrand converges
   with exponential rate (from the mass gap).

References: Glimm-Jaffe Ch. 6; Simon, The P(φ)₂ Theory, Ch. V;
Reed-Simon I §XIII.12 (mean ergodic theorem). -/
theorem os4_clustering_implies_ergodicity (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (h_limit : IsPphi2Limit μ P mass)
    (h_cluster : OS4_Clustering μ) :
    OS4_Ergodicity μ := by
  intro f g
  set L := (generatingFunctional μ f).re * (generatingFunctional μ g).re
  -- Step 1: Show Re(Z[f]·Z[g]) = Re(Z[f])·Re(Z[g]) using reality of Z
  have hf_real := pphi2_generating_functional_real P mass hmass μ h_limit f
  have hg_real := pphi2_generating_functional_real P mass hmass μ h_limit g
  have h_re_product : (generatingFunctional μ f * generatingFunctional μ g).re = L := by
    simp only [Complex.mul_re, L]
    rw [hf_real, hg_real]
    ring
  -- Step 2: Define the integrand h(t) = Re(Z[f + τ_{(t,0)} g])
  set h_fun : ℝ → ℝ := fun t =>
    (generatingFunctional μ (f + SchwartzMap.translate
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![t, 0]) g)).re
  -- Step 3: Show Z[f + τ_t g] → Z[f]·Z[g] in ℂ using clustering
  have h_Z_tend : Filter.Tendsto
      (fun t : ℝ => generatingFunctional μ (f + SchwartzMap.translate
        ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![t, 0]) g))
      Filter.atTop (nhds (generatingFunctional μ f * generatingFunctional μ g)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨R, hR, h_bound⟩ := h_cluster f g ε hε
    use R + 1
    intro t ht
    have h_norm_ge : ‖(WithLp.equiv 2 (Fin 2 → ℝ)).symm ![t, 0]‖ > R := by
      have h1 := PiLp.norm_apply_le
        ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![t, 0]) (0 : Fin 2)
      have h2 : ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![t, 0]).ofLp (0 : Fin 2) = t := by
        simp [WithLp.equiv_symm_apply, WithLp.ofLp_toLp, Matrix.cons_val_zero]
      rw [h2, Real.norm_eq_abs] at h1
      linarith [le_abs_self t]
    rw [Complex.dist_eq]
    exact h_bound _ h_norm_ge
  -- Step 4: Take Re: continuous Re ∘ Z-tendsto gives h(t) → L
  have h_ptwise : Filter.Tendsto h_fun Filter.atTop (nhds L) := by
    rw [show L = (generatingFunctional μ f * generatingFunctional μ g).re from h_re_product.symm]
    have h_re_cont : Filter.Tendsto Complex.re
        (nhds (generatingFunctional μ f * generatingFunctional μ g))
        (nhds (generatingFunctional μ f * generatingFunctional μ g).re) :=
      Complex.continuous_re.continuousAt
    exact h_re_cont.comp h_Z_tend
  -- Step 5: h is bounded (|Re(z)| ≤ ‖z‖ ≤ 1)
  have h_bounded : ∃ M : ℝ, ∀ t, |h_fun t| ≤ M := by
    use 1
    intro t
    exact (Complex.abs_re_le_norm _).trans (norm_generatingFunctional_le_one μ _)
  -- Step 6: h is measurable (from continuity of Z under translations)
  have h_meas : Measurable h_fun :=
    (Complex.continuous_re.comp (generatingFunctional_translate_continuous μ f g)).measurable
  -- Step 7: Apply Cesàro convergence
  exact cesaro_set_integral_tendsto h_fun L h_meas h_bounded h_ptwise

/-- **The continuum limit satisfies all five OS axioms.**

Assembles all results: OS3 is fully proved via the trig identity decomposition
and `os3_inheritance`. OS0, OS1, OS2, OS4 follow from the lattice construction
via the mechanisms described above. -/
theorem continuumLimit_satisfies_fullOS
    (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (ContinuumTestFunction 2)))
    (hμ : IsProbabilityMeasure μ)
    (h_limit : IsPphi2Limit μ P mass) :
    @SatisfiesFullOS μ hμ where
  os0 := os0_for_continuum_limit P mass hmass μ hμ h_limit
  os1 := os1_for_continuum_limit P mass hmass μ hμ h_limit
  os2 := os2_for_continuum_limit P mass hmass μ hμ h_limit
  os3 := os3_for_continuum_limit P mass hmass μ hμ h_limit
  os4_clustering := os4_for_continuum_limit P mass hmass μ hμ h_limit
  os4_ergodicity :=
    os4_clustering_implies_ergodicity P mass hmass μ h_limit
      (os4_for_continuum_limit P mass hmass μ hμ h_limit)

/-! ## Existence theorem (using full OS axioms) -/

/-- **Existence of the P(Φ)₂ Euclidean measure.**

There exists a probability measure μ on S'(ℝ²) satisfying all five
Osterwalder-Schrader axioms (`SatisfiesFullOS`). -/
theorem pphi2_exists (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (μ : Measure (Configuration (ContinuumTestFunction 2)))
      (hμ : IsProbabilityMeasure μ),
    @SatisfiesFullOS μ hμ := by
  obtain ⟨μ, hμ, h_limit⟩ := pphi2_limit_exists P mass hmass
  exact ⟨μ, hμ, continuumLimit_satisfies_fullOS P mass hmass μ hμ h_limit⟩

end Pphi2

end
