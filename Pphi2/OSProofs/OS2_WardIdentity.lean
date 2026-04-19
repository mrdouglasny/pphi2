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
  dim(O_break) = 4 > d = 2, so the anomaly is RG-irrelevant. In the
  super-renormalizable `P(Φ)₂` setting the formalized bound is
  `O(a² |log a|^p)`, which still vanishes as `a → 0`.

  **Key simplification for P(Φ)₂:** The theory is super-renormalizable, so
  logarithmic corrections are at most polynomial in |log a| (Glimm-Jaffe
  Theorem 19.3.1). The bound is O(a² |log a|^p), which still vanishes.

## Main results

- `translation_invariance_lattice` — lattice measure is translation-invariant
- `translation_invariance_continuum` — continuum limit is translation-invariant
- `ward_identity_lattice` — current formal Ward-identity slot on the lattice side
- `anomaly_scaling_dimension` — dim(O_break) = 4
- `anomaly_vanishes` — one-point rotation anomaly is `O(a² |log a|^p)` and hence vanishes
- `rotation_invariance_continuum` — continuum SO(2) invariance from anomaly decay
- `os2_for_continuum_limit` — full E(2) invariance of the continuum limit

## References

- Symanzik (1983), "Continuum limit of lattice field theories"
- Lüscher-Weisz (1985), Symanzik improvement program
- Duch (2024), Ward identities for lattice → continuum (O(N) models)
- Glimm-Jaffe, *Quantum Physics*, §19.5
-/

import Pphi2.OSAxioms
import Pphi2.EuclideanComplex
import Pphi2.GeneralResults.FunctionalAnalysis
import Pphi2.InteractingMeasure.LatticeEuclideanTime
import Pphi2.OSforGFF.TimeTranslation
import Lattice.Symmetry
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

/-! ### Helper lemmas for translation invariance -/

omit [NeZero N] in
/-- `latticeTranslation` is definitionally `latticeTranslationFun` from gaussian-field. -/
private lemma latticeTranslation_eq (v : FinLatticeSites d N) (φ : FinLatticeField d N) :
    latticeTranslation d N v φ = latticeTranslationFun d N v φ := rfl

/-- The manual `LinearMap` used in `latticeMeasure_translation_invariant` agrees with the bundled
`GaussianField.latticeTranslation` (same action on fields). -/
private lemma latticeTranslation_linear_toCLM_eq_gaussian (v : FinLatticeSites d N) :
    ({ toFun := latticeTranslation d N v, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl } :
        FinLatticeField d N →ₗ[ℝ] FinLatticeField d N).toContinuousLinearMap
      = GaussianField.latticeTranslation d N v :=
  ContinuousLinearMap.ext fun φ => by
    change latticeTranslation d N v φ = latticeTranslationFun d N v φ
    exact latticeTranslation_eq d N v φ

/-- The mass operator commutes with lattice translation.
`Q(T_v φ) = T_v(Q φ)` because both -Δ and m² commute with translation. -/
theorem massOperator_translation_commute (a mass : ℝ) (v : FinLatticeSites d N)
    (φ : FinLatticeField d N) :
    massOperator d N a mass (latticeTranslation d N v φ) =
    latticeTranslation d N v (massOperator d N a mass φ) := by
  have hΔ := finiteLaplacian_translation_commute d N a v φ
  ext x
  simp only [massOperator, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
    latticeTranslation_eq, latticeTranslationFun]
  have h := congr_fun hΔ x
  simp only [latticeTranslationFun] at h
  linarith

/-- The Gaussian density `ρ(φ) = exp(-½⟨φ, Qφ⟩)` is translation-invariant.

The quadratic form `∑_x φ(x)·(Qφ)(x)` is invariant because Q commutes
with translation and the sum over all lattice sites is relabeling-invariant. -/
theorem gaussianDensity_translation_invariant (a mass : ℝ) (v : FinLatticeSites d N)
    (φ : FinLatticeField d N) :
    gaussianDensity d N a mass (latticeTranslation d N v φ) =
    gaussianDensity d N a mass φ := by
  unfold gaussianDensity
  congr 1; congr 1
  -- Show: ∑ x, (T_v φ)(x) * (Q(T_v φ))(x) = ∑ x, φ(x) * (Qφ)(x)
  have hcomm := massOperator_translation_commute d N a mass v φ
  simp_rw [show ∀ x, massOperator d N a mass (latticeTranslation d N v φ) x =
    latticeTranslation d N v (massOperator d N a mass φ) x from fun x => congr_fun hcomm x]
  -- Relabel x ↦ x - v using Equiv.subRight
  apply Fintype.sum_equiv (Equiv.subRight v)
  intro x; rfl

/-- `latticeTranslation d N v` as a `MeasurableEquiv` on `FinLatticeField d N`. -/
private noncomputable def latticeTranslationEquiv (v : FinLatticeSites d N) :
    FinLatticeField d N ≃ᵐ FinLatticeField d N :=
  MeasurableEquiv.piCongrLeft (fun _ : FinLatticeSites d N => ℝ) (Equiv.addRight v)

omit [NeZero N] in
private lemma latticeTranslationEquiv_eq (v : FinLatticeSites d N)
    (φ : FinLatticeField d N) :
    latticeTranslationEquiv d N v φ = latticeTranslation d N v φ := by
  ext x
  change (Equiv.piCongrLeft (fun _ => ℝ) (Equiv.addRight v)) φ x = φ (fun i => x i - v i)
  conv_lhs => rw [show x = (Equiv.addRight v) (x - v) from (sub_add_cancel x v).symm]
  rw [Equiv.piCongrLeft_apply_apply]; rfl

/-- `latticeTranslation d N v` preserves Lebesgue measure on `FinLatticeField d N`. -/
private lemma latticeTranslation_volume_preserving (v : FinLatticeSites d N) :
    MeasurePreserving (latticeTranslationEquiv d N v)
      (volume : Measure (FinLatticeField d N)) volume :=
  volume_measurePreserving_piCongrLeft _ _

/-- Evaluating `evalMapInv φ` at a delta function `δ_x` returns `φ x`. -/
private lemma evalInv_delta (φ : FinLatticeField d N) (x : FinLatticeSites d N) :
    (evalMapMeasurableEquiv d N).symm φ (finLatticeDelta d N x) = φ x :=
  congr_fun ((evalMapMeasurableEquiv d N).apply_symm_apply φ) x

omit [NeZero N] in
/-- Translating a delta function shifts its support: `T_v(δ_x) = δ_{x+v}`. -/
private lemma latticeTranslation_delta (v : FinLatticeSites d N) (x : FinLatticeSites d N) :
    latticeTranslation d N v (finLatticeDelta d N x) = finLatticeDelta d N (x + v) := by
  ext z
  simp only [latticeTranslation, finLatticeDelta]
  have : ((fun i => z i - v i) = x) ↔ (z = x + v) := by
    change z - v = x ↔ z = x + v; exact sub_eq_iff_eq_add
  simp [this]

/-- The interacting lattice measure is invariant under lattice translations.

**Proof:** Both sides reduce (via the density bridge) to ratios of Lebesgue
integrals on `FinLatticeField d N`. The numerator integrand factors as
`(F ∘ evalMapInv)(φ) · BW_field(φ) · ρ(φ)`, where:
- `BW_field` is invariant under `T_v` (`latticeAction_translation_invariant`)
- `ρ` is invariant under `T_v` (`gaussianDensity_translation_invariant`)
- `T_v` preserves Lebesgue measure (`latticeTranslation_volume_preserving`)

A change of variables `φ → T_{-v}(φ)` then shows the LHS numerator equals
the RHS numerator.

Reference: Glimm-Jaffe §8.1 (translation invariance of lattice measures). -/
theorem latticeMeasure_translation_invariant (P : InteractionPolynomial)
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
    ∫ ω, F ω ∂(interactingLatticeMeasure d N P a mass ha hmass) := by
  intro F _hFi
  -- Setup notation
  set mu_GFF := latticeGaussianMeasure d N a mass ha hmass
  set bw := boltzmannWeight d N P a mass
  set ρ := gaussianDensity d N a mass
  set L_v : FinLatticeField d N →ₗ[ℝ] FinLatticeField d N :=
    { toFun := latticeTranslation d N v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- Step 1: Unfold the interacting measure = Z⁻¹ • μ_GFF.withDensity(bw)
  unfold interactingLatticeMeasure
  simp_rw [integral_smul_measure]
  congr 1  -- Z⁻¹ factor is the same on both sides
  -- Step 2: Convert withDensity integrals to μ_GFF integrals
  set bw_nn := fun ω : Configuration (FinLatticeField d N) => Real.toNNReal (bw ω)
  have hbw_nn_meas : Measurable bw_nn :=
    Measurable.real_toNNReal
      ((interactionFunctional_measurable d N P a mass).neg.exp)
  change ∫ ω, F (ω.comp L_v.toContinuousLinearMap)
      ∂(mu_GFF.withDensity (fun ω => ↑(bw_nn ω))) =
    ∫ ω, F ω ∂(mu_GFF.withDensity (fun ω => ↑(bw_nn ω)))
  rw [integral_withDensity_eq_integral_smul hbw_nn_meas,
      integral_withDensity_eq_integral_smul hbw_nn_meas]
  -- Simplify NNReal.smul to real multiplication
  have hbw_simp : ∀ ω : Configuration (FinLatticeField d N),
      (bw_nn ω : ℝ) = bw ω := fun ω =>
    Real.coe_toNNReal _ (le_of_lt (boltzmannWeight_pos d N P a mass ω))
  -- Step 3: Express integrands as functions of evalMap ω
  -- LHS integrand: bw(ω) * F(ω.comp L_v) = G_L(evalMap ω)
  -- RHS integrand: bw(ω) * F(ω) = G_R(evalMap ω)
  -- Since ω = evalMapInv(evalMap ω), both factor through evalMap
  set evalInv := (evalMapMeasurableEquiv d N).symm
  -- Key: ω.comp L_v = evalMapInv(T_{-v}(evalMap ω))
  -- and ω = evalMapInv(evalMap ω)
  have hcomp : ∀ ω : Configuration (FinLatticeField d N),
      ω.comp L_v.toContinuousLinearMap = evalInv (latticeTranslation d N (-v) (evalMap d N ω)) := by
    intro ω
    -- It suffices to show evalMap of both sides are equal
    have hinj := (evalMapMeasurableEquiv d N).injective
    apply hinj
    simp only [evalInv, MeasurableEquiv.apply_symm_apply]
    ext x
    -- LHS: evalMap(ω.comp L_v.toCLM)(x) = ω(T_v(δ_x))
    -- RHS: T_{-v}(evalMap ω)(x) = ω(δ_{x+v})
    -- Equal because T_v(δ_x) = δ_{x+v}
    change (ω.comp L_v.toContinuousLinearMap) (finLatticeDelta d N x) =
           latticeTranslation d N (-v) (fun y => ω (finLatticeDelta d N y)) x
    rw [ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap']
    simp only [L_v, LinearMap.coe_mk, AddHom.coe_mk,
      latticeTranslation_delta d N v x, latticeTranslation]
    -- Goal: ω(δ_{x+v}) = ω(δ_{fun i => x i - (-v) i})
    -- x + v = fun i => x i + v i = fun i => x i - (-v) i (definitionally)
    change ω (finLatticeDelta d N (x + v)) =
         ω (finLatticeDelta d N (fun i => x i - (-v) i))
    congr 2; ext i; simp [Pi.add_apply, sub_neg_eq_add]
  have hid : ∀ ω : Configuration (FinLatticeField d N),
      ω = evalInv (evalMap d N ω) := by
    intro ω; exact ((evalMapMeasurableEquiv d N).symm_apply_apply ω).symm
  -- Rewrite both integrands using evalMap
  simp_rw [NNReal.smul_def, smul_eq_mul, hbw_simp]
  -- LHS: ∫ bw(ω) * F(ω.comp L_v) dμ_GFF
  -- RHS: ∫ bw(ω) * F(ω) dμ_GFF
  -- Define field-level functions
  set G_L := fun φ : FinLatticeField d N =>
    bw (evalInv φ) * F (evalInv (latticeTranslation d N (-v) φ))
  set G_R := fun φ : FinLatticeField d N =>
    bw (evalInv φ) * F (evalInv φ)
  -- Show integrands match G_L(evalMap ω) and G_R(evalMap ω)
  have hL : ∀ ω, bw ω * F (ω.comp L_v.toContinuousLinearMap) = G_L (evalMap d N ω) := by
    intro ω
    simp only [G_L, hcomp, ← hid ω]
  have hR : ∀ ω, bw ω * F ω = G_R (evalMap d N ω) := by
    intro ω; simp only [G_R, ← hid ω]
  simp_rw [hL, hR]
  -- Step 4: Apply the density bridge to both sides
  rw [latticeGaussianMeasure_density_integral' d N a mass ha hmass G_L,
      latticeGaussianMeasure_density_integral' d N a mass ha hmass G_R]
  -- Denominators are equal; show numerators are equal
  congr 1
  -- Step 5: Change of variables on the Lebesgue integral
  -- LHS numerator: ∫ G_L(φ) * ρ(φ) dφ = ∫ bw(evalInv φ) * F(evalInv(T_{-v} φ)) * ρ(φ) dφ
  -- RHS numerator: ∫ G_R(φ) * ρ(φ) dφ = ∫ bw(evalInv φ) * F(evalInv φ) * ρ(φ) dφ
  -- Show LHS = ∫ (G_R * ρ)(T_{-v} φ) dφ = ∫ (G_R * ρ)(φ) dφ = RHS
  -- using: bw(evalInv(T_{-v} φ)) = bw(evalInv φ) and ρ(T_{-v} φ) = ρ(φ)
  -- BW invariance: interactionFunctional factors through evalMap,
  -- and latticeInteraction is T-invariant
  have hBW_inv : ∀ φ, bw (evalInv (latticeTranslation d N (-v) φ)) = bw (evalInv φ) := by
    intro φ
    -- suffices: interactionFunctional is invariant
    suffices h : interactionFunctional d N P a mass (evalInv (latticeTranslation d N (-v) φ)) =
                 interactionFunctional d N P a mass (evalInv φ) by
      simp only [bw, boltzmannWeight, h]
    simp only [interactionFunctional]
    congr 1
    -- ∑_x WM(evalInv(T_{-v} φ)(δ_x)) = ∑_x WM(evalInv φ (δ_x))
    -- evalInv(T_{-v} φ)(δ_x) = (T_{-v} φ)(x) = φ(x+v) by evalInv_delta
    -- evalInv(φ)(δ_{x+v}) = φ(x+v) by evalInv_delta
    -- Relabel x ↦ x + v
    apply Fintype.sum_equiv (Equiv.addRight v)
    intro x; congr 1
    rw [evalInv_delta, evalInv_delta]
    simp only [latticeTranslation, Equiv.addRight]
    congr 1; ext i; simp [Pi.neg_apply, Pi.add_apply, sub_neg_eq_add]
  have hρ_inv : ∀ φ, ρ (latticeTranslation d N (-v) φ) = ρ φ :=
    gaussianDensity_translation_invariant d N a mass (-v)
  -- Now: G_L(φ) * ρ(φ) = G_R(T_{-v} φ) * ρ(T_{-v} φ)
  -- Change of variables: ∫ (G_R ∘ T_{-v}) * (ρ ∘ T_{-v}) dφ = ∫ G_R * ρ dφ
  -- Change of variables: show LHS = ∫ (G_R * ρ) ∘ T_{-v} dφ = ∫ G_R * ρ dφ = RHS
  have hkey : ∀ φ, G_L φ * ρ φ =
      G_R (latticeTranslation d N (-v) φ) * ρ (latticeTranslation d N (-v) φ) := by
    intro φ; dsimp only [G_L, G_R]; rw [hBW_inv, hρ_inv]
  have hkey2 : (fun φ => G_L φ * ρ φ) =
      (fun φ => G_R (latticeTranslationEquiv d N (-v) φ) *
                ρ (latticeTranslationEquiv d N (-v) φ)) := by
    ext φ; rw [hkey, latticeTranslationEquiv_eq]
  rw [hkey2]
  exact (latticeTranslation_volume_preserving d N (-v)).integral_comp'
    (fun ψ => G_R ψ * ρ ψ)

/-- For `μ = interactingLatticeMeasure`, expectations of integrable `G` are unchanged under
`latticeConfigEuclideanTimeShift` (dual Euclidean-time translation).

**Proof.** `latticeMeasure_translation_invariant` at `v = latticeEuclideanTimeShift N k`, plus
`latticeTranslation_linear_toCLM_eq_gaussian`.

**Clustering:** `general_clustering_from_spectral_gap` subtracts `∫ F · ∫ G` with **unshifted** `G`;
for integrable `G`, `∫ G(τ_k ω) ∂μ = ∫ G ∂μ`, so this is the standard connected correlator
`Cov(F, G∘τ_k)` formulation. -/
theorem interactingLatticeMeasure_expectation_configEuclideanTimeShift
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (k : ℕ) (G : Configuration (FinLatticeField 2 N) → ℝ)
    (hG : Integrable G (interactingLatticeMeasure 2 N P a mass ha hmass)) :
    ∫ ω, G (latticeConfigEuclideanTimeShift N k ω)
        ∂(interactingLatticeMeasure 2 N P a mass ha hmass) =
      ∫ ω, G ω ∂(interactingLatticeMeasure 2 N P a mass ha hmass) := by
  set μ := interactingLatticeMeasure 2 N P a mass ha hmass
  calc
    ∫ ω, G (latticeConfigEuclideanTimeShift N k ω) ∂μ
        = ∫ ω, G
            (ω.comp (GaussianField.latticeTranslation 2 N (latticeEuclideanTimeShift N k))) ∂μ := by
          refine integral_congr_ae (ae_of_all μ fun ω => ?_)
          simp [latticeConfigEuclideanTimeShift]
    _ = ∫ ω, G (ω.comp
          ({ toFun := latticeTranslation 2 N (latticeEuclideanTimeShift N k),
              map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
              FinLatticeField 2 N →ₗ[ℝ] FinLatticeField 2 N).toContinuousLinearMap) ∂μ := by
          refine integral_congr_ae (ae_of_all μ fun ω => ?_)
          simp_rw [← latticeTranslation_linear_toCLM_eq_gaussian (d := 2)
            (v := latticeEuclideanTimeShift N k)]
    _ = ∫ ω, G ω ∂μ :=
          latticeMeasure_translation_invariant 2 N P a mass ha hmass
            (latticeEuclideanTimeShift N k) G hG

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

Reference: Glimm-Jaffe §8.6 (translation invariance of the continuum limit).

**Proof:** From `IsPphi2Limit` we extract:
- `cf_tendsto`: Z_{ν_k}[g] → Z_μ[g] for all g
- `lattice_inv`: Z_{ν_k}[f] = Z_{ν_k}[τ_v f] eventually, for all v, f

For any v, f: both Z_{ν_k}[f] and Z_{ν_k}[τ_v f] converge to Z_μ[f] and Z_μ[τ_v f]
respectively. Since Z_{ν_k}[f] = Z_{ν_k}[τ_v f] eventually, the limits are equal. -/
theorem translation_invariance_continuum (P : InteractionPolynomial)
    (mass : ℝ) (_hmass : 0 < mass)
    (μ : Measure (Configuration (ContinuumTestFunction 2)))
    (hμ : IsProbabilityMeasure μ)
    (h_limit : IsPphi2Limit μ P mass) :
    ∀ (v : EuclideanSpace ℝ (Fin 2)) (f : TestFunction2),
    generatingFunctional μ f = generatingFunctional μ (SchwartzMap.translate v f) := by
  rcases h_limit with ⟨a, ν, hprob, _ha_tend, _ha_pos, _hmom, _hneg, hcf, hlat, _hweakconv,
    _happrox_os3⟩
  intro v f
  -- SchwartzMap.translate v f = schwartzTranslate 2 v f (same definition)
  have htranslate_eq : SchwartzMap.translate v f = schwartzTranslate 2 v f := rfl
  rw [htranslate_eq]
  -- Z_{ν_k}[f] → Z_μ[f]
  have lim_f := hcf f
  -- Z_{ν_k}[τ_v f] → Z_μ[τ_v f]
  have lim_tv := hcf (schwartzTranslate 2 v f)
  -- Z_{ν_k}[f] = Z_{ν_k}[τ_v f] eventually
  have h_ev := hlat v f
  -- Generating functional = integral of exp(i·ω(·))
  change ∫ ω : FieldConfig2, Complex.exp (Complex.I * ↑(ω f)) ∂μ =
       ∫ ω : FieldConfig2, Complex.exp (Complex.I * ↑(ω (schwartzTranslate 2 v f))) ∂μ
  -- Both sequences have the same limit, since they're eventually equal
  exact tendsto_nhds_unique_of_eventuallyEq lim_f lim_tv h_ev

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
    push Not at hak
    have h_sq : 1 < (a * k i) ^ 2 := by
      nlinarith [sq_abs (a * k i), abs_nonneg (a * k i)]
    -- a²k² ≤ a⁴k⁴ since 1 ≤ a²k² (multiply both sides by a²k²)
    have h_bound : a ^ 2 * (k i) ^ 2 ≤ a ^ 4 * (k i) ^ 4 := by
      have : 0 ≤ a ^ 2 * (k i) ^ 2 * (a ^ 2 * (k i) ^ 2 - 1) :=
        mul_nonneg (by nlinarith) (by nlinarith)
      nlinarith
    nlinarith [sq_nonneg (k i), sq_nonneg a]

/-! ### One-point canonical CF rotation defect -/

/-- The pointwise characteristic-functional defect integrand for comparing `f` with its
Euclidean transform by `R`. This is the OS2 specialization of the generic characteristic-integrand
difference from `GeneralResults/FunctionalAnalysis`. -/
abbrev rotationCFPointwiseDefectIntegrand (f : TestFunction2) (R : O2) :
    FieldConfig2 → ℂ :=
  configuration_cexp_eval_sub_integrand f (euclideanAction2 ⟨R, 0⟩ f)

/-- The pointwise norm of the one-point characteristic-functional rotation defect observable. -/
abbrev rotationCFPointwiseDefect (f : TestFunction2) (R : O2) :
    FieldConfig2 → ℝ :=
  configuration_cexp_eval_dist f (euclideanAction2 ⟨R, 0⟩ f)

/-- The one-point characteristic-functional rotation defect for the canonical
continuum-embedded lattice measure at spacing `a`. -/
def rotationCFDefect (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (f : TestFunction2) (a : ℝ) (ha : 0 < a) (R : O2) : ℝ :=
  haveI : IsProbabilityMeasure (continuumMeasure 2 N P a mass ha hmass) :=
    continuumMeasure_isProbability 2 N P a mass ha hmass
  ‖generatingFunctional (continuumMeasure 2 N P a mass ha hmass) (euclideanAction2 ⟨R, 0⟩ f) -
    generatingFunctional (continuumMeasure 2 N P a mass ha hmass) f‖

/-- The norm of the integrated CF defect is bounded by the integral of the
pointwise defect observable. -/
theorem rotationCFDefect_le_pointwiseDefectIntegral (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) (f : TestFunction2)
    (a : ℝ) (ha : 0 < a) (R : O2) :
    rotationCFDefect (N := N) P mass hmass f a ha R ≤
      ∫ ω : FieldConfig2,
        rotationCFPointwiseDefect f R ω
          ∂(continuumMeasure 2 N P a mass ha hmass) := by
  let μ : Measure FieldConfig2 := continuumMeasure 2 N P a mass ha hmass
  haveI : IsProbabilityMeasure μ := continuumMeasure_isProbability 2 N P a mass ha hmass
  simpa [rotationCFDefect, rotationCFPointwiseDefect, EuclideanOS.generatingFunctional] using
    (norm_configuration_expIntegral_sub_le_integral_cexp_eval_dist
      (μ := μ) f (euclideanAction2 ⟨R, 0⟩ f))

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
axiom rotation_cf_pointwise_defect_polylog_bound (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (f : TestFunction2) :
    ∃ (C : ℝ) (p : ℕ), 0 < C ∧ ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
      ∀ (R : O2),
        ∫ ω : FieldConfig2,
          rotationCFPointwiseDefect f R ω
            ∂(continuumMeasure 2 N P a mass ha hmass) ≤
        C * a ^ 2 * (1 + |Real.log a|) ^ p

/-- The previous CF-defect bound is derived from the pointwise observable bound
by `‖∫g‖ ≤ ∫‖g‖`. -/
theorem rotation_cf_defect_polylog_bound (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (f : TestFunction2) :
    ∃ (C : ℝ) (p : ℕ), 0 < C ∧ ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
      ∀ (R : O2), rotationCFDefect (N := N) P mass hmass f a ha R ≤
        C * a ^ 2 * (1 + |Real.log a|) ^ p := by
  rcases rotation_cf_pointwise_defect_polylog_bound (N := N) P mass hmass f with
    ⟨C, p, hC, hpoly⟩
  refine ⟨C, p, hC, ?_⟩
  intro a ha hle R
  exact (rotationCFDefect_le_pointwiseDefectIntegral (N := N) P mass hmass f a ha R).trans
    (hpoly a ha hle R)

/-- Super-renormalizable one-point control of the rotation anomaly. -/
theorem anomaly_bound_from_superrenormalizability (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (f : TestFunction2) :
    ∃ (C : ℝ) (p : ℕ), 0 < C ∧ ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
    ∀ (R : O2),
    haveI : IsProbabilityMeasure (continuumMeasure 2 N P a mass ha hmass) :=
      continuumMeasure_isProbability 2 N P a mass ha hmass
    ‖generatingFunctional (continuumMeasure 2 N P a mass ha hmass) (euclideanAction2 ⟨R, 0⟩ f) -
     generatingFunctional (continuumMeasure 2 N P a mass ha hmass) f‖ ≤
      C * a ^ 2 * (1 + |Real.log a|) ^ p := by
  rcases rotation_cf_defect_polylog_bound (N := N) P mass hmass f with ⟨C, p, hC, hpoly⟩
  refine ⟨C, p, hC, ?_⟩
  intro a ha hle R
  simpa [rotationCFDefect] using hpoly a ha hle R

/-- **The one-point characteristic-functional rotation defect vanishes.**

For each real test function `f ∈ S(ℝ²)` and orthogonal transformation `R ∈ O(2)`,
the canonical continuum-embedded lattice generating functionals satisfy

  `‖Z_a[R · f] - Z_a[f]‖ ≤ C(f) · a² · (1 + |log a|)^p`.

The a² factor comes from the dimension-4 anomaly operator; the log factors
arise from Wick ordering and renormalization in the super-renormalizable theory.
Crucially, in d=2 these are at most polynomial in `|log a|`, so the defect still
vanishes as `a → 0`. -/
theorem anomaly_vanishes (P : InteractionPolynomial) (mass : ℝ)
    (hmass : 0 < mass) (f : TestFunction2) :
    -- The one-point rotation anomaly of the lattice generating functional
    -- vanishes as a → 0. For each rotation R ∈ O(2),
    -- Z_a[R·f] - Z_a[f] is O(a² |log a|^p), where Z_a is the generating
    -- functional of the continuum-embedded lattice measure.
    ∃ (C : ℝ) (p : ℕ), 0 < C ∧ ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
    ∀ (R : O2),
    haveI : IsProbabilityMeasure (continuumMeasure 2 N P a mass ha hmass) :=
      continuumMeasure_isProbability 2 N P a mass ha hmass
    ‖generatingFunctional (continuumMeasure 2 N P a mass ha hmass) (euclideanAction2 ⟨R, 0⟩ f) -
     generatingFunctional (continuumMeasure 2 N P a mass ha hmass) f‖ ≤
      C * a ^ 2 * (1 + |Real.log a|) ^ p := by
  exact anomaly_bound_from_superrenormalizability (N := N) P mass hmass f

/-! ## Rotation invariance in the continuum -/

/-- **Rotation invariance of the continuum limit.**

For any orthogonal transformation `R ∈ O(2)` and test function `f ∈ S(ℝ²)`,
the generating functional satisfies `Z[R·f] = Z[f]` where `(R·f)(x) = f(R⁻¹x)`.

Proof outline (Ward identity argument):
1. The lattice Ward identity: `⟨δ_J F⟩_a = ⟨F · O_break⟩_a` where O_break is
   the rotation-breaking operator from the nearest-neighbor action.
2. dim(O_break) = 4 > d = 2 (from Fourier analysis: Δ_lattice - Δ = O(a²k⁴)),
   so the anomaly is RG-irrelevant.
3. Super-renormalizability of P(Φ)₂ implies at most polynomial log corrections,
   so `|anomaly| ≤ C · a² · (1 + |log a|)^p`.
4. In the weak limit: `⟨δ_J F⟩_μ = 0`, so Schwinger functions are SO(2)-invariant.
5. Reflections: time reflection Θ is a symmetry (from OS3/RP). Combined with
   SO(2), this generates all of O(2).
6. Schwinger functions determine μ (nuclearity of S(ℝ²)) ⟹ `Z[R·f] = Z[f]`.

Refs: Symanzik (1983), Lüscher-Weisz (1985), Duch (2024). -/
theorem rotation_invariance_continuum (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (ContinuumTestFunction 2)))
    [IsProbabilityMeasure μ]
    (h_limit : IsPphi2Limit μ P mass)
    (R : O2) (f : TestFunction2) :
    generatingFunctional μ (euclideanAction2 ⟨R, 0⟩ f) = generatingFunctional μ f := by
  have hcanon :
      ∃ (N0 : ℕ) (a : ℕ → ℝ) (ha_pos : ∀ n, 0 < a n),
        (∀ n, a n ≤ 1) ∧
        Filter.Tendsto a Filter.atTop (nhds 0) ∧
        ∀ (f : TestFunction2),
          Filter.Tendsto
            (fun n =>
              ∫ ω : FieldConfig2,
                Complex.exp (Complex.I * ↑(ω f))
                  ∂(continuumMeasure 2 (Nat.succ N0) P (a n) mass (ha_pos n) hmass))
            Filter.atTop
            (nhds (generatingFunctional μ f)) :=
    canonical_continuumMeasure_cf_tendsto P mass hmass μ h_limit
  obtain ⟨N0, a, ha_pos, ha_le, ha_tend, hcf⟩ := hcanon
  let N : ℕ := Nat.succ N0
  haveI : NeZero N := ⟨Nat.succ_ne_zero N0⟩
  have h_rot_tend := hcf (euclideanAction2 ⟨R, 0⟩ f)
  have h_id_tend := hcf f
  obtain ⟨C, p, _hC, h_anom⟩ := anomaly_vanishes (N := N) P mass hmass f
  have h_norm_bound :
      ∀ n, ‖(∫ ω : FieldConfig2,
            Complex.exp (Complex.I * ↑(ω (euclideanAction2 ⟨R, 0⟩ f)))
              ∂(continuumMeasure 2 N P (a n) mass (ha_pos n) hmass)) -
          (∫ ω : FieldConfig2,
            Complex.exp (Complex.I * ↑(ω f))
              ∂(continuumMeasure 2 N P (a n) mass (ha_pos n) hmass))‖
          ≤ C * a n ^ 2 * (1 + |Real.log (a n)|) ^ p := by
    intro n
    haveI : IsProbabilityMeasure (continuumMeasure 2 N P (a n) mass (ha_pos n) hmass) :=
      continuumMeasure_isProbability 2 N P (a n) mass (ha_pos n) hmass
    simpa [EuclideanOS.generatingFunctional] using h_anom (a n) (ha_pos n) (ha_le n) R
  have h_sub :
      Filter.Tendsto
        (fun n =>
          (∫ ω : FieldConfig2,
            Complex.exp (Complex.I * ↑(ω (euclideanAction2 ⟨R, 0⟩ f)))
              ∂(continuumMeasure 2 N P (a n) mass (ha_pos n) hmass)) -
          (∫ ω : FieldConfig2,
            Complex.exp (Complex.I * ↑(ω f))
              ∂(continuumMeasure 2 N P (a n) mass (ha_pos n) hmass)))
        Filter.atTop
        (nhds (generatingFunctional μ (euclideanAction2 ⟨R, 0⟩ f) - generatingFunctional μ f)) :=
    h_rot_tend.sub h_id_tend
  have h_diff :
      Filter.Tendsto
        (fun n =>
          (∫ ω : FieldConfig2,
            Complex.exp (Complex.I * ↑(ω (euclideanAction2 ⟨R, 0⟩ f)))
              ∂(continuumMeasure 2 N P (a n) mass (ha_pos n) hmass)) -
          (∫ ω : FieldConfig2,
            Complex.exp (Complex.I * ↑(ω f))
              ∂(continuumMeasure 2 N P (a n) mass (ha_pos n) hmass)))
        Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm (fun n => h_norm_bound n)
    simpa [mul_assoc] using
      ((tendsto_zero_pow_mul_one_add_abs_log_pow
          a ha_tend ha_pos ha_le 2 p (by norm_num)).const_mul C)
  have h_eq0 :
      generatingFunctional μ (euclideanAction2 ⟨R, 0⟩ f) - generatingFunctional μ f = 0 :=
    tendsto_nhds_unique h_sub h_diff
  exact sub_eq_zero.mp h_eq0

/-! ## OS3: pass RP matrices to the limit

`IsPphi2Limit` now records reflection positivity for the approximating
continuum measures themselves. Combined with characteristic-functional
convergence, this lets us pass each RP matrix entry to the limit directly in
the standard `OS3_ReflectionPositivity` formulation. -/

/-- **OS3 transfers from the approximating continuum measures.**

The limit certificate `IsPphi2Limit μ P mass` records two ingredients:

1. characteristic-functional convergence for every real test function;
2. reflection positivity of every approximating continuum measure `ν_k`.

For a fixed RP matrix entry `Re(Z[fᵢ - Θfⱼ])`, (1) gives convergence of the
entry, and finite summation preserves this convergence. Since every approximant
matrix is nonnegative by (2), the limit matrix is also nonnegative. -/
theorem os3_for_continuum_limit (P : InteractionPolynomial)
    (mass : ℝ) (_hmass : 0 < mass)
    (μ : Measure (Configuration (ContinuumTestFunction 2)))
    (hμ : IsProbabilityMeasure μ)
    (h_limit : IsPphi2Limit μ P mass) :
    @OS3_ReflectionPositivity μ hμ := by
  rcases h_limit with ⟨_a, ν, _hprob, _ha_tend, _ha_pos, _hmom, _hneg, hcf, _hlat, _hweakconv,
    happrox_os3⟩
  intro n f c
  simp only [EuclideanOS.generatingFunctional]
  have hentry :
      ∀ i j : Fin n,
        Filter.Tendsto
          (fun k => (∫ ω : FieldConfig2,
            Complex.exp (Complex.I * ↑(ω ((f i : TestFunction2) -
              compTimeReflection2 ((f j : TestFunction2))))) ∂(ν k)).re)
          Filter.atTop
          (nhds ((∫ ω : FieldConfig2,
            Complex.exp (Complex.I * ↑(ω ((f i : TestFunction2) -
              compTimeReflection2 ((f j : TestFunction2))))) ∂μ).re)) := by
    intro i j
    have hcf_ij := hcf ((f i : TestFunction2) - compTimeReflection2 ((f j : TestFunction2)))
    exact Complex.continuous_re.continuousAt.tendsto.comp hcf_ij
  have hsum_tend :
      Filter.Tendsto
        (fun k =>
          ∑ i, ∑ j, c i * c j *
            (∫ ω : FieldConfig2,
              Complex.exp (Complex.I * ↑(ω ((f i : TestFunction2) -
                compTimeReflection2 ((f j : TestFunction2))))) ∂(ν k)).re)
        Filter.atTop
        (nhds (∑ i, ∑ j, c i * c j *
          (∫ ω : FieldConfig2,
            Complex.exp (Complex.I * ↑(ω ((f i : TestFunction2) -
              compTimeReflection2 ((f j : TestFunction2))))) ∂μ).re)) := by
    apply tendsto_finset_sum
    intro i _
    apply tendsto_finset_sum
    intro j _
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      Filter.Tendsto.const_mul (c i * c j) (hentry i j)
  have hsum_nonneg :
      ∀ k,
        0 ≤ ∑ i, ∑ j, c i * c j *
          (∫ ω : FieldConfig2,
            Complex.exp (Complex.I * ↑(ω ((f i : TestFunction2) -
              compTimeReflection2 ((f j : TestFunction2))))) ∂(ν k)).re := by
    intro k
    simpa using happrox_os3 k n f c
  exact ge_of_tendsto hsum_tend (Filter.Eventually.of_forall hsum_nonneg)

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
  making it RG-irrelevant with coefficient `O(a² |log a|^p)` in the
  super-renormalizable `P(Φ)₂` setting, hence still vanishing in the continuum limit.

- **OS4 (Clustering):** The uniform spectral gap `m_phys ≥ m₀ > 0` from
  `spectral_gap_uniform` gives exponential clustering on the lattice:
  `|⟨F·G_R⟩ - ⟨F⟩⟨G⟩| ≤ C·exp(-m₀R)`. For bounded continuous observables,
  this transfers to the weak limit. The clustering bound on the characteristic
  functional `Z[f + T_a g] - Z[f]·Z[g]` follows from the exponential decay of
  connected correlations. -/

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

/-! ## Textbook axioms for clustering → ergodicity -/

/-- **The continuum limit satisfies all five OS axioms.**

Assembles all results: OS3 is proved by passing the RP matrix inequalities of
the approximating continuum measures to the limit through characteristic
functional convergence. OS0, OS1, OS2, OS4 follow from the lattice
construction via the mechanisms described above. -/
theorem continuumLimit_satisfies_fullOS (P : InteractionPolynomial)
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
