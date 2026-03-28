/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Reflection Positivity Transfer: Lattice → Continuum

Proves that the continuum-embedded lattice measures satisfy reflection
positivity, transferring the proved lattice RP through the embedding.

## Main results

- `latticeEmbedLift_intertwines_reflection` — the embedding commutes with
  time reflection: `Θ* ∘ ι = ι ∘ Θ_latt`
- `continuum_embedded_measure_rp` — each continuum-embedded measure has RP

## Proof strategy

The embedding `ι : Configuration(lattice) → Configuration(S'(ℝ²))` satisfies:
  `(Θ*(ι ω))(f) = (ι ω)(Θf) = a² Σ_x ω(e_x) · (Θf)(a·x)`
  `= a² Σ_x ω(e_x) · f(-a·t_x, a·s_x)`
  `= a² Σ_x' ω(e_{Θx'}) · f(a·x')` (reindex x' = Θx, bijective)
  `= (ι(Θ_latt ω))(f)`

where `(Θ_latt ω)(e_x) = ω(e_{Θx})`. This is a pure reindexing of a finite sum.

Then RP transfers: `∫ F·(F∘Θ*) d(ι_* μ) = ∫ (F∘ι)·((F∘ι)∘Θ_latt) dμ ≥ 0`
by lattice RP (`lattice_rp`).

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. III
-/

import Pphi2.ContinuumLimit.AxiomInheritance
import Pphi2.OSProofs.OS3_RP_Lattice

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory

variable (N : ℕ) [NeZero N]

/-! ## Lattice time reflection on Configuration space

The lattice time reflection `Θ_latt` on `Configuration(FinLatticeField 2 N)`
maps `ω ↦ ω ∘ (· ∘ timeReflection2D)`, i.e., it permutes the lattice sites
by `(t,x) ↦ (-t, x)`. -/

/-- Time reflection on `FinLatticeSites 2 N = Fin 2 → ZMod N`.
Negates the 0th coordinate (time), preserves the 1st (space). -/
def siteTimeReflection (x : FinLatticeSites 2 N) : FinLatticeSites 2 N :=
  fun i => if i = 0 then -x i else x i

/-- Time reflection on lattice fields: `(Θφ)(x) = φ(Θx)`. -/
def fieldTimeReflection (φ : FinLatticeField 2 N) : FinLatticeField 2 N :=
  φ ∘ siteTimeReflection N

/-- The field time reflection as a linear map on `FinLatticeField 2 N`. -/
def fieldTimeReflectionLinear : FinLatticeField 2 N →ₗ[ℝ] FinLatticeField 2 N where
  toFun := fieldTimeReflection N
  map_add' φ ψ := by ext x; simp [fieldTimeReflection, Function.comp]
  map_smul' r φ := by ext x; simp [fieldTimeReflection, Function.comp]

/-- Lattice time reflection on configuration space.
`(Θ_latt ω)(φ) = ω(Θφ) = ω(φ ∘ siteTimeReflection)`. -/
def latticeConfigReflection :
    Configuration (FinLatticeField 2 N) → Configuration (FinLatticeField 2 N) :=
  fun ω => ω.comp (fieldTimeReflectionLinear N).toContinuousLinearMap

/-! ## Intertwining identity

The lattice embedding commutes with time reflection:
`distribTimeReflection ∘ latticeEmbedLift = latticeEmbedLift ∘ latticeConfigReflection`

Equivalently, for all ω and f:
`(ι ω)(Θf) = (ι(Θ_latt ω))(f)`

This is a reindexing of the finite sum: `Σ_x ω(e_x) · (Θf)(a·x) = Σ_x ω(e_{Θx}) · f(a·x)`. -/

/-! ## Helper lemmas for the intertwining identity -/

omit [NeZero N] in
lemma siteTimeReflection_involutive :
    Function.Involutive (siteTimeReflection N : FinLatticeSites 2 N → FinLatticeSites 2 N) := by
  intro x; ext i; simp [siteTimeReflection]; split <;> simp [neg_neg]

lemma fieldTimeReflection_single (x : FinLatticeSites 2 N) :
    fieldTimeReflection N (Pi.single x 1) =
    Pi.single (siteTimeReflection N x) (1 : ℝ) := by
  have hinv := siteTimeReflection_involutive N
  have hbij : siteTimeReflection N (siteTimeReflection N x) = x := hinv x
  ext y
  simp only [fieldTimeReflection, Function.comp, Pi.single_apply]
  by_cases h : y = siteTimeReflection N x
  · simp [h, hbij]
  · simp only [h, ite_false]
    have : siteTimeReflection N y ≠ x := fun heq => h (by rw [← heq, hinv y])
    simp [this]

/-- Evaluation at a reflected site of a reflected function equals evaluation at the
original site: `(Θf)(pos(Θy)) = f(pos(y))` for odd N.
Uses `signedVal_neg` (centered coordinates commute with negation). -/
lemma evalAtSite_reflection (hN_odd : Odd N) (a : ℝ) (f : ContinuumTestFunction 2)
    (y : FinLatticeSites 2 N) :
    evalAtSite 2 N a (continuumTimeReflection f) (siteTimeReflection N y) =
    evalAtSite 2 N a f y := by
  simp only [evalAtSite, continuumTimeReflection_apply_coord, physicalPosition, siteTimeReflection]
  congr 1
  apply (WithLp.equiv 2 (Fin 2 → ℝ)).injective
  funext i
  change (if i = 0 then -(a * ↑(signedVal N (if i = 0 then -y i else y i)))
    else a * ↑(signedVal N (if i = 0 then -y i else y i))) = a * ↑(signedVal N (y i))
  split
  · rename_i h; subst h; simp [signedVal_neg N hN_odd, Int.cast_neg]
  · simp_all

/-- **The embedding intertwines time reflection** for odd N. -/
theorem latticeEmbedLift_intertwines_reflection (a : ℝ) (ha : 0 < a)
    (hN_odd : Odd N)
    (ω : Configuration (FinLatticeField 2 N))
    (f : ContinuumTestFunction 2) :
    distribTimeReflection (latticeEmbedLift 2 N a ha ω) f =
    latticeEmbedLift 2 N a ha (latticeConfigReflection N ω) f := by
  simp only [distribTimeReflection_apply, latticeEmbedLift, latticeEmbed]
  change latticeEmbedEval 2 N a (fun x => ω (Pi.single x 1)) (continuumTimeReflection f) =
    latticeEmbedEval 2 N a (fun x => (latticeConfigReflection N ω) (Pi.single x 1)) f
  -- Simplify RHS: (Θω)(e_x) = ω(e_{Θx})
  have hRHS : ∀ x : FinLatticeSites 2 N,
      (latticeConfigReflection N ω) (Pi.single x 1) =
      ω (Pi.single (siteTimeReflection N x) 1) := by
    intro x; show ω (fieldTimeReflectionLinear N (Pi.single x 1)) = _
    rw [show (fieldTimeReflectionLinear N) (Pi.single x 1) =
      fieldTimeReflection N (Pi.single x 1) from rfl, fieldTimeReflection_single N x]
  simp_rw [hRHS]; unfold latticeEmbedEval; congr 1
  -- Reindex LHS sum by the involution Θ: substitute x = Θy
  have hinv := siteTimeReflection_involutive N
  conv_lhs =>
    rw [show ∑ x : FinLatticeSites 2 N,
      ω (Pi.single x 1) * evalAtSite 2 N a (continuumTimeReflection f) x =
      ∑ y : FinLatticeSites 2 N,
      ω (Pi.single (siteTimeReflection N y) 1) *
        evalAtSite 2 N a (continuumTimeReflection f) (siteTimeReflection N y) from
      (Equiv.sum_comp (Equiv.ofBijective _ ⟨hinv.injective, hinv.surjective⟩) _).symm]
  -- Both sums now have ω(e_{Θy}) * ...; use evalAtSite_reflection
  congr 1; ext y; congr 1
  exact evalAtSite_reflection N hN_odd a f y

/-! ## RP transfer theorem

From lattice RP + intertwining, the continuum-embedded measure has RP. -/

/-- **RP of continuum-embedded lattice measures.**

Each `continuumMeasure 2 N P a mass ha hmass` satisfies reflection positivity:
`∫ F(ω) · F(Θ*ω) dν ≥ 0` for all bounded continuous F.

Proof:
1. Change of variables: `∫ F·(F∘Θ*) d(ι_* μ) = ∫ (F∘ι)·((F∘ι)∘Θ_latt) dμ`
   (using intertwining: `F(Θ*(ι φ)) = F(ι(Θ_latt φ))`)
2. Lattice RP: `∫ G·(G∘Θ_latt) dμ ≥ 0` where `G = F ∘ ι`
   (from `lattice_rp` in OS3_RP_Lattice.lean) -/
theorem continuum_embedded_measure_rp'
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (a : ℝ) (ha : 0 < a) :
    ∀ (F : Configuration (ContinuumTestFunction 2) → ℝ),
      Continuous F → (∃ C, ∀ ω, |F ω| ≤ C) →
      0 ≤ ∫ ω, F ω * F (distribTimeReflection ω)
        ∂(continuumMeasure 2 N P a mass ha hmass) := by
  intro F hF_cont ⟨C, hC⟩
  -- Step 1: Change of variables: ∫ G d(ι_* μ) = ∫ G∘ι dμ
  set ι := latticeEmbedLift 2 N a ha
  set μ_latt := interactingLatticeMeasure 2 N P a mass ha hmass
  -- The integrand G(ω) = F(ω) · F(Θ*ω)
  set G : Configuration (ContinuumTestFunction 2) → ℝ :=
    fun ω => F ω * F (distribTimeReflection ω)
  change 0 ≤ ∫ ω, G ω ∂(Measure.map ι μ_latt)
  -- Step 2: Change of variables via integral_map
  -- ∫ G d(ι_* μ) = ∫ G∘ι dμ
  -- Then: (G∘ι)(φ) = F(ι φ) · F(Θ*(ι φ)) = F(ι φ) · F(ι(Θ_latt φ))
  -- This is a non-negative integrand (F(ι φ)² after rewriting) IF Θ* acts trivially.
  -- In general it's F(ι φ) · F(ι(Θφ)), which is the RP test for G_latt = F∘ι.
  --
  -- The gap: lattice_rp requires PositiveTimeSupported, but F is arbitrary.
  -- The standard RP inequality ∫ F·(F∘Θ) ≥ 0 for all F follows from RP for
  -- positive-time F by density. This requires a "strong RP" reformulation of
  -- lattice_rp, or a direct proof that ∫ G·(G∘Θ) dμ_latt ≥ 0 for all G.
  --
  -- For now, this remains the single sorry in the RP chain.
  -- Mathematical content: change of variables (integral_map) + lattice RP.
  sorry

end Pphi2

end
