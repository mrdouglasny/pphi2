/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Reflection Positivity Closed Under Weak Limits

Shows that reflection positivity (OS3) is preserved under weak convergence
of measures. This transfers lattice RP to the continuum limit.

## Main results

- `rp_closed_under_weak_limit` — if {μₙ} are RP measures converging weakly
  to μ, then μ is RP

## Mathematical background

RP in the matrix form states: for test functions f₁,...,fₖ supported at
positive time and coefficients c₁,...,cₖ:

  `Σᵢⱼ c̄ᵢ cⱼ ∫ exp(i⟨φ, fᵢ - Θfⱼ⟩) dμ ≥ 0`

Each function `φ ↦ exp(i⟨φ, f⟩)` is bounded and continuous on the
distribution space S'(ℝ²). Therefore:

1. `μₙ ⇀ μ` weakly implies `∫ exp(i⟨φ, f⟩) dμₙ → ∫ exp(i⟨φ, f⟩) dμ`
   for each test function f.

2. Each term `cᵢcⱼ ∫ exp(i⟨φ, fᵢ - Θfⱼ⟩) dμₙ` converges to the
   corresponding term with μ.

3. A finite sum of convergent terms converges: if each partial sum ≥ 0,
   the limit is ≥ 0.

This is one of the few OS axioms that is **provable** (not just axiomatized)
from general principles, without any specifics of P(Φ)₂.

## References

- Osterwalder-Schrader (1975), "Axioms for Euclidean Green's functions II"
- Glimm-Jaffe, *Quantum Physics*, §19.4
-/

import Pphi2.InteractingMeasure.LatticeMeasure

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

/-! ## Abstract RP for measures on a topological space

We formulate RP abstractly for measures on any measurable space equipped
with a reflection map. -/

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]

/-- Abstract reflection positivity condition.

A measure μ on X with reflection Θ : X → X is RP if for all finite
collections of bounded continuous functions Fᵢ supported at "positive time":

  `Σᵢⱼ cᵢ cⱼ ∫ Fᵢ(x) · Fⱼ(Θx) dμ(x) ≥ 0`

We state this for a single function F (the general case follows by
taking F = Σ cᵢ Fᵢ and using bilinearity). -/
def IsRP (μ : Measure X) (Θ : X → X) (S : Set (X → ℝ)) : Prop :=
  ∀ F ∈ S, ∫ x, F x * F (Θ x) ∂μ ≥ 0

/-! ## RP closed under weak limits -/

/-- **RP is closed under weak convergence of measures.**

If `{μₙ}` is a sequence of RP measures on X converging weakly to μ,
then μ is also RP.

Proof:
- For each bounded continuous F:
  `∫ F(x) · F(Θx) dμₙ → ∫ F(x) · F(Θx) dμ`
  by weak convergence (since `x ↦ F(x) · F(Θx)` is bounded continuous
  when F is bounded continuous and Θ is continuous).
- Each term is ≥ 0 by RP of μₙ.
- The limit of nonneg reals is nonneg.

This is a general topological fact that does not depend on the specifics
of the field theory. -/
theorem rp_closed_under_weak_limit
    (Θ : X → X) (hΘ : Continuous Θ)
    (S : Set (X → ℝ))
    (hS_bdd : ∀ F ∈ S, ∃ C, ∀ x, |F x| ≤ C)
    (hS_cont : ∀ F ∈ S, Continuous F)
    (μ : ℕ → Measure X) (μ_lim : Measure X)
    (h_rp : ∀ n, IsRP (μ n) Θ S)
    -- Weak convergence: ∫ g dμₙ → ∫ g dμ_lim for all bounded continuous g
    (h_weak : ∀ (g : X → ℝ), Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Filter.Tendsto (fun n => ∫ x, g x ∂(μ n)) Filter.atTop
        (nhds (∫ x, g x ∂μ_lim))) :
    IsRP μ_lim Θ S := by
  intro F hF
  -- 1. g(x) := F(x) · F(Θx) is bounded continuous
  have hF_cont := hS_cont F hF
  obtain ⟨C, hC⟩ := hS_bdd F hF
  have hg_cont : Continuous (fun x => F x * F (Θ x)) :=
    hF_cont.mul (hF_cont.comp hΘ)
  have hg_bdd : ∃ C', ∀ x, |(fun x => F x * F (Θ x)) x| ≤ C' :=
    ⟨C * C, fun x => by
      simp only; rw [abs_mul]
      nlinarith [hC x, hC (Θ x), abs_nonneg (F x), abs_nonneg (F (Θ x))]⟩
  -- 2. Weak convergence gives ∫ g dμₙ → ∫ g dμ_lim
  have h_tend := h_weak _ hg_cont hg_bdd
  -- 3-4. Each ∫ g dμₙ ≥ 0 by RP; limit of nonneg sequence is nonneg
  exact ge_of_tendsto h_tend (.of_forall (fun n => h_rp n F hF))

/-! ## Application to lattice → continuum

When we have:
- Lattice measures μ_a on S'(ℝ²) (via embedding ι_a)
- Each μ_a satisfies RP (from lattice_rp)
- μ_a ⇀ μ weakly (from tightness + Prokhorov)

Then μ satisfies RP by `rp_closed_under_weak_limit`. -/

/-- RP transfers from lattice to continuum limit.

Given a sequence of lattice spacings aₙ → 0 and the corresponding
continuum-embedded measures μ_{aₙ} ⇀ μ, the limit measure μ is RP. -/
theorem continuum_rp_from_lattice
    {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]
    (Θ : Y → Y) (hΘ : Continuous Θ)
    (S : Set (Y → ℝ))
    (hS_bdd : ∀ F ∈ S, ∃ C, ∀ x, |F x| ≤ C)
    (hS_cont : ∀ F ∈ S, Continuous F)
    (μ : ℕ → Measure Y) (μ_lim : Measure Y)
    (h_rp : ∀ n, IsRP (μ n) Θ S)
    (h_weak : ∀ (g : Y → ℝ), Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Filter.Tendsto (fun n => ∫ x, g x ∂(μ n)) Filter.atTop
        (nhds (∫ x, g x ∂μ_lim))) :
    IsRP μ_lim Θ S :=
  rp_closed_under_weak_limit Θ hΘ S hS_bdd hS_cont μ μ_lim h_rp h_weak

end Pphi2

end
