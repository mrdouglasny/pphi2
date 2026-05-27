/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Isotropic asymmetric-torus embedding (Z_Nt × Z_Ns)

The metric-correct replacement for `AsymTorusEmbedding.lean`'s `N×N` + geometric-mean-spacing
construction: the lattice is `AsymLatticeField Nt Ns = ZMod Nt × ZMod Ns → ℝ` with a single
isotropic spacing `a` (`a = Lt/Nt = Ls/Ns`), and the interacting measure is
`interactingLatticeMeasureAsym` (covariance `latticeCovarianceAsymGJ`, whose lattice→continuum
limit is the correct rectangular Green's function).

## Main definitions

- `evalAsymTorusAtSiteGJ` — GJ-weighted site evaluation `a • evalAsymTorusAtSite`
- `asymTorusEmbedLiftIso` — lift lattice configs to asymmetric-torus configs
- `asymLatticeTestFnIso` — pull a torus test function back to a lattice field
- `asymTorusInteractingMeasureIso` — pushforward of `interactingLatticeMeasureAsym`

## Normalisation

The GJ weight is the isotropic spacing `a` (per-site weight `a²`, cell area), so that the
embedded second moment is
`covariance (latticeCovarianceAsymGJ) (a·evalAsym f) (a·evalAsym g)
   = covariance (spectralLatticeCovarianceAsym) (evalAsym f) (evalAsym g)`
(the `(1/a)²` of `latticeCovarianceAsymGJ` cancels the `a²` GJ weight), which converges to
`greenFunctionBilinear` by `lattice_green_tendsto_continuum_asym`.
-/

import Pphi2.AsymTorus.AsymLatticeMeasure
import Pphi2.AsymTorus.AsymTorusEmbedding

noncomputable section

open GaussianField MeasureTheory Filter Topology

namespace Pphi2

variable (Lt Ls : ℝ) [hLt : Fact (0 < Lt)] [hLs : Fact (0 < Ls)]

/-- GJ-weighted isotropic site evaluation: `a • evalAsymTorusAtSite`. The single spacing `a`
plays the role of the (former) geometric-mean weight, giving per-site weight `a²`. -/
noncomputable def evalAsymTorusAtSiteGJ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a : ℝ) (x : AsymLatticeSites Nt Ns) : AsymTorusTestFunction Lt Ls →L[ℝ] ℝ :=
  a • evalAsymTorusAtSite Lt Ls Nt Ns x

@[simp] theorem evalAsymTorusAtSiteGJ_apply (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a : ℝ) (x : AsymLatticeSites Nt Ns) (f : AsymTorusTestFunction Lt Ls) :
    evalAsymTorusAtSiteGJ Lt Ls Nt Ns a x f = a * evalAsymTorusAtSite Lt Ls Nt Ns x f := by
  rw [evalAsymTorusAtSiteGJ, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- The isotropic asymmetric-torus embedding: maps a lattice config on `AsymLatticeField Nt Ns`
to a config on `AsymTorusTestFunction Lt Ls` via `(ι ω)(f) = Σ_x ω(δ_x) · evalGJ_x(f)`. -/
def asymTorusEmbedLiftIso (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) :
    Configuration (AsymLatticeField Nt Ns) →
    Configuration (AsymTorusTestFunction Lt Ls) :=
  fun ω =>
    { toFun := fun f => ∑ x : AsymLatticeSites Nt Ns,
        ω (asymLatticeDelta Nt Ns x) * evalAsymTorusAtSiteGJ Lt Ls Nt Ns a x f
      map_add' := fun f g => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r f => by
        simp [smul_eq_mul, mul_left_comm, Finset.mul_sum, RingHom.id_apply]
      cont := by
        apply continuous_finset_sum; intro x _
        exact continuous_const.mul (evalAsymTorusAtSiteGJ Lt Ls Nt Ns a x).cont }

/-- The isotropic asymmetric-torus embedding is measurable. -/
theorem asymTorusEmbedLiftIso_measurable (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) :
    @Measurable _ _ instMeasurableSpaceConfiguration instMeasurableSpaceConfiguration
      (asymTorusEmbedLiftIso Lt Ls Nt Ns a) := by
  apply configuration_measurable_of_eval_measurable
  intro f
  exact Finset.measurable_sum _ fun x _ =>
    (configuration_eval_measurable (asymLatticeDelta Nt Ns x)).mul measurable_const

/-- The isotropic lattice test function: evaluate a torus test function at each site
(GJ-weighted). -/
def asymLatticeTestFnIso (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ)
    (f : AsymTorusTestFunction Lt Ls) : AsymLatticeField Nt Ns :=
  fun x => evalAsymTorusAtSiteGJ Lt Ls Nt Ns a x f

theorem asymLatticeTestFnIso_expand (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ)
    (f : AsymTorusTestFunction Lt Ls) :
    asymLatticeTestFnIso Lt Ls Nt Ns a f =
    ∑ x : AsymLatticeSites Nt Ns,
      (asymLatticeTestFnIso Lt Ls Nt Ns a f) x • asymLatticeDelta Nt Ns x := by
  funext y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, asymLatticeDelta, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The isotropic embedding preserves evaluation:
`(asymTorusEmbedLiftIso ω) f = ω (asymLatticeTestFnIso f)`. -/
theorem asymTorusEmbedLiftIso_eval_eq (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ)
    (f : AsymTorusTestFunction Lt Ls)
    (ω : Configuration (AsymLatticeField Nt Ns)) :
    (asymTorusEmbedLiftIso Lt Ls Nt Ns a ω) f = ω (asymLatticeTestFnIso Lt Ls Nt Ns a f) := by
  change (∑ x : AsymLatticeSites Nt Ns,
      ω (asymLatticeDelta Nt Ns x) * evalAsymTorusAtSiteGJ Lt Ls Nt Ns a x f) =
    ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)
  rw [asymLatticeTestFnIso_expand Lt Ls Nt Ns a f, map_sum]
  simp_rw [map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold asymLatticeTestFnIso
  ring

/-- The isotropic asymmetric-torus interacting P(φ)₂ measure: pushforward of the heterogeneous
interacting lattice measure along the embedding. -/
def asymTorusInteractingMeasureIso (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a : ℝ) (P : InteractionPolynomial) (mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Measure (Configuration (AsymTorusTestFunction Lt Ls)) :=
  Measure.map (asymTorusEmbedLiftIso Lt Ls Nt Ns a)
    (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass)

/-! ## Second moment = spectral covariance, and its continuum limit -/

/-- **The GJ-weight cancellation.** The lattice second moment of the embedding test functions
under the GJ covariance equals the bare spectral covariance of the (unweighted) site
evaluations: `covariance(latticeCovarianceAsymGJ)(a·evalAsym f)(a·evalAsym g) =
covariance(spectralLatticeCovarianceAsym)(evalAsym f)(evalAsym g)`. The `(√(a²))⁻¹ = a⁻¹`
factor of `latticeCovarianceAsymGJ` cancels the `a` GJ weight (twice ⟹ `(a⁻¹·a)² = 1`). -/
theorem second_moment_asym_eq_spectral (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f g : AsymTorusTestFunction Lt Ls) :
    covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass)
      (asymLatticeTestFnIso Lt Ls Nt Ns a f) (asymLatticeTestFnIso Lt Ls Nt Ns a g) =
    covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
      (fun x => evalAsymTorusAtSite Lt Ls Nt Ns x f)
      (fun x => evalAsymTorusAtSite Lt Ls Nt Ns x g) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hc : (Real.sqrt (a ^ 2))⁻¹ * a = 1 := by
    rw [Real.sqrt_sq ha.le]; exact inv_mul_cancel₀ ha0
  have htf : ∀ h : AsymTorusTestFunction Lt Ls,
      asymLatticeTestFnIso Lt Ls Nt Ns a h =
      a • (fun x => evalAsymTorusAtSite Lt Ls Nt Ns x h) := by
    intro h; funext x
    simp [asymLatticeTestFnIso, evalAsymTorusAtSiteGJ_apply, Pi.smul_apply, smul_eq_mul]
  rw [htf f, htf g]
  unfold covariance latticeCovarianceAsymGJ
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul, map_smul,
    smul_smul, smul_smul, hc, one_smul, one_smul]

/-- **The embedded second moment converges to the continuum rectangular Green's function.**
Along any isotropic sequence `(Nt k, Ns k, a k)` with `Nt k·a k = Lt`, `Ns k·a k = Ls`,
`a k → 0`, the lattice second moment of the embedding test functions tends to
`asymTorusContinuumGreen Lt Ls mass hmass f g`. Combines `second_moment_asym_eq_spectral`
with the Phase-1b convergence `lattice_green_tendsto_continuum_asym`. -/
theorem second_moment_asym_tendsto
    (mass : ℝ) (hmass : 0 < mass)
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k))
    (ha : ∀ k, 0 < a k)
    (hLt : ∀ k, (Nt k : ℝ) * a k = Lt) (hLs : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Tendsto a atTop (nhds 0))
    (f g : AsymTorusTestFunction Lt Ls) :
    Tendsto (fun k => haveI := hNt k; haveI := hNs k
        covariance (latticeCovarianceAsymGJ (Nt k) (Ns k) (a k) mass (ha k) hmass)
          (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k) f)
          (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k) g))
      atTop
      (nhds (asymTorusContinuumGreen Lt Ls mass hmass f g)) := by
  have heq : ∀ k, (haveI := hNt k; haveI := hNs k
      covariance (latticeCovarianceAsymGJ (Nt k) (Ns k) (a k) mass (ha k) hmass)
        (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k) f)
        (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k) g)) =
      (haveI := hNt k; haveI := hNs k
      covariance (spectralLatticeCovarianceAsym (Nt k) (Ns k) (a k) mass (ha k) hmass)
        (fun x => evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x f)
        (fun x => evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x g)) := by
    intro k; haveI := hNt k; haveI := hNs k
    exact second_moment_asym_eq_spectral Lt Ls (Nt k) (Ns k) (a k) mass (ha k) hmass f g
  simp_rw [heq]
  unfold asymTorusContinuumGreen
  exact lattice_green_tendsto_continuum_asym Lt Ls mass hmass Nt Ns a hNt hNs ha hLt hLs ha0 f g

end Pphi2

end
