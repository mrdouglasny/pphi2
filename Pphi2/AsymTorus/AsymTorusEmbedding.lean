/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Asymmetric Torus Embedding: Route B'

Defines the continuum-embedded measures on the asymmetric torus
T_{Lt,Ls} = (ℝ/Lt ℤ) × (ℝ/Ls ℤ), analogous to `TorusEmbedding.lean`
for the symmetric torus.

This is the starting point for Route B': UV limit on T_{Lt,Ls}
followed by IR limit Lt → ∞ to the cylinder S¹_{Ls} × ℝ.

## Main definitions

- `asymTorusEmbedLift` — lifts lattice configs to asymmetric torus configs
- `asymTorusInteractingMeasure` — pushforward of lattice interacting measure
- `asymTorusContinuumGreen` — continuum Green's function on T_{Lt,Ls}

## Design

Uses `AsymTorusTestFunction Lt Ls = NTP(SMC_{Lt}, SMC_{Ls})` from
gaussian-field's `Torus/AsymmetricTorus.lean`. The lattice uses
`AsymLatticeSites Nt Ns = ZMod Nt × ZMod Ns` with spacings
`at = Lt/Nt` (time) and `as = Ls/Ns` (space).

All NTP infrastructure (evalCLM, mapCLM, etc.) works unchanged.
Route B's proofs adapt with minimal type changes.
-/

import Pphi2.InteractingMeasure.LatticeMeasure
import Torus.AsymmetricTorus
import HeatKernel.Bilinear
import SmoothCircle.Eigenvalues

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

variable (Lt Ls : ℝ) [hLt : Fact (0 < Lt)] [hLs : Fact (0 < Ls)]

/-! ## Lattice spacings -/

/-- Time lattice spacing: at = Lt/Nt. -/
def asymTimeSpacing (Nt : ℕ) [NeZero Nt] : ℝ := Lt / Nt

/-- Space lattice spacing: as = Ls/Ns. -/
def asymSpaceSpacing (Ns : ℕ) [NeZero Ns] : ℝ := Ls / Ns

theorem asymTimeSpacing_pos (Nt : ℕ) [NeZero Nt] :
    0 < asymTimeSpacing Lt Nt :=
  div_pos hLt.out (Nat.cast_pos.mpr (NeZero.pos Nt))

theorem asymSpaceSpacing_pos (Ns : ℕ) [NeZero Ns] :
    0 < asymSpaceSpacing Ls Ns :=
  div_pos hLs.out (Nat.cast_pos.mpr (NeZero.pos Ns))

/-! ## Embedding of asymmetric lattice fields

The asymmetric lattice (ZMod Nt) × (ZMod Ns) embeds into the asymmetric
torus configuration space via `asymTorusEmbedCLM` from gaussian-field. -/

/-- Convert `FinLatticeSites 2 N` to `AsymLatticeSites N N`.
These are equivalent: `(Fin 2 → ZMod N) ≃ (ZMod N × ZMod N)`. -/
def finToAsymSite (N : ℕ) (x : FinLatticeSites 2 N) : AsymLatticeSites N N :=
  (x 0, x 1)

/-- Evaluate an asymmetric torus test function at a site given in `FinLatticeSites 2 N` form.
Converts `(Fin 2 → ZMod N)` to `(ZMod N × ZMod N)` and applies `evalAsymTorusAtSite`. -/
def evalAsymAtFinSite (N : ℕ) [NeZero N]
    (x : FinLatticeSites 2 N) : AsymTorusTestFunction Lt Ls →L[ℝ] ℝ :=
  evalAsymTorusAtSite Lt Ls N N (x 0, x 1)

/-- The asymmetric torus embedding: maps lattice configs on `FinLatticeField 2 N`
to configs on `AsymTorusTestFunction Lt Ls`. Uses DIFFERENT circle restrictions
per direction (Lt/N for time, Ls/N for space). -/
def asymTorusEmbedLift (N : ℕ) [NeZero N] :
    Configuration (FinLatticeField 2 N) →
    Configuration (AsymTorusTestFunction Lt Ls) :=
  fun ω =>
    { toFun := fun f => ∑ x : FinLatticeSites 2 N,
        ω (Pi.single x 1) * evalAsymAtFinSite Lt Ls N x f
      map_add' := fun f g => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r f => by
        simp [smul_eq_mul, mul_left_comm, Finset.mul_sum, RingHom.id_apply]
      cont := by
        apply continuous_finset_sum; intro x _
        exact continuous_const.mul (evalAsymAtFinSite Lt Ls N x).cont }

/-- The asymmetric torus embedding lift is measurable. -/
theorem asymTorusEmbedLift_measurable (N : ℕ) [NeZero N] :
    @Measurable _ _ instMeasurableSpaceConfiguration instMeasurableSpaceConfiguration
      (asymTorusEmbedLift Lt Ls N) := by
  apply configuration_measurable_of_eval_measurable
  intro f
  exact Finset.measurable_sum _ fun x _ =>
    (configuration_eval_measurable (Pi.single x 1)).mul measurable_const

/-! ## Lattice test functions and eval identity -/

/-- The asymmetric lattice test function: evaluates an asymmetric torus test function
at each lattice site. This is the asymmetric analog of `latticeTestFn`. -/
def asymLatticeTestFn (N : ℕ) [NeZero N]
    (f : AsymTorusTestFunction Lt Ls) : FinLatticeField 2 N :=
  fun x => evalAsymAtFinSite Lt Ls N x f

/-- Key identity: the asymmetric lattice test function equals the sum of its
values times delta functions. -/
theorem asymLatticeTestFn_expand (N : ℕ) [NeZero N]
    (f : AsymTorusTestFunction Lt Ls) :
    asymLatticeTestFn Lt Ls N f =
    ∑ x : FinLatticeSites 2 N,
      (asymLatticeTestFn Lt Ls N f) x • Pi.single x (1 : ℝ) := by
  funext y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The asymmetric torus embedding preserves evaluation:
`(asymTorusEmbedLift ω) f = ω (asymLatticeTestFn f)`.

This is the asymmetric analog of `torusEmbedLift_eval_eq`. -/
theorem asymTorusEmbedLift_eval_eq (N : ℕ) [NeZero N]
    (f : AsymTorusTestFunction Lt Ls)
    (ω : Configuration (FinLatticeField 2 N)) :
    (asymTorusEmbedLift Lt Ls N ω) f = ω (asymLatticeTestFn Lt Ls N f) := by
  -- LHS = Σ_x ω(δ_x) * eval_x(f)
  -- RHS = ω(Σ_x eval_x(f) • δ_x) = Σ_x eval_x(f) * ω(δ_x)
  change (∑ x : FinLatticeSites 2 N,
      ω (Pi.single x 1) * evalAsymAtFinSite Lt Ls N x f) =
    ω (asymLatticeTestFn Lt Ls N f)
  rw [asymLatticeTestFn_expand Lt Ls N f, map_sum]
  simp_rw [map_smul, smul_eq_mul]
  congr 1
  funext x
  unfold asymLatticeTestFn
  ring

/-! ## Interacting measure on asymmetric torus -/

/-- The geometric mean spacing: √(at · as) = √(Lt · Ls) / N.

This is the effective spacing for the interaction on the asymmetric lattice.
The cell area at·as = Lt·Ls/N² equals a_geom², preserving the relationship
between physical volume and lattice sum that Nelson's estimate uses. -/
def asymGeomSpacing (N : ℕ) [NeZero N] : ℝ :=
  Real.sqrt (asymTimeSpacing Lt N * asymSpaceSpacing Ls N)

theorem asymGeomSpacing_pos (N : ℕ) [NeZero N] :
    0 < asymGeomSpacing Lt Ls N :=
  Real.sqrt_pos_of_pos (mul_pos (asymTimeSpacing_pos Lt N) (asymSpaceSpacing_pos Ls N))

/-- The asymmetric torus-embedded interacting P(φ)₂ measure.

Uses the same N for both directions (Option 2), with the geometric mean
spacing `a_geom = √(Lt·Ls)/N` as the effective lattice spacing parameter.
This means:
- The lattice is (ℤ/Nℤ)² (same sites as symmetric torus)
- The Gaussian measure uses the SYMMETRIC Laplacian with spacing a_geom
  (TODO: replace with asymmetric Laplacian for correct eigenvalues)
- The interaction V = a_geom² Σ_x :P(φ(x)):_c has cell area = Lt·Ls/N²
- Nelson's estimate: a_geom² · N² = Lt·Ls (physical volume, constant)

The pushforward maps lattice configs to asymmetric torus configs via
`asymTorusEmbedLift` which uses DIFFERENT circle restrictions per direction. -/
def asymTorusInteractingMeasure (N : ℕ) [NeZero N]
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    Measure (Configuration (AsymTorusTestFunction Lt Ls)) :=
  Measure.map (asymTorusEmbedLift Lt Ls N)
    (interactingLatticeMeasure 2 N P (asymGeomSpacing Lt Ls N) mass
      (asymGeomSpacing_pos Lt Ls N) hmass)

/-! ## Continuum Green's function -/

/-- The continuum Green's function on the asymmetric torus T_{Lt,Ls}.

  `G_{Lt,Ls}(f,g) = Σ_{(n₁,n₂)} ĉ_{n₁}(f₁) ĉ_{n₂}(f₂) / ((2πn₁/Lt)² + (2πn₂/Ls)² + m²)`

Uses `greenFunctionBilinear` which works generically for any NTP with
`HasLaplacianEigenvalues` on both factors. Both `SmoothMap_Circle Lt ℝ`
and `SmoothMap_Circle Ls ℝ` have this instance from gaussian-field. -/
noncomputable def asymTorusContinuumGreen (mass : ℝ) (hmass : 0 < mass)
    (f g : AsymTorusTestFunction Lt Ls) : ℝ :=
  greenFunctionBilinear mass hmass f g

end Pphi2

end
