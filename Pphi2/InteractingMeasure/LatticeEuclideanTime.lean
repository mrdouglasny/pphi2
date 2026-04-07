/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Euclidean time shift on the 2D periodic lattice

## P vs X

- **P:** `ZMod.valMinAbs` / `ZMod.valMinAbs_natAbs_eq_min` (Mathlib cyclic distance),
  `GaussianField.latticeTranslation`, `FinLatticeSites`.
- **X:** embedding **time** as index `0` on the `2 × N` torus (`latticeEuclideanTimeShift`)
  and the dual configuration map `latticeConfigEuclideanTimeShift` for OS2/OS4 covariance.

See `docs/mathlib_prerequisite_layering.md`.

Minimal import footprint: **no** `OS2_WardIdentity` (avoids cycles through `OSAxioms → … → OS4`).
For `μ = interactingLatticeMeasure`, invariance `∫ G(τ_k ω) ∂μ = ∫ G ∂μ` is proved in
`OS2_WardIdentity` via `latticeMeasure_translation_invariant` at `v = latticeEuclideanTimeShift N k`.
-/

import Lattice.Symmetry
import Mathlib.Data.ZMod.ValMinAbs

noncomputable section

open GaussianField

namespace Pphi2

/-- `k` steps along Euclidean time on the `2 × N` torus (`0` = time, `1` = space). -/
def latticeEuclideanTimeShift (N : ℕ) [NeZero N] (k : ℕ) : FinLatticeSites 2 N :=
  ![(k : ZMod N), 0]

/-- Geodesic time separation from `0` to the class of `k` on the periodic time circle.

Equals `((k : ZMod N).valMinAbs).natAbs`, i.e. the absolute value of the representative
of `k` in `ℤ/Nℤ` closest to `0` (`ZMod.valMinAbs`). By `ZMod.valMinAbs_natAbs_eq_min`,
this is `min (k % N) (N - k % N)` — the graph distance on the cyclic time graph. -/
def latticeEuclideanTimeSeparation (N : ℕ) [NeZero N] (k : ℕ) : ℕ :=
  ((k : ZMod N).valMinAbs).natAbs

theorem latticeEuclideanTimeSeparation_eq_min (N : ℕ) [NeZero N] (k : ℕ) :
    latticeEuclideanTimeSeparation N k = Nat.min (k % N) (N - k % N) := by
  simp [latticeEuclideanTimeSeparation, ZMod.valMinAbs_natAbs_eq_min, ZMod.val_natCast]

/-- Time shifts depend only on the class of `k` modulo `N`. -/
@[simp] theorem latticeEuclideanTimeShift_mod (N : ℕ) [NeZero N] (k : ℕ) :
    latticeEuclideanTimeShift N (k % N) = latticeEuclideanTimeShift N k := by
  ext i
  fin_cases i <;> simp [latticeEuclideanTimeShift]

/-- Cyclic time separation depends only on the class modulo `N`. -/
@[simp] theorem latticeEuclideanTimeSeparation_mod (N : ℕ) [NeZero N] (k : ℕ) :
    latticeEuclideanTimeSeparation N (k % N) = latticeEuclideanTimeSeparation N k := by
  rw [latticeEuclideanTimeSeparation_eq_min, latticeEuclideanTimeSeparation_eq_min]
  simp

/-- For a canonical representative `t : Fin N`, the cyclic separation is
`min(t, N - t)`. -/
@[simp] theorem latticeEuclideanTimeSeparation_val (N : ℕ) [NeZero N] (t : Fin N) :
    latticeEuclideanTimeSeparation N t.val = Nat.min t.val (N - t.val) := by
  simp [latticeEuclideanTimeSeparation, ZMod.valMinAbs_natAbs_eq_min,
    ZMod.val_natCast_of_lt t.is_lt]

/-- Dual translate `ω` by `k` Euclidean-time lattice steps:
`(τ_k ω)(φ) = ω(T_k φ)` with `(T_k φ)(x) = φ(x - k e_0)` (periodic). -/
noncomputable def latticeConfigEuclideanTimeShift (N : ℕ) [NeZero N] (k : ℕ) :
    Configuration (FinLatticeField 2 N) → Configuration (FinLatticeField 2 N) :=
  fun ω => ω.comp (latticeTranslation 2 N (latticeEuclideanTimeShift N k))

/-- Configuration time shifts depend only on the class modulo `N`. -/
@[simp] theorem latticeConfigEuclideanTimeShift_mod (N : ℕ) [NeZero N] (k : ℕ) :
    latticeConfigEuclideanTimeShift N (k % N) = latticeConfigEuclideanTimeShift N k := by
  funext ω
  simp [latticeConfigEuclideanTimeShift]

end Pphi2

end
