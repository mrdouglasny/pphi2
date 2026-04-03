/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Euclidean time shift on the 2D periodic lattice

Minimal API (gaussian-field `latticeTranslation` only — no `OS2_WardIdentity` import,
so this file stays below the `OSAxioms → … → OS4` layer and avoids cycles).

For `μ = interactingLatticeMeasure`, invariance of `∫ G ∂μ` under this map on
`Configuration` follows from `latticeMeasure_translation_invariant` in
`OS2_WardIdentity.lean` (specialized to `v = latticeEuclideanTimeShift N k`).
-/

import Lattice.Symmetry

noncomputable section

open GaussianField

namespace Pphi2

/-- `k` steps along Euclidean time on the `2 × N` torus (`0` = time, `1` = space). -/
def latticeEuclideanTimeShift (N : ℕ) [NeZero N] (k : ℕ) : FinLatticeSites 2 N :=
  ![(k : ZMod N), 0]

/-- Geodesic time separation from `0` to the class of `k` on the periodic time circle
of length `N`. This is the cyclic distance on `ℤ/Nℤ`. -/
def latticeEuclideanTimeSeparation (N : ℕ) [NeZero N] (k : ℕ) : ℕ :=
  Nat.min (k % N) (N - (k % N))

/-- Time shifts depend only on the class of `k` modulo `N`. -/
@[simp] theorem latticeEuclideanTimeShift_mod (N : ℕ) [NeZero N] (k : ℕ) :
    latticeEuclideanTimeShift N (k % N) = latticeEuclideanTimeShift N k := by
  ext i
  fin_cases i <;> simp [latticeEuclideanTimeShift]

/-- Cyclic time separation depends only on the class modulo `N`. -/
@[simp] theorem latticeEuclideanTimeSeparation_mod (N : ℕ) [NeZero N] (k : ℕ) :
    latticeEuclideanTimeSeparation N (k % N) = latticeEuclideanTimeSeparation N k := by
  simp [latticeEuclideanTimeSeparation]

/-- For a canonical representative `t : Fin N`, the cyclic separation is
`min(t, N - t)`. -/
@[simp] theorem latticeEuclideanTimeSeparation_val (N : ℕ) [NeZero N] (t : Fin N) :
    latticeEuclideanTimeSeparation N t.val = Nat.min t.val (N - t.val) := by
  simp [latticeEuclideanTimeSeparation, Nat.mod_eq_of_lt t.is_lt]

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
