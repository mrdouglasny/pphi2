/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.InteractingMeasure.U4Derivative
import Pphi2.TorusContinuumLimit.TorusInteractingLimit

/-!
# Uniform-in-N building blocks for the weak-coupling discharge

Foundational facts for the `N`-uniform remainder bound that closes
`torus_weakCoupling_lattice_connectedFourPoint_strictNeg` (see
`planning/uniform-remainder-roadmap.md`). This file starts with the **fixed-volume identity**: on the
torus the lattice spacing `a = L/N`, so the lattice "volume" `a^d · #sites = (a·N)^d` is `L^d`,
**independent of `N`**. This is the structural reason the fixed torus is uniformly controllable where
infinite volume is not.
-/

namespace Pphi2

open MeasureTheory GaussianField

/-- The number of lattice sites is `N^d`. -/
@[simp] lemma latticeSites_card (d N : ℕ) [NeZero N] :
    Fintype.card (FinLatticeSites d N) = N ^ d := by
  simp [FinLatticeSites, Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- **Fixed-volume identity.** `a^d · #sites = (a·N)^d`. With the torus spacing `a = L/N` this is
`L^d`, uniform in `N`. -/
lemma lattice_volume_eq (d N : ℕ) [NeZero N] (a : ℝ) :
    a ^ d * (Fintype.card (FinLatticeSites d N) : ℝ) = (a * N) ^ d := by
  rw [latticeSites_card]; push_cast; rw [mul_pow]

/-- **Torus volume is `L^d`, uniform in `N`.** The lattice volume `(circleSpacing L N)^d · #sites`
equals `L^d` for every `N`. -/
lemma torus_volume_eq (L : ℝ) [Fact (0 < L)] (d N : ℕ) [NeZero N] :
    (circleSpacing L N) ^ d * (Fintype.card (FinLatticeSites d N) : ℝ) = L ^ d := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [lattice_volume_eq, circleSpacing_eq]
  field_simp

end Pphi2
