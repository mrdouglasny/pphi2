/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import GaussianField.WickMultivariate

/-!
# Per-vertex connected four-point on the lattice GFF

The smeared Wick/Mehler kernel `GaussianField.gff_wickPower_two_smeared_inner`, specialised to one
**smeared external field** `f` and one **interaction-vertex site** `z`, evaluates the single-vertex
connected four-point:

  `∫ :φ(f)⁴: · :φ(δ_z)⁴: dμ_GFF = 4! · (C_a f)(z)⁴`,

where `(C_a f)(z) = ∑_x f(x) C(x,z)` is the lattice covariance applied to `f` at the vertex `z`. This
is the **atom** of the first-order four-point vertex sum behind `u₄'(0) = −6∫(C_a f)⁴` (step I of the
weak-coupling non-triviality of `φ⁴₂` on `T²`): summing this over the interaction vertices `z` with
the quartic coefficient gives the leading connected four-point.

Axiom-clean (`propext, Classical.choice, Quot.sound`), a direct corollary of the smeared kernel plus
the public covariance connectors `gffSmearedCovariance_self` / `gffSmearedCovariance_single_right`.
-/

namespace Pphi2

open GaussianField MeasureTheory

variable (d N : ℕ) [NeZero N]

/-- **Per-vertex connected four-point on the lattice GFF.** The smeared Wick/Mehler kernel with one
smeared external field `f` and one vertex site `z`:
`∫ :φ(f)⁴: · :φ(δ_z)⁴: dμ_GFF = 4! · (C_a f)(z)⁴ = 24 · (∑_x f(x) C(x,z))⁴`. -/
theorem wickFourth_smeared_vertex_inner (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : FinLatticeField d N) (z : FinLatticeSites d N) :
    ∫ ω, wickMonomial 4 (gffSmearedCovariance d N a mass f f) (ω f) *
          wickMonomial 4 (gffSmearedCovariance d N a mass (Pi.single z 1) (Pi.single z 1))
            (ω (Pi.single z 1))
        ∂(latticeGaussianMeasure d N a mass ha hmass) =
    24 * (∑ x, f x * gffPositionCovariance d N a mass x z) ^ 4 := by
  rw [gffSmearedCovariance_self d N a mass f,
      gffSmearedCovariance_self d N a mass (Pi.single z 1),
      gff_wickPower_two_smeared_inner d N a mass ha hmass 4 4 f (Pi.single z 1),
      gffSmearedCovariance_single_right d N a mass f z]
  norm_num [Nat.factorial]

end Pphi2
