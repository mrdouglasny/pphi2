/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Heterogeneous polynomial-chaos field decomposition (`Z_Nt × Z_Ns`)

The isotropic-lattice analogue of the square `CanonicalJoint` field decomposition
(`Pphi2/NelsonEstimate/FieldDecomposition.lean`): the lattice GFF is realized as the pushforward of
a product of two iid standard-Gaussian families (smooth + rough) synthesized through the rectangular
DFT modes `Fin Nt × Fin Ns` with the cutoff-split covariance weights. This is the dependency-root for
discharging `asymChaosCutoffDecomposition` (the heterogeneous Nelson chaos decomposition).

**Foundational layer (this file):** the joint space/measure, the rectangular-dispersion eigenvalue,
the smooth/rough cutoff weights, the DFT mode coefficients, and the smooth/rough/sum synthesis
functions. The deep `pushforward_eq_GFF` identity (`map (φ_S+φ_R) = latticeGaussianMeasureAsym`) is
the next target — see `docs/asym-fielddecomposition-redesign.md`.

The 1D DFT primitives (`latticeEigenvalue1d`, `latticeFourierBasisFun`, `latticeFourierNormSq`) are
the **same** functions the square uses (per direction `Nt`/`Ns`), so no new Fourier objects are
needed; the rectangular dispersion `λ_{m₁,m₂}` is exactly the eigenvalue of
`abstract_spectral_eq_dft_spectral_2d_asym` (Phase-1b).
-/

import Pphi2.AsymTorus.AsymLatticeMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real

noncomputable section

open MeasureTheory ProbabilityTheory GaussianField

namespace Pphi2

/-- DFT mode index for the rectangular lattice: `Fin Nt × Fin Ns` (cardinality `Nt·Ns`, matching the
site count and the mode sum of `abstract_spectral_eq_dft_spectral_2d_asym`). -/
abbrev AsymCanonicalMode (Nt Ns : ℕ) : Type := Fin Nt × Fin Ns

/-- The canonical joint space: two iid standard-Gaussian families over the DFT modes
(smooth, rough). -/
abbrev AsymCanonicalJoint (Nt Ns : ℕ) : Type :=
  (AsymCanonicalMode Nt Ns → ℝ) × (AsymCanonicalMode Nt Ns → ℝ)

/-- The joint reference measure: product of two iid standard Gaussians over the modes. -/
def asymCanonicalJointMeasure (Nt Ns : ℕ) : Measure (AsymCanonicalJoint Nt Ns) :=
  Measure.prod
    (Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1))
    (Measure.pi (fun _ : AsymCanonicalMode Nt Ns => gaussianReal 0 1))

instance asymCanonicalJointMeasure_isProbability (Nt Ns : ℕ) :
    IsProbabilityMeasure (asymCanonicalJointMeasure Nt Ns) := by
  unfold asymCanonicalJointMeasure; infer_instance

/-- Rectangular-lattice dispersion eigenvalue `λ_{m₁,m₂} = λ_1d(Nt,m₁) + λ_1d(Ns,m₂) + m²`. -/
def asymCanonicalEigenvalue (Nt Ns : ℕ) (a mass : ℝ) (m : AsymCanonicalMode Nt Ns) : ℝ :=
  latticeEigenvalue1d Nt a (m.1 : ℕ) + latticeEigenvalue1d Ns a (m.2 : ℕ) + mass ^ 2

/-- Smooth (low-frequency) part of the covariance eigenvalue `1/λ` at cutoff scale `T`. -/
def asymCanonicalSmoothWeight (Nt Ns : ℕ) (a mass T : ℝ) (m : AsymCanonicalMode Nt Ns) : ℝ :=
  Real.exp (-T * asymCanonicalEigenvalue Nt Ns a mass m) / asymCanonicalEigenvalue Nt Ns a mass m

/-- Rough (high-frequency) part of the covariance eigenvalue `1/λ` at cutoff scale `T`. -/
def asymCanonicalRoughWeight (Nt Ns : ℕ) (a mass T : ℝ) (m : AsymCanonicalMode Nt Ns) : ℝ :=
  (1 - Real.exp (-T * asymCanonicalEigenvalue Nt Ns a mass m)) /
    asymCanonicalEigenvalue Nt Ns a mass m

/-- Product DFT basis function `B_{m₁,m₂}(x) = e_{m₁}(x₁)·e_{m₂}(x₂)`. -/
def asymCanonicalBasis (Nt Ns : ℕ) (m : AsymCanonicalMode Nt Ns) (x : AsymLatticeSites Nt Ns) : ℝ :=
  latticeFourierBasisFun Nt (m.1 : ℕ) x.1 * latticeFourierBasisFun Ns (m.2 : ℕ) x.2

/-- Product DFT basis norm² `‖B_m‖² = normSq(Nt,m₁)·normSq(Ns,m₂)`. -/
def asymCanonicalNormSq (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (m : AsymCanonicalMode Nt Ns) : ℝ :=
  latticeFourierNormSq Nt (m.1 : ℕ) * latticeFourierNormSq Ns (m.2 : ℕ)

/-- Smooth synthesis coefficient: `√(smoothWeight/‖B_m‖²)·B_m(x)`. -/
def asymCanonicalSmoothModeCoeff (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (x : AsymLatticeSites Nt Ns) (m : AsymCanonicalMode Nt Ns) : ℝ :=
  Real.sqrt (asymCanonicalSmoothWeight Nt Ns a mass T m / asymCanonicalNormSq Nt Ns m) *
    asymCanonicalBasis Nt Ns m x

/-- Rough synthesis coefficient: `√(roughWeight/‖B_m‖²)·B_m(x)`. -/
def asymCanonicalRoughModeCoeff (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (x : AsymLatticeSites Nt Ns) (m : AsymCanonicalMode Nt Ns) : ℝ :=
  Real.sqrt (asymCanonicalRoughWeight Nt Ns a mass T m / asymCanonicalNormSq Nt Ns m) *
    asymCanonicalBasis Nt Ns m x

/-- The smooth field synthesized from the first (smooth) Gaussian family. The `(√(a²))⁻¹ = 1/a`
prefix is the Glimm–Jaffe `d = 2` normalization, matching
`latticeCovarianceAsymGJ = (√(a²))⁻¹ • spectral`: it makes the synthesis covariance equal the GJ
covariance (not the bare spectral one). -/
def asymCanonicalSmoothFieldFunction (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (η : AsymCanonicalJoint Nt Ns) : AsymLatticeField Nt Ns :=
  fun x => (Real.sqrt (a ^ 2))⁻¹ *
    ∑ m : AsymCanonicalMode Nt Ns, asymCanonicalSmoothModeCoeff Nt Ns a mass T x m * η.1 m

/-- The rough field synthesized from the second (rough) Gaussian family (same GJ `(√(a²))⁻¹`
prefix as the smooth part). -/
def asymCanonicalRoughFieldFunction (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (η : AsymCanonicalJoint Nt Ns) : AsymLatticeField Nt Ns :=
  fun x => (Real.sqrt (a ^ 2))⁻¹ *
    ∑ m : AsymCanonicalMode Nt Ns, asymCanonicalRoughModeCoeff Nt Ns a mass T x m * η.2 m

/-- The synthesized field `φ_S + φ_R`; its law (under `asymCanonicalJointMeasure`) is the lattice
GFF — the `pushforward_eq_GFF` identity, the next target (see the redesign doc). -/
def asymCanonicalSumFieldFunction (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (η : AsymCanonicalJoint Nt Ns) : AsymLatticeField Nt Ns :=
  fun x => asymCanonicalSmoothFieldFunction Nt Ns a mass T η x +
    asymCanonicalRoughFieldFunction Nt Ns a mass T η x

/-- The smooth + rough cutoff weights sum to the full covariance eigenvalue `1/λ_m` — the algebraic
identity underlying `pushforward_eq_GFF` (the two iid families synthesize a Gaussian field with the
GFF covariance). -/
theorem asymCanonicalSmoothWeight_add_roughWeight (Nt Ns : ℕ) (a mass T : ℝ)
    (m : AsymCanonicalMode Nt Ns) :
    asymCanonicalSmoothWeight Nt Ns a mass T m + asymCanonicalRoughWeight Nt Ns a mass T m =
      (asymCanonicalEigenvalue Nt Ns a mass m)⁻¹ := by
  unfold asymCanonicalSmoothWeight asymCanonicalRoughWeight
  rw [← add_div,
    show Real.exp (-T * asymCanonicalEigenvalue Nt Ns a mass m) +
        (1 - Real.exp (-T * asymCanonicalEigenvalue Nt Ns a mass m)) = 1 from by ring,
    one_div]

end Pphi2

end
