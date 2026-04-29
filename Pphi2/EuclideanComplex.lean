/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Generic Complex Test-Function API

This file packages the standard real/complex Schwartz-function conversions and
their interaction with Euclidean motions and generating functionals for an
arbitrary Euclidean background.

The canonical 2D API is the specialization to `plane2Background` via
`Pphi2/Backgrounds/EuclideanPlane2D.lean`.
-/

import Pphi2.EuclideanOS
import Pphi2.GeneralResults.ComplexAnalysis

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

/-- Embed a real Schwartz function as a complex-valued Schwartz function via
`Complex.ofReal`. -/
def schwartzOfReal {B : EuclideanPlaneBackground}
    (f : EuclideanPlaneBackground.RealTestFunction B) :
    EuclideanPlaneBackground.ComplexTestFunction B :=
  f.postcompCLM Complex.ofRealCLM

@[simp] theorem schwartzOfReal_apply {B : EuclideanPlaneBackground}
    (f : EuclideanPlaneBackground.RealTestFunction B)
    (x : EuclideanPlaneBackground.SpaceTime B) :
    schwartzOfReal f x = (f x : ℂ) := rfl

@[simp] theorem schwartzRe_schwartzOfReal {B : EuclideanPlaneBackground}
    (f : EuclideanPlaneBackground.RealTestFunction B) :
    EuclideanOS.schwartzRe (schwartzOfReal f) = f := by
  ext x
  change (((f x : ℝ) : ℂ)).re = f x
  simp [Complex.ofReal_re]

@[simp] theorem schwartzIm_schwartzOfReal {B : EuclideanPlaneBackground}
    (f : EuclideanPlaneBackground.RealTestFunction B) :
    EuclideanOS.schwartzIm (schwartzOfReal f) = 0 := by
  ext x
  change (((f x : ℝ) : ℂ)).im = 0
  simp [Complex.ofReal_im]

@[simp] theorem schwartzOfReal_add {B : EuclideanPlaneBackground}
    (f g : EuclideanPlaneBackground.RealTestFunction B) :
    schwartzOfReal (f + g) = schwartzOfReal f + schwartzOfReal g := by
  ext x
  change (((f + g) x : ℝ) : ℂ) = ((f x : ℂ) + (g x : ℂ))
  simp

@[simp] theorem schwartzOfReal_real_smul {B : EuclideanPlaneBackground}
    (r : ℝ) (f : EuclideanPlaneBackground.RealTestFunction B) :
    schwartzOfReal (r • f) = (r : ℂ) • schwartzOfReal f := by
  ext x
  change (((r • f) x : ℝ) : ℂ) = (r : ℂ) * (f x : ℂ)
  simp

@[simp] theorem schwartzRe_ofReal_add_real_smul {B : EuclideanPlaneBackground}
    (f h : EuclideanPlaneBackground.RealTestFunction B) (r : ℝ) :
    EuclideanOS.schwartzRe (schwartzOfReal f + (r : ℂ) • schwartzOfReal h) = f + r • h := by
  ext x
  change Complex.re ((f x : ℂ) + (r : ℂ) * (h x : ℂ)) = f x + r * h x
  simp [Complex.add_re, Complex.mul_re]

@[simp] theorem schwartzIm_ofReal_add_real_smul {B : EuclideanPlaneBackground}
    (f h : EuclideanPlaneBackground.RealTestFunction B) (r : ℝ) :
    EuclideanOS.schwartzIm (schwartzOfReal f + (r : ℂ) • schwartzOfReal h) = 0 := by
  ext x
  change Complex.im ((f x : ℂ) + (r : ℂ) * (h x : ℂ)) = 0
  simp [Complex.add_im, Complex.mul_im]

@[simp] theorem schwartzRe_complex_smul {B : EuclideanPlaneBackground}
    (z : ℂ) (J : EuclideanPlaneBackground.ComplexTestFunction B) :
    EuclideanOS.schwartzRe (z • J) =
      z.re • EuclideanOS.schwartzRe J - z.im • EuclideanOS.schwartzIm J := by
  ext x
  change Complex.re (z * J x) = z.re * Complex.re (J x) - z.im * Complex.im (J x)
  simp [Complex.mul_re]

@[simp] theorem schwartzIm_complex_smul {B : EuclideanPlaneBackground}
    (z : ℂ) (J : EuclideanPlaneBackground.ComplexTestFunction B) :
    EuclideanOS.schwartzIm (z • J) =
      z.re • EuclideanOS.schwartzIm J + z.im • EuclideanOS.schwartzRe J := by
  ext x
  change Complex.im (z * J x) = z.re * Complex.im (J x) + z.im * Complex.re (J x)
  simp [Complex.mul_im]

theorem schwartzRe_sum_complex_smul {B : EuclideanPlaneBackground} {n : ℕ}
    (z : Fin n → ℂ) (J : Fin n → EuclideanPlaneBackground.ComplexTestFunction B) :
    EuclideanOS.schwartzRe (∑ i, z i • J i) =
      ∑ i, ((z i).re • EuclideanOS.schwartzRe (J i) -
        (z i).im • EuclideanOS.schwartzIm (J i)) := by
  ext x
  simp [EuclideanOS.schwartzRe, EuclideanOS.schwartzIm, Complex.mul_re, Finset.sum_sub_distrib]

theorem schwartzIm_sum_complex_smul {B : EuclideanPlaneBackground} {n : ℕ}
    (z : Fin n → ℂ) (J : Fin n → EuclideanPlaneBackground.ComplexTestFunction B) :
    EuclideanOS.schwartzIm (∑ i, z i • J i) =
      ∑ i, ((z i).re • EuclideanOS.schwartzIm (J i) +
        (z i).im • EuclideanOS.schwartzRe (J i)) := by
  ext x
  simp [EuclideanOS.schwartzIm, EuclideanOS.schwartzRe, Complex.mul_im, Finset.sum_add_distrib]

/-- The complex pairing with a finite complex source family is linear in the coefficients. -/
lemma pairing_sum_complex_smul {B : EuclideanPlaneBackground} {n : ℕ}
    (ω : EuclideanPlaneBackground.Distribution B)
    (z : Fin n → ℂ) (J : Fin n → EuclideanPlaneBackground.ComplexTestFunction B) :
    ((ω (EuclideanOS.schwartzRe (∑ i, z i • J i)) : ℂ) +
        Complex.I * (ω (EuclideanOS.schwartzIm (∑ i, z i • J i)) : ℂ)) =
      ∑ i : Fin n,
        z i * ((ω (EuclideanOS.schwartzRe (J i)) : ℂ) +
          Complex.I * (ω (EuclideanOS.schwartzIm (J i)) : ℂ)) := by
  rw [schwartzRe_sum_complex_smul, schwartzIm_sum_complex_smul]
  apply Complex.ext
  · simp [map_sum, map_add, map_sub, map_smul, smul_eq_mul, Complex.mul_re,
      Complex.mul_im, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  · simp [map_sum, map_add, map_sub, map_smul, smul_eq_mul, Complex.mul_re,
      Complex.mul_im, Finset.sum_add_distrib, Finset.sum_sub_distrib]

@[simp] theorem actionComplex_schwartzOfReal {B : EuclideanPlaneBackground}
    (g : EuclideanPlaneBackground.Motion B)
    (f : EuclideanPlaneBackground.RealTestFunction B) :
    EuclideanPlaneBackground.actionComplex g (schwartzOfReal f) =
      schwartzOfReal (EuclideanPlaneBackground.action g f) := by
  ext x
  rfl

@[simp] theorem schwartzRe_actionComplex {B : EuclideanPlaneBackground}
    (g : EuclideanPlaneBackground.Motion B)
    (J : EuclideanPlaneBackground.ComplexTestFunction B) :
    EuclideanOS.schwartzRe (EuclideanPlaneBackground.actionComplex g J) =
      EuclideanPlaneBackground.action g (EuclideanOS.schwartzRe J) := by
  ext x
  rfl

@[simp] theorem schwartzIm_actionComplex {B : EuclideanPlaneBackground}
    (g : EuclideanPlaneBackground.Motion B)
    (J : EuclideanPlaneBackground.ComplexTestFunction B) :
    EuclideanOS.schwartzIm (EuclideanPlaneBackground.actionComplex g J) =
      EuclideanPlaneBackground.action g (EuclideanOS.schwartzIm J) := by
  ext x
  rfl

lemma generatingFunctionalℂ_ofReal_add_real_smul {B : EuclideanPlaneBackground}
    (μ : Measure (EuclideanPlaneBackground.Distribution B)) [IsProbabilityMeasure μ]
    (f h : EuclideanPlaneBackground.RealTestFunction B) (r : ℝ) :
    EuclideanOS.generatingFunctionalℂ μ (schwartzOfReal f + (r : ℂ) • schwartzOfReal h) =
      EuclideanOS.generatingFunctional μ (f + r • h) := by
  unfold EuclideanOS.generatingFunctionalℂ EuclideanOS.generatingFunctional
  refine integral_congr_ae ?_
  exact ae_of_all _ fun ω => by
    rw [schwartzRe_ofReal_add_real_smul, schwartzIm_ofReal_add_real_smul]
    simp [map_zero]

lemma schwartz_decompose {B : EuclideanPlaneBackground}
    (J : EuclideanPlaneBackground.ComplexTestFunction B) :
    J = schwartzOfReal (EuclideanOS.schwartzRe J) +
      (Complex.I : ℂ) • schwartzOfReal (EuclideanOS.schwartzIm J) := by
  ext x
  change J x = ((J x).re : ℂ) + Complex.I * ((J x).im : ℂ)
  simpa [mul_comm] using (Complex.re_add_im (J x)).symm

lemma schwartz_decompose_actionComplex {B : EuclideanPlaneBackground}
    (g : EuclideanPlaneBackground.Motion B)
    (J : EuclideanPlaneBackground.ComplexTestFunction B) :
    EuclideanPlaneBackground.actionComplex g J =
      schwartzOfReal (EuclideanPlaneBackground.action g (EuclideanOS.schwartzRe J)) +
        (Complex.I : ℂ) •
          schwartzOfReal (EuclideanPlaneBackground.action g (EuclideanOS.schwartzIm J)) := by
  calc
    EuclideanPlaneBackground.actionComplex g J
        = schwartzOfReal (EuclideanOS.schwartzRe (EuclideanPlaneBackground.actionComplex g J)) +
            (Complex.I : ℂ) •
              schwartzOfReal
                (EuclideanOS.schwartzIm (EuclideanPlaneBackground.actionComplex g J)) :=
          schwartz_decompose (EuclideanPlaneBackground.actionComplex g J)
    _ = schwartzOfReal (EuclideanPlaneBackground.action g (EuclideanOS.schwartzRe J)) +
          (Complex.I : ℂ) •
            schwartzOfReal (EuclideanPlaneBackground.action g (EuclideanOS.schwartzIm J)) := by
        rw [schwartzRe_actionComplex, schwartzIm_actionComplex]

/-- Same as `schwartz_decompose_actionComplex` for the `Continuum*` motion/pullback names in
`Backgrounds/EuclideanPlane.lean` (definitional specialisation to `planeBackground d`). -/
theorem schwartz_decompose_continuumEuclideanActionComplex {d : ℕ}
    (g : ContinuumMotion d) (J : ContinuumComplexTestFunction d) :
    continuumEuclideanActionComplex g J =
      schwartzOfReal (continuumEuclideanAction g (EuclideanOS.schwartzRe J)) +
        (Complex.I : ℂ) • schwartzOfReal (continuumEuclideanAction g (EuclideanOS.schwartzIm J)) :=
  schwartz_decompose_actionComplex g J

end Pphi2
