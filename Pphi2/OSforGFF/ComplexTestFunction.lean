import Pphi2.OSAxioms
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

/-- Embed a real Schwartz function as a complex-valued Schwartz function via `Complex.ofReal`. -/
def schwartzOfReal (f : TestFunction2) : TestFunction2ℂ :=
  SchwartzMap.mk (fun x => (f x : ℂ))
    (Complex.ofRealCLM.contDiff.comp f.smooth')
    (by
      intro k n
      obtain ⟨C, hC⟩ := f.decay' k n
      use C * ‖Complex.ofRealCLM‖
      intro x
      have h_eq : (fun y => ((f y : ℝ) : ℂ)) = Complex.ofRealCLM ∘ f.toFun := rfl
      rw [h_eq, ContinuousLinearMap.iteratedFDeriv_comp_left Complex.ofRealCLM
        f.smooth'.contDiffAt (WithTop.coe_le_coe.mpr le_top)]
      calc ‖x‖ ^ k * ‖Complex.ofRealCLM.compContinuousMultilinearMap
              (iteratedFDeriv ℝ n f.toFun x)‖
          ≤ ‖x‖ ^ k * (‖Complex.ofRealCLM‖ * ‖iteratedFDeriv ℝ n f.toFun x‖) :=
            mul_le_mul_of_nonneg_left
              (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _)
              (pow_nonneg (norm_nonneg _) _)
        _ = ‖Complex.ofRealCLM‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f.toFun x‖) := by ring
        _ ≤ ‖Complex.ofRealCLM‖ * C := mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)
        _ = C * ‖Complex.ofRealCLM‖ := by ring)

@[simp] theorem schwartzOfReal_apply (f : TestFunction2) (x : SpaceTime2) :
    schwartzOfReal f x = (f x : ℂ) := rfl

@[simp] theorem schwartzRe_schwartzOfReal (f : TestFunction2) :
    schwartzRe (schwartzOfReal f) = f := by
  ext x
  change (((f x : ℝ) : ℂ)).re = f x
  simp [Complex.ofReal_re]

@[simp] theorem schwartzIm_schwartzOfReal (f : TestFunction2) :
    schwartzIm (schwartzOfReal f) = 0 := by
  ext x
  change (((f x : ℝ) : ℂ)).im = 0
  simp [Complex.ofReal_im]

@[simp] theorem euclideanAction2ℂ_schwartzOfReal (g : E2) (f : TestFunction2) :
    euclideanAction2ℂ g (schwartzOfReal f) = schwartzOfReal (euclideanAction2 g f) := by
  ext x
  rfl

@[simp] theorem schwartzRe_euclideanAction2ℂ (g : E2) (J : TestFunction2ℂ) :
    schwartzRe (euclideanAction2ℂ g J) = euclideanAction2 g (schwartzRe J) := by
  ext x
  rfl

@[simp] theorem schwartzIm_euclideanAction2ℂ (g : E2) (J : TestFunction2ℂ) :
    schwartzIm (euclideanAction2ℂ g J) = euclideanAction2 g (schwartzIm J) := by
  ext x
  rfl

lemma generatingFunctionalℂ_ofReal_add_real_smul
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (f h : TestFunction2) (r : ℝ) :
    generatingFunctionalℂ μ (schwartzOfReal f + (r : ℂ) • schwartzOfReal h) =
      generatingFunctional μ (f + r • h) := by
  unfold generatingFunctionalℂ generatingFunctional
  have hre : schwartzRe (schwartzOfReal f + (r : ℂ) • schwartzOfReal h) = f + r • h := by
    ext x
    change Complex.re ((f x : ℂ) + (r : ℂ) * (h x : ℂ)) = f x + r * h x
    simp [Complex.add_re, Complex.mul_re]
  have him : schwartzIm (schwartzOfReal f + (r : ℂ) • schwartzOfReal h) = 0 := by
    ext x
    change Complex.im ((f x : ℂ) + (r : ℂ) * (h x : ℂ)) = 0
    simp [Complex.add_im, Complex.mul_im]
  rw [hre, him]
  simp

lemma schwartz_decompose (J : TestFunction2ℂ) :
    J = schwartzOfReal (schwartzRe J) + (Complex.I : ℂ) • schwartzOfReal (schwartzIm J) := by
  ext x
  change J x = ((J x).re : ℂ) + Complex.I * ((J x).im : ℂ)
  simpa [mul_comm] using (Complex.re_add_im (J x)).symm

end Pphi2
