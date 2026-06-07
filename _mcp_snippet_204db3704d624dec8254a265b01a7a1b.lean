import Pphi2.InteractingMeasure.U4DerivativeClosedForm

example {f g : ℝ → ℝ} {f' g' x : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => f y - 3 * (g y) ^ 2)
      (f' - 6 * g x * g') x := by
  have h := hf.sub ((hg.pow 2).const_mul (3 : ℝ))
  convert h using 1
  · ring

example {f g fd gd : ℝ → ℝ} {f' g' fd' gd' x : ℝ}
    (hfd : HasDerivAt fd fd' x) (hg : HasDerivAt g g' x)
    (hf : HasDerivAt f f' x) (hgd : HasDerivAt gd gd' x)
    (hne : (g x) ^ 2 ≠ 0) :
    HasDerivAt (fun y => (fd y * g y - f y * gd y) / (g y) ^ 2)
      (((fd' * g x + fd x * g') - (f' * gd x + f x * gd')) * (g x) ^ 2 -
          (fd x * g x - f x * gd x) * (2 * g x ^ (2 - 1) * g')) /
        ((g x) ^ 2) ^ 2) x := by
  have hnum := (hfd.mul hg).sub (hf.mul hgd)
  have hden := hg.pow 2
  simpa using hnum.div hden hne
