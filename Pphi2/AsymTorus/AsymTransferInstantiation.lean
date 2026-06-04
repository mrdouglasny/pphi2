/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import ReflectionPositivity.TransferConstruction
import ReflectionPositivity.TransferSystem
import Pphi2.AsymTorus.AsymSpectralGap

/-!
# Transfer-matrix discharge of the asym φ⁴₂ Layer-B2 bound — entry point

Towards discharging `asymInteractingVariance_le_freeVariance_Lt_uniform`
(`AsymExpMomentDischarge.lean`) via the transfer matrix.

**Route (decided 2026-06-03): Option B — the slice transfer matrix.** An axiom-vetting
pass (Gemini 3.1-pro) showed the finite-torus GNS instantiation of the abstract
`ReflectionPositivity.TransferConstruction` bridge is *unsound* — on a periodic torus the
positive-time sub-σ-algebra is not stable under the unit time shift (`τPos` is false), so
the GNS transfer operator is not well-defined. The sound route keeps the finite torus and
uses pphi2's **existing** slice operator `asymTransferOperatorCLM` on `L2SpatialField Ns`
(correctly normalized after the `a²/2` weight fix) together with its proved spectral gap
(`asymGappedTransfer'`, `ReflectionPositivity.GappedTransfer.susceptibility_le`).

The one missing theorem is the **Feynman–Kac trace dictionary**: the interacting measure's
time-correlations equal traces of powers of `asymTransferOperatorCLM`. Milestones B1–B5
(slice iso → Gaussian time-slice factorization → trace formula → `susceptibility_le` →
`1/a`-cancellation identification with `C·Var_free`) are scoped in
`docs/transfer-instantiation-plan.md` and `docs/layer-B2-discharge-plan.md`
("Feynman–Kac bridge — scoping"). B2 (the factorization) is the crux.

No declarations yet — this file imports the abstract bridge (`susceptibility_le` engine)
and the proved gap, and is the home for the B1–B5 trace dictionary.
-/

open MeasureTheory ReflectionPositivity GaussianField Real
open scoped BigOperators

namespace Pphi2

variable (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]

/-! ## B1 — slice structure: a spacetime field is a time-indexed family of spatial fields -/

/-- Currying a function on a product index into a function-of-functions, as a linear
equivalence. `(α × β → ℝ) ≃ₗ (α → β → ℝ)`. -/
def prodCurryLinearEquiv (α β : Type*) : (α × β → ℝ) ≃ₗ[ℝ] (α → β → ℝ) where
  toFun f a b := f (a, b)
  invFun g p := g p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **B1 slice equivalence.** A spacetime lattice field on `ZMod Nt × ZMod Ns` is the same
data as a time-indexed (`ZMod Nt`) family of spatial fields (`SpatialField Ns = Fin Ns → ℝ`).
Curry the time/space product index, then reindex the spatial `ZMod Ns` to `Fin Ns`. -/
noncomputable def asymSliceEquiv (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    AsymLatticeField Nt Ns ≃ₗ[ℝ] (ZMod Nt → SpatialField Ns) :=
  (prodCurryLinearEquiv (ZMod Nt) (ZMod Ns)).trans
    (LinearEquiv.piCongrRight fun _ =>
      LinearEquiv.funCongrLeft ℝ ℝ (ZMod.finEquiv Ns).toEquiv)

@[simp] theorem asymSliceEquiv_apply (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (φ : AsymLatticeField Nt Ns) (t : ZMod Nt) (x : Fin Ns) :
    asymSliceEquiv Nt Ns φ t x = φ (t, (ZMod.finEquiv Ns).toEquiv x) := rfl

/-! ## The asym transfer kernel and its `TransferSystem`

The single-time-slice state space is `SpatialField Ns = Fin Ns → ℝ` with Lebesgue `volume`;
the transfer kernel is `k(x,y) = w(x)·G(x−y)·w(y)` with `w = asymTransferWeight` (the
corrected `a²/2` weight) and `G = transferGaussian`. This is exactly the kernel of
`asymTransferOperatorCLM = M_w ∘ Conv_G ∘ M_w`, so `kPow` of this kernel are the kernels of
its powers — the bridge to the proved spectral gap. Instantiating `TransferSystem` gives the
periodic path measure and the Feynman–Kac trace dictionary off the shelf. -/

/-- The asym transfer kernel `k(x,y) = w(x)·G(x−y)·w(y)`. -/
noncomputable def asymTransferKernel (P : InteractionPolynomial) (a mass : ℝ) :
    SpatialField Ns → SpatialField Ns → ℝ :=
  fun x y => asymTransferWeight Nt Ns P a mass x * transferGaussian Ns (x - y) *
    asymTransferWeight Nt Ns P a mass y

theorem asymTransferKernel_symm (P : InteractionPolynomial) (a mass : ℝ) (x y : SpatialField Ns) :
    asymTransferKernel Nt Ns P a mass x y = asymTransferKernel Nt Ns P a mass y x := by
  unfold asymTransferKernel
  rw [transferGaussian_sub_comm Ns x y]; ring

theorem asymTransferKernel_nonneg (P : InteractionPolynomial) (a mass : ℝ)
    (x y : SpatialField Ns) : 0 ≤ asymTransferKernel Nt Ns P a mass x y := by
  unfold asymTransferKernel transferGaussian
  exact mul_nonneg (mul_nonneg (asymTransferWeight_pos Nt Ns P a mass x).le
    (Real.exp_pos _).le) (asymTransferWeight_pos Nt Ns P a mass y).le

theorem asymTransferKernel_measurable (P : InteractionPolynomial) (a mass : ℝ) :
    Measurable (Function.uncurry (asymTransferKernel Nt Ns P a mass)) := by
  unfold asymTransferKernel Function.uncurry
  exact (((asymTransferWeight_measurable Nt Ns P a mass).comp measurable_fst).mul
    ((continuous_transferGaussian Ns).measurable.comp
      (measurable_fst.sub measurable_snd))).mul
    ((asymTransferWeight_measurable Nt Ns P a mass).comp measurable_snd)


private theorem transferGaussian_le_one (z : SpatialField Ns) :
    transferGaussian Ns z ≤ 1 := by
  simpa [Real.norm_eq_abs, abs_of_pos (transferGaussian_pos Ns z)] using
    transferGaussian_norm_le_one Ns z

private theorem asymTransferKernel_le_weight_mul (P : InteractionPolynomial) (a mass : ℝ)
    (x y : SpatialField Ns) :
    asymTransferKernel Nt Ns P a mass x y ≤
      asymTransferWeight Nt Ns P a mass x * asymTransferWeight Nt Ns P a mass y := by
  have hG : transferGaussian Ns (x - y) ≤ 1 := transferGaussian_le_one Ns (x - y)
  have hx : 0 ≤ asymTransferWeight Nt Ns P a mass x :=
    (asymTransferWeight_pos Nt Ns P a mass x).le
  have hy : 0 ≤ asymTransferWeight Nt Ns P a mass y :=
    (asymTransferWeight_pos Nt Ns P a mass y).le
  have h :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG hx) hy
  simpa [asymTransferKernel, mul_assoc] using h

private theorem openChainDensity_asymTransferKernel_nonneg
    (P : InteractionPolynomial) (a mass : ℝ) (m : ℕ)
    (x y : SpatialField Ns) (q : Fin m → SpatialField Ns) :
    0 ≤ openChainDensity (asymTransferKernel Nt Ns P a mass) m x y q := by
  rw [← TransferSystem.openChainProduct_eq_density]
  exact Finset.prod_nonneg (fun i _ =>
    asymTransferKernel_nonneg Nt Ns P a mass
      (openChainVertices m x y q i.castSucc)
      (openChainVertices m x y q i.succ))

private theorem openChainDensity_asymTransferKernel_le_weight_mul_prod
    (P : InteractionPolynomial) (a mass : ℝ) :
    ∀ (m : ℕ) (x y : SpatialField Ns) (q : Fin m → SpatialField Ns),
      openChainDensity (asymTransferKernel Nt Ns P a mass) m x y q ≤
        asymTransferWeight Nt Ns P a mass x *
          asymTransferWeight Nt Ns P a mass y *
          ∏ j : Fin m, asymTransferWeight Nt Ns P a mass (q j) ^ 2
  | 0, x, y, q => by
      simpa [openChainDensity] using
        asymTransferKernel_le_weight_mul (Nt := Nt) (Ns := Ns) P a mass x y
  | m + 1, x, y, q => by
      let w := asymTransferWeight Nt Ns P a mass
      have hden :=
        openChainDensity_asymTransferKernel_le_weight_mul_prod P a mass m x
          (q (Fin.last m)) (Fin.init q)
      have hk :=
        asymTransferKernel_le_weight_mul (Nt := Nt) (Ns := Ns) P a mass (q (Fin.last m)) y
      have hk_nonneg :
          0 ≤ asymTransferKernel Nt Ns P a mass (q (Fin.last m)) y :=
        asymTransferKernel_nonneg Nt Ns P a mass (q (Fin.last m)) y
      have hdom_nonneg :
          0 ≤ w x * w (q (Fin.last m)) *
            ∏ j : Fin m, w (Fin.init q j) ^ 2 := by
        exact mul_nonneg
          (mul_nonneg (asymTransferWeight_pos Nt Ns P a mass x).le
            (asymTransferWeight_pos Nt Ns P a mass (q (Fin.last m))).le)
          (Finset.prod_nonneg (fun j _ => sq_nonneg _))
      have hmul := mul_le_mul hden hk hk_nonneg hdom_nonneg
      calc
        openChainDensity (asymTransferKernel Nt Ns P a mass) (m + 1) x y q
            ≤ (w x * w (q (Fin.last m)) *
                  ∏ j : Fin m, w (Fin.init q j) ^ 2) *
                (w (q (Fin.last m)) * w y) := by
              simpa [openChainDensity, w] using hmul
        _ = w x * w y * ∏ j : Fin (m + 1), w (q j) ^ 2 := by
              rw [Fin.prod_univ_castSucc]
              simp [Fin.init, w]
              ring

private theorem openChain_step_asymTransferKernel_le_dom
    (P : InteractionPolynomial) (a mass : ℝ) (m : ℕ)
    (x y z : SpatialField Ns) (q : Fin m → SpatialField Ns) :
    openChainDensity (asymTransferKernel Nt Ns P a mass) m x z q *
        asymTransferKernel Nt Ns P a mass z y ≤
      (asymTransferWeight Nt Ns P a mass x *
          asymTransferWeight Nt Ns P a mass y) *
        (asymTransferWeight Nt Ns P a mass z ^ 2 *
          ∏ j : Fin m, asymTransferWeight Nt Ns P a mass (q j) ^ 2) := by
  let w := asymTransferWeight Nt Ns P a mass
  have hden :=
    openChainDensity_asymTransferKernel_le_weight_mul_prod Nt Ns P a mass m x z q
  have hk := asymTransferKernel_le_weight_mul (Nt := Nt) (Ns := Ns) P a mass z y
  have hk_nonneg : 0 ≤ asymTransferKernel Nt Ns P a mass z y :=
    asymTransferKernel_nonneg Nt Ns P a mass z y
  have hdom_nonneg : 0 ≤ w x * w z * ∏ j : Fin m, w (q j) ^ 2 := by
    exact mul_nonneg
      (mul_nonneg (asymTransferWeight_pos Nt Ns P a mass x).le
        (asymTransferWeight_pos Nt Ns P a mass z).le)
      (Finset.prod_nonneg (fun j _ => sq_nonneg _))
  have hmul := mul_le_mul hden hk hk_nonneg hdom_nonneg
  calc
    openChainDensity (asymTransferKernel Nt Ns P a mass) m x z q *
        asymTransferKernel Nt Ns P a mass z y
        ≤ (w x * w z * ∏ j : Fin m, w (q j) ^ 2) * (w z * w y) := hmul
    _ = (w x * w y) * (w z ^ 2 * ∏ j : Fin m, w (q j) ^ 2) := by
      ring

private theorem openChainProduct_asymTransferKernel_le_dom
    (P : InteractionPolynomial) (a mass : ℝ) (m : ℕ)
    (x : SpatialField Ns) (q : Fin m → SpatialField Ns) :
    openChainProduct (asymTransferKernel Nt Ns P a mass) m x x q ≤
      asymTransferWeight Nt Ns P a mass x ^ 2 *
        ∏ j : Fin m, asymTransferWeight Nt Ns P a mass (q j) ^ 2 := by
  let w := asymTransferWeight Nt Ns P a mass
  calc
    openChainProduct (asymTransferKernel Nt Ns P a mass) m x x q =
        openChainDensity (asymTransferKernel Nt Ns P a mass) m x x q :=
          TransferSystem.openChainProduct_eq_density _ _ _ _ _
    _ ≤ w x * w x * ∏ j : Fin m, w (q j) ^ 2 :=
        openChainDensity_asymTransferKernel_le_weight_mul_prod Nt Ns P a mass
          m x x q
    _ = w x ^ 2 * ∏ j : Fin m, w (q j) ^ 2 := by
        ring


private theorem asymTransferKernel_measurable_apply
    {α : Type*} [MeasurableSpace α] (P : InteractionPolynomial) (a mass : ℝ)
    {f g : α → SpatialField Ns} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun t => asymTransferKernel Nt Ns P a mass (f t) (g t)) := by
  unfold asymTransferKernel
  exact (((asymTransferWeight_measurable Nt Ns P a mass).comp hf).mul
    ((continuous_transferGaussian Ns).measurable.comp (hf.sub hg))).mul
    ((asymTransferWeight_measurable Nt Ns P a mass).comp hg)

set_option maxHeartbeats 1000000 in
-- The recursive proof builds nested measurable maps on finite pi spaces.
private theorem openChainDensity_asymTransferKernel_measurable
    (P : InteractionPolynomial) (a mass : ℝ) (m : ℕ) :
    Measurable (fun p : SpatialField Ns × SpatialField Ns × (Fin m → SpatialField Ns) =>
      openChainDensity (asymTransferKernel Nt Ns P a mass) m p.1 p.2.1 p.2.2) := by
  induction m with
  | zero =>
      change Measurable
        (fun p : SpatialField Ns × SpatialField Ns × (Fin 0 → SpatialField Ns) =>
          asymTransferKernel Nt Ns P a mass p.1 p.2.1)
      exact asymTransferKernel_measurable_apply (Nt := Nt) (Ns := Ns) P a mass
        measurable_fst (measurable_fst.comp measurable_snd)
  | succ m ih =>
      have hq :
          Measurable
            (fun p : SpatialField Ns × SpatialField Ns × (Fin (m + 1) → SpatialField Ns) =>
              p.2.2 (Fin.last m)) :=
        (measurable_pi_apply (Fin.last m)).comp (measurable_snd.comp measurable_snd)
      have hinit :
          Measurable
            (fun p : SpatialField Ns × SpatialField Ns × (Fin (m + 1) → SpatialField Ns) =>
              Fin.init p.2.2) := by
        exact measurable_pi_lambda _ (fun i =>
          (measurable_pi_apply i.castSucc).comp (measurable_snd.comp measurable_snd))
      have hprev :
          Measurable
            (fun p : SpatialField Ns × SpatialField Ns × (Fin (m + 1) → SpatialField Ns) =>
              openChainDensity (asymTransferKernel Nt Ns P a mass) m
                p.1 (p.2.2 (Fin.last m)) (Fin.init p.2.2)) :=
        ih.comp (measurable_fst.prodMk (hq.prodMk hinit))
      have hlast :
          Measurable
            (fun p : SpatialField Ns × SpatialField Ns × (Fin (m + 1) → SpatialField Ns) =>
              asymTransferKernel Nt Ns P a mass (p.2.2 (Fin.last m)) p.2.1) :=
        asymTransferKernel_measurable_apply (Nt := Nt) (Ns := Ns) P a mass hq
          (measurable_fst.comp measurable_snd)
      change Measurable
        (fun p : SpatialField Ns × SpatialField Ns × (Fin (m + 1) → SpatialField Ns) =>
          openChainDensity (asymTransferKernel Nt Ns P a mass) m
              p.1 (p.2.2 (Fin.last m)) (Fin.init p.2.2) *
            asymTransferKernel Nt Ns P a mass (p.2.2 (Fin.last m)) p.2.1)
      exact hprev.mul hlast

set_option maxHeartbeats 1000000 in
-- This composes the recursive finite-pi measurability helper with product projections.
private theorem openChain_step_asymTransferKernel_measurable
    (P : InteractionPolynomial) (a mass : ℝ) (m : ℕ) (x y : SpatialField Ns) :
    Measurable (fun p : SpatialField Ns × (Fin m → SpatialField Ns) =>
      openChainDensity (asymTransferKernel Nt Ns P a mass) m x p.1 p.2 *
        asymTransferKernel Nt Ns P a mass p.1 y) := by
  have hden :
      Measurable (fun p : SpatialField Ns × (Fin m → SpatialField Ns) =>
        openChainDensity (asymTransferKernel Nt Ns P a mass) m x p.1 p.2) :=
    (openChainDensity_asymTransferKernel_measurable (Nt := Nt) (Ns := Ns) P a mass m).comp
      (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
  have hlast :
      Measurable (fun p : SpatialField Ns × (Fin m → SpatialField Ns) =>
        asymTransferKernel Nt Ns P a mass p.1 y) :=
    asymTransferKernel_measurable_apply (Nt := Nt) (Ns := Ns) P a mass
      measurable_fst measurable_const
  exact hden.mul hlast

set_option maxHeartbeats 1000000 in
-- This reuses the density measurability helper through `openChainProduct_eq_density`.
private theorem openChainProduct_asymTransferKernel_measurable
    (P : InteractionPolynomial) (a mass : ℝ) (m : ℕ) :
    Measurable (fun p : SpatialField Ns × (Fin m → SpatialField Ns) =>
      openChainProduct (asymTransferKernel Nt Ns P a mass) m p.1 p.1 p.2) := by
  have hden :
      Measurable (fun p : SpatialField Ns × (Fin m → SpatialField Ns) =>
        openChainDensity (asymTransferKernel Nt Ns P a mass) m p.1 p.1 p.2) :=
    (openChainDensity_asymTransferKernel_measurable (Nt := Nt) (Ns := Ns) P a mass m).comp
      (measurable_fst.prodMk (measurable_fst.prodMk measurable_snd))
  simpa only [TransferSystem.openChainProduct_eq_density] using hden

private theorem asymTransferWeight_sq_prod_integrable (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (m : ℕ) :
    Integrable
      (fun p : SpatialField Ns × (Fin m → SpatialField Ns) =>
        asymTransferWeight Nt Ns P a mass p.1 ^ 2 *
          ∏ j : Fin m, asymTransferWeight Nt Ns P a mass (p.2 j) ^ 2)
      (volume.prod (Measure.pi (fun _ : Fin m => volume))) := by
  let w := asymTransferWeight Nt Ns P a mass
  have hw_sq : Integrable (fun x : SpatialField Ns => w x ^ 2) volume :=
    (asymTransferWeight_memLp_two Nt Ns P a mass ha hmass).integrable_sq
  have hq : Integrable
      (fun q : Fin m → SpatialField Ns => ∏ j : Fin m, w (q j) ^ 2)
      (Measure.pi (fun _ : Fin m => volume)) := by
    exact MeasureTheory.Integrable.fintype_prod
      (μ := fun _ : Fin m => volume)
      (f := fun _ x => w x ^ 2)
      (fun _ => hw_sq)
  exact hw_sq.mul_prod hq

private theorem asymTransferWeight_step_dom_integrable
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) (x y : SpatialField Ns) :
    Integrable
      (fun p : SpatialField Ns × (Fin m → SpatialField Ns) =>
        (asymTransferWeight Nt Ns P a mass x *
          asymTransferWeight Nt Ns P a mass y) *
          (asymTransferWeight Nt Ns P a mass p.1 ^ 2 *
            ∏ j : Fin m, asymTransferWeight Nt Ns P a mass (p.2 j) ^ 2))
      (volume.prod (Measure.pi (fun _ : Fin m => volume))) :=
  (asymTransferWeight_sq_prod_integrable (Nt := Nt) (Ns := Ns) P a mass ha hmass m).const_mul
    (asymTransferWeight Nt Ns P a mass x * asymTransferWeight Nt Ns P a mass y)

/-- The asym φ⁴₂ cylinder packaged as a `TransferSystem` on the spatial slice space. -/
noncomputable def asymTransferSystem (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) : TransferSystem (SpatialField Ns) where
  ν := volume
  k := asymTransferKernel Nt Ns P a mass
  k_symm := asymTransferKernel_symm Nt Ns P a mass
  k_nonneg := asymTransferKernel_nonneg Nt Ns P a mass
  k_meas := asymTransferKernel_measurable Nt Ns P a mass
  ν_sigmaFinite := inferInstance
  openChain_step_integrable := by
    intro m x y
    refine (asymTransferWeight_step_dom_integrable (Nt := Nt) (Ns := Ns)
      P a mass ha hmass m x y).mono_nonneg
      (openChain_step_asymTransferKernel_measurable (Nt := Nt) (Ns := Ns)
        P a mass m x y).aestronglyMeasurable
      (ae_of_all _ (fun p => ?_)) (ae_of_all _ (fun p => ?_))
    · exact mul_nonneg
        (openChainDensity_asymTransferKernel_nonneg (Nt := Nt) (Ns := Ns)
          P a mass m x p.1 p.2)
        (asymTransferKernel_nonneg Nt Ns P a mass p.1 y)
    · exact openChain_step_asymTransferKernel_le_dom (Nt := Nt) (Ns := Ns)
        P a mass m x y p.1 p.2
  partition_integrable := by
    intro m
    refine (asymTransferWeight_sq_prod_integrable (Nt := Nt) (Ns := Ns)
      P a mass ha hmass m).mono_nonneg
      (openChainProduct_asymTransferKernel_measurable (Nt := Nt) (Ns := Ns)
        P a mass m).aestronglyMeasurable
      (ae_of_all _ (fun p => ?_)) (ae_of_all _ (fun p => ?_))
    · rw [TransferSystem.openChainProduct_eq_density]
      exact openChainDensity_asymTransferKernel_nonneg (Nt := Nt) (Ns := Ns)
        P a mass m p.1 p.1 p.2
    · exact openChainProduct_asymTransferKernel_le_dom (Nt := Nt) (Ns := Ns)
        P a mass m p.1 p.2
  pathDensity_measurable := by
    intro n _
    unfold periodicPathDensity asymTransferKernel
    refine Finset.measurable_prod _ (fun t _ => ?_)
    have hw := asymTransferWeight_measurable Nt Ns P a mass
    exact ((hw.comp (measurable_pi_apply t)).mul
      ((continuous_transferGaussian Ns).measurable.comp
        ((measurable_pi_apply t).sub (measurable_pi_apply (t + 1))))).mul
      (hw.comp (measurable_pi_apply (t + 1)))

end Pphi2
