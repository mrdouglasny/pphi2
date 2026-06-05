/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.AsymTorus.AsymTransferInstantiation

/-!
# The asym transfer operator as an integral operator

`asymTransferOperatorCLM = M_w ∘ Conv_G ∘ M_w` is the integral operator with kernel
`asymTransferKernel x y = w(x) · G(x−y) · w(y)`. This file proves:

* `asymTransferOperatorCLM_apply` — the integral-operator form
  `(T f)(x) =ᵐ ∫ y, asymTransferKernel x y · f y dy`.
* `asymTransferKernel_kPow_apply` — `(Tᵐ⁺¹ f)(x) =ᵐ ∫ y, kPow m x y · f y dy`, i.e. the
  iterated kernels `TransferSystem.kPow` are the kernels of the operator powers. Proved by
  induction on `m` from theorem 1 and Fubini (`integral_integral_swap`).

The single change-of-variables in theorem 1 is `integral_sub_left_eq_self`
(`∫ t, F (x − t) = ∫ t, F t`, valid for the add-left-invariant Lebesgue `volume` on
`SpatialField Ns = Fin Ns → ℝ`), applied to `F t = G (x − t) · w t · f t`.
-/

open MeasureTheory ReflectionPositivity GaussianField Real
open scoped BigOperators Convolution

namespace Pphi2

variable (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]

/-- The asym transfer operator is the integral operator with kernel `asymTransferKernel`:
`(T f)(x) =ᵐ ∫ y, asymTransferKernel x y · f y dy`. -/
theorem asymTransferOperatorCLM_apply (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (f : L2SpatialField Ns) :
    (⇑(asymTransferOperatorCLM Nt Ns P a mass ha hmass f) : SpatialField Ns → ℝ) =ᵐ[volume]
      (fun x => ∫ y, asymTransferKernel Nt Ns P a mass x y * f y ∂volume) := by
  classical
  set w := asymTransferWeight Nt Ns P a mass with hw_def
  set G := transferGaussian Ns with hG_def
  set hw_meas := asymTransferWeight_measurable Nt Ns P a mass with hwm_def
  set C := (asymTransferWeight_bound Nt Ns P a mass ha hmass).choose with hC_def
  set hC := (asymTransferWeight_bound Nt Ns P a mass ha hmass).choose_spec.1 with hCpos_def
  set hw_bound := (asymTransferWeight_bound Nt Ns P a mass ha hmass).choose_spec.2 with hwb_def
  set hG := transferGaussian_memLp Ns with hGmem_def
  -- Unfold the factorization `T = M_w ∘ Conv_G ∘ M_w`.
  have hT : asymTransferOperatorCLM Nt Ns P a mass ha hmass f
      = mulCLM w hw_meas C hC hw_bound (convCLM G hG (mulCLM w hw_meas C hC hw_bound f)) := rfl
  rw [hT]
  -- Step 1: outer multiplication.
  have h1 : (⇑(mulCLM w hw_meas C hC hw_bound
      (convCLM G hG (mulCLM w hw_meas C hC hw_bound f))) : SpatialField Ns → ℝ) =ᵐ[volume]
      fun x => w x * (convCLM G hG (mulCLM w hw_meas C hC hw_bound f)) x :=
    mulCLM_spec w hw_meas C hC hw_bound _
  -- Step 2: inner convolution acts as `realConv`.
  have h2 : (⇑(convCLM G hG (mulCLM w hw_meas C hC hw_bound f)) : SpatialField Ns → ℝ) =ᵐ[volume]
      realConv volume G ⇑(mulCLM w hw_meas C hC hw_bound f) :=
    convCLM_spec G hG _
  -- Step 3: the inner multiplication argument equals `w · f` a.e.
  have h3 : (⇑(mulCLM w hw_meas C hC hw_bound f) : SpatialField Ns → ℝ) =ᵐ[volume]
      fun y => w y * f y :=
    mulCLM_spec w hw_meas C hC hw_bound f
  -- Combine: replace the convolution argument by `w · f` (Haar-invariance gives plain congr).
  have h2' : (⇑(convCLM G hG (mulCLM w hw_meas C hC hw_bound f)) : SpatialField Ns → ℝ) =ᵐ[volume]
      realConv volume G (fun y => w y * f y) := by
    refine h2.trans ?_
    have : realConv volume G ⇑(mulCLM w hw_meas C hC hw_bound f)
        = realConv volume G (fun y => w y * f y) :=
      convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) (.refl _ _) h3
    rw [this]
  -- Now compute the realConv pointwise as an integral and change variables.
  refine h1.trans ?_
  filter_upwards [h2'] with x hx
  rw [hx]
  -- realConv volume G (w·f) x = ∫ t, G t * (w (x−t) * f (x−t)) dt
  have hconv : realConv volume G (fun y => w y * f y) x
      = ∫ t, G t * (w (x - t) * (f (x - t))) ∂volume := by
    simp only [realConv, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [hconv]
  -- Change variables `t ↦ x − t` via `integral_sub_left_eq_self` applied to
  -- `F t = G (x − t) * (w t * f t)`.  Then `(F (x − ·))` has `G (x − (x − t)) = G t`, so its
  -- integral is the convolution integrand; the RHS is the kernel form.
  have hcov := integral_sub_left_eq_self
      (fun t => G (x - t) * (w t * (f t))) (volume : Measure (SpatialField Ns)) x
  simp only [sub_sub_cancel] at hcov
  -- hcov : (∫ t, G t * (w (x−t) * f (x−t))) = ∫ t, G (x−t) * (w t * f t)
  rw [hcov, ← integral_const_mul]
  -- Now `∫ t, w x * (G (x−t) * (w t * f t))`; reshape into the kernel form.
  refine integral_congr_ae (.of_forall (fun y => ?_))
  unfold asymTransferKernel
  ring

/-! ## Iterated kernels are the kernels of the operator powers -/

section KPow

variable (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)

private theorem transferGaussian_le_one' (z : SpatialField Ns) :
    transferGaussian Ns z ≤ 1 := by
  simpa [Real.norm_eq_abs, abs_of_pos (transferGaussian_pos Ns z)] using
    transferGaussian_norm_le_one Ns z

/-- `k z y ≤ w z · w y`, since `transferGaussian ≤ 1` and the weights are nonnegative. -/
private theorem asymTransferKernel_le_weight (z y : SpatialField Ns) :
    asymTransferKernel Nt Ns P a mass z y
      ≤ asymTransferWeight Nt Ns P a mass z * asymTransferWeight Nt Ns P a mass y := by
  unfold asymTransferKernel
  have hz : 0 ≤ asymTransferWeight Nt Ns P a mass z := (asymTransferWeight_pos Nt Ns P a mass z).le
  have hy : 0 ≤ asymTransferWeight Nt Ns P a mass y := (asymTransferWeight_pos Nt Ns P a mass y).le
  have hG : transferGaussian Ns (z - y) ≤ 1 := transferGaussian_le_one' Ns (z - y)
  calc asymTransferWeight Nt Ns P a mass z * transferGaussian Ns (z - y)
          * asymTransferWeight Nt Ns P a mass y
        ≤ asymTransferWeight Nt Ns P a mass z * 1 * asymTransferWeight Nt Ns P a mass y := by
          gcongr
    _ = _ := by ring

/-- The "single-slice" L² mass constant `Wsq := ∫ w² ` and `Cm := Wsq ^ m`. -/
private noncomputable def Wsq : ℝ := ∫ z, asymTransferWeight Nt Ns P a mass z ^ 2 ∂volume

private theorem Wsq_nonneg : 0 ≤ Wsq Nt Ns P a mass :=
  integral_nonneg (fun _ => sq_nonneg _)

/-- A uniform Gaussian-product bound on the iterated kernel:
`kPow m x y ≤ Wsq^m · w x · w y`. By induction on `m`, dominating each transfer step's
`∫ w² ` factor. -/
private theorem asymTransferKernel_kPow_le (m : ℕ) (x y : SpatialField Ns) :
    (asymTransferSystem Nt Ns P a mass ha hmass).kPow m x y
      ≤ (Wsq Nt Ns P a mass) ^ m * asymTransferWeight Nt Ns P a mass x
          * asymTransferWeight Nt Ns P a mass y := by
  set Ts := asymTransferSystem Nt Ns P a mass ha hmass with hTs
  have hk : Ts.k = asymTransferKernel Nt Ns P a mass := rfl
  have hν : Ts.ν = (volume : Measure (SpatialField Ns)) := rfl
  set W := asymTransferWeight Nt Ns P a mass with hW
  have hW_nonneg : ∀ u, 0 ≤ W u := fun u => (asymTransferWeight_pos Nt Ns P a mass u).le
  have hw_sq : Integrable (fun z => W z ^ 2) volume :=
    (asymTransferWeight_memLp_two Nt Ns P a mass ha hmass).integrable_sq
  induction m generalizing y with
  | zero =>
      simp only [pow_zero, one_mul]
      rw [TransferSystem.kPow_zero, hk]
      exact asymTransferKernel_le_weight Nt Ns P a mass x y
  | succ m ih =>
      rw [TransferSystem.kPow_succ, hν]
      -- ∫ z, kPow m x z * k z y ≤ ∫ z, (Wsq^m W x W z)*(W z W y) = Wsq^(m+1) W x W y
      have hbound : ∀ z, Ts.kPow m x z * Ts.k z y
          ≤ ((Wsq Nt Ns P a mass) ^ m * W x) * (W z ^ 2 * W y) := by
        intro z
        have h1 : Ts.kPow m x z ≤ (Wsq Nt Ns P a mass) ^ m * W x * W z := ih z
        have h2 : Ts.k z y ≤ W z * W y := by
          rw [hk]; exact asymTransferKernel_le_weight Nt Ns P a mass z y
        have hk_nonneg : 0 ≤ Ts.k z y := by
          rw [hk]; exact asymTransferKernel_nonneg Nt Ns P a mass z y
        have hdom_nonneg : 0 ≤ (Wsq Nt Ns P a mass) ^ m * W x * W z :=
          mul_nonneg (mul_nonneg (pow_nonneg (Wsq_nonneg Nt Ns P a mass) m) (hW_nonneg x))
            (hW_nonneg z)
        calc Ts.kPow m x z * Ts.k z y
              ≤ ((Wsq Nt Ns P a mass) ^ m * W x * W z) * (W z * W y) :=
                mul_le_mul h1 h2 hk_nonneg hdom_nonneg
          _ = ((Wsq Nt Ns P a mass) ^ m * W x) * (W z ^ 2 * W y) := by ring
      have hdom_int : Integrable
          (fun z => ((Wsq Nt Ns P a mass) ^ m * W x) * (W z ^ 2 * W y)) volume := by
        have : Integrable (fun z => W z ^ 2 * W y) volume := hw_sq.mul_const _
        exact this.const_mul _
      calc ∫ z, Ts.kPow m x z * Ts.k z y ∂volume
            ≤ ∫ z, ((Wsq Nt Ns P a mass) ^ m * W x) * (W z ^ 2 * W y) ∂volume :=
              integral_mono_of_nonneg
                (.of_forall (fun z => mul_nonneg (Ts.kPow_nonneg m x z)
                  (by rw [hk]; exact asymTransferKernel_nonneg Nt Ns P a mass z y)))
                hdom_int (.of_forall hbound)
        _ = ((Wsq Nt Ns P a mass) ^ m * W x * W y) *
              ∫ z, W z ^ 2 ∂volume := by
              rw [← integral_const_mul]; congr 1; ext z; ring
        _ = (Wsq Nt Ns P a mass) ^ (m + 1) * W x * W y := by
              rw [show (∫ z, W z ^ 2 ∂volume) = Wsq Nt Ns P a mass from rfl]; ring

/-- The iterated kernel `kPow m x ·` is measurable in its second argument. By induction on
`m`, using that a parametric integral of a measurable integrand is measurable. -/
private theorem asymTransferKernel_kPow_measurable (m : ℕ) (x : SpatialField Ns) :
    Measurable (fun y => (asymTransferSystem Nt Ns P a mass ha hmass).kPow m x y) := by
  set Ts := asymTransferSystem Nt Ns P a mass ha hmass with hTs
  have hk : Ts.k = asymTransferKernel Nt Ns P a mass := rfl
  have hν : Ts.ν = (volume : Measure (SpatialField Ns)) := rfl
  have hk_unc : Measurable (Function.uncurry (asymTransferKernel Nt Ns P a mass)) :=
    asymTransferKernel_measurable Nt Ns P a mass
  induction m with
  | zero =>
      rw [TransferSystem.kPow_zero, hk]
      have : (fun y => asymTransferKernel Nt Ns P a mass x y)
          = Function.uncurry (asymTransferKernel Nt Ns P a mass) ∘ (fun y => (x, y)) := rfl
      rw [this]
      exact hk_unc.comp (measurable_const.prodMk measurable_id)
  | succ m ih =>
      have hint : Measurable (Function.uncurry
          (fun y z => Ts.kPow m x z * asymTransferKernel Nt Ns P a mass z y)) := by
        have h1 : Measurable (fun p : SpatialField Ns × SpatialField Ns => Ts.kPow m x p.2) :=
          ih.comp measurable_snd
        have h2 : Measurable (fun p : SpatialField Ns × SpatialField Ns =>
            asymTransferKernel Nt Ns P a mass p.2 p.1) := by
          have he : (fun p : SpatialField Ns × SpatialField Ns =>
              asymTransferKernel Nt Ns P a mass p.2 p.1)
              = Function.uncurry (asymTransferKernel Nt Ns P a mass)
                ∘ (fun p => (p.2, p.1)) := rfl
          rw [he]
          exact hk_unc.comp (measurable_snd.prodMk measurable_fst)
        exact h1.mul h2
      have hmeas : Measurable
          (fun y => ∫ z, Ts.kPow m x z * asymTransferKernel Nt Ns P a mass z y
            ∂(volume : Measure (SpatialField Ns))) :=
        (hint.stronglyMeasurable.integral_prod_right').measurable
      have hsucc : (fun y => Ts.kPow (m + 1) x y)
          = (fun y => ∫ z, Ts.kPow m x z * asymTransferKernel Nt Ns P a mass z y
            ∂(volume : Measure (SpatialField Ns))) := by
        funext y; rw [TransferSystem.kPow_succ, hk, hν]
      rw [hsucc]; exact hmeas

/-- The Fubini integrand for the kernel-composition step,
`(y, z) ↦ kPow m x y · k y z · f z`, is integrable on `volume.prod volume`.

Domination: `|kPow m x y · k y z · f z| ≤ (Wsq^m · w x · w y²) · (w z · |f z|)`, a product of
a function of `y` (integrable: `w² ∈ L¹`) and a function of `z` (integrable: `w · |f| ∈ L¹`
by Cauchy–Schwarz, both `L²`), hence integrable on the product (`Integrable.mul_prod`). -/
private theorem asymTransferKernel_kPow_fubini_integrable (m : ℕ) (x : SpatialField Ns)
    (f : L2SpatialField Ns) :
    Integrable (Function.uncurry (fun y z =>
        (asymTransferSystem Nt Ns P a mass ha hmass).kPow m x y
          * asymTransferKernel Nt Ns P a mass y z * f z))
      ((volume : Measure (SpatialField Ns)).prod volume) := by
  set Ts := asymTransferSystem Nt Ns P a mass ha hmass with hTs
  set W := asymTransferWeight Nt Ns P a mass with hW
  have hW_nonneg : ∀ u, 0 ≤ W u := fun u => (asymTransferWeight_pos Nt Ns P a mass u).le
  have hkpow_nonneg : ∀ y, 0 ≤ Ts.kPow m x y := fun y => Ts.kPow_nonneg m x y
  have hk_nonneg : ∀ y z, 0 ≤ asymTransferKernel Nt Ns P a mass y z :=
    fun y z => asymTransferKernel_nonneg Nt Ns P a mass y z
  -- L² facts.
  have hw2 : MemLp W 2 volume := asymTransferWeight_memLp_two Nt Ns P a mass ha hmass
  have hw_sq_int : Integrable (fun z => W z ^ 2) volume := hw2.integrable_sq
  -- Per-factor dominators.
  set Cm := (Wsq Nt Ns P a mass) ^ m with hCm
  have hCm_nonneg : 0 ≤ Cm := pow_nonneg (Wsq_nonneg Nt Ns P a mass) m
  -- `domY y = Cm · W x · W y²`, `domZ z = W z · |f z|`.
  have hdomY_int : Integrable (fun y => Cm * W x * W y ^ 2) volume :=
    hw_sq_int.const_mul _
  have hwf_int : Integrable (fun z => W z * (f z)) volume :=
    hw2.integrable_mul (Lp.memLp f)
  have hdomZ_int : Integrable (fun z => W z * |f z|) volume := by
    have : (fun z => W z * |f z|) = (fun z => |W z * (f z)|) := by
      funext z; rw [abs_mul, abs_of_nonneg (hW_nonneg z)]
    rw [this]; exact hwf_int.abs
  -- Product dominator integrable on the product measure.
  have hdom_int : Integrable
      (fun p : SpatialField Ns × SpatialField Ns =>
        (Cm * W x * W p.1 ^ 2) * (W p.2 * |f p.2|))
      (volume.prod volume) :=
    hdomY_int.mul_prod hdomZ_int
  -- AEStronglyMeasurable of the integrand on the product.
  have hf_aesm : AEStronglyMeasurable (⇑f) (volume : Measure (SpatialField Ns)) :=
    Lp.aestronglyMeasurable f
  have hkpow_meas : Measurable (fun y => Ts.kPow m x y) :=
    asymTransferKernel_kPow_measurable Nt Ns P a mass ha hmass m x
  have hk_unc : Measurable (Function.uncurry (asymTransferKernel Nt Ns P a mass)) :=
    asymTransferKernel_measurable Nt Ns P a mass
  have hintegrand_aesm : AEStronglyMeasurable
      (Function.uncurry (fun y z => Ts.kPow m x y * asymTransferKernel Nt Ns P a mass y z * f z))
      (volume.prod volume) := by
    have h1 : Measurable (fun p : SpatialField Ns × SpatialField Ns => Ts.kPow m x p.1) :=
      hkpow_meas.comp measurable_fst
    have h2 : Measurable (fun p : SpatialField Ns × SpatialField Ns =>
        asymTransferKernel Nt Ns P a mass p.1 p.2) :=
      hk_unc.comp (measurable_fst.prodMk measurable_snd)
    have h3 : AEStronglyMeasurable (fun p : SpatialField Ns × SpatialField Ns => f p.2)
        (volume.prod volume) :=
      hf_aesm.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_snd)
    exact ((h1.mul h2).aestronglyMeasurable.mul h3)
  -- Dominate.
  refine hdom_int.mono' hintegrand_aesm (.of_forall (fun p => ?_))
  -- ‖kPow m x y · k y z · f z‖ ≤ (Cm W x W y²)(W z |f z|).
  obtain ⟨y, z⟩ := p
  simp only [Function.uncurry_apply_pair]
  have hkpow_le : Ts.kPow m x y ≤ Cm * W x * W y := by
    have := asymTransferKernel_kPow_le Nt Ns P a mass ha hmass m x y
    simpa only [hCm, hW] using this
  have hk_le : asymTransferKernel Nt Ns P a mass y z ≤ W y * W z := by
    have := asymTransferKernel_le_weight Nt Ns P a mass y z
    simpa only [hW] using this
  rw [Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (hkpow_nonneg y), abs_of_nonneg (hk_nonneg y z)]
  -- kPow m x y · k y z · |f z| ≤ (Cm W x W y) · (W y W z) · |f z| = (Cm W x W y²)(W z |f z|).
  calc Ts.kPow m x y * asymTransferKernel Nt Ns P a mass y z * |f z|
        ≤ (Cm * W x * W y) * (W y * W z) * |f z| := by
          have hprod : Ts.kPow m x y * asymTransferKernel Nt Ns P a mass y z
              ≤ (Cm * W x * W y) * (W y * W z) :=
            mul_le_mul hkpow_le hk_le (hk_nonneg y z)
              (mul_nonneg (mul_nonneg hCm_nonneg (hW_nonneg x)) (hW_nonneg y))
          exact mul_le_mul_of_nonneg_right hprod (abs_nonneg _)
    _ = (Cm * W x * W y ^ 2) * (W z * |f z|) := by ring

end KPow

/-- **Iterated kernels are the kernels of operator powers.** For each `m`, the `(m+1)`-th power
of the transfer operator is the integral operator with kernel `kPow m`:
`(Tᵐ⁺¹ f)(x) =ᵐ ∫ y, kPow m x y · f y dy`. Proved by induction on `m` from
`asymTransferOperatorCLM_apply` (theorem 1) and Fubini for the kernel-composition step. -/
theorem asymTransferKernel_kPow_apply (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (m : ℕ) (f : L2SpatialField Ns) :
    (⇑(((asymTransferOperatorCLM Nt Ns P a mass ha hmass) ^ (m + 1)) f)
        : SpatialField Ns → ℝ) =ᵐ[volume]
      (fun x => ∫ y, (asymTransferSystem Nt Ns P a mass ha hmass).kPow m x y * f y ∂volume) := by
  induction m generalizing f with
  | zero =>
      -- T¹ = T, and kPow 0 = k = asymTransferKernel.
      rw [pow_one]
      refine (asymTransferOperatorCLM_apply Nt Ns P a mass ha hmass f).trans ?_
      refine .of_forall (fun x => ?_)
      refine integral_congr_ae (.of_forall (fun y => ?_))
      rw [show (asymTransferSystem Nt Ns P a mass ha hmass).kPow 0
          = asymTransferKernel Nt Ns P a mass from rfl]
  | succ m ih =>
      -- T^(m+2) f = T^(m+1) (T f).
      have hstep : ((asymTransferOperatorCLM Nt Ns P a mass ha hmass) ^ (m + 1 + 1)) f
          = ((asymTransferOperatorCLM Nt Ns P a mass ha hmass) ^ (m + 1))
              ((asymTransferOperatorCLM Nt Ns P a mass ha hmass) f) := by
        rw [pow_succ]; rfl
      rw [hstep]
      -- Apply IH to `T f`, then expand `T f` via theorem 1, then Fubini.
      set Tf := (asymTransferOperatorCLM Nt Ns P a mass ha hmass) f with hTf
      -- IH on Tf : (T^(m+1) Tf) x =ᵐ ∫ y, kPow m x y * Tf y dy.
      have hIH := ih Tf
      refine hIH.trans ?_
      -- Replace `Tf y` by `∫ z, k y z * f z dz` inside the integral (a.e. in y), then swap.
      have hTf_eq : (⇑Tf : SpatialField Ns → ℝ) =ᵐ[volume]
          fun y => ∫ z, asymTransferKernel Nt Ns P a mass y z * f z ∂volume :=
        asymTransferOperatorCLM_apply Nt Ns P a mass ha hmass f
      refine .of_forall (fun x => ?_)
      simp only []
      -- ∫ y, kPow m x y * Tf y  =  ∫ y, kPow m x y * (∫ z, k y z * f z)
      have hinner : (∫ y, (asymTransferSystem Nt Ns P a mass ha hmass).kPow m x y * Tf y ∂volume)
          = ∫ y, (asymTransferSystem Nt Ns P a mass ha hmass).kPow m x y
              * (∫ z, asymTransferKernel Nt Ns P a mass y z * f z ∂volume) ∂volume := by
        refine integral_congr_ae ?_
        filter_upwards [hTf_eq] with y hy
        rw [hy]
      rw [hinner]
      -- Pull the constant `kPow m x y` into the z-integral.
      have hpull : (∫ y, (asymTransferSystem Nt Ns P a mass ha hmass).kPow m x y
              * (∫ z, asymTransferKernel Nt Ns P a mass y z * f z ∂volume) ∂volume)
          = ∫ y, ∫ z, (asymTransferSystem Nt Ns P a mass ha hmass).kPow m x y
              * asymTransferKernel Nt Ns P a mass y z * f z ∂volume ∂volume := by
        refine integral_congr_ae (.of_forall (fun y => ?_))
        simp only []
        rw [← integral_const_mul]
        refine integral_congr_ae (.of_forall (fun z => ?_)); ring
      rw [hpull]
      -- Fubini swap.
      have hfub := MeasureTheory.integral_integral_swap
        (asymTransferKernel_kPow_fubini_integrable Nt Ns P a mass ha hmass m x f)
      rw [hfub]
      -- ∫ z, (∫ y, kPow m x y * k y z dy) * f z = ∫ z, kPow (m+1) x z * f z.
      refine integral_congr_ae (.of_forall (fun z => ?_))
      simp only []
      rw [show (asymTransferSystem Nt Ns P a mass ha hmass).kPow (m + 1) x z
          = ∫ y, (asymTransferSystem Nt Ns P a mass ha hmass).kPow m x y
              * asymTransferKernel Nt Ns P a mass y z ∂volume from by
        rw [TransferSystem.kPow_succ]; rfl]
      rw [← integral_mul_const]

end Pphi2
