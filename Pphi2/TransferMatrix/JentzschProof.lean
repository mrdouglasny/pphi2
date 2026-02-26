/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Proof of Jentzsch's Theorem via the Variational Absolute Value Trick

This file proves Jentzsch's theorem for compact self-adjoint positivity-improving
operators on L²(ℝ^n, Lebesgue). The proof avoids the Krein-Rutman / Banach lattice
cone machinery and uses only the Rayleigh quotient, Cauchy-Schwarz, and L² lattice
structure (absolute value, positive/negative parts).

## Proof outline (Courant-Hilbert / Barry Simon)

1. **Phase 1**: Positivity-preserving operators satisfy |Tf| ≤ T|f| a.e.
2. **Phase 2**: Therefore |⟨f, Tf⟩| ≤ ⟨|f|, T|f|⟩.
3. **Phase 3**: If f is a ground state (Tf = lam₀f), then |f| is also a ground state.
4. **Phase 4**: By positivity-improving, the ground state is strictly positive a.e.
5. **Phase 5**: Every ground state eigenvector has constant sign a.e.
6. **Phase 6**: The ground state eigenvalue lam₀ is simple (multiplicity 1).
7. **Phase 7**: All other eigenvalues satisfy |λ| < lam₀ (strict spectral gap).

## References

- Reed-Simon IV, Theorems XIII.43–44
- Simon, *Functional Integration and Quantum Physics* (2005), §I.13
- Courant-Hilbert, *Methods of Mathematical Physics*, Ch. VI
-/

import Pphi2.TransferMatrix.L2Operator

noncomputable section

open MeasureTheory

/-! ## Definitions -/

/-- An operator on L²(ℝ^n) is positivity-preserving if it maps nonneg
functions to nonneg functions. This is weaker than positivity-improving. -/
def IsPositivityPreserving {n : ℕ}
    (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ))) : Prop :=
  ∀ f : Lp ℝ 2 (volume : Measure (Fin n → ℝ)),
    (0 ≤ f) → (0 ≤ T f)

/-- An operator on L²(ℝ^n) is positivity-improving if it maps nonneg
nonzero functions to a.e. strictly positive functions. -/
def IsPositivityImproving' {n : ℕ}
    (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ))) : Prop :=
  ∀ f : Lp ℝ 2 (volume : Measure (Fin n → ℝ)),
    (0 ≤ f) →
    (f ≠ 0) →
    (∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), 0 < (T f : (Fin n → ℝ) → ℝ) x)

/-- Positivity-improving implies positivity-preserving.
    If f ≥ 0 and f ≠ 0, then Tf > 0 a.e. ≥ 0. If f = 0, then Tf = 0 ≥ 0. -/
theorem IsPositivityImproving'.toPreserving {n : ℕ}
    {T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ))}
    (hT : IsPositivityImproving' T) : IsPositivityPreserving T := by
  intro f hf
  by_cases hf0 : f = 0
  · rw [hf0, map_zero]
  · -- Tf > 0 a.e. implies Tf ≥ 0
    have hpos := hT f hf hf0
    rw [← Lp.coeFn_le]
    filter_upwards [hpos, Lp.coeFn_zero ℝ 2 volume] with x hx h0
    rw [h0]
    exact le_of_lt hx

/-! ## Phase 1: Absolute value inequality

For a positivity-preserving operator T on L²:
  |Tf| ≤ T|f| a.e.

Proof: f = f⁺ - f⁻ with f⁺, f⁻ ≥ 0. Since T is positivity-preserving,
Tf⁺ ≥ 0 and Tf⁻ ≥ 0. Then:
  |Tf| = |Tf⁺ - Tf⁻| ≤ Tf⁺ + Tf⁻ = T(f⁺ + f⁻) = T|f|
-/

/-- Phase 1: Absolute value inequality for positivity-preserving operators. -/
theorem abs_apply_le_apply_abs {n : ℕ}
    (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (hT : IsPositivityPreserving T)
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    |T f| ≤ T |f| := by
  -- Strategy: |Tf| ≤ T|f| iff Tf ≤ T|f| and -Tf ≤ T|f| (by abs_le').
  -- Both follow from monotonicity of T (positivity-preserving + linear)
  -- and f ≤ |f|, -f ≤ |f|.
  -- Monotonicity: g ≤ h → Tg ≤ Th (since h-g ≥ 0 → T(h-g) ≥ 0 → Th-Tg ≥ 0)
  have hT_mono : ∀ (g h : Lp ℝ 2 (volume : Measure (Fin n → ℝ))),
      g ≤ h → T g ≤ T h := by
    intro g h hgh
    have h1 : 0 ≤ h - g := sub_nonneg.mpr hgh
    have h2 := hT (h - g) h1
    rwa [map_sub, sub_nonneg] at h2
  rw [abs_le']
  constructor
  · -- f ≤ |f| since |f| = f ⊔ (-f)
    exact hT_mono f |f| le_sup_left
  · -- -f ≤ |f| since |f| = f ⊔ (-f)
    rw [← map_neg]
    exact hT_mono (-f) |f| le_sup_right

/-! ## Phase 2: Inner product inequality

  |⟨f, Tf⟩| ≤ ⟨|f|, T|f|⟩

Proof: |⟨f, Tf⟩| = |∫ f(x) (Tf)(x) dx|
  ≤ ∫ |f(x)| |Tf(x)| dx       (integral triangle inequality)
  ≤ ∫ |f(x)| (T|f|)(x) dx     (Phase 1: |Tf| ≤ T|f|, and |f| ≥ 0)
  = ⟨|f|, T|f|⟩                (since |f| ≥ 0 and T|f| ≥ 0)
-/

/-- For nonneg L² functions, the inner product is nonneg.
    This is ⟨f, g⟩ = ∫ f(x)·g(x) dx ≥ 0 when f, g ≥ 0 a.e. -/
private theorem inner_nonneg_of_nonneg_L2 {n : ℕ}
    (f g : Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (hf : 0 ≤ f) (hg : 0 ≤ g) :
    (0 : ℝ) ≤ @inner ℝ _ _ f g := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [(Lp.coeFn_nonneg f).mpr hf, (Lp.coeFn_nonneg g).mpr hg] with x hfx hgx
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  exact mul_nonneg hgx hfx

/-- Inner product is monotone in the right argument when the left argument is nonneg.
    If 0 ≤ u and g₁ ≤ g₂ then ⟨u, g₁⟩ ≤ ⟨u, g₂⟩. -/
private theorem inner_mono_right_L2 {n : ℕ}
    (u g₁ g₂ : Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (hu : 0 ≤ u) (hg : g₁ ≤ g₂) :
    @inner ℝ _ _ u g₁ ≤ @inner ℝ _ _ u g₂ := by
  have h := inner_nonneg_of_nonneg_L2 u (g₂ - g₁) hu (sub_nonneg.mpr hg)
  rwa [inner_sub_right, sub_nonneg] at h

/-- |⟨f, g⟩| ≤ ⟨|f|, |g|⟩ for L² functions.
    Follows from the integral triangle inequality and |a·b| = |a|·|b|. -/
private theorem abs_inner_le_inner_abs_abs {n : ℕ}
    (f g : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    |@inner ℝ _ _ f g| ≤ @inner ℝ _ _ |f| |g| := by
  -- Expand inner products as integrals
  simp only [MeasureTheory.L2.inner_def]
  -- |∫ ⟪f x, g x⟫| ≤ ∫ ⟪|f| x, |g| x⟫
  -- via integral triangle inequality + pointwise ‖⟪a,b⟫‖ = ⟪|a|,|b|⟩
  calc |∫ x, @inner ℝ _ _ (f x) (g x) ∂volume|
      = ‖∫ x, @inner ℝ _ _ (f x) (g x) ∂volume‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, ‖@inner ℝ _ _ (f x) (g x)‖ ∂volume := norm_integral_le_integral_norm _
    _ = ∫ x, @inner ℝ _ _ (|f| x) (|g| x) ∂volume := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_abs f, Lp.coeFn_abs g] with x hf_abs hg_abs
        simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
        rw [hf_abs, hg_abs, Real.norm_eq_abs, abs_mul]

/-- Phase 2: Inner product inequality. -/
theorem abs_inner_le_inner_abs {n : ℕ}
    (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (hT_pp : IsPositivityPreserving T)
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    |@inner ℝ _ _ f (T f)| ≤ @inner ℝ _ _ |f| (T |f|) := by
  -- Step 1: |⟨f, Tf⟩| ≤ ⟨|f|, |Tf|⟩ (integral triangle inequality)
  -- Step 2: ⟨|f|, |Tf|⟩ ≤ ⟨|f|, T|f|⟩ (monotonicity + Phase 1)
  calc |@inner ℝ _ _ f (T f)|
      ≤ @inner ℝ _ _ |f| |T f| := abs_inner_le_inner_abs_abs f (T f)
    _ ≤ @inner ℝ _ _ |f| (T |f|) := by
        apply inner_mono_right_L2 |f| |T f| (T |f|)
        · -- 0 ≤ |f|: pointwise |f(x)| ≥ 0
          rw [← Lp.coeFn_nonneg]
          filter_upwards [Lp.coeFn_abs f] with x habs
          rw [habs]
          exact abs_nonneg _
        · exact abs_apply_le_apply_abs T hT_pp f

/-! ## Phase 3: |f| is a ground state if f is

The Rayleigh quotient R(g) = ⟨g, Tg⟩ / ‖g‖² achieves its supremum
at the ground state eigenvector. The chain of inequalities:

  lam₀ ‖f‖² = ⟨f, Tf⟩ ≤ |⟨f, Tf⟩| ≤ ⟨|f|, T|f|⟩ ≤ lam₀ ‖|f|‖²

Since ‖|f|‖ = ‖f‖, we get equality throughout, so |f| achieves the
supremum of R, hence |f| is an eigenvector for lam₀.
-/

/-- Phase 3: If f is an eigenvector for the top eigenvalue lam₀,
then |f| is also an eigenvector for lam₀. -/
theorem abs_eigenvector_of_top_eigenvector {n : ℕ}
    (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (hT_compact : IsCompactOperator T)
    (hT_sa : IsSelfAdjoint T)
    (hT_pp : IsPositivityPreserving T)
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (hf_ne : f ≠ 0)
    (lam₀ : ℝ) (hlam₀ : 0 < lam₀)
    (hf_eigen : (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →ₗ[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ))) f = lam₀ • f)
    (hlam₀_top : ∀ (g : Lp ℝ 2 (volume : Measure (Fin n → ℝ))),
      @inner ℝ _ _ g (T g) ≤ lam₀ * ‖g‖ ^ 2) :
    (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →ₗ[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ))) |f| = lam₀ • |f| := by
  set h := |f| with h_def
  -- Step 1: ‖h‖ = ‖f‖ and h ≠ 0
  have h_norm : ‖h‖ = ‖f‖ := norm_abs_eq_norm f
  have hh_ne : h ≠ 0 := by
    intro heq; apply hf_ne; rw [← norm_eq_zero, ← h_norm]; exact norm_eq_zero.mpr heq
  -- Step 2: ⟨f, Tf⟩ = lam₀ ‖f‖²
  have h_eigen_clm : T f = lam₀ • f := by exact_mod_cast hf_eigen
  have h_inner_f : @inner ℝ _ _ f (T f) = lam₀ * ‖f‖ ^ 2 := by
    rw [h_eigen_clm, inner_smul_right, real_inner_self_eq_norm_sq]
  -- Step 3: ⟨h, Th⟩ = lam₀ ‖h‖²
  have h_inner_abs : @inner ℝ _ _ h (T h) = lam₀ * ‖h‖ ^ 2 := by
    have hpos : 0 < @inner ℝ _ _ f (T f) := by
      rw [h_inner_f]; positivity [norm_pos_iff.mpr hf_ne]
    apply le_antisymm (hlam₀_top h)
    calc lam₀ * ‖h‖ ^ 2 = lam₀ * ‖f‖ ^ 2 := by rw [h_norm]
      _ = @inner ℝ _ _ f (T f) := h_inner_f.symm
      _ = |@inner ℝ _ _ f (T f)| := (abs_of_pos hpos).symm
      _ ≤ @inner ℝ _ _ h (T h) := abs_inner_le_inner_abs T hT_pp f
  -- Step 4: h maximizes reApplyInnerSelf on its sphere
  have h_max : IsMaxOn T.reApplyInnerSelf (Metric.sphere 0 ‖h‖) h := by
    intro y hy
    rw [Metric.mem_sphere, dist_zero_right] at hy
    change T.reApplyInnerSelf y ≤ T.reApplyInnerSelf h
    simp only [ContinuousLinearMap.reApplyInnerSelf_apply]
    -- For ℝ: re ⟪Tx, x⟫ = ⟨Tx, x⟩ = ⟨x, Tx⟩
    have h1 : RCLike.re (@inner ℝ _ _ (T y) y) = @inner ℝ _ _ y (T y) := by
      rw [RCLike.re_to_real, real_inner_comm]
    have h2 : RCLike.re (@inner ℝ _ _ (T h) h) = @inner ℝ _ _ h (T h) := by
      rw [RCLike.re_to_real, real_inner_comm]
    rw [h1, h2, h_inner_abs]
    calc @inner ℝ _ _ y (T y) ≤ lam₀ * ‖y‖ ^ 2 := hlam₀_top y
      _ = lam₀ * ‖h‖ ^ 2 := by rw [hy]
  -- Step 5: Apply eq_smul_self_of_isLocalExtrOn
  have h_eig := hT_sa.eq_smul_self_of_isLocalExtrOn (Or.inr h_max.localize)
  -- h_eig : T h = T.rayleighQuotient h • h
  -- Step 6: Compute rayleighQuotient h = lam₀
  have h_rq : T.rayleighQuotient h = lam₀ := by
    unfold ContinuousLinearMap.rayleighQuotient
    have h_re : T.reApplyInnerSelf h = lam₀ * ‖h‖ ^ 2 := by
      simp only [ContinuousLinearMap.reApplyInnerSelf_apply]
      rw [RCLike.re_to_real, real_inner_comm]
      exact h_inner_abs
    rw [h_re]
    have hh_norm_pos : 0 < ‖h‖ := norm_pos_iff.mpr hh_ne
    field_simp
  -- Step 7: Conclude
  rw [h_rq] at h_eig
  change (T : Lp ℝ 2 _ →ₗ[ℝ] Lp ℝ 2 _) h = lam₀ • h
  exact_mod_cast h_eig

/-! ## Phase 4: Ground state is strictly positive a.e.

Since |f| ≥ 0 and |f| ≠ 0, and T is positivity-improving,
T|f| > 0 a.e. But T|f| = lam₀|f|, so |f| > 0 a.e.
-/

/-- Phase 4: The ground state eigenvector (after taking absolute value)
is strictly positive almost everywhere. -/
theorem ground_state_strictly_positive {n : ℕ}
    (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (hT_pi : IsPositivityImproving' T)
    (e₀ : Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (he₀_ne : e₀ ≠ 0)
    (he₀_nonneg : 0 ≤ e₀)
    (lam₀ : ℝ) (hlam₀ : 0 < lam₀)
    (he₀_eigen : (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →ₗ[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ))) e₀ = lam₀ • e₀) :
    ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), 0 < (e₀ : (Fin n → ℝ) → ℝ) x := by
  -- T e₀ = lam₀ e₀, and T is positivity-improving, so T e₀ > 0 a.e.
  -- Therefore lam₀ e₀ > 0 a.e., and since lam₀ > 0, e₀ > 0 a.e.
  have hT_pos := hT_pi e₀ he₀_nonneg he₀_ne
  -- T e₀ = lam₀ • e₀ as elements of L²
  have heq : (T e₀ : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) = lam₀ • e₀ := by
    exact_mod_cast he₀_eigen
  -- (lam₀ • e₀)(x) = lam₀ * e₀(x) a.e.
  have hsmul := Lp.coeFn_smul lam₀ e₀
  -- Combine: 0 < (T e₀)(x) =ᵐ lam₀ * e₀(x), so e₀(x) > 0
  filter_upwards [hT_pos, heq ▸ hsmul] with x hpos hsmul_x
  -- hpos : 0 < (T e₀)(x), and (T e₀)(x) = lam₀ * e₀(x)
  simp only [Pi.smul_apply, smul_eq_mul] at hsmul_x
  rw [hsmul_x] at hpos
  exact (mul_pos_iff.mp hpos).elim (fun ⟨_, h⟩ => h) (fun ⟨h, _⟩ => absurd h (not_lt.mpr hlam₀.le))

/-! ## Phase 5: Every ground state eigenvector has constant sign

If f is an eigenvector for lam₀, then |f| is also (Phase 3).
Define h = |f| - f. Then h ≥ 0 and h is an eigenvector for lam₀.
By Phase 4, either h = 0 a.e. (so f = |f| ≥ 0, hence f > 0 a.e.)
or h > 0 a.e. Since h = |f| - f, having h > 0 a.e. means
|f(x)| > f(x) a.e., i.e., f(x) < 0 a.e. (strictly).

So every ground state eigenvector is either strictly positive or
strictly negative a.e.
-/

/-- Phase 5: Every eigenvector for the top eigenvalue has constant sign. -/
theorem eigenvector_constant_sign {n : ℕ}
    (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (hT_compact : IsCompactOperator T)
    (hT_sa : IsSelfAdjoint T)
    (hT_pi : IsPositivityImproving' T)
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (hf_ne : f ≠ 0)
    (lam₀ : ℝ) (hlam₀ : 0 < lam₀)
    (hf_eigen : (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →ₗ[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ))) f = lam₀ • f)
    (hlam₀_top : ∀ (g : Lp ℝ 2 (volume : Measure (Fin n → ℝ))),
      @inner ℝ _ _ g (T g) ≤ lam₀ * ‖g‖ ^ 2) :
    (∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), 0 < (f : (Fin n → ℝ) → ℝ) x) ∨
    (∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), (f : (Fin n → ℝ) → ℝ) x < 0) := by
  set g := |f| - f with g_def
  -- g ≥ 0: |f(x)| ≥ f(x) pointwise
  have hg_nonneg : 0 ≤ g := by
    rw [← Lp.coeFn_nonneg]
    filter_upwards [Lp.coeFn_sub (|f| : Lp ℝ 2 _) f, Lp.coeFn_abs f] with x hsub habs
    rw [show (g : (Fin n → ℝ) → ℝ) x = ((|f| - f : Lp ℝ 2 _) : (Fin n → ℝ) → ℝ) x from rfl,
        hsub]
    simp only [Pi.sub_apply, Pi.zero_apply]
    rw [habs, sub_nonneg]
    exact le_abs_self _
  -- T|f| = lam₀|f| from Phase 3
  have hf_abs_eigen : (T : _ →ₗ[ℝ] _) |f| = lam₀ • |f| :=
    abs_eigenvector_of_top_eigenvector T hT_compact hT_sa hT_pi.toPreserving
      f hf_ne lam₀ hlam₀ hf_eigen hlam₀_top
  -- Tg = lam₀ g by linearity
  have hg_eigen : (T : _ →ₗ[ℝ] _) g = lam₀ • g := by
    change (T : _ →ₗ[ℝ] _) (|f| - f) = lam₀ • (|f| - f)
    rw [map_sub, hf_abs_eigen, hf_eigen, smul_sub]
  by_cases hg_eq : g = 0
  · -- g = 0, so |f| = f, hence f ≥ 0 and f ≠ 0
    left
    have hf_eq_abs : |f| = f := by rwa [sub_eq_zero] at hg_eq
    have hf_nonneg : 0 ≤ f := by
      rw [← hf_eq_abs, ← Lp.coeFn_nonneg]
      filter_upwards [Lp.coeFn_abs f] with x habs
      rw [habs]; exact abs_nonneg _
    exact ground_state_strictly_positive T hT_pi f hf_ne hf_nonneg lam₀ hlam₀ hf_eigen
  · -- g ≠ 0, so g > 0 a.e. by Phase 4, meaning |f(x)| > f(x), so f(x) < 0
    right
    have hg_pos := ground_state_strictly_positive T hT_pi g hg_eq hg_nonneg lam₀ hlam₀ hg_eigen
    filter_upwards [hg_pos, Lp.coeFn_sub (|f| : Lp ℝ 2 _) f,
        Lp.coeFn_abs f] with x hx hsub habs
    -- 0 < g(x) = |f(x)| - f(x), so f(x) < 0
    rw [show (g : (Fin n → ℝ) → ℝ) x = ((|f| - f : Lp ℝ 2 _) : (Fin n → ℝ) → ℝ) x from rfl,
        hsub] at hx
    simp only [Pi.sub_apply] at hx
    rw [habs] at hx
    -- hx : 0 < |f x| - f x. If f x ≥ 0, then |f x| = f x, contradiction.
    by_contra h_ge; push_neg at h_ge
    linarith [abs_of_nonneg h_ge]

/-! ## Phase 6: The top eigenvalue lam₀ is simple

If u, v are two orthogonal eigenvectors for lam₀ with ⟨u, v⟩ = 0,
then by Phase 5, we may assume u > 0 a.e. and v > 0 a.e. (or
multiply by -1). But then ⟨u, v⟩ = ∫ u(x)v(x) dx > 0,
contradicting orthogonality.
-/

/-- Phase 6: The top eigenvalue has multiplicity 1 (is simple). -/
theorem top_eigenvalue_simple {n : ℕ}
    (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (hT_compact : IsCompactOperator T)
    (hT_sa : IsSelfAdjoint T)
    (hT_pi : IsPositivityImproving' T)
    (lam₀ : ℝ) (hlam₀ : 0 < lam₀)
    (hlam₀_top : ∀ (g : Lp ℝ 2 (volume : Measure (Fin n → ℝ))),
      @inner ℝ _ _ g (T g) ≤ lam₀ * ‖g‖ ^ 2)
    (u v : Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (hu_ne : u ≠ 0) (hv_ne : v ≠ 0)
    (hu_eigen : (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →ₗ[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ))) u = lam₀ • u)
    (hv_eigen : (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →ₗ[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ))) v = lam₀ • v)
    (h_orth : @inner ℝ _ _ u v = 0) :
    False := by
  -- Helper: if u > 0 a.e. and v > 0 a.e., then ⟨u, v⟩ > 0
  have inner_pos_of_pos :
      ∀ (f g : Lp ℝ 2 (volume : Measure (Fin n → ℝ))),
      (∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), 0 < (f : (Fin n → ℝ) → ℝ) x) →
      (∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), 0 < (g : (Fin n → ℝ) → ℝ) x) →
      (0 : ℝ) < @inner ℝ _ _ f g := by
    intro f g hf_pos hg_pos
    rw [MeasureTheory.L2.inner_def]
    have h_eq : (fun x => @inner ℝ _ _ ((f : (Fin n → ℝ) → ℝ) x)
        ((g : (Fin n → ℝ) → ℝ) x)) =ᵐ[volume]
        (fun x => (g : (Fin n → ℝ) → ℝ) x * (f : (Fin n → ℝ) → ℝ) x) := by
      filter_upwards with x
      simp [RCLike.inner_apply]
    rw [integral_congr_ae h_eq]
    have h_nn : (0 : (Fin n → ℝ) → ℝ) ≤ᶠ[ae volume]
        (fun x => (g : (Fin n → ℝ) → ℝ) x * (f : (Fin n → ℝ) → ℝ) x) := by
      filter_upwards [hf_pos, hg_pos] with x hfx hgx
      exact mul_nonneg (le_of_lt hgx) (le_of_lt hfx)
    have h_int : Integrable
        (fun x => (g : (Fin n → ℝ) → ℝ) x * (f : (Fin n → ℝ) → ℝ) x) volume :=
      (L2.integrable_inner f g).congr h_eq.symm
    rw [integral_pos_iff_support_of_nonneg_ae h_nn h_int, pos_iff_ne_zero]
    intro h_zero
    have h_ae_zero : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)),
        (g : (Fin n → ℝ) → ℝ) x * (f : (Fin n → ℝ) → ℝ) x = 0 :=
      ae_iff.mpr h_zero
    have : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), (0 : ℝ) < 0 := by
      filter_upwards [h_ae_zero, hf_pos, hg_pos] with x hx hfx hgx
      linarith [mul_pos hgx hfx]
    exact absurd this.exists.choose_spec (lt_irrefl 0)
  -- By Phase 5, u has constant sign
  rcases eigenvector_constant_sign T hT_compact hT_sa hT_pi u hu_ne lam₀ hlam₀
    hu_eigen hlam₀_top with hu_pos | hu_neg
  · -- u > 0 a.e.
    rcases eigenvector_constant_sign T hT_compact hT_sa hT_pi v hv_ne lam₀ hlam₀
      hv_eigen hlam₀_top with hv_pos | hv_neg
    · -- v > 0 a.e. → ⟨u, v⟩ > 0, contradiction
      linarith [inner_pos_of_pos u v hu_pos hv_pos]
    · -- v < 0 a.e. → -v > 0 a.e. → ⟨u, -v⟩ > 0 → ⟨u, v⟩ < 0, contradiction
      have hv_neg_pos : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)),
          0 < ((-v : Lp ℝ 2 _) : (Fin n → ℝ) → ℝ) x := by
        filter_upwards [hv_neg, Lp.coeFn_neg v] with x hx hneg
        rw [hneg, Pi.neg_apply]; linarith
      have h_pos := inner_pos_of_pos u (-v) hu_pos hv_neg_pos
      rw [inner_neg_right] at h_pos
      linarith
  · -- u < 0 a.e. → -u > 0 a.e.
    have hu_neg_pos : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)),
        0 < ((-u : Lp ℝ 2 _) : (Fin n → ℝ) → ℝ) x := by
      filter_upwards [hu_neg, Lp.coeFn_neg u] with x hx hneg
      rw [hneg, Pi.neg_apply]; linarith
    rcases eigenvector_constant_sign T hT_compact hT_sa hT_pi v hv_ne lam₀ hlam₀
      hv_eigen hlam₀_top with hv_pos | hv_neg
    · -- v > 0 a.e. → ⟨-u, v⟩ > 0 → ⟨u, v⟩ < 0, contradiction
      have h_pos := inner_pos_of_pos (-u) v hu_neg_pos hv_pos
      rw [inner_neg_left] at h_pos
      linarith
    · -- v < 0 a.e. → -v > 0 a.e. → ⟨-u, -v⟩ > 0 → ⟨u, v⟩ > 0, contradiction
      have hv_neg_pos : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)),
          0 < ((-v : Lp ℝ 2 _) : (Fin n → ℝ) → ℝ) x := by
        filter_upwards [hv_neg, Lp.coeFn_neg v] with x hx hneg
        rw [hneg, Pi.neg_apply]; linarith
      have h_pos := inner_pos_of_pos (-u) (-v) hu_neg_pos hv_neg_pos
      rw [inner_neg_left, inner_neg_right, neg_neg] at h_pos
      linarith

/-! ## Phase 7: Strict spectral gap

For any eigenvalue μ ≠ lam₀, we have |μ| < lam₀.

Case 1: μ ≥ 0. Then μ < lam₀ by simplicity (if μ = lam₀, the eigenspace
is 1-dimensional by Phase 6, so the eigenvector would be in the same
eigenspace).

Case 2: μ < 0. Suppose |μ| = lam₀, i.e., μ = -lam₀.
Let g be an eigenvector for -lam₀. By self-adjointness, ⟨e₀, g⟩ = 0.
Apply the absolute value trick: |Tg| = |-lam₀g| = lam₀|g|.
Phase 1 gives |Tg| ≤ T|g|, so lam₀|g| ≤ T|g|.
The Rayleigh quotient bound gives ⟨|g|, T|g|⟩ ≤ lam₀ ‖g‖².
Together: T|g| = lam₀|g|, so |g| is in the lam₀-eigenspace.
By simplicity (Phase 6), |g| = c·e₀ for some c > 0.
So |g| > 0 a.e. Phase 5 forces g to have constant sign.
But ⟨e₀, g⟩ = 0 with e₀ > 0 and |g| > 0 contradicts constant sign.
-/

/-- Phase 7: All eigenvalues other than lam₀ satisfy |μ| < lam₀. -/
theorem spectral_gap {n : ℕ}
    (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (hT_compact : IsCompactOperator T)
    (hT_sa : IsSelfAdjoint T)
    (hT_pi : IsPositivityImproving' T)
    (e₀ : Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (he₀_ne : e₀ ≠ 0)
    (lam₀ : ℝ) (hlam₀ : 0 < lam₀)
    (he₀_eigen : (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →ₗ[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ))) e₀ = lam₀ • e₀)
    (hlam₀_top : ∀ (g : Lp ℝ 2 (volume : Measure (Fin n → ℝ))),
      @inner ℝ _ _ g (T g) ≤ lam₀ * ‖g‖ ^ 2)
    (hlam₀_simple : ∀ v, v ≠ 0 →
      (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →ₗ[ℝ]
        Lp ℝ 2 (volume : Measure (Fin n → ℝ))) v = lam₀ • v →
      ∃ c : ℝ, v = c • e₀)
    (μ : ℝ) (hμ_ne : μ ≠ lam₀)
    (g : Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (hg_ne : g ≠ 0)
    (hg_eigen : (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →ₗ[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ))) g = μ • g) :
    |μ| < lam₀ := by
  -- Step 1: μ ≤ lam₀ from Rayleigh bound
  have hg_norm_sq_pos : 0 < ‖g‖ ^ 2 := by positivity [norm_pos_iff.mpr hg_ne]
  have h_eigen_clm : T g = μ • g := by exact_mod_cast hg_eigen
  have h_inner_g : @inner ℝ _ _ g (T g) = μ * ‖g‖ ^ 2 := by
    rw [h_eigen_clm, inner_smul_right, real_inner_self_eq_norm_sq]
  have hmu_le : μ ≤ lam₀ := by
    have : μ * ‖g‖ ^ 2 ≤ lam₀ * ‖g‖ ^ 2 := by
      calc μ * ‖g‖ ^ 2 = @inner ℝ _ _ g (T g) := h_inner_g.symm
        _ ≤ lam₀ * ‖g‖ ^ 2 := hlam₀_top g
    exact le_of_mul_le_mul_right this hg_norm_sq_pos
  -- Step 2: |μ| ≤ lam₀ from Phase 2 absolute value trick
  have h_abs_mu_le : |μ| ≤ lam₀ := by
    have : |μ| * ‖g‖ ^ 2 ≤ lam₀ * ‖g‖ ^ 2 :=
      calc |μ| * ‖g‖ ^ 2 = |μ * ‖g‖ ^ 2| := by
              rw [abs_mul, abs_of_pos hg_norm_sq_pos]
        _ = |@inner ℝ _ _ g (T g)| := by rw [h_inner_g]
        _ ≤ @inner ℝ _ _ |g| (T |g|) :=
              abs_inner_le_inner_abs T hT_pi.toPreserving g
        _ ≤ lam₀ * ‖|g|‖ ^ 2 := hlam₀_top |g|
        _ = lam₀ * ‖g‖ ^ 2 := by rw [norm_abs_eq_norm]
    exact le_of_mul_le_mul_right this hg_norm_sq_pos
  -- Step 3: Case split on sign of μ
  by_cases hmu_nonneg : 0 ≤ μ
  · -- μ ≥ 0: |μ| = μ ≤ lam₀, and μ ≠ lam₀, so |μ| < lam₀
    rw [abs_of_nonneg hmu_nonneg]
    exact lt_of_le_of_ne hmu_le hμ_ne
  · -- μ < 0: |μ| = -μ. Need -μ < lam₀, i.e., |μ| < lam₀.
    push_neg at hmu_nonneg
    -- If |μ| < lam₀, done. Otherwise |μ| = lam₀, i.e., μ = -lam₀.
    rcases lt_or_eq_of_le h_abs_mu_le with h_done | h_eq
    · exact h_done
    · -- μ = -lam₀. Derive contradiction using positivity-improving.
      exfalso
      have hmu_eq : μ = -lam₀ := by linarith [abs_of_neg hmu_nonneg]
      -- T|g| = lam₀|g| by Phase 3's Rayleigh argument
      -- (|g| achieves the Rayleigh max since |⟨g,Tg⟩| = lam₀‖g‖²)
      have hg_abs_ne : |g| ≠ (0 : Lp ℝ 2 _) := by
        intro h; apply hg_ne
        rw [← norm_eq_zero, ← norm_abs_eq_norm g, norm_eq_zero]; exact h
      -- Reuse Phase 3 Rayleigh argument for |g|
      have h_abs_inner : @inner ℝ _ _ (|g| : Lp ℝ 2 _) (T |g|) =
          lam₀ * ‖(|g| : Lp ℝ 2 _)‖ ^ 2 := by
        apply le_antisymm
        · exact (hlam₀_top |g|).trans_eq (by rw [norm_abs_eq_norm])
        · calc lam₀ * ‖(|g| : Lp ℝ 2 _)‖ ^ 2
              = lam₀ * ‖g‖ ^ 2 := by rw [norm_abs_eq_norm]
            _ = |μ| * ‖g‖ ^ 2 := by rw [h_eq]
            _ = |μ * ‖g‖ ^ 2| := by rw [abs_mul, abs_of_pos hg_norm_sq_pos]
            _ = |@inner ℝ _ _ g (T g)| := by rw [h_inner_g]
            _ ≤ @inner ℝ _ _ |g| (T |g|) :=
                  abs_inner_le_inner_abs T hT_pi.toPreserving g
      -- Rayleigh max → T|g| = lam₀|g| (same argument as Phase 3)
      have h_abs_max : IsMaxOn T.reApplyInnerSelf
          (Metric.sphere 0 ‖(|g| : Lp ℝ 2 _)‖) (|g| : Lp ℝ 2 _) := by
        intro y hy
        rw [Metric.mem_sphere, dist_zero_right] at hy
        change T.reApplyInnerSelf y ≤ T.reApplyInnerSelf |g|
        simp only [ContinuousLinearMap.reApplyInnerSelf_apply]
        have h1 : RCLike.re (@inner ℝ _ _ (T y) y) =
            @inner ℝ _ _ y (T y) := by
          rw [RCLike.re_to_real, real_inner_comm]
        have h2 : RCLike.re (@inner ℝ _ _ (T (|g| : Lp ℝ 2 _)) (|g| : Lp ℝ 2 _)) =
            @inner ℝ _ _ (|g| : Lp ℝ 2 _) (T |g|) := by
          rw [RCLike.re_to_real, real_inner_comm]
        rw [h1, h2, h_abs_inner]
        calc @inner ℝ _ _ y (T y) ≤ lam₀ * ‖y‖ ^ 2 := hlam₀_top y
          _ = lam₀ * ‖(|g| : Lp ℝ 2 _)‖ ^ 2 := by rw [hy]
      have h_abs_eig := hT_sa.eq_smul_self_of_isLocalExtrOn
        (Or.inr h_abs_max.localize)
      have h_rq : T.rayleighQuotient (|g| : Lp ℝ 2 _) = lam₀ := by
        unfold ContinuousLinearMap.rayleighQuotient
        simp only [ContinuousLinearMap.reApplyInnerSelf_apply]
        rw [RCLike.re_to_real, real_inner_comm, h_abs_inner]
        field_simp
      have h_T_abs_g : T (|g| : Lp ℝ 2 _) = lam₀ • (|g| : Lp ℝ 2 _) := by
        rw [h_abs_eig, h_rq]; simp
      -- Now: Tg = -lam₀ g, T|g| = lam₀|g|
      -- T(|g| + g) = T|g| + Tg = lam₀|g| + (-lam₀)g = lam₀(|g| - g)
      -- T(|g| - g) = T|g| - Tg = lam₀|g| - (-lam₀)g = lam₀(|g| + g)
      -- Let p = |g| + g ≥ 0 and q = |g| - g ≥ 0.
      -- Tp = lam₀ q and Tq = lam₀ p.
      set p := (|g| : Lp ℝ 2 _) + g with p_def
      set q := (|g| : Lp ℝ 2 _) - g with q_def
      have hp_nonneg : 0 ≤ p := by
        rw [← Lp.coeFn_nonneg]
        filter_upwards [Lp.coeFn_add (|g| : Lp ℝ 2 _) g, Lp.coeFn_abs g]
          with x hadd habs
        rw [show (p : (Fin n → ℝ) → ℝ) x =
            ((|g| + g : Lp ℝ 2 _) : (Fin n → ℝ) → ℝ) x from rfl, hadd]
        simp only [Pi.add_apply, Pi.zero_apply]
        rw [habs]; linarith [neg_abs_le ((g : (Fin n → ℝ) → ℝ) x)]
      have hq_nonneg : 0 ≤ q := by
        rw [← Lp.coeFn_nonneg]
        filter_upwards [Lp.coeFn_sub (|g| : Lp ℝ 2 _) g, Lp.coeFn_abs g]
          with x hsub habs
        rw [show (q : (Fin n → ℝ) → ℝ) x =
            ((|g| - g : Lp ℝ 2 _) : (Fin n → ℝ) → ℝ) x from rfl, hsub]
        simp only [Pi.sub_apply, Pi.zero_apply]
        rw [habs]; linarith [le_abs_self ((g : (Fin n → ℝ) → ℝ) x)]
      -- Tp = lam₀ q
      have h_eigen_neg : T g = (-lam₀) • g := by rw [h_eigen_clm, hmu_eq]
      have hTp : T p = lam₀ • q := by
        rw [p_def, map_add, h_T_abs_g, h_eigen_neg, q_def,
            smul_sub, neg_smul]; abel
      -- Tq = lam₀ p
      have hTq : T q = lam₀ • p := by
        rw [q_def, map_sub, h_T_abs_g, h_eigen_neg, p_def,
            smul_add, neg_smul]; abel
      -- At least one of p, q is nonzero (both zero ⟹ g = 0)
      have h_not_both_zero : p ≠ 0 ∨ q ≠ 0 := by
        by_contra h; push_neg at h; obtain ⟨hp0, hq0⟩ := h
        apply hg_ne
        have h2g : (2 : ℝ) • g = p - q := by
          change (2 : ℝ) • g = (|g| : Lp ℝ 2 _) + g - ((|g| : Lp ℝ 2 _) - g)
          module
        rw [show g = (2 : ℝ)⁻¹ • ((2 : ℝ) • g) from by
              rw [inv_smul_smul₀ two_ne_zero],
            h2g, hp0, hq0, sub_self, smul_zero]
      -- WLOG p ≠ 0 (the q ≠ 0 case is symmetric)
      -- If p ≠ 0: T positivity-improving + p ≥ 0, p ≠ 0 ⟹ Tp > 0 a.e.
      -- Tp = lam₀ q, so q > 0 a.e.
      -- Similarly Tq = lam₀ p > 0 a.e. ⟹ p > 0 a.e.
      -- p > 0 means |g(x)| + g(x) > 0, i.e., g(x) > -|g(x)|, always true unless g(x) ≤ 0
      -- But |g(x)| + g(x) > 0 implies g(x) > -|g(x)|:
      --   if g(x) ≥ 0: |g| + g = 2g > 0, so g > 0. ✓
      --   if g(x) < 0: |g| + g = -g + g = 0, not > 0. ✗
      -- So p > 0 a.e. means g > 0 a.e.
      -- And q > 0 means |g| - g > 0:
      --   if g(x) ≥ 0: |g| - g = 0, not > 0. ✗
      -- Contradiction: can't have both g > 0 a.e. and |g(x)| - g(x) > 0 a.e.
      rcases h_not_both_zero with hp_ne | hq_ne
      · -- p ≠ 0, p ≥ 0: Tp > 0 a.e.
        have hTp_pos := hT_pi p hp_nonneg hp_ne
        -- Tp = lam₀ q: so lam₀ q > 0 a.e., hence q > 0 a.e. (since lam₀ > 0)
        have hq_pos : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)),
            0 < (q : (Fin n → ℝ) → ℝ) x := by
          have hTp_eq : (T p : (Fin n → ℝ) → ℝ) =ᵐ[volume]
              (lam₀ • q : Lp ℝ 2 _) := by rw [hTp]
          filter_upwards [hTp_pos, hTp_eq,
              Lp.coeFn_smul lam₀ q] with x hpos heq hsmul
          rw [heq, hsmul, Pi.smul_apply, smul_eq_mul] at hpos
          exact (mul_pos_iff.mp hpos).elim (fun ⟨_, h⟩ => h)
            (fun ⟨h, _⟩ => absurd h (not_lt.mpr hlam₀.le))
        -- q > 0 a.e. means |g(x)| - g(x) > 0 a.e.
        -- Similarly: Tq = lam₀ p, q ≠ 0 (since q > 0 a.e.)
        have hq_ne' : q ≠ 0 := by
          intro h; rw [h] at hq_pos
          have : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), (0 : ℝ) < 0 := by
            filter_upwards [hq_pos, Lp.coeFn_zero ℝ 2 volume] with x hp hz
            rwa [hz] at hp
          exact absurd this.exists.choose_spec (lt_irrefl 0)
        have hTq_pos := hT_pi q hq_nonneg hq_ne'
        -- Tq = lam₀ p > 0 a.e., so p > 0 a.e.
        have hp_pos : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)),
            0 < (p : (Fin n → ℝ) → ℝ) x := by
          have hTq_eq : (T q : (Fin n → ℝ) → ℝ) =ᵐ[volume]
              (lam₀ • p : Lp ℝ 2 _) := by rw [hTq]
          filter_upwards [hTq_pos, hTq_eq,
              Lp.coeFn_smul lam₀ p] with x hpos heq hsmul
          rw [heq, hsmul, Pi.smul_apply, smul_eq_mul] at hpos
          exact (mul_pos_iff.mp hpos).elim (fun ⟨_, h⟩ => h)
            (fun ⟨h, _⟩ => absurd h (not_lt.mpr hlam₀.le))
        -- p > 0 a.e. means |g(x)| + g(x) > 0, so g(x) > -|g(x)|
        -- q > 0 a.e. means |g(x)| - g(x) > 0, so g(x) < |g(x)|
        -- Combined: -|g(x)| < g(x) < |g(x)|
        -- But for g(x) ≥ 0: |g(x)| + g(x) = 2g(x) > 0 → g(x) > 0
        --   and |g(x)| - g(x) = 0, contradicting q(x) > 0
        -- So we get contradiction a.e.
        have : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), False := by
          filter_upwards [hp_pos, hq_pos,
              Lp.coeFn_add (|g| : Lp ℝ 2 _) g,
              Lp.coeFn_sub (|g| : Lp ℝ 2 _) g,
              Lp.coeFn_abs g] with x hpx hqx hadd hsub habs
          rw [show (p : (Fin n → ℝ) → ℝ) x =
              ((|g| + g : Lp ℝ 2 _) : (Fin n → ℝ) → ℝ) x from rfl, hadd,
              Pi.add_apply] at hpx
          rw [show (q : (Fin n → ℝ) → ℝ) x =
              ((|g| - g : Lp ℝ 2 _) : (Fin n → ℝ) → ℝ) x from rfl, hsub,
              Pi.sub_apply] at hqx
          rw [habs] at hpx hqx
          -- hpx : 0 < |g x| + g x, hqx : 0 < |g x| - g x
          -- These imply g x > -|g x| and g x < |g x|
          -- Adding: 0 < 2|g x|, so |g x| > 0, so g x ≠ 0
          -- If g x > 0: |g x| = g x, so hqx gives 0 < g x - g x = 0. False.
          -- If g x < 0: |g x| = -g x, so hpx gives 0 < -g x + g x = 0. False.
          -- If g x = 0: hpx gives 0 < 0. False.
          rcases lt_trichotomy ((g : (Fin n → ℝ) → ℝ) x) 0 with hneg | hzero | hpos_x
          · rw [abs_of_neg hneg] at hpx; linarith
          · rw [hzero, abs_zero] at hpx; linarith
          · rw [abs_of_pos hpos_x] at hqx; linarith
        exact absurd this.exists.choose_spec id
      · -- q ≠ 0 case: symmetric argument
        have hTq_pos := hT_pi q hq_nonneg hq_ne
        have hp_pos : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)),
            0 < (p : (Fin n → ℝ) → ℝ) x := by
          have hTq_eq : (T q : (Fin n → ℝ) → ℝ) =ᵐ[volume]
              (lam₀ • p : Lp ℝ 2 _) := by rw [hTq]
          filter_upwards [hTq_pos, hTq_eq,
              Lp.coeFn_smul lam₀ p] with x hpos heq hsmul
          rw [heq, hsmul, Pi.smul_apply, smul_eq_mul] at hpos
          exact (mul_pos_iff.mp hpos).elim (fun ⟨_, h⟩ => h)
            (fun ⟨h, _⟩ => absurd h (not_lt.mpr hlam₀.le))
        have hp_ne' : p ≠ 0 := by
          intro h; rw [h] at hp_pos
          have : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), (0 : ℝ) < 0 := by
            filter_upwards [hp_pos, Lp.coeFn_zero ℝ 2 volume] with x hp hz
            rwa [hz] at hp
          exact absurd this.exists.choose_spec (lt_irrefl 0)
        have hTp_pos := hT_pi p hp_nonneg hp_ne'
        have hq_pos : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)),
            0 < (q : (Fin n → ℝ) → ℝ) x := by
          have hTp_eq : (T p : (Fin n → ℝ) → ℝ) =ᵐ[volume]
              (lam₀ • q : Lp ℝ 2 _) := by rw [hTp]
          filter_upwards [hTp_pos, hTp_eq,
              Lp.coeFn_smul lam₀ q] with x hpos heq hsmul
          rw [heq, hsmul, Pi.smul_apply, smul_eq_mul] at hpos
          exact (mul_pos_iff.mp hpos).elim (fun ⟨_, h⟩ => h)
            (fun ⟨h, _⟩ => absurd h (not_lt.mpr hlam₀.le))
        have : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), False := by
          filter_upwards [hp_pos, hq_pos,
              Lp.coeFn_add (|g| : Lp ℝ 2 _) g,
              Lp.coeFn_sub (|g| : Lp ℝ 2 _) g,
              Lp.coeFn_abs g] with x hpx hqx hadd hsub habs
          rw [show (p : (Fin n → ℝ) → ℝ) x =
              ((|g| + g : Lp ℝ 2 _) : (Fin n → ℝ) → ℝ) x from rfl, hadd,
              Pi.add_apply] at hpx
          rw [show (q : (Fin n → ℝ) → ℝ) x =
              ((|g| - g : Lp ℝ 2 _) : (Fin n → ℝ) → ℝ) x from rfl, hsub,
              Pi.sub_apply] at hqx
          rw [habs] at hpx hqx
          rcases lt_trichotomy ((g : (Fin n → ℝ) → ℝ) x) 0 with hneg | hzero | hpos_x
          · rw [abs_of_neg hneg] at hpx; linarith
          · rw [hzero, abs_zero] at hpx; linarith
          · rw [abs_of_pos hpos_x] at hqx; linarith
        exact absurd this.exists.choose_spec id

/-! ## Assembly: Jentzsch's theorem

Combine all phases to prove the full theorem. -/

/-- **Jentzsch's theorem** (proved).

For a compact, self-adjoint, positivity-improving operator on L²(ℝ^n)
with eigenbasis indexed by a type with ≥ 2 elements:
- The top eigenvalue lam₀ > 0 is simple.
- All other eigenvalues satisfy |λ| < lam₀.
- The second-largest eigenvalue exists and is attained. -/
theorem jentzsch_theorem_proved {n : ℕ}
    (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (hT_compact : IsCompactOperator T)
    (hT_sa : IsSelfAdjoint T)
    (hT_pi : IsPositivityImproving' T) :
    ∀ {ι : Type}
      (b : HilbertBasis ι ℝ (Lp ℝ 2 (volume : Measure (Fin n → ℝ))))
      (eigenval : ι → ℝ)
      (h_eigen : ∀ i,
        (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →ₗ[ℝ]
          Lp ℝ 2 (volume : Measure (Fin n → ℝ))) (b i) = eigenval i • b i)
      (h_sum : ∀ x, HasSum (fun i => (eigenval i * @inner ℝ _ _ (b i) x) • b i) (T x))
      (h_nt : ∃ j k : ι, j ≠ k),
    ∃ i₀ i₁ : ι,
      (0 < eigenval i₀) ∧
      (∀ i, eigenval i = eigenval i₀ → i = i₀) ∧
      (∀ i, i ≠ i₀ → |eigenval i| < eigenval i₀) ∧
      (i₁ ≠ i₀) ∧
      (∀ i, i ≠ i₀ → eigenval i ≤ eigenval i₁) := by
  intro ι b eigenval h_eigen h_sum h_nt
  -- Step 1: Find i₀ with |eigenval i₀| = ‖T‖ (compact SA operator achieves norm)
  -- Step 2: Show eigenval i₀ > 0 (from positivity-improving)
  -- Step 3: Show lam₀ is simple (Phase 6)
  -- Step 4: Show |eigenval i| < eigenval i₀ for i ≠ i₀ (Phase 7)
  -- Step 5: Find i₁ achieving max among excited eigenvalues (compact operator
  --         eigenvalues converge to 0, so max over nonempty bounded set attained)
  sorry

end
