/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Jentzsch's Theorem and Kernel Positivity

This file states Jentzsch's theorem (proved in JentzschProof.lean), axiomatizes
kernel positivity facts about the transfer operator, and derives the
Perron-Frobenius properties needed for the P(Φ)₂ construction.

## Theorem: Jentzsch's theorem (Reed-Simon IV, XIII.43–44)

For a compact, self-adjoint, positivity-improving operator T on L² with
eigenbasis indexed by a type with ≥ 2 elements:
- The spectral radius r is a simple eigenvalue with strictly positive value.
- All other eigenvalues λ satisfy |λ| < r.

Proved in `JentzschProof.lean` via the variational absolute value trick.

**Important**: Jentzsch does NOT imply all eigenvalues are positive.
Counterexample: [[1,2],[2,1]] is positivity-improving with eigenvalues 3,-1.

## Axiom 2: Transfer operator positivity-improving

The kernel T(ψ,ψ') = w(ψ)·G(ψ-ψ')·w(ψ') > 0 is strictly positive.

## Axiom 3: Gaussian kernel is strictly positive definite

⟨f, Tf⟩ > 0 for nonzero f, since the Gaussian kernel exp(-½‖·‖²) has
strictly positive Fourier transform (Bochner), and w > 0 preserves this.

## Axiom 4: L²(ℝ^Ns) Hilbert basis nontriviality

Any Hilbert basis of L²(ℝ^Ns) has at least 2 elements.

## Derived theorems

From Jentzsch + axioms 2-4 we derive:
- `transferOperator_inner_nonneg`: ⟨f, Tf⟩ ≥ 0
- `transferOperator_eigenvalues_pos`: all λᵢ > 0
- `transferOperator_ground_simple`: unique leading eigenvalue with strict gap
- `transferOperator_ground_simple_spectral`: packaged spectral data

## References

- Reed-Simon IV, Theorems XIII.43–44
- Simon, *The P(φ)₂ Euclidean QFT*, §III.2
- Glimm-Jaffe, *Quantum Physics*, §6.1
-/

import Pphi2.TransferMatrix.L2Operator
import Pphi2.TransferMatrix.JentzschProof

noncomputable section

open MeasureTheory

/-! ## Jentzsch's theorem (proved in JentzschProof.lean) -/

/-- **Jentzsch's theorem** for compact self-adjoint positivity-improving
operators on L²(ℝ^n).

Given a nontrivial eigenbasis (|ι| ≥ 2), there exists a distinguished index
i₀ (ground) such that:
(a) λ(i₀) > 0 (the leading eigenvalue is strictly positive).
(b) λ(i₀) is simple: it is the unique index with this eigenvalue.
(c) |λ(i)| < λ(i₀) for all i ≠ i₀ (strict spectral gap).

Proved in `JentzschProof.lean` via the variational absolute value trick.
The bridge from `IsPositivityImproving` (ae) to `IsPositivityImproving'` (Lp lattice)
is `IsPositivityImproving.toPI'`.

**References**: Reed-Simon IV, Theorems XIII.43–44. -/
theorem jentzsch_theorem {n : ℕ}
    (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (hT_compact : IsCompactOperator T)
    (hT_sa : IsSelfAdjoint T)
    (hT_pi : IsPositivityImproving T) :
    ∀ {ι : Type}
      (b : HilbertBasis ι ℝ (Lp ℝ 2 (volume : Measure (Fin n → ℝ))))
      (eigenval : ι → ℝ)
      (h_eigen : ∀ i,
        (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →ₗ[ℝ]
          Lp ℝ 2 (volume : Measure (Fin n → ℝ))) (b i) = eigenval i • b i)
      (h_sum : ∀ x, HasSum (fun i => (eigenval i * @inner ℝ _ _ (b i) x) • b i) (T x))
      (h_nt : ∃ j k : ι, j ≠ k),
    ∃ i₀ : ι,
      (0 < eigenval i₀) ∧
      (∀ i, eigenval i = eigenval i₀ → i = i₀) ∧
      (∀ i, i ≠ i₀ → |eigenval i| < eigenval i₀) :=
  jentzsch_theorem_proved T hT_compact hT_sa hT_pi.toPI'

namespace Pphi2

variable (Ns : ℕ) [NeZero Ns]

/-! ## Axiom 2: Transfer operator is positivity-improving -/

/-- The transfer operator is positivity-improving.

The kernel `T(ψ,ψ') = exp(-(a/2)h(ψ)) · exp(-½‖ψ-ψ'‖²) · exp(-(a/2)h(ψ')) > 0`
is strictly positive for all ψ, ψ'. For f ≥ 0, f ≠ 0, the set
S = {ψ' : f(ψ') > 0} has positive measure, so
(Tf)(ψ) = ∫ T(ψ,ψ') f(ψ') dψ' ≥ ∫_S T(ψ,ψ') f(ψ') dψ' > 0.

**Proof**: Uses the factorization T = M_w ∘ Conv_G ∘ M_w where w > 0 (exp) and G > 0 (exp).
Multiplication by w > 0 preserves nonneg/nonzero. Convolution with the strictly positive
Gaussian kernel maps nonneg nonzero functions to ae strictly positive functions (by
`integral_pos_iff_support_of_nonneg_ae` and translation invariance of Lebesgue measure).
Final multiplication by w > 0 preserves ae strict positivity. -/
theorem transferOperator_positivityImproving (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    IsPositivityImproving (transferOperatorCLM Ns P a mass ha hmass) := by
  intro f hf_nonneg hf_nonzero
  -- Abbreviations for the building blocks
  set w := transferWeight Ns P a mass
  set G := transferGaussian Ns
  set hw_meas := transferWeight_measurable Ns P a mass
  set C := (transferWeight_bound Ns P a mass ha hmass).choose
  set hC := (transferWeight_bound Ns P a mass ha hmass).choose_spec.1
  set hw_bound := (transferWeight_bound Ns P a mass ha hmass).choose_spec.2
  set hG := transferGaussian_memLp Ns
  -- Key positivity facts
  have hw_pos : ∀ ψ, 0 < w ψ := transferWeight_pos Ns P a mass
  have hG_pos : ∀ ψ, 0 < G ψ := transferGaussian_pos Ns
  -- T f = M_w (Conv_G (M_w f))
  -- Step 1: g := M_w f satisfies g ≥ 0 ae, g ≢ 0 ae
  set g := mulCLM w hw_meas C hC hw_bound f with hg_def
  have hg_spec := mulCLM_spec w hw_meas C hC hw_bound f
  have hg_nonneg : ∀ᵐ x ∂(volume : Measure (SpatialField Ns)), 0 ≤ (g : SpatialField Ns → ℝ) x := by
    filter_upwards [hg_spec, hf_nonneg] with x hx hfx
    rw [hx]; exact mul_nonneg (le_of_lt (hw_pos x)) hfx
  have hg_nonzero : ¬ (g : SpatialField Ns → ℝ) =ᵐ[volume] 0 := by
    intro h_absurd
    apply hf_nonzero
    -- g =ᵐ 0 and g =ᵐ w * f, so w * f =ᵐ 0, so f =ᵐ 0 (since w > 0)
    have h_wf_zero : (fun x => w x * (f : SpatialField Ns → ℝ) x) =ᵐ[volume] 0 := by
      filter_upwards [h_absurd, hg_spec] with x hx1 hx2
      rwa [← hx2]
    filter_upwards [h_wf_zero] with x hx
    exact (mul_eq_zero.mp hx).resolve_left (ne_of_gt (hw_pos x))
  -- Step 2: h := Conv_G g satisfies h > 0 ae
  set h := convCLM G hG g with hh_def
  have hh_spec := convCLM_spec G hG g
  -- The convolution ∫ G(t) · g(x-t) dt is > 0 because G > 0 and g ≥ 0 ae, g ≢ 0 ae
  have hh_pos : ∀ᵐ x ∂(volume : Measure (SpatialField Ns)),
      0 < (h : SpatialField Ns → ℝ) x := by
    -- Use convCLM_spec: ↑↑h =ᵐ realConv vol G ⇑g
    -- Then show realConv vol G ⇑g x = ∫ G(t) * ⇑g(x-t) dt > 0 for all x
    -- by integral_pos_iff_support_of_nonneg_ae
    filter_upwards [hh_spec] with x hx
    rw [hx]
    -- Goal: 0 < realConv volume G ⇑g x = ∫ G(t) * ⇑g(x-t) dt
    -- Helper: the map t ↦ x - t preserves Lebesgue measure (neg + left translation)
    have h_mp : MeasurePreserving (fun t : SpatialField Ns => x - t) volume volume :=
      (measurePreserving_add_left volume x).comp (Measure.measurePreserving_neg volume)
    -- Step 2a: the integrand t ↦ G(t) * ⇑g(x-t) is nonneg ae
    have h_integrand_nonneg : ∀ᵐ t ∂(volume : Measure (SpatialField Ns)),
        0 ≤ G t * (g : SpatialField Ns → ℝ) (x - t) := by
      have h_trans : ∀ᵐ t ∂volume, 0 ≤ (g : SpatialField Ns → ℝ) (x - t) := by
        rw [ae_iff] at hg_nonneg ⊢
        -- volume {t | ¬0 ≤ g(x-t)} = volume (f⁻¹'S) ≤ volume S = 0
        exact le_antisymm (hg_nonneg ▸ h_mp.measure_preimage_le _) (zero_le _)
      filter_upwards [h_trans] with t ht
      exact mul_nonneg (le_of_lt (hG_pos t)) ht
    -- Step 2b: the integrand is integrable (L² × L² → L¹ by Cauchy-Schwarz)
    have h_integrand_int : Integrable (fun t => G t * (g : SpatialField Ns → ℝ) (x - t))
        (volume : Measure (SpatialField Ns)) := by
      -- Both G and g(x-·) are in L², use integrable_inner from L2Space
      have hG2 : MemLp G 2 volume := transferGaussian_memLp_two Ns
      have hgx : MemLp ((↑↑g : SpatialField Ns → ℝ) ∘ (x - ·)) 2 volume :=
        (Lp.memLp g).comp_measurePreserving h_mp
      set G' := hG2.toLp G
      set gx' := hgx.toLp _
      refine (L2.integrable_inner (𝕜 := ℝ) G' gx').congr ?_
      filter_upwards [hG2.coeFn_toLp, hgx.coeFn_toLp] with t hGt hgxt
      -- Goal: ⟪G'(t), gx'(t)⟫_ℝ = G t * g(x-t)
      -- For ℝ: ⟪a, b⟫ = b * conj a = b * a
      rw [RCLike.inner_apply, starRingEnd_apply, star_trivial]
      simp only [Function.comp_apply] at hgxt
      rw [hGt, hgxt, mul_comm]
    -- Step 2c: the support of the integrand has positive measure
    have h_support_pos : 0 < (volume : Measure (SpatialField Ns))
        (Function.support (fun t => G t * (g : SpatialField Ns → ℝ) (x - t))) := by
      -- Support of G*g(x-·) ⊇ (x-·)⁻¹'(support g), both have same measure
      have h_subset : (fun t => x - t) ⁻¹'
            (Function.support (g : SpatialField Ns → ℝ)) ⊆
          Function.support (fun t => G t * (g : SpatialField Ns → ℝ) (x - t)) := by
        intro t ht
        simp only [Function.mem_support, Set.mem_preimage] at ht ⊢
        exact mul_ne_zero (ne_of_gt (hG_pos t)) ht
      have h_g_support : 0 < volume (Function.support (g : SpatialField Ns → ℝ)) := by
        rw [pos_iff_ne_zero]
        intro h_eq
        exact hg_nonzero (ae_iff.mpr h_eq)
      calc volume (Function.support fun t => G t * (g : SpatialField Ns → ℝ) (x - t))
          ≥ volume ((fun t => x - t) ⁻¹'
              Function.support (g : SpatialField Ns → ℝ)) :=
            measure_mono h_subset
        _ = volume (Function.support (g : SpatialField Ns → ℝ)) :=
            h_mp.measure_preimage
              (measurableSet_support
                (Lp.stronglyMeasurable g).measurable).nullMeasurableSet
        _ > 0 := h_g_support
    -- Combine using integral_pos_iff_support_of_nonneg_ae
    rw [show realConv volume G (⇑g) x =
        ∫ t, G t * (g : SpatialField Ns → ℝ) (x - t) ∂volume from by
      simp [realConv, convolution, ContinuousLinearMap.lsmul_apply]]
    exact (integral_pos_iff_support_of_nonneg_ae h_integrand_nonneg h_integrand_int).mpr
      h_support_pos
  -- Step 3: T f = M_w h, and M_w maps ae positive to ae positive
  -- transferOperatorCLM f = mulCLM w ... (convCLM G ... (mulCLM w ... f)) = mulCLM w ... h
  have hTf_coercion : (transferOperatorCLM Ns P a mass ha hmass f : SpatialField Ns → ℝ) =
      (mulCLM w hw_meas C hC hw_bound h : SpatialField Ns → ℝ) :=
    congr_arg (fun e : L2SpatialField Ns => (e : SpatialField Ns → ℝ))
      (show transferOperatorCLM Ns P a mass ha hmass f =
        mulCLM w hw_meas C hC hw_bound h from rfl)
  have hresult_spec := mulCLM_spec w hw_meas C hC hw_bound h
  simp only [hTf_coercion]
  filter_upwards [hresult_spec, hh_pos] with x hx hhx
  rw [hx]; exact mul_pos (hw_pos x) hhx

/-! ## Axiom 3: Strictly positive definite kernel

The Gaussian kernel exp(-½‖x-y‖²) is strictly positive definite: its Fourier
transform is (2π)^{n/2} exp(-½‖k‖²) > 0 everywhere, so by Bochner's theorem
G is strictly PD on L². The full kernel K(x,y) = w(x)G(x-y)w(y) with
w = exp(-(a/2)h) > 0 preserves strict PD (Schur product with w⊗w), giving
⟨f, Tf⟩ = ∫∫ K(x,y) f(x) f(y) dx dy > 0 for all nonzero f ∈ L². -/

/-- The transfer operator is strictly positive definite: ⟨f, Tf⟩ > 0 for
all nonzero f ∈ L².

This follows from:
1. The Gaussian kernel G(x-y) = exp(-½‖x-y‖²) is strictly PD
   (Bochner's theorem: Fourier transform is strictly positive).
2. K(x,y) = w(x)·G(x-y)·w(y) with w > 0 is strictly PD.
3. ⟨f, Tf⟩ = ∫∫ K(x,y) f(x) f(y) dx dy > 0 for f ≠ 0.

**References**: Reed-Simon I, §VI.5; Stein-Shakarchi, *Real Analysis*, Ch. 6. -/
axiom transferOperator_strictly_positive_definite (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∀ (f : L2SpatialField Ns), f ≠ 0 →
      0 < @inner ℝ _ _ f (transferOperatorCLM Ns P a mass ha hmass f)

/-! ## L²(ℝ^Ns) Hilbert basis nontriviality

L²(ℝ^Ns, Lebesgue) is infinite-dimensional (it contains orthogonal indicator
functions of disjoint sets), so any Hilbert basis has at least 2 elements. -/

/-- Any Hilbert basis of L²(ℝ^Ns) has at least 2 elements.

**Proof**: Construct two orthogonal nonzero elements using indicator functions
of disjoint balls, then use the Hilbert basis expansion to derive that ι
must have ≥ 2 elements. -/
theorem l2SpatialField_hilbertBasis_nontrivial
    {ι : Type} (b : HilbertBasis ι ℝ (L2SpatialField Ns)) :
    ∃ j k : ι, j ≠ k := by
  classical
  -- Construct two disjoint balls with positive finite Lebesgue measure
  let μ : Measure (Fin Ns → ℝ) := volume
  let A := Metric.ball (0 : Fin Ns → ℝ) 1
  let B := Metric.ball (fun _ : Fin Ns => (4 : ℝ)) 1
  have hA_meas : MeasurableSet A := measurableSet_ball
  have hB_meas : MeasurableSet B := measurableSet_ball
  have hA_fin : μ A ≠ ⊤ := measure_ball_ne_top
  have hB_fin : μ B ≠ ⊤ := measure_ball_ne_top
  have hA_pos : μ A ≠ 0 := ne_of_gt (Metric.measure_ball_pos μ 0 one_pos)
  have hB_pos : μ B ≠ 0 := ne_of_gt (Metric.measure_ball_pos μ _ one_pos)
  -- Balls are disjoint via triangle inequality
  have hAB : Disjoint A B := Set.disjoint_left.mpr fun x hxA hxB => by
    have h1 : dist x 0 < 1 := Metric.mem_ball.mp hxA
    have h2 : dist x (fun _ => (4:ℝ)) < 1 := Metric.mem_ball.mp hxB
    have htri : dist (0 : Fin Ns → ℝ) (fun _ => (4:ℝ)) < 2 :=
      calc dist 0 (fun _ => (4:ℝ))
          ≤ dist (0 : Fin Ns → ℝ) x + dist x (fun _ => 4) := dist_triangle _ _ _
        _ = dist x 0 + dist x (fun _ => 4) := by rw [dist_comm]
        _ < 1 + 1 := add_lt_add h1 h2
        _ = 2 := by ring
    have hge : (4 : ℝ) ≤ dist (0 : Fin Ns → ℝ) (fun _ => (4:ℝ)) := by
      have i₀ : Fin Ns := ⟨0, Fin.pos'⟩
      have h1 : dist (0 : ℝ) 4 = 4 := by norm_num
      have h2 : dist ((0 : Fin Ns → ℝ) i₀) ((fun _ => (4:ℝ)) i₀)
          = dist (0 : ℝ) 4 := by simp
      have h3 : dist ((0 : Fin Ns → ℝ) i₀) ((fun _ => (4:ℝ)) i₀)
          ≤ dist (0 : Fin Ns → ℝ) (fun _ => (4:ℝ)) := by
        exact dist_le_pi_dist (0 : Fin Ns → ℝ) (fun _ => (4:ℝ)) i₀
      linarith
    linarith
  -- Construct indicator functions in L²
  let f₁ := indicatorConstLp (E := ℝ) 2 hA_meas hA_fin 1
  let f₂ := indicatorConstLp (E := ℝ) 2 hB_meas hB_fin 1
  -- They are nonzero (norm > 0)
  have hf₁_ne : f₁ ≠ 0 := by
    intro h; have h1 := congr_arg (‖·‖) h
    simp only [norm_zero] at h1
    rw [show f₁ = indicatorConstLp 2 hA_meas hA_fin (1:ℝ) from rfl,
      norm_indicatorConstLp (by norm_num) (by norm_num),
      norm_one, one_mul] at h1
    have : (0 : ℝ) < μ.real A := ENNReal.toReal_pos hA_pos hA_fin
    linarith [Real.rpow_pos_of_pos this (1 / (2:ENNReal).toReal)]
  have hf₂_ne : f₂ ≠ 0 := by
    intro h; have h1 := congr_arg (‖·‖) h
    simp only [norm_zero] at h1
    rw [show f₂ = indicatorConstLp 2 hB_meas hB_fin (1:ℝ) from rfl,
      norm_indicatorConstLp (by norm_num) (by norm_num),
      norm_one, one_mul] at h1
    have : (0 : ℝ) < μ.real B := ENNReal.toReal_pos hB_pos hB_fin
    linarith [Real.rpow_pos_of_pos this (1 / (2:ENNReal).toReal)]
  -- They are orthogonal (disjoint supports)
  have h_orth : @inner ℝ _ _ f₁ f₂ = 0 := by
    show @inner ℝ _ _ (indicatorConstLp 2 hA_meas hA_fin (1:ℝ))
      (indicatorConstLp 2 hB_meas hB_fin (1:ℝ)) = 0
    rw [MeasureTheory.L2.inner_indicatorConstLp_indicatorConstLp]
    simp [hAB.inter_eq]
  -- By contradiction: assume ι has < 2 elements
  by_contra h_not
  push_neg at h_not
  -- h_not : ∀ j k : ι, j = k (ι is subsingleton)
  by_cases hι : IsEmpty ι
  · -- ι empty: b.repr maps to ℓ²(∅) = {0}, so f₁ = 0
    exact hf₁_ne (b.repr.injective (by ext i; exact hι.elim i))
  · -- ι has exactly one element j₀
    rw [not_isEmpty_iff] at hι
    obtain ⟨j₀⟩ := hι
    -- Every vector is a scalar multiple of b j₀
    have h_span : ∀ v : L2SpatialField Ns,
        v = @inner ℝ _ _ (b j₀) v • b j₀ := by
      intro v
      have h_expand := b.hasSum_repr v
      have h_repr_eq : ∀ i, b.repr v i = @inner ℝ _ _ (b i) v :=
        fun i => b.repr_apply_apply v i
      simp_rw [h_repr_eq] at h_expand
      have heq : (fun i => @inner ℝ _ _ (b i) v • b i) =
          (fun _ => @inner ℝ _ _ (b j₀) v • b j₀) :=
        funext fun i => by rw [h_not i j₀]
      rw [heq] at h_expand
      have h_ite : HasSum (fun i => if i = j₀
          then @inner ℝ _ _ (b j₀) v • (b j₀ : L2SpatialField Ns)
          else 0) (@inner ℝ _ _ (b j₀) v • (b j₀ : L2SpatialField Ns)) := by
        convert hasSum_ite_eq j₀ (@inner ℝ _ _ (b j₀) v • (b j₀ : L2SpatialField Ns))
      have h_same : (fun _ : ι => @inner ℝ _ _ (b j₀) v • (b j₀ : L2SpatialField Ns))
          = (fun i => if i = j₀
            then @inner ℝ _ _ (b j₀) v • (b j₀ : L2SpatialField Ns)
            else 0) :=
        funext fun i => by simp [h_not i j₀]
      rw [h_same] at h_expand
      exact h_expand.unique h_ite
    -- inner f₁ f₂ = c₁ * c₂
    have h1 := h_span f₁
    have h2 := h_span f₂
    rw [h1, h2] at h_orth
    simp only [inner_smul_left, inner_smul_right, star_trivial,
      real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one j₀,
      one_pow, mul_one] at h_orth
    rcases mul_eq_zero.mp h_orth with hc | hc
    · exact hf₂_ne (by rw [h2, hc, zero_smul])
    · rw [starRingEnd_apply, star_trivial] at hc
      exact hf₁_ne (by rw [h1, hc, zero_smul])

/-! ## Derived theorems

We now derive the Perron-Frobenius properties of the transfer
operator from the axioms above. These have the same signatures as the
former axioms in L2Operator.lean, ensuring downstream compatibility. -/

/-- ⟨f, Tf⟩ ≥ 0 for all f. Immediate from strict PD (which gives > 0 for f ≠ 0,
and ⟨0, T0⟩ = 0 for f = 0). -/
theorem transferOperator_inner_nonneg (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∀ (f : L2SpatialField Ns),
      0 ≤ @inner ℝ _ _ f (transferOperatorCLM Ns P a mass ha hmass f) := by
  intro f
  by_cases hf : f = 0
  · rw [hf, map_zero, inner_self_eq_zero.mpr rfl]
  · exact le_of_lt (transferOperator_strictly_positive_definite Ns P a mass ha hmass f hf)

/-- All eigenvalues of the transfer operator are strictly positive.

Proof: ⟨bᵢ, T(bᵢ)⟩ = λᵢ · ‖bᵢ‖² = λᵢ > 0 by strict positive definiteness,
since bᵢ ≠ 0 (it has norm 1). -/
theorem transferOperator_eigenvalues_pos (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    {ι : Type} (b : HilbertBasis ι ℝ (L2SpatialField Ns)) (eigenval : ι → ℝ)
    (h_eigen : ∀ i, (transferOperatorCLM Ns P a mass ha hmass :
        L2SpatialField Ns →ₗ[ℝ] L2SpatialField Ns) (b i) = eigenval i • b i)
    (i : ι) : 0 < eigenval i := by
  -- bᵢ ≠ 0 since ‖bᵢ‖ = 1
  have hbi_ne : (b i : L2SpatialField Ns) ≠ 0 := by
    intro h
    have := b.orthonormal.norm_eq_one i
    rw [h, norm_zero] at this
    exact one_ne_zero this.symm
  -- ⟨bᵢ, Tbᵢ⟩ > 0 by strict PD
  have hpd := transferOperator_strictly_positive_definite Ns P a mass ha hmass (b i) hbi_ne
  -- Rewrite ⟨bᵢ, Tbᵢ⟩ = λᵢ · ‖bᵢ‖² = λᵢ
  have h_eigen_i := h_eigen i
  have hconv : (transferOperatorCLM Ns P a mass ha hmass :
    L2SpatialField Ns →ₗ[ℝ] L2SpatialField Ns) (b i) =
    transferOperatorCLM Ns P a mass ha hmass (b i) := rfl
  rw [← hconv, h_eigen_i] at hpd
  rw [@inner_smul_right ℝ, @real_inner_self_eq_norm_sq] at hpd
  have hnorm : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
  rw [hnorm, one_pow, mul_one] at hpd
  exact hpd

/-- Ground-state simplicity and existence of first excited level.

Derived from Jentzsch (which gives i₀ with spectral gap) combined with
nontriviality (to pick some i₁ ≠ i₀) and eigenvalue positivity
(to convert |λᵢ| < λ₀ to λᵢ < λ₀). -/
theorem transferOperator_ground_simple (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∀ {ι : Type} (b : HilbertBasis ι ℝ (L2SpatialField Ns)) (eigenval : ι → ℝ)
      (h_eigen : ∀ i, (transferOperatorCLM Ns P a mass ha hmass :
          L2SpatialField Ns →ₗ[ℝ] L2SpatialField Ns) (b i) = eigenval i • b i)
      (h_sum : ∀ x, HasSum (fun i => (eigenval i * @inner ℝ _ _ (b i) x) • b i)
          (transferOperatorCLM Ns P a mass ha hmass x)),
      ∃ i₀ i₁ : ι, i₁ ≠ i₀ ∧ eigenval i₁ < eigenval i₀ := by
  intro ι b eigenval h_eigen h_sum
  -- Nontriviality: L²(ℝ^Ns) is infinite-dimensional
  have h_nt := l2SpatialField_hilbertBasis_nontrivial Ns b
  -- Jentzsch gives i₀ with positivity, simplicity, and spectral gap
  obtain ⟨i₀, hpos, _hsimple, hgap⟩ := jentzsch_theorem
    (transferOperatorCLM Ns P a mass ha hmass)
    (transferOperator_isCompact Ns P a mass ha hmass)
    (transferOperator_isSelfAdjoint Ns P a mass ha hmass)
    (transferOperator_positivityImproving Ns P a mass ha hmass)
    b eigenval h_eigen h_sum h_nt
  -- Pick any i₁ ≠ i₀ from nontriviality
  obtain ⟨j, k, hjk⟩ := h_nt
  have h_exists_ne : ∃ i₁, i₁ ≠ i₀ := by
    by_cases hj : j = i₀
    · exact ⟨k, fun hk => hjk (hj.trans hk.symm)⟩
    · exact ⟨j, hj⟩
  obtain ⟨i₁, hi₁_ne⟩ := h_exists_ne
  -- All eigenvalues positive, so |λᵢ| = λᵢ → gap gives λ(i₁) < λ(i₀)
  have hall_pos : ∀ i, 0 < eigenval i :=
    fun i => transferOperator_eigenvalues_pos Ns P a mass ha hmass b eigenval h_eigen i
  have hlt : eigenval i₁ < eigenval i₀ := by
    have := hgap i₁ hi₁_ne
    rwa [abs_of_pos (hall_pos i₁)] at this
  exact ⟨i₀, i₁, hi₁_ne, hlt⟩

/-- Spectral data with distinguished ground and first excited levels. -/
theorem transferOperator_ground_simple_spectral (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∃ (ι : Type) (b : HilbertBasis ι ℝ (L2SpatialField Ns)) (eigenval : ι → ℝ)
      (i₀ i₁ : ι),
      (∀ i, (transferOperatorCLM Ns P a mass ha hmass :
          L2SpatialField Ns →ₗ[ℝ] L2SpatialField Ns) (b i) = eigenval i • b i) ∧
      (∀ x, HasSum (fun i => (eigenval i * @inner ℝ _ _ (b i) x) • b i)
          (transferOperatorCLM Ns P a mass ha hmass x)) ∧
      i₁ ≠ i₀ ∧ eigenval i₁ < eigenval i₀ := by
  rcases transferOperator_spectral Ns P a mass ha hmass with ⟨ι, b, eigenval, h_eigen, h_sum⟩
  rcases transferOperator_ground_simple Ns P a mass ha hmass b eigenval h_eigen h_sum
    with ⟨i₀, i₁, hi_ne, hlt⟩
  exact ⟨ι, b, eigenval, i₀, i₁, h_eigen, h_sum, hi_ne, hlt⟩

end Pphi2

end
