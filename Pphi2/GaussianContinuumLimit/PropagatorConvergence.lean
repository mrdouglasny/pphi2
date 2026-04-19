/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michael R. Douglas

# Lattice Propagator Convergence

The main analytical content of the Gaussian continuum limit: the lattice
Green's function converges to the continuum Green's function as a → 0.

## Main results

- `latticeGreenBilinear_basis_tendsto_continuum` — (axiom) basis-pair spectral
  convergence
- `latticeGreenBilinear_tendsto_continuum` — theorem extending basis-pair
  convergence to arbitrary Schwartz test functions
- `propagator_convergence` — theorem deduced from
  `embeddedTwoPoint_eq_latticeGreenBilinear`
- `embeddedTwoPoint_uniform_bound` — `E[Φ_a(f)²] ≤ C · ‖f‖²` uniformly in a, N
- `continuumGreenBilinear_pos` — `G(f,f) > 0` for nonzero f

## Mathematical background

### Propagator convergence

The lattice propagator in Fourier space is:

  `Ĉ_a(k) = 1 / ((4/a²) Σ_i sin²(πk_i a/L) + m²)`

For k in any compact set, as a → 0 with L = Na → ∞:

  `Ĉ_a(k) → 1 / (|k|² + m²)`

since `(2/a) sin(πk_i a/L) → 2πk_i/L → k_i` (with appropriate scaling).

The rapid decay of f̂, ĝ controls the contribution from large k, giving:

  `a^{2d} Σ_{x,y} C_a(x,y) f(ax) g(ay) → ∫ f̂(k) ĝ(k) / (|k|²+m²) dk/(2π)^d`

### Uniform bound

All eigenvalues of `-Δ_a + m²` satisfy `λ ≥ m²`, so:

  `E[Φ_a(f)²] = ⟨f_a, C_a f_a⟩ ≤ (1/m²) · ‖f_a‖²_{L²(Λ_a)}`

The discretized L² norm `a^d Σ_x |f(ax)|²` converges to `‖f‖²_{L²(ℝ^d)}` and is
uniformly bounded for Schwartz f, giving `E[Φ_a(f)²] ≤ C/m²`.

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I
-/

import Pphi2.GaussianContinuumLimit.EmbeddedCovariance
import Pphi2.GeneralResults.DyninMityaginBilinear
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Data.ZMod.ValMinAbs
import SchwartzNuclear.HermiteNuclear

noncomputable section

open GaussianField MeasureTheory Filter

namespace Pphi2

variable (d N : ℕ) [NeZero N]

private noncomputable instance continuumFinNonempty [Fact (0 < d)] : Nonempty (Fin d) :=
  Fin.pos_iff_nonempty.mp Fact.out

private noncomputable instance continuumEuclideanNontrivial [Fact (0 < d)] :
    Nontrivial (EuclideanSpace ℝ (Fin d)) := inferInstance

private noncomputable instance continuumTestFunction_dyninMityagin [Fact (0 < d)] :
    DyninMityaginSpace (ContinuumTestFunction d) :=
  schwartz_dyninMityaginSpace

/-! ## Propagator convergence -/

/- **Basis-pair lattice propagator converges to the continuum Green's function.**

This is the remaining analytic input after all algebraic rewrites:
for each pair of Dynin-Mityagin basis vectors and lattice parameters
`a → 0` with `Na → ∞`, the lattice spectral Green form converges to the
continuum Green form.

The full Schwartz-space convergence theorem `latticeGreenBilinear_tendsto_continuum`
is proved later in this file by two DM-expansion steps plus polynomial bounds
on the lattice bilinear form applied to basis vectors.

Reference: Glimm-Jaffe §6.1, Simon Ch. I. -/
section ConvergenceAxiom

variable [Fact (0 < d)]
axiom latticeGreenBilinear_basis_tendsto_continuum
    (mass : ℝ) (hmass : 0 < mass)
    -- Sequence of lattice spacings tending to 0
    (a_seq : ℕ → ℝ) (ha_pos : ∀ n, 0 < a_seq n)
    (ha_lim : Tendsto a_seq atTop (nhds 0))
    -- Sequence of lattice sizes with N_n · a_n → ∞
    (N_seq : ℕ → ℕ) [∀ n, NeZero (N_seq n)]
    (hNa : Tendsto (fun n => (N_seq n : ℝ) * a_seq n) atTop atTop)
    (i j : ℕ) :
    Tendsto
      (fun n =>
        latticeGreenBilinear d (N_seq n) (a_seq n) mass
          (DyninMityaginSpace.basis i)
          (DyninMityaginSpace.basis j))
      atTop
      (nhds
        (continuumGreenBilinear d mass
          (DyninMityaginSpace.basis i)
          (DyninMityaginSpace.basis j)))

end ConvergenceAxiom

/-! ## Uniform bound on the embedded two-point function -/

/-- **Covariance upper bound via eigenvalue lower bound.**

The covariance `⟨T h, T h⟩ ≤ (1/m²) · ‖h‖²_ℓ²` because all eigenvalues of
the mass operator satisfy `λ_k ≥ m²`, hence `λ_k⁻¹ ≤ m⁻²`. By the spectral
decomposition `⟨Th, Th⟩ = Σ_k λ_k⁻¹ (e_k · h)²`, the bound follows from Parseval. -/
private theorem covariance_le_mass_inv_sq_norm (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (h : FinLatticeField d N) :
    GaussianField.covariance (latticeCovariance d N a mass ha hmass) h h ≤
    mass⁻¹ ^ 2 * ∑ x : FinLatticeSites d N, h x ^ 2 := by
  rw [lattice_covariance_eq_spectral]
  -- Bound each term: λ_k⁻¹ * (e_k · h)² ≤ m⁻² * (e_k · h)²
  calc ∑ k, (massEigenvalues d N a mass k)⁻¹ *
        (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * h x) *
        (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * h x)
      = ∑ k, (massEigenvalues d N a mass k)⁻¹ *
          (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * h x) ^ 2 := by
        congr 1; ext k; ring
    _ ≤ ∑ k, mass⁻¹ ^ 2 *
          (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * h x) ^ 2 := by
        apply Finset.sum_le_sum; intro k _
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        -- Need: λ_k⁻¹ ≤ m⁻²
        have hev_pos := massOperatorMatrix_eigenvalues_pos d N a mass ha hmass k
        have hev_ge : mass ^ 2 ≤ massEigenvalues d N a mass k := by
          -- Use the quadratic form: Σ_x e_k(x) * (Q e_k)(x) = λ_k ≥ m²
          -- because Q = -Δ + m² and -Δ ≥ 0
          set e_k := (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _)
          -- Quadratic form equals eigenvalue * norm² = eigenvalue * 1
          have hquad := massOperator_quadratic_eq_spectral (d := d) (N := N) a mass e_k
          -- The k-th coefficient of e_k in the eigenbasis is 1, rest are 0
          -- So the sum simplifies to lambda_k * 1
          have hcoeff : ∀ j : FinLatticeSites d N,
              (∑ x, (massEigenvectorBasis d N a mass j : EuclideanSpace ℝ _) x *
                e_k x) = if j = k then 1 else 0 := by
            intro j
            have hinner := (massEigenvectorBasis d N a mass).inner_eq_ite j k
            -- hinner: ∑ i, e_k(i) * e_j(i) = if j = k then 1 else 0
            rw [← hinner]
            apply Finset.sum_congr rfl; intro x _; exact mul_comm _ _
          rw [show (∑ x, (e_k : FinLatticeSites d N → ℝ) x *
              (massOperator d N a mass (e_k : FinLatticeSites d N → ℝ)) x) =
              ∑ x, e_k x * (massOperator d N a mass e_k) x from rfl] at hquad
          simp_rw [hcoeff] at hquad
          -- Simplify: (if j = k then 1 else 0)^2 → ite, then sum_ite_eq'
          have hquad' := hquad
          simp only [ite_pow, one_pow, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
            not_false_eq_true] at hquad'
          -- Now: ∑ x, eigenvalue x * if x = k then 1 else 0
          -- Rewrite mul_ite and simplify
          simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
            Finset.mem_univ, ite_true] at hquad'
          -- Now hquad': Σ_x e_k(x) * Q(e_k)(x) = massEigenvalues d N a mass k
          -- Lower bound from finiteLaplacian_neg_semidefinite
          have hmass_bound :
            mass ^ 2 * ∑ x : FinLatticeSites d N, e_k x ^ 2 ≤
            ∑ x, e_k x * (massOperator d N a mass e_k) x := by
            -- Expand massOperator = -Δ + m²·id
            have hexpand : ∀ x : FinLatticeSites d N,
                e_k x * (massOperator d N a mass e_k) x =
                -(e_k x * (finiteLaplacian d N a e_k) x) + mass ^ 2 * e_k x ^ 2 := by
              intro x
              simp only [massOperator, ContinuousLinearMap.add_apply,
                ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
                ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
                smul_eq_mul]
              ring
            have hlap := finiteLaplacian_neg_semidefinite d N a ha e_k
            simp_rw [hexpand, Finset.sum_add_distrib, ← Finset.mul_sum]
            linarith [Finset.sum_neg_distrib
              (f := fun x => e_k x * (finiteLaplacian d N a e_k) x)
              (s := Finset.univ)]
          -- e_k is normalized: Σ_x e_k(x)^2 = 1
          have hnorm : ∑ x : FinLatticeSites d N, e_k x ^ 2 = 1 := by
            have h_norm1 := (massEigenvectorBasis d N a mass).orthonormal.1 k
            simp only [EuclideanSpace.norm_eq] at h_norm1
            have h1 : ∑ x : FinLatticeSites d N, e_k x ^ 2 =
              ∑ x, ‖e_k x‖ ^ 2 := by
              congr 1; ext x; rw [Real.norm_eq_abs, sq_abs]
            rw [h1]
            have h3 : 0 ≤ ∑ x, ‖e_k x‖ ^ 2 :=
              Finset.sum_nonneg (fun x _ => sq_nonneg _)
            -- sqrt(s) = 1 implies s = sqrt(s)^2 = 1^2 = 1
            nlinarith [Real.sq_sqrt h3]
          rw [hnorm, mul_one] at hmass_bound
          linarith [hmass_bound, hquad']
        rw [inv_pow, ← one_div, ← one_div]
        exact div_le_div_of_nonneg_left zero_le_one (sq_pos_of_pos hmass) hev_ge
    _ = mass⁻¹ ^ 2 * ∑ k,
          (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * h x) ^ 2 := by
        rw [← Finset.mul_sum]
    _ = mass⁻¹ ^ 2 * ∑ x, h x ^ 2 := by
        congr 1
        -- Parseval: Σ_k (e_k · h)² = Σ_x h(x)²
        have := massEigenbasis_sum_mul_sum_eq_site_inner (d := d) (N := N) a mass h h
        simp only [sq]
        linarith

/-! ### Helper lemmas for the Schwartz Riemann sum bound -/

/-- EuclideanSpace component norm ≤ full norm: `‖y_i‖ ≤ ‖y‖`. -/
private lemma euclidean_component_le_norm
    (y : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    ‖y i‖ ≤ ‖y‖ := by
  have h1 : ‖y i‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have : y i = y.ofLp i := rfl; rw [this]
    exact Finset.single_le_sum (f := fun j => ‖y.ofLp j‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  nlinarith [sq_nonneg (‖y i‖ - ‖y‖), norm_nonneg y]

/-- Schwartz decay squared: `f(y)² ≤ S_f² / (1+‖y‖)^{2d}`. -/
private lemma schwartz_sq_decay (f : ContinuumTestFunction d)
    (y : EuclideanSpace ℝ (Fin d)) :
    f y ^ 2 ≤ (2 ^ d * ((Finset.Iic ((d : ℕ), (0 : ℕ))).sup
      fun m => SchwartzMap.seminorm ℝ m.1 m.2) f) ^ 2 /
    (1 + ‖y‖) ^ (2 * d) := by
  set S := 2 ^ d * ((Finset.Iic ((d : ℕ), (0 : ℕ))).sup
    fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  have hdecay : (1 + ‖y‖) ^ d * ‖f y‖ ≤ S := by
    have h := SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := ℝ) (m := (d, 0)) (k := d) (n := 0)
      (le_refl d) (le_refl 0) f y
    simp only [norm_iteratedFDeriv_zero] at h; exact h
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (1 + ‖y‖) ^ (2 * d))]
  calc f y ^ 2 * (1 + ‖y‖) ^ (2 * d)
      = (‖f y‖) ^ 2 * ((1 + ‖y‖) ^ d) ^ 2 := by
        rw [Real.norm_eq_abs, sq_abs, ← pow_mul]; ring_nf
    _ = ((1 + ‖y‖) ^ d * ‖f y‖) ^ 2 := by ring
    _ ≤ S ^ 2 := by
        apply sq_le_sq'
        · nlinarith [mul_nonneg
            (pow_nonneg
              (show (0 : ℝ) ≤ 1 + ‖y‖ by linarith [norm_nonneg y]) d)
            (norm_nonneg (f y))]
        · exact hdecay

/-- Product norm bound: `∏_i (1+‖y_i‖)² ≤ (1+‖y‖)^{2d}`. -/
private lemma norm_prod_bound (y : EuclideanSpace ℝ (Fin d)) :
    ∏ i : Fin d, (1 + ‖y i‖) ^ 2 ≤ (1 + ‖y‖) ^ (2 * d) := by
  rw [show (1 + ‖y‖) ^ (2 * d) = ∏ _i : Fin d, (1 + ‖y‖) ^ 2
    from by simp [Finset.prod_const, pow_mul]]
  exact Finset.prod_le_prod (fun i _ => sq_nonneg _)
    (fun i _ => pow_le_pow_left₀
      (by linarith [norm_nonneg (y i)])
      (by linarith [euclidean_component_le_norm d y i]) 2)

/-- Schwartz product bound: `f(y)² · ∏_i (1+‖y_i‖)² ≤ S_f²`. -/
private lemma schwartz_sq_product_bound (f : ContinuumTestFunction d)
    (y : EuclideanSpace ℝ (Fin d)) :
    f y ^ 2 * ∏ i : Fin d, (1 + ‖y i‖) ^ 2 ≤
    (2 ^ d * ((Finset.Iic ((d : ℕ), (0 : ℕ))).sup
      fun m => SchwartzMap.seminorm ℝ m.1 m.2) f) ^ 2 := by
  set S := 2 ^ d * ((Finset.Iic ((d : ℕ), (0 : ℕ))).sup
    fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  calc f y ^ 2 * ∏ i, (1 + ‖y i‖) ^ 2
      ≤ S ^ 2 / (1 + ‖y‖) ^ (2 * d) * ∏ i, (1 + ‖y i‖) ^ 2 :=
        mul_le_mul_of_nonneg_right (schwartz_sq_decay d f y)
          (Finset.prod_nonneg (fun i _ => sq_nonneg _))
    _ ≤ S ^ 2 / (1 + ‖y‖) ^ (2 * d) * (1 + ‖y‖) ^ (2 * d) :=
        mul_le_mul_of_nonneg_left (norm_prod_bound d y)
          (div_nonneg (sq_nonneg _) (le_of_lt (by positivity)))
    _ = S ^ 2 := by field_simp

/-- `signedVal` agrees with Mathlib's centered representative `ZMod.valMinAbs`. -/
private lemma signedVal_eq_valMinAbs (x : ZMod N) :
    signedVal N x = x.valMinAbs := by
  rw [signedVal, ZMod.valMinAbs_def_pos]
  have hxcast : x.cast = (x.val : ℤ) := by
    simpa using (ZMod.cast_eq_val (R := ℤ) x)
  by_cases h : x.val ≤ N / 2
  · have h' : x.cast ≤ (N : ℤ) / 2 := by
      rw [hxcast]
      omega
    simp [h, h']
  · have h' : ¬ x.cast ≤ (N : ℤ) / 2 := by
      intro hx
      apply h
      rw [hxcast] at hx
      omega
    simp [h, h']

/-- The absolute centered representative equals the minimum of the two boundary
distances on `ZMod N`. -/
private lemma signedVal_natAbs_eq_min (x : ZMod N) :
    (signedVal N x).natAbs = min (ZMod.val x) (N - ZMod.val x) := by
  rw [signedVal_eq_valMinAbs N x, ZMod.valMinAbs_natAbs_eq_min]

private lemma physPos_norm_component (a : ℝ) (ha : 0 < a)
    (x : FinLatticeSites d N) (i : Fin d) :
    ‖(physicalPosition d N a x) i‖ =
      a * ((signedVal N (x i)).natAbs : ℝ) := by
  rw [show (physicalPosition d N a x) i = a * (signedVal N (x i) : ℝ)
    from by rfl]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_of_lt ha)]
  have h_abs : ((signedVal N (x i)).natAbs : ℝ) = |(signedVal N (x i) : ℝ)| := by
    simpa using (Nat.cast_natAbs (α := ℝ) (signedVal N (x i)))
  rw [← h_abs]

/-- ZMod sum equals Finset.range sum. -/
private lemma zmod_sum_eq_range_sum (g : ℕ → ℝ) :
    ∑ x : ZMod N, g (ZMod.val x) =
    ∑ n ∈ Finset.range N, g n := by
  rw [show ∑ x : ZMod N, g (ZMod.val x) = ∑ n : Fin N, g n.val
    from Fintype.sum_bijective
      (fun (x : ZMod N) =>
        (⟨ZMod.val x, ZMod.val_lt x⟩ : Fin N))
      ⟨fun a b h => ZMod.val_injective N (Fin.mk.inj h),
       fun ⟨n, hn⟩ =>
        ⟨(n : ZMod N), by
          ext; exact ZMod.val_natCast_of_lt hn⟩⟩
      _ _ (fun _ => rfl),
    ← Finset.sum_range (f := g)]

/-- Telescoping: `a/(1+an)² ≤ 1/(1+a(n-1)) - 1/(1+an)` for `n ≥ 1`. -/
private lemma telescoping_step (a : ℝ) (ha : 0 < a)
    (n : ℕ) (hn : 1 ≤ n) :
    a / (1 + a * (n : ℝ)) ^ 2 ≤
    1 / (1 + a * ((n : ℝ) - 1)) - 1 / (1 + a * (n : ℝ)) := by
  have h1 : (0 : ℝ) < 1 + a * (n : ℝ) := by positivity
  have h2 : (0 : ℝ) < 1 + a * ((n : ℝ) - 1) := by
    nlinarith [show (1 : ℝ) ≤ (n : ℝ) from Nat.one_le_cast.mpr hn]
  suffices a / (1 + a * (n : ℝ)) ^ 2 ≤
      a / ((1 + a * ((n : ℝ) - 1)) * (1 + a * (n : ℝ))) by
    calc a / (1 + a * (n : ℝ)) ^ 2
        ≤ a / ((1 + a * ((n : ℝ) - 1)) * (1 + a * (n : ℝ))) := this
      _ = 1 / (1 + a * ((n : ℝ) - 1)) - 1 / (1 + a * (n : ℝ)) := by
          field_simp; ring
  exact div_le_div_of_nonneg_left (le_of_lt ha)
    (mul_pos h2 h1) (by nlinarith [le_of_lt h1])

/-- 1D sum bound: `Σ_{n ∈ range M} a/(1+an)² ≤ 2` for `0 < a ≤ 1`. -/
private lemma one_d_sum_bound (a : ℝ) (ha : 0 < a)
    (ha1 : a ≤ 1) (M : ℕ) :
    ∑ n ∈ Finset.range M,
      a / (1 + a * (n : ℝ)) ^ 2 ≤ 2 := by
  cases M with
  | zero => simp
  | succ K =>
    rw [Finset.sum_range_succ'
      (f := fun n => a / (1 + a * (n : ℝ)) ^ 2)]
    simp only [Nat.cast_zero, mul_zero, add_zero,
      one_pow, div_one]
    have htel : ∑ k ∈ Finset.range K,
        a / (1 + a * ((k : ℝ) + 1)) ^ 2 ≤
        ∑ k ∈ Finset.range K,
          (1 / (1 + a * (k : ℝ)) -
           1 / (1 + a * ((k : ℝ) + 1))) := by
      apply Finset.sum_le_sum; intro k _
      have h := telescoping_step a ha (k + 1)
        (Nat.le_add_left 1 k)
      simp only [Nat.cast_add, Nat.cast_one,
        show ((k : ℝ) + 1) - 1 = (k : ℝ) by ring] at h
      exact h
    have hsum_eq : ∑ k ∈ Finset.range K,
        (1 / (1 + a * (k : ℝ)) -
         1 / (1 + a * ((k : ℝ) + 1))) =
        1 - 1 / (1 + a * (K : ℝ)) := by
      have h := Finset.sum_range_sub'
        (fun k => 1 / (1 + a * (k : ℝ))) K
      simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one,
        mul_zero, add_zero, div_one] at h
      exact h
    -- Normalize ↑(k+1) to ↑k + 1 everywhere
    simp only [Nat.cast_add, Nat.cast_one] at htel ⊢
    rw [hsum_eq] at htel
    linarith [div_nonneg one_pos.le
      (le_of_lt
        (by positivity : (0 : ℝ) < 1 + a * (K : ℝ)))]

/-- Tail version of the 1D decay bound:
    `Σ_{n ∈ range M} a/(1+a(n+1))² ≤ 1`. -/
private lemma one_d_shift_sum_bound (a : ℝ) (ha : 0 < a) (M : ℕ) :
    ∑ n ∈ Finset.range M,
      a / (1 + a * ((n : ℝ) + 1)) ^ 2 ≤ 1 := by
  have htel : ∑ n ∈ Finset.range M,
      a / (1 + a * ((n : ℝ) + 1)) ^ 2 ≤
      ∑ n ∈ Finset.range M,
        (1 / (1 + a * (n : ℝ)) -
         1 / (1 + a * ((n : ℝ) + 1))) := by
    apply Finset.sum_le_sum
    intro n _
    have h := telescoping_step a ha (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
    simpa only [Nat.cast_add, Nat.cast_one,
      show ((n : ℝ) + 1) - 1 = (n : ℝ) by ring] using h
  calc ∑ n ∈ Finset.range M, a / (1 + a * ((n : ℝ) + 1)) ^ 2
      ≤ ∑ n ∈ Finset.range M,
          (1 / (1 + a * (n : ℝ)) -
           1 / (1 + a * ((n : ℝ) + 1))) := htel
    _ = 1 - 1 / (1 + a * (M : ℝ)) := by
        have h := Finset.sum_range_sub' (fun k => 1 / (1 + a * (k : ℝ))) M
        simpa only [Nat.cast_zero, Nat.cast_add, Nat.cast_one,
          mul_zero, add_zero, div_one] using h
    _ ≤ 1 := by
        have hpos : (0 : ℝ) < 1 + a * (M : ℝ) := by positivity
        linarith [div_nonneg one_pos.le (le_of_lt hpos)]

/-- 1D bound over `ZMod N` written in centered coordinates:
    `Σ_{n : ZMod N} a/(1+a·|signedVal n|)² ≤ 3`. -/
private lemma one_d_zmod_bound (a : ℝ) (ha : 0 < a)
    (ha1 : a ≤ 1) :
    ∑ n : ZMod N,
      a / (1 + a * ((signedVal N n).natAbs : ℝ)) ^ 2 ≤ 3 := by
  let g : ℕ → ℝ := fun n => a / (1 + a * (n : ℝ)) ^ 2
  have hpoint : ∀ n : ZMod N,
      g ((signedVal N n).natAbs) ≤ g (ZMod.val n) + g (N - ZMod.val n) := by
    intro n
    rw [signedVal_natAbs_eq_min N n]
    by_cases h : ZMod.val n ≤ N - ZMod.val n
    · rw [min_eq_left h]
      exact le_add_of_nonneg_right (by positivity)
    · rw [min_eq_right (Nat.le_of_lt (lt_of_not_ge h))]
      exact le_add_of_nonneg_left (by positivity)
  calc ∑ n : ZMod N, a / (1 + a * ((signedVal N n).natAbs : ℝ)) ^ 2
      = ∑ n : ZMod N, g ((signedVal N n).natAbs) := by
          simp [g]
    _ ≤ ∑ n : ZMod N, (g (ZMod.val n) + g (N - ZMod.val n)) := by
          exact Finset.sum_le_sum (fun n _ => hpoint n)
    _ = (∑ n : ZMod N, g (ZMod.val n)) + ∑ n : ZMod N, g (N - ZMod.val n) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ n ∈ Finset.range N, g n) + ∑ n ∈ Finset.range N, g (N - n) := by
          rw [zmod_sum_eq_range_sum N g, zmod_sum_eq_range_sum N (fun n => g (N - n))]
    _ = (∑ n ∈ Finset.range N, g n) + ∑ n ∈ Finset.range N, g (n + 1) := by
          congr 1
          trans ∑ n ∈ Finset.range N, g (N - 1 - n + 1)
          · apply Finset.sum_congr rfl
            intro n hn
            congr 1
            have hnlt : n < N := Finset.mem_range.mp hn
            omega
          · simpa [Nat.succ_eq_add_one] using
              (Finset.sum_range_reflect (fun n => g (n + 1)) N)
    _ ≤ 3 := by
          have h1 : ∑ n ∈ Finset.range N, g n ≤ 2 := one_d_sum_bound a ha ha1 N
          have h2 : ∑ n ∈ Finset.range N, g (n + 1) ≤ 1 := by
            simpa [g] using one_d_shift_sum_bound a ha N
          linarith

/-! ### Schwartz Riemann sum bound -/

private def schwartzSeminormWindow (d : ℕ) : Finset (ℕ × ℕ) :=
  Finset.Iic ((d : ℕ), (0 : ℕ))

private def schwartzDecayMajorant (d : ℕ) (f : ContinuumTestFunction d) : ℝ :=
  2 ^ d * ((schwartzSeminormWindow d).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) f

/-- The Riemann-sum estimate with an explicit seminorm majorant.

If `S` dominates the finite family of seminorms used in
`schwartz_sq_product_bound`, then the lattice Schwartz Riemann sum is bounded by
`S² * 3^d`. -/
private theorem schwartz_riemann_sum_bound_of_majorant
    (f : ContinuumTestFunction d) (S : ℝ)
    (hS :
      schwartzDecayMajorant d f ≤ S) :
    ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
    ∀ (N : ℕ) [NeZero N],
    a ^ d * ∑ x : FinLatticeSites d N,
      (evalAtSite d N a f x) ^ 2 ≤ S ^ 2 * 3 ^ d := by
  intro a ha ha1 N _
  have hmajorant_nonneg : 0 ≤ schwartzDecayMajorant d f := by
    unfold schwartzDecayMajorant
    exact mul_nonneg (by positivity)
      (apply_nonneg
        ((schwartzSeminormWindow d).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) f)
  have hS_nonneg : 0 ≤ S := le_trans hmajorant_nonneg hS
  simp only [evalAtSite]
  have hbound : ∀ x : FinLatticeSites d N,
      f (physicalPosition d N a x) ^ 2 ≤
      S ^ 2 / ∏ i : Fin d,
        (1 + a * ((signedVal N (x i)).natAbs : ℝ)) ^ 2 := by
    intro x
    have hprod_pos : (0 : ℝ) < ∏ i : Fin d,
        (1 + a * ((signedVal N (x i)).natAbs : ℝ)) ^ 2 :=
      Finset.prod_pos (fun i _ =>
        sq_pos_of_pos (by positivity))
    rw [le_div_iff₀ hprod_pos]
    calc f (physicalPosition d N a x) ^ 2 *
          ∏ i, (1 + a * ((signedVal N (x i)).natAbs : ℝ)) ^ 2
        = f (physicalPosition d N a x) ^ 2 *
          ∏ i, (1 + ‖(physicalPosition d N a x) i‖) ^ 2 := by
          congr 1; apply Finset.prod_congr rfl
          intro i _; congr 1; congr 1
          exact (physPos_norm_component d N a ha x i).symm
      _ ≤ schwartzDecayMajorant d f ^ 2 := by
          simpa [schwartzDecayMajorant, schwartzSeminormWindow] using
            schwartz_sq_product_bound d f (physicalPosition d N a x)
      _ ≤ S ^ 2 := by
          nlinarith [hS, hmajorant_nonneg]
  calc a ^ d * ∑ x, f (physicalPosition d N a x) ^ 2
      ≤ a ^ d * ∑ x : FinLatticeSites d N,
          S ^ 2 / ∏ i : Fin d,
            (1 + a * ((signedVal N (x i)).natAbs : ℝ)) ^ 2 := by
        gcongr with x
        exact hbound x
    _ = S ^ 2 * ∑ x : FinLatticeSites d N,
          ∏ i : Fin d,
            a / (1 + a * ((signedVal N (x i)).natAbs : ℝ)) ^ 2 := by
        conv_lhs =>
          rw [Finset.mul_sum]
          arg 2; ext x
          rw [show a ^ d * (S ^ 2 /
              ∏ i : Fin d,
                (1 + a * ((signedVal N (x i)).natAbs : ℝ)) ^ 2) =
            S ^ 2 * (a ^ d /
              ∏ i : Fin d,
                (1 + a * ((signedVal N (x i)).natAbs : ℝ)) ^ 2) from
              by ring]
          rw [show a ^ d = ∏ _i : Fin d, a from
            by simp [Finset.prod_const]]
          rw [← Finset.prod_div_distrib]
        rw [← Finset.mul_sum]
    _ = S ^ 2 * ∏ _i : Fin d,
          ∑ n : ZMod N,
            a / (1 + a * ((signedVal N n).natAbs : ℝ)) ^ 2 := by
        congr 1
        rw [← Fintype.prod_sum
          (fun _ => fun n : ZMod N =>
            a / (1 + a * ((signedVal N n).natAbs : ℝ)) ^ 2)]
    _ ≤ S ^ 2 * 3 ^ d := by
        gcongr
        rw [show (3 : ℝ) ^ d = ∏ _i : Fin d, (3 : ℝ)
          from by simp [Finset.prod_const]]
        exact Finset.prod_le_prod
          (fun i _ => Finset.sum_nonneg
            (fun n _ => div_nonneg
              (le_of_lt ha) (sq_nonneg _)))
          (fun i _ => one_d_zmod_bound N a ha ha1)

/-- **Schwartz Riemann sum bound.**

For a Schwartz function f : S(ℝ^d) and the lattice (ℤ/Nℤ)^d with spacing a,
the weighted sum `a^d · Σ_{x} |f(a·x)|²` is bounded uniformly in a ∈ (0,1] and N.

The proof uses:
1. Schwartz decay: `(1+‖y‖)^d · |f(y)| ≤ S_f` from seminorm bounds
2. Product factorization: `(1+‖y‖)^{2d} ≥ ∏_i (1+|y_i|)²`
3. Sum factorization: `Σ_x ∏_i g(x_i) = ∏_i Σ_n g(n)` over the lattice
4. 1D centered-coordinate bound: `Σ_n a/(1+a|n|)² ≤ 3` for `0 < a ≤ 1`

This gives `a^d Σ_x f(ax)² ≤ S_f² · 3^d`. -/
private theorem schwartz_riemann_sum_bound
    (f : ContinuumTestFunction d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
    ∀ (N : ℕ) [NeZero N],
    a ^ d * ∑ x : FinLatticeSites d N,
      (evalAtSite d N a f x) ^ 2 ≤ C := by
  set S := schwartzDecayMajorant d f
  refine ⟨S ^ 2 * 3 ^ d + 1, by positivity, ?_⟩
  intro a ha ha1 N _
  have hmain := schwartz_riemann_sum_bound_of_majorant (d := d) (N := N) f S (le_rfl) a ha ha1
  linarith

/-- Polynomial Riemann-sum bound on DM basis vectors of the Schwartz space. -/
private theorem schwartz_riemann_sum_basis_bound [Fact (0 < d)] :
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℕ, ∀ i (a : ℝ) (ha : 0 < a), a ≤ 1 →
    ∀ (N : ℕ) [NeZero N],
    a ^ d * ∑ x : FinLatticeSites d N,
      (evalAtSite d N a (DyninMityaginSpace.basis i) x) ^ 2 ≤
        C * (1 + (i : ℝ)) ^ r := by
  obtain ⟨D, hD_pos, r, hD⟩ :=
    finset_sup_poly_bound
      (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)
      (schwartzSeminormWindow d)
      (DyninMityaginSpace.basis (E := ContinuumTestFunction d))
      (fun m hm => by
        simpa using DyninMityaginSpace.basis_growth (E := ContinuumTestFunction d) m)
  set A : ℝ := 2 ^ d * D
  refine ⟨A ^ 2 * 3 ^ d + 1, by positivity, 2 * r, ?_⟩
  intro i a ha ha1 N _
  have hmajorant :
      schwartzDecayMajorant d (DyninMityaginSpace.basis (E := ContinuumTestFunction d) i) ≤
        A * (1 + (i : ℝ)) ^ r := by
    dsimp [schwartzDecayMajorant, schwartzSeminormWindow, A]
    calc
      2 ^ d *
          ((schwartzSeminormWindow d).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2)
            (DyninMityaginSpace.basis (E := ContinuumTestFunction d) i)
        ≤ 2 ^ d * (D * (1 + (i : ℝ)) ^ r) := by
            gcongr
            exact hD i
      _ = A * (1 + (i : ℝ)) ^ r := by ring
  have hmain :=
    schwartz_riemann_sum_bound_of_majorant
      (d := d) (N := N)
      (f := DyninMityaginSpace.basis (E := ContinuumTestFunction d) i)
      (S := A * (1 + (i : ℝ)) ^ r)
      hmajorant a ha ha1
  have hpow_nonneg : 0 ≤ (1 + (i : ℝ)) ^ (2 * r) := by positivity
  calc
    a ^ d * ∑ x : FinLatticeSites d N,
      (evalAtSite d N a (DyninMityaginSpace.basis i) x) ^ 2
      ≤ (A * (1 + (i : ℝ)) ^ r) ^ 2 * 3 ^ d := hmain
    _ = A ^ 2 * 3 ^ d * (1 + (i : ℝ)) ^ (2 * r) := by ring
    _ ≤ (A ^ 2 * 3 ^ d + 1) * (1 + (i : ℝ)) ^ (2 * r) := by
        have hA : A ^ 2 * 3 ^ d ≤ A ^ 2 * 3 ^ d + 1 := by linarith
        calc
          A ^ 2 * 3 ^ d * (1 + (i : ℝ)) ^ (2 * r)
            ≤ (A ^ 2 * 3 ^ d + 1) * (1 + (i : ℝ)) ^ (2 * r) :=
              mul_le_mul_of_nonneg_right hA hpow_nonneg

/-- The lattice Green form on the diagonal is controlled by any lattice
Riemann-sum bound for the corresponding test function. -/
private theorem latticeGreenBilinear_diag_bound_of_riemann_bound
    (mass : ℝ) (hmass : 0 < mass)
    (f : ContinuumTestFunction d) (C_f : ℝ)
    (hC : ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
      ∀ (N : ℕ) [NeZero N],
      a ^ d * ∑ x : FinLatticeSites d N, (evalAtSite d N a f x) ^ 2 ≤ C_f) :
    ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
      latticeGreenBilinear d N a mass f f ≤ mass⁻¹ ^ 2 * C_f := by
  intro a ha ha_le
  rw [← embeddedTwoPoint_eq_latticeGreenBilinear (d := d) (N := N) (a := a)
    (mass := mass) (ha := ha) (hmass := hmass) f f]
  set T := latticeCovariance d N a mass ha hmass
  set μ := latticeGaussianMeasure d N a mass ha hmass
  set h_f : FinLatticeField d N := fun x => a ^ d * evalAtSite d N a f x
  have hintegrand : ∀ ω : Configuration (FinLatticeField d N),
      (a ^ d * ∑ x, ω (Pi.single x 1) * evalAtSite d N a f x) *
      (a ^ d * ∑ x, ω (Pi.single x 1) * evalAtSite d N a f x) =
      (ω h_f) ^ 2 := by
    intro ω
    have hlin : ω h_f = a ^ d * ∑ x, ω (Pi.single x 1) * evalAtSite d N a f x := by
      show ω h_f = a ^ d * ∑ x, ω (Pi.single x 1) * evalAtSite d N a f x
      have : h_f = a ^ d • ∑ x : FinLatticeSites d N,
          evalAtSite d N a f x • Pi.single x (1 : ℝ) := by
        ext y; simp [h_f, Finset.sum_apply, Pi.single_apply]
      rw [this, map_smul, smul_eq_mul]
      congr 1
      rw [map_sum]
      congr 1; ext x
      rw [map_smul, smul_eq_mul, mul_comm]
    rw [hlin]
    ring
  rw [embeddedTwoPoint_eq_covariance (d := d) (N := N) (a := a)
    (mass := mass) (ha := ha) (hmass := hmass) f f]
  simp only [latticeEmbed_eval, latticeEmbedEval]
  have hintegrand_eq :
      (fun ω : Configuration (FinLatticeField d N) =>
        (a ^ d * ∑ x, ω (Pi.single x 1) * evalAtSite d N a f x) *
        (a ^ d * ∑ x, ω (Pi.single x 1) * evalAtSite d N a f x)) =
      fun ω => (ω h_f) ^ 2 := by
    ext ω
    exact hintegrand ω
  rw [hintegrand_eq]
  have hsecond :
      ∫ ω : Configuration (FinLatticeField d N), ω h_f ^ 2
        ∂latticeGaussianMeasure d N a mass ha hmass =
      GaussianField.covariance T h_f h_f := by
    simpa [T, latticeGaussianMeasure, GaussianField.covariance] using
      (GaussianField.second_moment_eq_covariance T h_f)
  rw [hsecond]
  calc
    GaussianField.covariance T h_f h_f
      ≤ mass⁻¹ ^ 2 * ∑ x, h_f x ^ 2 :=
        covariance_le_mass_inv_sq_norm d N a mass ha hmass h_f
    _ = mass⁻¹ ^ 2 * (a ^ d * a ^ d * ∑ x, (evalAtSite d N a f x) ^ 2) := by
        congr 1
        simp only [h_f, mul_pow, ← Finset.mul_sum]
        ring
    _ = mass⁻¹ ^ 2 * (a ^ d * (a ^ d * ∑ x, (evalAtSite d N a f x) ^ 2)) := by
        ring_nf
    _ ≤ mass⁻¹ ^ 2 * (1 * C_f) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        apply mul_le_mul _ (hC a ha ha_le N) (by positivity) (by positivity)
        exact pow_le_one₀ (le_of_lt ha) ha_le
    _ = mass⁻¹ ^ 2 * C_f := by ring

/-- Polynomial diagonal bound for the lattice Green form on DM basis vectors. -/
private theorem latticeGreenBilinear_basis_diag_bound [Fact (0 < d)]
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℕ, ∀ i (a : ℝ) (ha : 0 < a), a ≤ 1 →
      ∀ (N : ℕ) [NeZero N],
      latticeGreenBilinear d N a mass
        (DyninMityaginSpace.basis i)
        (DyninMityaginSpace.basis i) ≤
          C * (1 + (i : ℝ)) ^ r := by
  obtain ⟨C_f, hC_f_pos, r, hC_f⟩ := schwartz_riemann_sum_basis_bound (d := d)
  refine ⟨mass⁻¹ ^ 2 * C_f, mul_pos (sq_pos_of_pos (inv_pos.mpr hmass)) hC_f_pos, r, ?_⟩
  intro i a ha ha1 N _
  have h :=
    latticeGreenBilinear_diag_bound_of_riemann_bound
    (d := d) (N := N) mass hmass
    (DyninMityaginSpace.basis i)
    (C_f * (1 + (i : ℝ)) ^ r)
    (fun a ha ha1 N => hC_f i a ha ha1 N) a ha ha1
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

/-- Cross terms are controlled by diagonal lattice Green terms via
`2|xy| ≤ x² + y²` modewise in the spectral sum. -/
private theorem latticeGreenBilinear_abs_le_half_diag_add_diag
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f g : ContinuumTestFunction d) :
    |latticeGreenBilinear d N a mass f g| ≤
      (latticeGreenBilinear d N a mass f f +
        latticeGreenBilinear d N a mass g g) / 2 := by
  let Af : FinLatticeSites d N → ℝ := fun k =>
    ∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
      latticeTestField d N a f x
  let Ag : FinLatticeSites d N → ℝ := fun k =>
    ∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
      latticeTestField d N a g x
  unfold latticeGreenBilinear
  have hterm :
      ∀ k : FinLatticeSites d N,
        |(massEigenvalues d N a mass k)⁻¹ * Af k * Ag k| ≤
          (massEigenvalues d N a mass k)⁻¹ * ((Af k) ^ 2 + (Ag k) ^ 2) / 2 := by
    intro k
    have hLambda_nonneg : 0 ≤ (massEigenvalues d N a mass k)⁻¹ := by
      positivity [massOperatorMatrix_eigenvalues_pos d N a mass ha hmass k]
    have hxy_abs : 2 * (|Af k| * |Ag k|) ≤ |Af k| ^ 2 + |Ag k| ^ 2 := by
      nlinarith [sq_nonneg (|Af k| - |Ag k|)]
    have hxy : 2 * (|Af k| * |Ag k|) ≤ (Af k) ^ 2 + (Ag k) ^ 2 := by
      simpa [sq_abs] using hxy_abs
    have hscaled :
        (massEigenvalues d N a mass k)⁻¹ * (2 * (|Af k| * |Ag k|)) ≤
          (massEigenvalues d N a mass k)⁻¹ * ((Af k) ^ 2 + (Ag k) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hxy hLambda_nonneg
    have habs :
        2 * |(massEigenvalues d N a mass k)⁻¹ * Af k * Ag k| =
          (massEigenvalues d N a mass k)⁻¹ * (2 * (|Af k| * |Ag k|)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hLambda_nonneg]
      ring
    have hscaled' : 2 * |(massEigenvalues d N a mass k)⁻¹ * Af k * Ag k| ≤
        (massEigenvalues d N a mass k)⁻¹ * ((Af k) ^ 2 + (Ag k) ^ 2) := by
      rw [habs]
      exact hscaled
    have htwo_pos : (0 : ℝ) < 2 := by norm_num
    nlinarith
  calc
    |∑ k : FinLatticeSites d N, (massEigenvalues d N a mass k)⁻¹ * Af k * Ag k|
      ≤ ∑ k : FinLatticeSites d N,
          |(massEigenvalues d N a mass k)⁻¹ * Af k * Ag k| := by
            exact Finset.abs_sum_le_sum_abs (f := fun k : FinLatticeSites d N =>
              (massEigenvalues d N a mass k)⁻¹ * Af k * Ag k) (s := Finset.univ)
    _ ≤ ∑ k : FinLatticeSites d N,
          (massEigenvalues d N a mass k)⁻¹ * ((Af k) ^ 2 + (Ag k) ^ 2) / 2 := by
            exact Finset.sum_le_sum fun k _ => hterm k
    _ = ((∑ k : FinLatticeSites d N, (massEigenvalues d N a mass k)⁻¹ * Af k * Af k) +
          (∑ k : FinLatticeSites d N, (massEigenvalues d N a mass k)⁻¹ * Ag k * Ag k)) / 2 := by
        rw [show (fun k : FinLatticeSites d N =>
            (massEigenvalues d N a mass k)⁻¹ * ((Af k) ^ 2 + (Ag k) ^ 2) / 2) =
            fun k => ((massEigenvalues d N a mass k)⁻¹ * Af k * Af k +
              (massEigenvalues d N a mass k)⁻¹ * Ag k * Ag k) / 2 by
              ext k; ring]
        calc
          ∑ k : FinLatticeSites d N,
              ((massEigenvalues d N a mass k)⁻¹ * Af k * Af k +
                (massEigenvalues d N a mass k)⁻¹ * Ag k * Ag k) / 2
              = (1 / 2) * ∑ k : FinLatticeSites d N,
                  ((massEigenvalues d N a mass k)⁻¹ * Af k * Af k +
                    (massEigenvalues d N a mass k)⁻¹ * Ag k * Ag k) := by
                    rw [Finset.mul_sum]
                    congr 1
                    ext k
                    ring
          _ = (1 / 2) *
                ((∑ k : FinLatticeSites d N, (massEigenvalues d N a mass k)⁻¹ * Af k * Af k) +
                  (∑ k : FinLatticeSites d N, (massEigenvalues d N a mass k)⁻¹ * Ag k * Ag k)) := by
                    rw [Finset.sum_add_distrib]
          _ = ((∑ k : FinLatticeSites d N, (massEigenvalues d N a mass k)⁻¹ * Af k * Af k) +
                (∑ k : FinLatticeSites d N, (massEigenvalues d N a mass k)⁻¹ * Ag k * Ag k)) / 2 := by
                    ring
/-- Eventual polynomial basis-pair bound for the lattice Green form along any
continuum-limit sequence `a_n → 0`. -/
private theorem latticeGreenBilinear_basis_eventually_bound [Fact (0 < d)]
    (mass : ℝ) (hmass : 0 < mass)
    (a_seq : ℕ → ℝ) (ha_pos : ∀ n, 0 < a_seq n)
    (ha_lim : Tendsto a_seq atTop (nhds 0))
    (N_seq : ℕ → ℕ) [∀ n, NeZero (N_seq n)] :
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℕ,
      ∀ᶠ n in atTop, ∀ i j,
        |latticeGreenBilinear d (N_seq n) (a_seq n) mass
          (DyninMityaginSpace.basis i)
          (DyninMityaginSpace.basis j)| ≤
            C * (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r := by
  obtain ⟨C, hC_pos, r, hdiag⟩ := latticeGreenBilinear_basis_diag_bound (d := d) mass hmass
  have ha_le_one : ∀ᶠ n in atTop, a_seq n ≤ 1 := by
    have hmem : Set.Iic (1 : ℝ) ∈ nhds (0 : ℝ) :=
      Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num)
    exact ha_lim hmem
  refine ⟨C, hC_pos, r, ?_⟩
  filter_upwards [ha_le_one] with n hn i j
  have hii := hdiag i (a_seq n) (ha_pos n) hn (N_seq n)
  have hjj := hdiag j (a_seq n) (ha_pos n) hn (N_seq n)
  have hcross :=
    latticeGreenBilinear_abs_le_half_diag_add_diag
      (d := d) (N := N_seq n) (a := a_seq n) (mass := mass)
      (ha := ha_pos n) (hmass := hmass)
      (DyninMityaginSpace.basis i) (DyninMityaginSpace.basis j)
  have hpow_i_nonneg : 0 ≤ (1 + (i : ℝ)) ^ r := by positivity
  have hpow_j_nonneg : 0 ≤ (1 + (j : ℝ)) ^ r := by positivity
  have hsum_le_prod :
      (C * (1 + (i : ℝ)) ^ r + C * (1 + (j : ℝ)) ^ r) / 2 ≤
        C * (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r := by
    have hi_one : 1 ≤ (1 + (i : ℝ)) ^ r := by
      apply one_le_pow₀
      linarith
    have hj_one : 1 ≤ (1 + (j : ℝ)) ^ r := by
      apply one_le_pow₀
      linarith
    have hleft :
        C * (1 + (i : ℝ)) ^ r ≤ C * (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r := by
      calc
        C * (1 + (i : ℝ)) ^ r = C * (1 + (i : ℝ)) ^ r * 1 := by ring
        _ ≤ C * (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r := by
            exact mul_le_mul_of_nonneg_left hj_one
              (mul_nonneg (le_of_lt hC_pos) hpow_i_nonneg)
    have hright :
        C * (1 + (j : ℝ)) ^ r ≤ C * (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r := by
      calc
        C * (1 + (j : ℝ)) ^ r = 1 * (C * (1 + (j : ℝ)) ^ r) := by ring
        _ ≤ (1 + (i : ℝ)) ^ r * (C * (1 + (j : ℝ)) ^ r) := by
            exact mul_le_mul_of_nonneg_right hi_one
              (mul_nonneg (le_of_lt hC_pos) hpow_j_nonneg)
        _ = C * (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r := by ring
    have hsum :
        C * (1 + (i : ℝ)) ^ r + C * (1 + (j : ℝ)) ^ r ≤
          2 * (C * (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r) := by
      linarith
    nlinarith [hsum]
  calc
    |latticeGreenBilinear d (N_seq n) (a_seq n) mass
      (DyninMityaginSpace.basis i)
      (DyninMityaginSpace.basis j)|
      ≤ (latticeGreenBilinear d (N_seq n) (a_seq n) mass
            (DyninMityaginSpace.basis i)
            (DyninMityaginSpace.basis i) +
          latticeGreenBilinear d (N_seq n) (a_seq n) mass
            (DyninMityaginSpace.basis j)
            (DyninMityaginSpace.basis j)) / 2 := hcross
    _ ≤ (C * (1 + (i : ℝ)) ^ r + C * (1 + (j : ℝ)) ^ r) / 2 := by
        gcongr
    _ ≤ C * (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r := hsum_le_prod

/-! ### Right-continuous bilinear forms for the DM extension theorem -/

private noncomputable def continuumEvalCLM (x : EuclideanSpace ℝ (Fin d)) :
    ContinuumTestFunction d →L[ℝ] ℝ :=
  SchwartzMap.mkCLMtoNormedSpace (fun f => f x)
    (fun f g => by simp [SchwartzMap.add_apply])
    (fun a f => by simp [SchwartzMap.smul_apply])
    ⟨{(0, 0)}, 1, zero_le_one, fun f => by
      simp only [one_mul, Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply]
      exact SchwartzMap.norm_le_seminorm ℝ f x⟩

@[simp] private theorem continuumEvalCLM_apply
    (x : EuclideanSpace ℝ (Fin d)) (f : ContinuumTestFunction d) :
    continuumEvalCLM (d := d) x f = f x := by
  simp [continuumEvalCLM, SchwartzMap.mkCLMtoNormedSpace]

private noncomputable def latticeModeCoeffCLM (a mass : ℝ)
    (k : FinLatticeSites d N) :
    ContinuumTestFunction d →L[ℝ] ℝ :=
  ∑ x : FinLatticeSites d N,
    (a ^ d * (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) •
      continuumEvalCLM (d := d) (physicalPosition d N a x)

@[simp] private theorem latticeModeCoeffCLM_apply
    (a mass : ℝ) (k : FinLatticeSites d N) (f : ContinuumTestFunction d) :
    latticeModeCoeffCLM (d := d) (N := N) a mass k f =
      ∑ x : FinLatticeSites d N,
        (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
          latticeTestField d N a f x := by
  simp [latticeModeCoeffCLM, latticeTestField, evalAtSite, continuumEvalCLM_apply, smul_eq_mul,
    mul_assoc]
  apply Finset.sum_congr rfl
  intro x hx
  ring

private noncomputable def latticeGreenBilinearRightCLM
    (a mass : ℝ) (f : ContinuumTestFunction d) :
    ContinuumTestFunction d →L[ℝ] ℝ :=
  ∑ k : FinLatticeSites d N,
    ((massEigenvalues d N a mass k)⁻¹ *
      (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
        latticeTestField d N a f x)) •
      latticeModeCoeffCLM (d := d) (N := N) a mass k

@[simp] private theorem latticeGreenBilinearRightCLM_apply
    (a mass : ℝ) (f g : ContinuumTestFunction d) :
    latticeGreenBilinearRightCLM (d := d) (N := N) a mass f g =
      latticeGreenBilinear d N a mass f g := by
  simp [latticeGreenBilinearRightCLM, latticeGreenBilinear, latticeModeCoeffCLM_apply, mul_assoc,
    mul_left_comm, mul_comm]

private theorem latticeGreenBilinear_symm
    (a mass : ℝ) (f g : ContinuumTestFunction d) :
    latticeGreenBilinear d N a mass f g =
      latticeGreenBilinear d N a mass g f := by
  unfold latticeGreenBilinear
  congr 1
  ext k
  ring

private def continuumKernel (mass : ℝ) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun k =>
    (2 * Real.pi) ^ (-(d : ℤ)) / (‖k‖ ^ 2 + mass ^ 2)

private theorem continuumKernel_eq_scaled (mass : ℝ) (hmass : 0 < mass) :
    continuumKernel d mass =
      fun k =>
        (2 * Real.pi) ^ (-(d : ℤ)) * mass⁻¹ ^ 2 *
          (1 + ‖(mass⁻¹ : ℝ) • k‖ ^ 2) ^ (-1 : ℝ) := by
  funext k
  have hmass_ne : mass ≠ 0 := ne_of_gt hmass
  have hnorm : ‖(mass⁻¹ : ℝ) • k‖ ^ 2 = mass⁻¹ ^ 2 * ‖k‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hmass)]
    ring
  unfold continuumKernel
  rw [hnorm]
  have haux : 1 + mass⁻¹ ^ 2 * ‖k‖ ^ 2 = (mass ^ 2 + ‖k‖ ^ 2) / mass ^ 2 := by
    field_simp [hmass_ne]
  rw [haux, Real.rpow_neg_one]
  field_simp [hmass_ne]
  ring

private theorem continuumKernel_hasTemperateGrowth (mass : ℝ) (hmass : 0 < mass) :
    (continuumKernel d mass).HasTemperateGrowth := by
  rw [continuumKernel_eq_scaled (d := d) mass hmass]
  have hconst :
      (fun _ : EuclideanSpace ℝ (Fin d) =>
        (2 * Real.pi) ^ (-(d : ℤ)) * mass⁻¹ ^ 2).HasTemperateGrowth := by
    fun_prop
  have hbase :
      (fun x : EuclideanSpace ℝ (Fin d) => (1 + ‖x‖ ^ 2) ^ (-1 : ℝ)).HasTemperateGrowth := by
    fun_prop
  have hscale :
      (fun k : EuclideanSpace ℝ (Fin d) => (mass⁻¹ : ℝ) • k).HasTemperateGrowth := by
    fun_prop
  exact hconst.mul (hbase.comp hscale)

private def continuumGreenWeight (mass : ℝ) (f : ContinuumTestFunction d) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun k => continuumKernel d mass k * f k

private theorem continuumGreenWeight_hasTemperateGrowth
    (mass : ℝ) (hmass : 0 < mass) (f : ContinuumTestFunction d) :
    (continuumGreenWeight d mass f).HasTemperateGrowth := by
  unfold continuumGreenWeight
  exact (continuumKernel_hasTemperateGrowth (d := d) mass hmass).mul f.hasTemperateGrowth

private noncomputable def continuumGreenBilinearRightCLM
    (mass : ℝ) (hmass : 0 < mass) (f : ContinuumTestFunction d) :
    ContinuumTestFunction d →L[ℝ] ℝ :=
  (SchwartzMap.integralCLM ℝ
      (volume : Measure (EuclideanSpace ℝ (Fin d)))).comp
    (SchwartzMap.smulLeftCLM ℝ (continuumGreenWeight d mass f))

@[simp] private theorem continuumGreenBilinearRightCLM_apply
    (mass : ℝ) (hmass : 0 < mass) (f g : ContinuumTestFunction d) :
    continuumGreenBilinearRightCLM (d := d) mass hmass f g =
      continuumGreenBilinear d mass f g := by
  rw [continuumGreenBilinearRightCLM, ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply,
    SchwartzMap.smulLeftCLM_apply (continuumGreenWeight_hasTemperateGrowth (d := d) mass hmass f)]
  unfold continuumGreenWeight continuumGreenBilinear continuumKernel
  have hpointwise :
      (fun x : EuclideanSpace ℝ (Fin d) =>
        ((2 * Real.pi) ^ (-(d : ℤ)) / (‖x‖ ^ 2 + mass ^ 2) * f x) • g x) =
      fun x => (2 * Real.pi) ^ (-(d : ℤ)) * (f x * g x / (‖x‖ ^ 2 + mass ^ 2)) := by
    funext x
    have hden : ‖x‖ ^ 2 + mass ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg ‖x‖, sq_pos_of_pos hmass]
    simp [smul_eq_mul]
    field_simp [hden]
  rw [hpointwise, integral_const_mul]
  rfl

private theorem continuumGreenBilinear_symm
    (mass : ℝ) (f g : ContinuumTestFunction d) :
    continuumGreenBilinear d mass f g =
      continuumGreenBilinear d mass g f := by
  unfold continuumGreenBilinear
  congr 1
  apply integral_congr_ae
  filter_upwards with k
  ring

/-- Extend basis-pair convergence of the lattice Green form to arbitrary
Schwartz test functions via the generic Dynin-Mityagin bilinear theorem. -/
theorem latticeGreenBilinear_tendsto_continuum [Fact (0 < d)]
    (mass : ℝ) (hmass : 0 < mass)
    (f g : ContinuumTestFunction d)
    (a_seq : ℕ → ℝ) (ha_pos : ∀ n, 0 < a_seq n)
    (ha_lim : Tendsto a_seq atTop (nhds 0))
    (N_seq : ℕ → ℕ) [∀ n, NeZero (N_seq n)]
    (hNa : Tendsto (fun n => (N_seq n : ℝ) * a_seq n) atTop atTop) :
    Tendsto
      (fun n => latticeGreenBilinear d (N_seq n) (a_seq n) mass f g)
      atTop
      (nhds (continuumGreenBilinear d mass f g)) := by
  obtain ⟨C, hC_pos, r, hbound⟩ :=
    latticeGreenBilinear_basis_eventually_bound (d := d) mass hmass a_seq ha_pos ha_lim N_seq
  simpa [latticeGreenBilinearRightCLM_apply, continuumGreenBilinearRightCLM_apply] using
    (GaussianField.tendsto_of_symmetric_basis_tendsto
      (l := atTop)
      (B_seq := fun n f =>
        latticeGreenBilinearRightCLM (d := d) (N := N_seq n) (a := a_seq n) (mass := mass) f)
      (B := fun f => continuumGreenBilinearRightCLM (d := d) (mass := mass) hmass f)
      (h_symm_seq := by
        intro n f g
        simpa [latticeGreenBilinearRightCLM_apply] using latticeGreenBilinear_symm
          (d := d) (N := N_seq n) (a := a_seq n) (mass := mass) f g)
      (h_symm := by
        intro f g
        simpa [continuumGreenBilinearRightCLM_apply] using
          continuumGreenBilinear_symm (d := d) (mass := mass) f g)
      (h_basis_bound := by
        refine ⟨C, hC_pos, r, r, ?_⟩
        filter_upwards [hbound] with n hn i j
        simpa [latticeGreenBilinearRightCLM_apply] using hn i j)
      (h_basis_tendsto := by
        intro i j
        simpa [latticeGreenBilinearRightCLM_apply, continuumGreenBilinearRightCLM_apply] using
          latticeGreenBilinear_basis_tendsto_continuum
            (d := d) mass hmass a_seq ha_pos ha_lim N_seq hNa i j)
      f g)

/-- The original propagator-convergence statement, now proved by combining the
spectral rewrite with the generic Dynin-Mityagin bilinear extension theorem. -/
theorem propagator_convergence [Fact (0 < d)]
    (mass : ℝ) (hmass : 0 < mass)
    (f g : ContinuumTestFunction d)
    (a_seq : ℕ → ℝ) (ha_pos : ∀ n, 0 < a_seq n)
    (ha_lim : Tendsto a_seq atTop (nhds 0))
    (N_seq : ℕ → ℕ) [∀ n, NeZero (N_seq n)]
    (hNa : Tendsto (fun n => (N_seq n : ℝ) * a_seq n) atTop atTop) :
    Tendsto
      (fun n => embeddedTwoPoint d (N_seq n) (a_seq n) mass (ha_pos n) hmass f g)
      atTop
      (nhds (continuumGreenBilinear d mass f g)) := by
  have hgreen := latticeGreenBilinear_tendsto_continuum
    (d := d) (mass := mass) hmass f g a_seq ha_pos ha_lim N_seq hNa
  simpa [embeddedTwoPoint_eq_latticeGreenBilinear] using hgreen

theorem embeddedTwoPoint_uniform_bound (mass : ℝ) (hmass : 0 < mass)
    (f : ContinuumTestFunction d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
    embeddedTwoPoint d N a mass ha hmass f f ≤ C := by
  -- Get the Schwartz Riemann sum bound
  obtain ⟨C_f, hC_pos, hC_bound⟩ := schwartz_riemann_sum_bound d f
  refine ⟨mass⁻¹ ^ 2 * C_f, mul_pos (sq_pos_of_pos (inv_pos.mpr hmass)) hC_pos, ?_⟩
  intro a ha ha_le
  -- Step 1: Rewrite as integral over lattice configurations
  rw [embeddedTwoPoint_eq_covariance]
  -- Step 2: Unfold latticeEmbed to latticeEmbedEval
  simp only [latticeEmbed_eval, latticeEmbedEval]
  -- The integrand is (a^d * Σ_x ω(e_x) f(ax))^2
  -- This is (ω(h_f))^2 where h_f(x) = a^d * f(ax), by linearity of ω
  set T := latticeCovariance d N a mass ha hmass
  set μ := latticeGaussianMeasure d N a mass ha hmass
  set h_f : FinLatticeField d N := fun x => a ^ d * evalAtSite d N a f x
  -- Show the integrand equals (ω h_f)^2
  have hintegrand : ∀ ω : Configuration (FinLatticeField d N),
      (a ^ d * ∑ x, ω (Pi.single x 1) * evalAtSite d N a f x) *
      (a ^ d * ∑ x, ω (Pi.single x 1) * evalAtSite d N a f x) =
      (ω h_f) ^ 2 := by
    intro ω
    -- ω is a CLM, so ω(Σ_x c_x e_x) = Σ_x c_x ω(e_x) by linearity
    have hlin : ω h_f = a ^ d * ∑ x, ω (Pi.single x 1) * evalAtSite d N a f x := by
      show ω h_f = a ^ d * ∑ x, ω (Pi.single x 1) * evalAtSite d N a f x
      have : h_f = a ^ d • ∑ x : FinLatticeSites d N,
          evalAtSite d N a f x • Pi.single x (1 : ℝ) := by
        ext y; simp [h_f, Finset.sum_apply, Pi.single_apply]
      rw [this, map_smul, smul_eq_mul]
      congr 1
      rw [map_sum]
      congr 1; ext x
      rw [map_smul, smul_eq_mul, mul_comm]
    rw [hlin]; ring
  simp_rw [hintegrand]
  -- Step 3: Apply second moment = covariance
  -- μ = latticeGaussianMeasure = GaussianField.measure T, unfold so rw can match
  have hμ_eq : μ = GaussianField.measure T := rfl
  rw [hμ_eq, GaussianField.second_moment_eq_covariance T h_f]
  -- Now goal: @inner ℝ _ _ (T h_f) (T h_f) ≤ mass⁻¹ ^ 2 * C_f
  -- Unfold inner to covariance
  rw [← GaussianField.covariance]
  -- Step 4: Apply covariance upper bound
  calc GaussianField.covariance T h_f h_f
      ≤ mass⁻¹ ^ 2 * ∑ x, h_f x ^ 2 :=
        covariance_le_mass_inv_sq_norm d N a mass ha hmass h_f
    _ = mass⁻¹ ^ 2 * (a ^ d * a ^ d * ∑ x, (evalAtSite d N a f x) ^ 2) := by
        congr 1; simp only [h_f, mul_pow, ← Finset.mul_sum]; ring
    _ = mass⁻¹ ^ 2 * (a ^ d * (a ^ d * ∑ x, (evalAtSite d N a f x) ^ 2)) := by
        ring_nf
    _ ≤ mass⁻¹ ^ 2 * (1 * C_f) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        apply mul_le_mul _ (hC_bound a ha ha_le N) (by positivity) (by positivity)
        exact pow_le_one₀ (le_of_lt ha) ha_le
    _ = mass⁻¹ ^ 2 * C_f := by ring

/-- **Positivity of the continuum Green's function.**

  `G(f, f) > 0` for nonzero f ∈ S(ℝ^d)

The Fourier-space integrand `|f̂(k)|² / (|k|² + m²)` is nonneg, and
strictly positive on a set of positive measure (since f̂ ≠ 0 for f ≠ 0
in Schwartz space — the Fourier transform is injective on S). -/
theorem continuumGreenBilinear_pos (mass : ℝ) (hmass : 0 < mass)
    (f : ContinuumTestFunction d) (hf : f ≠ 0) :
    0 < continuumGreenBilinear d mass f f := by
  unfold continuumGreenBilinear
  -- Factor as positive_constant * positive_integral
  apply mul_pos
  · -- (2π)^(-d) > 0
    exact zpow_pos (by positivity) _
  · -- ∫ f(k)² / (‖k‖² + m²) dk > 0
    -- Abbreviate the integrand
    set g := fun k : EuclideanSpace ℝ (Fin d) =>
      f.toFun k * f.toFun k / (‖k‖ ^ 2 + mass ^ 2)
    -- The denominator is positive everywhere
    have hden_pos : ∀ k : EuclideanSpace ℝ (Fin d), 0 < ‖k‖ ^ 2 + mass ^ 2 :=
      fun k => add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hmass)
    -- g is nonneg
    have hg_nonneg : 0 ≤ g := fun k =>
      div_nonneg (mul_self_nonneg (a := f.toFun k)) (le_of_lt (hden_pos k))
    -- g is continuous
    have hg_cont : Continuous g := by
      apply Continuous.div (f.continuous.mul f.continuous)
        ((continuous_norm.pow 2).add continuous_const)
      intro k; exact ne_of_gt (hden_pos k)
    -- g is integrable (bounded by f²/m², and f² is integrable since f ∈ L²)
    have hf_sq_int : Integrable (fun k => (f k) ^ 2)
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))) :=
      (f.memLp 2).integrable_sq
    have hg_int : Integrable g := by
      apply (hf_sq_int.div_const (mass ^ 2)).mono hg_cont.aestronglyMeasurable
      apply Filter.Eventually.of_forall; intro k
      rw [Real.norm_eq_abs, abs_of_nonneg (hg_nonneg k)]
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
      -- g(k) = f(k)^2 / (||k||^2 + m^2) ≤ f(k)^2 / m^2 since ||k||^2 + m^2 ≥ m^2
      change f.toFun k * f.toFun k / (‖k‖ ^ 2 + mass ^ 2) ≤ f k ^ 2 / mass ^ 2
      have hfk : f.toFun k = f k := rfl
      rw [hfk, ← sq]
      apply div_le_div_of_nonneg_left (sq_nonneg (f k)) (by positivity)
      linarith [sq_nonneg ‖k‖]
    -- f ≠ 0 gives k₀ with f(k₀) ≠ 0
    obtain ⟨k₀, hk₀⟩ := DFunLike.ne_iff.mp hf
    -- g(k₀) ≠ 0
    have hg_k₀ : g k₀ ≠ 0 := by
      simp only [g]
      exact ne_of_gt (div_pos (mul_self_pos.mpr hk₀) (hden_pos k₀))
    -- Integral positive by `integral_pos_of_integrable_nonneg_nonzero`
    exact integral_pos_of_integrable_nonneg_nonzero hg_cont hg_int hg_nonneg hg_k₀

end Pphi2

end
