import Lattice.CirculantDFT2d

noncomputable section

namespace GaussianField

open Matrix Finset
open scoped BigOperators

variable (N : ℕ) [NeZero N]

/-- Product DFT basis function on the `d`-dimensional discrete torus. -/
def latticeFourierProductBasisFun (d : ℕ) (m : Fin d → Fin N)
    (x : FinLatticeSites d N) : ℝ :=
  ∏ i : Fin d, latticeFourierBasisFun N (m i) (x i)

/-- Split a sum over `(ZMod N)^(d+1)` into the first coordinate and the tail. -/
theorem sum_finLatticeSites_succ {α : Type*} [AddCommMonoid α]
    (d : ℕ) (F : FinLatticeSites (d + 1) N → α) :
    ∑ x : FinLatticeSites (d + 1) N, F x =
      ∑ z : ZMod N, ∑ xs : FinLatticeSites d N, F (Fin.cons z xs) := by
  let e : FinLatticeSites (d + 1) N ≃ ZMod N × FinLatticeSites d N :=
    { toFun := fun x => (x 0, fun i => x i.succ)
      invFun := fun p => Fin.cons p.1 p.2
      left_inv := by
        intro x
        funext i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro j
          rfl
      right_inv := by
        intro p
        cases p
        rfl }
  calc
    ∑ x : FinLatticeSites (d + 1) N, F x
      = ∑ p : ZMod N × FinLatticeSites d N, F (Fin.cons p.1 p.2) := by
          exact Fintype.sum_equiv e
            (fun x : FinLatticeSites (d + 1) N => F x)
            (fun p : ZMod N × FinLatticeSites d N => F (Fin.cons p.1 p.2))
            (fun x => by
              simpa [e] using congrArg F (e.left_inv x).symm)
    _ = ∑ z : ZMod N, ∑ xs : FinLatticeSites d N, F (Fin.cons z xs) := by
          rw [Fintype.sum_prod_type]

/-- The squared norm of a product basis vector factors coordinatewise. -/
theorem latticeFourierProductBasis_sq_sum
    : ∀ d : ℕ, ∀ m : Fin d → Fin N,
      ∑ x : FinLatticeSites d N, latticeFourierProductBasisFun N d m x ^ 2 =
        ∏ i : Fin d, latticeFourierNormSq N (m i)
  | 0, m => by
      simp [latticeFourierProductBasisFun, latticeFourierNormSq]
  | d + 1, m => by
      rw [sum_finLatticeSites_succ (N := N) d
        (F := fun x : FinLatticeSites (d + 1) N =>
          latticeFourierProductBasisFun N (d + 1) m x ^ 2)]
      simp_rw [latticeFourierProductBasisFun, Fin.prod_univ_succ]
      rw [Finset.sum_comm]
      calc
        ∑ xs : FinLatticeSites d N,
            ∑ z : ZMod N,
              (latticeFourierBasisFun N (m 0) z *
                latticeFourierProductBasisFun N d (fun i => m i.succ) xs) ^ 2
          = ∑ xs : FinLatticeSites d N,
              ∑ z : ZMod N,
                latticeFourierBasisFun N (m 0) z ^ 2 *
                  latticeFourierProductBasisFun N d (fun i => m i.succ) xs ^ 2 := by
                    refine Finset.sum_congr rfl ?_
                    intro xs hx
                    refine Finset.sum_congr rfl ?_
                    intro z hz
                    ring
        _ = ∑ xs : FinLatticeSites d N,
              (∑ z : ZMod N, latticeFourierBasisFun N (m 0) z ^ 2) *
                latticeFourierProductBasisFun N d (fun i => m i.succ) xs ^ 2 := by
                  refine Finset.sum_congr rfl ?_
                  intro xs hx
                  rw [Finset.sum_mul]
        _ = (∑ z : ZMod N, latticeFourierBasisFun N (m 0) z ^ 2) *
              ∑ xs : FinLatticeSites d N,
                latticeFourierProductBasisFun N d (fun i => m i.succ) xs ^ 2 := by
                  rw [← Finset.mul_sum]
        _ = latticeFourierNormSq N (m 0) *
              ∏ i : Fin d, latticeFourierNormSq N (m i.succ) := by
                  rw [latticeFourierNormSq, latticeFourierProductBasis_sq_sum d
                    (fun i => m i.succ)]
        _ = ∏ i : Fin (d + 1), latticeFourierNormSq N (m i) := by
                  exact
                    (Fin.prod_univ_succ
                      (f := fun i : Fin (d + 1) => latticeFourierNormSq N (↑(m i) : ℕ))).symm
      exact Fin.prod_univ_succAbove (fun i ↦ latticeFourierNormSq N ↑(m i)) 0

/-- The mass operator is surjective in every finite dimension. -/
theorem massOperator_surjective (d : ℕ) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    Function.Surjective (massOperator d N a mass) := by
  have hinj : Function.Injective (massOperator d N a mass) := by
    intro f g hfg
    by_contra hne
    have hne' : f - g ≠ 0 := sub_ne_zero.mpr hne
    have hpos := massOperator_pos_def d N a mass ha hmass (f - g) hne'
    have hzero : ∑ x, (f - g) x * (massOperator d N a mass (f - g)) x = 0 := by
      have : massOperator d N a mass (f - g) = 0 := by
        ext x
        simp [map_sub, hfg, sub_self]
      simp [this]
    linarith
  exact (massOperator d N a mass).toLinearMap.surjective_of_injective hinj

private lemma latticeFourierProductBasisFun_update (d : ℕ) (m : Fin d → Fin N)
    (x : FinLatticeSites d N) (i : Fin d) (z : ZMod N) :
    latticeFourierProductBasisFun N d m (Function.update x i z) =
      latticeFourierBasisFun N (m i) z *
        Finset.prod (Finset.univ \ {i}) (fun j => latticeFourierBasisFun N (m j) (x j)) := by
  unfold latticeFourierProductBasisFun
  calc
    ∏ j : Fin d, latticeFourierBasisFun N (m j) ((Function.update x i z) j)
      = latticeFourierBasisFun N (m i) z *
          Finset.prod (Finset.univ \ {i})
            (fun j => latticeFourierBasisFun N (m j) ((Function.update x i z) j)) := by
              simpa [Function.update] using
                (Finset.prod_eq_mul_prod_diff_singleton (s := Finset.univ) i
                  (fun j => latticeFourierBasisFun N (m j) ((Function.update x i z) j))
                  (by
                    intro hi
                    exact False.elim (hi (Finset.mem_univ i))))
    _ = latticeFourierBasisFun N (m i) z *
          Finset.prod (Finset.univ \ {i}) (fun j => latticeFourierBasisFun N (m j) (x j)) := by
            congr 1
            refine Finset.prod_congr rfl ?_
            intro j hj
            have hji : j ≠ i := by
              simpa [Finset.mem_singleton] using (show j ∈ Finset.univ ∧ j ∉ ({i} : Finset (Fin d)) from by
                simpa [Finset.mem_sdiff] using hj)
            simp [Function.update, hji]

/-- A product of 1D DFT modes is an eigenvector of the `d`-dimensional mass
operator with eigenvalue `Σᵢ λᵢ + mass²`. -/
theorem massOperator_product_eigenvector_family (d : ℕ) (a mass : ℝ) (ha : a ≠ 0)
    (m : Fin d → Fin N) (x : FinLatticeSites d N) :
    (massOperator d N a mass (latticeFourierProductBasisFun N d m)) x =
      ((∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2) *
        latticeFourierProductBasisFun N d m x := by
  have hplus : ∀ i : Fin d,
      (fun j => if j = i then x j + 1 else x j) = Function.update x i (x i + 1) := by
    intro i
    funext j
    by_cases hji : j = i <;> simp [Function.update, hji]
  have hminus : ∀ i : Fin d,
      (fun j => if j = i then x j - 1 else x j) = Function.update x i (x i - 1) := by
    intro i
    funext j
    by_cases hji : j = i <;> simp [Function.update, hji]
  have hcoord : ∀ i : Fin d,
      -(a⁻¹ ^ 2 *
          (((latticeFourierProductBasisFun N d m fun j => if j = i then x j + 1 else x j) +
              latticeFourierProductBasisFun N d m (fun j => if j = i then x j - 1 else x j)) -
            2 * latticeFourierProductBasisFun N d m x)) =
        latticeEigenvalue1d N a (m i) * latticeFourierProductBasisFun N d m x := by
    intro i
    have h1d := dft_1d_eigenvalue_pointwise N a ha (m i) (m i).isLt (x i)
    set tail : ℝ := Finset.prod (Finset.univ \ {i})
      (fun j => latticeFourierBasisFun N (m j) (x j))
    have hself :
        latticeFourierProductBasisFun N d m x =
          latticeFourierBasisFun N (m i) (x i) * tail := by
      simpa [tail, Function.update_self] using
        (latticeFourierProductBasisFun_update (N := N) (d := d) (m := m) (x := x) (i := i)
          (z := x i))
    rw [hplus i]
    rw [latticeFourierProductBasisFun_update (N := N) (d := d) (m := m) (x := x) (i := i)
          (z := x i + 1)]
    rw [hminus i]
    rw [latticeFourierProductBasisFun_update (N := N) (d := d) (m := m) (x := x) (i := i)
          (z := x i - 1)]
    rw [hself]
    linear_combination
      tail * h1d
  have hcoord_update : ∀ i : Fin d,
      -(a⁻¹ ^ 2 *
          ((latticeFourierProductBasisFun N d m (Function.update x i (x i + 1)) +
              latticeFourierProductBasisFun N d m (Function.update x i (x i - 1))) -
            2 * latticeFourierProductBasisFun N d m x)) =
        latticeEigenvalue1d N a (m i) * latticeFourierProductBasisFun N d m x := by
    intro i
    simpa [hplus i, hminus i] using hcoord i
  simp only [massOperator, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul]
  simp only [finiteLaplacian, ContinuousLinearMap.coe_mk',
    finiteLaplacianLM, LinearMap.coe_mk, AddHom.coe_mk,
    finiteLaplacianFun]
  calc
    -(a⁻¹ ^ 2 *
        ∑ i : Fin d,
          (((latticeFourierProductBasisFun N d m fun j => if j = i then x j + 1 else x j) +
              latticeFourierProductBasisFun N d m (fun j => if j = i then x j - 1 else x j)) -
            2 * latticeFourierProductBasisFun N d m x)) +
        mass ^ 2 * latticeFourierProductBasisFun N d m x
      = -(a⁻¹ ^ 2 *
          ∑ i : Fin d,
            ((latticeFourierProductBasisFun N d m (Function.update x i (x i + 1)) +
                latticeFourierProductBasisFun N d m (Function.update x i (x i - 1))) -
              2 * latticeFourierProductBasisFun N d m x)) +
          mass ^ 2 * latticeFourierProductBasisFun N d m x := by
            refine congrArg
              (fun t : ℝ => -(a⁻¹ ^ 2 * t) + mass ^ 2 * latticeFourierProductBasisFun N d m x) ?_
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hplus i, hminus i]
    _
      = (∑ i : Fin d, latticeEigenvalue1d N a (m i) *
            latticeFourierProductBasisFun N d m x) +
          mass ^ 2 * latticeFourierProductBasisFun N d m x := by
            rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
            simpa using (Finset.sum_congr rfl (fun i _ => hcoord_update i))
    _ = ((∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2) *
          latticeFourierProductBasisFun N d m x := by
            rw [← Finset.sum_mul]
            ring

end GaussianField

end
