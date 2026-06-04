/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Lattice.AsymCovariance
import Pphi2.AsymTorus.AsymTransferInstantiation

/-!
# Crux-2: the energy / density factorization for the asym φ⁴₂ cylinder

Towards the Layer-B2 measure↔operator bridge: the slice-pushforward of the interacting
lattice measure equals the periodic path measure of the transfer kernel `k`. The analytic
heart is the **energy factorization** — through the slice iso `asymSliceEquiv`, the mass
operator's quadratic form `⟨φ, Q φ⟩` (`Q = massOperatorAsym = −Δ_a + m²`) splits into a
time-coupling term + a per-slice spatial term, matching `∏_t k(ψ_t, ψ_{t+1})` exactly.

The full `a`-power bookkeeping (and its Gemini-deep-think vetting, 2026-06-04) is in
`docs/crux2-energy-factorization.md`. This file formalizes step 1 of that roadmap: the
summation-by-parts decomposition of `⟨φ, Q φ⟩` into nearest-neighbour bond sums.

## Main results

* `asym_sbp_direction` — periodic summation by parts in one lattice direction.
* `massOperatorAsym_quadratic_form_bonds` — `⟨φ, Q φ⟩ = a⁻²·(time bonds + space bonds) + m²·‖φ‖²`.
-/

open MeasureTheory GaussianField ReflectionPositivity
open scoped BigOperators

namespace Pphi2

variable {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]

/-- The two unit lattice vectors: `e1` = one step in time, `e2` = one step in space. -/
local notation "e1" => ((1 : ZMod Nt), (0 : ZMod Ns))
local notation "e2" => ((0 : ZMod Nt), (1 : ZMod Ns))

/-- **Periodic summation by parts** in one lattice direction `v`:
`∑ₓ f(x)·(f(x+v)+f(x−v)−2f(x)) = −∑ₓ (f(x+v)−f(x))²`. Re-proves the (private)
`asym_direction_sum_eq_neg_sq` of `GaussianField.Lattice.AsymCovariance` for local use. -/
lemma asym_sbp_direction (f : AsymLatticeField Nt Ns) (v : AsymLatticeSites Nt Ns) :
    ∑ x, f x * (f (x + v) + f (x - v) - 2 * f x) = -(∑ x, (f (x + v) - f x) ^ 2) := by
  -- reindexing `x ↦ x + v` is measure-preserving on the finite additive group of sites
  have reindex_sq : ∑ x, f (x + v) ^ 2 = ∑ x, f x ^ 2 :=
    Fintype.sum_equiv (Equiv.addRight v) (fun x => f (x + v) ^ 2) (fun x => f x ^ 2)
      (fun x => by simp)
  have shift_bwd : ∑ x, f x * f (x - v) = ∑ x, f (x + v) * f x := by
    rw [← Equiv.sum_comp (Equiv.addRight v) (fun x => f x * f (x - v))]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
  have comm_sum : ∑ x, f (x + v) * f x = ∑ x, f x * f (x + v) :=
    Finset.sum_congr rfl (fun x _ => mul_comm _ _)
  have lhs_eq : ∑ x, f x * (f (x + v) + f (x - v) - 2 * f x) =
      (∑ x, f x * f (x + v)) + (∑ x, f x * f (x - v)) + (-2) * (∑ x, f x ^ 2) := by
    have h1 : ∀ x, f x * (f (x + v) + f (x - v) - 2 * f x) =
        f x * f (x + v) + f x * f (x - v) + (-2) * (f x ^ 2) := fun x => by ring
    simp_rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [lhs_eq, shift_bwd, comm_sum]
  have rhs_eq : -(∑ x, (f (x + v) - f x) ^ 2) =
      -(∑ x, f (x + v) ^ 2) + 2 * (∑ x, f x * f (x + v)) + (-1) * (∑ x, f x ^ 2) := by
    have h2 : ∀ x, (f (x + v) - f x) ^ 2 =
        f (x + v) ^ 2 + (-2) * (f x * f (x + v)) + f x ^ 2 := fun x => by ring
    simp_rw [h2, Finset.sum_add_distrib, ← Finset.mul_sum]; ring
  rw [rhs_eq, reindex_sq]; ring

/-- **Quadratic form of the mass operator in nearest-neighbour bond form.** Summation by
parts turns `⟨φ, Q φ⟩` (`Q = −Δ_a + m²`) into `a⁻²·(time-bond sum + space-bond sum) + m²·‖φ‖²`.
This is the lattice-side input to the energy factorization. -/
theorem massOperatorAsym_quadratic_form_bonds (a mass : ℝ) (φ : AsymLatticeField Nt Ns) :
    ∑ x, φ x * (massOperatorAsym Nt Ns a mass φ) x =
      a⁻¹ ^ 2 * (∑ x, (φ (x + e1) - φ x) ^ 2)
      + a⁻¹ ^ 2 * (∑ x, (φ (x + e2) - φ x) ^ 2)
      + mass ^ 2 * ∑ x, φ x ^ 2 := by
  -- pointwise value of `Q φ`
  have hQ : ∀ x, (massOperatorAsym Nt Ns a mass φ) x =
      -(finiteLaplacianAsymFun Nt Ns a φ x) + mass ^ 2 * φ x := by
    intro x
    simp only [massOperatorAsym, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply,
      Pi.smul_apply, smul_eq_mul]
    rfl
  simp only [hQ]
  -- split the on-site sum into the Laplacian piece and the mass piece
  have hsplit : ∀ x, φ x * (-(finiteLaplacianAsymFun Nt Ns a φ x) + mass ^ 2 * φ x) =
      -(φ x * finiteLaplacianAsymFun Nt Ns a φ x) + mass ^ 2 * φ x ^ 2 := fun x => by ring
  simp only [hsplit, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  -- the Laplacian quadratic form, via the two-direction split + SBP
  have e1p : ∀ x : AsymLatticeSites Nt Ns, ((x.1 + 1, x.2) : AsymLatticeSites Nt Ns) = x + e1 := by
    intro x; simp [Prod.ext_iff]
  have e1m : ∀ x : AsymLatticeSites Nt Ns, ((x.1 - 1, x.2) : AsymLatticeSites Nt Ns) = x - e1 := by
    intro x; simp [Prod.ext_iff]
  have e2p : ∀ x : AsymLatticeSites Nt Ns, ((x.1, x.2 + 1) : AsymLatticeSites Nt Ns) = x + e2 := by
    intro x; simp [Prod.ext_iff]
  have e2m : ∀ x : AsymLatticeSites Nt Ns, ((x.1, x.2 - 1) : AsymLatticeSites Nt Ns) = x - e2 := by
    intro x; simp [Prod.ext_iff]
  have hlap : ∑ x, φ x * finiteLaplacianAsymFun Nt Ns a φ x =
      a⁻¹ ^ 2 * (-(∑ x, (φ (x + e1) - φ x) ^ 2)) +
      a⁻¹ ^ 2 * (-(∑ x, (φ (x + e2) - φ x) ^ 2)) := by
    simp only [finiteLaplacianAsymFun]
    simp_rw [e1p, e1m, e2p, e2m]
    have expand : ∀ x : AsymLatticeSites Nt Ns,
        φ x * (a⁻¹ ^ 2 * (φ (x + e1) + φ (x - e1) + φ (x + e2) + φ (x - e2) - 4 * φ x)) =
        a⁻¹ ^ 2 * (φ x * (φ (x + e1) + φ (x - e1) - 2 * φ x)) +
        a⁻¹ ^ 2 * (φ x * (φ (x + e2) + φ (x - e2) - 2 * φ x)) := fun x => by ring
    simp_rw [expand, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [asym_sbp_direction φ e1, asym_sbp_direction φ e2]
  rw [hlap]
  ring

/-! ## Step 1b — pushing the bond sums through the slice iso `asymSliceEquiv`

Each lattice bond sum becomes a time-indexed family of spatial sums on the slices
`ψ_t = asymSliceEquiv φ t : SpatialField Ns`. The spatial index `ZMod Ns` is reindexed to
`Fin Ns` via the ring iso `ZMod.finEquiv`, which commutes with the successor (used for the
spatial bonds). -/

/-- `ZMod.finEquiv` (a ring iso) commutes with the successor: `finEquiv (i+1) = finEquiv i + 1`. -/
private lemma finEquiv_succ (i : Fin Ns) :
    (ZMod.finEquiv Ns).toEquiv (i + 1) = (ZMod.finEquiv Ns).toEquiv i + 1 := by
  change (ZMod.finEquiv Ns) (i + 1) = (ZMod.finEquiv Ns) i + 1
  rw [map_add, map_one]

/-- Mass sum through the slice iso: `∑_x φ(x)² = ∑_t ∑_i ψ_t(i)²`. -/
theorem asym_sq_sum_slice (φ : AsymLatticeField Nt Ns) :
    ∑ x, φ x ^ 2 =
      ∑ t : ZMod Nt, ∑ i : Fin Ns, (asymSliceEquiv Nt Ns φ t i) ^ 2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [← Equiv.sum_comp (ZMod.finEquiv Ns).toEquiv (fun s => φ (t, s) ^ 2)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [asymSliceEquiv_apply]

/-- Time-bond sum through the slice iso:
`∑_x (φ(x+e1)−φ(x))² = ∑_t ∑_i (ψ_{t+1}(i)−ψ_t(i))²`. -/
theorem asym_timeBond_sum_slice (φ : AsymLatticeField Nt Ns) :
    ∑ x, (φ (x + e1) - φ x) ^ 2 =
      ∑ t : ZMod Nt, ∑ i : Fin Ns,
        (asymSliceEquiv Nt Ns φ (t + 1) i - asymSliceEquiv Nt Ns φ t i) ^ 2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [← Equiv.sum_comp (ZMod.finEquiv Ns).toEquiv (fun s => (φ ((t, s) + e1) - φ (t, s)) ^ 2)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Prod.mk_add_mk, add_zero]
  rw [asymSliceEquiv_apply, asymSliceEquiv_apply]

/-- Space-bond sum through the slice iso:
`∑_x (φ(x+e2)−φ(x))² = ∑_t ∑_i (ψ_t(i+1)−ψ_t(i))²` (uses `finEquiv_succ`). -/
theorem asym_spaceBond_sum_slice (φ : AsymLatticeField Nt Ns) :
    ∑ x, (φ (x + e2) - φ x) ^ 2 =
      ∑ t : ZMod Nt, ∑ i : Fin Ns,
        (asymSliceEquiv Nt Ns φ t (i + 1) - asymSliceEquiv Nt Ns φ t i) ^ 2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [← Equiv.sum_comp (ZMod.finEquiv Ns).toEquiv (fun s => (φ ((t, s) + e2) - φ (t, s)) ^ 2)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Prod.mk_add_mk, add_zero]
  rw [asymSliceEquiv_apply, asymSliceEquiv_apply, ← finEquiv_succ]

/-! ## Step 1c — assembly: the free-action half in slice form -/

/-- **Slice form of the mass-operator quadratic form** (the free-action half of the energy
factorization). Combining `massOperatorAsym_quadratic_form_bonds` with the slice-bridging
lemmas, `(a²/2)·⟨φ,Qφ⟩` equals the time-coupling double sum `+` the spatial-kinetic double sum
`+` the mass double sum over slices. The `a²·a⁻²=1` cancellation needs `a ≠ 0`. -/
theorem massOperatorAsym_quadratic_form_slice (a mass : ℝ) (ha : a ≠ 0)
    (φ : AsymLatticeField Nt Ns) :
    (a ^ 2 / 2) * ∑ x, φ x * (massOperatorAsym Nt Ns a mass φ) x =
      (1 / 2) * (∑ t : ZMod Nt, ∑ i : Fin Ns,
          (asymSliceEquiv Nt Ns φ (t + 1) i - asymSliceEquiv Nt Ns φ t i) ^ 2)
      + (1 / 2) * (∑ t : ZMod Nt, ∑ i : Fin Ns,
          (asymSliceEquiv Nt Ns φ t (i + 1) - asymSliceEquiv Nt Ns φ t i) ^ 2)
      + (a ^ 2 / 2) * mass ^ 2 * (∑ t : ZMod Nt, ∑ i : Fin Ns,
          (asymSliceEquiv Nt Ns φ t i) ^ 2) := by
  rw [massOperatorAsym_quadratic_form_bonds, asym_timeBond_sum_slice,
    asym_spaceBond_sum_slice, asym_sq_sum_slice]
  have hcancel : a ^ 2 * a⁻¹ ^ 2 = 1 := by
    rw [inv_pow]; exact mul_inv_cancel₀ (pow_ne_zero 2 ha)
  set T := ∑ t : ZMod Nt, ∑ i : Fin Ns,
    (asymSliceEquiv Nt Ns φ (t + 1) i - asymSliceEquiv Nt Ns φ t i) ^ 2
  set S := ∑ t : ZMod Nt, ∑ i : Fin Ns,
    (asymSliceEquiv Nt Ns φ t (i + 1) - asymSliceEquiv Nt Ns φ t i) ^ 2
  set Q := ∑ t : ZMod Nt, ∑ i : Fin Ns, (asymSliceEquiv Nt Ns φ t i) ^ 2
  linear_combination ((T + S) / 2) * hcancel

/-! ## Step 1d — identifying the slice double-sums with `timeCoupling` / `spatialKinetic`,
and the generic on-site bridging. -/

/-- The time-coupling double sum is the per-slice `timeCoupling` summed over time. -/
theorem timeCoupling_sum_slice (φ : AsymLatticeField Nt Ns) :
    ∑ t : ZMod Nt,
        timeCoupling Ns (asymSliceEquiv Nt Ns φ t) (asymSliceEquiv Nt Ns φ (t + 1)) =
      (1 / 2) * ∑ t : ZMod Nt, ∑ i : Fin Ns,
        (asymSliceEquiv Nt Ns φ (t + 1) i - asymSliceEquiv Nt Ns φ t i) ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  unfold timeCoupling
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- The spatial-kinetic double sum is `a²·`(per-slice `spatialKinetic` summed over time);
the `a²·a⁻²=1` cancellation needs `a ≠ 0`. -/
theorem spatialKinetic_sum_slice (a : ℝ) (ha : a ≠ 0) (φ : AsymLatticeField Nt Ns) :
    a ^ 2 * ∑ t : ZMod Nt, spatialKinetic Ns a (asymSliceEquiv Nt Ns φ t) =
      (1 / 2) * ∑ t : ZMod Nt, ∑ i : Fin Ns,
        (asymSliceEquiv Nt Ns φ t (i + 1) - asymSliceEquiv Nt Ns φ t i) ^ 2 := by
  have hcancel : a ^ 2 * a⁻¹ ^ 2 = 1 := by
    rw [inv_pow]; exact mul_inv_cancel₀ (pow_ne_zero 2 ha)
  unfold spatialKinetic
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  linear_combination
    ((asymSliceEquiv Nt Ns φ t (i + 1) - asymSliceEquiv Nt Ns φ t i) ^ 2 / 2) * hcancel

/-- **Generic on-site bridging**: `∑_x g(φ(x)) = ∑_t ∑_i g(ψ_t(i))` for any `g : ℝ → ℝ`
(covers the mass term `g = (·²)` and the Wick interaction). -/
theorem asym_onsite_sum_slice (g : ℝ → ℝ) (φ : AsymLatticeField Nt Ns) :
    ∑ x, g (φ x) = ∑ t : ZMod Nt, ∑ i : Fin Ns, g (asymSliceEquiv Nt Ns φ t i) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [← Equiv.sum_comp (ZMod.finEquiv Ns).toEquiv (fun s => g (φ (t, s)))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [asymSliceEquiv_apply]

/-! ## Step 1e — the energy exponent factorization (capstone of step 1) -/

/-- **Energy exponent factorization.** The full interacting lattice action (relative to
Lebesgue) factorizes through the slice iso as a sum over time of `timeCoupling + a²·spatialAction`:
`(a²/2)·⟨φ,Qφ⟩ + a²·Σ_x :P:(φ(x)) = Σ_t [timeCoupling(ψ_t,ψ_{t+1}) + a²·spatialAction(ψ_t)]`.
This is the `−log` form of `dμ_int/dλ = (1/Z)∏_t k(ψ_t,ψ_{t+1})`; the remaining `exp`/measure
wrapping routes through the (asym) Gaussian-density bridge (crux-1). Needs `a ≠ 0`. -/
theorem energy_exponent_factorization (P : InteractionPolynomial) (a mass : ℝ) (ha : a ≠ 0)
    (φ : AsymLatticeField Nt Ns) :
    (a ^ 2 / 2) * (∑ x, φ x * (massOperatorAsym Nt Ns a mass φ) x)
      + a ^ 2 * ∑ x, wickPolynomial P (wickConstantAsym Nt Ns a mass) (φ x) =
    ∑ t : ZMod Nt,
      (timeCoupling Ns (asymSliceEquiv Nt Ns φ t) (asymSliceEquiv Nt Ns φ (t + 1))
        + a ^ 2 * spatialAction Ns P a mass (wickConstantAsym Nt Ns a mass)
            (asymSliceEquiv Nt Ns φ t)) := by
  have htc := timeCoupling_sum_slice (Nt := Nt) (Ns := Ns) φ
  have hsk := spatialKinetic_sum_slice (Nt := Nt) (Ns := Ns) a ha φ
  have hq := massOperatorAsym_quadratic_form_slice (Nt := Nt) (Ns := Ns) a mass ha φ
  have hwick := asym_onsite_sum_slice (Nt := Nt) (Ns := Ns)
    (fun y => wickPolynomial P (wickConstantAsym Nt Ns a mass) y) φ
  have hpot : a ^ 2 * ∑ t : ZMod Nt,
        spatialPotential Ns P a mass (wickConstantAsym Nt Ns a mass) (asymSliceEquiv Nt Ns φ t) =
      (a ^ 2 / 2) * mass ^ 2 * (∑ t : ZMod Nt, ∑ i : Fin Ns, (asymSliceEquiv Nt Ns φ t i) ^ 2)
        + a ^ 2 * ∑ t : ZMod Nt, ∑ i : Fin Ns,
            wickPolynomial P (wickConstantAsym Nt Ns a mass) (asymSliceEquiv Nt Ns φ t i) := by
    simp only [spatialPotential, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    congr 1 <;>
      exact Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun i _ => by ring))
  rw [hq, hwick, Finset.sum_add_distrib, htc, ← Finset.mul_sum]
  simp only [spatialAction]
  rw [Finset.sum_add_distrib, mul_add, hsk, hpot]
  ring

/-! ## Step 2 (exp level) — kernel product equals `exp(−action)`

The remaining measure-level conclusion `μ_int.map sliceEquiv = pathMeasure` routes through the
asym Gaussian-density bridge (crux-1); this exp-level identity is the last piece provable
without it: the abstract `periodicPathDensity` of `asymTransferKernel` equals `exp(−S)` where
`S` is the interacting lattice action. -/

/-- The transfer kernel splits as `exp(−(a²/2)·spatialAction(x)) · exp(−timeCoupling(x,y)) ·
exp(−(a²/2)·spatialAction(y))`. -/
private lemma asymTransferKernel_eq_exp (P : InteractionPolynomial) (a mass : ℝ)
    (x y : SpatialField Ns) :
    asymTransferKernel Nt Ns P a mass x y =
      Real.exp (-(a ^ 2 / 2) * spatialAction Ns P a mass (wickConstantAsym Nt Ns a mass) x)
      * Real.exp (-timeCoupling Ns x y)
      * Real.exp (-(a ^ 2 / 2) * spatialAction Ns P a mass (wickConstantAsym Nt Ns a mass) y) := by
  unfold asymTransferKernel asymTransferWeight transferGaussian
  have htc : timeCoupling Ns 0 (x - y) = timeCoupling Ns x y := by
    unfold timeCoupling
    congr 1
    exact Finset.sum_congr rfl (fun s _ => by simp only [Pi.sub_apply, Pi.zero_apply]; ring)
  rw [htc]

/-- **Kernel product = `exp(−action)`.** The periodic path density of `asymTransferKernel`
along the slices of `φ` equals `exp` of minus the interacting lattice action. Combined with
`energy_exponent_factorization` (the `−log` identity); needs `a ≠ 0`. -/
theorem periodicPathDensity_asymTransferKernel_eq_exp (P : InteractionPolynomial) (a mass : ℝ)
    (ha : a ≠ 0) (φ : AsymLatticeField Nt Ns) :
    periodicPathDensity (asymTransferKernel Nt Ns P a mass) Nt (asymSliceEquiv Nt Ns φ) =
      Real.exp (-((a ^ 2 / 2) * (∑ x, φ x * (massOperatorAsym Nt Ns a mass φ) x)
        + a ^ 2 * ∑ x, wickPolynomial P (wickConstantAsym Nt Ns a mass) (φ x))) := by
  rw [periodicPathDensity]
  -- collapse each kernel factor into a single `exp`
  have hker2 : ∀ t : ZMod Nt, asymTransferKernel Nt Ns P a mass
        (asymSliceEquiv Nt Ns φ t) (asymSliceEquiv Nt Ns φ (t + 1)) =
      Real.exp ((-(a ^ 2 / 2) * spatialAction Ns P a mass (wickConstantAsym Nt Ns a mass)
            (asymSliceEquiv Nt Ns φ t))
          + (-timeCoupling Ns (asymSliceEquiv Nt Ns φ t) (asymSliceEquiv Nt Ns φ (t + 1)))
          + (-(a ^ 2 / 2) * spatialAction Ns P a mass (wickConstantAsym Nt Ns a mass)
            (asymSliceEquiv Nt Ns φ (t + 1)))) := by
    intro t
    rw [asymTransferKernel_eq_exp, ← Real.exp_add, ← Real.exp_add]
  simp_rw [hker2]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- reindex the `ψ (t+1)` spatial-action sum to a `ψ t` sum
  have hshift' : (∑ t : ZMod Nt, -(a ^ 2 / 2) * spatialAction Ns P a mass
        (wickConstantAsym Nt Ns a mass) (asymSliceEquiv Nt Ns φ (t + 1))) =
      ∑ t : ZMod Nt, -(a ^ 2 / 2) * spatialAction Ns P a mass
        (wickConstantAsym Nt Ns a mass) (asymSliceEquiv Nt Ns φ t) :=
    Equiv.sum_comp (Equiv.addRight (1 : ZMod Nt))
      (fun t => -(a ^ 2 / 2) * spatialAction Ns P a mass
        (wickConstantAsym Nt Ns a mass) (asymSliceEquiv Nt Ns φ t))
  rw [hshift', energy_exponent_factorization P a mass ha φ,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  conv_rhs => rw [neg_eq_neg_one_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun t _ => by ring)

end Pphi2
