import Pphi2.NelsonEstimate.FieldDecomposition
import Pphi2.NelsonEstimate.HeatKernelBound
import Lattice.FKG
import MarkovSemigroups.Matrix.HeatKernel
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory
open scoped Matrix.Norms.L2Operator

private lemma integral_one_div_sqrt_eq_two :
    (∫ u in (0 : ℝ)..1, (1 : ℝ) / Real.sqrt u) = 2 := by
  calc
    (∫ u in (0 : ℝ)..1, (1 : ℝ) / Real.sqrt u)
      = ∫ u in (0 : ℝ)..1, u ^ ((-1 : ℝ) / 2) := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards with u hu
          have hu0 : 0 < u := by
            simpa using hu.1
          have hpow : (u ^ ((1 : ℝ) / 2))⁻¹ = u ^ (-((1 : ℝ) / 2)) := by
            simpa using (Real.rpow_neg (le_of_lt hu0) ((1 : ℝ) / 2)).symm
          have hneg : -((1 : ℝ) / 2) = ((-1 : ℝ) / 2) := by
            ring
          rw [show (1 / Real.sqrt u : ℝ) = (u ^ ((1 : ℝ) / 2))⁻¹ by
            simp [one_div, Real.sqrt_eq_rpow], hpow, hneg]
    _ = 2 := by
          rw [integral_rpow]
          · norm_num
          · left
            norm_num

private lemma unitSquare_inv_add_integral_eq_two_log_two :
    (∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, (1 : ℝ) / (u + v)) =
      2 * Real.log 2 := by
  have hinner : ∀ u ∈ Set.Ioc (0 : ℝ) 1,
      (∫ v in (0 : ℝ)..1, (1 : ℝ) / (u + v)) = Real.log (u + 1) - Real.log u := by
    intro u hu
    have hshift := intervalIntegral.integral_comp_add_left
      (f := fun x : ℝ => (1 : ℝ) / x) (a := (0 : ℝ)) (b := 1) u
    rw [show (∫ v in (0 : ℝ)..1, (1 : ℝ) / (u + v)) = ∫ x in u..u + 1, (1 : ℝ) / x by
      simpa [add_comm] using hshift]
    have hu1 : 0 < u + 1 := by
      nlinarith [hu.1]
    rw [integral_one_div_of_pos hu.1 hu1]
    have hu_ne : u + 1 ≠ 0 := ne_of_gt hu1
    rw [Real.log_div hu_ne hu.1.ne']
  have hlogshift_int :
      IntervalIntegrable (fun u : ℝ => Real.log (u + 1)) MeasureSpace.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    have hcont : ContinuousOn (fun u : ℝ => u + 1) (Set.uIcc (0 : ℝ) 1) := by
      fun_prop
    refine Real.continuousOn_log.comp hcont ?_
    intro u hu
    have hu0 : 0 ≤ u := by
      simpa using hu.1
    have : 0 < u + 1 := by
      nlinarith
    exact ne_of_gt this
  have hshiftlog :
      (∫ u in (0 : ℝ)..1, Real.log (u + 1)) = ∫ x in (1 : ℝ)..2, Real.log x := by
    convert
      (intervalIntegral.integral_comp_add_left (f := Real.log) (a := (0 : ℝ)) (b := 1) 1) using 1
    · ring_nf
    · ring_nf
  calc
    (∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, (1 : ℝ) / (u + v))
      = ∫ u in (0 : ℝ)..1, (Real.log (u + 1) - Real.log u) := by
          apply intervalIntegral.integral_congr_ae'
          · filter_upwards with u hu
            exact hinner u hu
          · simp
    _ = (∫ u in (0 : ℝ)..1, Real.log (u + 1)) - ∫ u in (0 : ℝ)..1, Real.log u := by
          rw [intervalIntegral.integral_sub hlogshift_int intervalIntegral.intervalIntegrable_log']
    _ = (∫ x in (1 : ℝ)..2, Real.log x) - ∫ u in (0 : ℝ)..1, Real.log u := by
          rw [hshiftlog]
    _ = 2 * Real.log 2 := by
          rw [integral_log, integral_log_from_zero]
          ring_nf
          simp

private lemma unitSquare_inv_add_integral_le_two :
    (∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, (1 : ℝ) / (u + v)) ≤ 2 := by
  rw [unitSquare_inv_add_integral_eq_two_log_two]
  have hlog2_le_one : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  nlinarith

private lemma squareIntegral_inv_add_scale (T : ℝ) (hT : 0 < T) :
    (∫ s in (0 : ℝ)..T, ∫ t in (0 : ℝ)..T, (1 : ℝ) / (s + t)) =
      T * ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, (1 : ℝ) / (u + v) := by
  have hinner_scale : ∀ u : ℝ,
      (∫ t in (0 : ℝ)..T, (1 : ℝ) / (T * u + t)) =
        ∫ v in (0 : ℝ)..1, (1 : ℝ) / (u + v) := by
    intro u
    have h := intervalIntegral.smul_integral_comp_mul_left
      (f := fun x : ℝ => (1 : ℝ) / (T * u + x)) (a := (0 : ℝ)) (b := 1) T
    rw [smul_eq_mul] at h
    calc
      (∫ t in (0 : ℝ)..T, (1 : ℝ) / (T * u + t))
        = T * ∫ v in (0 : ℝ)..1, (1 : ℝ) / (T * u + T * v) := by
            simpa [hT.le, add_comm, add_left_comm, add_assoc] using h.symm
      _ = ∫ v in (0 : ℝ)..1, (1 : ℝ) / (u + v) := by
            rw [← intervalIntegral.integral_const_mul]
            apply intervalIntegral.integral_congr_ae
            filter_upwards with v hv
            have hTv : T * (T * u + T * v)⁻¹ = (u + v)⁻¹ := by
              field_simp [hT.ne']
            simpa [one_div] using hTv
  have houter := intervalIntegral.smul_integral_comp_mul_left
    (f := fun x : ℝ => ∫ t in (0 : ℝ)..T, (1 : ℝ) / (x + t)) (a := (0 : ℝ)) (b := 1) T
  rw [smul_eq_mul] at houter
  calc
    (∫ s in (0 : ℝ)..T, ∫ t in (0 : ℝ)..T, (1 : ℝ) / (s + t))
      = T * ∫ u in (0 : ℝ)..1, (∫ t in (0 : ℝ)..T, (1 : ℝ) / (T * u + t)) := by
          simpa [hT.le, add_comm] using houter.symm
    _ = T * ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, (1 : ℝ) / (u + v) := by
          congr 1
          apply intervalIntegral.integral_congr_ae
          filter_upwards with u hu
          exact hinner_scale u

private lemma squareIntegral_inv_add_le_two_mul
    (T : ℝ) (hT : 0 < T) :
    (∫ s in (0 : ℝ)..T, ∫ t in (0 : ℝ)..T, (1 : ℝ) / (s + t)) ≤ 2 * T := by
  rw [squareIntegral_inv_add_scale T hT]
  calc
    T * ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, (1 : ℝ) / (u + v)
      ≤ T * 2 := by
          gcongr
          exact unitSquare_inv_add_integral_le_two
    _ = 2 * T := by ring

private lemma squareIntegral_exp_neg_le_div
    (μ T : ℝ) (hμ : 0 < μ) (hT : 0 < T) :
    (∫ s in (0 : ℝ)..T, ∫ t in (0 : ℝ)..T, Real.exp (-(s + t) * μ)) ≤ T / μ := by
  set A : ℝ := ∫ t in (0 : ℝ)..T, Real.exp (-t * μ)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact intervalIntegral.integral_nonneg hT.le (fun t ht => by positivity)
  have hA_le_inv : A ≤ 1 / μ := by
    dsimp [A]
    rw [← schwinger_rough_interval μ hμ T hT.le]
    apply div_le_div_of_nonneg_right
    · have hexp_nonneg : 0 ≤ Real.exp (-T * μ) := by positivity
      linarith
    · exact hμ.le
  have hA_le_T : A ≤ T := by
    dsimp [A]
    have hleft : IntervalIntegrable (fun t : ℝ => Real.exp (-t * μ)) volume 0 T := by
      exact (Real.continuous_exp.comp (continuous_neg.mul continuous_const)).intervalIntegrable _ _
    have hright : IntervalIntegrable (fun _t : ℝ => (1 : ℝ)) volume 0 T := by
      exact continuous_const.intervalIntegrable _ _
    calc
      (∫ t in (0 : ℝ)..T, Real.exp (-t * μ)) ≤ ∫ t in (0 : ℝ)..T, (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on hT.le hleft hright
        intro t ht
        have hnonneg : 0 ≤ t := ht.1
        have hle_one : Real.exp (-t * μ) ≤ 1 := by
          apply Real.exp_le_one_iff.mpr
          nlinarith [hμ, hnonneg]
        simpa using hle_one
      _ = T := by simp
  have hinner : ∀ s : ℝ,
      (∫ t in (0 : ℝ)..T, Real.exp (-(s + t) * μ)) = Real.exp (-s * μ) * A := by
    intro s
    dsimp [A]
    calc
      (∫ t in (0 : ℝ)..T, Real.exp (-(s + t) * μ))
        = ∫ t in (0 : ℝ)..T, Real.exp (-s * μ) * Real.exp (-t * μ) := by
            apply intervalIntegral.integral_congr_ae
            filter_upwards with t ht
            rw [show -(s + t) * μ = -s * μ + -t * μ by ring, Real.exp_add]
      _ = Real.exp (-s * μ) * ∫ t in (0 : ℝ)..T, Real.exp (-t * μ) := by
            rw [intervalIntegral.integral_const_mul]
  rw [show (∫ s in (0 : ℝ)..T, ∫ t in (0 : ℝ)..T, Real.exp (-(s + t) * μ))
      = ∫ s in (0 : ℝ)..T, Real.exp (-s * μ) * A by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with s hs
      exact hinner s]
  rw [intervalIntegral.integral_mul_const]
  have hAexp : ∫ s in (0 : ℝ)..T, Real.exp (-s * μ) = A := by rfl
  rw [hAexp]
  calc
    A * A ≤ A * (1 / μ) := by gcongr
    _ ≤ T * (1 / μ) := by gcongr
    _ = T / μ := by ring

private lemma one_add_inv_sqrt_sq_le_two_mul_one_add_inv
    (s : ℝ) (hs : 0 < s) :
    (1 + 1 / Real.sqrt s) ^ 2 ≤ 2 * (1 + 1 / s) := by
  set u : ℝ := 1 / Real.sqrt s
  have hu_sq : u ^ 2 = 1 / s := by
    have hsqrt : Real.sqrt s ≠ 0 := by positivity
    have hsqrt_sq : (Real.sqrt s) ^ 2 = s := by
      rw [Real.sq_sqrt (show 0 ≤ s by linarith)]
    calc
      u ^ 2 = (1 / Real.sqrt s) ^ 2 := by simp [u]
      _ = 1 / ((Real.sqrt s) ^ 2) := by field_simp [hsqrt]
      _ = 1 / s := by rw [hsqrt_sq]
  have h2u : 2 * u ≤ u ^ 2 + 1 := by
    have hsq_nonneg : 0 ≤ (u - 1) ^ 2 := sq_nonneg (u - 1)
    nlinarith
  calc
    (1 + 1 / Real.sqrt s) ^ 2 = (1 + u) ^ 2 := by simp [u]
    _ = 1 + 2 * u + u ^ 2 := by ring
    _ ≤ 1 + (u ^ 2 + 1) + u ^ 2 := by gcongr
    _ = 2 * (1 + u ^ 2) := by ring
    _ = 2 * (1 + 1 / s) := by rw [hu_sq]

private lemma prefactor_eq_L_inv_sq
    (L : ℝ) (N : ℕ) [NeZero N] (a : ℝ)
    (ha : 0 < a) (hvol : (N : ℝ) * a = L) :
    (a ^ 2 : ℝ)⁻¹ * (1 / Fintype.card (FinLatticeSites 2 N) : ℝ) = L⁻¹ ^ 2 := by
  have hcard_nat : Fintype.card (FinLatticeSites 2 N) = N ^ 2 := by
    simp only [FinLatticeSites, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hcard :
      (Fintype.card (FinLatticeSites 2 N) : ℝ) = (N : ℝ) ^ 2 := by
    rw [hcard_nat]
    norm_num
  have hvol_sq : a ^ 2 * (Fintype.card (FinLatticeSites 2 N) : ℝ) = L ^ 2 := by
    rw [hcard]
    calc
      a ^ 2 * (N : ℝ) ^ 2 = ((N : ℝ) * a) ^ 2 := by ring
      _ = L ^ 2 := by rw [hvol]
  have ha2_ne : a ^ 2 ≠ 0 := by positivity
  have hcard_ne : (Fintype.card (FinLatticeSites 2 N) : ℝ) ≠ 0 := by positivity
  have hL_ne : (L : ℝ) ≠ 0 := by
    have hN_pos : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
    nlinarith [hN_pos, ha, hvol]
  calc
    (a ^ 2 : ℝ)⁻¹ * (1 / Fintype.card (FinLatticeSites 2 N) : ℝ)
        = 1 / (a ^ 2 * (Fintype.card (FinLatticeSites 2 N) : ℝ)) := by
            field_simp [ha2_ne, hcard_ne]
    _ = 1 / L ^ 2 := by rw [hvol_sq]
    _ = L⁻¹ ^ 2 := by
          rw [inv_eq_one_div]
          field_simp [hL_ne]

private lemma heatKernel_diagonal_mass_weighted_le_uniform
    (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a) (hvol : (N : ℝ) * a = L)
        (u : ℝ) (hu : 0 < u) (x : FinLatticeSites 2 N),
        Real.exp (-u * mass ^ 2) * latticeHeatKernelMatrix 2 N a u x x ≤
          (1 / Fintype.card (FinLatticeSites 2 N) : ℝ) *
            (C * (1 + 1 / Real.sqrt u) ^ 2 * Real.exp (-u * mass ^ 2)) := by
  obtain ⟨C, hC_pos, hC⟩ := heat_kernel_trace_bound_uniform 2 L hL mass hmass
  refine ⟨C, hC_pos, ?_⟩
  intro N hN a ha hvol u hu x
  have hsum_eq :
      ∑ m : Fin 2 → Fin N, Real.exp (-u * canonicalEigenvalue 2 N a mass m)
        = ∑ m ∈ Finset.range (Fintype.card (FinLatticeSites 2 N)),
            Real.exp (-u * latticeEigenvalue 2 N a mass m) := by
    symm
    rw [← Fin.sum_univ_eq_sum_range]
    exact sum_latticeEigenvalue_eq_sum_latticeEigenvalue1d_family
      (N := N) (d := 2) (a := a) (mass := mass)
      (F := fun t => Real.exp (-u * t))
  calc
    Real.exp (-u * mass ^ 2) * latticeHeatKernelMatrix 2 N a u x x
      = (1 / Fintype.card (FinLatticeSites 2 N) : ℝ) *
          ∑ m : Fin 2 → Fin N, Real.exp (-u * canonicalEigenvalue 2 N a mass m) := by
            simpa using
              (heatKernel_diagonal_mass_weighted_eq_eigenvalue_average
                (d := 2) (N := N) (a := a) (ha := ha) (mass := mass) (t := u) x)
    _ = (1 / Fintype.card (FinLatticeSites 2 N) : ℝ) *
          ∑ m ∈ Finset.range (Fintype.card (FinLatticeSites 2 N)),
            Real.exp (-u * latticeEigenvalue 2 N a mass m) := by rw [hsum_eq]
    _ ≤ (1 / Fintype.card (FinLatticeSites 2 N) : ℝ) *
          (C * (1 + 1 / Real.sqrt u) ^ 2 * Real.exp (-u * mass ^ 2)) := by
            gcongr
            exact hC N a ha hvol u hu

private lemma one_div_sqrt_integrableOn_Icc
    (T : ℝ) (hT : 0 < T) :
    IntegrableOn (fun s : ℝ => 1 / Real.sqrt s) (Set.Icc 0 T) volume := by
  have hpow : IntegrableOn (fun s : ℝ => s ^ ((-1 : ℝ) / 2)) (Set.Icc 0 T) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hT.le]
    simpa using intervalIntegral.intervalIntegrable_rpow' (by norm_num : -1 < ((-1 : ℝ) / 2))
  refine hpow.congr_fun ?_ measurableSet_Icc
  intro s hs
  have hs0 : 0 ≤ s := hs.1
  by_cases hspos : 0 < s
  · have hpow' : (s ^ ((1 : ℝ) / 2))⁻¹ = s ^ (-((1 : ℝ) / 2)) := by
      simpa using (Real.rpow_neg hs0 ((1 : ℝ) / 2)).symm
    have hneg : -((1 : ℝ) / 2) = ((-1 : ℝ) / 2) := by ring
    have hsqrt : (1 / Real.sqrt s : ℝ) = s ^ ((-1 : ℝ) / 2) := by
      rw [show (1 / Real.sqrt s : ℝ) = (s ^ ((1 : ℝ) / 2))⁻¹ by
        simp [one_div, Real.sqrt_eq_rpow]]
      rw [hpow', hneg]
    simpa using hsqrt.symm
  · have hs_eq : s = 0 := by linarith
    simp [hs_eq]

private lemma one_div_sqrt_integrable_Ioc
    (T : ℝ) (hT : 0 < T) :
    Integrable (fun s : ℝ => 1 / Real.sqrt s) (volume.restrict (Set.Ioc 0 T)) := by
  simpa [IntegrableOn] using
    (one_div_sqrt_integrableOn_Icc T hT).mono_set Set.Ioc_subset_Icc_self

private lemma integrable_inv_add_Ioc
    (T : ℝ) (hT : 0 < T) :
    Integrable
      (fun p : ℝ × ℝ => 1 / (p.1 + p.2 : ℝ))
      ((volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T))) := by
  have hdom : Integrable
      (fun p : ℝ × ℝ => (1 / Real.sqrt p.1) * (1 / Real.sqrt p.2))
      ((volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T))) := by
    simpa using Integrable.mul_prod (one_div_sqrt_integrable_Ioc T hT) (one_div_sqrt_integrable_Ioc T hT)
  have hpos :
      ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T))),
        0 < p.1 ∧ 0 < p.2 := by
    have hpos_restrict :
        ∀ᵐ p : ℝ × ℝ ∂((volume.prod volume).restrict (Set.Ioc 0 T ×ˢ Set.Ioc 0 T)),
          0 < p.1 ∧ 0 < p.2 := by
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
      exact ⟨hp.1.1, hp.2.1⟩
    simpa [Measure.prod_restrict] using hpos_restrict
  refine Integrable.mono' hdom ?_ ?_
  · simpa [one_div] using
      (((measurable_fst.add measurable_snd : Measurable fun p : ℝ × ℝ => p.1 + p.2).inv).aestronglyMeasurable)
  · filter_upwards [hpos] with p hp
    rcases p with ⟨s, t⟩
    have hs : 0 < s := hp.1
    have ht : 0 < t := hp.2
    have hs0 : 0 ≤ s := hs.le
    have ht0 : 0 ≤ t := ht.le
    have hsum_pos : 0 < s + t := add_pos hs ht
    have hAMGM : 2 * (Real.sqrt s * Real.sqrt t) ≤ s + t := by
      nlinarith [sq_nonneg (Real.sqrt s - Real.sqrt t), Real.sq_sqrt hs0, Real.sq_sqrt ht0]
    have hden_pos : 0 < 2 * (Real.sqrt s * Real.sqrt t) := by positivity
    have hinv : 1 / (s + t) ≤ 1 / (2 * (Real.sqrt s * Real.sqrt t)) := by
      exact one_div_le_one_div_of_le hden_pos hAMGM
    have hhalf : 1 / (2 * (Real.sqrt s * Real.sqrt t)) ≤ (1 / Real.sqrt s) * (1 / Real.sqrt t) := by
      have hsqrt_ne : Real.sqrt s ≠ 0 := by positivity
      have htsqrt_ne : Real.sqrt t ≠ 0 := by positivity
      have hA_nonneg : 0 ≤ (1 / Real.sqrt s) * (1 / Real.sqrt t) := by positivity
      calc
        1 / (2 * (Real.sqrt s * Real.sqrt t)) = (1 / 2) * ((1 / Real.sqrt s) * (1 / Real.sqrt t)) := by
          field_simp [hsqrt_ne, htsqrt_ne]
        _ ≤ (1 / Real.sqrt s) * (1 / Real.sqrt t) := by
          nlinarith
    rw [Real.norm_of_nonneg (one_div_nonneg.2 hsum_pos.le)]
    exact hinv.trans hhalf

private lemma integrable_inv_add_mul_exp_Ioc
    (μ T : ℝ) (hμ : 0 ≤ μ) (hT : 0 < T) :
    Integrable
      (fun p : ℝ × ℝ => (1 / (p.1 + p.2 : ℝ)) * Real.exp (-(p.1 + p.2) * μ))
      ((volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T))) := by
  have hdom := integrable_inv_add_Ioc T hT
  have hpos :
      ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T))),
        0 < p.1 + p.2 := by
    have hpos_restrict :
        ∀ᵐ p : ℝ × ℝ ∂((volume.prod volume).restrict (Set.Ioc 0 T ×ˢ Set.Ioc 0 T)),
          0 < p.1 + p.2 := by
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
      exact add_pos hp.1.1 hp.2.1
    simpa [Measure.prod_restrict] using hpos_restrict
  refine Integrable.mono' hdom ?_ ?_
  · simpa [one_div] using
      ((((measurable_fst.add measurable_snd : Measurable fun p : ℝ × ℝ => p.1 + p.2).inv).mul
        ((((measurable_fst.add measurable_snd : Measurable fun p : ℝ × ℝ => p.1 + p.2).neg).mul_const μ).exp)).aestronglyMeasurable)
  · filter_upwards [hpos] with p hp
    have hexp_le : Real.exp (-(p.1 + p.2) * μ) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith
    calc
      ‖1 / (p.1 + p.2) * Real.exp (-(p.1 + p.2) * μ)‖
        = (1 / (p.1 + p.2)) * Real.exp (-(p.1 + p.2) * μ) := by
            rw [Real.norm_of_nonneg]
            positivity
      _ ≤ (1 / (p.1 + p.2)) * 1 := by gcongr
      _ = 1 / (p.1 + p.2) := by ring

private lemma ioc_prod_exp_integral_le
    (μ T : ℝ) (hμ : 0 < μ) (hT : 0 < T) :
    ∫ p, Real.exp (-(p.1 + p.2) * μ)
      ∂((volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T)))
      ≤ T / μ := by
  have hmeasure :
      ((volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T))) =
        ((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T))) := by
    simp [restrict_Ioc_eq_restrict_Icc]
  have hcont : Continuous (fun p : ℝ × ℝ => Real.exp (-(p.1 + p.2) * μ)) := by
    fun_prop
  have hOn : IntegrableOn (fun p : ℝ × ℝ => Real.exp (-(p.1 + p.2) * μ))
      (Set.Icc 0 T ×ˢ Set.Icc 0 T) (volume.prod volume) := by
    exact hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hInt :
      Integrable (fun p : ℝ × ℝ => Real.exp (-(p.1 + p.2) * μ))
        ((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T))) := by
    simpa [IntegrableOn, Measure.prod_restrict, Set.Icc_prod_Icc] using hOn
  have hprod :
      ∫ p, Real.exp (-(p.1 + p.2) * μ)
        ∂((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T))) =
      ∫ s in Set.Icc 0 T, ∫ t in Set.Icc 0 T, Real.exp (-(s + t) * μ) := by
    simpa [Measure.prod_restrict, Set.Icc_prod_Icc, add_comm, add_left_comm, add_assoc] using
      (MeasureTheory.integral_prod (fun p : ℝ × ℝ => Real.exp (-(p.1 + p.2) * μ)) hInt)
  have hconvert :
      (∫ s in Set.Icc 0 T, ∫ t in Set.Icc 0 T, Real.exp (-(s + t) * μ)) =
        ∫ s in (0 : ℝ)..T, ∫ t in (0 : ℝ)..T, Real.exp (-(s + t) * μ) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT.le]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hs
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT.le]
  rw [hmeasure, hprod, hconvert]
  exact squareIntegral_exp_neg_le_div μ T hμ hT

private lemma ioc_prod_inv_add_integral_le
    (T : ℝ) (hT : 0 < T) :
    ∫ p, (1 / (p.1 + p.2 : ℝ))
      ∂((volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T)))
      ≤ 2 * T := by
  have hmeasure :
      ((volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T))) =
        ((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T))) := by
    simp [restrict_Ioc_eq_restrict_Icc]
  have hInt :
      Integrable (fun p : ℝ × ℝ => (1 / (p.1 + p.2 : ℝ)))
        ((volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T))) := by
    exact integrable_inv_add_Ioc T hT
  have hInt' :
      Integrable (fun p : ℝ × ℝ => (1 / (p.1 + p.2 : ℝ)))
        ((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T))) := by
    rw [← hmeasure]
    exact hInt
  have hprod :
      ∫ p, (1 / (p.1 + p.2 : ℝ))
        ∂((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T))) =
      ∫ s in Set.Icc 0 T, ∫ t in Set.Icc 0 T, (1 / (s + t : ℝ)) := by
    simpa [Measure.prod_restrict, Set.Icc_prod_Icc, add_comm] using
      (MeasureTheory.integral_prod (fun p : ℝ × ℝ => (1 / (p.1 + p.2 : ℝ))) hInt')
  have hconvert :
      (∫ s in Set.Icc 0 T, ∫ t in Set.Icc 0 T, (1 / (s + t : ℝ))) =
        ∫ s in (0 : ℝ)..T, ∫ t in (0 : ℝ)..T, (1 / (s + t : ℝ)) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT.le]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hs
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT.le]
  rw [hmeasure, hprod, hconvert]
  exact squareIntegral_inv_add_le_two_mul T hT

private lemma ioc_prod_inv_add_mul_exp_integral_le
    (μ T : ℝ) (hμ : 0 < μ) (hT : 0 < T) :
    ∫ p, ((1 / (p.1 + p.2 : ℝ)) * Real.exp (-(p.1 + p.2) * μ))
      ∂((volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T)))
      ≤ 2 * T := by
  let ν : Measure (ℝ × ℝ) :=
    (volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T))
  have hIntF :
      Integrable (fun p : ℝ × ℝ => (1 / (p.1 + p.2 : ℝ)) * Real.exp (-(p.1 + p.2) * μ)) ν := by
    simpa [ν] using integrable_inv_add_mul_exp_Ioc μ T hμ.le hT
  have hIntG :
      Integrable (fun p : ℝ × ℝ => (1 / (p.1 + p.2 : ℝ))) ν := by
    simpa [ν] using integrable_inv_add_Ioc T hT
  have hpos :
      ∀ᵐ p : ℝ × ℝ ∂ν, 0 < p.1 + p.2 := by
    have hpos_restrict :
        ∀ᵐ p : ℝ × ℝ ∂((volume.prod volume).restrict (Set.Ioc 0 T ×ˢ Set.Ioc 0 T)),
          0 < p.1 + p.2 := by
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
      exact add_pos hp.1.1 hp.2.1
    simpa [ν, Measure.prod_restrict] using hpos_restrict
  have hmono :
      (fun p : ℝ × ℝ => (1 / (p.1 + p.2 : ℝ)) * Real.exp (-(p.1 + p.2) * μ))
        ≤ᵐ[ν]
      (fun p : ℝ × ℝ => (1 / (p.1 + p.2 : ℝ))) := by
    filter_upwards [hpos] with p hp
    have hexp_le : Real.exp (-(p.1 + p.2) * μ) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith
    calc
      (1 / (p.1 + p.2 : ℝ)) * Real.exp (-(p.1 + p.2) * μ)
        ≤ (1 / (p.1 + p.2 : ℝ)) * 1 := by gcongr
      _ = (1 / (p.1 + p.2 : ℝ)) := by ring
  calc
    ∫ p, ((1 / (p.1 + p.2 : ℝ)) * Real.exp (-(p.1 + p.2) * μ)) ∂ν
      ≤ ∫ p, (1 / (p.1 + p.2 : ℝ)) ∂ν := by
          exact MeasureTheory.integral_mono_ae hIntF hIntG hmono
    _ ≤ 2 * T := by
          simpa [ν] using ioc_prod_inv_add_integral_le T hT

private theorem canonicalRoughCovariance_pow_two_sum_le_uniform_in_aN
    (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ C2 : ℝ, 0 < C2 ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a) (hvol : (N : ℝ) * a = L)
        (T : ℝ) (hT : 0 < T) (x : FinLatticeSites 2 N),
        a ^ 2 * ∑ y : FinLatticeSites 2 N,
          |canonicalRoughCovariance 2 N a mass T x y| ^ 2 ≤ C2 * T := by
  obtain ⟨C, hC_pos, hCdiag⟩ := heatKernel_diagonal_mass_weighted_le_uniform mass L hL hmass
  refine ⟨2 * L⁻¹ ^ 2 * C * (1 / mass ^ 2 + 2), by positivity, ?_⟩
  intro N hN a ha hvol T hT x
  have hsq_abs :
      a ^ 2 * ∑ y : FinLatticeSites 2 N, |canonicalRoughCovariance 2 N a mass T x y| ^ 2
        = a ^ 2 * ∑ y : FinLatticeSites 2 N, (canonicalRoughCovariance 2 N a mass T x y) ^ 2 := by
    congr 1
    refine Finset.sum_congr rfl ?_
    intro y hy
    rw [sq_abs]
  let f : ℝ × ℝ → ℝ := fun p =>
    Real.exp (-(p.1 + p.2) * mass ^ 2) * latticeHeatKernelMatrix 2 N a (p.1 + p.2) x x
  let g : ℝ × ℝ → ℝ := fun p =>
    2 * C * (1 + 1 / (p.1 + p.2)) * Real.exp (-(p.1 + p.2) * mass ^ 2)
  let ν : Measure (ℝ × ℝ) :=
    (volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T))
  have hmeasure :
      ((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T))) = ν := by
    simp [ν, restrict_Ioc_eq_restrict_Icc]
  have hf_cont : Continuous f := by
    let card : ℝ := (1 / Fintype.card (FinLatticeSites 2 N) : ℝ)
    have hEq :
        f = fun p : ℝ × ℝ =>
          card * ∑ m : Fin 2 → Fin N,
            Real.exp (-(p.1 + p.2) * canonicalEigenvalue 2 N a mass m) := by
      funext p
      simpa [card, f] using
        (heatKernel_diagonal_mass_weighted_eq_eigenvalue_average
          (d := 2) (N := N) (a := a) (ha := ha) (mass := mass) (t := p.1 + p.2) x)
    have hCont :
        Continuous (fun p : ℝ × ℝ =>
          card * ∑ m : Fin 2 → Fin N,
            Real.exp (-(p.1 + p.2) * canonicalEigenvalue 2 N a mass m)) := by
      fun_prop
    rw [hEq]
    exact hCont
  have hfOn :
      IntegrableOn f (Set.Icc 0 T ×ˢ Set.Icc 0 T) (volume.prod volume) := by
    exact hf_cont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hfIntIcc :
      Integrable f ((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T))) := by
    simpa [IntegrableOn, Measure.prod_restrict, Set.Icc_prod_Icc] using hfOn
  have hfInt :
      Integrable f ν := by
    rw [← hmeasure]
    exact hfIntIcc
  have hprodIcc :
      ∫ p, f p ∂((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T))) =
        ∫ s in Set.Icc 0 T, ∫ t in Set.Icc 0 T, f (s, t) := by
    simpa [Measure.prod_restrict, Set.Icc_prod_Icc, add_comm, add_left_comm, add_assoc] using
      (MeasureTheory.integral_prod f hfIntIcc)
  have hprod :
      ∫ s in Set.Icc 0 T, ∫ t in Set.Icc 0 T, f (s, t) = ∫ p, f p ∂ν := by
    rw [← hmeasure]
    exact hprodIcc.symm
  have hgExpInt :
      Integrable (fun p : ℝ × ℝ => Real.exp (-(p.1 + p.2) * mass ^ 2)) ν := by
    have hcont : Continuous (fun p : ℝ × ℝ => Real.exp (-(p.1 + p.2) * mass ^ 2)) := by
      fun_prop
    have hOn :
        IntegrableOn (fun p : ℝ × ℝ => Real.exp (-(p.1 + p.2) * mass ^ 2))
          (Set.Icc 0 T ×ˢ Set.Icc 0 T) (volume.prod volume) := by
      exact hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have hIntIcc :
        Integrable (fun p : ℝ × ℝ => Real.exp (-(p.1 + p.2) * mass ^ 2))
          ((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T))) := by
      simpa [IntegrableOn, Measure.prod_restrict, Set.Icc_prod_Icc] using hOn
    rw [← hmeasure]
    exact hIntIcc
  have hgInvExpInt :
      Integrable (fun p : ℝ × ℝ =>
        ((1 / (p.1 + p.2 : ℝ)) * Real.exp (-(p.1 + p.2) * mass ^ 2))) ν := by
    simpa [ν] using integrable_inv_add_mul_exp_Ioc (mass ^ 2) T (by positivity) hT
  have hgInt : Integrable g ν := by
    have hsum :
        Integrable (fun p : ℝ × ℝ =>
          Real.exp (-(p.1 + p.2) * mass ^ 2) +
            ((1 / (p.1 + p.2 : ℝ)) * Real.exp (-(p.1 + p.2) * mass ^ 2))) ν := by
      exact hgExpInt.add hgInvExpInt
    have hEq :
        g = fun p : ℝ × ℝ =>
          (2 * C) *
            (Real.exp (-(p.1 + p.2) * mass ^ 2) +
              ((1 / (p.1 + p.2 : ℝ)) * Real.exp (-(p.1 + p.2) * mass ^ 2))) := by
      funext p
      dsimp [g]
      ring
    rw [hEq]
    exact hsum.const_mul (2 * C)
  have hScaledInt :
      Integrable (fun p : ℝ × ℝ => (1 / Fintype.card (FinLatticeSites 2 N) : ℝ) * g p) ν := by
    exact hgInt.const_mul _
  have hpos :
      ∀ᵐ p : ℝ × ℝ ∂ν, 0 < p.1 ∧ 0 < p.2 := by
    have hpos_restrict :
        ∀ᵐ p : ℝ × ℝ ∂((volume.prod volume).restrict (Set.Ioc 0 T ×ˢ Set.Ioc 0 T)),
          0 < p.1 ∧ 0 < p.2 := by
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
      exact ⟨hp.1.1, hp.2.1⟩
    simpa [ν, Measure.prod_restrict] using hpos_restrict
  have hfg :
      f ≤ᵐ[ν] (fun p : ℝ × ℝ => (1 / Fintype.card (FinLatticeSites 2 N) : ℝ) * g p) := by
    filter_upwards [hpos] with p hp
    rcases p with ⟨s, t⟩
    have hst : 0 < s + t := add_pos hp.1 hp.2
    have hdiag := hCdiag N a ha hvol (s + t) hst x
    have hsqrt :
        (1 + 1 / Real.sqrt (s + t)) ^ 2 ≤ 2 * (1 + 1 / (s + t)) :=
      one_add_inv_sqrt_sq_le_two_mul_one_add_inv (s + t) hst
    calc
      f (s, t)
        ≤ (1 / Fintype.card (FinLatticeSites 2 N) : ℝ) *
            (C * (1 + 1 / Real.sqrt (s + t)) ^ 2 * Real.exp (-(s + t) * mass ^ 2)) := by
              simpa [f] using hdiag
      _ ≤ (1 / Fintype.card (FinLatticeSites 2 N) : ℝ) *
            (C * (2 * (1 + 1 / (s + t))) * Real.exp (-(s + t) * mass ^ 2)) := by
              gcongr
      _ = (1 / Fintype.card (FinLatticeSites 2 N) : ℝ) * g (s, t) := by
            dsimp [g]
            ring
  have hgBound :
      ∫ p, g p ∂ν ≤ 2 * C * (1 / mass ^ 2 + 2) * T := by
    have hEq :
        g = fun p : ℝ × ℝ =>
          (2 * C) *
            (Real.exp (-(p.1 + p.2) * mass ^ 2) +
              ((1 / (p.1 + p.2 : ℝ)) * Real.exp (-(p.1 + p.2) * mass ^ 2))) := by
      funext p
      dsimp [g]
      ring
    rw [hEq, integral_const_mul, integral_add hgExpInt hgInvExpInt]
    calc
      (2 * C) *
          (∫ p, Real.exp (-(p.1 + p.2) * mass ^ 2) ∂ν +
            ∫ p, ((1 / (p.1 + p.2 : ℝ)) * Real.exp (-(p.1 + p.2) * mass ^ 2)) ∂ν)
        ≤ (2 * C) * (T / mass ^ 2 + 2 * T) := by
            gcongr
            · simpa [ν] using ioc_prod_exp_integral_le (mass ^ 2) T (by positivity) hT
            · simpa [ν] using ioc_prod_inv_add_mul_exp_integral_le (mass ^ 2) T (by positivity) hT
      _ = 2 * C * (1 / mass ^ 2 + 2) * T := by ring
  rw [hsq_abs, canonicalRoughCovariance_sq_row_sum_eq_double_integral
    (d := 2) (N := N) (a := a) (mass := mass) ha hmass T hT x]
  rw [hprod]
  calc
    (a ^ 2 : ℝ)⁻¹ * ∫ p, f p ∂ν
      ≤ (a ^ 2 : ℝ)⁻¹ * ∫ p, (1 / Fintype.card (FinLatticeSites 2 N) : ℝ) * g p ∂ν := by
          apply mul_le_mul_of_nonneg_left
            (MeasureTheory.integral_mono_ae hfInt hScaledInt hfg)
          positivity
    _ = (((a ^ 2 : ℝ)⁻¹) * (1 / Fintype.card (FinLatticeSites 2 N) : ℝ)) * ∫ p, g p ∂ν := by
          rw [integral_const_mul]
          ring
    _ = L⁻¹ ^ 2 * ∫ p, g p ∂ν := by
          rw [prefactor_eq_L_inv_sq L N a ha hvol]
    _ ≤ L⁻¹ ^ 2 * (2 * C * (1 / mass ^ 2 + 2) * T) := by
          exact mul_le_mul_of_nonneg_left hgBound (by positivity)
    _ = (2 * L⁻¹ ^ 2 * C * (1 / mass ^ 2 + 2)) * T := by ring

/-- The lattice heat kernel is entrywise nonnegative. -/
private lemma latticeHeatKernel_nonneg
    {d N : ℕ} [NeZero N] (a : ℝ) (ha : 0 < a) (t : ℝ) (ht : 0 ≤ t)
    (x y : FinLatticeSites d N) :
    0 ≤ latticeHeatKernelMatrix d N a t x y := by
  have hZ : MatrixSemigroup.IsZMatrix (negLaplacianMatrix d N a) := by
    intro u v huv
    have hoff :=
      massOperator_offDiag_nonpos d N a 1 ha (by norm_num : 0 < (1 : ℝ)) u v huv
    simpa [negLaplacianMatrix, massOperatorMatrix, massOperatorEntry, massOperator,
      finLatticeDelta, huv] using hoff
  simpa [latticeHeatKernelMatrix] using
    MatrixSemigroup.heat_kernel_entrywise_nonneg (negLaplacianMatrix d N a) hZ t ht x y

/-- The canonical rough covariance is entrywise nonnegative. -/
private lemma canonicalRoughCovariance_nonneg
    {d N : ℕ} [NeZero N] (a mass T : ℝ) (ha : 0 < a) (hmass : 0 < mass) (hT : 0 < T)
    (x y : FinLatticeSites d N) :
    0 ≤ canonicalRoughCovariance d N a mass T x y := by
  rw [canonicalRoughCovariance_eq_integral_Icc_heatKernel
    (d := d) (N := N) (a := a) (mass := mass) ha hmass T hT x y]
  apply mul_nonneg
  · positivity
  · refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t htIcc
    exact mul_nonneg (by positivity)
      (latticeHeatKernel_nonneg a ha t htIcc.1 x y)

/-- Phase 2 (`m = 1`) of the rough-side Glimm-Jaffe bound in `d = 2`:
the position-space absolute row sum of the canonical rough covariance is
`O(T)`, uniformly in `(N, a)` at fixed `L = N * a`. -/
theorem canonicalRoughCovariance_pow_one_sum_le_uniform_in_aN_proved
    (mass L : ℝ) (_hL : 0 < L) (hmass : 0 < mass) :
    ∃ C1 : ℝ, 0 < C1 ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a) (_hvol : (N : ℝ) * a = L)
        (T : ℝ) (hT : 0 < T) (x : FinLatticeSites 2 N),
        a ^ 2 * ∑ y : FinLatticeSites 2 N,
          |canonicalRoughCovariance 2 N a mass T x y| ≤ C1 * T := by
  refine ⟨1, by positivity, ?_⟩
  intro N hN a ha hvol T hT x
  have ha2_ne : (a ^ 2 : ℝ) ≠ 0 := by positivity
  have h_abs :
      a ^ 2 * ∑ y : FinLatticeSites 2 N, |canonicalRoughCovariance 2 N a mass T x y|
        = a ^ 2 * ∑ y : FinLatticeSites 2 N, canonicalRoughCovariance 2 N a mass T x y := by
    congr 1
    refine Finset.sum_congr rfl ?_
    intro y hy
    rw [abs_of_nonneg]
    exact canonicalRoughCovariance_nonneg a mass T ha hmass hT x y
  have hEntryCont :
      ∀ y : FinLatticeSites 2 N,
        Continuous (fun t : ℝ =>
          Real.exp (-t * mass ^ 2) * latticeHeatKernelMatrix 2 N a t x y) := by
    intro y
    have hExp : Continuous (fun t : ℝ => Real.exp (-t * mass ^ 2)) := by
      exact Real.continuous_exp.comp
        (continuous_id.neg.mul (continuous_const : Continuous fun _ : ℝ => mass ^ 2))
    have hEntry :
        Continuous (fun t : ℝ => latticeHeatKernelMatrix 2 N a t x y) := by
      have hEq :
          (fun t : ℝ => latticeHeatKernelMatrix 2 N a t x y) =
            (fun t : ℝ =>
              ∑ m : Fin 2 → Fin N,
                Real.exp (-t * ∑ i : Fin 2, latticeEigenvalue1d N a (m i)) *
                  latticeFourierProductBasisFun N 2 m x *
                  latticeFourierProductBasisFun N 2 m y /
                  latticeFourierProductNormSq N 2 m) := by
        funext t
        rw [latticeHeatKernel_entry_eq_eigenvalue_average
          (d := 2) (N := N) (a := a) (ha := ne_of_gt ha) (t := t) (x := x) (y := y)]
      rw [hEq]
      refine continuous_finset_sum _ ?_
      intro m hm
      have hMode :
          Continuous
            (fun t : ℝ => Real.exp (-t * ∑ i : Fin 2, latticeEigenvalue1d N a (m i))) := by
        exact Real.continuous_exp.comp
          (continuous_id.neg.mul
            (continuous_const :
              Continuous fun _ : ℝ => ∑ i : Fin 2, latticeEigenvalue1d N a (m i)))
      have hConst :
          Continuous
            (fun _ : ℝ =>
              latticeFourierProductBasisFun N 2 m x *
                latticeFourierProductBasisFun N 2 m y /
                latticeFourierProductNormSq N 2 m) :=
        continuous_const
      simpa [mul_assoc, div_eq_mul_inv] using hMode.mul hConst
    exact hExp.mul hEntry
  have hEntryInt :
      ∀ y : FinLatticeSites 2 N,
        IntegrableOn
          (fun t : ℝ => Real.exp (-t * mass ^ 2) * latticeHeatKernelMatrix 2 N a t x y)
          (Set.Icc 0 T) := by
    intro y
    exact (hEntryCont y).integrableOn_Icc
  have hsum :
      a ^ 2 * ∑ y : FinLatticeSites 2 N, canonicalRoughCovariance 2 N a mass T x y
        = ∫ t in Set.Icc 0 T,
            Real.exp (-t * mass ^ 2) *
              ∑ y : FinLatticeSites 2 N, latticeHeatKernelMatrix 2 N a t x y := by
    calc
      a ^ 2 * ∑ y : FinLatticeSites 2 N, canonicalRoughCovariance 2 N a mass T x y
        = a ^ 2 * ∑ y : FinLatticeSites 2 N,
            ((a ^ 2 : ℝ)⁻¹ *
              ∫ t in Set.Icc 0 T,
                Real.exp (-t * mass ^ 2) * latticeHeatKernelMatrix 2 N a t x y) := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro y hy
              rw [canonicalRoughCovariance_eq_integral_Icc_heatKernel
                (d := 2) (N := N) (a := a) (mass := mass) ha hmass T hT x y]
      _ = ∑ y : FinLatticeSites 2 N,
            ∫ t in Set.Icc 0 T,
              Real.exp (-t * mass ^ 2) * latticeHeatKernelMatrix 2 N a t x y := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl ?_
                intro y hy
                have hscal : a ^ 2 * (a ^ 2 : ℝ)⁻¹ = 1 := by
                  field_simp [ha2_ne]
                calc
                  a ^ 2 *
                      ((a ^ 2 : ℝ)⁻¹ *
                        ∫ t in Set.Icc 0 T,
                          Real.exp (-t * mass ^ 2) * latticeHeatKernelMatrix 2 N a t x y)
                    = (a ^ 2 * (a ^ 2 : ℝ)⁻¹) *
                        ∫ t in Set.Icc 0 T,
                          Real.exp (-t * mass ^ 2) * latticeHeatKernelMatrix 2 N a t x y := by
                            ring
                  _ = ∫ t in Set.Icc 0 T,
                        Real.exp (-t * mass ^ 2) * latticeHeatKernelMatrix 2 N a t x y := by
                            rw [hscal, one_mul]
      _ = ∫ t in Set.Icc 0 T,
            ∑ y : FinLatticeSites 2 N,
              Real.exp (-t * mass ^ 2) * latticeHeatKernelMatrix 2 N a t x y := by
                rw [integral_finset_sum]
                intro y hy
                exact hEntryInt y
      _ = ∫ t in Set.Icc 0 T,
            Real.exp (-t * mass ^ 2) *
              ∑ y : FinLatticeSites 2 N, latticeHeatKernelMatrix 2 N a t x y := by
                apply integral_congr_ae
                filter_upwards with t
                rw [Finset.mul_sum]
  have hexp_int :
      ∫ t in Set.Icc 0 T, Real.exp (-t * mass ^ 2)
        = (1 - Real.exp (-T * mass ^ 2)) / (mass ^ 2) := by
    symm
    exact schwinger_rough (mass ^ 2) (by positivity) T hT.le
  have hexp_le : ∫ t in Set.Icc 0 T, Real.exp (-t * mass ^ 2) ≤ T := by
    rw [hexp_int]
    have haux : 1 - Real.exp (-(T * mass ^ 2)) ≤ T * mass ^ 2 := by
      linarith [Real.add_one_le_exp (-(T * mass ^ 2))]
    have haux' : 1 - Real.exp (-T * mass ^ 2) ≤ T * mass ^ 2 := by
      simpa using haux
    have hmass2_pos : 0 < mass ^ 2 := by positivity
    rw [div_le_iff₀ hmass2_pos]
    exact haux'
  rw [h_abs, hsum]
  calc
    ∫ t in Set.Icc 0 T, Real.exp (-t * mass ^ 2) *
        ∑ y : FinLatticeSites 2 N, latticeHeatKernelMatrix 2 N a t x y
      = ∫ t in Set.Icc 0 T, Real.exp (-t * mass ^ 2) * 1 := by
          apply integral_congr_ae
          filter_upwards with t
          rw [heatKernel_row_sum_eq_one (d := 2) (N := N) (a := a) ha t x]
    _ = ∫ t in Set.Icc 0 T, Real.exp (-t * mass ^ 2) := by simp
    _ ≤ T := hexp_le
    _ = 1 * T := by ring

/-- Phase 3 (`m = 2`) of the rough-side Glimm-Jaffe bound in `d = 2`:
the position-space square row sum of the canonical rough covariance is
`O(T)`, uniformly in `(N, a)` at fixed `L = N * a`. -/
theorem canonicalRoughCovariance_pow_two_sum_le_uniform_in_aN_proved
    (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ C2 : ℝ, 0 < C2 ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a) (hvol : (N : ℝ) * a = L)
        (T : ℝ) (hT : 0 < T) (x : FinLatticeSites 2 N),
        a ^ 2 * ∑ y : FinLatticeSites 2 N,
          |canonicalRoughCovariance 2 N a mass T x y| ^ 2 ≤ C2 * T :=
  canonicalRoughCovariance_pow_two_sum_le_uniform_in_aN mass L hL hmass

private lemma heatKernel_entry_sq_le_diagonal_mul_diagonal
    {d N : ℕ} [NeZero N] (a t : ℝ) (x y : FinLatticeSites d N) :
    latticeHeatKernelMatrix d N a t x y ^ 2 ≤
      latticeHeatKernelMatrix d N a t x x *
        latticeHeatKernelMatrix d N a t y y := by
  let r : ℝ := t / 2
  have hsymm :
      ∀ u v : FinLatticeSites d N,
        latticeHeatKernelMatrix d N a r u v =
          latticeHeatKernelMatrix d N a r v u := by
    intro u v
    have hT :
        Matrix.transpose (latticeHeatKernelMatrix d N a r) = latticeHeatKernelMatrix d N a r := by
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
      exact (latticeHeatKernelMatrix_isHermitian d N a r).eq
    have hentry := congr_fun (congr_fun hT u) v
    simpa [Matrix.transpose_apply] using hentry.symm
  have hxy :
      latticeHeatKernelMatrix d N a t x y =
        ∑ z : FinLatticeSites d N,
          latticeHeatKernelMatrix d N a r x z *
            latticeHeatKernelMatrix d N a r y z := by
    calc
      latticeHeatKernelMatrix d N a t x y
        = latticeHeatKernelMatrix d N a (r + r) x y := by
            congr 1
            dsimp [r]
            ring
      _ = (latticeHeatKernelMatrix d N a r * latticeHeatKernelMatrix d N a r) x y := by
            rw [latticeHeatKernelMatrix_semigroup (d := d) (N := N) a r r]
      _ = ∑ z : FinLatticeSites d N,
            latticeHeatKernelMatrix d N a r x z *
              latticeHeatKernelMatrix d N a r z y := by
              simp [Matrix.mul_apply]
      _ = ∑ z : FinLatticeSites d N,
            latticeHeatKernelMatrix d N a r x z *
              latticeHeatKernelMatrix d N a r y z := by
              refine Finset.sum_congr rfl ?_
              intro z hz
              rw [hsymm z y]
  rw [hxy]
  calc
    (∑ z : FinLatticeSites d N,
        latticeHeatKernelMatrix d N a r x z *
          latticeHeatKernelMatrix d N a r y z) ^ 2
      ≤ (∑ z : FinLatticeSites d N, latticeHeatKernelMatrix d N a r x z ^ 2) *
          ∑ z : FinLatticeSites d N, latticeHeatKernelMatrix d N a r y z ^ 2 := by
            simpa using
              (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ)
                (fun z => latticeHeatKernelMatrix d N a r x z)
                (fun z => latticeHeatKernelMatrix d N a r y z))
    _ = latticeHeatKernelMatrix d N a t x x *
          latticeHeatKernelMatrix d N a t y y := by
            have hxx :
                ∑ z : FinLatticeSites d N, latticeHeatKernelMatrix d N a r x z ^ 2 =
                  latticeHeatKernelMatrix d N a t x x := by
              calc
                ∑ z : FinLatticeSites d N, latticeHeatKernelMatrix d N a r x z ^ 2
                  = ∑ z : FinLatticeSites d N,
                      latticeHeatKernelMatrix d N a r x z *
                        latticeHeatKernelMatrix d N a r x z := by
                          simp_rw [pow_two]
                _ = latticeHeatKernelMatrix d N a (r + r) x x := by
                      rw [heatKernel_row_pairing_eq_diagonal (d := d) (N := N) a r r x]
                _ = latticeHeatKernelMatrix d N a t x x := by
                      congr 1
                      dsimp [r]
                      ring
            have hyy :
                ∑ z : FinLatticeSites d N, latticeHeatKernelMatrix d N a r y z ^ 2 =
                  latticeHeatKernelMatrix d N a t y y := by
              calc
                ∑ z : FinLatticeSites d N, latticeHeatKernelMatrix d N a r y z ^ 2
                  = ∑ z : FinLatticeSites d N,
                      latticeHeatKernelMatrix d N a r y z *
                        latticeHeatKernelMatrix d N a r y z := by
                          simp_rw [pow_two]
                _ = latticeHeatKernelMatrix d N a (r + r) y y := by
                      rw [heatKernel_row_pairing_eq_diagonal (d := d) (N := N) a r r y]
                _ = latticeHeatKernelMatrix d N a t y y := by
                      congr 1
                      dsimp [r]
                      ring
            rw [hxx, hyy]

private lemma exp_mul_one_add_inv_sqrt_sq_le_const_div
    (μ t : ℝ) (hμ : 0 < μ) (ht : 0 < t) :
    Real.exp (-t * μ) * (1 + 1 / Real.sqrt t) ^ 2 ≤
      (2 * (1 + 1 / μ)) / t := by
  have hexp_nonneg : 0 ≤ Real.exp (-t * μ) := by positivity
  have hexp_le_one : Real.exp (-t * μ) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith
  have hμt_pos : 0 < t * μ := by positivity
  have hμt_le_exp : t * μ ≤ Real.exp (t * μ) := by
    exact le_trans (by linarith) (Real.add_one_le_exp (t * μ))
  have hexp_le_inv : Real.exp (-t * μ) ≤ 1 / (t * μ) := by
    have hdiv := one_div_le_one_div_of_le hμt_pos hμt_le_exp
    simpa [one_div, Real.exp_neg, mul_comm] using hdiv
  have ht_mul_exp_le_inv : t * Real.exp (-t * μ) ≤ 1 / μ := by
    have hmul := mul_le_mul_of_nonneg_left hexp_le_inv ht.le
    rwa [show t * (1 / (t * μ)) = 1 / μ by
      field_simp [ht.ne', hμ.ne']] at hmul
  have hsqrt :
      (1 + 1 / Real.sqrt t) ^ 2 ≤ 2 * (1 + 1 / t) :=
    one_add_inv_sqrt_sq_le_two_mul_one_add_inv t ht
  calc
    Real.exp (-t * μ) * (1 + 1 / Real.sqrt t) ^ 2
      ≤ Real.exp (-t * μ) * (2 * (1 + 1 / t)) := by
          gcongr
    _ = (2 / t) * (t * Real.exp (-t * μ) + Real.exp (-t * μ)) := by
          field_simp [ht.ne']
    _ ≤ (2 / t) * (1 / μ + 1) := by
          gcongr
    _ = (2 * (1 + 1 / μ)) / t := by
          field_simp [ht.ne', hμ.ne']
          ring

private lemma heatKernel_entry_mass_weighted_le_div
    (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a) (hvol : (N : ℝ) * a = L)
        (t : ℝ) (ht : 0 < t) (x y : FinLatticeSites 2 N),
        (a ^ 2 : ℝ)⁻¹ * Real.exp (-t * mass ^ 2) *
            latticeHeatKernelMatrix 2 N a t x y ≤
          B / t := by
  obtain ⟨C, hC_pos, hCdiag⟩ := heatKernel_diagonal_mass_weighted_le_uniform mass L hL hmass
  refine ⟨2 * L⁻¹ ^ 2 * C * (1 + 1 / mass ^ 2), by positivity, ?_⟩
  intro N hN a ha hvol t ht x y
  let pxy : ℝ :=
    (a ^ 2 : ℝ)⁻¹ * Real.exp (-t * mass ^ 2) * latticeHeatKernelMatrix 2 N a t x y
  let pxx : ℝ :=
    (a ^ 2 : ℝ)⁻¹ * Real.exp (-t * mass ^ 2) * latticeHeatKernelMatrix 2 N a t x x
  let pyy : ℝ :=
    (a ^ 2 : ℝ)⁻¹ * Real.exp (-t * mass ^ 2) * latticeHeatKernelMatrix 2 N a t y y
  have hxy_nonneg : 0 ≤ pxy := by
    dsimp [pxy]
    exact mul_nonneg (by positivity)
      (latticeHeatKernel_nonneg a ha t ht.le x y)
  have hB_nonneg : 0 ≤ (2 * L⁻¹ ^ 2 * C * (1 + 1 / mass ^ 2)) / t := by
    positivity
  have hsq :
      pxy ^ 2 ≤ pxx * pyy := by
    have hentry := heatKernel_entry_sq_le_diagonal_mul_diagonal
      (d := 2) (N := N) a t x y
    have hscale_nonneg :
        0 ≤ (((a ^ 2 : ℝ)⁻¹ * Real.exp (-t * mass ^ 2)) ^ 2) := by positivity
    calc
      pxy ^ 2
        = (((a ^ 2 : ℝ)⁻¹ * Real.exp (-t * mass ^ 2)) ^ 2) *
            latticeHeatKernelMatrix 2 N a t x y ^ 2 := by
              dsimp [pxy]
              ring
      _ ≤ (((a ^ 2 : ℝ)⁻¹ * Real.exp (-t * mass ^ 2)) ^ 2) *
            (latticeHeatKernelMatrix 2 N a t x x *
              latticeHeatKernelMatrix 2 N a t y y) := by
                gcongr
      _ = pxx * pyy := by
            dsimp [pxx, pyy]
            ring
  have hxx :
      pxx ≤ (2 * L⁻¹ ^ 2 * C * (1 + 1 / mass ^ 2)) / t := by
    have hdiag := hCdiag N a ha hvol t ht x
    calc
      pxx
        ≤ ((a ^ 2 : ℝ)⁻¹ * (1 / Fintype.card (FinLatticeSites 2 N) : ℝ)) *
            (C * (1 + 1 / Real.sqrt t) ^ 2 * Real.exp (-t * mass ^ 2)) := by
              simpa [pxx, mul_assoc, mul_left_comm, mul_comm] using
                mul_le_mul_of_nonneg_left hdiag (by positivity : 0 ≤ (a ^ 2 : ℝ)⁻¹)
      _ = L⁻¹ ^ 2 * (C * (1 + 1 / Real.sqrt t) ^ 2 * Real.exp (-t * mass ^ 2)) := by
            rw [prefactor_eq_L_inv_sq L N a ha hvol]
      _ = L⁻¹ ^ 2 * C * (Real.exp (-t * mass ^ 2) * (1 + 1 / Real.sqrt t) ^ 2) := by ring
      _ ≤ L⁻¹ ^ 2 * C * ((2 * (1 + 1 / mass ^ 2)) / t) := by
            gcongr
            exact exp_mul_one_add_inv_sqrt_sq_le_const_div (mass ^ 2) t (by positivity) ht
      _ = (2 * L⁻¹ ^ 2 * C * (1 + 1 / mass ^ 2)) / t := by
            field_simp [ht.ne']
  have hyy :
      pyy ≤ (2 * L⁻¹ ^ 2 * C * (1 + 1 / mass ^ 2)) / t := by
    have hdiag := hCdiag N a ha hvol t ht y
    calc
      pyy
        ≤ ((a ^ 2 : ℝ)⁻¹ * (1 / Fintype.card (FinLatticeSites 2 N) : ℝ)) *
            (C * (1 + 1 / Real.sqrt t) ^ 2 * Real.exp (-t * mass ^ 2)) := by
              simpa [pyy, mul_assoc, mul_left_comm, mul_comm] using
                mul_le_mul_of_nonneg_left hdiag (by positivity : 0 ≤ (a ^ 2 : ℝ)⁻¹)
      _ = L⁻¹ ^ 2 * (C * (1 + 1 / Real.sqrt t) ^ 2 * Real.exp (-t * mass ^ 2)) := by
            rw [prefactor_eq_L_inv_sq L N a ha hvol]
      _ = L⁻¹ ^ 2 * C * (Real.exp (-t * mass ^ 2) * (1 + 1 / Real.sqrt t) ^ 2) := by ring
      _ ≤ L⁻¹ ^ 2 * C * ((2 * (1 + 1 / mass ^ 2)) / t) := by
            gcongr
            exact exp_mul_one_add_inv_sqrt_sq_le_const_div (mass ^ 2) t (by positivity) ht
      _ = (2 * L⁻¹ ^ 2 * C * (1 + 1 / mass ^ 2)) / t := by
            field_simp [ht.ne']
  have hxx_nonneg : 0 ≤ pxx := by
    dsimp [pxx]
    exact mul_nonneg (by positivity)
      (latticeHeatKernel_nonneg a ha t ht.le x x)
  have hyy_nonneg : 0 ≤ pyy := by
    dsimp [pyy]
    exact mul_nonneg (by positivity)
      (latticeHeatKernel_nonneg a ha t ht.le y y)
  nlinarith [hsq, hxx, hyy, hxy_nonneg, hxx_nonneg, hyy_nonneg]

private lemma heatKernel_entry_mass_weighted_continuous
    {d N : ℕ} [NeZero N] (a mass : ℝ) (ha : 0 < a)
    (x y : FinLatticeSites d N) :
    Continuous (fun t : ℝ =>
      Real.exp (-t * mass ^ 2) * latticeHeatKernelMatrix d N a t x y) := by
  have hExp : Continuous (fun t : ℝ => Real.exp (-t * mass ^ 2)) := by
    exact Real.continuous_exp.comp
      (continuous_id.neg.mul (continuous_const : Continuous fun _ : ℝ => mass ^ 2))
  have hEntry :
      Continuous (fun t : ℝ => latticeHeatKernelMatrix d N a t x y) := by
    have hEq :
        (fun t : ℝ => latticeHeatKernelMatrix d N a t x y) =
          (fun t : ℝ =>
            ∑ m : Fin d → Fin N,
              Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i)) *
                latticeFourierProductBasisFun N d m x *
                latticeFourierProductBasisFun N d m y /
                latticeFourierProductNormSq N d m) := by
      funext t
      rw [latticeHeatKernel_entry_eq_eigenvalue_average
        (d := d) (N := N) (a := a) (ha := ne_of_gt ha) (t := t) (x := x) (y := y)]
    rw [hEq]
    refine continuous_finset_sum _ ?_
    intro m hm
    have hMode :
        Continuous
          (fun t : ℝ => Real.exp (-t * ∑ i : Fin d, latticeEigenvalue1d N a (m i))) := by
      exact Real.continuous_exp.comp
        (continuous_id.neg.mul
          (continuous_const :
            Continuous fun _ : ℝ => ∑ i : Fin d, latticeEigenvalue1d N a (m i)))
    have hConst :
        Continuous
          (fun _ : ℝ =>
            latticeFourierProductBasisFun N d m x *
              latticeFourierProductBasisFun N d m y /
              latticeFourierProductNormSq N d m) :=
      continuous_const
    simpa [mul_assoc, div_eq_mul_inv] using hMode.mul hConst
  exact hExp.mul hEntry

private lemma heatKernel_entry_mass_weighted_integrableOn_Icc
    {d N : ℕ} [NeZero N] (a mass : ℝ) (ha : 0 < a)
    (x y : FinLatticeSites d N) (T : ℝ) :
    IntegrableOn
      (fun t : ℝ => Real.exp (-t * mass ^ 2) * latticeHeatKernelMatrix d N a t x y)
      (Set.Icc 0 T) := by
  exact (heatKernel_entry_mass_weighted_continuous a mass ha x y).integrableOn_Icc

private lemma rpow_two_div_nat_mul_nat
    (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha : 0 < a) :
    (a ^ (2 / (m : ℝ))) ^ (m : ℝ) = a ^ 2 := by
  have hm_ne : (m : ℝ) ≠ 0 := by positivity
  have hmul : (2 / (m : ℝ)) * (m : ℝ) = 2 := by
    field_simp [hm_ne]
  calc
    (a ^ (2 / (m : ℝ))) ^ (m : ℝ)
      = a ^ ((2 / (m : ℝ)) * (m : ℝ)) := by
          rw [← Real.rpow_mul (le_of_lt ha)]
    _ = a ^ 2 := by simpa [hmul]

private lemma div_pow_nat_sub_one_rpow_inv_eq
    (m : ℕ) (hm : 1 ≤ m) (B t : ℝ) (hB : 0 ≤ B) (ht : 0 < t) :
    (((B / t) ^ (m - 1 : ℕ) : ℝ) ^ ((m : ℝ)⁻¹)) =
      B ^ (1 - (m : ℝ)⁻¹) * t ^ ((m : ℝ)⁻¹ - 1) := by
  have hm_ne : (m : ℝ) ≠ 0 := by positivity
  have hBt_nonneg : 0 ≤ B / t := by positivity
  have hm_sub : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    norm_num [Nat.cast_sub hm]
  calc
    (((B / t) ^ (m - 1 : ℕ) : ℝ) ^ ((m : ℝ)⁻¹))
      = (B / t) ^ (((m - 1 : ℕ) : ℝ) * (m : ℝ)⁻¹) := by
          rw [show ((B / t) ^ (m - 1 : ℕ) : ℝ) = (B / t) ^ (((m - 1 : ℕ) : ℝ)) by
            rw [Real.rpow_natCast]]
          rw [← Real.rpow_mul hBt_nonneg]
    _ = (B / t) ^ (1 - (m : ℝ)⁻¹) := by
          congr 1
          rw [hm_sub]
          field_simp [hm_ne]
    _ = (B * t⁻¹) ^ (1 - (m : ℝ)⁻¹) := by rw [div_eq_mul_inv]
    _ = B ^ (1 - (m : ℝ)⁻¹) * (t⁻¹) ^ (1 - (m : ℝ)⁻¹) := by
          rw [Real.mul_rpow hB (inv_nonneg.mpr ht.le)]
    _ = B ^ (1 - (m : ℝ)⁻¹) * (t ^ (1 - (m : ℝ)⁻¹))⁻¹ := by
          rw [Real.inv_rpow (le_of_lt ht)]
    _ = B ^ (1 - (m : ℝ)⁻¹) * t ^ ((m : ℝ)⁻¹ - 1) := by
          congr 1
          rw [← Real.rpow_neg (le_of_lt ht)]
          congr 1
          ring

private lemma integral_rpow_inv_nat_sub_one
    (m : ℕ) (hm : 1 ≤ m) (T : ℝ) (hT : 0 < T) :
    (∫ t in (0 : ℝ)..T, t ^ ((m : ℝ)⁻¹ - 1)) = (m : ℝ) * T ^ ((m : ℝ)⁻¹) := by
  have hm0 : m ≠ 0 := by omega
  have h_inv_pos : 0 < (m : ℝ)⁻¹ := by positivity
  calc
    (∫ t in (0 : ℝ)..T, t ^ ((m : ℝ)⁻¹ - 1))
      = (T ^ (((m : ℝ)⁻¹ - 1) + 1) - (0 : ℝ) ^ (((m : ℝ)⁻¹ - 1) + 1)) /
          (((m : ℝ)⁻¹ - 1) + 1) := by
            rw [integral_rpow]
            left
            linarith
    _ = (T ^ ((m : ℝ)⁻¹) - 0 ^ ((m : ℝ)⁻¹)) / ((m : ℝ)⁻¹) := by ring_nf
    _ = T ^ ((m : ℝ)⁻¹) / ((m : ℝ)⁻¹) := by
          rw [Real.zero_rpow (by positivity : (m : ℝ)⁻¹ ≠ 0), sub_zero]
    _ = (m : ℝ) * T ^ ((m : ℝ)⁻¹) := by
          field_simp [Nat.cast_ne_zero.mpr hm0]

private lemma rpow_inv_nat_sub_one_integrableOn_Icc
    (m : ℕ) (hm : 1 ≤ m) (T : ℝ) (hT : 0 < T) :
    IntegrableOn (fun t : ℝ => t ^ ((m : ℝ)⁻¹ - 1)) (Set.Icc 0 T) volume := by
  rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hT.le]
  refine intervalIntegral.intervalIntegrable_rpow' ?_
  have h_inv_pos : 0 < (m : ℝ)⁻¹ := by positivity
  linarith

private lemma rough_heatKernel_slice_weighted_pow_sum_le
    (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a) (hvol : (N : ℝ) * a = L)
        (t : ℝ) (ht : 0 < t) (x : FinLatticeSites 2 N),
        ∑ y : FinLatticeSites 2 N,
          ‖a ^ (2 / (m : ℝ)) *
              ((a ^ 2 : ℝ)⁻¹ * Real.exp (-t * mass ^ 2) *
                latticeHeatKernelMatrix 2 N a t x y)‖ ^ (m : ℝ)
          ≤ ((B / t) ^ (m - 1 : ℕ) : ℝ) := by
  obtain ⟨B, hB_pos, hB⟩ := heatKernel_entry_mass_weighted_le_div mass L hL hmass
  refine ⟨B, hB_pos, ?_⟩
  intro N hN a ha hvol t ht x
  let α : ℝ := a ^ (2 / (m : ℝ))
  let g : FinLatticeSites 2 N → ℝ := fun y =>
    (a ^ 2 : ℝ)⁻¹ * Real.exp (-t * mass ^ 2) * latticeHeatKernelMatrix 2 N a t x y
  have hm_pos : 0 < (m : ℝ) := by positivity
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    positivity
  have hg_nonneg : ∀ y : FinLatticeSites 2 N, 0 ≤ g y := by
    intro y
    dsimp [g]
    exact mul_nonneg (by positivity)
      (latticeHeatKernel_nonneg a ha t ht.le x y)
  have hBg : ∀ y : FinLatticeSites 2 N, g y ≤ B / t := by
    intro y
    simpa [g] using hB N a ha hvol t ht x y
  have hpow_term :
      ∀ y : FinLatticeSites 2 N,
        g y ^ (m : ℝ) ≤ ((B / t) ^ (m - 1 : ℕ) : ℝ) * g y := by
    intro y
    have hpow :
        g y ^ (m - 1 : ℕ) ≤ (B / t) ^ (m - 1 : ℕ) := by
      exact pow_le_pow_left₀ (hg_nonneg y) (hBg y) (m - 1)
    calc
      g y ^ (m : ℝ) = g y ^ m := by rw [Real.rpow_natCast]
      _ = g y ^ (m - 1) * g y := by
            have hm1 : m = (m - 1) + 1 := by omega
            rw [hm1, pow_add]
            simp
      _ ≤ (B / t) ^ (m - 1) * g y := by
            gcongr
            exact hg_nonneg y
  have hrow :
      a ^ 2 * ∑ y : FinLatticeSites 2 N, g y = Real.exp (-t * mass ^ 2) := by
    calc
      a ^ 2 * ∑ y : FinLatticeSites 2 N, g y
        = a ^ 2 * ∑ y : FinLatticeSites 2 N,
            ((a ^ 2 : ℝ)⁻¹ * Real.exp (-t * mass ^ 2) *
              latticeHeatKernelMatrix 2 N a t x y) := by
                simp [g]
      _ = ∑ y : FinLatticeSites 2 N,
            Real.exp (-t * mass ^ 2) * latticeHeatKernelMatrix 2 N a t x y := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro y hy
              have ha2_ne : (a ^ 2 : ℝ) ≠ 0 := by positivity
              calc
                a ^ 2 *
                    ((a ^ 2 : ℝ)⁻¹ * Real.exp (-t * mass ^ 2) *
                      latticeHeatKernelMatrix 2 N a t x y)
                  = (a ^ 2 * (a ^ 2 : ℝ)⁻¹) *
                      (Real.exp (-t * mass ^ 2) *
                        latticeHeatKernelMatrix 2 N a t x y) := by ring
                _ = Real.exp (-t * mass ^ 2) * latticeHeatKernelMatrix 2 N a t x y := by
                      field_simp [ha2_ne]
      _ = Real.exp (-t * mass ^ 2) *
            ∑ y : FinLatticeSites 2 N, latticeHeatKernelMatrix 2 N a t x y := by
              rw [Finset.mul_sum]
      _ = Real.exp (-t * mass ^ 2) * 1 := by
            rw [heatKernel_row_sum_eq_one (d := 2) (N := N) (a := a) ha t x]
      _ = Real.exp (-t * mass ^ 2) := by ring
  have hsum_g :
      a ^ 2 * ∑ y : FinLatticeSites 2 N, g y ^ (m : ℝ) ≤ ((B / t) ^ (m - 1 : ℕ) : ℝ) := by
    have hsum_le :
        ∑ y : FinLatticeSites 2 N, g y ^ (m : ℝ) ≤
          ∑ y : FinLatticeSites 2 N, ((B / t) ^ (m - 1 : ℕ) : ℝ) * g y := by
      exact Finset.sum_le_sum (fun y hy => hpow_term y)
    have hexp_le_one : Real.exp (-t * mass ^ 2) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith
    calc
      a ^ 2 * ∑ y : FinLatticeSites 2 N, g y ^ (m : ℝ)
        ≤ a ^ 2 *
            ∑ y : FinLatticeSites 2 N, ((B / t) ^ (m - 1 : ℕ) : ℝ) * g y := by
            gcongr
      _ = a ^ 2 * (((B / t) ^ (m - 1 : ℕ) : ℝ) * ∑ y : FinLatticeSites 2 N, g y) := by
            congr 1
            rw [Finset.mul_sum]
      _ = ((B / t) ^ (m - 1 : ℕ) : ℝ) * (a ^ 2 * ∑ y : FinLatticeSites 2 N, g y) := by
            ring
      _ = ((B / t) ^ (m - 1 : ℕ) : ℝ) * Real.exp (-t * mass ^ 2) := by rw [hrow]
      _ ≤ ((B / t) ^ (m - 1 : ℕ) : ℝ) * 1 := by
            gcongr
      _ = ((B / t) ^ (m - 1 : ℕ) : ℝ) := by ring
  have hsum_alpha :
      ∑ y : FinLatticeSites 2 N, ‖α * g y‖ ^ (m : ℝ) =
        a ^ 2 * ∑ y : FinLatticeSites 2 N, g y ^ (m : ℝ) := by
    calc
      ∑ y : FinLatticeSites 2 N, ‖α * g y‖ ^ (m : ℝ)
        = ∑ y : FinLatticeSites 2 N, α ^ (m : ℝ) * g y ^ (m : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            have hgy : 0 ≤ g y := hg_nonneg y
            have hmul_nonneg : 0 ≤ α * g y := mul_nonneg hα_nonneg hgy
            rw [Real.norm_of_nonneg hmul_nonneg, Real.mul_rpow hα_nonneg hgy]
      _ = a ^ 2 * ∑ y : FinLatticeSites 2 N, g y ^ (m : ℝ) := by
            rw [rpow_two_div_nat_mul_nat m hm a ha, Finset.mul_sum]
  calc
    ∑ y : FinLatticeSites 2 N, ‖α * g y‖ ^ (m : ℝ)
      = a ^ 2 * ∑ y : FinLatticeSites 2 N, g y ^ (m : ℝ) := hsum_alpha
    _ ≤ ((B / t) ^ (m - 1 : ℕ) : ℝ) := hsum_g

axiom canonicalRoughCovariance_pow_sum_le_uniform_in_aN_of_three_le
    {d : ℕ} (hd : d = 2) (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (m : ℕ) (hm : 3 ≤ m) :
    ∃ C_m : ℝ, 0 < C_m ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a)
        (_h_vol : (N : ℝ) * a = L)
        (T : ℝ) (_hT : 0 < T) (x : FinLatticeSites d N),
        a^d * ∑ y : FinLatticeSites d N,
          |canonicalRoughCovariance d N a mass T x y| ^ m ≤ C_m * T


/-- **Glimm-Jaffe Thm 8.5.2 (smooth-side, d=2).** Polylog `T` bound on
the smooth Wick constant, uniform in `(N, a)` at fixed `L = N · a`:

  `smoothWickConstant d N a mass T ≤ A + B · (1 + |log T|)`

with `A, B ≥ 0` depending only on `(mass, L)`. The `hd : d = 2`
restriction is essential: in `d ≥ 3` the smooth Wick constant diverges
as `T^{-1/2}` (power-law, not log), and the axiom is mathematically
false.

**References:** Glimm–Jaffe, *Quantum Physics: A Functional Integral
Point of View*, 2nd ed., Theorem 8.5.2 + Lemma 8.5.4 (lattice heat
kernel trace bound); Reed–Simon vol. II, Theorem XI.2 (heat kernel
trace).

**Vetting:** Gemini deep-think (DT 2026-05-12) — verdict **Standard**.
The 2026-05-12 vetting round caught a d=2 trap (the original draft
had `d : ℕ` quantified generically) and confirmed (a) correct typing,
(b) correct strength matching Glimm–Jaffe Thm 8.5.2, (c) non-vacuity,
(d) sufficiency for downstream S4 use. Full record at
`AXIOM_AUDIT.md` (2026-05-12 entry) and `docs/phase-B-textbook-axioms.md`.

**Discharge strategy:** tighten the existing `heat_kernel_1d_bound`
(currently with the trivial `C = N` constant) to the textbook
`(a, N)`-uniform `C(L)` form via `gaussian_sum_bound`
(`Pphi2/NelsonEstimate/HeatKernelBound.lean:204` — uniform Gaussian
sum estimate via `sin² ≥ (2/π)² · x²` on [0, π/2]). Propagate through
`heat_kernel_trace_bound` and the Schwinger integral
`c_S = ∫_T^∞ trace(e^{-t · M_a})/|Λ| dt`. Estimated ~500-800 lines /
2-3 weeks. Full plan: `docs/phase-B-textbook-axioms.md`. -/
theorem smoothWickConstant_le_log_uniform_in_aN
    {d : ℕ} (hd : d = 2) (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a)
        (_h_vol : (N : ℝ) * a = L)
        (T : ℝ) (_hT : 0 < T),
        smoothWickConstant d N a mass T ≤ A + B * (1 + |Real.log T|) :=
  smoothWickConstant_le_log_uniform_in_aN_proved hd mass L hL hmass

/-- **Glimm-Jaffe Thm 8.5.2 (rough-side, d=2).** Position-space `L^m`
site-sum bound for the canonical rough covariance, uniform in `(N, a)`
at fixed `L = N · a`:

  `a^d · Σ_y |C_R(x, y)|^m ≤ C_m · T`     for all `m ≥ 1`

with `C_m > 0` depending only on `(mass, L, m)`. The `hd : d = 2`
restriction is essential: for `d ≥ 3` the scaling becomes
`T^{m(1 − d/2) + d/2}`, which diverges at `m ≥ 3` for `d = 3` — the
linear-in-`T` bound asserted here is a magical d=2 property (the
exponent reduces to `m · 0 + 1 = 1`).

**References:** Glimm–Jaffe, *Quantum Physics*, 2nd ed., Theorem 8.5.2
+ Lemma 8.5.5 (rough covariance position-space estimates); Janson,
*Gaussian Hilbert Spaces*, Ch. 6 (hypercontractivity input).

**Vetting:** Gemini deep-think (DT 2026-05-12) — verdict **Standard**.
Same vetting round as the smooth-side axiom; caught the d=2 trap and
confirmed `|C_R|^m` (vs `C_R^m`) is the correct LHS for the m-odd case
and that per-`m` existential `C_m` (vs uniform in `m`) is sufficient
for the downstream S4 use, where `m` is fixed to `k - j` per cross-term.
Full record at `AXIOM_AUDIT.md` (2026-05-12 entry).

**Discharge strategy:**
* `m = 1`: directly from the Schwinger identity + heat-kernel
  probability normalisation `a^d · Σ_y p_t(x, y) = 1` (gives
  `a^d · Σ_y C_R(x, y) = ∫_0^T 1 dt = T`).
* `m = 2`: position-space rewrite of the existing
  `roughCovariance_sq_summable` via Plancherel + translation
  invariance.
* `m ≥ 3`: Hölder interpolation between `m = 2` and the L^∞ bound on
  off-diagonal `C_R(x, y)` (which decays Gaussian-exponentially in
  `|x − y|`, dominating the at-most-logarithmic coincident-points
  divergence in d=2).

Estimated ~300-500 lines / 1-2 weeks. Full plan:
`docs/phase-B-textbook-axioms.md`. -/
theorem canonicalRoughCovariance_pow_sum_le_uniform_in_aN
    {d : ℕ} (hd : d = 2) (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ C_m : ℝ, 0 < C_m ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a)
        (_h_vol : (N : ℝ) * a = L)
        (T : ℝ) (_hT : 0 < T) (x : FinLatticeSites d N),
        a^d * ∑ y : FinLatticeSites d N,
          |canonicalRoughCovariance d N a mass T x y| ^ m ≤ C_m * T := by
  subst d
  by_cases hm1 : m = 1
  · rcases canonicalRoughCovariance_pow_one_sum_le_uniform_in_aN_proved mass L hL hmass with
      ⟨C1, hC1_pos, hC1⟩
    refine ⟨C1, hC1_pos, ?_⟩
    intro N hN a ha hvol T hT x
    simpa [hm1] using hC1 N a ha hvol T hT x
  · by_cases hm2 : m = 2
    · rcases canonicalRoughCovariance_pow_two_sum_le_uniform_in_aN_proved mass L hL hmass with
        ⟨C2, hC2_pos, hC2⟩
      refine ⟨C2, hC2_pos, ?_⟩
      intro N hN a ha hvol T hT x
      simpa [hm2] using hC2 N a ha hvol T hT x
    · have hm3 : 3 ≤ m := by omega
      exact canonicalRoughCovariance_pow_sum_le_uniform_in_aN_of_three_le
        (d := 2) rfl mass L hL hmass m hm3

end Pphi2
