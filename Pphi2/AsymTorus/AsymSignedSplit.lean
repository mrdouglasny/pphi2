/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.AsymTorus.AsymExpMomentDischarge

/-!
# Signed test functions via the `f = f₊ − f₋` split (Layer C recovery)

The Layer A axiom `asymInteracting_mgf_gaussianDominated`
(`AsymExpMomentDischarge.lean`) is restricted to quartic `P` and sitewise
same-sign test functions. The explicit one-site sextic in `AXIOM_AUDIT.md`
(2026-08-22) shows why the degree hypothesis survives the signed split.
This file recovers **signed** lattice test functions:

* **`asymInteracting_expMoment_of_signed`** — for any `f`, writing
  `f = f₊ − f₋` with `f₊ = max f 0`, `f₋ = max (−f) 0` (both sitewise `≥ 0`),
  `|⟨ω,f⟩| ≤ |⟨ω,f₊⟩| + |⟨ω,f₋⟩|`, Cauchy-Schwarz
  `E[e^{|A|+|B|}] ≤ (E e^{2|A|})^{1/2} (E e^{2|B|})^{1/2}`, and the
  sign-restricted axiom at `2f₊`, `2f₋` give
  `∫ e^{|⟨ω,f⟩|} dμ_int ≤ 2 · exp(Var_int(⟨ω,f₊⟩) + Var_int(⟨ω,f₋⟩))`.
  Constants: the axiom at `g = 2f₊` gives `E e^{2|⟨ω,f₊⟩|} ≤ 2·exp(2·Var f₊)`;
  the square root halves both the exponent and the prefactor:
  `√(2e^{2V₊})·√(2e^{2V₋}) = 2·e^{V₊+V₋}` (vetted constants — AXIOM_AUDIT
  2026-07-12 Codex entry).

* **`asymInteracting_expMoment_volume_uniform_proof`** — the Layer C assembly
  (moved here from `AsymExpMomentDischarge.lean`, 2026-07-13): split lemma +
  Layer B2 lattice variance bound + the joint-↔-torus pushforward. The
  free-variance seminorm is stated in the **split form**
  `C · (Var_free(f₊) + Var_free(f₋))`: `Var_free(f₊) + Var_free(f₋)` is NOT
  controlled by `Var_free(f)` (cross-term cancellation), so the pre-2026-07-13
  conclusion form `C · Var_free(f)` is not recoverable from the sign-restricted
  Layer A without the (unformalized) entrywise nonnegativity of the free
  lattice covariance kernel, which would give
  `Var_free(f₊) + Var_free(f₋) ≤ Var_free(|f|)`.
-/

noncomputable section

open MeasureTheory GaussianField

namespace Pphi2

/-- **Signed test functions from the sign-restricted Newman bound.**

This theorem inherits `hP : P.n = 4` from Layer A.

For an arbitrary (mixed-sign) lattice test function `f`, split `f = f₊ − f₋`
into its sitewise nonnegative and nonpositive parts. Then `|⟨ω,f⟩| ≤
|⟨ω,f₊⟩| + |⟨ω,f₋⟩|`, and Cauchy-Schwarz together with the sign-restricted
Layer A axiom `asymInteracting_mgf_gaussianDominated` applied at `2f₊` and
`2f₋` yields the exp-moment bound with the split variance seminorm:
`∫ e^{|⟨ω,f⟩|} dμ_int ≤ 2 · exp(Var_int(⟨ω,f₊⟩) + Var_int(⟨ω,f₋⟩))`.

This is the vetted Layer-C recovery of signed `f` (AXIOM_AUDIT.md,
2026-07-12/13; Gemini 3.1-pro + Codex GPT-5.5). -/
theorem asymInteracting_expMoment_of_signed
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (hP : P.n = 4)
    (mass : ℝ) (hmass : 0 < mass) (a : ℝ) (ha : 0 < a)
    (f : AsymLatticeField Nt Ns) :
    Integrable (fun ω => Real.exp (|ω f|))
      (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ∧
    ∫ ω, Real.exp (|ω f|)
      ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ≤
    2 * Real.exp (
      (∫ ω, (ω (fun x => max (f x) 0)) ^ 2
        ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass)) +
      (∫ ω, (ω (fun x => max (-(f x)) 0)) ^ 2
        ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass))) := by
  set μ := interactingLatticeMeasureAsym Nt Ns P a mass ha hmass with hμ_def
  set fp : AsymLatticeField Nt Ns := fun x => max (f x) 0 with hfp_def
  set fm : AsymLatticeField Nt Ns := fun x => max (-(f x)) 0 with hfm_def
  -- Sitewise nonnegativity of the doubled parts
  have h2fp : ∀ x, 0 ≤ ((2 : ℝ) • fp) x := fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, hfp_def]
    exact mul_nonneg (by norm_num) (le_max_right _ _)
  have h2fm : ∀ x, 0 ≤ ((2 : ℝ) • fm) x := fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, hfm_def]
    exact mul_nonneg (by norm_num) (le_max_right _ _)
  -- Decomposition f = f₊ − f₋
  have hsplit : f = fp - fm := by
    funext x
    simp only [Pi.sub_apply, hfp_def, hfm_def]
    rcases le_total (f x) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith : (0 : ℝ) ≤ -(f x))]
      ring
    · rw [max_eq_left h, max_eq_right (by linarith : -(f x) ≤ (0 : ℝ))]
      ring
  -- Pairing identities (ω is a continuous linear functional)
  have heval : ∀ ω : Configuration (AsymLatticeField Nt Ns), ω f = ω fp - ω fm := by
    intro ω
    conv_lhs => rw [hsplit]
    exact map_sub ω fp fm
  have h2p : ∀ ω : Configuration (AsymLatticeField Nt Ns),
      ω ((2 : ℝ) • fp) = 2 * ω fp := fun ω => by
    rw [map_smul, smul_eq_mul]
  have h2m : ∀ ω : Configuration (AsymLatticeField Nt Ns),
      ω ((2 : ℝ) • fm) = 2 * ω fm := fun ω => by
    rw [map_smul, smul_eq_mul]
  -- Layer A (sign-restricted) at the doubled positive/negative parts
  obtain ⟨hint_p, hbound_p⟩ :=
    asymInteracting_mgf_gaussianDominated P hP mass hmass Nt Ns a ha ((2 : ℝ) • fp) h2fp
  obtain ⟨hint_m, hbound_m⟩ :=
    asymInteracting_mgf_gaussianDominated P hP mass hmass Nt Ns a ha ((2 : ℝ) • fm) h2fm
  -- exp|⟨ω,2f±⟩| is the square of exp|⟨ω,f±⟩|
  have hu_sq : ∀ ω : Configuration (AsymLatticeField Nt Ns),
      Real.exp (|ω ((2 : ℝ) • fp)|) = Real.exp (|ω fp|) ^ 2 := fun ω => by
    rw [h2p ω, abs_mul, abs_two, two_mul, Real.exp_add, sq]
  have hv_sq : ∀ ω : Configuration (AsymLatticeField Nt Ns),
      Real.exp (|ω ((2 : ℝ) • fm)|) = Real.exp (|ω fm|) ^ 2 := fun ω => by
    rw [h2m ω, abs_mul, abs_two, two_mul, Real.exp_add, sq]
  -- Measurability
  have hmeas_u : Measurable fun ω : Configuration (AsymLatticeField Nt Ns) =>
      Real.exp (|ω fp|) := ((configuration_eval_measurable fp).abs).exp
  have hmeas_v : Measurable fun ω : Configuration (AsymLatticeField Nt Ns) =>
      Real.exp (|ω fm|) := ((configuration_eval_measurable fm).abs).exp
  have hmeas_uf : Measurable fun ω : Configuration (AsymLatticeField Nt Ns) =>
      Real.exp (|ω f|) := ((configuration_eval_measurable f).abs).exp
  -- L² membership of u = exp|⟨ω,f₊⟩| and v = exp|⟨ω,f₋⟩|
  have hint_u2 : Integrable
      (fun ω : Configuration (AsymLatticeField Nt Ns) => Real.exp (|ω fp|) ^ 2) μ :=
    hint_p.congr (ae_of_all _ fun ω => hu_sq ω)
  have hint_v2 : Integrable
      (fun ω : Configuration (AsymLatticeField Nt Ns) => Real.exp (|ω fm|) ^ 2) μ :=
    hint_m.congr (ae_of_all _ fun ω => hv_sq ω)
  have hu2 : MemLp (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      Real.exp (|ω fp|)) 2 μ :=
    (memLp_two_iff_integrable_sq hmeas_u.aestronglyMeasurable).mpr hint_u2
  have hv2 : MemLp (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      Real.exp (|ω fm|)) 2 μ :=
    (memLp_two_iff_integrable_sq hmeas_v.aestronglyMeasurable).mpr hint_v2
  -- Product of the two L² functions is integrable
  have hint_uv : Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      Real.exp (|ω fp|) * Real.exp (|ω fm|)) μ := by
    simpa [Pi.mul_apply] using hu2.integrable_mul hv2
  -- Pointwise domination exp|⟨ω,f⟩| ≤ exp|⟨ω,f₊⟩| · exp|⟨ω,f₋⟩|
  have hpoint : ∀ ω : Configuration (AsymLatticeField Nt Ns),
      Real.exp (|ω f|) ≤ Real.exp (|ω fp|) * Real.exp (|ω fm|) := by
    intro ω
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    rw [heval ω]
    simpa [sub_eq_add_neg, abs_neg] using abs_add_le (ω fp) (-(ω fm))
  -- Integrability of the signed exp-moment
  have hint_f : Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      Real.exp (|ω f|)) μ := by
    refine hint_uv.mono' hmeas_uf.aestronglyMeasurable ?_
    refine ae_of_all _ fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact hpoint ω
  refine ⟨hint_f, ?_⟩
  -- Abbreviate the four second moments
  set Vp := ∫ ω : Configuration (AsymLatticeField Nt Ns), (ω fp) ^ 2 ∂μ with hVp_def
  set Vm := ∫ ω : Configuration (AsymLatticeField Nt Ns), (ω fm) ^ 2 ∂μ with hVm_def
  -- Rewrite the Layer A bounds in terms of Vp, Vm
  have hbound_u2 : ∫ ω, Real.exp (|ω fp|) ^ 2 ∂μ ≤ 2 * Real.exp (2 * Vp) := by
    have hvar : ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω ((2 : ℝ) • fp)) ^ 2 ∂μ = 4 * Vp := by
      rw [hVp_def, ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      change (ω ((2 : ℝ) • fp)) ^ 2 = 4 * (ω fp) ^ 2
      rw [h2p ω]; ring
    calc ∫ ω, Real.exp (|ω fp|) ^ 2 ∂μ
        = ∫ ω, Real.exp (|ω ((2 : ℝ) • fp)|) ∂μ :=
          integral_congr_ae (ae_of_all _ fun ω => (hu_sq ω).symm)
      _ ≤ 2 * Real.exp ((1 / 2) *
            ∫ ω : Configuration (AsymLatticeField Nt Ns),
              (ω ((2 : ℝ) • fp)) ^ 2 ∂μ) := hbound_p
      _ = 2 * Real.exp (2 * Vp) := by rw [hvar]; ring_nf
  have hbound_v2 : ∫ ω, Real.exp (|ω fm|) ^ 2 ∂μ ≤ 2 * Real.exp (2 * Vm) := by
    have hvar : ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω ((2 : ℝ) • fm)) ^ 2 ∂μ = 4 * Vm := by
      rw [hVm_def, ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      change (ω ((2 : ℝ) • fm)) ^ 2 = 4 * (ω fm) ^ 2
      rw [h2m ω]; ring
    calc ∫ ω, Real.exp (|ω fm|) ^ 2 ∂μ
        = ∫ ω, Real.exp (|ω ((2 : ℝ) • fm)|) ∂μ :=
          integral_congr_ae (ae_of_all _ fun ω => (hv_sq ω).symm)
      _ ≤ 2 * Real.exp ((1 / 2) *
            ∫ ω : Configuration (AsymLatticeField Nt Ns),
              (ω ((2 : ℝ) • fm)) ^ 2 ∂μ) := hbound_m
      _ = 2 * Real.exp (2 * Vm) := by rw [hvar]; ring_nf
  -- Cauchy-Schwarz (Hölder with p = q = 2)
  have hCS : ∫ ω, Real.exp (|ω fp|) * Real.exp (|ω fm|) ∂μ ≤
      (∫ ω, Real.exp (|ω fp|) ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) *
      (∫ ω, Real.exp (|ω fm|) ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) := by
    refine integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (ae_of_all _ fun ω => (Real.exp_pos _).le)
      (ae_of_all _ fun ω => (Real.exp_pos _).le) ?_ ?_
    · rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]; exact hu2
    · rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]; exact hv2
  -- Convert the inner rpow to npow
  have hrpow : ∀ x : ℝ, x ^ (2 : ℝ) = x ^ 2 := fun x => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [hrpow] at hCS
  -- Assemble: monotone comparison, Cauchy-Schwarz, Layer A bounds
  have hVp_nonneg : (0 : ℝ) ≤ ∫ ω, Real.exp (|ω fp|) ^ 2 ∂μ :=
    integral_nonneg fun ω => sq_nonneg _
  have hVm_nonneg : (0 : ℝ) ≤ ∫ ω, Real.exp (|ω fm|) ^ 2 ∂μ :=
    integral_nonneg fun ω => sq_nonneg _
  have hfactor : ((2 : ℝ) * Real.exp (2 * Vp)) ^ ((1 : ℝ) / 2) *
      ((2 : ℝ) * Real.exp (2 * Vm)) ^ ((1 : ℝ) / 2) = 2 * Real.exp (Vp + Vm) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    have hsq : (2 : ℝ) * Real.exp (2 * Vp) * ((2 : ℝ) * Real.exp (2 * Vm)) =
        ((2 : ℝ) * Real.exp (Vp + Vm)) ^ 2 := by
      have hkey : Real.exp (2 * Vp) * Real.exp (2 * Vm) =
          Real.exp (Vp + Vm) ^ 2 := by
        rw [← Real.exp_add, sq, ← Real.exp_add]
        congr 1
        ring
      rw [mul_pow, ← hkey]
      ring
    rw [hsq, ← Real.rpow_natCast ((2 : ℝ) * Real.exp (Vp + Vm)) 2,
      ← Real.rpow_mul (by positivity)]
    norm_num
  calc ∫ ω, Real.exp (|ω f|) ∂μ
      ≤ ∫ ω, Real.exp (|ω fp|) * Real.exp (|ω fm|) ∂μ :=
        integral_mono hint_f hint_uv hpoint
    _ ≤ (∫ ω, Real.exp (|ω fp|) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) *
        (∫ ω, Real.exp (|ω fm|) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := hCS
    _ ≤ ((2 : ℝ) * Real.exp (2 * Vp)) ^ ((1 : ℝ) / 2) *
        ((2 : ℝ) * Real.exp (2 * Vm)) ^ ((1 : ℝ) / 2) := by
        refine mul_le_mul
          (Real.rpow_le_rpow hVp_nonneg hbound_u2 (by norm_num))
          (Real.rpow_le_rpow hVm_nonneg hbound_v2 (by norm_num))
          (Real.rpow_nonneg hVm_nonneg _)
          (Real.rpow_nonneg (by positivity) _)
    _ = 2 * Real.exp (Vp + Vm) := hfactor

/-! ## Layer C: assembly theorem (moved from `AsymExpMomentDischarge.lean`) -/

/-- **Layer C assembly**: combining Layer A (quartic, sign-restricted Newman MGF
Gaussian-domination on the lattice, via the signed-split lemma
`asymInteracting_expMoment_of_signed`) + Layer B2 (`Lt`-uniform
interacting-vs-free variance bound) gives the volume-uniform exp-moment
bound with the **split free-variance seminorm**.

The assembly is purely structural:
1. For a torus test function `f`, push the torus integral back to the
   lattice via `asymTorusInteractingMeasureIso = (μ_int^{lattice}).map ι`
   where `ι = asymTorusEmbedLiftIso`.
2. Use `(ι ω)(f) = ω(asymLatticeTestFnIso f)` to swap the torus pairing
   for the lattice pairing; set `g = asymLatticeTestFnIso f`.
3. Apply the signed-split lemma on the lattice:
   `∫ e^{|⟨ω,g⟩|} dμ_int^{lattice} ≤ 2 · exp(Var_int(⟨ω,g₊⟩) + Var_int(⟨ω,g₋⟩))`.
4. Apply Layer B2 at `g₊` and `g₋`:
   `Var_int(⟨ω,g±⟩) ≤ C_B · Var_free(⟨ω,g±⟩)` uniformly in `Lt`.
5. Combine: `≤ 2 · exp(C_B · (Var_free(⟨ω,g₊⟩) + Var_free(⟨ω,g₋⟩)))`.
   Set `K = 2`, `C = C_B`.

The constant `C_B` is `Lt`-uniform by Layer B2, so `K = 2`, `C = C_B` is
`Lt`-uniform.

**Seminorm form (2026-07-13).** Before the sign restriction of Layer A this
theorem carried the seminorm `C · Var_free(⟨ω,g⟩)`; that form is NOT
recoverable from the sign-restricted axiom, since
`Var_free(g₊) + Var_free(g₋)` is not controlled by `Var_free(g)`
(cross-term cancellation). Matching the original form would additionally
need the entrywise nonnegativity of the free lattice covariance kernel
(`Var_free(g₊) + Var_free(g₋) ≤ Var_free(|g|)`) plus an `|f|`-seminorm
restatement of the torus-level target — tracked in `AXIOM_AUDIT.md`
(2026-07-13). -/
theorem asymInteracting_expMoment_volume_uniform_proof
    (Ls : ℝ) [hLs : Fact (0 < Ls)]
    (P : InteractionPolynomial) (hP : P.n = 4) (mass : ℝ) (hmass : 0 < mass) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (L : ℝ) [Fact (0 < L)] (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
        (a : ℝ) (ha : 0 < a),
        (Nt : ℝ) * a = L → (Ns : ℝ) * a = Ls → ∀ f : AsymTorusTestFunction L Ls,
        Integrable (fun ω : Configuration (AsymTorusTestFunction L Ls) =>
            Real.exp (|ω f|))
          (asymTorusInteractingMeasureIso L Ls Nt Ns a P mass ha hmass) ∧
        ∫ ω : Configuration (AsymTorusTestFunction L Ls), Real.exp (|ω f|)
          ∂(asymTorusInteractingMeasureIso L Ls Nt Ns a P mass ha hmass) ≤
        K * Real.exp (C * (
          (∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω (fun x => max (asymLatticeTestFnIso L Ls Nt Ns a f x) 0)) ^ 2
            ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) +
          (∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω (fun x => max (-(asymLatticeTestFnIso L Ls Nt Ns a f x)) 0)) ^ 2
            ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)))) := by
  obtain ⟨C_B, hC_B_pos, hC_B_bound⟩ :=
    asymInteractingVariance_le_freeVariance_lattice_Lt_uniform P mass hmass Ls
  refine ⟨2, C_B, by norm_num, hC_B_pos, ?_⟩
  intro L _hL Nt Ns _ _ a ha hvolt hvols f
  set g := asymLatticeTestFnIso L Ls Nt Ns a f with hg_def
  set μ_int_T := asymTorusInteractingMeasureIso L Ls Nt Ns a P mass ha hmass
  set μ_int_L := interactingLatticeMeasureAsym Nt Ns P a mass ha hmass
  set μ_free := latticeGaussianMeasureAsym Nt Ns a mass ha hmass
  have hι_meas : Measurable (asymTorusEmbedLiftIso L Ls Nt Ns a) :=
    asymTorusEmbedLiftIso_measurable L Ls Nt Ns a
  have h_eval : ∀ ω : Configuration (AsymLatticeField Nt Ns),
      (asymTorusEmbedLiftIso L Ls Nt Ns a ω) f = ω g :=
    asymTorusEmbedLiftIso_eval_eq L Ls Nt Ns a f
  -- Signed-split Layer A bound at the lattice level
  obtain ⟨hA_int, hA_bound⟩ :=
    asymInteracting_expMoment_of_signed Nt Ns P hP mass hmass a ha g
  -- Pushforward μ_int_T = (μ_int_L).map ι and integrability transfer
  have h_pushforward : μ_int_T =
      Measure.map (asymTorusEmbedLiftIso L Ls Nt Ns a) μ_int_L := rfl
  have h_F_meas :
      AEStronglyMeasurable (fun ω : Configuration (AsymTorusTestFunction L Ls) =>
        Real.exp (|ω f|)) μ_int_T :=
    ((configuration_eval_measurable f).abs.exp).aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · -- Integrability transfers across the pushforward
    rw [h_pushforward]
    rw [integrable_map_measure h_F_meas hι_meas.aemeasurable]
    refine hA_int.congr ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    simp [h_eval ω]
  · -- The main bound
    rw [h_pushforward]
    rw [integral_map hι_meas.aemeasurable h_F_meas]
    have hint_lattice_eq :
        ∫ ω, Real.exp (|(asymTorusEmbedLiftIso L Ls Nt Ns a ω) f|) ∂μ_int_L =
        ∫ ω, Real.exp (|ω g|) ∂μ_int_L := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun ω => ?_
      simp [h_eval ω]
    rw [hint_lattice_eq]
    -- Apply the signed-split bound, then Layer B2 at g₊ and g₋
    refine le_trans hA_bound ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.exp_le_exp.mpr
    have hBp := hC_B_bound L Nt Ns a ha hvolt hvols (fun x => max (g x) 0)
    have hBm := hC_B_bound L Nt Ns a ha hvolt hvols (fun x => max (-(g x)) 0)
    rw [mul_add]
    exact add_le_add hBp hBm

end Pphi2

end
