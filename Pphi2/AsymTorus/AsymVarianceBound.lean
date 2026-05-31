/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Asym cylinder Layer B1: interacting-vs-free variance bound (Phase 4)

The Layer B1 deliverable for the
`asymInteracting_expMoment_volume_uniform` discharge architecture:
**at fixed `(Nt, Ns, a, Lt)` with `Lt = Nt·a` fixed, the interacting
variance is bounded by a constant times the free Gaussian variance**:

```
∃ C(Lt, Ls), ∀ Nt Ns a f,  Var_int(⟨ω, f⟩) ≤ C(Lt, Ls) · Var_free(⟨ω, f⟩)
```

with the constant **uniform in `(Nt, Ns, a)` at fixed `(Lt, Ls)`**.
Layer B2's task is then to show `C(Lt, Ls)` stays bounded as `Lt → ∞`
at fixed `Ls`.

## Architectural note: this is a wrap-up, not a new derivation

The original scoping for Phase 4 anticipated a Källén-Lehmann variance
bound derived from the cylinder transfer-matrix mass gap (built in
Phases 1-3: `AsymL2Operator`, `AsymJentzsch`, `AsymPositivity`). That
route is mathematically valid but **not needed for Layer B1's
existential form**: a cheaper route already exists in pphi2 via the
density-transfer + Gaussian-4th-moment chain through the Nelson
exp-moment bound (now a theorem after UNIT 7's discharge of
`asymChaosCutoffDecomposition`).

Specifically: `asymTorusIso_interacting_second_moment_density_transfer`
(`Pphi2/AsymTorus/AsymContinuumLimit.lean:48`) already proves the bound
in essentially the form Layer B1 wants. This file wraps that theorem
in the explicit Layer-B1 packaging and documents the relationship.

The transfer-matrix spectral work in Phases 1-3 is **not deadweight** —
it is the foundation that Layer B2 (UV uniformity of `C(Lt, Ls)` as
`Lt → ∞`) will build on. The Källén-Lehmann derivation via spectral
decomposition gives a *tighter* and *uniform-in-Lt* constant; the
density-transfer route gives an *existential per-Lt* constant. For
B1's existential form, the cheaper route suffices; for B2's
Lt-uniform form, the transfer-matrix mass gap (from Phase 3) becomes
load-bearing.

## Main declarations

* `asymInteractingVariance_le_freeVariance_lattice` — Layer B1 in
  the most useful form: variance bound at the lattice level
  (`AsymLatticeField Nt Ns` / `latticeGaussianMeasureAsym`).
* `asymInteractingVariance_le_freeVariance_torus` — Layer B1 lifted
  to the torus test-function level via the `asymTorusEmbedLiftIso`
  pullback. This is the form that feeds Layer C.

## What remains for Layer C

To assemble the full
`asymInteracting_expMoment_volume_uniform` discharge:
1. **Layer A** (Newman MGF): supplied by the proposed `lee-yang`
   repo (Phase 1 of that project) + a pphi2 adapter. See
   `docs/asym-expmoment-discharge-via-lee-yang-vet-request.md` and
   `lee-yang/PLAN.md`.
2. **Layer B1**: this file (and the Phases 1-3 transfer-matrix
   infrastructure, which Layer B2 will need).
3. **Layer B2** (Lt-uniformity): chessboard / Fröhlich-Simon-Spencer
   route, deferred. Shares discharge path with the square's open
   `spectral_gap_uniform`.
4. **Layer C**: ~50 lines combining A + B2 once both are ready.

## References

* `docs/asym-l2-operator-port-scoping.md` — full Layer B1 scoping +
  rationale for the route choice.
* `docs/asym-interacting-expmoment-volume-uniform-discharge-plan.md`
  — overall axiom-discharge architecture.
-/

import Pphi2.AsymTorus.AsymPositivity
import Pphi2.AsymTorus.AsymContinuumLimit

noncomputable section

open MeasureTheory GaussianField

namespace Pphi2

variable (Lt Ls : ℝ) [hLt : Fact (0 < Lt)] [hLs : Fact (0 < Ls)]

/-- **Layer B1 variance bound at the lattice level** for the asym
cylinder construction.

For each `(Nt, Ns, a)` with `Nt · a = Lt`, `Ns · a = Ls`, and any test
function `g : AsymLatticeField Nt Ns`, the interacting second moment
is bounded by `C(Lt, Ls)` times the free Gaussian second moment,
**uniformly in `(Nt, Ns, a)` at fixed `(Lt, Ls)`**.

The constant `C(Lt, Ls) = 3 · √K(Lt, Ls)` where `K` is the uniform
Nelson exp-moment constant from `asymNelson_exponential_estimate_iso`.
Proof routes the existing infrastructure: Nelson exp-moment (now
unconditional after UNIT 7) → density-transfer (Cauchy-Schwarz) →
Gaussian 4th-moment bound. -/
theorem asymInteractingVariance_le_freeVariance_lattice
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
        (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
        ∀ (g : AsymLatticeField Nt Ns),
          ∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω g) ^ 2 ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ≤
          C * ∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω g) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
  obtain ⟨K, hK_pos, hK_bound⟩ :=
    asymNelson_exponential_estimate_iso P mass hmass Lt Ls
      (Fact.out (p := (0 < Lt))) (Fact.out (p := (0 < Ls)))
  refine ⟨3 * Real.sqrt K, mul_pos (by norm_num : (0 : ℝ) < 3)
    (Real.sqrt_pos_of_pos hK_pos), ?_⟩
  intro Nt Ns _ _ a ha hvolt hvols g
  set μ_int := interactingLatticeMeasureAsym Nt Ns P a mass ha hmass
  set μ_GFF := latticeGaussianMeasureAsym Nt Ns a mass ha hmass
  set T := latticeCovarianceAsymGJ Nt Ns a mass ha hmass
  have hμ_eq : μ_GFF = GaussianField.measure T := rfl
  have hZ_ge_one := partitionFunctionAsym_ge_one Nt Ns P a mass ha hmass
  have hF_nn : ∀ ω : Configuration (AsymLatticeField Nt Ns), 0 ≤ (ω g) ^ 2 :=
    fun ω => sq_nonneg _
  have hF_meas : AEStronglyMeasurable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      (ω g) ^ 2) μ_GFF :=
    ((configuration_eval_measurable g).pow_const 2).aestronglyMeasurable
  have hF_sq_int :
      Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) => ((ω g) ^ 2) ^ 2) μ_GFF := by
    have h4 : MemLp (fun ω : Configuration (AsymLatticeField Nt Ns) => ω g) 4 μ_GFF := by
      exact_mod_cast pairing_memLp T g 4
    have hmem := h4.norm_rpow (p := (4 : ENNReal))
      (by norm_num : (4 : ENNReal) ≠ 0) (by norm_num : (4 : ENNReal) ≠ ⊤)
    rw [memLp_one_iff_integrable] at hmem
    have h_int : Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
        ‖ω g‖ ^ (4 : ℕ)) μ_GFF := by
      refine hmem.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp [ENNReal.toReal_ofNat]
    exact h_int.congr (Filter.Eventually.of_forall fun ω => by
      dsimp only
      rw [Real.norm_eq_abs]
      conv_rhs => rw [show ω g ^ 2 = |ω g| ^ 2 from (sq_abs _).symm]
      ring)
  have h_dt := density_transfer_bound_iso Nt Ns P a mass ha hmass K hK_pos
    (hK_bound Nt Ns a ha hvolt hvols)
    hZ_ge_one (fun ω => (ω g) ^ 2) hF_nn hF_meas hF_sq_int
  have h_int_rpow_eq :
      ∫ ω, (fun ω => (ω g) ^ 2) ω ^ (2 : ℝ) ∂μ_GFF =
        ∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF := by
    congr 1; ext ω; exact Real.rpow_natCast ((ω g) ^ 2) 2
  have h_second_nn : 0 ≤ ∫ ω, (ω g) ^ 2 ∂μ_GFF :=
    integral_nonneg fun ω => sq_nonneg _
  have h_fourth_le : ∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF ≤
      9 * (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 2 := by
    have h_eq4 : ∀ ω : Configuration (AsymLatticeField Nt Ns),
        ((ω g) ^ 2) ^ 2 = |ω g| ^ 4 := by
      intro ω; rw [show ω g ^ 2 = |ω g| ^ 2 from (sq_abs _).symm]; ring
    simp_rw [h_eq4]
    have h_hyper := gaussian_hypercontractive T g 1 4
      (by norm_num : (2 : ℝ) ≤ 4) 2 (by norm_num : 1 ≤ 2)
      (by norm_num : (4 : ℝ) = 2 * ↑2)
    have h_lhs_eq : ∫ ω, |ω g| ^ 4 ∂μ_GFF =
        ∫ ω, |ω g| ^ ((4 : ℝ) * ↑(1 : ℕ)) ∂(GaussianField.measure T) := by
      rw [hμ_eq]; congr 1; ext ω
      simp only [Nat.cast_one, mul_one]; exact (Real.rpow_natCast _ 4).symm
    rw [h_lhs_eq]
    have h_coeff : ((4 : ℝ) - 1) ^ ((4 : ℝ) * ↑(1 : ℕ) / 2) = 9 := by
      simp only [Nat.cast_one, mul_one]
      rw [show (4 : ℝ) / 2 = ↑(2 : ℕ) from by norm_num, Real.rpow_natCast]; norm_num
    have h_exp_eq' : (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((4 : ℝ) / 2) =
        (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 2 := by
      rw [show (4 : ℝ) / 2 = ↑(2 : ℕ) from by norm_num, Real.rpow_natCast]
    have h_int_2_eq : ∫ ω, |ω g| ^ (2 * 1) ∂(GaussianField.measure T) =
        ∫ ω, (ω g) ^ 2 ∂μ_GFF := by
      rw [hμ_eq]; congr 1; ext ω; simp [sq_abs]
    have h_hyper' : ∫ ω, |ω g| ^ ((4 : ℝ) * ↑(1 : ℕ)) ∂(GaussianField.measure T) ≤
        ((4 : ℝ) - 1) ^ ((4 : ℝ) * ↑(1 : ℕ) / 2) *
        (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((4 : ℝ) / 2) := by
      have := h_hyper; rwa [h_int_2_eq] at this
    calc ∫ ω, |ω g| ^ ((4 : ℝ) * ↑(1 : ℕ)) ∂(GaussianField.measure T)
        ≤ ((4 : ℝ) - 1) ^ ((4 : ℝ) * ↑(1 : ℕ) / 2) *
          (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((4 : ℝ) / 2) := h_hyper'
      _ = 9 * (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 2 := by rw [h_coeff, h_exp_eq']
  have h_fourth_nn : (0 : ℝ) ≤ ∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF :=
    integral_nonneg fun ω => by positivity
  have h_4th_bound : (∫ ω, (fun ω => (ω g) ^ 2) ω ^ (2 : ℝ) ∂μ_GFF) ^ (1 / 2 : ℝ) ≤
      3 * ∫ ω, (ω g) ^ 2 ∂μ_GFF := by
    rw [h_int_rpow_eq]
    calc (∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF) ^ (1 / 2 : ℝ)
        ≤ (9 * (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 2) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow h_fourth_nn h_fourth_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
      _ = 3 * ∫ ω, (ω g) ^ 2 ∂μ_GFF := by
          rw [show 9 * (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 2 =
            (3 * ∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 2 from by ring]
          rw [← Real.sqrt_eq_rpow, Real.sqrt_sq
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) h_second_nn)]
  have hK_sqrt : K ^ (1 / 2 : ℝ) = Real.sqrt K := (Real.sqrt_eq_rpow K).symm
  calc ∫ ω, (ω g) ^ 2 ∂μ_int
      ≤ K ^ (1 / 2 : ℝ) * (∫ ω, (fun ω => (ω g) ^ 2) ω ^ (2 : ℝ) ∂μ_GFF) ^ (1 / 2 : ℝ) := h_dt
    _ ≤ K ^ (1 / 2 : ℝ) * (3 * ∫ ω, (ω g) ^ 2 ∂μ_GFF) :=
        mul_le_mul_of_nonneg_left h_4th_bound (Real.rpow_nonneg hK_pos.le _)
    _ = Real.sqrt K * (3 * ∫ ω, (ω g) ^ 2 ∂μ_GFF) := by rw [hK_sqrt]
    _ = 3 * Real.sqrt K * ∫ ω, (ω g) ^ 2 ∂μ_GFF := by ring

/-- **Layer B1 variance bound at the torus test-function level**. The
form the eventual Layer C assembly will consume. Wrapper of
`asymTorusIso_interacting_second_moment_density_transfer` (in
`AsymContinuumLimit.lean`) restated as a Layer-B1 variance bound. -/
theorem asymInteractingVariance_le_freeVariance_torus
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : AsymTorusTestFunction Lt Ls)
        (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
        (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
        ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
          (ω f) ^ 2 ∂(asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) ≤
        C * ∫ ω : Configuration (AsymLatticeField Nt Ns),
          (ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ^ 2
            ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) :=
  asymTorusIso_interacting_second_moment_density_transfer Lt Ls P mass hmass

end Pphi2

end
