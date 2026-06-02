/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Discharge of `asymInteracting_expMoment_volume_uniform` from two upstream-input axioms

**Architecture-closing file.** Defines the two upstream-input axioms
that the proposed `lee-yang` and `reflection-positivity` workstreams
will discharge, and proves the Layer C assembly theorem that combines
them into the discharge of the project-level axiom
`asymInteracting_expMoment_volume_uniform`.

## What this file does

States two clean, individually-vettable axioms:

* **`asymInteracting_mgf_gaussianDominated`** — Layer A: Newman's MGF
  Gaussian-domination of the lattice interacting measure. This is the
  pphi2-side translation of what the proposed `lee-yang` repo will
  produce (Newman MGF inequality applied to the asym Wick interacting
  measure via `evenPolynomialWick_isLeeYang` + iterated Asano on the
  lattice graph + the marginal-projection lemma).

* **`asymInteractingVariance_le_freeVariance_Lt_uniform`** — Layer B2:
  Lt-uniform variance bound. The chessboard / FSS / cylinder-mass-gap
  refinement of the per-Lt variance bound Layer B1 already gave (in
  `AsymVarianceBound.lean`). This is the pphi2-side translation of
  what the proposed `reflection-positivity` repo + the Phases 1-3
  cylinder transfer-matrix infrastructure will produce.

And proves the **Layer C assembly theorem**:

* **`asymInteracting_expMoment_volume_uniform_proof`** — combines
  Layer A + Layer B2 + the joint-↔-torus pushforward to produce the
  full existential statement of the original project axiom.

This file is the **structural close of the discharge architecture**:
once the two upstream axioms are discharged by their respective
workstreams, the original project axiom drops automatically with no
additional pphi2 work needed.

## Why state these here as pphi2 axioms?

Per CLAUDE.md axiom protocol, this is a "vetted provable theorem with
a vetted discharge plan." Defining the upstream inputs as pphi2-internal
axioms lets us:

1. Verify the Layer C assembly closes the discharge **before**
   investing weeks in `lee-yang` Phase 1 or the chessboard workstream.
2. Provide a clean interface contract: the upstream repos can be
   developed independently, with this file as the consumer spec.
3. Use deep-think vetting to catch architectural gaps now, not later.

**Net axiom-count impact**: the original
`asymInteracting_expMoment_volume_uniform` axiom is replaced by the
two new axioms (Layer A + Layer B2), net **+1 axiom raw** for
clearer factorization. Each new axiom is individually shallower than
the original (Newman MGF is a textbook result; chessboard mass-gap
variance bound is the standard FSS argument). Both are independently
discharged by their respective upstream workstreams.

## Status

* Layer A axiom (`asymInteracting_mgf_gaussianDominated`): vetted
  2026-06-02 (deep-think, see `docs/asym-expmoment-discharge-via-lee-yang-vet-request.md`
  for the architecture vet from 2026-05-31).
* Layer B2 axiom (`asymInteractingVariance_le_freeVariance_Lt_uniform`):
  vetted 2026-06-02 (deep-think).
* Layer C theorem: proved here.

## References

* `docs/asym-interacting-expmoment-volume-uniform-discharge-plan.md`
  — full discharge architecture.
* `docs/asym-expmoment-discharge-via-lee-yang-vet-request.md`
  — deep-think vet of Layer A architecture.
* `docs/asym-l2-operator-port-scoping.md` — Layer B1 (Phases 1-4 done).
* `lee-yang/PLAN.md` — Layer A's upstream home.
-/

import Pphi2.AsymTorus.AsymVarianceBound

noncomputable section

open MeasureTheory GaussianField

namespace Pphi2

/-! ## Layer A axiom (lee-yang adapter output) -/

/-- **Layer A: Newman's MGF Gaussian-domination of the asym interacting measure**.

For every `(Nt, Ns, a, P, mass)` with the standard positivity constraints, the
moment-generating function of the interacting measure
`interactingLatticeMeasureAsym` for a linear functional `⟨ω, f⟩` is Gaussian-
dominated by `2 · exp((1/2) · Var_int(⟨ω, f⟩))`. The `K = 2` constant is the
universal `|·|`-form of Newman's inequality: `e^|x| ≤ e^x + e^{-x}` plus the
two-sided Newman MGF bound at `t = ±1`.

**Mathematical content** (Newman 1975, Comm. Math. Phys. 41, Thm 3): if the
joint distribution of `(ω(x))_{x ∈ Λ}` under the interacting measure lies in
the **Lee-Yang class** (characteristic function has zeros confined to the
imaginary axis), then for any real linear functional `S = ⟨ω, f⟩`,
`E[e^{tS}] ≤ exp(t² · Var(S) / 2)`. The hypothesis is satisfied for the
P(φ)₂ Wick-ordered interacting measure on the asym lattice via the
Griffiths-Simon Asano-Ising approximation of the single-site Wick measure
`exp(-a²:P(φ):_{wickConstantAsym})` combined with iterated Asano on the
nearest-neighbour coupling structure (which is ferromagnetic for even monic
P with positive leading coefficient).

**Upstream discharge plan**: this is the pphi2-side instantiation that the
proposed `lee-yang` repo's Phase 1 (`Measure/Newman.lean` and
`Measure/GriffithsSimon.lean`) plus a pphi2 adapter file
(`AsymInteractingLeeYang.lean`, ~200-400 lines) will produce. See
`docs/asym-expmoment-discharge-via-lee-yang-vet-request.md` for the full
deep-think-vetted plan (2026-05-31).

**Reference**: C. M. Newman, *Inequalities for Ising models and field
theories which obey the Lee-Yang theorem*, Comm. Math. Phys. 41 (1975), 1-9,
Theorem 3. T. D. Lee and C. N. Yang, *Statistical theory of equations of
state and phase transitions II*, Phys. Rev. 87 (1952), 410-419.

✅ Vetted: deep-think-gemini (2026-06-02) — confirmed the Newman MGF
inequality for Lee-Yang interacting measures with the K=2 / Var_int form;
the Griffiths-Simon-Asano discharge route is the standard one (Simon §VIII,
Glimm-Jaffe Ch. 4). -/
axiom asymInteracting_mgf_gaussianDominated
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a)
    (f : AsymLatticeField Nt Ns) :
    Integrable (fun ω => Real.exp (|ω f|))
      (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ∧
    ∫ ω, Real.exp (|ω f|)
      ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ≤
    2 * Real.exp ((1/2) *
      ∫ ω, (ω f) ^ 2
        ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass))

/-! ## Layer B2 axiom (chessboard / reflection-positivity output) -/

/-- **Layer B2: `Lt`-uniform interacting-vs-free variance bound**.

There exists a single constant `C > 0` such that, for **every** time
period `Lt` (with `Ls` fixed), every refinement `(Nt, Ns, a)` with
`Nt · a = Lt`, `Ns · a = Ls`, and every test function
`f : AsymTorusTestFunction Lt Ls`,
`∫(ω f)² dμ_int ≤ C · ∫(ω g)² dμ_free` where
`g = asymLatticeTestFnIso Lt Ls Nt Ns a f`.

**Comparison to the existing Layer B1 bound**:
`asymTorusIso_interacting_second_moment_density_transfer`
(`Pphi2/AsymTorus/AsymContinuumLimit.lean:48`) and the Layer B1 wrapper
`asymInteractingVariance_le_freeVariance_torus`
(`Pphi2/AsymTorus/AsymVarianceBound.lean`) give the same bound but with
`C = C(Lt, Ls)` *depending on `Lt`* (because the Nelson exp-moment
constant `K(Lt, Ls)` from `asymNelson_exponential_estimate_iso` depends
on `Lt`). Layer B2 is the **uniformity-in-`Lt`** refinement: the bound
holds with a single constant uniformly as `Lt → ∞` at fixed `Ls`.

**Mathematical content**: the cylinder mass gap (which IS unconditional
in the cylinder regime — `Ls` fixed, `Lt → ∞` is a 1D thermodynamic
limit with isolated transfer-matrix top eigenvalue by infinite-dim
Perron-Frobenius, see `Pphi2/AsymTorus/AsymPositivity.lean`) controls
the interacting susceptibility via the lattice Källén-Lehmann sum
rule. The uniformity-in-`Lt` then follows from chessboard / FSS
(Fröhlich-Simon-Spencer) estimates that bound the interacting
2-point function by the free 2-point function via reflection
positivity, without needing a full spatial cluster expansion.

**Upstream discharge plan**: a new `reflection-positivity` repo
(scoped 2026-05-31) will provide the abstract chessboard / multiple-
reflection algebra; a pphi2 adapter then specializes to the asym
lattice's reflection structure and produces this bound. The cylinder
transfer-matrix infrastructure (`AsymL2Operator`, `AsymJentzsch`,
`AsymPositivity`) is the foundation. See
`docs/asym-l2-operator-port-scoping.md` for the Layer B2 sub-plan
and the noted "shares discharge path with the square's open
`spectral_gap_uniform`" connection.

**Reference**: Glimm-Jaffe Ch. 6, 10, 19 (chessboard estimates);
Fröhlich-Simon-Spencer (1976), "Phase Transitions and Reflection
Positivity I", Comm. Math. Phys. 50, 79-95 (the original FSS bound);
Simon, *The P(φ)₂ Euclidean QFT* (1974) Ch. V.

✅ Vetted: deep-think-gemini (2026-06-02) — confirmed the Lt-uniform
variance bound from chessboard + cylinder mass gap (Källén-Lehmann
sum rule) is the standard result; the cylinder shortcut (no full 2D
cluster expansion needed) is mathematically sound and computationally
tractable. -/
axiom asymInteractingVariance_le_freeVariance_Lt_uniform
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Ls : ℝ) [Fact (0 < Ls)] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Lt : ℝ) [Fact (0 < Lt)]
        (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
        (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
        ∀ (f : AsymTorusTestFunction Lt Ls),
          ∫ ω : Configuration (AsymTorusTestFunction Lt Ls), (ω f) ^ 2
            ∂(asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) ≤
          C * ∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ^ 2
              ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)

/-! ## Layer C: assembly theorem -/

/-- **Layer C assembly**: combining Layer A (Newman MGF
Gaussian-domination on the lattice) + Layer B2 (`Lt`-uniform
interacting-vs-free variance bound) gives the discharge of
`asymInteracting_expMoment_volume_uniform`.

The assembly is purely structural:
1. For a torus test function `f`, push the torus integral back to the
   lattice via `asymTorusInteractingMeasureIso = (μ_int^{lattice}).map ι`
   where `ι = asymTorusEmbedLiftIso`.
2. Use `(ι ω)(f) = ω(asymLatticeTestFnIso f)` to swap the torus pairing
   for the lattice pairing.
3. Apply Layer A on the lattice: `∫ e^{|⟨ω,g⟩|} dμ_int^{lattice} ≤ 2 ·
   exp((1/2) · Var_int(⟨ω,g⟩))` where `g = asymLatticeTestFnIso f`.
4. The `Var_int(⟨ω,g⟩)` at the torus level pushes back to
   `Var_int(⟨ω_lattice, g⟩)` (same integral by the pushforward).
5. Apply Layer B2: `Var_int(⟨ω,g⟩) ≤ C_B · Var_free(⟨ω,g⟩)` uniformly
   in `Lt`.
6. Combine: `≤ 2 · exp((C_B/2) · Var_free(⟨ω,g⟩))`. Set `K = 2`,
   `C = C_B / 2`.

The constant `C_B` is `Lt`-uniform by Layer B2, so the final
`K = 2`, `C = C_B / 2` is `Lt`-uniform — exactly what the original
axiom asks for. -/
theorem asymInteracting_expMoment_volume_uniform_proof
    (Ls : ℝ) [hLs : Fact (0 < Ls)]
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (L : ℝ) [Fact (0 < L)] (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
        (a : ℝ) (ha : 0 < a),
        (Nt : ℝ) * a = L → (Ns : ℝ) * a = Ls → ∀ f : AsymTorusTestFunction L Ls,
        Integrable (fun ω : Configuration (AsymTorusTestFunction L Ls) =>
            Real.exp (|ω f|))
          (asymTorusInteractingMeasureIso L Ls Nt Ns a P mass ha hmass) ∧
        ∫ ω : Configuration (AsymTorusTestFunction L Ls), Real.exp (|ω f|)
          ∂(asymTorusInteractingMeasureIso L Ls Nt Ns a P mass ha hmass) ≤
        K * Real.exp (C *
          ∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω (asymLatticeTestFnIso L Ls Nt Ns a f)) ^ 2
            ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) := by
  obtain ⟨C_B, hC_B_pos, hC_B_bound⟩ :=
    asymInteractingVariance_le_freeVariance_Lt_uniform P mass hmass Ls
  refine ⟨2, C_B / 2, by norm_num, by linarith, ?_⟩
  intro L _hL Nt Ns _ _ a ha hvolt hvols f
  set g := asymLatticeTestFnIso L Ls Nt Ns a f
  set μ_int_T := asymTorusInteractingMeasureIso L Ls Nt Ns a P mass ha hmass
  set μ_int_L := interactingLatticeMeasureAsym Nt Ns P a mass ha hmass
  set μ_free := latticeGaussianMeasureAsym Nt Ns a mass ha hmass
  have hι : (asymTorusEmbedLiftIso L Ls Nt Ns a : _ → _) = _ := rfl
  have hι_meas : Measurable (asymTorusEmbedLiftIso L Ls Nt Ns a) :=
    asymTorusEmbedLiftIso_measurable L Ls Nt Ns a
  have h_eval : ∀ ω : Configuration (AsymLatticeField Nt Ns),
      (asymTorusEmbedLiftIso L Ls Nt Ns a ω) f = ω g :=
    asymTorusEmbedLiftIso_eval_eq L Ls Nt Ns a f
  obtain ⟨hA_int, hA_bound⟩ :=
    asymInteracting_mgf_gaussianDominated P mass hmass Nt Ns a ha g
  -- Pushforward μ_int_T = (μ_int_L).map ι and integrability transfer
  have h_pushforward : μ_int_T =
      Measure.map (asymTorusEmbedLiftIso L Ls Nt Ns a) μ_int_L := rfl
  have h_F_meas :
      AEStronglyMeasurable (fun ω : Configuration (AsymTorusTestFunction L Ls) =>
        Real.exp (|ω f|)) μ_int_T :=
    ((configuration_eval_measurable f).abs.exp).aestronglyMeasurable
  have h_F_sq_meas :
      AEStronglyMeasurable (fun ω : Configuration (AsymTorusTestFunction L Ls) =>
        (ω f) ^ 2) μ_int_T :=
    ((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable
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
    -- Apply Layer A bound: ∫ exp|ωg| dμ_int ≤ 2 · exp((1/2) · Var_int(⟨ω,g⟩))
    refine le_trans hA_bound ?_
    -- Now: 2 · exp((1/2) · ∫(ωg)² dμ_int_L) ≤ 2 · exp((C_B/2) · ∫(ωg)² dμ_free)
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.exp_le_exp.mpr
    -- Need: (1/2) · ∫(ωg)² dμ_int_L ≤ (C_B/2) · ∫(ωg)² dμ_free
    -- Step: pushforward identity for the lattice 2nd moment
    have h_var_pushforward :
        ∫ ω : Configuration (AsymLatticeField Nt Ns), (ω g) ^ 2 ∂μ_int_L =
        ∫ ω : Configuration (AsymTorusTestFunction L Ls), (ω f) ^ 2 ∂μ_int_T := by
      rw [h_pushforward, integral_map hι_meas.aemeasurable h_F_sq_meas]
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun ω => ?_
      simp [h_eval ω]
    rw [h_var_pushforward]
    -- Now: (1/2) · ∫(ωf)² dμ_int_T ≤ (C_B/2) · ∫(ωg)² dμ_free
    have hB := hC_B_bound L Nt Ns a ha hvolt hvols f
    nlinarith [hB,
      integral_nonneg (μ := μ_free)
        (f := fun ω : Configuration (AsymLatticeField Nt Ns) => (ω g) ^ 2)
        (fun ω => sq_nonneg _)]

end Pphi2

end
