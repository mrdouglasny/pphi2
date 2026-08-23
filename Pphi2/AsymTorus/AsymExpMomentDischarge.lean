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
  Gaussian-domination of the lattice interacting measure, restricted to
  quartic `P` and sitewise-nonnegative test functions. The former all-`P`
  contract fails for an explicit one-site sextic family recorded in
  `AXIOM_AUDIT.md` (2026-08-22). Signed `f` is recovered by the `f₊`/`f₋`
  split in `AsymSignedSplit.lean`.

* **`asymInteractingVariance_le_freeVariance_lattice_Lt_uniform`** —
  Layer B2 Route-A lattice output: the Lt-uniform interacting/free
  variance bound on the lattice. The torus statement
  `asymInteractingVariance_le_freeVariance_Lt_uniform` is now a theorem
  obtained from this lattice output by the pushforward embedding.

The **Layer C assembly theorem**
`asymInteracting_expMoment_volume_uniform_proof` — combining Layer A +
Layer B2 + the joint-↔-torus pushforward — lives in
`Pphi2/AsymTorus/AsymSignedSplit.lean` (moved 2026-07-13 with the sign
restriction of Layer A; the assembly consumes the signed-split lemma and
its seminorm is the split form `C · (Var_free(f₊) + Var_free(f₋))`).

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
  for the architecture vet from 2026-05-31); **sign-restricted 2026-07-13**
  after the Gemini + Codex vet of 2026-07-12 found the unrestricted
  test-function quantifier false, then **quartic-restricted 2026-08-22**
  after an explicit one-site sextic counterexample to the all-`P` contract
  (see `AXIOM_AUDIT.md`).
* Layer B2 Route-A lattice axiom
  (`asymInteractingVariance_le_freeVariance_lattice_Lt_uniform`):
  factored 2026-06-23 as the remaining lattice assembly input.
* Layer C theorem: proved in `AsymSignedSplit.lean` (split-seminorm form).

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

For quartic `P` and a sitewise nonnegative `f`, the moment-generating function
of `interactingLatticeMeasureAsym` at `⟨ω, f⟩` is bounded by
`2 · exp((1/2) · Var_int(⟨ω, f⟩))`. The `K = 2` constant comes from
`e^|x| ≤ e^x + e^{-x}` and the two one-sided MGF estimates at `t = ±1`.

**Mathematical content** (Newman 1975, Comm. Math. Phys. 41, Thm 3): if the
joint distribution of `(ω(x))_{x ∈ Λ}` under the interacting measure lies in
the **Lee-Yang class**, then for a same-sign linear functional `S = ⟨ω, f⟩`,
`E[e^{tS}] ≤ exp(t² · Var(S) / 2)`. The hypothesis is satisfied for the
quartic Wick-ordered lattice model only after its single-site Lee-Yang input
and the ferromagnetic closure have been supplied. This declaration keeps that
mathematical input explicit.

**Reference**: C. M. Newman, *Inequalities for Ising models and field
theories which obey the Lee-Yang theorem*, Comm. Math. Phys. 41 (1975), 1-9,
Theorem 3. T. D. Lee and C. N. Yang, *Statistical theory of equations of
state and phase transitions II*, Phys. Rev. 87 (1952), 410-419.

The cited Newman theorem supplies the conditional MGF inequality once the
Lee-Yang hypothesis is available.

**SIGN RESTRICTION (2026-07-12/13)**: Newman domination requires same-sign
coefficients — the unrestricted form is FALSE (2-spin mixed-sign
counterexample; Lebowitz-κ₄ mechanism; n-pair amplification kills the K=2
form). Hence the hypothesis `hf : ∀ x, 0 ≤ f x` (sitewise nonnegative).
Signed `f` is recovered via the `f₊`/`f₋` split (see
`asymInteracting_expMoment_of_signed` in `AsymSignedSplit.lean`).
Vet: Gemini 3.1-pro + Codex GPT-5.5, 2026-07-12 — `AXIOM_AUDIT.md` entry
(restated 2026-07-13).

**DEGREE RESTRICTION (2026-08-22)**: the sitewise sign condition does not
extend the contract to general even `P`. The explicit one-site sextic family
in `AXIOM_AUDIT.md` converges to
`(δ_{-1} + 16δ_0 + δ_1) / 18` and violates this precise `K = 2` bound at
the nonnegative source `f(*) = 9`. The live axiom therefore requires
`hP : P.n = 4`. -/
axiom asymInteracting_mgf_gaussianDominated
    (P : InteractionPolynomial) (hP : P.n = 4) (mass : ℝ) (hmass : 0 < mass)
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a)
    (f : AsymLatticeField Nt Ns) (hf : ∀ x, 0 ≤ f x) :
    Integrable (fun ω => Real.exp (|ω f|))
      (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ∧
    ∫ ω, Real.exp (|ω f|)
      ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ≤
    2 * Real.exp ((1/2) *
      ∫ ω, (ω f) ^ 2
        ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass))

/-! ## Layer B2 axiom (chessboard / reflection-positivity output) -/

/-- **Layer B2 Route-A lattice output: `Lt`-uniform interacting-vs-free
variance bound on the lattice**.

There exists a single constant `C > 0` such that, for **every** time
period `Lt` (with `Ls` fixed), every refinement `(Nt, Ns, a)` with
`Nt · a = Lt`, `Ns · a = Ls`, and every lattice test function
`G : AsymLatticeField Nt Ns`,
`∫(ω G)² dμ_int ≤ C · ∫(ω G)² dμ_free`.

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
tractable.

**Discharge update (2026-06-02; see `docs/layer-B2-discharge-plan.md`).**
The "chessboard / FSS … shares discharge path with the square's open
`spectral_gap_uniform`" framing above is SUPERSEDED: at fixed `Ls` the
cylinder mass gap is uniform via compact-resolvent convergence
(`T_a → e^{−aH(Ls)}`, Simon Ch. VI), so **no chessboard is needed** (FSS is
only for the thermodynamic `Ls → ∞` limit; see
`reflection-positivity/docs/B2_UNIFORMITY_QUESTION.md`). The transfer-matrix
spectral gap is now **proved**: `asymGappedTransfer'` /
`susceptibility_le` (via `AsymGappedTransfer.lean` + `AsymSpectralGap.lean`
+ the `reflection-positivity` dep). The remaining discharge is the 3-piece
plan: (1) the interacting Källén-Lehmann/Feynman-Kac representation
(the un-formalized measure↔operator bridge — a more-fundamental axiom-to-be);
(2) the free representation (provable, Gaussian); (3) the int/free ratio,
whose `1/a` cancellation is essential — a naive `Var_int ≤ 1/(1−γ)·Var_free`
is `a`-non-uniform and WRONG.

**Piece-5 factoring note (2026-06-23).** The former torus-level axiom
`asymInteractingVariance_le_freeVariance_Lt_uniform` is discharged below
from this lattice statement plus the already-proved pushforward identity
`asymTorusInteractingMeasureIso = (interactingLatticeMeasureAsym).map
asymTorusEmbedLiftIso` and pairing identity
`(asymTorusEmbedLiftIso ω) f = ω (asymLatticeTestFnIso f)`. This keeps the
remaining Route-A obligation at the lattice level, where Piece 4
`interacting_second_moment_bound_to_lattice_free_covariance` is stated.

MIGRATION NOTE (2026-07-13): the thresholded form is now a THEOREM
(`asymInteractingVariance_le_freeVariance_torus_thresholded` /
`asymInteractingVariance_le_freeVariance_lattice_thresholded`, 5 vetted axioms);
this all-(Lt,a) axiom remains only for the legacy Layer-C wiring and is
over-broad at small Lt / coarse a (true but unproved there) — consumers should
migrate to the thresholded form (planning/b2-stageB-holes-spec.md §C4 design). -/
axiom asymInteractingVariance_le_freeVariance_lattice_Lt_uniform
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Ls : ℝ) [Fact (0 < Ls)] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Lt : ℝ) [Fact (0 < Lt)]
        (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
        (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
        ∀ (G : AsymLatticeField Nt Ns),
          ∫ ω : Configuration (AsymLatticeField Nt Ns), (ω G) ^ 2
            ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ≤
          C * ∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω G) ^ 2
              ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)

/-- **Layer B2 torus assembly theorem.** The torus variance bound follows from
the lattice Route-A output by pushing the torus interacting measure back along
`asymTorusEmbedLiftIso` and rewriting the torus pairing as the lattice pairing
against `asymLatticeTestFnIso`. -/
theorem asymInteractingVariance_le_freeVariance_Lt_uniform
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
              ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
  obtain ⟨C, hC_pos, hC_bound⟩ :=
    asymInteractingVariance_le_freeVariance_lattice_Lt_uniform P mass hmass Ls
  refine ⟨C, hC_pos, ?_⟩
  intro Lt _hLt Nt Ns _ _ a ha hvolt hvols f
  set g := asymLatticeTestFnIso Lt Ls Nt Ns a f
  set μ_int_T := asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass
  set μ_int_L := interactingLatticeMeasureAsym Nt Ns P a mass ha hmass
  have hι_meas : Measurable (asymTorusEmbedLiftIso Lt Ls Nt Ns a) :=
    asymTorusEmbedLiftIso_measurable Lt Ls Nt Ns a
  have h_eval : ∀ ω : Configuration (AsymLatticeField Nt Ns),
      (asymTorusEmbedLiftIso Lt Ls Nt Ns a ω) f = ω g :=
    asymTorusEmbedLiftIso_eval_eq Lt Ls Nt Ns a f
  have h_pushforward : μ_int_T =
      Measure.map (asymTorusEmbedLiftIso Lt Ls Nt Ns a) μ_int_L := rfl
  have h_F_sq_meas :
      AEStronglyMeasurable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
        (ω f) ^ 2) μ_int_T :=
    ((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable
  rw [h_pushforward]
  rw [integral_map hι_meas.aemeasurable h_F_sq_meas]
  have h_integrand :
      ∫ ω : Configuration (AsymLatticeField Nt Ns),
          (asymTorusEmbedLiftIso Lt Ls Nt Ns a ω f) ^ 2 ∂μ_int_L =
        ∫ ω : Configuration (AsymLatticeField Nt Ns), (ω g) ^ 2 ∂μ_int_L := by
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun ω => ?_
    simpa using congrArg (fun x : ℝ => x ^ 2) (h_eval ω)
  rw [h_integrand]
  exact hC_bound Lt Nt Ns a ha hvolt hvols g

/-! ## Layer C: assembly theorem

**Moved (2026-07-13).** The Layer C assembly theorem
`asymInteracting_expMoment_volume_uniform_proof` now lives in
`Pphi2/AsymTorus/AsymSignedSplit.lean`: after the sign restriction of the
Layer A axiom (see its docstring above), signed test functions are recovered
via the `f = f₊ − f₋` split lemma `asymInteracting_expMoment_of_signed`
(that file), and the assembly's free-variance seminorm is stated in the
split form `C · (Var_free(f₊) + Var_free(f₋))`. -/

end Pphi2

end
