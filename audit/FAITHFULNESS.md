# pphi2 — faithfulness map

*Informal↔formal correspondence for the headline objects and theorems.*

Faithfulness is a **validation** layer: a sorry-free, axiom-free declaration can
still be the wrong statement. This file records, for each headline name, the
informal definition / theorem it is intended to match, the formal Lean
declaration, and any divergences a reader should know about.

For the conventional model see
[`math-commons/formalization-assurance/VERIFICATION_VALIDATION.md`](https://github.com/math-commons/formalization-assurance/blob/main/VERIFICATION_VALIDATION.md).

---

## OS axioms (the target spec)

**Informal source.** Osterwalder–Schrader, *Axioms for Euclidean Green's
functions*, Comm. Math. Phys. 31 (1973) 83–112 and 42 (1975) 281–305. The
canonical formulation:

> A real Borel probability measure `μ` on `S'(ℝᵈ)` satisfies the **OS axioms**
> if its generating functional `S[f] := ∫ e^{i⟨ω,f⟩} dμ(ω)` is:
> **(OS0)** analytic (entire in real-vector directions, with the factorial growth
> bound); **(OS1)** regular (Schwinger functions exist and are tempered
> distributions); **(OS2)** Euclidean covariant (`E(d)`-invariant Schwinger
> functions); **(OS3)** reflection-positive (Schwinger functions on positive-time
> test functions yield PSD matrices); **(OS4)** translation-clustering / ergodic;
> with the technical regularity / boundedness needed to apply OS reconstruction.

**Formal.** `Pphi2.SatisfiesFullOS μ` in `Pphi2/OSAxioms.lean`, bundling
`OS0`, `OS1`, `OS2`, `OS3`, `OS4` as separate predicates on the measure.

**Divergences.** None substantive in the OS predicates themselves. The
**reconstruction step** (OS axioms ⟹ Wightman QFT in Minkowski) is **not**
formalized here — that's the separate
[`OSreconstruction`](https://github.com/mrdouglasny/OSreconstruction) project.
This repo formalizes only the *Euclidean side*.

---

## Headline existence theorem

**Informal claim** (Glimm–Jaffe Ch. 8–11; Simon Ch. V–VIII): for any
P(φ) polynomial of even degree with positive leading coefficient and any
positive bare mass, there exists a probability measure on `S'(ℝ²)` that
satisfies the OS axioms — the constructive Euclidean P(Φ)₂ measure obtained
as the continuum limit of the lattice action with Wick-ordered interaction.

**Formal.** `Pphi2.pphi2_existence` (`Pphi2/Main.lean:110`):

```lean
theorem pphi2_existence (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ μ : Measure (Configuration (TestFunction 2 ℝ)) (_ : IsProbabilityMeasure μ),
      SatisfiesFullOS μ
```

**Kernel certificate** (from `audit/axiom-report.txt`):
- depends on `propext`, `Classical.choice`, `Quot.sound` (Lean kernel);
- depends on the project axioms `canonical_continuumMeasure_cf_tendsto`,
  `continuum_exponential_clustering`, `continuum_exponential_moment_bound`,
  `rotation_cf_defect_polylog_bound` (4 of the 17 architectural axioms).
  The other 13 architectural axioms are dormant for this statement —
  load-bearing only for stronger or sibling headlines (cylinder OS3,
  non-Gaussianity, two-point nondegeneracy).

**Divergences from the informal claim:**

1. **Coherence gap A (`SatisfiesFullOS` is satisfied by the free field too).**
   The headline ∃ is satisfied by the free Gaussian measure with the same
   covariance. Non-triviality (`pphi2_nontriviality`) and non-Gaussianity
   (`continuumLimit_nonGaussian`) are **separate** existential statements,
   not yet conjoined with the OS measure into a single "the interacting
   measure exists and satisfies OS". See
   [`planning/coherence-analysis.md`](../planning/coherence-analysis.md).
2. **Coherence gap B (over-claim across regimes).** The spectral-gap and
   non-Gaussianity content holds only at weak coupling (the φ⁴₂ phase
   transition exists), but the statement is unscoped. Should thread
   `IsWeakCoupling` up into the headline.
3. **Coherence keystone C (missing).** Weak-coupling **uniqueness of the
   limit** (cluster expansion / Dobrushin) — would glue the separate
   `∃μ`s into one, fix the regime, and upgrade subsequence → limit. This
   is the proposed item 18 in [`planning/INDEX.md`](../planning/INDEX.md).

The divergences are openly tracked, not hidden — the informal claim "the
*interacting* φ⁴₂ measure exists and satisfies OS" is **not yet** what's
formalized.

---

## Other formalized headlines

### `Pphi2.pphi2_main`
The OS bundle for the canonical continuum-limit measure (same axiom basis as
`pphi2_existence`). Same divergences apply.

### `Pphi2.pphi2_nonGaussianity`
`u₄ ≠ 0` for the headline measure. Rests on `continuumLimit_nonGaussian`.
**Status — Route A (PR #48, branch `route-a-weak-coupling`, OPEN /
not on this branch / not on `main`):** the T² non-Gaussianity *content*
(`torus_pphi2_isInteractingStrict_weakCoupling`) is **axiom-free** on
PR #48 in the T² formalization. Once PR #48 merges, the T² version
becomes part of `main`; the ℝ²-version axiom (this declaration)
remains as the infinite-volume lift.

### `Pphi2.pphi2_nontrivial`
`S₂(f,f) > 0` for `f ≠ 0`. Rests on `pphi2_nontriviality`. The free Gaussian
limit already witnesses this `∃μ` — see the coherence analysis for why the
"interacting" content requires the FKG short-distance singularity route
(blocked, ★★★).

### `Pphi2.cylinderIso_OS_of_RP_OS2`
Cylinder `S¹(Lₛ) × ℝ` φ⁴₂ OS0–OS3 assembly, conditional on the separate
reflection-positivity and OS2-symmetry inputs and the uniform exponential-moment
axiom (`asymInteracting_expMoment_volume_uniform`). Also pulls in the upstream
`GaussianField.embed_l2_uniform_bound` from `gaussian-field`.

---

## Per-axiom faithfulness (deferred to vetting records)

Each of the 17 architectural axioms has (or will have) a vetting record at
`audit/vetting/<AxiomName>.md` recording the informal statement it is
intended to capture, the literature reference, and a verdict on whether
the formal axiom faithfully matches that informal statement.

Until each record lands the **per-axiom faithfulness check** is L1
(warn, not enforced). See [`audit/CONVENTIONS.md`](CONVENTIONS.md) for
strictness policy.
