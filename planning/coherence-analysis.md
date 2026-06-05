# Cross-cutting coherence analysis — do the axiom-discharge plans compose?

Each axiom's discharge plan is individually plausible. This doc checks whether, **once all are
discharged, they actually assemble into the headline result** — "an *interacting* φ⁴₂ theory
satisfying OS exists." Conclusion: **not as currently wired.** There are three structural gaps,
all resolved by one missing ingredient (weak-coupling uniqueness). These are architecture issues,
not individual-axiom issues, and they should shape *how* the axioms are stated/discharged.

## What IS coherent
`SatisfiesFullOS μ` (`EuclideanOS.lean:159`) is a **structure** bundling `os0, os1, os2, os3,
os4_clustering, os4_ergodicity` for **one** measure `μ`. `pphi2_main` assembles these from the
lower axioms (clustering 14/15, os2 5/13, …) for that single `μ`. So the **OS bundle is internally
coherent** — one measure, all six OS properties. Good.

## Gap A — "interacting" is NOT conjoined with OS (the most important)

`pphi2_existence` proves `∃ μ, SatisfiesFullOS μ`. But **the free Gaussian field also satisfies
`SatisfiesFullOS`** — OS0–OS4 do not distinguish free from interacting. The interacting-ness lives
in two **separate** axioms with their **own** existential measures:
- `pphi2_nontriviality` : `∃ μ', ∀ f≠0, S₂(μ')(f,f) > 0`   (≠ δ₀)
- `continuumLimit_nonGaussian` / `pphi2_nonGaussianity` : `∃ μ'', u₄(μ'') ≠ 0`   (interacting)

Nothing conjoins them: there is **no theorem** `∃ μ, SatisfiesFullOS μ ∧ (∀f≠0, S₂>0) ∧ u₄≠0` for
**one** `μ`. As stated, the project proves "an OS measure exists" and, *separately*, "a non-Gaussian
measure exists" — which together do **not** imply "the OS measure is interacting." The headline
could be honestly read as "the free field exists." **Fix:** a single conjoined theorem about one
`μ`. That requires either (i) proving `S₂>0` and `u₄≠0` for the **same extracted limit** that
`pphi2_exists` produces (thread the properties through the one Prokhorov extraction), or (ii)
uniqueness of the limit (gap C) so the separate `∃μ` provably coincide.

## Gap B — the weak-coupling regime is not propagated to the headline

The gap axioms (`spectral_gap_uniform` 17, `spectral_gap_lower_bound` 16) and non-Gaussianity
(`continuumLimit_nonGaussian` 9) are **only true at weak coupling** (φ⁴₂ phase transition closes the
gap; `λ>0` needed for `u₄≠0`) — see `cyl-2a-spectral-gap.md`, `non-triviality.md`. But:
- `pphi2_existence` / `pphi2_exists` are stated for **all** `P`, `mass>0` — **no** coupling
  hypothesis — yet `os4_clustering`/`os4_ergodicity` transitively depend on the gap axioms. So the
  headline implicitly invokes `spectral_gap_uniform` over all `P`, which is **false at criticality**.
- The Bridge layer already has the right notion — `IsWeakCoupling P mass coupling` (`Bridge.lean:178`)
  and `schwinger_agreement` carries `hP : isPhi4 P coupling`, `h_weak : IsWeakCoupling …` — but it is
  **not threaded into `Main.pphi2_exists`**.

**Fix (a real refactor implied by honest discharge):** add an `IsWeakCoupling` (or `0<λ` small)
hypothesis to axioms 9/16/17 **and propagate it** up through `os4_*` into `pphi2_exists`'s signature.
Discharging these axioms verbatim (all `P`) is impossible; the signatures must change.

## Gap C — uniqueness is the glue, and it is not an explicit ingredient

Both A and B are resolved by the **same** fact, which the Bridge layer *notes* but does not
formalize: **at weak coupling the limit is unique** (cluster expansion; `Bridge.lean:214` "At weak
coupling, the limit is unique"). With a uniqueness lemma:
- the separate `∃μ` of OS / nontriviality / non-Gaussianity provably refer to **one** `μ` (closes A);
- the regime hypothesis is exactly the uniqueness regime (closes B);
- and it upgrades subsequential convergence to genuine convergence (the existence axioms currently
  only extract *a* Prokhorov subsequence — cf. the earlier existence-vs-uniqueness discussion).

**Uniqueness at weak coupling is therefore the keystone the architecture is missing** — it is not
in the 17-axiom list, but it is what makes the discharge of the 17 *compose* into the headline. It
should be added as an explicit target (its own discharge plan: cluster expansion / Dobrushin
uniqueness at weak coupling), or the construction must be restructured so all properties are proved
on a single shared extraction (avoiding the need for full uniqueness, but still needing the regime).

## Minor — geometry: clustering (square) vs B2 (asym)
`two_point_clustering` / `general_clustering` (14/15) are stated on the **square** `FinLatticeField
2 Ns`; the B2/B4 trace machinery (`asymTransferKernel_kPow_apply`, the gap) is on the **asym**
`AsymLatticeField`. The "clustering rides on the B2 trace bridge" claim needs the **square**
instance of the kPow↔operator link + a `GappedTransfer` (or the asym↔square equivalence at `Nt=Ns`).
Low-risk but a real wiring step — note it in the B2 trace-bridge PR.

## Recommended architectural actions (in dependency order)
1. **Pick the regime up front.** Add `IsWeakCoupling P mass coupling` as a standing hypothesis;
   thread it into axioms 9/16/17 and into `pphi2_exists` (Gap B).
2. **Make uniqueness an explicit target** (new plan: weak-coupling uniqueness via cluster
   expansion / Dobrushin). This is the keystone (Gap C). Alternatively, design the extraction so
   OS + S₂>0 + u₄≠0 are all proved on one shared subsequence.
3. **State the conjoined headline:** `∃ μ, IsProbabilityMeasure μ ∧ SatisfiesFullOS μ ∧ (∀f≠0,
   S₂(μ)>0) ∧ (∃f, u₄(μ,f)≠0)` — the actual "*interacting* φ⁴₂ QFT exists" statement (Gap A).
4. Wire the square clustering instance to the (shared) transfer machinery (geometry note).

**Bottom line:** the 17 individual plans are sound, but the *assembly* currently proves a strictly
weaker (and regime-overclaimed) statement than intended. The missing keystone is **weak-coupling
uniqueness**, which simultaneously fixes the interacting-conjunction (A), the regime propagation
(B), and the subsequence-vs-limit issue (C). Recommend adding it to the plan as an 18th target and
restating the headline as a single conjoined theorem.
