# pphi2 — validation (acceptance ladder)

*Where does pphi2 sit on the acceptance ladder?*

For the general model see
[`math-commons/formalization-assurance/VERIFICATION_VALIDATION.md`](https://github.com/math-commons/formalization-assurance/blob/main/VERIFICATION_VALIDATION.md).

The ladder, from weakest to strongest:

1. **Type-check.** The declaration compiles. — *kernel; automatic.*
2. **Sorry-free + axiom-pinned.** The declaration has a finite, named axiom
   basis recorded in a golden trace. — *`audit/axiom-report.txt`.*
3. **Named-property pinning.** Acceptance theorems pin the formal definition
   to *named informal properties* a mathematician would expect. (E.g.
   "the OS bundle satisfies translation invariance under `E(d)`.")
4. **Characterization.** A categorical-style theorem: the formal object is
   the **unique** model of a small set of axioms a reader can audit. (E.g.
   "any measure satisfying the OS bundle plus uniqueness arises as a
   continuum limit of the lattice construction.")
5. **Equivalence to an independent formalization** (where applicable).

## Current rung — and the gap

**Current rung: 2 (sorry-free + axiom-pinned).** The headline
`Pphi2.pphi2_existence` is `0 sorries` and rests on a kernel-certified
axiom basis: 4 project axioms plus the 3 Lean kernel axioms (see
[`audit/axiom-report.txt`](axiom-report.txt)). The other 13 architectural
axioms are dormant for this headline, load-bearing only for stronger or
sibling results — see [`audit/FAITHFULNESS.md`](FAITHFULNESS.md).

**Gap to rung 3 (named-property pinning).** The OS bundle
(`Pphi2.SatisfiesFullOS`) is the right informal target *if* one accepts
the bundle as a faithful encoding of OS73/OS75. Property-pinning theorems
that would close that loop:

- `SatisfiesFullOS.os2_implies_translation_invariance` and
  `os2_implies_euclidean_invariance` (already proved as part of the bundle;
  verify they're named/exposed).
- `SatisfiesFullOS.os3_is_reflection_positivity` — the formal OS3
  predicate is **definitionally** the reflection-positivity matrix
  condition (rather than via a chain of intermediate `def`s).
- Acceptance theorems for OS4 clustering in the cylinder branch.

These would let a reader audit the OS encoding without reading the proofs
inside `OSAxioms.lean`. **Not yet systematically catalogued** — partly
deferred until the headline existence is properly conjoined with
non-Gaussianity (the coherence-keystone item 18).

**Gap to rung 4 (characterization).** The keystone-18
**weak-coupling uniqueness** result, when proved, gives the natural
characterization: "the φ⁴₂ measure at weak coupling is *the* OS measure
satisfying P(φ) at that coupling, up to isomorphism." That theorem doesn't
yet exist in pphi2.

**Rung 5 (independent formalization equivalence).** Not currently relevant
— pphi2 is the only Lean 4 P(Φ)₂ formalization at this scale that we know
of. If a Coq or Isabelle competitor lands, a translation/equivalence pass
becomes the natural rung-5 capstone.

## Validation evidence

- **Kernel certificate** for the six headline targets:
  [`audit/axiom-report.txt`](axiom-report.txt). Regenerate with:
  ```bash
  lake env lean audit/axiom_report.lean > audit/axiom-report.txt
  ```
- **Coherence analysis** (the architectural gaps A/B/C):
  [`planning/coherence-analysis.md`](../planning/coherence-analysis.md).
- **Faithfulness map** (per-headline informal↔formal):
  [`audit/FAITHFULNESS.md`](FAITHFULNESS.md).
- **Comparator pass** (external kernel-replay + axiom-whitelist check):
  not yet run. Pre-requisite is the headline becoming axiom-clean for a
  released, sorry-free, public version of the theorem (currently 4
  project axioms remain — not axiom-clean). See the user-global
  [`COMPARATOR.md`](https://github.com/math-commons/formalization-assurance/blob/main/COMPARATOR.md)
  hub doc for the protocol.

## Roadmap

- **Short term (weeks).** Close out the cylinder Layer-B2 wiring
  (item 3 in [`planning/INDEX.md`](../planning/INDEX.md)). This is the
  nearest concrete formalization win and tightens the cylinder side of
  the kernel certificate.
- **Medium term.** Vetting coverage is at **19/19** as of 2026-06-21
  (see [`vetting/README.md`](vetting/README.md)). Next step is to
  raise `vetting_strictness` from L1 to L2 in
  [`vetting/policy.yml`](vetting/policy.yml) once the per-record
  metadata stabilizes (e.g. the `NEEDS_REVISION`-flagged records 7 and 11
  are resolved). Subsequently raise to L3 by populating `statement_hash`
  in each record.
- **Long term.** The four ★★★ mountains in
  [`planning/INDEX.md`](../planning/INDEX.md): Lee–Yang/Newman MGF
  (Layer A); spectral-gap uniformity (CYL-2a); non-Gaussianity on ℝ²;
  rotation restoration (OS2). Plus the keystone (item 18, weak-coupling
  uniqueness). When the keystone lands, the headline can be rephrased as
  "an OS measure that is also interacting" and rung 4 becomes reachable.
