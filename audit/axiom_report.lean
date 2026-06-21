/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2

/-!
# Kernel axiom certificate generator for pphi2

Runs `#print axioms` on the headline theorems and prints the result. The
output is the kernel-authoritative axiom set: anything that does NOT appear
in this trace cannot have leaked through the build, so this is the single
source of truth for "what does the headline depend on".

**Targets** (matching `formalization.yaml` → `main_results`):

* `Pphi2.pphi2_existence` — ∃ μ on S'(ℝ²) satisfying OS0–OS4 (conditional).
* `Pphi2.pphi2_main` — a P(Φ)₂ continuum-limit measure satisfies the OS bundle.
* `Pphi2.pphi2_nonGaussianity` — u₄ ≠ 0 (rests on `continuumLimit_nonGaussian`).
* `Pphi2.pphi2_nontrivial` — S₂(f,f) > 0 (rests on `pphi2_nontriviality`).
* `Pphi2.cylinderIso_OS_of_RP_OS2` — cylinder OS0–OS3 assembly
  (conditional on RP + OS2-symmetry + the uniform exp-moment axiom).
* `Pphi2.pphi2_exists_os_and_massParameter_positive` — secondary headline,
  the variant carrying the (input) mass-parameter positivity.

**Usage**:

```
lake env lean audit/axiom_report.lean > audit/axiom-report.txt
```

The committed `audit/axiom-report.txt` is the **golden trace**; CI diffs the
fresh run against it (when wired). The two-file split is deliberate:
generator vs. golden output, with the underscore/hyphen difference in the
filename per the hub convention.
-/

#print axioms Pphi2.pphi2_existence
#print axioms Pphi2.pphi2_main
#print axioms Pphi2.pphi2_nonGaussianity
#print axioms Pphi2.pphi2_nontrivial
#print axioms Pphi2.cylinderIso_OS_of_RP_OS2
#print axioms Pphi2.pphi2_exists_os_and_massParameter_positive
