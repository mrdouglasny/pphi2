# `SpectralGap.lean` -- Informal Summary

> **Source**: [`Pphi2/TransferMatrix/SpectralGap.lean`](../../Pphi2/TransferMatrix/SpectralGap.lean)
>
> **Generated**: 2026-03-20

## Overview
Restates the strict positivity of the mass gap (`spectral_gap_pos`, proved). The two former axioms for a uniform-in-`a` lower bound at fixed `Ns` (`spectral_gap_uniform`, `spectral_gap_lower_bound`) were **removed 2026-07-12 as false as stated** (shrinking-volume regime; wrong-counterterm double well closes the gap — see `AXIOM_AUDIT.md` 2026-07-12 and `planning/cyl-2a-volume-scaling-addendum.md` for the corrected coupled-limit replacement design).

## Status
**Main result**: `spectral_gap_pos` (proved)
**Length**: 0 definitions + 1 theorem + 0 axioms (updated 2026-07-12)

---

### `spectral_gap_pos`
$E_1 - E_0 > 0$. Delegates to `massGap_pos`. Fully proved.

