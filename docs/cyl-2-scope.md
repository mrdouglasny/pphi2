# CYL-2 scope — OS4 (clustering / mass gap) for the cylinder S¹(Lₛ)×ℝ

*Code-grounded scope (2026-05-23), verified against the source — not the master plan (which was
off on CYL-1a). Target: extend `routeBPrime_cylinder_OS` (currently OS0+OS2+OS3) to **OS4
clustering**, giving `cylinder_satisfies_OS` and, via reconstruction, a 1+1d Wightman QFT with a
positive mass gap.*

`OS4_Clustering` (`OSAxioms`/`EuclideanOS.lean:133`): the generating functional factorizes at large
separation — `‖Z[f + τ_a g] − Z[f]·Z[g]‖ → 0` as `‖a‖ → ∞`. For the cylinder the relevant
separation is **Euclidean time** (the spatial circle Lₛ is fixed/compact).

## What is already proved (the foundation)

- **Transfer matrix, fixed lattice spatial size `Ns`** (`TransferMatrix/`): `massGap_pos`
  (`Positivity.lean:137`, `E₁−E₀ > 0` via Jentzsch/Perron–Frobenius), `transferOperator_ground_simple(_spectral)`
  (`Jentzsch.lean:465,499`, simple top eigenvalue + strict gap), `transferOperator_isSelfAdjoint`,
  `_isCompact`, `_spectral` (`L2Operator.lean:459,625,652` — full compact self-adjoint
  eigendecomposition). The cylinder's spatial direction is **compact (fixed Lₛ)**, so this gap *is*
  the physical mass gap of a fixed transfer operator (cleaner than the plane's IR situation).
- `clustering_implies_ergodicity` (`OS4_Ergodicity.lean:63`, abstract, proved).
- `os4_for_continuum_limit` (`ContinuumLimit/AxiomInheritance.lean:371`, proved): an exponential
  clustering bound ⟹ the OS4 ε-δ `Prop`. *(Plane route — reusable shape.)*

## The gaps, by difficulty tier

### Tier A — lattice clustering from the spectral gap *(currently 2 axioms; medium)*
`two_point_clustering_from_spectral_gap` (`OS4_MassGap.lean:137`) and
`general_clustering_from_spectral_gap` (`:160`) are **axioms** asserting exponential decay of the
connected lattice correlators in **cyclic** Euclidean-time distance
`d_cyc(t)=min(t,Nt−t)`, rate `m_phys`. They are the standard "spectral gap ⟹ exponential
clustering," and *in principle* follow from the proved compact-self-adjoint spectral decomposition
`transferOperator_spectral` via
`⟨F·(G∘shift_t)⟩ − ⟨F⟩⟨G⟩ = Σ_{k≥1}(λ_k/λ_0)^t ⟨F,ψ_k⟩⟨ψ_k,G⟩ ≤ (λ_1/λ_0)^t‖F‖‖G‖`.
**Prerequisite that is currently MISSING:** the **transfer-matrix representation of the lattice
correlations** — i.e. the identity expressing a Euclidean correlation `∫ ω(δ_{t,x})ω(δ_{0,y}) dμ`
as a transfer-operator matrix element `⟨v_x, T^t v_y⟩/⟨…⟩` (Feynman–Kac / time-slice
factorization). No such identity was found in `TransferMatrix/` or `OSProofs/`. So Tier A is **two
steps**: (A1) establish the transfer-matrix correlation representation (real work — connects the
*measure* to the *operator*), then (A2) the spectral-expansion bound (finite-dim spectral theory,
mechanical). A1 is the substance.

### Tier B — cylinder-level OS4 via the `Lₜ→∞` transfer *(new wiring; medium, no analogue)*
**Missing entirely.** Need a new `cylinder_os4_clustering` and to wire OS4 into
`routeBPrime_cylinder_OS`. Route:
1. lattice clustering (Tier A) in **cyclic** time distance on T²(Lₜ×Lₛ);
2. as `Lₜ→∞`, `d_cyc(t)=min(t,Nt−t) → t` (genuine, unbounded) — the bound becomes
   `≤ C·exp(−m_phys·τ)` for unbounded `τ`;
3. carry that bound through the weak / characteristic-functional limit to the cylinder IR measure
   (the survey flags this is *not* formalized: unlike RP/moments, no factorization-bound transfer
   exists yet — mirror the OS3 pattern `rp_closed_under_weak_limit` /
   `cylinderMeasureReflectionPositive_of_tendsto_cf`);
4. `clustering_implies_ergodicity` + `os4_for_continuum_limit`-style wrapper ⟹ OS4.
Analogous in weight to the (already-done) OS3 transfer — tractable but genuinely new.

### Tier C — the `a`-uniform mass gap *(textbook-axiom territory; the hard core of constructive P(φ)₂)*
`spectral_gap_uniform` (`SpectralGap.lean:89`): `∃ m₀>0, ∀ a≤a₀, m₀ ≤ massGap(a)` — the gap
**survives the continuum (UV) limit** with a positive lower bound. `spectral_gap_lower_bound`
(`:100`, `m_phys ≥ c·m_bare`) is similar. **This is the physical mass gap and the genuinely hard
theorem of constructive P(φ)₂** (Glimm–Jaffe / Simon — established via cluster expansion /
correlation inequalities). Recommendation: **keep as vetted textbook axioms**, cited and audited,
rather than reproving the cluster-expansion machinery from scratch (out of scope for the
formalization unless that whole apparatus is built). These are the legitimate "textbook axiom" per
`AXIOM_MANAGEMENT`.

*(Plane route note: ℝ² OS4 is already handled conditionally by `continuum_exponential_clustering`
(`AxiomInheritance.lean:354`, an axiom) + `os4_for_continuum_limit`. The cylinder has no analogue
yet — Tiers A+B build it; the cylinder is cleaner since Lₛ is compact.)*

## Recommended staging (most tractable first)

1. **Tier A1 — transfer-matrix correlation representation.** State + prove that lattice Euclidean
   two-point (and general) correlations equal transfer-operator matrix elements. This is the
   load-bearing measure↔operator bridge; everything in OS4 rests on it. *Start here.*
2. **Tier A2 — spectral clustering.** Discharge `two_point_clustering_from_spectral_gap` /
   `general_clustering_from_spectral_gap` from A1 + `transferOperator_spectral`. Mechanical once A1
   lands (finite-dim spectral expansion). Removes 2 axioms.
3. **Tier B — cylinder OS4.** State `cylinder_os4_clustering`; prove cyclic→genuine-distance limit +
   weak-limit transfer of the factorization bound; wire OS4 into `routeBPrime_cylinder_OS` →
   `cylinder_satisfies_OS`.
4. **Tier C — leave as audited textbook axioms** (`spectral_gap_uniform`, `spectral_gap_lower_bound`):
   the mass-gap-survives-continuum-limit input. Document Glimm–Jaffe/Simon citations; revisit only
   if the cluster-expansion apparatus is ever built.

## Honest assessment

- The transfer-matrix **gap itself is proved** (fixed `Ns`); the **operator spectral theory is
  proved**. The missing analytic content is concentrated in (A1) the correlation↔operator
  representation and (B) the `Lₜ→∞` clustering transfer — both real but bounded, each comparable to
  the OS3 work already completed.
- The **genuinely hard** input (mass gap survival under the continuum limit, Tier C) is
  appropriately a textbook axiom — proving it is the substance of the original constructive program,
  not a formalization-plumbing task.
- **No quick win**: unlike this cycle's two discharges (which had all inputs proved), Tier A2 is
  gated on the not-yet-existing A1. Realistic first deliverable: A1 (the transfer-matrix correlation
  representation), then A2 falls out.

## Axiom ledger relevant to CYL-2
| Axiom | File:Line | Tier | Disposition |
|---|---|---|---|
| `two_point_clustering_from_spectral_gap` | `OS4_MassGap.lean:137` | A | dischargeable (after A1) |
| `general_clustering_from_spectral_gap` | `OS4_MassGap.lean:160` | A | dischargeable (after A1) |
| `spectral_gap_uniform` | `SpectralGap.lean:89` | C | keep as textbook axiom |
| `spectral_gap_lower_bound` | `SpectralGap.lean:100` | C | keep as textbook axiom |
| `continuum_exponential_clustering` | `AxiomInheritance.lean:354` | (plane) | plane OS4 bridge; analogue of Tier B for ℝ² |
