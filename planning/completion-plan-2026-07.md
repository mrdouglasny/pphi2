# pphi2 completion plan — 2026-07 review synthesis

**Date**: 2026-07-12 (status refreshed 2026-07-13 — see the addendum at the end). **Source**: full-project review (four parallel audits: T² validity,
cylinder Route B′ gaps, Route A ℝ² status, planning-repo/random-fields leverage). Fresh
`lean_verify` kernel checks were run against the current build cache for every headline named
below; findings marked **[verified]** are from those runs, not from the committed certificate.

**Companion docs**: [`INDEX.md`](INDEX.md) (per-axiom status machine — remains the single source
of truth for axiom rows), [`coherence-analysis.md`](coherence-analysis.md) (Gaps A/B/C),
[`../docs/cylinder-master-plan.md`](../docs/cylinder-master-plan.md),
[`../docs/layer-B2-discharge-plan.md`](../docs/layer-B2-discharge-plan.md).

---

## Review verdict (what this plan is built on)

1. **T² is partially valid: strong pieces, unassembled whole.**
   - `torusInteracting_satisfies_OS` (`TorusInteractingOS.lean:2822`) — OS0/OS1/OS2 for any weak
     subsequential limit of the Wick-ordered interacting torus measures. Kernel footprint
     `{propext, Classical.choice, Quot.sound}` **[verified]**. Definitions faithful (real
     analyticity of the actual CF, real Green-diagonal seminorm, real invariances); hypotheses
     witnessed by the axiom-clean `torusInteractingLimit_exists` — non-vacuous.
   - `torus_pphi2_isInteractingStrict_weakCoupling` (`TorusCouplingResult.lean:166`) — u₄ < 0
     for the coupling-family limit, kernel-only **[verified]**; `lattice_u4_neg_uniform` is a
     theorem.
   - **BUT**: OS and interactivity are proved for *different families*
     (`torusInteractingMeasure` vs `torusInteractingMeasureCoupling`), never conjoined (Gap A on
     the torus); the conjoined target `TorusInteractingTheoryExists`
     (`TorusNontriviality.lean:137`) is an unproved `def` that omits OS; the coupling files are
     **not imported by `Pphi2.lean`** (outside the built root); **no torus theorem is in
     `audit/axiom-report.txt`**; `TorusIsNondegenerate` (S₂ > 0) is undischarged;
     `audit/FAITHFULNESS.md:98–104` is stale (says coupling files are PR-only; they are on main).
2. **ℝ² headline `pphi2_existence` is near-vacuous as stated**: `pphi2_limit_exists`
   (`ContinuumLimit/Convergence.lean:282`) is witnessed by `Measure.dirac 0`; the 4 kernel axioms
   (`continuum_exponential_moment_bound`, `canonical_continuumMeasure_cf_tendsto`,
   `continuum_exponential_clustering`, `rotation_cf_defect_polylog_bound`) supply all physics
   about that abstract measure. Known (memory `pphi2-existence-vacuous-delta0`); this plan makes
   fixing the statement a gating step before further ℝ² analytic spend.
3. **Cylinder Route B′** is structurally wired (`routeBPrime_cylinder_OS` conditional OS0+OS2+OS3;
   IR machinery 0 local axioms). Critical path: Layer B2 finish → Layer A (Lee–Yang, not
   started) → Layer C assembly → OS3 asym-lattice RP port. OS4 long pole: `a`-uniform spectral
   gap, which must first be regime-restricted (false at criticality).
4. **External leverage**: `reflection-positivity` (already a dep) carries the proved B2 operator
   machinery; `random-fields/RandomFields` `Instances/OUDiffusion` has a proved
   `gaussian_chaos_hypercontractive` (Bonami–Nelson) that may discharge the single remaining
   gaussian-hilbert axiom; `random-fields/GibbsMeasure` branch `feat/Ch6InfVolume` tree
   `Ch6Subtree/` has a **genuine** Kotecký–Preiss cluster expansion (lattice, finite spin) —
   a template for keystone 18, *not* a drop-in. (Beware: the parallel `Ch6InfVolume/` tree is
   vacuous stubs; never cite its grep counts.)

---

## Phase 0 — T² assembly + certificate honesty  *(≈ 2–5 active days; do first)*

Converts the strongest existing results into one citable composed theorem and closes the
claims/code gaps found in the audit. All mechanical or near-mechanical.

- [ ] **0.1 Conjoined T² headline.** Prove
  `∃ g₀ ∈ (0,1], ∃ μ, SatisfiesTorusOS L μ ∧ TorusIsInteractingStrict L μ`.
  Route: check whether `torusInteractingMeasureCoupling L N P mass g ≡`
  `torusInteractingMeasure L N (g•P) mass` (the "coupling folds into P" design suggests it, or
  a `Measure.map`-level equality lemma). If yes, apply the existing OS bundle to the coupling
  family along the *same* subsequence extracted in `TorusCouplingResult.lean` and conjoin.
  If the definitional route fails, port the OS bundle statement to the coupling family (the
  proofs are coupling-uniform Nelson + Prokhorov, so this is re-plumbing, not new analysis).
  Deliverable: theorem in `TorusCouplingResult.lean` (or a new `TorusAssembly.lean`); upgrade
  `TorusInteractingTheoryExists` to include OS and prove it (weak-coupling form).
- [ ] **0.2 Built-root inclusion.** Import `TorusCouplingLimit`/`TorusCouplingResult` (and 0.1's
  file) from `Pphi2.lean` so the sorry/axiom gate sees them.
- [ ] **0.3 Golden certificate.** Add the torus headlines (`torusInteracting_satisfies_OS`,
  `torus_pphi2_isInteractingStrict_weakCoupling`, `torusInteractingLimit_exists`, 0.1's theorem)
  to `audit/axiom_report.lean`; regenerate `audit/axiom-report.txt`.
- [ ] **0.4 Doc refresh.** Fix `audit/FAITHFULNESS.md` (coupling files are on main); fix stale
  docstrings (`analyticOnNhd_integral` is a proved theorem — `TorusInteractingOS.lean:129`;
  stale `sorry` mentions at `TorusTightness.lean:70`); fix the `TorusOSAxioms.lean` module
  header claiming OS0–OS3 (bundle is OS0–OS2). Update README per-route table wording:
  "T² OS0–OS2 + weak-coupling non-triviality, **conjoined**" once 0.1 lands.
- [ ] **0.5 (Optional, bounded) T² nondegeneracy.** `TorusIsNondegenerate`
  (`TorusNontriviality.lean:103`): S₂(f,f) > 0 for f ≠ 0. Candidate route: Gaussian
  lower bound via FKG/Griffiths or directly from the density-transfer Cauchy–Schwarz machinery
  (interacting second moment ≥ c · free second moment at weak coupling). Scope before
  committing; park if it exceeds ~3 days.

**Acceptance**: `#print axioms` on the conjoined theorem = kernel trio; torus rows present in
`audit/axiom-report.txt`; CI green.

---

## Phase 1 — Upstream hypercontractivity check  *(RESOLVED 2026-07-12 — already done upstream)*

**Outcome (kernel-verified 2026-07-12, closes 1.1–1.3): no port needed.** At pphi2's current pins
(gaussian-hilbert `56ee09f` = its main HEAD; markov-semigroups `acf6491`, two doc-only commits
behind main), `#print axioms` gives the bare Mathlib trio for all of:
`GaussianHilbert.ouSemigroupAct_eLpNorm_hypercontractive`, `GaussianHilbert.bonami_nelson_chaos`,
`GaussianHilbert.polynomial_chaos_concentration`. The Gross step rides markov-semigroups'
**proved** `gross_lsi_implies_hypercontractive_of_hypotheses`
(`Instances/WorkInProgress/EuclideanHypercontractive.lean:482` explicitly bypasses the legacy
axiom at `Abstract/Hypercontractivity.lean:648`); the Concentration axioms (`herbst_mgf_bound`,
`poincare_of_lsi`) are not load-bearing for the chain either. RandomFields'
`gaussian_{hypercontractive,lp_improvement,chaos_hypercontractive}` were independently
kernel-verified axiom-free (its `GrossODE.lean` "documented sorry" notes are stale prose over
real proofs). **Follow-ups**: (a) gaussian-hilbert `HypercontractivityFromBE.lean:21–46`
header ("4 non-core axioms") is stale — fix in that repo; (b) pphi2 `AXIOM_AUDIT.md` summary
rows for MarkovSemigroups/gaussian-hilbert overstate the load-bearing debt — dated entry added.

- [x] **1.1** Compare `random-fields/RandomFields` `Instances/OUDiffusion`
  (`gaussian_hypercontractive`, `gaussian_lp_improvement`, chaos-level
  `gaussian_chaos_hypercontractive`: `‖f‖_{L^p(γ)} ≤ (p−1)^{k/2}‖f‖_{L²}`) against the **single
  remaining gaussian-hilbert axiom** `ouSemigroupAct_eLpNorm_hypercontractive`
  (Bonami–Beckner–Nelson; discharge plan
  `gaussian-hilbert/docs/hypercontractivity-discharge-plan.md`). Check: measure conventions
  (γFin vs isonormal), semigroup vs chaos-grading form, Lp index conventions, Mathlib pin
  compatibility (RandomFields is on v4.30.0).
- [x] **1.2** Moot — chain already theorem-backed at current pins (see outcome above).
- [x] **1.3** Moot — no mismatch to record; stale docs flagged instead (see outcome above).

**Payoff**: removes the last upstream axiom under every Nelson-estimate consumer in pphi2 —
cheap, high leverage, independent of all other phases.

---

## Phase 2 — Cylinder OS0–OS3 unconditional  *(the main campaign; ≈ 4–8 wk elapsed)*

Target: `routeBPrime_cylinder_OS` with all three family hypotheses discharged →
**M-cyl-1: cylinder OS0+OS1+OS2+OS3, axiom count on this lane → 0** (modulo any axioms
deliberately retained as vetted GJ inputs — decide at 2.4).

### 2a. Layer B2 finish (current crux; ~1.5–3 wk per `layer-B2-scoping.md`)

- [ ] **2a.1** Close Route-A Pieces 2–3: the finite-K time-family estimate and the K→∞
  dominated-convergence packaging (Pieces 1 & 5 landed 2026-06-23).
- [ ] **2a.2** Discharge B5b `groundVariance_le_freeCovariance`
  (`AsymB5bSingleSlice.lean:162`) and the free-side assembly. **Hard constraint** (crux-2
  class): the `1/a` must cancel inside the int/free ratio — never evaluate `1/(1−γ)`
  standalone (`layer-B2-discharge-plan.md:456–462`). Mandated: an a-power design pass
  (Gemini/Codex) before formalizing the free-side assembly.
- [ ] **2a.3** Discharge the 6 GNS bridge axioms (`AsymBridgeInstance.lean:81–219`):
  `asymGroundStateRep_pos_ae`, `asymTransferNormalized_contract`,
  `asymGroundStateRep_eq_groundIsometry_one`, `asymGroundSemigroup_intertwines`,
  `asymPartition_ground_bound`, `asymFinitePeriodicBridge_remainder_bound`. Each has an inline
  docstring plan + `audit/vetting/` record; most are Jentzsch/spectral bookkeeping against the
  **proved** `asymGappedTransfer'`. Consume `reflection-positivity`'s proved
  `TransferSystem`/`TransferConstruction` dictionaries (see its `RECON.md` "Op 1") rather than
  re-proving trace identities.
- [ ] **2a.4** Assemble → convert `asymInteractingVariance_le_freeVariance_lattice_Lt_uniform`
  (`AsymExpMomentDischarge.lean:215`) to a theorem.
- **Route discipline (vetted dead-ends — do not revisit):** direct TM-sum vs `Var_free`
  comparison (NORM MISMATCH, L² ⊄ H⁻¹); mode-by-mode covariance domination (false — Wick
  bare mass → −∞); spectral-measure domination ρ_int ≤ Cρ_free (false — mutually singular);
  Brascamp–Lieb (non-convex); Nelson-rotation as spatial control (red herring); interacting KL
  representation axiom (do not write). Surviving route: **B1 ⊕ gap**. No chessboard/FSS at
  fixed Ls.

### 2b. Layer A — Newman/Lee–Yang MGF domination (★★★ — *see 2026-07-13 addendum: axiom sign-restricted; producer chain proof-complete in `lee-yang`; A3/A4 remain*)

- [x] **2b.1** *(DONE 2026-07-12 — [`layer-a-lee-yang-scoping.md`](layer-a-lee-yang-scoping.md):
  polynomial/Asano side already complete in `lee-yang`; recommended inequality-first restructure
  avoids Hadamard/Hurwitz; A1–A4 breakdown ~4–7 wk.)* Scope the `lee-yang` repo deliverable: Lee–Yang property for the lattice P(φ)₂
  (ferromagnetic, even P) → Newman's Gaussian domination of the MGF
  (`asymInteracting_mgf_gaussianDominated`, `AsymExpMomentDischarge.lean:127`, K = 2 form).
  Refs: Newman 1975; GJ Ch. 18–19; vetting record in AXIOM_AUDIT (the `∃C·σ²` exponent form is
  the correct one; `C = 1` is false in infinite volume).
- [ ] **2b.2** Decide staging: this is the natural candidate to **retain as a vetted textbook
  axiom for M-cyl-1** (per the master plan's decided path) and discharge as its own campaign.
  If retained: keep the axiom, tighten its vetting record, and proceed; if attacked now, budget
  it like a fresh mid-size project (weeks, new repo).
- [x] **2b.3** (RESOLVED 2026-10-08: removed as false as stated, issue #63.) Same decision for `nelson_exponential_estimate_master_bounded`
  (`PolynomialChaosBridge.lean:1321`) — note Phase 1 success shrinks its upstream debt.

### 2c. Layer C assembly

- [ ] **2c.1** `asymInteracting_expMoment_volume_uniform` (`AsymContinuumLimit.lean:621`) →
  theorem, ~50 lines from A × B2. Discharges `hUnif` /
  `AsymTorusSequenceHasUniformGreenMomentBound` at the family level.

### 2d. OS3 — asym lattice RP port

- [ ] **2d.1** Write `OS3_RP_AsymLattice.lean` (~2000 lines, mechanical port of the square
  chain per `docs/cylinder-os3-discharge-plan.md`); the only genuinely new lemma is
  `massOperatorAsym_cross_block_zero`. Reuses the single private axiom
  `gaussian_rp_cov_perfect_square` (`OS3_RP_Lattice.lean:648`) — consider discharging it in
  passing (it is a finite-dimensional Gaussian Fubini/perfect-square fact).
- [ ] **2d.2** Discharge `CylinderMeasureSequenceEventuallyReflectionPositive` via
  compact-support/no-wrap + torus RP + density (`docs/ir-limit-overview.md` §5.5).
- [ ] **2d.3** `AsymTorusSequenceHasCylinderOS2Symmetry` via the existing `.of_torusOS`
  (`IRLimit/CylinderOS.lean:380`) — wiring only.

### 2e. Continuum inheritance + OS1 lane

- [ ] **2e.1** Discharge/narrow the inheritance axioms now that their inputs are theorems:
  `continuum_exponential_moment_bound` (`AxiomInheritance.lean:123`),
  `latticeGreenBilinear_basis_tendsto_continuum` (`PropagatorConvergence.lean:103`),
  `continuum_exponential_clustering` (`AxiomInheritance.lean:354`, waits on Phase 3).
  **Restate** `canonical_continuumMeasure_cf_tendsto` (`AxiomInheritance.lean:327`) in the
  forward direction (lattice → continuum CF convergence for the *constructed* sequence) instead
  of the blocked converse form — fold into Phase 4.1's headline rewrite.
- [ ] **2e.2** CYL-1d: add OS1 to the cylinder bundle (extends the proved OS0 transfer).

**Acceptance**: `routeBPrime_cylinder_OS` specialization with zero hypotheses; kernel trace of
the cylinder OS0–OS3 headline lists only the deliberately retained axioms (target: Layer A pair
at most); rows updated in `INDEX.md`; torus+cylinder headlines in the golden certificate.

---

## Phase 3 — Cylinder OS4 (mass gap / clustering)  *(parallel to 2b–2e; research-flavored)*

*(3.1/3.2 refined 2026-07-12 by [`cyl-2a-volume-scaling-addendum.md`](cyl-2a-volume-scaling-addendum.md):
the gap axioms are stated at FIXED `Ns` — a shrinking-volume limit; split into 17a fixed-`Ls`
(no regime hypothesis, compact-resolvent route) + 17b volume-uniform (weak coupling, FSS/keystone
track). Follow the addendum's 3.1'-3.4' sequencing.)*
- [ ] **3.1 Regime restriction first.** Restate `spectral_gap_uniform`
  (`TransferMatrix/SpectralGap.lean:89`) and `spectral_gap_lower_bound` (`:100`) under an
  explicit weak-coupling/single-phase hypothesis (both are **false at criticality** —
  `planning/cyl-2a-spectral-gap.md:37–46`). Thread the same `IsWeakCoupling` used in Phase 4.1.
- [ ] **3.2 The `a`-uniform gap (CYL-2a, the long pole).** Finite-`a` gap is proved
  (`asymGappedTransfer'`, `asymTransferNormalized_gap`). The new theorem is gap survival as
  `a → 0` at fixed Ls via compact-resolvent convergence `T_a → e^{−aH(Ls)}` (Simon Ch. VI;
  expert-vetted in `reflection-positivity/docs/B2_UNIFORMITY_QUESTION.md`). This is genuinely
  new formalization territory (strong-resolvent convergence of transfer operators) — scope a
  dedicated plan doc before starting; treat as its own ~3–6 wk campaign.
- [ ] **3.3 Clustering discharge.** `two_point_clustering_from_spectral_gap`
  (`OS4_MassGap.lean:137`) and `general_clustering_from_spectral_gap` (`:160`) ride the proved
  B2 trace bridge (`connected_two_point_le`) — same-PR material as 2a.4, **but** they are
  stated on the square lattice while the trace machinery is asym: either build the square trace
  dictionary or port the statements to asym (low-risk wiring, flagged in
  `coherence-analysis.md:63–68`).
- [ ] **3.4** Cylinder OS4 statement + weak-limit transfer (mirror the OS3 inheritance pattern);
  then `continuum_exponential_clustering` (2e.1) discharges.
- [ ] **3.5 (Look-ahead)** Reconstruction needs CYL-4a (`LinearGrowth` witness for the cylinder
  OSPackage) — keep as an explicit named input; do not fold into OS4.

---

## Phase 4 — ℝ² (infinite volume), honestly stated  *(gate all ℝ² analytic spend on 4.1)*

- [ ] **4.1 Headline restatement (blocking).** *(Design DONE 2026-07-12 — decision spec with
  pinned statements at [`r2-honest-headline-spec.md`](r2-honest-headline-spec.md); implementation
  ~1–2 days, mostly mechanical, sequence after Phase 0 merges.)* Replace the δ₀-satisfiable
  `pphi2_existence` with a conjoined, regime-scoped target:
  `∀ P even deg ≥ 4 …, IsWeakCoupling P mass → ∃ μ, SatisfiesFullOS μ ∧ TorusIsNondegenerate-analog ∧ u₄ ≠ 0`,
  where μ is required to be the weak limit of the **constructed** lattice family
  (forward-direction `IsPphi2Limit`, strengthened per
  `planning/ispphi2limit-strengthening-scope.md`). Demote the current `pphi2_existence` to a
  clearly-labeled structural lemma or delete. This also resolves the blocked axiom 7
  (`canonical_continuumMeasure_cf_tendsto`) by never needing the converse.
- [ ] **4.2 Keystone 18 — weak-coupling uniqueness (cluster expansion).** *(Campaign design
  DONE 2026-07-13 — [`keystone-18-campaign.md`](keystone-18-campaign.md): K18-0 KP-core
  extraction (delegable) → K18-1 foundations → K18-2 small/large-field research core (★★★,
  Fable-led, vet-first) → K18-3 fixed-spacing uniqueness assembly → K18-4 coupled-limit step
  (Gap C proper, own design pass). Template extraction verified the KP engine is fully
  generic; only the activity layer is genuinely new.)* The glue for Gaps
  A/B/C (`coherence-analysis.md`). Route: continuum/lattice P(φ)₂ polymer expansion at weak
  coupling → boundary-independence + uniqueness + exponential clustering. **Template**: the
  genuine `Ch6Subtree/` expansion in `random-fields/GibbsMeasure`
  (`feat/Ch6InfVolume`): `KPCondition`/`kpSystem_condition`, cluster-series summability
  (tree-graph bounds), `cluster_expansion_converges_and_error`
  (`Tendsto` along exhaustions + `D·e^{K|supp f|}·‖f‖∞·e^{−C·dist}` error),
  `ClusterExpansionCriterion` uniqueness. Mirror its architecture declaration-for-declaration
  for unbounded spins/Gaussian base (the polymer bounds change; the combinatorics and KP
  framework port). Pre-steps: (i) get `feat/Ch6InfVolume` merged or at least CI-verified
  upstream — its counts are currently grep-only, no CI; (ii) **never** cite the sibling
  `Ch6InfVolume/` tree (vacuous stubs/tautologies per its own `AXIOM_AUDIT.md`); (iii) update
  `planning/status/GibbsMeasure.md` in the planning repo to distinguish the two trees.
  Budget as a fresh multi-week campaign (sister-project speedup applies: KP combinatorics
  exists; the new analysis is the P(φ)₂ polymer estimates ≈ small-field/large-field split).
- [ ] **4.3 Cluster A — GJ Ch. 8 dynamical-cutoff Nelson estimate** (~6–8 wk per the Gemini
  estimate in `docs/lattice-action-normalization-fix.md` §4; could compress given the proved
  Phase-B Fourier estimates and the asym ports). Discharges the exp-moment chain feeding
  `continuum_exponential_moment_bound`. Shares infrastructure with 2b — sequence after the
  cylinder campaign settles which pieces are already theorems.
- [ ] **4.4 Rotation restoration** — `rotation_cf_defect_polylog_bound`
  (`OS2_WardIdentity.lean:614`, ★★★, GJ §19.3 anomaly O(a²|log a|^p)). Needed for full E(2)
  OS2 on ℝ² only (cylinder does not need it). Keep last unless an external result materializes.
- [ ] **4.5 IR limit ℝ²**: after the cylinder is done, the remaining geometry step is
  `Ls → ∞`. The parked FSS infrared bound (`docs/fss-infrared-bound-spec.md`, vetted statement
  + drop-in signature, needs a Fourier layer) is the designated tool — introduce it only when
  this step starts (it currently has no consumer).

---

## Cross-cutting discipline

- **Certificate**: every phase's headline goes into `audit/axiom_report.lean` in the same PR;
  `audit/axiom-report.txt` regenerated; `count_axioms.sh` + `status.md` + README counts updated
  together (existing project rule).
- **Axiom hygiene**: any axiom retained at a milestone (Layer A pair, spectral-gap pair) gets a
  refreshed vetting record under `audit/vetting/` and an explicit "retained for milestone X"
  note in `INDEX.md`.
- **External repos**: pin bumps (gaussian-hilbert, reflection-positivity, GibbsMeasure-derived
  code) follow the stale-dep-cache clearing rule; upstream anything lattice-generic (KP
  combinatorics, trace dictionaries) rather than growing pphi2.
- **planning repo**: correct `planning/status/GibbsMeasure.md` (Ch6Subtree vs Ch6InfVolume) —
  the current "0 sorry/0 axiom" line is measuring the vacuous tree.

## Milestones & rough budget (recalibrated norms)

| # | Milestone | Contents | Est. active effort |
|---|---|---|---|
| M0 | **T² composed theorem** | Phase 0 | 2–5 days |
| M1 | Upstream hypercontractivity | Phase 1 | 1–2 days (or drop) |
| M2 | **Cylinder OS0–OS3**, ≤ 2 retained vetted axioms (Layer A pair) | Phase 2 | 3–5 wk |
| M3 | Cylinder OS0–OS3 axiom-free | 2b discharge (Lee–Yang campaign) | +3–6 wk |
| M4 | **Cylinder OS4** (weak coupling) | Phase 3 (gap transfer = long pole) | 3–6 wk, partly parallel |
| M5 | **ℝ² honest headline + uniqueness keystone** | 4.1 + 4.2 | 4.1: days; 4.2: 4–8 wk |
| M6 | ℝ² OS0–OS4 conjoined, weak coupling | 4.3–4.5 | multi-week tail |

Ordering: M0 → M1 immediately; M2 is the main line; M4 scoping (3.1–3.2 plan doc) can start in
parallel; M5's 4.1 (headline restatement) should land **before** any further ℝ²-specific
analytic work so effort accrues to a non-vacuous target.

---

## Status addendum (2026-07-13, end of the overnight/morning loop)

**Landed since the plan was written** (all on `t2-conjoined-os`, pushed):
- **B2 DISCHARGED (thresholded)**: `asymInteractingVariance_le_freeVariance_lattice_thresholded`
  AND its torus-level Piece-5 migration `…_torus_thresholded` — theorems on exactly the
  5 vetted axioms (S1 FSS, S2 gap, τ-bridge pair, B5b). Legacy all-`(Lt,a)` axiom carries a
  migration note; Layer-C rewiring to the eventual form is the remaining wiring.
- **Asym exponential clustering** in physical distance (2-axiom footprint) — the OS4 lattice
  input, replacing the removed `clustering_uniform` route.
- **Phase 4.1 DONE**: honest ℝ² headline (δ₀ closed, vetted existence axiom, 31 raw/29 real).
- **Keystone-18 fully designed**: campaign staged (K18-0..4) + the K18-2 activity layer
  vetted FINAL (AR-BKAR, no field split — Hölder+Nelson; λ₀ a-uniform; adjacent-block
  integrated bounds). Effort for K18-2 reduced to 2–4 wk.
- **Layer A**: A2.1–A2.4 landed in lee-yang (Codex, reviewed/accepted); task files for A2.5
  + A1 committed and Codex-ready; repo now public (mrdouglasny/lee-yang).
- Also this cycle: PR #60 merged (false gap axioms off main); the τ-form/K-uniform bridge
  axiom architecture; Stage A/B2 route (a) infrastructure (S4 spectral toolkit, S1 high
  branch, slice-constant + band machinery, B-I/B-II, hInt discharge).

**Open owner decisions**: K18-0 home; Layer-A axiom restatement (`0 ≤ f`); Layer-C
eventual-form rewiring sign-off; lee-yang A2.5/A1 Codex dispatch.
**Next Fable arcs** (fresh-context recommended): K18-1 foundations + AR-identity statement
work (after K18-0), Layer-A A3 (GS limit passage) design, OS4 continuum-transfer design
(cylinder clustering → `continuum_exponential_clustering`).
