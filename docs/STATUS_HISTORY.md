# Status history (archived from README)

Dated, narrative status detail moved out of `README.md` on 2026-06-07 to keep the README's
"Current status" a concise per-route snapshot. This file is the historical log; for the **current**
state see `README.md` → "Current status", [`../planning/INDEX.md`](../planning/INDEX.md) (per-axiom
master status machine), [`../BRANCHES.md`](../BRANCHES.md) (branch → axiom map), and
[`AXIOM_STATUS.md`](AXIOM_STATUS.md) (axiom inventory). Older audit passes live in
[`axiom_audit.md`](axiom_audit.md) and [`../status.md`](../status.md).

---

## Route A (ℝ²) — discharge narrative (through 2026-06)

Stage 1 lattice-action fix raised the axiom count from 22 to 35; Phase 2 partial discharge plus
PR #14 (Route B′ IR-limit refactor + `fourierTransform_lp_eq_fourierIntegral` proof) brought it back
to 24. Cluster B was completed: the symmetric-torus uniform-bound pair
(`torusEmbeddedTwoPoint_uniform_bound` / `torusEmbeddedTwoPoint_le_seminorm`) and the asymmetric pair
(`asymGaussian_second_moment_uniform_bound` / `asymGf_sub_norm_le_seminorm`) are all proved, the
latter via a GJ-aligned asym embedding `evalAsymAtFinSiteGJ := a_geom • evalAsymAtFinSite` mirroring
the symmetric `evalTorusAtSiteGJ`. Other Phase 2 discharges: `roughCovariance_sq_summable`,
`smoothVariance_le_log` (trivial-`C` form), the gaussian-field density bridge
`normalizedGaussianDensityMeasure_eq_normalizedQuadraticGaussianMeasure`, the GJ-aligned Gaussian
Fourier identity `normalizedGaussianDensityMeasure_linearFourier`, and
`torus_propagator_convergence_GJ`. Three further pphi2 axioms cleared by PR #14:
`fourierTransform_lp_eq_fourierIntegral` (private), `cylinderIR_uniform_exponential_moment`, and
`cylinderIR_os3` (refactored to consume explicit Green-moment / RP inputs). The embedding-
normalisation audit on `circleRestriction` was completed 2026-05-08. The remaining Stage-1 axioms
(Cluster A — Nelson dynamical-cutoff, Glimm–Jaffe Ch. 8) reduce to the same dynamical-cutoff Nelson
estimate (~6–8 wk per the Gemini estimate in `lattice-action-normalization-fix.md`).

On the `cylinder-isotropic-lattice` branch the isotropic `Z_Nt × Z_Ns` cylinder construction added
two deep-think-vetted analytic axioms (`asymChaosCutoffDecomposition`,
`asymInteracting_expMoment_volume_uniform`); `count_axioms.sh` reported 21 raw / 19 real, 0 sorries
there (`wickConstantAsym_eq_variance` and the per-cross-term L² bound `asymCanonicalCrossTerm_l2_sq_le`
became theorems, and `asymRoughError_variance` is proved on top of them); `MeasureHasGreenMomentBound`
is a theorem and `cylinderIso_OS_of_RP_OS2` gives cylinder OS0/OS1/OS2/OS3 modulo the separate
reflection-positivity and OS2-symmetry inputs (see `cylinder-conditional-inputs-provability.md`).

## Route B (T²_L) — discharge narrative

`torusEmbeddedTwoPoint_le_seminorm` was discharged 2026-05-08 via the `(a^d)⁻¹·(L/N)² = 1`
cancellation between `evalTorusAtSiteGJ` and `latticeCovarianceGJ`. Upstream resolutions
(`torus-route-gap-audit.md`): OS0's `osgood_separately_analytic` PROVED (Osgood's lemma, 1965 lines,
0 axioms); Gaussian OS0's `torusGeneratingFunctionalℂ_analyticOnNhd` PROVED (AM-GM induction); OS2
`evalTorusAtSite_timeReflection` / `evalTorusAtSite_latticeTranslation` PROVED in gaussian-field.

## Route B′ (asym torus → cylinder) — discharge narrative

UV limit (Step 1) completed: Route B's OS0–OS2 proofs adapted to the asymmetric case;
`asymGf_sub_norm_le_seminorm` and `asymGaussian_second_moment_uniform_bound` discharged 2026-05-08 via
the `evalAsymAtFinSiteGJ` embedding + the same cancellation pattern. IR limit (Step 2) in progress:
`limit_exponential_moment` (MCT + truncation + BC convergence) proved; uniform cylinder exponential
moment derived from the eventual Green-controlled torus moment hypothesis
`AsymTorusSequenceHasUniformGreenMomentBound` (with proved bridges from stronger pointwise / `Lt ≥ 1`
tail estimates); OS2 time reflection proved via characteristic-functional convergence (compact-support,
finite-rank, and general cylinder covariance convergence proved against a physically normalized
cylinder form from `cylinderGreen` by explicit temporal `2π` rescaling, with uniform bilinear seminorm
control); spatial translation exact at each finite `Lt`; OS3 transferred from the eventual pullback RP
hypothesis `CylinderMeasureSequenceEventuallyReflectionPositive` (with proved bridges from full-RP
statements to the matrixwise eventual input).

## Continuum-limit / foundations narrative

`measure_determined_by_schwinger` was discharged to a theorem on 2026-05-22 (continuum-limit moment
determinacy: finite exp-moment ⟹ entire MGF ⟹ equal moments force equal MGF ⟹ equal law; Cramér–Wold
lift — `MeasureUniqueness.lean`, `[propext, Classical.choice, Quot.sound]` only). `rough_error_variance`
became fully theorem-derived (same axiom set). `continuumMeasures_tight` (S'(ℝ^d) tightness) proved
(Mitoma–Chebyshev + `interacting_moment_bound` + `gaussian_second_moment_uniform`). `cylinderIR_os0`,
`analyticOn_generatingFunctionalC`, `continuum_exponential_moments`, `exponential_moment_schwartz_bound`,
`complex_gf_invariant_of_real_gf_invariant`, and the `os{0,1,4}_for_continuum_limit` wrappers
theorem-derived. The continuum-limit inheritance layer is split between
`ContinuumLimit/{AxiomInheritance,CharacteristicFunctional,TimeReflection}.lean`.
`prokhorov_configuration_sequential` (`Convergence.lean`) is a proved theorem using gaussian-field's
`prokhorov_configuration` (DM-basis embedding `Configuration ↪ ℕ → ℝ`, avoiding Polish/Borel); the old
axiomatized Polish/Borel instances were removed as inconsistent. Remaining continuum analytic debt as
of mid-2026: the mixed `L¹`/Green exponential-moment bridge `∫ exp(|ω f|) ≤ exp(c₁∫|f| + c₂G(f,f))`,
the coupled canonical characteristic-functional bridge `continuumMeasure 2 (N n) P (a n) mass → μ`
(`a_n → 0`, `(N n)·a n → ∞`), the spectral-gap-to-clustering input, and the Ward-identity `N`-uniform
polynomial-log `a²` bound for `rotationCFDefect` (the pointwise `rotationCFPointwiseDefect` API and
`tendsto_zero_pow_mul_one_add_abs_log_pow` are proved support layers).

---

## README front-matter status (archived 2026-06-07)

The README opening used to carry the in-flight workstream status verbatim; moved here so the README
can lead with orientation. Live plans: [`../planning/INDEX.md`](../planning/INDEX.md);
branch map: [`../BRANCHES.md`](../BRANCHES.md).

**Active workstream (cylinder).** The cylinder `S¹(L_s) × ℝ` φ⁴₂ construction on an isotropic
`Z_{N_t} × Z_{N_s}` lattice (single spacing `a`, `L_s = N_s·a` fixed, `N_t → ∞`) leaves the compact
torus behind to gain OS3 (reflection positivity) and OS4 (mass gap / clustering), toward OS
reconstruction → a Wightman QFT in 1+1d. `cylinderIso_OS_of_RP_OS2`
(`AsymTorus/AsymContinuumLimit.lean`) assembles cylinder OS0–OS3 modulo the remaining project axioms
(build green, 0 sorries).

**Last-axiom discharge architecture (the `Lt`-uniform exp-moment chain).**
- *Layer B1* complete 2026-05-31: cylinder transfer matrix → variance bound (`AsymL2Operator.lean`
  TM compactness + self-adjointness; `AsymJentzsch.lean` positivity-improving + simple ground;
  `AsymPositivity.lean` energy levels + mass-gap positivity; `AsymVarianceBound.lean`).
- *Layer A* (Newman MGF via Lee–Yang): `lee-yang` repo scaffolded, Phase 1 not implemented.
- *Layer B2* (`asymInteractingVariance_le_freeVariance_Lt_uniform`, `Lt`-uniformity): transfer-matrix
  Feynman–Kac route. Much done & axiom-clean by 2026-06-04 (abstract trace dictionary; φ⁴₂
  `TransferSystem` instance, PR #36; energy factorization; GaussianField asym density bridge,
  gaussian-field PR #3; measure factorization `μ_int.map sliceEquiv = pathMeasure`; abstract B4
  susceptibility engine, reflection-positivity PR #3; operator↔kernel link
  `asymTransferKernel_kPow_apply`). Remaining tail: the Hilbert–Schmidt trace-bridge layer +
  single-slice stability (`docs/B4B5-design.md`, `docs/transfer-instantiation-plan.md`). NB: the
  earlier "Option B / B1–B5 slice transfer" framing on branch `option-b-feynman-kac` is SUPERSEDED
  (see that doc's banner).
- *Layer C* (assembly): ~50 lines, blocked on A + B2.

**Lattice-action normalisation fix (early May 2026).** A missing `a^d` Riemann-sum prefactor on the
kinetic term (Gemini-vetted scaling analysis) was resolved and merged to `main`; the fix branch is
preserved as the `archive/fix/lattice-action-normalization` release tag. The Glimm–Jaffe-aligned
action `S = (a^d/2)⟨φ, M_a φ⟩` is the project default (`latticeCovarianceGJ`,
`gaussianDensity = exp(−(a^d/2)⟨φ, Qφ⟩)`); `Pphi2/Main.lean`'s OS0–OS4 chain proves theorems about
this textbook GJ-aligned measure. The Stage-1 / Cluster-A / Cluster-B axiom inventory was substantially
discharged via Workstream A (Phase-B Glimm–Jaffe Fourier estimates, complete 2026-05-16:
`smoothWickConstant_le_log_uniform_in_aN`, `canonicalRoughCovariance_pow_sum_le_uniform_in_aN` now
theorems) and Workstream C (gaussian-hilbert OU/Mehler, complete 2026-05-15). The remaining non-Mathlib
axiom on the T²_L OS0–OS2 critical path was `polynomial_chaos_exp_moment_bridge` (Workstream B; last
math blocker `wickPolynomial_lower_bound_general` resolved 2026-05-17).

**Roadmap docs (cylinder campaign):** `cylinder-master-plan.md` (master plan);
`cylinder-isotropic-lattice-redesign.md` (why the isotropic redesign);
`cylinder-isotropic-lattice-implementation.md` (phase-by-phase build);
`asym-fielddecomposition-redesign.md` (the §2 polynomial-chaos port);
`asym-cross-term-l2-discharge-plan.md` (✅ 2026-05-29);
`asym-chaos-cutoff-decomposition-discharge-plan.md` (UNIT 6+7);
`cylinder-conditional-inputs-provability.md` (input provability vetting);
`cylinder-os3-discharge-plan.md` (OS3 `hRP` discharge).
