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
