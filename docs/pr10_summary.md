# PR #10 — Detailed Summary of Changes and Improvements

**Title:** Refactor continuum-limit axioms and enhance functional analysis support
**Author:** `or4nge19` (Matteo Cipollina)
**State:** DRAFT
**Stats:** +2330 / −1269, 32 files, 28 commits
**CI:** `lake build` ✅
**Axiom count:** pphi2 23 → 21 (net −2)

---

## 1. Structural reorganization

The old monolithic `OSProofs/OS2_WardIdentity.lean` split into four files, with most Ward/Characteristic/Inheritance content relocated and deduplicated:

| File | Role | Status |
|---|---|---|
| `OSProofs/OS2_WardIdentity.lean` | Ward anomaly chain + `rotation_invariance_continuum` (now a **theorem**) + lattice-level invariance | 6 axioms → **1** (`rotation_cf_pointwise_defect_polylog_bound`) |
| `ContinuumLimit/AxiomInheritance.lean` | OS0/OS1/OS4 inheritance packaged into bundle wrappers | was 0 axioms → **3** (`continuum_exponential_moment_green_bound`, `canonical_continuumMeasure_cf_tendsto`, `continuum_exponential_clustering`) |
| `ContinuumLimit/CharacteristicFunctional.lean` **(NEW)** | `Z[·]` infrastructure: complex analyticity, Z₂/reality, translation continuity, norm bound, clustering→ergodicity | 0 axioms, 529 lines |
| `ContinuumLimit/TimeReflection.lean` **(NEW)** | `continuumTimeReflection` + `distribTimeReflection` + weak-* continuity | 0 axioms, 82 lines |
| `InteractingMeasure/LatticeEuclideanTime.lean` **(NEW)** | Cyclic Euclidean-time shift on the `2×N` torus via `ZMod.valMinAbs` | 0 axioms, 79 lines |

Authorship is updated to `Authors: Matteo Cipollina, Michael R. Douglas` on `AxiomInheritance.lean`, `Backgrounds/EuclideanPlane.lean`, `GeneralResults/FunctionalAnalysis.lean`.

---

## 2. Axioms eliminated (converted to theorems)

The headline progress: 5 axioms dropped from the continuum-limit proof chain.

| Axiom → theorem | Derivation |
|---|---|
| `rotation_invariance_continuum` | Canonical-CF convergence + `anomaly_vanishes` + log-polynomial decay via `tendsto_nhds_unique` (proof in `OS2_WardIdentity.lean`) |
| `anomaly_bound_from_superrenormalizability` | Factored through the new pointwise `rotation_cf_pointwise_defect_polylog_bound` + `norm_integral_le_integral_norm` |
| `analyticOn_generatingFunctionalC` | Proved via `analyticOnNhd_integral` + `pairing_sum_complex_smul` + compact domination from `schwartzRe`/`schwartzIm` exponential moments |
| `continuum_exponential_moments` | Derived by scaling `f ↦ c • f` from `continuum_exponential_moment_green_bound` |
| `exponential_moment_schwartz_bound` | Derived from `continuum_exponential_moment_green_bound` + `continuumGreenBilinear_le_mass_inv_sq` (the Mathlib-side mass-gap bound, newly added in PropagatorConvergence.lean) |

Additional proved-theorem cleanups (moved from `OS2_WardIdentity` to `CharacteristicFunctional`): `pphi2_measure_neg_invariant`, `pphi2_generating_functional_real`, `generatingFunctional_translate_continuous`, `norm_generatingFunctional_le_one`, `os4_clustering_implies_ergodicity`, `complex_gf_invariant_of_real_gf_invariant`. No soundness changes for these — they are proved theorems in both main and PR, just relocated.

---

## 3. New axioms introduced (3)

All three are **self-audit (SA) only** in `docs/axiom_audit.md` — the PR explicitly flags them as pending targeted re-review. Locations:

| Axiom | File:line | Shape |
|---|---|---|
| `continuum_exponential_moment_green_bound` | `AxiomInheritance.lean:117` | `∫ exp|ω f| ≤ exp(c₁·‖f‖₁ + c₂·G(f,f))` |
| `canonical_continuumMeasure_cf_tendsto` | `AxiomInheritance.lean:327` | ∃ fixed `N₀`, `aₙ→0`: CF of `continuumMeasure 2 (N₀+1) P aₙ mass` → Z_μ |
| `continuum_exponential_clustering` | `AxiomInheritance.lean:351` | `‖Z[f + τ_a g] − Z[f]·Z[g]‖ ≤ C·exp(−m₀·‖a‖)` |
| `rotation_cf_pointwise_defect_polylog_bound` | `OS2_WardIdentity.lean:~605` | pointwise-L¹ form of the Ward anomaly bound |

`continuum_exponential_clustering` is not new content — it was moved from `OS2_WardIdentity`, functionally unchanged.

**Gemini deep-think verdicts (from this session):**
- #1 (Green-form): **SUSPICIOUS** — the `c₁·‖f‖₁` term is non-standard; textbook bound is `exp(½·G(f,f))` (Fernique) or `exp(C·G(f,f))` (Glimm-Jaffe via Hölder on `exp(−V)`), with Nelson sub-leading `K·G(f,f)^{1/2}`, never a separate L¹ term.
- #2 (Canonical CF bridge): **WRONG** — with `N` fixed as `a→0`, physical box `(N·a)^2→0`, the embedded distribution collapses to 0, CF→1, so the limit is δ₀ ∈ S'(ℝ²). Bypasses the IR/thermodynamic limit. Fix: couple `N_n→∞` with `a_n→0`.
- #3 (Pointwise Ward): **SUSPICIOUS** — Ward identity gives `‖∫(exp(iA)−exp(iB))dμ‖` via cancellations inside the integral; cancellations do not survive pointwise. The naive triangle bound `‖exp(iA)−exp(iB)‖≤|A−B|` gives `∫|⟨ω,f−R·f⟩|dμ` which does not scale as `a²`.

---

## 4. Mathematical content changes

### OS4_MassGap — cyclic torus separation
The old `two_point_clustering_from_spectral_gap` and `general_clustering_from_spectral_gap` axioms were **statement-corrected** to decay in the cyclic Euclidean-time separation `latticeEuclideanTimeSeparation N R = ((R : ZMod N).valMinAbs).natAbs` instead of the unbounded `(R : ℕ)`. The directed `R` form was unsound on a periodic torus (exponential decay in an unbounded linear coordinate contradicts periodicity).

New lattice infrastructure (`InteractingMeasure/LatticeEuclideanTime.lean`):
- `latticeEuclideanTimeShift N k : FinLatticeSites 2 N` — `k` lattice steps along Euclidean time
- `latticeConfigEuclideanTimeShift N k : Configuration → Configuration` — dual translate of configurations
- `latticeEuclideanTimeSeparation N k` — cyclic/geodesic separation, equals `min(k % N, N − k % N)`

`general_clustering_lattice` lost its unused `Nt` parameter and its `G` is now evaluated on the shifted configuration. `OS4_MassGap.lean` doc was rewritten with proper finite-volume caveats and a GRS reference to `refs/GRS1975-p2.md`.

Supporting theorem in `OS2_WardIdentity.lean`:
- `interactingLatticeMeasure_expectation_configEuclideanTimeShift` — `∫ G(τ_k ω) dμ = ∫ G dμ` for integrable G (the Cov(F, G∘τ_R) equivalence used by clustering)

### Log corrections in the anomaly bound
Both the prose in `OS2_WardIdentity.lean` and the inline docstrings in `Main.lean` were updated from the overclaim "no log corrections in d=2" to the correct "`O(a² |log a|^p)` in the super-renormalizable setting" (matches GJ Thm 19.3.1).

### Main.lean — renamed theorems reflecting scope
The "Wightman theorem" and "OS reconstruction" claims were renamed and redocumented to accurately describe their actual formal content:

| Before | After | Why |
|---|---|---|
| `os_reconstruction` | **`massParameter_positive`** (old name deprecated) | Conclusion is `∃ m₀ > 0` witnessed by the hypothesis `0 < mass` — not OS reconstruction |
| `pphi2_wightman` | **`pphi2_exists_os_and_massParameter_positive`** (old name deprecated) | No Wightman theory is actually constructed — this is `pphi2_exists` ∧ `massParameter_positive` |
| `pphi2_mass_gap` | **`bareMassParameter_positive`** (old name deprecated) | Same reason: it returns the input `mass`, not a derived mass gap |

Docstrings now explicitly disclaim that OS reconstruction and the Wightman axioms are not formalized here. This is purely honesty / correctness; zero downstream proof changes.

---

## 5. Generalized lemmas moved to `GeneralResults/`

Several local helpers in `AsymTorus/AsymTorusOS.lean` were generalized and promoted to project-wide results so the CF analytic/OS0 proofs can share them.

`GeneralResults/ComplexAnalysis.lean` (new):
- `compact_im_bound` — uniform imaginary-part bound on compact K ⊆ ℂⁿ (was `asymCompact_im_bound`, private)
- `compact_re_im_bound` — both parts uniformly bounded
- `exp_mul_add_le` — `exp(c(a+b)) ≤ exp(2ca) + exp(2cb)`
- `exp_mul_sum_le` — `exp(c·Σaᵢ) ≤ Σ exp(n·c·aᵢ)` (was `asymExp_mul_sum_le`, private)

`GeneralResults/FunctionalAnalysis.lean` (enhanced):
- **Logarithmic-decay lemmas (new):**
  - `tendsto_zero_mul_one_add_abs_log_pow` — `aₙ(1+|log aₙ|)^p → 0`
  - `tendsto_zero_pow_mul_one_add_abs_log_pow` — `aₙ^m(1+|log aₙ|)^p → 0` for `m ≥ 1`
  - `tendsto_zero_sq_mul_one_add_abs_log_pow` — m=2 corollary (directly consumed by `rotation_invariance_continuum`)
- **Characteristic-functional toolkit (new):**
  - `configuration_cexp_eval_integrable` — `exp(i⟨ω,f⟩)` always integrable on any finite Configuration measure (its norm is 1)
  - `configuration_expIntegral_re_eq_integral_cos` / `configuration_expIntegral_im_eq_integral_sin` — Euler decomposition
  - `configuration_cexp_eval_sub_integrand f g` — the difference `exp(i⟨·,g⟩) − exp(i⟨·,f⟩)` as an ℂ-valued observable
  - `configuration_cexp_eval_dist f g` — its pointwise norm
  - `norm_configuration_expIntegral_sub_le_integral_cexp_eval_dist` — generic `‖∫…‖ ≤ ∫‖…‖` defect estimate

These new CF helpers are also consumed by `EuclideanOS.lean` (for the background-level `generatingFunctional_re/im_eq_integral_cos/sin` theorems) and by `IRLimit/IRTightness.lean` and `TorusContinuumLimit/*.lean` — eliminating 4 duplicate local proofs.

`GaussianContinuumLimit/PropagatorConvergence.lean` (new theorem):
- `continuumGreenBilinear_le_mass_inv_sq` — `G(f,f) ≤ (2π)^{−d} · m^{−2} · ∫ f²` — the mass-gap L² estimate that bridges `continuum_exponential_moment_green_bound` to `exponential_moment_schwartz_bound`.

---

## 6. Infrastructure strengthening

### `IsPphi2Limit` — already present, CF convergence clause is key
The abstract marker predicate `IsPphi2Limit` (defined in `ContinuumLimit/Embedding.lean`, unchanged by this PR) bundles approximation data: ν_k (probability measures), a_k → 0, moment convergence, **characteristic-functional convergence**, Z₂ symmetry, translation invariance (eventually), weak convergence on bounded continuous functions, and reflection positivity of the approximants. This PR newly consumes the CF convergence clause in `canonical_continuumMeasure_cf_tendsto` (albeit unsoundly, as flagged).

### `Backgrounds/EuclideanPlane.lean` — better Mathlib layering
Added `@[simp]` equalities showing every `Continuum*` abbreviation is definitionally a Mathlib type (`EuclideanSpace`, `SchwartzMap`, `Configuration`, etc.). Makes notational goals discharge by `simp`:
- `ContinuumSpaceTime_eq`, `ContinuumTestFunction_eq`, `ContinuumComplexTestFunction_eq`, `ContinuumFieldConfig_eq`, `ContinuumOrthogonalGroup_eq`, `planeBackground_dim`

New structural theorems in the background layer:
- `action_apply`, `actionComplex_apply`, `continuumEuclideanAction_apply`, `continuumEuclideanActionComplex_apply` — all `(Mf)(x) = f(g⁻¹·x − g.t)` characterizations
- `inversePointAction_translationMotion` — pure translation is subtraction
- `translate_apply`, `translateComplex_apply` — simplified proofs using the above
- In `EuclideanPlane2D.lean`: `translate_timeTranslationVector2_eq_timeTranslationSchwartz_neg` bridging the `translate`/`timeTranslationSchwartz` sign conventions

### `EuclideanComplex.lean` — massively simplified
`schwartzOfReal` went from a hand-rolled 30-line `SchwartzMap.mk` with full decay bounds to a one-liner `f.postcompCLM Complex.ofRealCLM`. Same treatment for `schwartzRe`, `schwartzIm` in `EuclideanOS.lean`.

New simp lemmas:
- `schwartzOfReal_add`, `schwartzOfReal_real_smul`
- `schwartzRe_ofReal_add_real_smul`, `schwartzIm_ofReal_add_real_smul`
- `schwartzRe_complex_smul`, `schwartzIm_complex_smul`
- `schwartzRe_sum_complex_smul`, `schwartzIm_sum_complex_smul` (crucial for complex-analytic generating-functional proofs)
- `pairing_sum_complex_smul` — `⟨ω, Σ zᵢ Jᵢ⟩_ℂ = Σ zᵢ · ⟨ω, Jᵢ⟩_ℂ` as Re/Im decomposition

Plus `schwartz_decompose_continuumEuclideanActionComplex`, a simple specialization for the `Continuum*` names.

### `TimeTranslation.lean` — cleaner algebra
Rewrote `timeShiftConst` decomposition via `unitTimeDir = EuclideanSpace.single timeIndex 1`:
- `norm_unitTimeDir = 1`
- `timeShiftConst_eq_smul_unitTimeDir`
- `timeShift_eq_add_smul_unitTimeDir`, `timeShift_eq_fun_add_smul_unitTimeDir`
- `timeTranslationSchwartzCLM_apply`
- `timeTranslationSchwartz_apply_add_smul_unitTimeDir`, `timeTranslationSchwartz_eq_fun_add_smul_unitTimeDir`

These let `timeShift_hasTemperateGrowth`, `iteratedFDeriv_timeTranslationSchwartz`, and the continuity lemma `continuous_timeTranslationSchwartz` simplify substantially (calc-block rewrites).

### `PropagatorConvergence.lean` — explicit proofs replacing simp chains
Rewrote `latticeModeCoeffCLM_apply`, `latticeGreenBilinearRightCLM_apply`, and the proof of `latticeGreenBilinear_tendsto_continuum` to avoid flaky `simp` applications of missing rewrite lemmas — now uses explicit `ContinuousLinearMap.sum_apply`/`smul_apply` unfolding and a manual `convert` into `GaussianField.tendsto_of_symmetric_basis_tendsto`. Also added a manual `hlast` derivation in `continuumKernel_eq_scaled` where `ring_nf` had been overreaching.

Renamed the active remaining axiom: `latticeGreenBilinear_tendsto_continuum` → `latticeGreenBilinear_basis_tendsto_continuum` (it's now the basis-pair version; the full-function statement is derived).

### `RPTransfer.lean` — minor
`omit [NeZero N] in` added to `fieldTimeReflection_single`; import changed from `AxiomInheritance` to the new `TimeReflection`. Proof of `latticeEmbedLift_intertwines_reflection` cleaned up via `change` + direct `rw`.

### `AsymTorusOS.lean` — dedup against new `GeneralResults`
Replaced local private `asymGf_re/im_eq_cos/sin_integral` 15-line proofs with 1-line `simpa using configuration_expIntegral_re/im_eq_integral_cos/sin`. Replaced `asymCompact_im_bound`, `asymExp_mul_sum_le` references with the promoted `compact_im_bound`, `exp_mul_sum_le`.

### `TorusInteractingOS.lean`, `TorusOSAxioms.lean`, `IRLimit/IRTightness.lean` — dedup
Same pattern: local Re/Im-integral-of-CF proofs replaced by `simpa using configuration_expIntegral_…` calls.

### `GaussianContinuumLimit/GaussianLimit.lean` — doc
`gaussianLimit_isGaussian` no longer labeled `(axiom)` — it's a theorem.

---

## 7. Documentation updates

- `README.md` — narrative around Wightman/OS reconstruction softened; axiom count table refreshed
- `ROUTES.md` — minor
- `status.md` — regenerated from `count_axioms.sh`, inventory tables now reflect the file split. **However**, timestamp says 2026-04-07 18:18 — stale vs today (2026-04-19). Needs refresh before merge.
- `docs/axiom_audit.md` — Phase 5 entirely rewritten; the 3 new axioms flagged as SA-only with "request fresh DT/GR-style review" action item
- `docs/axiom_proof_plans.md`, `docs/os_axioms_lattice_plan.md`, `docs/same_measure.md` — updates for renamed axioms, cyclic torus wording
- `summary/Pphi2/Main.md`, `summary/Pphi2/OSProofs/OS4_MassGap.md`, `summary/Pphi2/GaussianContinuumLimit/GaussianLimit.md` — auto-generated refreshes

---

## 8. Net impact

### What's unambiguously better
- 5 axioms converted to theorems (real progress on the Ward/analytic chain)
- Clean file split for Ward / CF / TimeReflection / AxiomInheritance
- Reusable FA toolkit for CF decomposition and compact-set bounds
- Boilerplate-free `schwartzOfReal`/`schwartzRe`/`schwartzIm` via `postcompCLM`
- Correct log factors in the anomaly bound prose
- Cyclic torus separation in OS4 clustering (previously unsound for `R ≥ N`)
- Honest naming in `Main.lean` (`massParameter_positive` not `os_reconstruction`)
- Improved Mathlib↔project definitional-equality discipline in `Backgrounds/EuclideanPlane`
- Single OS0/OS1 analytic input (`continuum_exponential_moment_green_bound`) replacing two

### What regresses or needs attention
- **Axiom 2 (`canonical_continuumMeasure_cf_tendsto`) is unsound** as stated (fixed-`N` UV limit gives δ₀, not P(Φ)₂). Fix requires coupled `(N_n, a_n)` with `N_n·a_n → ∞`; the Ward proof then needs the anomaly bound uniform in `N`. Worked correction in `/tmp/canonical_cf_tendsto_fix.lean`.
- **Axiom 1 (`continuum_exponential_moment_green_bound`)** has the wrong bound shape. Drop `c₁·‖f‖₁` to match Fernique/Glimm-Jaffe.
- **Axiom 3 (`rotation_cf_pointwise_defect_polylog_bound`)** is stronger than what the Ward identity delivers. Either revert to the integrated-CF form or justify the pointwise `a²` separately.
- Stale timestamp in `status.md`.
- The three new axioms need `deep_think_gemini` review per project convention (`CLAUDE.md`).

### Count ledger
- Main: 23 axioms (15 pphi2 files with axioms)
- PR: 21 axioms, same 15 files (one shifted: OS2_WardIdentity 6→1, AxiomInheritance 0→3, OS4_MassGap unchanged at 2)

---

## 9. Files changed

```
Pphi2/AsymTorus/AsymTorusOS.lean                    (dedup via GeneralResults)
Pphi2/Backgrounds/EuclideanPlane.lean               (Mathlib layering + apply lemmas)
Pphi2/Backgrounds/EuclideanPlane2D.lean             (timeShift ↔ translate bridge)
Pphi2/ContinuumLimit/AxiomInheritance.lean          (3 new axioms + 3 new theorems)
Pphi2/ContinuumLimit/CharacteristicFunctional.lean  (NEW; 529 lines)
Pphi2/ContinuumLimit/RPTransfer.lean                (import tweak; omit NeZero)
Pphi2/ContinuumLimit/TimeReflection.lean            (NEW; 82 lines)
Pphi2/EuclideanComplex.lean                         (schwartzOfReal one-liner + simp lemmas)
Pphi2/EuclideanOS.lean                              (schwartzRe/Im one-liner + Z[·] re/im lemmas)
Pphi2/GaussianContinuumLimit/GaussianLimit.lean     (doc)
Pphi2/GaussianContinuumLimit/PropagatorConvergence.lean  (basis-pair axiom + L² bound)
Pphi2/GeneralResults/ComplexAnalysis.lean           (compact bounds + exp_mul_sum_le)
Pphi2/GeneralResults/FunctionalAnalysis.lean        (log decay + CF-defect API)
Pphi2/IRLimit/IRTightness.lean                      (dedup)
Pphi2/InteractingMeasure/LatticeEuclideanTime.lean  (NEW; 79 lines)
Pphi2/Main.lean                                     (renames + docstrings)
Pphi2/OSAxioms.lean                                 (doc layering note)
Pphi2/OSProofs/OS2_WardIdentity.lean                (refactor; rotation_invariance_continuum proved)
Pphi2/OSProofs/OS4_MassGap.lean                     (cyclic torus separation)
Pphi2/OSforGFF/TimeTranslation.lean                 (unitTimeDir cleanup)
Pphi2/TorusContinuumLimit/TorusInteractingOS.lean   (dedup)
Pphi2/TorusContinuumLimit/TorusOSAxioms.lean        (dedup)
README.md / ROUTES.md / status.md                   (counts + narrative)
docs/axiom_audit.md                                 (Phase 5 rewritten)
docs/axiom_proof_plans.md                           (updates)
docs/os_axioms_lattice_plan.md                      (updates)
docs/same_measure.md                                (updates)
summary/Pphi2/GaussianContinuumLimit/GaussianLimit.md (refresh)
summary/Pphi2/Main.md                               (refresh)
summary/Pphi2/OSProofs/OS4_MassGap.md               (refresh)
```
