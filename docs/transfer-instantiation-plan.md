# pphi2-side instantiation of the abstract OS transfer bridge — plan (2026-06-03)

## Status machine (plan-loop; re-read every cycle)

**DECISION 2026-06-03: Option B (slice transfer matrix), per the axiom-vetting verdict.**
The finite-torus GNS instantiation (M1–M5 below) is a DEAD END (`τPos` false on the
periodic torus — Gemini 3.1-pro). Option B keeps the finite torus and uses pphi2's
EXISTING slice operator `asymTransferOperatorCLM` (correctly normalized, `bb4b86d`) +
the proved gap (`asymGappedTransfer'`, `susceptibility_le`); the one missing theorem is
the **Feynman–Kac trace dictionary** (measure correlations = transfer-operator traces),
which IS the 4-step factorization already scoped in
`layer-B2-discharge-plan.md` → "Feynman–Kac bridge — scoping". Active plan = B1–B5:

- [ ] B1. Slice iso `Configuration (AsymLatticeField Nt Ns) ≃ (ZMod Nt → SpatialField Ns)`, measure-compatible   status: todo   deps: []   note: `Configuration E = WeakDual ℝ E` (cylindrical σ-algebra), so this is a measurable pushforward on `WeakDual` (dualize a test-space iso `AsymLatticeField ≃ ZMod Nt × Fin Ns → ℝ` via `Equiv.curry` + `ZMod.finEquiv`), not a plain curry. Real but bounded.
- [ ] B2. Measure factorization: `dμ_int ∝ ∏_t [w(ψ_t)·G(ψ_t−ψ_{t+1})·w(ψ_t)]` with `w = exp(−(a²/2)·spatialAction)` (corrected weight), `G = transferGaussian` — the Gaussian time-slicing. THE CRUX.   status: blocked   deps: [B1]   note: show `latticeCovarianceAsymGJ` = the slice-decomposed (time-coupling + a²·spatialAction) quadratic form.
- [ ] B3. Trace dictionary: `∫ A(ψ_0)·B(ψ_n) dμ = Tr(M_A Tⁿ M_B T^{Nt−n})/Tr(T^{Nt})`; connected/vacuum-projected form `∑ ⟨v_f, T̂^{|t−t'|} v_f⟩`   status: blocked   deps: [B2]   note: `T = asymTransferOperatorCLM`.
- [ ] B4. Apply `asymGappedTransfer'`.`susceptibility_le` ⟹ `Lt`-uniform bound on the time-summed correlator   status: blocked   deps: [B3]   note: mechanical given B3 + the proved gap.
- [ ] B5. Identify with `C·Var_free` via the `1/a` cancellation; B1-Nelson = `a`-uniformity   status: blocked   deps: [B4]   note: discharges `asymInteractingVariance_le_freeVariance_Lt_uniform`.

**PROGRESS 2026-06-04 (branch `transfer-instantiation`).** Abstract dictionary **B3 DONE**
(reflection-positivity `TransferSystem.lean`, merged `61cd790`). pphi2 **B2 instantiation:
`asymTransferSystem : TransferSystem (SpatialField Ns)` is now FULLY PROVED, sorry-free,
axiom-clean** (`fda6be7` structural fields; `741c6aa` the two Gaussian-integrability fields
via `transferGaussian_le_one` ⟹ `k ≤ w·w` ⟹ `openChainProduct ≤ w(x)w(y)∏w(qⱼ)²`,
dominated by an integrable `∏w²`). So the dictionary (`partition_eq_trace`,
`twoPoint_dictionary`) now applies to pphi2's cylinder off the shelf.

**PROGRESS 2026-06-04 (cont.).** B1 slice iso landed: `asymSliceEquiv : AsymLatticeField Nt Ns
≃ₗ (ZMod Nt → SpatialField Ns)` (`71fc7be`, sorry-free, pure Mathlib `LinearEquiv`).

**The B2 "measure↔operator bridge" — CORRECTED decomposition (the key finding, 2026-06-04).**
pphi2's own B2-axiom docstring calls this "the interacting Källén–Lehmann/Feynman–Kac
representation — the un-formalized measure↔operator bridge — a more-fundamental axiom-to-be."
It is NOT new-infrastructure-from-scratch: GaussianField **already has the analogous bridge
for the SQUARE lattice** (`GaussianField/Density.lean`):
  - `evalMapMeasurableEquiv` — the `Configuration (FinLatticeField) ≃ᵐ FinLatticeField`
    (WeakDual↔coordinate) measurable equiv;
  - `quadraticGaussianMeasure Q = volume.withDensity exp(−½⟨φ,Qφ⟩)` and
    `normalizedGaussianDensityMeasure_eq_normalizedQuadraticGaussianMeasure` — the abstract
    `GaussianField.measure` **= Lebesgue-density Gaussian** identity;
  - `gaussianDensity_eq_exp_spectral` / `SpectralCovariance` — the precision quadratic form.
The asym lattice (`AsymLatticeField`, `latticeCovarianceAsymGJ`) is a *separate type* with
**no** asym analogue yet (confirmed by grep). So the crux = a **bounded PORT**, not invention.

**REMAINING sub-pieces (all that stands between here and the deliverable):**
- ✅ **operator side** — proved abstract dictionary (`twoPoint_dictionary`) + sorry-free
  `asymTransferSystem`; **DONE**.
- ✅ **B1 slice iso** (`asymSliceEquiv`); **DONE**.
- ⛏ **(crux-1) asym density bridge** — port `Density.lean`'s square-lattice
  `evalMapMeasurableEquiv` + `normalizedGaussianDensityMeasure_eq_normalizedQuadraticGaussianMeasure`
  to `AsymLatticeField`/`latticeCovarianceAsymGJ`. Lands `interactingLatticeMeasureAsym` as a
  Lebesgue-density measure `(1/Z)·exp(−½⟨φ,Q_asym φ⟩−V_int) dλ` on the coordinate space. **The
  heaviest piece — a GaussianField (dependency) development.**
- ✅ **(crux-2) energy factorization — DERIVED + VETTED** (Gemini deep-think, 2026-06-04; see
  [`crux2-energy-factorization.md`](crux2-energy-factorization.md)). Result: `dμ_int/dλ =
  (1/Z)∏_t k(ψ_t,ψ_{t+1})` **EXACTLY**, so `μ_int.map sliceEquiv = asymTransferSystem.pathMeasure`
  as normalized measures with **no residual `a`-rescaling**. The pivotal `a`-power: the covariance
  is supplied as the **square-root** operator (`covariance T f g = ⟨Tf,Tg⟩`, `T = a⁻¹Q^{−1/2}`),
  so the free **precision is `a²Q`** (NOT `aQ`) — then the `a²/2` weight cancels `Δ_a`'s `a⁻²` to
  give coefficient `1` on `timeCoupling` (the `a^{d−2}=a⁰` feature of `d=2`), and the interaction
  `a²·Σ:P:` matches on both sides. **The `1/a` cancellation lives in B5's torus↔lattice
  test-function map (`asymLatticeTestFnIso = a • evalAtSite`), not here.**
  **FORMALIZED (2026-06-04, `AsymEnergyFactorization.lean`, sorry-free, axiom-clean):** the
  action/exp level — `energy_exponent_factorization` (the `−log` identity) and
  `periodicPathDensity_asymTransferKernel_eq_exp` (`∏_t k = exp(−action)`). **Remaining = the
  measure-level steps (asym Gaussian density `= exp(−(a²/2)⟨φ,Qφ⟩) dλ`, then `μ_int.map
  sliceEquiv = pathMeasure`), which route through crux-1 — the where-to-develop fork.**
- **B3/B4** — `kPow asymTransferKernel d` = `asymTransferOperatorCLM`'s `d`-th power kernel;
  `(ω f)² = Σ_{t,s} ⟨f_t,ψ_t⟩⟨f_s,ψ_s⟩` ⟹ `twoPoint_dictionary` + `susceptibility_le` (proved
  gap) ⟹ `Lt`-uniform correlator bound. Mechanical given crux-1/2.
- **B5** — identify with `C·Var_free` via the `1/a` cancellation; B1-Nelson = `a`-uniformity.

### Superseded (finite-torus GNS — DEAD END, kept for the record)
- [x] M1/M2/M3 scaffold (`Pphi2AsymTTS`, `93ae9f0`) — UNSOUND (`τPos` false); not on the path. M4/M5 dropped.

### Road ahead (honest sizing)
B1–B5 = the finite-torus **Feynman–Kac trace dictionary**, the genuine hard core of B2.
B3/B4/B5 are mechanical/short given B2 + the proved gap + B1-Nelson; **B2 (the Gaussian
time-slicing factorization: `latticeCovarianceAsymGJ` = slice-decomposed
time-coupling + `a²·spatialAction`) is the crux** — a multi-week formalization touching
the `WeakDual` measure structure. Prereqs all in place: corrected weight (`bb4b86d`),
proved gap (`asymGappedTransfer'`/`susceptibility_le`), `susceptibility_le` engine
(reflection-positivity `0c3b961`). This is a dedicated effort, not a single pass; the
env Codex is flaky for grinding it. Pickup-ready.

**Loop checkpoint (2026-06-03):** scaffold landed (typed `Pphi2AsymTTS` + structural
lemmas, committed `93ae9f0`); 5 analytic sorries + M4 + M5 remain.

## ⚠⚠⚠ AXIOM VETTING (Gemini 3.1-pro, 2026-06-03): finite-torus GNS instance is UNSOUND

Vetted two proposed textbook helper axioms for correctness AND later-provability:
- **A_RP** (`Pphi2Asym_reflectionPositive`, OS3 RP in abstract form): **GREEN — correct,
  canonical, non-vacuous, dischargeable.** Porting the square `lattice_rp` (V₊+V₀+V₋
  chessboard) + a density adapter (mPos-`Lp` ↔ `PositiveTimeSupported` representatives,
  via continuity) suffices; the asym `Nt≠Ns` case is the SAME proof. Cite GJ Ch 6.1 /
  Simon III.3. KEEP.
- **A_contract** (reflection-seminorm contraction): the inequality is true, but the axiom
  is **ILL-POSED in the finite-torus GNS setting — REJECTED.** Root cause = the `τPos`
  structural flaw is REAL: on a finite *periodic* torus no shift preserves a strict
  positive-time half-region `{0<t<Nt/2}` (`+1` leaks the boundary), so `T:[f]↦[f∘τ]` is
  **not a well-defined operator** on `H_phys`. ⟹ **`Pphi2AsymTTS` cannot be a valid
  `TimeTranslatedSystem` on the finite torus** — the `τPos` field is FALSE, so M3/M4/M5
  as built are a DEAD END. (The Codex scaffold sorried `τPos` precisely because it's false.)

**Reframe (required) — two sound settings, pick one:**
- **(A) Infinite cylinder** `ℤ × ZMod Ns` (`Nt→∞`): positive-time `= {t>0}`, the `+1` shift
  preserves it ⟹ `τPos` holds, `T` well-defined, A_contract well-posed. Standard GJ
  setting; matches B2's `Lt→∞` regime. Cost: build/relate the `Nt→∞` cylinder measure.
- **(B) Slice transfer matrix** on `L²(ℝ^Ns)` with `Z = Tr(T^Nt)`, prove `RP ⟺ T`-positivity
  + the correlation = trace dictionary on the finite torus. **This is what pphi2 ALREADY
  has** (`asymTransferOperatorCLM` on `L2SpatialField` + the proved gap `asymGappedTransfer'`).
  The abstract GNS bridge is NOT the right vehicle here; the missing piece is the
  measure↔trace (Feynman–Kac) dictionary, sound on the finite torus.

Status updates: M3 `τPos`/`contraction` and M4/M5 are **blocked: finite-torus GNS instance
unsound — reframe to (A) or (B) (human decision)**. A_RP stays valid in both reframings.



Goal: discharge `asymInteractingVariance_le_freeVariance_Lt_uniform`
(`AsymExpMomentDischarge.lean:206`) by instantiating the abstract bridge
`ReflectionPositivity.TransferConstruction` (D0–D3, merged to reflection-positivity
`main` `0c3b961`; pphi2 pin bumped) for the asym φ⁴₂ cylinder.

**Unblocked (2026-06-03):** pphi2 pin → `0c3b961`; `import
ReflectionPositivity.TransferConstruction` builds (dep compiles against pphi2's mathlib).

## The abstract API we consume (reflection-positivity)

- `TimeTranslatedSystem Ω` (extends `ReflectionSystem`): fields `μ, θ, mp, inv, mPos, le,
  rp`, plus `τ, τmp, τθ (θτθ=τ⁻¹), τPos, contraction`.
- `transferOperator : H_phys →L[ℝ] H_phys`, `transferOperator_selfAdjoint`, `vacuum`.
- D2 `reflectionCorrelation_eq_inner_T_pow`: `⟪[f],Tⁿ[g]⟫ = ∫ f·(g∘τ^[n]∘θ) dμ`.
- D3 `reflectionCorrelation_susceptibility_le (G : GappedTransfer H_phys)
  (hGT : G.T = transferOperator) (hv : ⟪G.vacuum,[v]⟫=0) (N) :
  ∑_{n<N}|∫ v·(v∘τ^[n]∘θ)dμ| ≤ ‖[v]‖²/(1−G.gap)`.

## Milestones (sequenced; ⚠ = substantive, the rest mechanical)

### M1 — asym lattice reflection positivity in the abstract form ⚠
pphi2 has `OSProofs/OS3_RP_Lattice.lean` `lattice_rp` : `∫ F(φ)·F(Θφ) dμ ≥ 0` for
`PositiveTimeSupported` F on the **square** `ZMod N × ZMod N` (V₊+V₀+V₋ decomposition +
`gaussian_rp_with_boundary_weight`; GJ Ch 6.1 / Simon III.3). Needed:
- (a) **Port to asym** `ZMod Nt × ZMod Ns` (the proof technique is dimension-agnostic;
  check whether an asym/cylinder version already exists or `cylinderIso_OS_of_RP_OS2`'s
  RP input is dischargeable from the square via the embedding).
- (b) **Adapter to `IsReflectionPositive Ω m0 μ θ mPos`**: convert pphi2's
  "`PositiveTimeSupported` raw function F" formulation to the abstract one
  (`mPos`-measurable `f : Lp`, `∫ f·(f∘θ) dμ ≥ 0`). Define `mPos` = the sub-σ-algebra
  generated by positive-time site evaluations; show `PositiveTimeSupported` ⇔
  `mPos`-measurable (for the relevant class), and bridge `F(Θφ)` with `f∘θ`.

### M2 — the `θ` involution + `mPos` on `Configuration (AsymLatticeField Nt Ns)`
- `θ : Configuration → Configuration` from `timeReflectSites` (pphi2 has the site map +
  `asymInteractingLatticeMeasure_timeReflection_invariant` ⟹ `mp : MeasurePreserving θ μ`;
  `inv` from `timeReflectSites` involutivity).
- `mPos` = `MeasurableSpace.comap` of positive-time evaluations; `le : mPos ≤ m0`.

### M3 — assemble `TimeTranslatedSystem` for the asym cylinder
- `τ` = time shift (`ZMod Nt` +1 in time); `τmp` (measure shift-invariance, OS2);
  `τθ : θτθ=τ⁻¹` (site-level identity); `τPos` (shift preserves positive-time — note: only
  for shifts that keep support positive; may need the half-period / cylinder convention);
  `contraction` (free: the lattice transfer is a bounded/finite Gaussian contraction —
  derivable, or take as the supplied field).
- Yields `Pphi2AsymTTS : TimeTranslatedSystem (Configuration (AsymLatticeField Nt Ns))`.

### M4 — the operator-coincidence ⚠⚠ (the hard core; = the old "Feynman–Kac" step)
Identify `Pphi2AsymTTS.physicalHilbertSpace` / `transferOperator` with `L2SpatialField Ns`
/ `asymTransferOperatorCLM` (now correctly normalized, `bb4b86d`):
- a unitary `H_phys ≃ₗᵢ L2SpatialField Ns` intertwining `transferOperator` with the
  normalized `asymTransferNormalized`;
- transport the proved gap (`asymGappedTransfer'`) to a `GappedTransfer H_phys` with
  `G.T = transferOperator`, satisfying D3's `hGT`.
This is the genuine time-slicing content (a single GNS-side computation; the abstract
correlation identity D2 means we do NOT redo the Gaussian Fubini — we match the operator
that already computes the correlations). **Largest piece.**

### M5 — variance connection + `1/a` cancellation
- Connect D3's LHS `∑|∫ v·(v∘τ^[n]∘θ)dμ|` to `∫ (ω f)² dμ_int` for the test function `f`
  (the field-excited vector `v` = `f` projected off vacuum; mean-zero by evenness).
- Identify `‖[v]‖²/(1−gap)` with `C·Var_free(f)` via the `1/a` cancellation (see
  `[[pphi2-b2-adapter-plan]]`: never evaluate `1/(1−gap)` standalone; form the int/free
  ratio first). **B1 supplies the `a`-uniformity**; gap supplies `Lt`-uniformity.

## Dependencies / sequencing
M2 → M3 (M3 needs θ, mPos). M1 feeds M3's `rp`. M4 needs M3 (the TTS). M5 needs M4 (the
GappedTransfer) + D3. M1 and M2 are independent and can go first. M4 is the critical path.

## Risks
- M1(b) adapter (raw-function RP ↔ abstract `lpMeas` RP) — measure-theoretic plumbing.
- M3 `τPos`/`τθ` on the periodic cylinder — the time-shift vs positive-time-support
  interaction needs the right cylinder convention.
- M4 — the operator-coincidence; the hard mathematical core (weeks).
