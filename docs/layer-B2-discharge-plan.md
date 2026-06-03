# Layer B2 discharge plan — Lt-uniform interacting variance bound

*Refined 2026-06-02 (branch `b2-kallen-lehmann`). Supersedes the chessboard
framing in the `asymInteractingVariance_le_freeVariance_Lt_uniform` docstring.
The transfer-matrix spectral gap this plan rests on is now **proved**.*

## RECONCILED ROUTE (read first): B1 ⊕ gap, not a fresh representation

The authoritative plan is the **B1 ⊕ gap** route already stated in
`Pphi2/AsymTorus/AsymVarianceBound.lean`'s architectural note: B1
(`asymInteractingVariance_le_freeVariance_torus`, **proved** via density-transfer
/ Nelson **hypercontractivity**) gives `Var_int ≤ C(Lt)·Var_free` — `a`-uniform,
norm-correct, but **per-`Lt`**; B2 upgrades `C(Lt)` to a **`Lt`-uniform** constant
using the now-proved transfer-matrix gap (`asymGappedTransfer'` / `susceptibility_le`).

Why this is the right framing (session reasoning + two vettings, 2026-06-02):
- **UV / spatial-Sobolev matching is already done by B1** (Nelson hypercontractivity),
  *not* by a transfer-matrix representation and *not* by Nelson *symmetry* (the 90°
  rotation is a red herring here — it relocates the problem to a swapped-extent
  thermodynamic gap).
- **The gap supplies only the `Lt`/IR uniformity** (clustering; volume-independent,
  unlike B1's extensive Nelson constant).
- The concrete remaining hard step is the **interacting-vs-free resolvent / Toeplitz-form
  comparison** `⟨Q,(1−T̂_int)⁻¹Q⟩ ≤ C·⟨Q,(1−T̂_free)⁻¹Q⟩` that turns B1's `C(Lt)` into
  a `Lt`-uniform `C ≈ m_free/m_int`. (The field-vectors `Q` carry the equal-time
  `H^{−1/2}` covariance, so the naive `L²`-vs-`H⁻¹` mismatch is softened; the danger
  is crudely Young-bounding the time sum and discarding the `p_t` structure.)

**The "interacting Källén–Lehmann *representation* axiom + cyclic-Young" framing in
the sections below was a DETOUR** — both Codex and Gemini-3.1 flagged it (norm
mismatch; false mode-by-mode domination). Keep the sections for the vetting record,
but the live plan is B1 ⊕ gap (resolvent comparison). Older docs
(`asym-interacting-expmoment-volume-uniform-discharge-plan.md`,
`asym-l2-operator-port-scoping.md`) use a yet-earlier split (B1 per-`a`, B2 = UV
chessboard) that is itself superseded now that B1 is `a`-uniform.

## Step B design — CORRECTED 2026-06-03 (code map): B2 = B1 ⊕ gap ⊕ Feynman–Kac bridge

**The pinned B2 work is the Feynman–Kac measure↔transfer-operator bridge — NOT a new
textbook axiom, and NOT FSS.** Reading the actual code (`AsymExpMomentDischarge.lean:206`,
`AsymVarianceBound.lean`, the `ReflectionPositivity` dep) settles the architecture:

- **The B2 target is real-space, per-test-function**: `∫(ω f)² dμ_int ≤ C·∫(ω g)² dμ_free`
  for arbitrary `f : AsymTorusTestFunction Lt Ls`, `C` uniform in `Lt`, `Ls` fixed.
  pphi2 has **no momentum-space / Fourier layer** (`φ̂(k)` is not a random variable here).
- **B2 fixes `Ls`, sends `Lt → ∞`.** At fixed `Ls` the spatial momenta are discrete and
  gapped by the box (`|k_s| ≥ 2π/Ls > 0`) — **no spatial infrared problem**. The only
  dangerous direction is **time** (`Lt`), controlled by the **already-proved
  transfer-matrix mass gap** (`asymGappedTransfer'`, `susceptibility_le`, `Lt`-uniform).
- So B2's two uniformity directions are exactly the established **B1 ⊕ gap** split:
  **time (`Lt`) → proved gap**; **space/UV (`a→0` at fixed `Ls`) → B1 (already
  `a`-uniform)**. No new textbook input is required.

**The genuine missing piece is the Feynman–Kac bridge** (the deferred
`transfer-operator-construction-todo`): expressing `∫(ω f)² dμ_int` as the
time-correlation sum `Σ_{t,t'} f̃(t) f̃(t') ⟨g, T̂^{|t−t'|} g⟩` (with `g ⊥ vacuum` the
spatially-smeared field-excited vector, mean-zero by evenness) so the proved gap's
`susceptibility_le` gives the `Lt`-uniform bound, and B1 supplies the `a`-uniform
interacting-vs-free spatial comparison. See "Feynman–Kac bridge — scoping" below.

**FSS infrared bound is PARKED for the `Ls → ∞` step, not B2.** The Fröhlich–Simon–
Spencer Gaussian-domination bound (`⟨φ̂(k)φ̂(−k)⟩_int ≤ 1/(2E(k))`, `k≠0`) is the right
tool for the *spatial* infinite-volume limit, where small spatial momenta must be
controlled. It is a momentum-space statement and pphi2 has no Fourier layer to host
it. Full vetted statement + citation + drop-in Lean signature saved in
**`docs/fss-infrared-bound-spec.md`**. (Gemini deep-think 2026-06-03 ranked it #1 for
the general "interacting ≤ free two-point, uniform" question — correct, but that is
the spatial-infrared problem, a *superset* of what B2 needs. Do not add a free-floating
momentum-space axiom: it would have no consumer and would not discharge B2.)

**Candidate C — Glimm–Jaffe Ch. 9 `N_τ` relative form bound (DEMOTED to fallback).**
`H_free ≤ c₁H_int + c₂` + gap + operator-monotone inverse ⟹ `H_int⁻¹ ≤ C·H_free⁻¹`.
Mathematically valid, but deep-think rates it **low-faithfulness as a *lattice*
axiom**: GJ Ch. 9 develops it in continuum Fock space with momentum cutoffs, so
citing an `a`-uniform *lattice* form is an impedance mismatch (continuum statement)
or a quiet self-translation (not a clean textbook citation) — and it still leaves
the operator-monotone-inverse step to formalize. Keep only as a fallback if FSS
fails to formalize. (Earlier "pinned target" — superseded by FSS on 2026-06-03.)

**Candidate A — Brascamp–Lieb variance inequality: REFUTED.** `Var ≤ ⟨∇f,A⁻¹∇f⟩`
needs `Hess S ≥ A > 0` globally, but `Hess S = −Δ + m₀² + 12λ diag(φ²)`; at `φ=0`
this is `−Δ − |m₀²|` with negative low-`k` eigenvalues (double well). No finite-`a`
regime makes it `≥` free. (Gemini deep-think confirms my refutation — this non-convexity
is *precisely* why φ⁴₂ variance bounds are hard, and what FSS sidesteps.)

**Also considered & rejected** (deep-think): correlation inequalities
(Lebowitz, Griffiths/GKS, Aizenman–Fröhlich) are for triviality / higher-point
bounds, not for isolating a free *upper* bound under a double well. FSS is the
definitive citable standard for the *spatial-infrared* task (`Ls → ∞`).

---

## Feynman–Kac bridge — scoping (2026-06-03): the pinned next code task for B2

> **PRIMARY ROUTE (owner decision 2026-06-03): build this in MAXIMUM GENERALITY in the
> `reflection-positivity` library, NOT as the lattice Fubini below.** In the OS/GNS
> framework the correlation identity `⟪[F],Tⁿ[G]⟫_phys = reflectionInnerProduct μ θ F
> (G∘τⁿ)` is essentially definitional, so the hard lattice steps (action factorization,
> kernel-composition Fubini, trace-ratio limit) **collapse**; the only φ⁴₂-specific work
> left is one operator-coincidence lemma (abstract `H_phys`/`T` = pphi2's
> `L2SpatialField`/`asymTransferOperatorCLM`) + free boundedness. Full design:
> `reflection-positivity/RECON.md` → "The Feynman–Kac bridge in MAXIMUM GENERALITY".
> The lattice-specific 4-step design below is kept as the concrete fallback / as the
> content of the operator-coincidence lemma.

This is the real remaining B2 work. It is the **Step B (Källén–Lehmann)** of the
detailed plan in the `reflection-positivity` repo's `RECON.md` ("Op 1: pphi2
Layer-B2 adapter") — Steps A and C there are already done/mechanical; Step B is the
bulk. Crystallized here as the live task.

**State already in place (do not re-derive):**
- **Step A — `GappedTransfer` package:** `asymGappedTransfer'` (`AsymSpectralGap.lean:167`),
  hypothesis-free, with the operator-norm gap `asymTransferNormalized_gap` proved.
- **Step C — `susceptibility_le`:** `∑_{n<N} |⟨v, T̂ⁿ v⟩| ≤ ‖v‖²/(1−γ)`, **uniform in
  `N` (hence `Lt`)** — `asymTransfer_susceptibility_le` (`AsymGappedTransfer.lean:92`).
- **B1 (`a`-uniform, per-`Lt`):** `asymInteractingVariance_le_freeVariance_lattice`
  / `_torus` (`AsymVarianceBound.lean:101/208`).

**⚠ FINDING (2026-06-03, opened the code): the operator and the measure are two
DISJOINT halves with NO connecting lemma.**
- `density_transfer_bound`'s asym wrapper `asymTorusIso_interacting_second_moment_density_transfer`
  (`AsymContinuumLimit.lean:48`) is **pure B1** — Cauchy–Schwarz (`density_transfer_bound_iso`)
  + Gaussian 4th-moment (`gaussian_hypercontractive`), constant `C = 3√K(Lt)` with `K`
  the **volume-growing Nelson constant**. It NEVER touches the transfer operator. It
  gives the *statement shape* and the `Lt`-growing constant — **nothing toward the bridge**.
  (The earlier RECON guess that it "may supply the measure→operator half" was WRONG.)
- `asymTransferOperatorCLM = M_w ∘L Conv_G ∘L M_w` (`AsymL2Operator.lean:276`,
  `w = exp(−(a/2)·spatialAction)`, `Conv_G` the time-step Gaussian) lives on the
  **spatial** `L2SpatialField Ns` (one time slice). It is referenced ONLY in the 5
  spectral files (`AsymL2Operator`, `AsymJentzsch`, `AsymPositivity`, `AsymSpectralGap`,
  `AsymGappedTransfer`) — **never in any measure file.**
- `interactingLatticeMeasureAsym = (1/Z)·exp(−V)·dμ_GFF` (`AsymLatticeMeasure.lean:363`)
  is the **global spacetime** Gibbs measure on `Configuration (AsymLatticeField Nt Ns)`.
- **So the proved gap is for an operator not yet known to compute the measure's
  correlations.** The bridge is the missing link between these halves.

**The bridge lemma to build (Step B) — this is the Feynman–Kac time-slicing theorem.**
The substantial, foundational, currently-unbuilt result: the global Gibbs measure's
time-correlations equal transfer-operator products,

  `∫ (ω f)² dμ_int  =  ∑_{t,t' ∈ Z_Nt} f̃(t) f̃(t') ⟨v_f, T̂^{|t−t'|} v_f⟩`,

`T̂ = asymTransferNormalized`, `v_f ∈ L2SpatialField Ns` the spatial vector of `f` off
the vacuum, `f̃` its time profile. This is NOT wiring — it is proving that the global
spacetime path-integral **factorizes time-slice by time-slice** into the single-step
kernel `M_w ∘ Conv_G ∘ M_w`. Mechanism: the global Gaussian splits into spatial slices
+ nearest-neighbour time coupling; the time coupling × spatial weight = the transfer
kernel; a Gaussian-Fubini / Markov computation on the finite lattice. Bounded but real
work (the concrete operator is manifestly bounded, so — unlike the abstract
`reflection-positivity` route — the difficulty is NOT a-priori boundedness; it is the
slice-factorization identity and the spatial-slice decomposition of `AsymLatticeField`).

**Downstream (mechanical once the bridge exists):**
2. **Vacuum projection** `v_f ⊥ vacuum` from evenness (mean zero).
3. **Apply Step C** ⟹ `≤ (‖f̃‖₁)² ‖v_f‖² / (1−γ)`, `Lt`-uniform.
4. **Identify RHS with `C · Var_free(f)`** (free covariance `latticeCovarianceAsymGJ`),
   watching the `1/a` cancellation (see `[[pphi2-b2-adapter-plan]]` memory: never
   evaluate `1/(1−γ)` standalone — form the int/free ratio first).

**Uniformity factorization (CONFIRMED by the code map):** single `C` = **B1 (owns
`a`-uniformity at fixed `Lt`) ⊕ gap (owns `Lt`-uniformity via `susceptibility_le`)**.
`Ls` fixed ⟹ no spatial-infrared input (the parked FSS step). Residual: gap bounded
below as `a→0`, i.e. `m_a → m(Ls) > 0` (master-plan banner).

**Effort / risk:** the Feynman–Kac time-slicing identity is the real cost — it joins
two halves of the development that have never met. This is a genuine sub-project, not
a finishing touch.

### Factorization design (grounded in the code, 2026-06-03)

**Nothing to port:** the *square* torus `Pphi2/TransferMatrix/` is also operator-side
only (GaussianFourier/Jentzsch/Positivity/SpectralGap; its only measures are Lebesgue
`volume` internal to building `T`). The bridge is unbuilt project-wide.

**Building blocks that DO exist** (square `TransferMatrix.lean`, reused by the asym
operator): `SpatialField Ns := Fin Ns → ℝ` (one time slice); `spatialAction P a mass c ψ`
(`:86`) `= spatialKinetic + spatialPotential` (single-slice); `timeCoupling ψ ψ' =
½Σ_x(ψx−ψ'x)²` (`:100`) (nearest-neighbour in time); `transferGaussian = exp(−timeCoupling)`
(= `Conv_G`); `transferWeight = exp(−(a/2)·spatialAction)` (= `M_w`); and
`T = M_w ∘ Conv_G ∘ M_w`.

**The factorization to prove (chain of identities):**
1. **Slice iso.** `Configuration (AsymLatticeField Nt Ns) ≃ (Fin Nt → SpatialField Ns)`
   (spacetime config = `Nt` time-slices), measure-compatibly. Needs `AsymLatticeSites`
   to factor as `Fin Nt × Fin Ns` (time × space) — VERIFY.
2. **Action decomposition.** Global lattice action `= Σ_t (a·spatialAction(ψ_t)) +
   Σ_t timeCoupling(ψ_t, ψ_{t+1})` (periodic in `t`). **Hardest sub-piece:** show the
   GJ Gaussian covariance `latticeCovarianceAsymGJ` (defined via an operator inverse)
   realizes exactly this quadratic form, so `dμ_int ∝ ∏_t [w(ψ_t)²·G(ψ_t−ψ_{t+1})]∏dψ_t`.
   This is the Gaussian-factorization step; least sure of existing infra here.
3. **Kernel composition (the core Fubini).** Integrating out intermediate slices
   composes the kernel: `∫ ∏_{s<n} G(ψ_s−ψ_{s+1}) w(ψ_s)² dψ_s … = (Tⁿ)(ψ_0, ψ_n)`.
   `T = M_w Conv_G M_w` is exactly one step. ⟹ `∫ A(ψ_0)B(ψ_n) dμ = Tr(M_A Tⁿ M_B T^{Nt−n})/Tr(T^{Nt})`.
4. **Trace → ground projection.** As `Nt→∞`, `Tr(T^{Nt−n}·)/Tr(T^{Nt}) → ⟨vacuum, ·⟩`
   (the proved gap ⟹ the top eigenvector dominates). Reduces the second moment to
   `∑_{t,t'} f̃(t)f̃(t')⟨v_f, T̂^{|t−t'|}v_f⟩`; then `susceptibility_le` (Step C).

Steps 1, 3 are mechanical-ish Fubini/iso wiring; **step 2 (Gaussian covariance =
slice-decomposed action) is the crux**, and step 4 needs a Perron-Frobenius
trace-ratio limit (have the gap; need the limit lemma). Size estimate (from the older
`asym-interacting-expmoment-volume-uniform-discharge-plan.md`): Layer B ≈ 1500–3000
lines. Realistic wall-clock: **a few weeks** given gaussian-field + the done spectral
side.

### ⚠⚠ Codex review (2026-06-03): VERIFY NORMALIZATION BEFORE BUILDING ANYTHING

Codex reviewed this against the actual code; **independently confirmed by derivation
(2026-06-03).** The exact 2D lattice action factorizes as
`S = Σ_t [ timeCoupling(φ_t,φ_{t+1}) + a²·spatialAction(φ_t) ]`
(since `a²·½(∂_tφ)² = ½(Δ_tφ)² = timeCoupling`; `a²·½(∂_sφ)² = a²·spatialKinetic`;
`a²·(½m²φ²+:P:) = a²·spatialPotential`). So the correct slice weight is
`exp(−(a²/2)·spatialAction)`. **The 4-step route is not sound as written — Step 2 is
false as stated due to a factor-`a` mismatch in the weight exponent:**
- Gibbs interaction `V = a²·Σ wickPolynomial` (`AsymLatticeMeasure.lean:257`); the
  GFF precision is `a²·Q`, `Q = −finiteLaplacianAsym + mass²` (GaussianField
  `AsymCovariance.lean:54,152,220`), matching the GJ convention `exp(−(aᵈ/2)φQφ)`,
  `d=2 ⟹ a²` (square density bridge `SpectralCovariance.lean:569`, `Density.lean:1324`).
- BUT the transfer weight is `asymTransferWeight = exp(−(a/2)·spatialAction)`
  (`AsymL2Operator.lean:63`). A product around the time circle yields `a·spatialAction`,
  **not** the `a²` the measure carries.
- **⟹ the built `asymTransferOperatorCLM` may not be THE transfer operator of
  `interactingLatticeMeasureAsym`** — and then Part A's proved gap, though a valid
  theorem, is about the wrong operator. **This must be resolved first.** Likely fix:
  re-derive the correct slice weight (probably `exp(−(a²/2)·spatialAction)`) and check
  whether the gap proof survives the reweight, OR find the convention that reconciles
  them (e.g. an absorbed time-spacing). Do NOT build the bridge until the two-point of
  the measure is shown to equal the operator's (a 2-slice check suffices).

Other Codex findings (route-I specific; see below for how the abstract route dodges them):
- **No asym Gaussian density/precision bridge exists** (the square one does;
  `Density.lean`). Route-I step 2 would need it. Easiest target: evaluated asym GFF has
  Lebesgue density with precision `a²·massOperatorAsym` (precision-matrix equality, not
  characteristic functions).
- **No infinite-dim trace-class / Perron-Frobenius trace-asymptotics API** (Mathlib has
  only finite-dim `InnerProductSpace.Trace`). Route-I step 4 would have to build it —
  UNLESS one takes the **finite-`Nt` periodic-trace** route (Codex's recommendation,
  question A), which `susceptibility_le` already supports. But the finite periodic-trace
  formula is itself not formalized (`TransferMatrix.lean:175,188`).
- No φ⁴₂-specific circularity — the issue is normalization + missing infrastructure.
- Effort: **~3–6 weeks finite-`Nt`** (normalization fixed early); 6–10+ weeks if also
  building trace-class asymptotics. ~1.5k–4k lines.

**How the MAXIMUM-GENERALITY (abstract OS) route relates to these (see RECON.md +
`docs/transfer-bridge-spec.md`):** the abstract D0–D3 deliverables **avoid** the missing
density bridge, the trace formula, AND the trace-class asymptotics — D2 is a finite-`n`,
gap-free, near-definitional identity and D3 uses only `susceptibility_le`. So Codex's
risks 2 & 3 do **not** block the abstract bridge. **Risk 1 (normalization) still bites**,
but it relocates to the single operator-coincidence lemma (abstract `H_phys`/`T` ≅
`L2SpatialField`/`asymTransferOperatorCLM`): that unitary can only carry the proved gap
if the operators actually match — i.e. the same normalization check. **Bottom line:
resolve the `a`-power normalization first, regardless of route.**

---

**DEAD END — spectral-MEASURE domination `ρ_int ≤ C·ρ_free` is FALSE.** (Gemini
3.1, 2026-06-02.) `ρ_free` lives on the free single-particle dispersion
`λ_free(k)=e^{−aω_free(k)}`; `ρ_int` lives on the **physical** pole
`λ_phys(k)=e^{−aω_phys(k)}` (`m_phys ≠ m_free`, mass shift) **plus** a
multi-particle continuum (Simon Ch. IX). The single-particle peaks sit at
*different* `λ`, so the measures are **mutually singular** — no finite-`C`
pointwise/measure domination, and band-limiting `h` cannot force it; the
resolvent-weighted `dρ_int/dρ_free` is ill-defined (disjoint supports). The
reframe below (kept for the record) was the wrong target: the resolvent FORM
bound replaces it precisely because it bounds the *integral*, never the singular
measures. The earlier finite-`Nt` claim that `ρ` is exactly `Lt`-independent also
only holds in the `Lt→∞` limit (finite-`Nt` has thermal `Tr T̂^{Nt}` corrections).

---

### (Superseded) spectral-measure reframe — kept for the record

The `Lt`-uniform comparison reduces to an **`Lt`-free spectral-measure domination**.

**Reframe.** For fixed `(Ns, a)`, the time-2-point function is a spectral integral
`S(d) = ⟨Q, T̂^{d} Q⟩ = ∫_{[−γ,γ]} λ^{d} dρ(λ)`, where `ρ` is the Källén–Lehmann
spectral measure of `T̂` w.r.t. the field-excited state `Q = A·Ω ⊥ vacuum`.
**`ρ` depends only on `(Ns, a)`, NOT on `Lt`** (`T̂`, `Q` are the one-time-step
operator and the spatial ground state). Then
`Var^{Nt}(f) = ∫ K_h^{Nt}(λ) dρ(λ)` with `K_h^{Nt}(λ) = (1/Z)Σ_{t,t'∈Z_{Nt}}
h(t)h(t')(λ^{d}+λ^{N−d}) ≥ 0` (positive by RP; `Z = Tr T̂^{Nt}` bounded, `→1`).

**Key simplification — `Lt`-uniformity is automatic.** Both sides are `∫K_h^{Nt}dρ`
with the *same* `K_h^{Nt} ≥ 0`. So **IF** the `Lt`-free domination
`ρ_int ≤ C·ρ_free` (measures on `[−γ,γ]`, `C` indep. of `Lt` and `a`) holds, then
`Var_int^{Nt}(f) ≤ C·Var_free^{Nt}(f)` for **every** `Nt` — B2, `Lt`-uniform for
free. **So the precise Step-B target is `ρ_int ≤ C·ρ_free`** (an `Lt`-free statement).

**Not a free B1-bootstrap.** B1 gives, per `Nt`, the moment-matrix domination
`G_{ρ_int}^{Nt} ≼ C(Nt)·G_{ρ_free}^{Nt}` (moments `∫λ^d dρ`, `d≤Nt`) with `C(Nt)`
*growing*. Finite-`C` measure domination is strictly stronger; the gap
(supp `ρ ⊆ [−γ,γ]`, compact, away from `1`) makes moments determine the measure,
but the constant is not inherited.

**The real crux (VET THIS).** Whether `ρ_int ≤ C·ρ_free` holds with finite `C`, and
in what exact form: (i) full measure domination (possibly *false* — interacting KL
weight, with one-particle peak at the physical mass + multi-particle continuum, may
sit where `ρ_free` is thin); (ii) `k`-restricted / susceptibility-side comparison —
suffices if B2's continuum test functions have band-limited `h` so `K_h` concentrates
near `k≈0`; (iii) resolvent-weighted relative-boundedness `dρ_int/dρ_free ≤ C`.
Pin the correct sufficient form before any code.

## ⚠ Vetting result (Codex, 2026-06-02): the 3-piece sketch below is FLAWED as written

Verdict: **flawed but salvageable**. The idea (gap ⟹ Lt-uniform variance via the
ratio) is sound, but the *as-written* Pieces 1–3 have real gaps. Read the
corrections here first; the sketch in the lower sections is the original, kept
for context. **Required corrections:**

1. **Piece-1 representation is WRONG as an equality.** On the periodic cylinder
   the finite-volume 2-point object is a **two-arc trace**, `⟨A Tᵗ A T^{Lt−t}⟩ / ⟨T^{Lt}⟩`
   (exactly as `reflection-positivity/ReflectionPositivity/VarianceBound.lean`'s
   own docstring states), not `a²·Σ ⟪Q_s, T^{dist(s,t)} Q_t⟫`. The single-`dist`
   kernel is at best a *bound*; the correct periodized factor is `γ^r + γ^{Nt−r}`,
   `r = |s−t| mod Nt`. **Fix:** state Piece 1 as an exact **trace** representation
   with insertion operators `A_s` and the periodic-trace denominator, then derive
   the `γ^r + γ^{Nt−r}` corollary bound.

2. **The free lower bound (Piece 2) is the biggest risk — likely false as stated.**
   `Var_free ≳ (1/(1−γ_free))·Σ_s‖Q_s‖²` uses the *zero-mode* (low-frequency)
   susceptibility scale for **all** test functions; it is not a valid uniform
   lower spectral multiplier for time-dependent profiles with high temporal modes.
   **Fix:** do NOT use a scalar free lower bound. Instead prove **mode-by-mode
   operator domination** — the interacting *connected covariance form* `≤ C ·` the
   *exact free covariance form* — so the comparison is against the true free
   covariance, not a single susceptibility scale. (This also removes the need for
   the `1/a` cancellation to be done "by hand".)

3. **`susceptibility_le` is used beyond its proved scope.** It controls a *single*
   vector (`∑_n |⟪v,Tⁿv⟫| ≤ ‖v‖²/(1−γ)`). The double sum `Σ_{s,t}⟪Q_s,T^d Q_t⟫`
   needs a separate **mixed cyclic Young inequality**:
   `Σ_{s,t<N} γ^{d(s,t)} ‖Q_s‖‖Q_t‖ ≤ (C/(1−γ))·Σ_s‖Q_s‖²` (with the periodic `d`).
   This is a new lemma (candidate for `reflection-positivity`).

4. **Connected vs raw second moment.** The target bounds the *raw* `∫(ωf)²`, but
   the representation/gap argument controls the *connected* (ground-orthogonal)
   part. Add a zero-/one-point lemma (Z₂/evenness of the measure) so raw 2nd
   moment = covariance for these observables, or carry the disconnected term.

5. **`a`-normalization double-counting.** `asymLatticeTestFnIso` already inserts a
   GJ `a` weight (`evalAsymTorusAtSiteGJ_apply = a·…`, `AsymTorusEmbeddingIso.lean:47,76`).
   Pin whether the spatial `a` lives in `A_s` or in the outer `a²`; do not hide it
   in both.

6. **fixed-`Ls` gap convergence is not yet in Lean.** `asymTransferNormalized_gap`
   is per-lattice-parameter; `AsymPositivity.lean:135` puts `a→0` uniformity out of
   scope. Add `m_a → m(Ls) > 0` (equiv. a uniform lower bound on `−log γ_a / a`
   over `Ns·a = Ls`, finitely many coarse spacings handled separately) as an
   explicit lemma/axiom.

**Net:** replacing the black-box B2 axiom with a *correct* trace-representation
axiom is still a genuine improvement, but the discharge needs (i) the two-arc
trace representation, (ii) mode-by-mode free-covariance domination (not a scalar
lower bound), (iii) the cyclic Young lemma, (iv) the Z₂ zero-mean lemma, and
(v) the explicit fixed-`Ls` gap input. (Codex full review: read-only, 2026-06-02.)

## ⚠⚠ Second vetting (Gemini 3.1-pro, 2026-06-02): the corrected plan is STILL flawed — structural norm mismatch

Even with the Codex corrections above, the transfer-matrix discharge does **not**
close B2. A deeper, structural flaw:

1. **NORM MISMATCH (the killer).** The target bounds `Var_int` by the **free
   covariance** `Var_free = ⟨f, (−Δ_{2D}+m²)⁻¹ f⟩` — an `H⁻¹` space-*time* Sobolev
   norm with spatial-gradient suppression `1/(p_s²+p_t²+m²)`. The transfer-matrix
   route (two-arc trace + cyclic Young) yields the **time** gap `1/(1−γ)` times a
   **spatial `L²`** norm of `f`'s slices. Since `L² ⊄ H⁻¹`, a 1D (time) spectral
   gap cannot produce the spatial-gradient bound needed to match `Var_free`.
   *"Without spatial/spacetime symmetry, a 1D transfer-matrix gap will never bound
   a 2D Sobolev norm."* — the chain dies for lack of spatial control.

   **NUANCE to settle (owner):** this objection assumes `‖Q_s‖²` is a raw spatial
   `L²` norm. If `Q_s` lives in the physical Hilbert space with the
   reflection/`B`-inner product, it may already carry spatial covariance structure
   — which is exactly where the objection does or does not bite. **Pin down the
   `Q_s` inner product before any axiom.**

2. **Codex's Piece-2 fix (mode-by-mode domination) is FALSE.** If
   `interacting connected covariance ≤ C·free covariance` held, you'd be done
   immediately and the **entire transfer-matrix apparatus is redundant**. But it
   is analytically false for Wick-ordered φ⁴₂ as `a→0`: Lebowitz/GRS bounds the
   interacting theory by the free one with the **bare** mass
   `m₀² = m_phys² − cλ·log(1/a) → −∞`, so the bounding covariance diverges;
   Brascamp–Lieb needs log-concavity, destroyed by the `−log(1/a)·φ²` counterterm.
   (Consistent with the earlier literature vetting: Wick ordering breaks the naive
   comparison.)

3. **What stands.** The **two-arc trace + `γʳ+γ^{Nt−r}` + cyclic Young** is correct
   and sufficient for the **`Lt`-direction time-sum only**
   (`‖γʳ+γ^{Nt−r}‖_{L¹(Z_{Nt})} ≤ 2/(1−γ)`). The periodized kernel is mandatory.

4. **Salvage — Nelson symmetry.** To bridge time→space without the (forbidden)
   chessboard, use **Nelson symmetry** (Euclidean rotation invariance of the
   measure): the spatial transfer matrix behaves like the time one, reconstructing
   the `1/(p_s²+p_t²+m²)` free covariance. Standard Glimm–Jaffe/Simon Route C uses
   the **chessboard** (FSS) for exactly this rotation; Nelson symmetry is the
   alternative.

5. **Implication for the architecture.** pphi2's **B1 already achieves the
   norm-match via Nelson** (the `asymNelson` exp-moment / density-transfer route).
   So the discharge most likely must **combine** B1's Nelson-based norm-matching
   (per-`Lt`) with the transfer-matrix gap supplying **`Lt`-uniformity** — NOT
   represent `Var_int` directly as a transfer-matrix sum and compare to `Var_free`.
   The transfer-matrix work (Part A + #1) provides the `Lt`-uniform time-decay; it
   does not, by itself, provide the spatial/Sobolev match.

**RECOMMENDATION: do not write any representation axiom until the norm-mismatch /
`Q_s`-inner-product question is settled.** Two independent vettings (Codex,
Gemini 3.1-pro) now flag the direct transfer-matrix-vs-`Var_free` route as
broken; the viable path is the Nelson-symmetry bridge or a B1⊕(TM-`Lt`-uniformity)
combination. This is an owner-level design decision.

## Target (the axiom to discharge)

`asymInteractingVariance_le_freeVariance_Lt_uniform`
(`Pphi2/AsymTorus/AsymExpMomentDischarge.lean:190`):

> ∃ `C > 0` (depending only on `P, mass, Ls`) such that for **all** `Lt`, `Nt,
> Ns, a` with `Nt·a = Lt`, `Ns·a = Ls`, and all test functions `f`:
> `∫(ω f)² dμ_int ≤ C · ∫(ω g)² dμ_GFF`, `g = asymLatticeTestFnIso … f`.

`C` must be uniform in **both** `Lt → ∞` (IR) **and** `a → 0` (UV), at fixed `Ls`.

## Resolved architecture (no chessboard; fixed `Ls`)

See `reflection-positivity/docs/B2_UNIFORMITY_QUESTION.md` (expert-vetted):

- **No chessboard / FSS needed**, *because `Ls` is fixed.* The fixed-`Ls`
  cylinder mass gap `m_a → m(Ls) > 0` by compact-resolvent + norm-resolvent
  convergence `T_a → e^{−a H(Ls)}` (Simon "P(φ)₂" 1974 Ch. VI; Thm V.15).
  FSS/chessboard is only for the thermodynamic `Ls → ∞` limit.
- **The `1/a`-cancellation trap is decisive.** `susceptibility_le` gives
  `Σ_{t<Nt} γ^t ≤ 1/(1−γ)` with `γ = e^{−m_a a}`, so `1/(1−γ) ≈ 1/(m_a a)`
  **diverges as `1/a`**. A single axiom `Var_int ≤ 1/(1−γ)·Var_free` is therefore
  `a`-NON-uniform and WRONG. The `1/a` must cancel inside the **ratio** of the
  interacting and free transfer-matrix representations (both carry the same `a²`
  spacetime measure and the same `1/a` geometric-sum factor), leaving
  `C ≈ m_free/m_int`, finite and `a`-uniform.

## Already proved (do not re-derive)

- `reflection-positivity` (v4.30.0, dep of pphi2): `GappedTransfer` and
  `GappedTransfer.susceptibility_le`:
  `∑_{n<N} |⟪v, Tⁿ v⟫| ≤ ‖v‖²/(1−γ)`, **uniform in `N`** (the `Lt` direction).
- `Pphi2/AsymTorus/AsymGappedTransfer.lean`: `asymGappedTransfer` packaging.
- `Pphi2/AsymTorus/AsymSpectralGap.lean`: `asymTransferNormalized_gap` (the
  operator-norm gap on the ground-orthogonal complement) and `asymGappedTransfer'`
  (the `GappedTransfer` with no hypotheses). So `susceptibility_le` applies to the
  asym cylinder off the shelf.
- `AsymJentzsch`/`AsymPositivity`: `AsymTransferGroundExcitedData.htop` (the
  Perron-Frobenius dominance pinning the ground index as the spectral top).

## The three remaining pieces

### Piece 1 — interacting Källén–Lehmann representation (the new axiom)

The genuinely un-formalized Feynman–Kac fact (TransferMatrix.lean's docstring:
*"the trace formula … is a standard identity but not formalized here"*). State,
for the cylinder interacting measure, the time-slice decomposition of the
2-point function as a normalized transfer-matrix Toeplitz form:

```
∫(ω f)² dμ_int  =  a² · Σ_{s,t < Nt} ⟪Q_s(f), (asymTransferNormalized)^{dist(s,t)} (Q_t(f))⟫
```

where `Q_s(f) : L2SpatialField Ns` is the spatial field-vector of `f` at time
slice `s` projected onto the ground-orthogonal complement (connected part),
and `dist(s,t)` is the periodic-time distance on `Z_{Nt}`. (Precise statement:
isolate `Q` and the connected/disconnected split carefully; verify
non-vacuity and correct quantifiers per the axiom protocol; mark NOT VERIFIED
and **vet with deep-think + Codex before relying** — the axiom statement is the
delicate part.)

References: Glimm–Jaffe "Quantum Physics" Ch. 6 (lattice transfer matrix);
Simon "P(φ)₂" (1974) Ch. III; Osterwalder–Schrader. This axiom is **more
fundamental** than B2 — it is the representation; all operator-theoretic content
(gap, geometric series) is now proved.

### Piece 2 — free Källén–Lehmann representation (provable, not an axiom)

The free side is Gaussian and explicitly computable. pphi2 already has
`∫(ω g)² dμ_GFF = ⟪T g, T g⟫` (`AsymContinuumLimit.lean:163`,
`second_moment_eq_covariance`). Derive the matching free transfer-matrix
Toeplitz form `a² · Σ_{s,t} ⟪Q_s, T_free^{dist(s,t)} Q_t⟫` and the **lower bound**
`Var_free ≳ (1/(1−γ_free))·‖Q‖²`-scale, so the `1/a` factors match the
interacting side. (Free, so no axiom needed — this is the key to the ratio.)

### Piece 3 — the ratio (proved; the `1/a` cancellation)

Combine: interacting upper bound (Piece 1 + `susceptibility_le`, giving the
`1/(1−γ_int)` factor) over free lower bound (Piece 2, the `1/(1−γ_free)` factor).
The `a²` and the leading `1/a` are common factors that cancel **before** any
`a → 0` limit (keep everything in dimensionless ratio form; never evaluate
`1/(1−γ)` standalone). Result: `C ≈ (1−γ_free)/(1−γ_int) × (overlap) → m_free/m_int`,
finite and uniform in `Lt` and `a`. The `a`-uniformity of `C` reduces to the
fixed-`Ls` gap convergence `m_a → m(Ls) > 0` (compact resolvent — a separate,
non-chessboard input; can be its own lemma/axiom).

## Net

- **Axioms**: replace the high-level B2 axiom with **one** more-fundamental
  Feynman–Kac representation axiom (Piece 1). Net axiom-quality improvement:
  the operator-theoretic content (the hard part historically) is now proved.
- **Proofs**: Pieces 2 (free representation) and 3 (ratio) are provable from
  existing infrastructure + the proved `susceptibility_le`.
- **Sequencing**: state + vet the Piece-1 axiom; prove Piece 2; prove Piece 3;
  prove `fixed-Ls gap convergence` (or take as a small, clearly-cited lemma);
  assemble into the discharge theorem; remove the B2 axiom.
