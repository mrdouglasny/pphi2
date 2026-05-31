# `asymInteracting_expMoment_volume_uniform` discharge plan

*2026-05-31. Scoping plan for the **last** project-introduced axiom on
`cylinder-isotropic-lattice`. After UNIT 7 landed
(`asymChaosCutoffDecomposition` axiom → theorem), this is the only
remaining axiom blocking a fully unconditional cylinder OS0/OS1/OS2/OS3
construction (modulo the upstream `embed_l2_uniform_bound` and the
two cylinder-RP/OS2-symmetry hypotheses).*

## Target — the exact axiom

`Pphi2/AsymTorus/AsymContinuumLimit.lean:601`:

```lean
axiom asymInteracting_expMoment_volume_uniform
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (L : ℝ) [Fact (0 < L)] (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
        (Nt : ℝ) * a = L → (Ns : ℝ) * a = Ls → ∀ f : AsymTorusTestFunction L Ls,
        Integrable (fun ω => Real.exp (|ω f|))
          (asymTorusInteractingMeasureIso L Ls Nt Ns a P mass ha hmass) ∧
        ∫ ω, Real.exp (|ω f|)
          ∂(asymTorusInteractingMeasureIso L Ls Nt Ns a P mass ha hmass) ≤
        K * Real.exp (C * ∫ ω, (ω (asymLatticeTestFnIso L Ls Nt Ns a f)) ^ 2
          ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass))
```

i.e. `∫ e^{|ωf|} dμ_int ≤ K · exp(C · σ²(f))` with `K, C` uniform in the
time period `L` (and in `(Nt, Ns, a)`). The spatial period `Ls` is fixed.

## Why this is deep (and why it stayed an axiom)

**Status verdict** (`docs/cylinder-conditional-inputs-provability.md` §4,
deep-think-vetted 2026-05-27): **TRUE in the form `K · e^{C·σ²}`** —
the `C = 1` form would be FALSE since the interacting susceptibility
can exceed `2/m²` in infinite volume. With `∃C` the bound is the
volume-uniform interacting exp-moment of P(φ)₂, comparable in difficulty
to **the square's `spectral_gap_uniform` — which is itself still an
open axiom** in this project (`Pphi2/TransferMatrix/SpectralGap.lean:89`).

Reference depth: Glimm–Jaffe Ch. 18–19; Simon *P(φ)₂* Ch. V, VIII;
Newman (1975) CMP 41; Glimm–Jaffe–Spencer cluster expansion.

## The cylinder shortcut — why we can do better than the square

The square form requires the full **2D** spatial cluster expansion. The
asym/cylinder form has `Ls` **fixed**, so `L → ∞` is a **1D
thermodynamic limit** — no phase transition, no full cluster expansion.

The transfer matrix `T = e^{-a H_{Ls}}` is the bridge: with `Ls` fixed,
`T` acts on `L²(ℝ^{Ns})` (finite-dim per `a`, but with controlled
growth) and has a strictly isolated non-degenerate maximal eigenvalue
by the **infinite-dimensional Perron–Frobenius theorem** (positivity
improvement, already proved on the square side via
`transferOperator_positivityImproving` + Jentzsch). Hence the cylinder
mass gap `m₁ > 0` is *unconditional* and the susceptibility stays
bounded as `L → ∞`. The bound is then dischargeable via
**chessboard estimates (Fröhlich–Simon–Spencer)** + the transfer-matrix
spectral radius — saving the bulk of a spatial-cluster-expansion
formalization.

## Three-layer discharge architecture

| Layer | Statement (informal) | Reference | Discharges from |
|---|---|---|---|
| **A** Newman MGF Gaussian-domination | `E[e^{ωf}]_int ≤ exp(½⟨(ωf)²⟩_int)` for even-degree Wick-ordered P (Lee-Yang / Simon–Griffiths class) | Newman (1975); Glimm–Jaffe §4.2 | Single-site Lee–Yang for `:P(φ):` + GHS-type multiplication |
| **B** Interacting variance ≤ free variance | `⟨(ωf)²⟩_int ≤ C₀ · ⟨(ωf)²⟩_free` uniformly in L | Källén–Lehmann; lattice sum rule | Cylinder transfer-matrix mass gap (1D PF) |
| **C** Assembly | C₀, K = 2 ⟹ `∫ e^{|ωf|} ≤ 2 · exp(C₀/2 · σ²(f))` uniformly in L | (combine A + B; `e^{|x|} ≤ e^x + e^{-x}`) | A + B |

Layer C is short (~50 lines of arithmetic). The work lives in A and B.

### Layer A: Newman MGF Gaussian-domination (~600–1000 lines)

The mathematical core:

```lean
theorem newman_mgf_gaussian_domination
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (f : AsymLatticeField Nt Ns) :
    ∫ ω, Real.exp (ω f) ∂(interactingLatticeMeasureAsym Nt Ns a P mass ha hmass) ≤
      Real.exp ((1/2) * ∫ ω, (ω f) ^ 2
        ∂(interactingLatticeMeasureAsym Nt Ns a P mass ha hmass))
```

Building blocks:
1. **Lee–Yang for the single-site Wick distribution** — `exp(-a²:P(φ):)` is
   in the Simon–Griffiths class (real zeros of the partition function).
   This needs the single-site `:P(φ):_c` to be Lee–Yang: a textbook
   result for even monic `P` (Simon §VIII; Newman §3). **Estimated:
   ~250–400 lines**, depends on whether we already have a working
   single-site Lee–Yang lemma in `gaussian-field`/upstream.
2. **Newman's inequality for sums of Lee–Yang variables** — for the
   lattice product measure, the joint MGF inherits Gaussian
   domination. ~200–400 lines.
3. **Take `|·|` via `e^{|x|} ≤ e^x + e^{-x}`** — short (50–80 lines).

**Reusability**: this *should* eventually live in `gaussian-field`,
parameterized over an abstract Lee-Yang lattice action (not asym-specific).

### Layer B: Cylinder transfer-matrix mass gap (~1500–3000 lines)

The biggest piece. The bound `⟨(ωf)²⟩_int ≤ C₀ · ⟨(ωf)²⟩_free` follows
from `m_phys > 0` uniformly in L. Sub-layers:

1. **Define the cylinder transfer matrix** for the asym lattice with
   `Ls` fixed. The square already has `transferOperatorCLM` (factored
   as `M_w ∘L Conv_G ∘L M_w` in `TransferMatrix/L2Operator.lean`) —
   port to asym with the rectangular dispersion. **~300–500 lines**.
2. **Positivity improvement / Jentzsch on the cylinder transfer
   matrix** — the asym analogue of `transferOperator_positivityImproving`
   (which is already PROVED on the square via Cauchy–Schwarz +
   integrable-translation arguments). Port should be mechanical.
   **~200–300 lines**.
3. **Infinite-dim Perron–Frobenius spectral gap** — strictly isolated
   non-degenerate maximal eigenvalue, hence a strictly positive mass
   gap. The square has `jentzsch_theorem` (proved) +
   `transferOperator_strictly_positive_definite` (proved) +
   `ground_simple` (proved); the asym port follows the same
   self-adjointness + Bochner bridge route. **~400–600 lines**.
4. **Uniformity in `a` and `L`** — the spatial spacing `a = Ls/Ns` is
   bounded as `Ns → ∞` (any UV refinement), and `L → ∞` is what we
   want. Uniformity in `a` is the genuinely hard part — for the square
   it's the open `spectral_gap_uniform` axiom. The cylinder case is
   **easier** because we control the spatial direction (fixed `Ls`),
   but a UV-uniform mass gap on the cylinder still needs *something*.
   **Two routes**: (i) a 1D variational / Bonami–Beckner argument on
   the cylinder ground state; (ii) the much-more-extensive
   **chessboard estimate** (Fröhlich–Simon–Spencer). Estimated:
   **~600–1500 lines** depending on route.
5. **Convert mass-gap to variance bound** via Källén–Lehmann
   representation of the lattice 2-point function — ~150–250 lines.

### Layer C: Assembly (~50–100 lines)

Combine A's `K = 2` and B's `C = C₀/2` into the axiom's `K · exp(C·σ²)`
statement. The `σ²(f)` in the axiom is the *free*-Gaussian variance
(RHS uses `latticeGaussianMeasureAsym`), so the conversion in step B(5)
puts everything on the same footing.

## Total scope

**~2700–4500 lines** of new code, spread across `gaussian-field` (for
Layer A's reusable Lee-Yang/Newman content) and `pphi2` (for Layers B
and C). For comparison:

| Discharge | Lines | Wall-clock (per CLAUDE.md heuristic) |
|---|---|---|
| `wickConstantAsym_eq_variance` (2026-05-27) | ~500 | ~3 days |
| `asymChaosCutoffDecomposition` (UNIT 7, 2026-05-31) | ~900 (across UNITs 5+6+7) | ~9 days |
| `asymInteracting_expMoment_volume_uniform` | **~2700–4500** | **~3–8 weeks** |

This is structurally a different beast — not a "port of proved square
machinery" (the square *itself* doesn't have it; `spectral_gap_uniform`
is open). It's net-new constructive QFT formalization.

## Three options

### Option 1 — Full discharge

Execute Layers A + B + C. Multi-week. Produces a fully unconditional
cylinder OS0/OS1/OS2/OS3 result (modulo the upstream
`embed_l2_uniform_bound` and the two cylinder-RP/OS2-symmetry
hypotheses, which are also separate proof workstreams).

**Pros**: zero project-introduced axioms on the branch; the
construction is genuinely standalone.

**Cons**: 3–8 weeks of work for a single axiom; the math is at the
research-formalization frontier (Newman MGF + 1D PF on a Schrödinger
operator + chessboard); the resulting `gaussian-field` Lee–Yang/Newman
infrastructure is a substantial upstream contribution.

### Option 2 — Split into sub-axioms

Replace the single axiom with **two or three** smaller sub-axioms,
each separately deep-think-vetted:

* `lattice_interacting_mgf_gaussian_domination` — Layer A's Newman
  bound (provable via single-site Lee–Yang).
* `cylinder_transfer_matrix_mass_gap_uniform` — Layer B's
  transfer-matrix gap on the cylinder (analogue of the square's
  `spectral_gap_uniform`, but in the easier quasi-1D regime).
* (Layer C becomes a proved theorem combining the two.)

Each sub-axiom is then a clearly-stated, individually vettable input;
the assembly becomes a proved theorem; the project axiom count stays
the same (or grows by 1) but the **conceptual** content is cleanly
separated.

**Pros**: makes the bound's structure explicit; each piece is a known
result with its own discharge path; can be done piecemeal over time
(e.g., discharge Layer A first while B remains an axiom, then vice
versa).

**Cons**: doesn't actually drop the axiom count; still moves the same
debt around.

### Option 3 — Keep as single deep-think-vetted axiom

Accept that this is the genuine cluster-expansion / transfer-matrix-gap
input and leave it as an axiom on the branch. The construction would
then live with **one** vetted project-introduced axiom indefinitely.

**Pros**: the math is standard (Newman + 1D PF + chessboard, all
textbook-level); the axiom's form `∃ K, C` is provably the right shape;
all the *novel* content of the cylinder construction is already
unconditional.

**Cons**: branch retains one project axiom; the "fully axiom-free
cylinder construction" headline is delayed.

## Recommendation

**Option 2 with deferred execution.** Splitting the axiom is cheap
(~1 day of design work, ~200 lines of proved Layer-C assembly) and
yields the clearest *narrative* about what's left. Discharging the
sub-axioms can then happen on whatever timescale fits the broader
campaign — likely:

1. **Layer A first** (Newman MGF) — easier, ports to `gaussian-field`
   as reusable upstream infrastructure, ~1–2 weeks.
2. **Layer B last** (transfer-matrix gap) — the deeper one, can wait
   until the square's own `spectral_gap_uniform` is being worked
   (shared discharge path).

The full Option-1 discharge is reasonable but high-cost and not the
critical path for the broader pphi2 / cylinder campaign. **Option 3 is
also defensible** — the axiom is well-vetted, the form is correct, and
the bigger gains right now are likely in (a) extending the cylinder
construction to the full square-lattice case, or (b) discharging the
upstream `embed_l2_uniform_bound`.

## What's NOT in this plan

* `embed_l2_uniform_bound` (upstream `gaussian-field` axiom, §3).
* `hRP` (cylinder reflection positivity, §5).
* `hOS2` (cylinder Euclidean symmetry, §6).

These are all separate workstreams; see
`docs/cylinder-conditional-inputs-provability.md` for their provability
verdicts and `docs/cylinder-os3-discharge-plan.md` for the OS3 line of
attack.

## Cross-references

* `docs/cylinder-conditional-inputs-provability.md` §4 — full provability
  verdict for this axiom (the source of the `∃C` correction).
* `docs/cylinder-master-plan.md` — campaign-level rollup.
* `docs/asym-chaos-cutoff-decomposition-discharge-plan.md` — the
  reference template for staged axiom discharges (UNITs 1–7); useful
  as a methodology reference but the math content is different.
* `Pphi2/TransferMatrix/SpectralGap.lean:89` — the analogous square
  axiom `spectral_gap_uniform` (also still open); shared discharge
  path with Layer B above.
