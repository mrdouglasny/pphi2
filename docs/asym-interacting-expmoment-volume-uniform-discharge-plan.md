# `asymInteracting_expMoment_volume_uniform` discharge plan

*2026-05-31. Scoping plan for the **last** project-introduced axiom on
`cylinder-isotropic-lattice`. After UNIT 7 landed
(`asymChaosCutoffDecomposition` axiom → theorem), this is the only
remaining axiom blocking a fully unconditional cylinder OS0/OS1/OS2/OS3
construction (modulo the upstream `embed_l2_uniform_bound` and the
two cylinder-RP/OS2-symmetry hypotheses).*

**2026-05-31 update**: deep-think vet of the discharge architecture (not
the axiom statement, which was vetted 2026-05-27) returned three
refinements:
1. **Split layer B further** — the "finite-`a` mass gap" and the
   "UV uniformity as `a → 0`" are separate topological gaps and should
   be separate axioms. The recommended split is **4 axioms** (A, B1,
   B2 + C theorem), not 2-3.
2. **Add missing compactness step** — at fixed `a`, the transfer matrix
   `T = M_w ∘ Conv ∘ M_w` on `L²(ℝ^{Ns})` must be shown **compact
   (often Hilbert-Schmidt)** to ensure continuous spectrum doesn't
   swallow the gap. The pphi2 square infrastructure asserts positivity
   improvement but not compactness explicitly.
3. **Scope is ~2-3× larger than originally estimated** — Layer A
   (Newman) needs Griffiths-Simon (Asano contractions → Ising Lee-Yang
   → continuous spins); Layer B4 (chessboard) needs the full
   reflection-positivity multiple-reflection algebra; Lean's spectral
   theorem is WIP and may need bespoke functional calculus for the
   Källén-Lehmann step. Revised total: **6000-8000 lines, 8-14
   weeks** wall-clock.

The revised architecture and the new "extraction to upstream" plan
are in §§ "Three-layer..." and "Reusable upstream extractions" below;
the original estimates are preserved for the record.

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

## Three-layer discharge architecture (original; superseded by 4-layer split below)

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

## Revised four-layer discharge (post deep-think vet, 2026-05-31)

The deep-think vet recommends **splitting Layer B into B1 + B2** —
"finite-`a` mass gap" vs "UV uniformity as `a → 0`" are separate
topological gaps and should be separate sub-axioms.

| Layer | Statement | Provability | Status |
|---|---|---|---|
| **A** | `E[e^{ωf}]_int ≤ exp(½⟨(ωf)²⟩_int)` (Newman MGF Gaussian-domination via single-site Lee-Yang) | Standard, but needs Griffiths-Simon | **axiom** (proposed split) |
| **B1** | At fixed `a`: cylinder TM is compact (HS), has positive mass gap; lattice Källén-Lehmann gives `⟨(ωf)²⟩_int ≤ C(a)·⟨(ωf)²⟩_free` (per `a`, *not* uniform) | Standard infinite-dim PF on confined Schrödinger | **axiom** (proposed split) |
| **B2** | `C(a)` is bounded uniformly as `a → 0`, `Ns → ∞` (chessboard / FSS) | Deep — analogous to square `spectral_gap_uniform` | **axiom** (proposed split) |
| **C** | Combine A + B2 ⟹ `K · exp(C·σ²)` with `K=2`, `C = C₀/2` | Pure assembly | **theorem** (~50 lines) |

The square's `spectral_gap_uniform` (still open) is essentially **B2**
in disguise — they should share a discharge workstream.

### Newly-identified missing sub-pieces

Three pieces I missed in the original plan, all flagged by deep-think:
* **Compactness of `T = M_w ∘ Conv ∘ M_w`** on `L²(ℝ^{Ns})` —
  Hilbert-Schmidt norm bounds on the kernel. Required so the continuous
  spectrum doesn't swallow the gap. Belongs to B1.
* **Lattice Källén-Lehmann spectral representation** — Lean's spectral
  theorem is WIP; may need bespoke functional calculus for bounded
  self-adjoint operators. Required for the gap → variance bound step.
  Belongs to B1.
* **Griffiths-Simon approximation** (Ising Lee-Yang → continuous spins)
  — needed for Layer A unless someone proves continuous-spin Lee-Yang
  directly. ~2000+ line graph-theory/combinatorics campaign on its own.

## Total scope

**Revised post deep-think vet (2026-05-31): ~6000–8000 lines, 8–14
weeks** wall-clock (was ~2700-4500 / 3-8 weeks in the original plan).

| Discharge | Lines | Wall-clock |
|---|---|---|
| `wickConstantAsym_eq_variance` (2026-05-27) | ~500 | ~3 days |
| `asymChaosCutoffDecomposition` (UNIT 7, 2026-05-31) | ~900 (across UNITs 5+6+7) | ~9 days |
| `asymInteracting_expMoment_volume_uniform` (revised) | **~6000–8000** | **~8–14 weeks** |

The doubled estimate comes from:
* Layer A: Griffiths-Simon (Asano contractions → Ising Lee-Yang →
  continuous spins) is a 2000+ line graph-theory/combinatorics
  sub-project on its own, unless Mathlib gets Ising Lee-Yang first.
* Layer B4 / B2: chessboard / multiple-reflection RP algebra is
  2000-3000 lines, not 600-1500.
* Missing pieces (compactness + Källén-Lehmann + spectral-theorem
  workarounds) add another 500-1000 lines.

This is structurally a different beast — not a "port of proved square
machinery" (the square *itself* doesn't have it; `spectral_gap_uniform`
and `continuum_exponential_moment_bound` are both open). It's net-new
constructive QFT formalization.

## Reusable upstream extractions

The deep-think vet emphasized that Layer A (Newman) is "highly reusable
for generic spin systems" and that splitting into 4 axioms "allows
parallel workstreams." Rather than executing this all in pphi2, most of
the work should live in upstream / sister repos, where it stands as
general theorems independent of this project's specific lattice types.

Categorized targets:

### → Mathlib (pure combinatorics / functional analysis)

| Target | Where | Notes |
|---|---|---|
| **Asano contractions** on polynomials with prescribed-zero structure | `Mathlib.Algebra.Polynomial.Asano` (new) | Pure polynomial algebra; foundational for Lee-Yang |
| **Lee-Yang class** (polynomials with all zeros in unit disk / on circle) — closure under products, convolutions, Möbius transforms | `Mathlib.Analysis.LeeYang` (new) | Algebraic; ~Heilmann-Lieb-type |
| **Polynomial Lee-Yang theorem** (Newman 1974) for monotone-coefficient real polynomials with zeros on imaginary axis | as above | Direct from Asano + reduction |
| **Hilbert-Schmidt operators on `L²(ℝⁿ)`** with explicit kernel bounds via `∫∫ k² < ∞` | `Mathlib.Analysis.NormedSpace.HilbertSchmidt` (exists; may need extensions) | Operator-theoretic; needed for B1 compactness |
| **`e^{|x|} ≤ e^x + e^{-x}`** | exists or trivial | Convenience |

### → `gaussian-field` (Gaussian-specific, abstract setting)

| Target | Notes |
|---|---|
| **Newman MGF Gaussian-domination** abstracted: for any Lee-Yang positive measure `dμ` on `ℝ^n` and any linear `f : ℝ^n → ℝ`, `∫ e^{tf} dμ ≤ exp(t²·⟨f²⟩_μ / 2)` | The core Layer A theorem in pure form; no pphi2 types |
| **Griffiths-Simon approximation**: every Lee-Yang continuous-spin measure on `ℝ` arises as a weak limit of (Asano-rescaled) Ising spin measures | Pure measure theory + analysis; the bridge from Mathlib's combinatorial Lee-Yang to continuous-spin Lee-Yang |
| **Generic lattice reflection positivity** for nearest-neighbor Gaussian + even single-site interaction | Abstract over the lattice type (Z^d, Z_N^d, rectangular) and the interaction class |
| **Källén-Lehmann variance bound** from a positive-mass-gap self-adjoint generator | Spectral fact; pure functional analysis once we have the spectral theorem |

### → `markov-semigroups` (semigroup / transfer-matrix infrastructure)

| Target | Notes |
|---|---|
| **Infinite-dim Perron-Frobenius / Jentzsch** for compact positivity-improving operators | Already mostly in pphi2's `jentzsch_theorem` — could be lifted up |
| **Confined Schrödinger transfer matrix**: for `V : ℝⁿ → ℝ` with `V(x) → ∞` and reasonable growth, `T = e^{-tH}` with `H = -½Δ + V` is compact (often HS) on `L²(ℝⁿ)` | Generic Schrödinger theory; covers our transfer matrix as a special case |
| **Spectral gap from compact positivity-improving + confinement** | Combines the above into a packaged "compact + PI ⟹ isolated top eigenvalue ⟹ gap" result |

### → New repo `reflection-positivity` (or `chessboard`)

The chessboard / FSS algebra is general enough that it deserves its own
home. Candidates:

| Target | Notes |
|---|---|
| **Multiple-reflection / Cauchy-Schwarz reflection algebra** on a group with a Z/2 reflection | Abstract over the group; works for any RP measure |
| **Chessboard estimates** (Fröhlich-Simon-Spencer) | Reduces L¹ bounds for products of fields at separated sites to single-site / product-state bounds |
| **OS reflection positivity** for product / Gaussian measures | The "instance" library: this lattice has RP, this measure has RP, this transformation preserves RP |

This repo would be reusable across pphi2 (cylinder RP §5, chessboard
for `spectral_gap_uniform`), Phi4, OSforGFF, OSreconstruction, etc.

### Must stay in `pphi2`

| Piece | Why |
|---|---|
| Asym transfer matrix definition (`asymTransferOperatorCLM`) | Uses `AsymLatticeField Nt Ns` (project-specific) |
| The specific instantiation `asymInteracting_expMoment_volume_uniform_proof` | Glues the upstream general theorems to the asym types |
| Cylinder OS assembly (`cylinderIso_OS_of_RP_OS2` already exists) | Project-specific endpoint |

**Net effect of the extraction strategy**:

| Repo | Lines | What it produces (reusable beyond pphi2) |
|---|---|---|
| Mathlib | ~1500-2500 | Asano + Lee-Yang polynomial class + HS operator extensions |
| `gaussian-field` | ~1500-2500 | Newman MGF / Griffiths-Simon / general lattice RP / Källén-Lehmann |
| `markov-semigroups` | ~500-800 | Compact-PI spectral gap (generalized) |
| `reflection-positivity` (new) | ~1500-2500 | Chessboard / multiple-reflection algebra |
| `pphi2` | ~500-800 | Instantiation glue + assembly |
| **Total** | **~5500-9000** | **Most of it reusable for other QFT projects** |

The bulk of the discharge does NOT need to live in pphi2. Done right,
this campaign would substantially strengthen the upstream constructive
QFT / harmonic-analysis / Gaussian / Schrödinger infrastructure
available to *every* downstream project.

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

## Recommendation (revised post-vet)

**Option 2 (4-axiom split) with extraction-first execution.** With the
revised scope of 6000-8000 lines and the deep-think recommendation to
split into 4 axioms (A + B1 + B2 + C theorem), the right plan is:

1. **Cheap structural move first** (~1-2 days): split the single axiom
   into A + B1 + B2, prove C as the assembly theorem. Each piece is
   then individually deep-think-vettable; the axiom count goes from 1
   to 3 on this branch but the *conceptual* clarity is far higher.
2. **Discharge from the bottom up via upstream extraction** (see
   "Reusable upstream extractions" §): Mathlib first (Asano + Lee-Yang
   polynomial class), then `gaussian-field` (Newman MGF abstract +
   Griffiths-Simon), then `markov-semigroups` (compact-PI gap), then
   new `reflection-positivity` repo (chessboard) in parallel.
3. **pphi2 instantiation last** (~500-800 lines): once all the upstream
   pieces are in place, the pphi2 file is just glue.

**Total wall-clock** with extraction-first: same 8-14 weeks, but the
**output** is ~5500-9000 lines of generically-useful upstream
infrastructure plus a clean 500-800-line pphi2 instantiation, rather
than a 6000-8000-line pphi2-only monolith. The reusability multiplier
is real: every constructive-QFT downstream (Phi4, OSforGFF,
OSreconstruction, future Higgs / gauge work) inherits the Lee-Yang,
chessboard, and confined-Schrödinger infrastructure for free.

**Option 3 (keep as single axiom) remains the right call for the
near-term cylinder campaign** if higher-leverage targets exist
elsewhere — the axiom is well-vetted, the form is correct, and 8-14
weeks is a substantial investment. Candidates for higher leverage:
* Extending the cylinder construction to the full square-lattice case
* Discharging `embed_l2_uniform_bound` upstream
* The cylinder OS3 / hRP / hOS2 hypothesis chain
* The square's own `spectral_gap_uniform` (which shares the Layer B2
  discharge path)

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
