# Roadmap — `N`-uniform remainder closing `torus_weakCoupling_lattice_connectedFourPoint_strictNeg`

Vetted by Gemini deep-think (2026-06-05; see `gemini-uniform-remainder-questions.md` for the prompt).
The perturbative core (steps I–III) is **done, axiom-free** (`U4Derivative.lean`); the headline axiom
needs only to feed **uniform-in-N** constants `s, K, g₀` into `deriv_affine_bound_neg`.

## Strategy (confirmed)

- **Route:** the affine derivative bound `u₄'(t) ≤ −s + K·t` on `[0,g₀]` (⟺ `sup|u₄''| ≤ K`). Two-sided
  `u₄''` bound, NOT Lebowitz/convexity — modular and reuses the `NelsonEstimate` `Lᵖ` machinery.
- **Why uniform works (fixed torus):** the 2D covariance `C_a(x−y) ∼ −ln|x−y|` has `C_a^n` locally
  integrable for all `n`, so Wick-polynomial `L²` norms (e.g. `‖V‖_{L²}`) are uniform in `N`; Nelson
  hypercontractivity lifts `L² → Lᵖ` uniformly. **CORRECTION (2026-06-05):** `V` is **NOT** uniformly
  bounded below — the 2D Wick constant `c_a ∼ (1/2π)ln(1/a)` log-diverges, so `:φ⁴:_c ≥ −6c²` blows up
  and the naive `V ≥ −L²A` is **false** (`wickConstant_le_inv_mass_sq` gives only `(a²)⁻¹m⁻²`). The
  uniform control instead comes from: (i) `Z_t ≥ 1` (Jensen + `⟨V⟩₀ = 0`, since `⟨:φ⁴:_c⟩₀ = 0`);
  (ii) the **Nelson exp-estimate** `∫e^{−2V}dμ_GFF ≤ K` uniform, hence `∫e^{−2tV} ≤ K^t ≤ max(1,K)`
  for `t∈[0,1]` (Hölder); (iii) `‖V‖_{L²}` uniform despite the divergent diagonal (`a⁴·c_a⁴·card =
  a²L²c_a⁴ → 0`). This is why Nelson is essential — there is no pointwise-lower-bound shortcut.
- **Worst term** in `u₄''`: `⟨φ(f)⁴V²⟩₀ ≤ ‖φ(f)‖_{L⁸}⁴·‖V‖_{L⁴}²` (Cauchy–Schwarz). Need `L⁸` for
  `φ(f)`, `L⁴` for `V` — both uniform.

## Skeleton (2026-06-06): connective assembly PROVED; problem reduced to leaves

The monolithic uniform axiom is now reduced to a small leaf set, with the **connective tissue proved**:
- ✅ `exists_uniform_neg_of_uniform_affine_bound` (`UniformBounds.lean`) — `i`-uniform upgrade of
  `deriv_affine_bound_neg`: `(∀i, φ_i 0=0) + (∀i, diff on [0,g₀]) + (∀i, φ_i'(t)≤−s+Kt)` ⟹
  `∃ g c>0, ∀i, φ_i g ≤ −c`. Feed `φ_N = u₄` of the Gibbs family.
- ✅ `integral_interaction_sq_eq_canonicalJoint` (`InteractionL2.lean`) — L1 bridge.

**Connective lemma (corrected interface, 2026-06-06):** `exists_uniform_neg_of_uniform_affine_bound'`
(`UniformBounds.lean`) — uses **`ContinuousOn [0,g₀]` + `HasDerivAt` on the OPEN `(0,g₀)`** (NOT
`HasDerivAt` on `Icc`). Reason: the `u₄` Gibbs family has no two-sided derivative at `g=0` —
`∫e^{-gV}` diverges for `g<0` (Dyson). MVT (`exists_hasDerivAt_eq_slope`) only needs interior
derivative + continuity. (`deriv_affine_bound_neg_of_continuousOn` is the per-`N` MVT step.)

**Remaining = the leaf hypotheses for `φ_N = u₄`** (each a bounded, mostly-mechanical job):
1. **`h0`** `u₄_N(0)=0` — ✅ `u4_at_zero` (already proved per N).
2. **`hcont`** `ContinuousOn u₄_N [0,g₀]` — NEW: continuity of the normalised moments
   `M_n(g)=∫(ωf)ⁿe^{-gV}/Z_g` in `g` (dominated convergence; `Z_g≥1>0` via `partitionFn_ge_one`).
3. **`hderiv`** `∀t∈(0,g₀), HasDerivAt u₄_N (u₄'_N t) t` — NEW: re-do the differentiation chain
   (bricks 2–5) at a general interior `t`, **two-sided** (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`,
   the standard Mathlib lemma; domination near `t` by `e^{(3t/2)|B|}|(ωf)ⁿV|`, brick 1). First sub-brick:
   `moment_hasDerivAt` (general `t`) → `Z'_t` → `M_n'_t` (quotient) → `u₄'_t` (product).
3. **`hbound`** `u₄'_N(t) ≤ −s + Kt` uniform, which splits into the two textbook estimates:
   - **leading slope `s`**: `u₄'_N(0) = −6a²∑(C_a f)⁴ ≤ −s` uniform (Riemann/low-mode; the `s`-leaf).
   - **second-order `K`**: `u₄'_N(t) − u₄'_N(0) ≤ Kt`, i.e. `|u₄''_N| ≤ K` uniform — from the moment
     bounds `⟨φ(f)ⁿV^k⟩` (L1 `‖V‖_{L²}` → L2 chaos-hypercontractivity → L3 Cauchy–Schwarz; `boltzmann_cauchySchwarz`+`partitionFn_ge_one`+`expMoment_le_rpow` done).
4. **framing**: `torusConnectedFourPoint(map ι μ) = connectedFourPoint μ (ι*f)` + mass↔g
   (`FieldRedefinition`) to land on `torusInteractingMeasure`.

Each leaf is derivable (per the don't-axiomatize-the-derivable rule) — the deep analysis (covariance
pow-sums) is already proved. Convert a leaf to a cited+vetted textbook axiom (Glimm–Jaffe Ch.8 / Simon
V,VIII) only if it proves genuinely beyond reach.

## Lemma decomposition (with infra status)

| # | Lemma | Statement | Status |
|---|-------|-----------|--------|
| **L1** | uniform `L²` of `V` | `‖V_N‖²_{L²(μ_GFF)} = ⟨V²⟩₀ = 24·a⁴∑_{z,w}C_a(z,w)⁴ ≤ C(m,L)` uniform in N | **NEW** — `⟨V²⟩₀` part is `gff_wickPower_two_smeared_inner` (`n=m=4`) + the `δ_z/δ_w` bridge; the uniform bound on `a⁴∑_{z,w}C_a(z,w)⁴` uses `NelsonEstimate/CovarianceBoundsGJ`, `HeatKernelBound` (2D propagator summability, fixed volume) |
| **L2** | hypercontractivity `Lᵖ` lift | `‖W‖_{Lᵖ} ≤ (p−1)^{d/2}‖W‖_{L²}` for degree-`d` Wick `W` ⟹ `‖V‖_{L⁴}`, `‖φ(f)‖_{L⁸}` uniform | **MOSTLY EXISTS** — `gaussian_hypercontractivity_continuum` gives the lift for `|ω f|` (field). Need the analogous lift applied to `V` (degree-4 Wick), via the same Nelson route |
| **L3** | free `L²` moment bound | `‖φ(f)ⁿV^k‖²_{L²(μ_GFF)} = ⟨φ(f)^{2n}V^{2k}⟩₀ ≤ K₀` (n≤4, k≤2, so up to `φ(f)⁸V⁴`) — Cauchy–Schwarz `≤ ‖φ(f)‖_{L^{4n}}^{2n}‖V‖_{L^{4k}}^{2k}` + L2 (uniform `L^{16}` of `φ(f)`, `L^8` of `V`) | **NEW** (combinational, on top of L1/L2) |
| **L4** | interacting → free pull-back | `⟨\|X\|⟩_t = ∫\|X\|e^{−tV}/Z_t ≤ ‖X‖_{L²(μ_GFF)}·√(∫e^{−2tV})/Z_t ≤ ‖X‖_{L²}·√K` (`X = φ(f)ⁿV^k`), via **Cauchy–Schwarz + Nelson exp-estimate** and `Z_t ≥ 1` — NOT a pointwise `V ≥ −B` bound (that is false) | ✅ **DONE** (`UniformBounds.lean`): `interactionFunctional_integral_nonpos` (`⟨V⟩₀≤0`), `partitionFn_ge_one` (`Z_t≥1`), `expMoment_le_rpow` (`∫e^{−sV}≤(∫e^{−2V})^{s/2}`), `boltzmann_cauchySchwarz` (the pull-back). Remaining: a one-line composition of these + plumb `nelson_exponential_estimate` to the torus params (`∫e^{−2V}≤K`) for the final `⟨\|X\|⟩_t ≤ ‖X‖_{L²}·√K` |
| **L5** | `u₄''` assembly (the slog) | expand `u₄''(t)` as a moment polynomial; apply L4 termwise ⟹ `sup_{[0,g₀]}\|u₄''(t)\| ≤ K`, uniform. Plus `∀ t∈[0,g₀], HasDerivAt u₄ (u₄' t) t` (extend `MomentDerivative` from `g=0` to general `t`) | **NEW** — largest piece; needs `u₄ ∈ C²` on `[0,g₀]` |
| **s** | leading-term lower bound | `6·a²∑_z(C_a f)(z)⁴ ≥ s > 0` uniform: pick `f` = lowest non-zero `−Δ+m²` eigenmode on T²; `a²∑(C_a f)⁴ → ∫_{T²}(C f)⁴ > 0` (Riemann sum, `TorusPropagatorConvergence`) | **NEW** (self-contained; good independent start) |
| **L6** | affine application | feed `s` (from `s`-lemma) and `K` (from L5) into `deriv_affine_bound_neg`; `g₀` any fixed positive, `g = min(g₀, s/(2K))` | **interface DONE** (`deriv_affine_bound_neg`) |
| **F** | framing | field-rescaling `mass↔g` (commutes with N-uniformity — rescale depends on mass not N) + torus-embedding pullback `torusConnectedFourPoint (map ι μ) f = connectedFourPoint μ (ι*f)` ⟹ the axiom | **NEW** — bookkeeping via `FieldRedefinition.lean` |

**Hardest sub-lemma:** L5 (the `u₄''` algebraic assembly + `C²` regularity). L1 is the most concrete
*first* step (connects to the smeared-Wick kernel already proved); `s` is the cleanest *independent*
start.

## References
Simon *P(φ)₂* Ch. V.3 (uniform `Lᵖ` of Wick polynomials / hypercontractivity, `∫:φ⁴:` bounds),
Ch. VIII (Taylor / weak-coupling). Glimm–Jaffe Ch. 8.5 (quantitative polynomial bounds), Ch. 9
(`φ⁴` functional-integration mechanics).

## Suggested order
1. **`s`** (leading-term lower bound) — self-contained, validates the test-function choice.
2. **L1** (uniform `‖V‖_{L²}`) — reuses `gff_wickPower_two_smeared_inner`; the covariance-summability
   core.
3. **L2/L3/L4** (the `Lᵖ` chain to `⟨|φ(f)ⁿV^k|⟩_t ≤ K`).
4. **L5** (the `u₄''` slog + `C²`).
5. **L6 + F** (assembly + framing) ⟹ axiom discharged.
