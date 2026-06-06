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

## Lemma decomposition (with infra status)

| # | Lemma | Statement | Status |
|---|-------|-----------|--------|
| **L1** | uniform `L²` of `V` | `‖V_N‖²_{L²(μ_GFF)} = ⟨V²⟩₀ = 24·a⁴∑_{z,w}C_a(z,w)⁴ ≤ C(m,L)` uniform in N | **NEW** — `⟨V²⟩₀` part is `gff_wickPower_two_smeared_inner` (`n=m=4`) + the `δ_z/δ_w` bridge; the uniform bound on `a⁴∑_{z,w}C_a(z,w)⁴` uses `NelsonEstimate/CovarianceBoundsGJ`, `HeatKernelBound` (2D propagator summability, fixed volume) |
| **L2** | hypercontractivity `Lᵖ` lift | `‖W‖_{Lᵖ} ≤ (p−1)^{d/2}‖W‖_{L²}` for degree-`d` Wick `W` ⟹ `‖V‖_{L⁴}`, `‖φ(f)‖_{L⁸}` uniform | **MOSTLY EXISTS** — `gaussian_hypercontractivity_continuum` gives the lift for `|ω f|` (field). Need the analogous lift applied to `V` (degree-4 Wick), via the same Nelson route |
| **L3** | free `L²` moment bound | `‖φ(f)ⁿV^k‖²_{L²(μ_GFF)} = ⟨φ(f)^{2n}V^{2k}⟩₀ ≤ K₀` (n≤4, k≤2, so up to `φ(f)⁸V⁴`) — Cauchy–Schwarz `≤ ‖φ(f)‖_{L^{4n}}^{2n}‖V‖_{L^{4k}}^{2k}` + L2 (uniform `L^{16}` of `φ(f)`, `L^8` of `V`) | **NEW** (combinational, on top of L1/L2) |
| **L4** | interacting → free pull-back | `⟨\|X\|⟩_t = ∫\|X\|e^{−tV}/Z_t ≤ ‖X‖_{L²(μ_GFF)}·√(∫e^{−2tV})/Z_t ≤ ‖X‖_{L²}·√K` (`X = φ(f)ⁿV^k`), via **Cauchy–Schwarz + Nelson exp-estimate** and `Z_t ≥ 1` — NOT a pointwise `V ≥ −B` bound (that is false) | **FOUNDATION DONE** (`UniformBounds.lean`): ✅ `interactionFunctional_integral_nonpos` (`⟨V⟩₀≤0`), ✅ `partitionFn_ge_one` (`Z_t≥1`, uniform `c=1`), ✅ `expMoment_le_rpow` (`∫e^{−sV}≤(∫e^{−2V})^{s/2}`). Remaining: the Cauchy–Schwarz assembly + plumb `nelson_exponential_estimate` for the torus params (`∫e^{−sV}≤K` uniform) |
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
