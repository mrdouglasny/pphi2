# L1 working doc — uniform `‖V‖_{L²(μ_GFF)}` (next uniform-discharge brick)

Branch: `uniform-discharge-L1` (off `main` @ 9d4e1e4, post-PR#38). Status: L4 complete
(`UniformBounds.lean`); this is the next brick. Full roadmap: `planning/uniform-remainder-roadmap.md`.

## Target

```
theorem interaction_sq_integral_le_uniform (L mass) (hL : 0 < L) (hmass : 0 < mass)
    (P : InteractionPolynomial) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N],
      ∫ ω, (interactionFunctional 2 N P (circleSpacing L N) mass ω)^2
        ∂(latticeGaussianMeasure 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass) ≤ C
```
i.e. `⟨V²⟩₀ ≤ C` uniform in `N`. (Equivalently `‖V‖_{L²} ≤ √C`; this feeds L3 → L4.)

## ★ BETTER ROUTE (2026-06-06): reuse the Nelson smooth/rough decomposition

Do NOT build `⟨V²⟩₀ = a⁴∑_{z,w}C^m` from scratch. Instead reuse the Nelson decomposition
(`NelsonEstimate/RoughErrorBound.lean`, `FieldDecomposition.lean`):
- `canonicalFullInteractionJoint = interactionFunctional` **exactly** (`canonicalFullInteractionJoint_eq_interactionFunctional`), `V = V_smooth + V_rough` (`canonicalRoughError = full − smooth`).
- **Bridge** `integral_comp_canonicalSumConfig` (FieldDecomposition.lean:4221): `∫ F(V) dμ_GFF = ∫ F(V_full) dμ_joint` for measurable `F`. Mirror `integral_exp_neg_interaction_sq_eq_canonicalJoint` (RoughErrorBound.lean:123) with `F = (·)²` to get `∫ V² dμ_GFF = ∫ V_full² dμ_joint`.
- Then `‖V_full‖_{L²} ≤ ‖V_smooth‖_{L²} + ‖V_rough‖_{L²}` (Minkowski; or `∫V_full² = ∫V_s² + 2∫V_sV_r + ∫V_r²`, and smooth⊥rough chaos may give `∫V_sV_r=0` via `integral_sum_mul_sum_eq_zero_of_orth` RoughErrorBound.lean:2093).
- **`‖V_rough‖_{L²}` — CITABLE**: `canonicalRoughError_leading_l2_sq` (RoughErrorBound.lean:2422) + the rough-variance machinery; uniform in N at fixed cutoff `T`.
- **`‖V_smooth‖_{L²}` — the one piece to BUILD**: `V_smooth = a²∑:P(φ_S):`, needs smooth-covariance summability `a⁴∑_{x,y}C_smooth(x,y)^m ≤ uniform`. Smooth covariance is `canonicalSmoothCovariance_eq_sum_gamma_mul_gamma` (FieldDecomposition.lean:2842, Gram form); needs a pow-sum bound (no smooth analog of `canonicalRoughCovariance_pow_sum_le_uniform_in_aN` yet — build it, or bound via `smoothWickConstant_le_log_uniform_in_aN` + row-sum).
- **First concrete brick**: ✅ DONE — `integral_interaction_sq_eq_canonicalJoint` (`InteractionL2.lean`,
  the bridge `∫V² dμ_GFF = ∫V_full² dμ_joint`, axiom-clean).

### Remaining L1 assembly (2026-06-06 — all prerequisites located, both are cross-term Wick assemblies)
On the joint measure `φ_S ⊥ φ_R` (independent), `⟨V_full²⟩ = a⁴∑_{x,y}∑_m coeff_m²·m!·` (block-diagonal
Wick: smooth contractions give `C_smooth^{m-j}`, rough give `C_rough^j`). So both sides reduce to
covariance pow-sums, all of which EXIST:
- **rough `∫V_rough²`**: `canonicalRoughError_leading_l2_sq` (RoughErrorBound.lean:2422, the L²-sq
  cross-term *identity*) + per-cross-term bound `∫ canonicalCrossTerm² ≤ uniform`, assembled from
  `canonicalRoughCovariance_pow_one_sum_le_uniform_in_aN_proved` (CovarianceBoundsGJ.lean:709),
  `_pow_two_sum_…:851`, `_pow_sum_…_of_three_le:1297`. The `∫crossTerm²` → pow-sum assembly is the work
  (no single citable `∫crossTerm² ≤ C` for the symmetric torus — the asym track has it,
  `AsymRoughErrorChaosStd.lean`; port or re-derive).
- **smooth `∫V_smooth²`**: `smoothVariance_le_log_uniform` (CovarianceSplit.lean:112, the DIAGONAL
  smooth covariance ≤ log, uniform) — need the smooth-covariance POW-SUM (row-sum) analogue, then the
  same cross-term Wick assembly. Build the smooth pow-sum (parallel to the rough ones).
- **assembly**: Minkowski `‖V_full‖ ≤ ‖V_s‖+‖V_r‖` (or `∫V_full² = ∫V_s²+2∫V_sV_r+∫V_r²`, with
  `∫V_sV_r=0` from smooth⊥rough chaos orthogonality, `integral_sum_mul_sum_eq_zero_of_orth:2093`).
- **Verdict**: deep but fully de-risked — the covariance pow-sum BOUNDS (the hard analytic core) are
  proved; remaining = the cross-term Wick L² assembly tying them to `⟨V²⟩₀`. A focused fresh-context job.

## Three sub-steps (ORIGINAL from-scratch plan — superseded by the decomposition route above)

**(i) Product integrability** — `Integrable (fun ω => W_z ω * W_w ω) μ_GFF`, `W_z = wickPolynomial P c (ωδ_z)`.
Cleanest route: AM–GM `|W_z W_w| ≤ ½(W_z² + W_w²)` (`mono'`), reduce to same-site `Integrable (W_z²)`.
For `W_z²`: expand `wickPolynomial² = ∑_{i,j} (coeff_i)(coeff_j)·wickMonomial_i·wickMonomial_j` (same
site); each `wickMonomial_i(ωδ_z)·wickMonomial_j(ωδ_z)` is a polynomial in the single pairing `(ωδ_z)`,
integrable. **Reusable infra** (`MomentIntegrability.lean`): `integrable_pow_pairing` (`(ωf)^n`),
`integrable_pow_pairing_mul` (`(ωf)^n(ωg)^m`), `integrable_powMul_wickMonomial` (`(ωf)^n(ωδ_z)^l·wickMon_k`),
`integrable_powMul_wickPolynomial` (`(ωf)^n·wickPoly(ωδ_z)`). Note: same-site `wickMon_i·wickMon_j`
isn't a direct powMul form — may need a small `wickMonomial`-product integrability helper (strong
induction on degree, mirroring `integrable_powMul_wickMonomial`), OR expand to powers.

**(ii) Exact `⟨V²⟩₀` identity** — `∫ V² = a⁴ ∑_{z,w} ∫ W_z W_w` (expand `(a²∑W_z)²`, `integral_finset_sum`
using (i)), and per pair `∫ W_z W_w = ∑_m (coeff'_m)²·m!·C(z,w)^m` where `coeff'_m` are `P`'s
coefficients (`1/n` leading; `coeff_m` lower) and `C(z,w) = gffPositionCovariance z w`. **Infra**:
`gff_wickPower_two_smeared_inner` (`WickMultivariate.lean:1202`) gives the per-monomial
`∫ wickMon_m(ωδ_z)·wickMon_n(ωδ_w) = δ_{mn} m! (gffSmearedCovariance δ_z δ_w)^m`, and
`gffSmearedCovariance δ_z δ_w = gffPositionCovariance z w` (bridge in `WickConstantBridge.lean`).
Cross-monomial orthogonality (`m≠n → 0`) kills the off-diagonal-degree terms.

**(iii) Uniform bound** `a⁴ ∑_{z,w} C(z,w)^m ≤ C_m` (the deep part, m=1..P.n). The 2D
log-singular `C` is `L^m`-integrable; the divergent diagonal `C(z,z)^m = c^m` is killed by
`a⁴·#sites = a²·L² → 0`. **Infra** (`NelsonEstimate/CovarianceBoundsGJ.lean`):
`canonicalRoughCovariance_pow_sum_le_uniform_in_aN` (`a^d ∑_y |C_rough x y|^m ≤ C_m·T`, ROW sum) —
double-sum via `a^d ∑_x [row] ≤ a^d·#sites·C_m·T = L^d·C_m·T` (`torus_volume_eq`, `UniformBounds.lean`).
**Catch**: this is the ROUGH covariance; full `C = C_smooth + C_rough`. Either (a) binomial-expand
`C^m`, bound `C_smooth` via the smooth-covariance bounds (`smoothWickConstant_le_log_uniform_in_aN`)
and `C_rough` via the above, or (b) find/prove a full-`C` pow-sum bound directly (the diagonal-killed
Riemann-sum argument). This step mirrors part of the Nelson exp-estimate proof and is the genuine work.

## Critical correctness notes (do NOT regress)
- **`V` is NOT uniformly bounded below** — the 2D Wick constant `c_a ∼ (1/2π)ln(1/a)` log-diverges, so
  `:φ⁴:_c ≥ −6c²` blows up. `‖V‖_{L²}` is uniform only via the exact `a⁴∑C^m` computation (diagonal
  killed by `a⁴`), NOT a pointwise bound. (This is why L4 uses Cauchy–Schwarz + Nelson, not `V≥−B`.)
- Axiom scoped to `P.n = 4` (pure quartic) — but L1 works for general `P` (sum over `m ≤ P.n`).
- Keep everything axiom-clean; build `lake build Pphi2.InteractingMeasure.UniformBounds` after each lemma.

## Downstream
L1 → **L2** (hypercontractivity `L²→L^p` for `V`, deg-4 Wick; field version `gaussian_hypercontractivity_continuum`
exists) → **L3** (`⟨φ(f)^{2n}V^{2k}⟩₀ ≤ K₀` via Cauchy–Schwarz) → **L4** (done) → **L5** (`u₄''` `C²`,
hardest) + **s** (leading-term lower bound) → **L6+F** ⟹ the axiom.
