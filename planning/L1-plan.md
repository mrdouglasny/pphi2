# L1 — uniform `∫ V² dμ_GFF ≤ C(m,L)` (the K-leaf analytic core)

Branch: `uniform-discharge-L1` (off `main` @ 8d71475). Goal: `∃ C, ∀ N, ∫ V² dμ_GFF ≤ C`
uniform in N (torus a=L/N), V = interactionFunctional 2 N P a mass. Feeds L3 → L5 → discharge.

## Survey (2026-06-06): what EXISTS vs what's MISSING

**DONE (reuse directly):**
- **Bridge**: `integral_interaction_sq_eq_canonicalJoint` (InteractionL2.lean:36) —
  `∫ V² dμ_GFF = ∫ V_full² dμ_joint` for ANY T>0 (so ∫V_full² is T-independent, = ∫V²dμ_GFF).
- **Decomposition**: V_full = V_smooth + V_rough. `canonicalFullInteractionJoint_eq_interactionFunctional`
  (RoughErrorBound:104); `canonicalRoughError = full − smooth` (RoughErrorBound:99).
- **ROUGH variance DONE**: `rough_error_variance` (RoughErrorBound:3299) —
  `∫ (canonicalRoughError)² dμ_joint ≤ K·T·(1+|log T|)^{P.n−1}`, uniform in (N,a) at fixed L.
- **cross orthogonality pieces**: `canonicalSmoothRough_cross_moment_zero` (FieldDecomposition:818,
  field level ∫φ_S(x)φ_R(y)=0); `integral_sum_mul_sum_eq_zero_of_orth` (RoughErrorBound:2093).
- **smooth covariance bounds**: `abs_canonicalSmoothCovariance_le_smoothWickConstant`
  (FieldDecomposition:3812, |C_smooth(x,y)| ≤ smoothWickConstant); `smoothWickConstant_le_log_uniform_in_aN`
  (CovarianceBoundsGJ:1536, smoothWickConstant ≤ A+B(1+|log T|) uniform).
- **smooth Wick moment hint**: `canonicalCrossTerm_l2_sq_eq_covSum` (RoughErrorBound:2862) gives
  `∫(crossTerm k j)² = (a^d)²·j!·(k−j)!·∑_{x,y} C_smooth^j C_rough^{k−j}` — the j=k case is the pure
  smooth Wick moment `(a^d)²·k!·∑_{x,y}C_smooth^k`. BUT `canonicalCrossTerm_l2_sq_le` (:3057) only
  bounds the j<k (rough) terms (needs 1≤k−j); the j=k smooth terms are NOT covered.

**MISSING (the L1 work):**
- **M1 smooth double-sum bound** ✅ DONE (InteractionVariance.lean,
  `canonicalSmoothCovariance_pow_double_sum_le`, axiom-clean): `a^{2d}∑_{x,y}|C_smooth(x,y)|^m ≤
  (L^{2d}(A+B)^m+1)·(1+|log T|)^m` uniform, from the pointwise bound + a^d·card=L^d.
- **M2 smooth variance**: `∫ (canonicalSmoothInteraction)² dμ_joint ≤ K_s·(1+|log T|)^{P.n}` uniform.
  ROUTE B (de-risked, NO orthogonality/Pythagorean needed):
  • **M2a** ✅ DONE (`canonicalSmoothInteraction_eq_sum_crossTerm_diag`, InteractionVariance.lean):
    `V_s = (1/P.n)·crossTerm(P.n,P.n) + ∑_m coeff_m·crossTerm(m,m)` (diagonal cross-terms).
  • **M2c** ✅ DONE (`canonicalCrossTerm_diag_l2_sq_le`, InteractionVariance.lean): per-term bound
    `∫(crossTerm(k,k))² ≤ k!·C·(1+|log T|)^k` uniform (covSum at j=k + M1). Axiom-clean.
  • **M2b** (the assembly, REMAINING — final M2 piece): bound `∫V_s²` by **pointwise Cauchy–Schwarz**
    `(∑ cᵢ gᵢ(η))² ≤ (∑cᵢ²)(∑gᵢ(η)²)` (`Finset.sum_mul_sq_le_sq_mul_sq`) under the integral — split
    lead+∑ via `(a+b)²≤2a²+2b²`, integrability from `canonicalCrossTerm_pair_integrable`
    (RoughErrorBound:2775) via M2a, integral_mono/integral_finset_sum/integral_const_mul, per-term via
    M2c, collect the finitely many M2c constants (choose over Fin P.n) into one. ~100 lines.
  This route AVOIDS the deep diagonal-orthogonality lemma (canonicalCrossTerm_inner_eq_zero needs
  j<k, fails for j=k) — Cauchy–Schwarz is cruder but uniform, which is all L1 needs. ~80 focused lines.
- **M3 cross vanishing**: NOT NEEDED — use `(a+b)²≤2a²+2b²` instead of orthogonality:
  `∫V_full² ≤ 2∫V_s² + 2∫V_r²`.
- **M4 assembly** (NEXT, but BLOCKED on integrability): fix T=1 (kills log factors):
  `∫V_full² ≤ 2∫V_s² + 2∫V_r²` (integral_mono_of_nonneg + pointwise (a+b)²≤2a²+2b²) ≤ 2C_s + 2C_r
  (M2 `canonicalSmoothInteraction_variance_le` + `rough_error_variance`); bridge
  `integral_interaction_sq_eq_canonicalJoint` ⟹ `∫V²dμ_GFF ≤ 2C_s+2C_r` uniform = L1.
  ★ BLOCKER: `integral_mono_of_nonneg` needs `2V_s²+2V_r²` **integrable on canonicalJointMeasure**,
  i.e. `Integrable (V_rough²)` and `Integrable (V_smooth²)`. NEITHER is exposed:
  - `V_rough²` integrability lives ONLY inside `rough_error_variance`'s proof (RoughErrorBound.lean
    ~3878 `hsq_integrable`), behind PRIVATE chaos lemmas (`canonicalCrossTermStd_mem_wienerChaosLE`
    :1647, `canonicalCrossTermLinearCombo_mem_wienerChaosLE` :1759). NEXT STEP: add a public
    `canonicalRoughError_sq_integrable` to RoughErrorBound.lean by extracting that ~15-line block
    (or `canonicalRoughError_memLp_two`).
  - `V_smooth²` integrability: derivable in InteractionVariance via `Integrable.mono'` with the M2b
    bound function (V_s² ≤ bound, bound integrable from `canonicalCrossTerm_pair_integrable`) — needs
    V_smooth AEStronglyMeasurable. Self-contained once attempted.
  - (NOTE: `V²` IS integrable on the GFF side — `integrable_powMul_interaction_sq` at n=0 — but that's
    the GFF measure, not the joint; doesn't directly give joint-side V_s²/V_r².)

## Order
1. **M1** (smooth double-sum) — clean, self-contained. Build first.
2. **M2** (smooth variance) — the hard core; needs smooth Wick L² formula.
3. **M3** (cross=0), **M4** (T=1 assembly + bridge) ⟹ L1.

Then L1 → L2 (`interacting_moment_bound` exists) → L3 (Cauchy–Schwarz) → L5(ii) (the u₄'' bound,
using D2's `moment_hasDerivAt2`) → L6F (feed s+K into `exists_uniform_neg_of_uniform_affine_bound'`).
