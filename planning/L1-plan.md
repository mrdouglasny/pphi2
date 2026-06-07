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
  Needs the smooth-field Wick L² formula (analogue of canonicalCrossTerm_l2_sq_eq_covSum for the pure
  smooth interaction = ∑ of j=k crossTerms), then M1. The deep piece (mirrors rough machinery).
- **M3 cross vanishing**: `∫ V_smooth · V_rough dμ_joint = 0` (smooth⊥rough chaos), from the field
  orthogonality + chaos-layer argument.
- **M4 assembly**: fix T=1 (kills log factors): ∫V_full²(T=1) = ∫V_s² + ∫V_r² (cross=0) ≤ K_s+K_r;
  bridge at T=1 ⟹ ∫V²dμ_GFF ≤ K_s+K_r. ⟹ `interaction_variance` uniform.

## Order
1. **M1** (smooth double-sum) — clean, self-contained. Build first.
2. **M2** (smooth variance) — the hard core; needs smooth Wick L² formula.
3. **M3** (cross=0), **M4** (T=1 assembly + bridge) ⟹ L1.

Then L1 → L2 (`interacting_moment_bound` exists) → L3 (Cauchy–Schwarz) → L5(ii) (the u₄'' bound,
using D2's `moment_hasDerivAt2`) → L6F (feed s+K into `exists_uniform_neg_of_uniform_affine_bound'`).
