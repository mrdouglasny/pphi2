# L3 — free L² moment bound `⟨φ(f)^{2n}V^{2k}⟩₀ ≤ K₀` (and the K-leaf remainder)

Branch: `k-leaf-l3` (off `main` post-#45). L2-for-V is merged (`interaction_moment_le`:
`∃K,∀N, ∫V^{2m}dμ_GFF ≤ K`, axiom-clean).

## L3 target
`⟨φ(f)^{2n}V^{2k}⟩₀ = ∫(ωf)^{2n}·V^{2k} dμ_GFF ≤ K₀` uniform (n≤4, k≤2, so up to φ⁸V⁴), for the
discharge's test function `f`. Feeds L4 (`interacting_moment_le_L2_of_expBound`): `⟨|φⁿVᵏ|⟩_t ≤
‖φⁿVᵏ‖_{L²}·√K`, with `‖φⁿVᵏ‖_{L²}² = ⟨φ^{2n}V^{2k}⟩₀`.

## Route (Cauchy–Schwarz) + the bricks — ✅ DONE (all axiom-clean)
`∫(ωf)^{2n}V^{2k} ≤ (∫(ωf)^{4n})^{1/2}·(∫V^{4k})^{1/2}` (`integral_mul_le_Lp_mul_Lq_of_nonneg`,
Hölder 2,2). All bricks landed:
- **∫V^{4k} ≤ K**: ✅ `interaction_moment_le` (m=2k).
- **L3a — `interaction_memLp`** ✅ (`InteractionVariance.lean`): `MemLp V p (μ_GFF)` for `p≥2`
  (generalised to arbitrary `a>0`), via `canonicalFullInteractionJoint_memLp` (exposed in
  RoughErrorBound) + bonami + the std-Gaussian MeasurePreserving transfer +
  `canonicalJointMeasure_map_canonicalSumConfig`. Plus `interactionFunctional_pow_integrable`
  (per-N integrability of `Vⁿ`, n≥2).
- **L3b — field hypercontractivity** ✅ `field_pow_le_second_pow` (`InteractionVariance.lean`):
  `∫(ωf)^{2m} ≤ (2m-1)^m·(∫(ωf)²)^m` for ALL m, direct from `gaussian_hypercontractive` (n=1,p=2m).
  Variance closed form `normConst_second_moment` (`FreeMomentBound.lean`):
  `∫(ωf)² = (a^d·#sites·m²)⁻¹` (variance bridge + covariance row-sum), `= (L²m²)⁻¹` on the torus.
- **L3c — Cauchy–Schwarz** ✅ `free_product_moment_cauchy_schwarz` (`InteractionVariance.lean`),
  assembled into the uniform-in-N `torus_free_product_moment_uniform` (`FreeMomentBound.lean`):
  `∃K₀,∀N, ∫(ωf)^{2n}·V^{2k} dμ_GFF ≤ K₀` (k≥1). Field side uses
  `torus_normConst_field_moment_uniform`.

## After L3 — the realistic remainder
- **L5(ii)** — the flagged **slog**: `u₄''(t) ≤ K` uniform. Expand `u₄''(t)` (quotient rule twice on
  `M₄/Z − 3(M₂/Z)²`, using D2 `moment_hasDerivAt2`) into a polynomial of interacting moments
  `⟨φⁿVᵏ⟩_t` (n≤4,k≤2); bound each via L4∘L3. Largest assembly in the project; needs `u₄ ∈ C²`.
- **L6F** — feed `s` (`leadingTerm_const_eq`) + `K` (L5ii) into
  `exists_uniform_neg_of_uniform_affine_bound'` (h0/hcont/hderiv leaves done) + torus framing
  (`torusConnectedFourPoint` pullback + mass↔g, `FieldRedefinition`) ⟹
  `torus_weakCoupling_lattice_connectedFourPoint_strictNeg` ⟹ `torus_pphi2_isInteracting_weakCoupling`.

HONEST SCOPE: L1 + L2-for-V + **L3** (all axiom-clean) are DONE. The remaining wall is **L5(ii)** —
the genuine multi-session slog: `u₄'' ∈ C²` + the quotient-rule expansion of `u₄''(t)` into the
interacting moments `⟨(ωf)^a V^b⟩_t` (a≤4, b≤2), each bounded by L4∘L3. Then **L6F** (short): feed
`s` (`leadingTerm_const_eq`) + `K` (L5ii) into `exists_uniform_neg_of_uniform_affine_bound'` + torus
framing ⟹ discharge `torus_weakCoupling_lattice_connectedFourPoint_strictNeg`.
