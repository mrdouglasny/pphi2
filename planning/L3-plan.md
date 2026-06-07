# L3 — free L² moment bound `⟨φ(f)^{2n}V^{2k}⟩₀ ≤ K₀` (and the K-leaf remainder)

Branch: `k-leaf-l3` (off `main` post-#45). L2-for-V is merged (`interaction_moment_le`:
`∃K,∀N, ∫V^{2m}dμ_GFF ≤ K`, axiom-clean).

## L3 target
`⟨φ(f)^{2n}V^{2k}⟩₀ = ∫(ωf)^{2n}·V^{2k} dμ_GFF ≤ K₀` uniform (n≤4, k≤2, so up to φ⁸V⁴), for the
discharge's test function `f`. Feeds L4 (`interacting_moment_le_L2_of_expBound`): `⟨|φⁿVᵏ|⟩_t ≤
‖φⁿVᵏ‖_{L²}·√K`, with `‖φⁿVᵏ‖_{L²}² = ⟨φ^{2n}V^{2k}⟩₀`.

## Route (Cauchy–Schwarz) + the bricks
`∫(ωf)^{2n}V^{2k} ≤ (∫(ωf)^{4n})^{1/2}·(∫V^{4k})^{1/2}` (`integral_mul_le_Lp_mul_Lq_of_nonneg`,
Hölder 2,2). Then:
- **∫V^{4k} ≤ K**: ✅ `interaction_moment_le` (m=2k), DONE.
- **L3a — `interaction_memLp`** (the foundation, NEXT): `MemLp V p (μ_GFF)` for `p≥2`, so `V^{2k}∈L²`
  (`memLp_two_iff_integrable_sq`). Route: `canonicalFullInteractionJointStd ∈ wienerChaosLE` (done,
  RoughErrorBound) → bonami ⟹ eLpNorm finite ⟹ `MemLp …Std p (stdGaussianFin)` → transfer to
  `MemLp V_full p (joint)` (`canonicalFullInteractionJointStd_eq` + MeasurePreserving equiv) →
  transfer to `MemLp V p (μ_GFF)` (`canonicalJointMeasure_map_canonicalSumConfig` +
  `memLp_map_measure_iff`/`MemLp.comp_measurePreserving`; `canonicalFullInteractionJoint_eq_interactionFunctional`).
  Note: most of these `…Std` lemmas are PRIVATE in RoughErrorBound, so `interaction_memLp` (or
  `MemLp V_full p joint`) should be EXPOSED there. ENNReal/transfer-fiddly, ~40-50 lines.
- **L3b — uniform field moment** `∫(ωf)^{4n} ≤ K_f`: Gaussian even moment of the pairing,
  `= (4n-1)!!·(∫(ωf)²)^{2n}`; `∫(ωf)²` = GFF variance of `ω(f)`, uniform for the discharge's `f`
  (the normalised constant from the `s`-leaf: row-sum covariance `= 1/(a^d m²)`, uniform). Reuse
  `gffSmearedCovariance`/`leadingTerm` machinery.
- **L3c — assemble**: Cauchy–Schwarz + L3a (MemLp for the two factors) + ∫V^{4k}≤K + L3b ⟹ `⟨φ^{2n}V^{2k}⟩₀ ≤ K₀`.

## After L3 — the realistic remainder
- **L5(ii)** — the flagged **slog**: `u₄''(t) ≤ K` uniform. Expand `u₄''(t)` (quotient rule twice on
  `M₄/Z − 3(M₂/Z)²`, using D2 `moment_hasDerivAt2`) into a polynomial of interacting moments
  `⟨φⁿVᵏ⟩_t` (n≤4,k≤2); bound each via L4∘L3. Largest assembly in the project; needs `u₄ ∈ C²`.
- **L6F** — feed `s` (`leadingTerm_const_eq`) + `K` (L5ii) into
  `exists_uniform_neg_of_uniform_affine_bound'` (h0/hcont/hderiv leaves done) + torus framing
  (`torusConnectedFourPoint` pullback + mass↔g, `FieldRedefinition`) ⟹
  `torus_weakCoupling_lattice_connectedFourPoint_strictNeg` ⟹ `torus_pphi2_isInteracting_weakCoupling`.

HONEST SCOPE: L1 + L2-for-V (the two deepest analytic bricks) are DONE + axiom-clean. L3 is a bounded
chain (Cauchy–Schwarz + the MemLp/field-moment foundations). L5(ii) is a genuine multi-session slog
(the u₄'' C² assembly). Full discharge is still several focused sessions.
