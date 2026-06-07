# K leaf — status machine (`u₄'(t) ≤ −s + K·t` uniform; the `K` half)

Branch: `uniform-discharge-K` (off `main` @ 38b5a94, post-PR#40 / `s` leaf done).
Goal: feed a uniform `K` (with the proved `s = leadingTerm_const_eq`) into
`exists_uniform_neg_of_uniform_affine_bound'` ⟹ discharge
`torus_weakCoupling_lattice_connectedFourPoint_strictNeg`.

The affine bound `u₄'(t) ≤ −s + K·t` on `[0,g₀]` ⟺ `u₄'(0) ≤ −s` (✅ s leaf) + `u₄''(t) ≤ K`
uniform. There is **no second-derivative infra yet** — that (L5) is the slog.

## Items

- [x] L4. `interacting_moment_le_L2_of_expBound` — pull-back: given `∫e^{−2V} ≤ K` (K≥1) and `t∈[0,1]`,
      `X∈L²`, then `⟨|X|⟩_t = ∫|X|e^{−tV}/Z_t ≤ ‖X‖_{L²}·√K`.
      status: DONE (UniformBounds.lean, axiom-clean). General in d,N,a,mass,P.
- [x] L4t. `expMoment_two_le_uniform` (TorusInteractingLimit.lean): `∃ K≥1, ∀N, ∫e^{−(2V)} ≤ K`
      on the torus, axiom-clean. Repackages `nelson_exponential_estimate`. Feeds directly into L4.
      status: DONE  deps: [L4]

## ★ KEY FINDING (2026-06-06): Nelson is ALREADY PROVED, axiom-clean
`nelson_exponential_estimate` (TorusInteractingLimit.lean:111) is sorry-free and depends only on the 3
standard axioms — NOT the custom-axiom bridge. It routes nelson_exponential_estimate_lattice →
nelson_exponential_estimate_master → polynomial_chaos_exp_moment_bridge (smooth lower-bound +
rough cutoff-tail layer-cake), the LEGITIMATE Nelson argument (NOT the false `V ≥ −L²A` pointwise
bound — that was a stale comment, now fixed). This DE-RISKS the K leaf: the deepest analytic input
(∫e^{−2V}≤K uniform) is done. (Note: a SEPARATE `axiom nelson_exponential_estimate_master_bounded`
for the `a≤1` interface in Hypercontractivity.lean is still axiomatic, but the fixed-volume torus
route we use does NOT touch it.)
⟹ REASSESS: much of L1/L2 covariance-summability infra likely already exists inside NelsonEstimate/
(CovarianceBoundsGJ, CovarianceSplit) + ContinuumLimit/Hypercontractivity.lean. Survey before rebuilding.
- [ ] L1. uniform `⟨V²⟩₀ ≤ C(m,L)`. status: PARTIAL — THE remaining analytic piece. Bridge
      `integral_interaction_sq_eq_canonicalJoint` (InteractionL2:36) reduces to the canonical joint;
      rough row-sums `canonicalRoughCovariance_pow_{one,two}_sum_le_uniform_in_aN` (CovarianceBoundsGJ:
      709,851) + smooth `smoothVariance_le_log` (CovarianceSplit:140) + rough-error L²-sq decomp
      `canonicalRoughError_l2_sq_eq_lead_plus_perCoef_sq` (RoughErrorBound:2540) all EXIST. Missing =
      the unified assembly tying them into a single N-uniform `⟨V²⟩₀ ≤ C`. deps: []
- [~] L2. hypercontractivity / uniform Lᵖ. status: MOSTLY FOUND. `interacting_moment_bound`
      (Hypercontractivity.lean:1218) `∫|ωf|^{pn}dμ_a ≤ C(2p−1)^{pn/2}(∫|ωf|^{2n}dμ_GFF)^{p/2}`;
      `gaussian_hypercontractivity_continuum` (:112); `pairing_memLp_lattice` (MomentIntegrability:30)
      `(ωf)∈Lᵖ ∀p`. CAVEAT: Hypercontractivity.lean route uses `exponential_moment_bound` (:923)
      which depends on the `a≤1` AXIOM nelson_exponential_estimate_master_bounded — for axiom-clean
      K leaf prefer the fixed-volume `expMoment_two_le_uniform` (L4t). Need: uniform Lᵖ of `V` itself.
- [~] L3. moment-product integrability. status: FOUND (integrability). `integrable_powMul_interaction`
      (MomentIntegrability:141) `(ωf)ⁿ·V` integrable; `integrable_powMul_wickPolynomial` (:117);
      `wickMonomial_latticeGaussian` (Hypercontractivity:864) ⟨:wickₙ:⟩₀=0. Remaining: the uniform
      BOUND `⟨φ(f)^{2n}V^{2k}⟩₀ ≤ K₀` (Cauchy–Schwarz on top of L1 + L2), not just integrability.
- [ ] D2. second-derivative infra: `moment_hasDerivAt2` / closed form `d²/dt²∫(ωf)ⁿe^{−tV} =
      ∫(ωf)ⁿV²e^{−tV}`; partitionFn 2nd deriv; quotient-rule C² for the normalized moments and u₄.
      status: todo  deps: []  note: NEW, no infra. Mirror moment_hasDerivAt (dominated, deriv under ∫).
      Candidate for Codex (self-contained, like moment_hasDerivAt was).
- [ ] L5. `u₄''(t) ≤ K` uniform: expand u₄''(t) as a moment polynomial in ⟨φ(f)ⁿV^k⟩_t, bound termwise
      via L4∘L3. status: todo  deps: [L3, D2, L4t]  note: the slog; hardest sub-lemma.
- [ ] L6F. feed s (leadingTerm_const_eq) + K (L5) into exists_uniform_neg_of_uniform_affine_bound';
      framing torusConnectedFourPoint pullback + mass↔g. status: todo  deps: [L5]

## Key infra (from Explore sweep 2026-06-06)
- ⟨V²⟩₀ identity: `gff_wickPower_two_smeared_inner` (GaussianField WickMultivariate.lean:1202),
  `gffSmearedCovariance_eq_sum_position` (:1120), `gffPositionCovariance_eq_covarianceGJ` (:722).
  `interactionFunctional_eq_single` (MomentDerivative.lean:33).
- cov row-sums (ROUGH, d=2, m≥1): `canonicalRoughCovariance_pow_sum_le_uniform_in_aN`
  (CovarianceBoundsGJ.lean:1582), forms `a^d∑_y|C_rough|^m ≤ C_m·T`, hyp `(N:ℝ)*a=L`.
- L4 pieces: `partitionFn_ge_one` (UniformBounds.lean:75), `expMoment_le_rpow` (:111),
  `boltzmann_cauchySchwarz` (:153), `interactionFunctional_integral_nonpos` (:50).
- nelson: `nelson_exponential_estimate` (TorusContinuumLimit/TorusInteractingLimit.lean:111),
  `nelson_exponential_estimate_lattice` (NelsonEstimate/NelsonEstimate.lean:81) — ∫e^{−2V}≤K, circleSpacing.
- 1st derivs: `moment_hasDerivAt` (MomentDerivative.lean:126) deriv `−∫(ωf)ⁿVe^{−tV}`;
  `partitionFn_hasDerivAt` (U4DerivativeInterior.lean:29); `u4_differentiableAt` (:46).
- integrability: `integrable_pow_pairing` (MomentIntegrability.lean:38), `integrable_powMul_interaction` (:141).
- P: `InteractionPolynomial` (Polynomial.lean:26), eval `(1/n)τⁿ+∑a_mτᵐ`, P.n=4 ⟹ (1/4)φ⁴+a₂φ²+a₀.
