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
- [ ] L1. uniform `⟨V²⟩₀ ≤ C(m,L)`. ⟨V²⟩₀ = a^{2d}∑_{z,w}∑_m c_m² m! C(z,w)^m (gff_wickPower_two_smeared_inner,
      C = gffPositionCovariance FULL). Need full-cov double-sum `a^{2d}∑_{z,w}|C|^m ≤ uniform`.
      status: todo  deps: []  note: GAP — existing pow-sum bounds are ROW sums of canonicalRough
      (CovarianceBoundsGJ). Two sub-steps: (1a) row→double via a^d·#sites=L^d (torus_volume_eq);
      (1b) full=smooth+rough binomial OR a full-C row-sum. The deep analytic part.
- [ ] L2. hypercontractivity lift for V (degree-4 Wick): ‖V‖_{L⁴},‖φ(f)‖_{L⁸} uniform.
      status: todo  deps: [L1]  note: gaussian_hypercontractivity_continuum exists for |ωf|; apply to V.
- [ ] L3. free L² moment bound `⟨φ(f)^{2n}V^{2k}⟩₀ ≤ K₀` (n≤4,k≤2) via Cauchy–Schwarz + L2.
      status: todo  deps: [L1, L2]
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
