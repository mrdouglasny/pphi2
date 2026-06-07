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
- [ ] L1. uniform `⟨V²⟩₀ ≤ C(m,L)`. status: SCOPED, not blocked — THE remaining analytic core. deps: []
      ROUTING DECISION (2026-06-06): TWO routes.
      • Direct (gffPositionCovariance): ⟨V²⟩₀=∑_m c_m²m!·a^{2d}∑_{z,w}C(z,w)^m via
        gff_wickPower_two_smeared_inner, then full-cov row-sum→double via a^d·card=L^d. BLOCKED by a
        MISSING eigenbasis bridge: `gffPositionCovariance = canonicalSmooth+canonicalRough` does NOT
        exist (gffPositionCovariance uses massEigenvectorBasis; canonical uses latticeFourierProductBasisFun
        — two different eigenrepresentations; covariance_split (CovarianceSplit:52) is only eigenvalue-level
        λ⁻¹=smoothEig+roughEig). Building that bridge is itself deep.
      • Canonical-joint (INTENDED): use bridge `integral_interaction_sq_eq_canonicalJoint` (done) →
        ∫V_full²dμ_joint, V_full=V_s+V_r (φ_S⊥φ_R indep) → ∫V_s²+2∫V_sV_r+∫V_r². Cross term via
        smooth⊥rough chaos orthogonality (integral_sum_mul_sum_eq_zero_of_orth, RoughErrorBound:2093);
        ∫V_r² via canonicalRoughError_l2_sq_eq_lead_plus_perCoef_sq (:2540) + rough row-sums; ∫V_s² via
        abs_canonicalSmoothCovariance_le_smoothWickConstant (FieldDecomposition:3812) +
        smoothWickConstant_le_log_uniform_in_aN (CovarianceBoundsGJ:1536) pointwise→row-sum.
      VERDICT: buildable, all analytic inputs proved; remaining = intricate assembly in the Nelson
      canonical-joint machinery (RoughErrorBound/FieldDecomposition). A focused dedicated job; the
      deepest-unfamiliar-machinery piece of the K leaf. Good Codex/fresh-context candidate.
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
- [~] D2. second-derivative infra: `moment_mul_interaction_hasDerivAt` (d/dt ∫(ωf)ⁿVe^{−tV} =
      −∫(ωf)ⁿV²e^{−tV}, t>0). status: DERIVATIVE PROOF DRAFTED (Codex, mirrors moment_hasDerivAt
      template MomentDerivative.lean:126-213 — set μ/V, B from interactionFunctional_bounded_below,
      F/F', hasDerivAt_integral_of_dominated_loc_of_deriv_le). BLOCKED on one sub-lemma:
      `integrable_powMul_interaction_sq` : Integrable ((ωf)ⁿ·V²). deps: [D2int]
- [~] D2int. `Integrable ((ω f)ⁿ · V²)`. status: KERNEL DONE (branch uniform-discharge-D2), tail left.
      DONE + axiom-clean (MomentIntegrability.lean): integrable_powMul_wickMonomial_mul (same-site
      :x^{k₁}::x^{k₂}: by induction on k₂), _mulWickPoly (sum over wickPoly), _mul_self (wickPoly·wickPoly
      same site), _sq ((ωf)ⁿ·wickPoly². TAIL (mechanical): (C) different-site
      `(ωf)ⁿ·wickPoly(δ_z)·wickPoly(δ_w)` via AM-GM Integrable.mono' dominating by
      ½(|ωf|ⁿwpz²+|ωf|ⁿwpw²) [use _sq + .abs; measurability via wickPolynomial_continuous₂
      (WickPolynomial.lean:428) + configuration_eval_measurable; AM-GM two_mul_le_add_sq]; then (D)
      `integrable_powMul_interaction_sq` = (ωf)ⁿV² via V²=a^{2d}∑_{z,w}wpz wpw (Finset.sum_mul_sum) +
      integrable_finset_sum of C.
      OLD note (routes) — superseded; the induction-kernel route above worked. V²=
      a^{2d}∑_{z,w}wickPoly(δ_z)wickPoly(δ_w) ⟹ need `(ωf)ⁿ·wickMon_{k₁}(δ_z)·wickMon_{k₂}(δ_w)`
      integrable = a 3-SITE pairing product (existing integrable_powMul_wickMonomial does only 2 sites
      f,z). Routes (all need a new sub-lemma): (a) double strong-induction on (k₁,k₂) mirroring
      integrable_powMul_wickMonomial; (b) AM-GM wickMon(δ_z)wickMon(δ_w) ≤ ½(wickMon(δ_z)²+wickMon(δ_w)²)
      → still need (ωf)ⁿwickMon_k(δ_z)² (single-site wickMon square); (c) MemLp route: MemLp(wickPoly) 3
      ×3 → Hölder → L¹ (needs MemLp(wickMon) p, absent); (d) polynomial bound |wickMon_k(x)|≤C(1+|x|^k)
      → integrable_pow_pairing(_mul) (needs the bound lemma). EASY foundation available:
      integrable_pow_pairing_mul3 (3-pairing AM-GM, trivial mirror of integrable_pow_pairing_mul:61).
      Recommend: focused Codex --resume or dedicated session on this one lemma.
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
