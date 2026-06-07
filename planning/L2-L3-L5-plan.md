# K leaf — post-L1 roadmap (L2-for-V → L3 → L5(ii) → L6F)

**Status after 2026-06-07**: all analytic foundations done — `s` leaf (`leadingTerm_const_eq`),
L4/L4t (`interacting_moment_le_L2_of_expBound`, `expMoment_two_le_uniform`), Nelson
(`nelson_exponential_estimate`, pre-existing), D2 (`moment_mul_interaction_hasDerivAt`,
`moment_hasDerivAt2`), **L1 (`interaction_variance_le`, `∫V²dμ_GFF ≤ C` uniform)**.

Remaining chain to discharge `torus_weakCoupling_lattice_connectedFourPoint_strictNeg`:

## L2-for-V (NEXT — the deep one): uniform `Lᵖ` of the Wick polynomial `V`
Target: `∫ V^{2m} dμ_GFF ≤ C_m · (∫ V² dμ_GFF)^m` uniform in N (so via L1, `∫V^{2m} ≤ C_m·C^m`),
for m ≤ 4 (need `V⁸` for L3's `⟨φ⁸V⁴⟩₀` Cauchy–Schwarz). Equivalently `‖V‖_{Lᵖ} ≤ (p−1)²‖V‖_{L²}`
(Nelson, `V` ∈ 4th Wiener chaos since P.n=4).
- WHAT EXISTS: `gaussian_hypercontractivity_continuum` (Hypercontractivity.lean:112) — FIELD ONLY
  (`|ω f|^{pn}`), NOT for V. gaussian-field: `gross_log_sobolev` (Hypercontractive.lean:385),
  `gaussian_hypercontractive` (:299) — abstract Gross/OU; `hypercontractive_gaussianReal` (HypercontractiveNat:225).
- WHAT'S MISSING: chaos hypercontractivity for V. ROUTE: V is in `wienerChaosLE … P.n` (cf
  `canonicalRoughErrorStd_mem_wienerChaosLE`, the std representative); the OU semigroup acts on the
  k-th chaos as `e^{-kt}`, so Gross ⟹ `‖V‖_q ≤ (q−1)^{P.n/2}‖V‖_2`. Need to (a) get V's std representative
  in chaos (mirror the rough-error machinery), (b) apply the abstract hypercontractive bound. SUBSTANTIAL
  — the genuine remaining theoretical brick. (Alt: brute-force `∫V^{2m} = a^{2md}∑_{2m sites}` Wick +
  covariance pow-sums — far messier than L1's V² case.)

## L3 (after L2): free moment bound `⟨φ(f)^{2n}V^{2k}⟩₀ ≤ K₀` (n≤4, k≤2)
Cauchy–Schwarz `⟨φ^{2n}V^{2k}⟩₀ ≤ √(⟨φ^{4n}⟩₀)·√(⟨V^{4k}⟩₀)`. `⟨φ^{4n}⟩₀` = free Gaussian pairing
moment (uniform; `pairing_memLp_lattice` + explicit even-moment, or `gaussian_even_moment_eq_doubleFactorial`).
`⟨V^{4k}⟩₀` from L2-for-V + L1. Integrability of `φ^n V^k` products: `integrable_powMul_interaction` (done).

## L5(ii) (the "slog"): uniform `u₄''(t) ≤ K` on [0,g₀]
`u₄(g) = M₄(g)/Z(g) − 3(M₂(g)/Z(g))²`. Expand `u₄''(t)` (quotient rule twice; use `moment_hasDerivAt2`
= Mₙ''(t)=∫φⁿV²e^{−tV}, `partitionFn` 2nd deriv = n=0 case, Z≠0 from `partitionFn_ge_one`) as a
polynomial in interacting moments `⟨φⁿVᵏ⟩_t` (n≤4,k≤2). Bound each via L4
(`interacting_moment_le_L2_of_expBound`, `expMoment_two_le_uniform`) ∘ L3. Largest assembly.

## L6F: discharge
Feed `s` (`leadingTerm_const_eq`) + `K` (L5ii) into `exists_uniform_neg_of_uniform_affine_bound'`
(UniformBounds) with leaves h0 (`u4_at_zero`), hcont, hderiv (`u4_differentiableAt`). Then framing:
`torusConnectedFourPoint (map ι μ) f = connectedFourPoint μ (ι*f)` + mass↔g (`FieldRedefinition`) ⟹
`torus_weakCoupling_lattice_connectedFourPoint_strictNeg` ⟹ `torus_pphi2_isInteracting_weakCoupling`.
