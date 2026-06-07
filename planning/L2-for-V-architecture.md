# L2-for-V — uniform `Lᵖ` / moment bound on the Wick polynomial `V` (architecture)

Branch: `k-leaf-l2-for-v` (off `main` @ 51a294b, L1 merged).
Target (what L3 consumes): `∃ C_m, ∀ N, ∫ V^{2m} dμ_GFF ≤ C_m` uniform, for `m ≤ 4`
(L3 needs `⟨φ⁸V⁴⟩₀` ⟹ `∫V⁸`). Equivalently `∫|V|^p ≤ K` for `p ∈ {2,…,8}`.
`V = interactionFunctional 2 N P a mass` = Wick-ordered degree-≤`P.n`(=4) poly in the GFF.

## The tool EXISTS: Bonami–Nelson chaos hypercontractivity
`bonami_nelson_chaosLE (n d) (F : Lp 2 (stdGaussianFin n)) (hF : F ∈ wienerChaosLE n d) (p) (hp:2≤p) :`
`eLpNorm F p ≤ ((d+1)(p-1)^{d/2}) · eLpNorm F 2`
(gaussian-hilbert/GaussianHilbert/PolynomialChaosConcentration.lean:234). eLpNorm-form only.
Also `bonami_nelson_chaos` (single chaos, :120). Depends on markov-semigroups OU axioms (transitive).

## Route (canonical-joint, reusing rough-error machinery)
`∫V^{2m}dμ_GFF = ∫V_full^{2m}dμ_joint` (general bridge `integral_comp_canonicalSumConfig`, F=(·)^{2m}).
`V_full = V_smooth + V_rough`; `∫V_full^{2m} ≤ 2^{2m-1}(∫V_s^{2m} + ∫V_r^{2m})` (convexity/power-mean).
Handle each via Bonami on its std representative (on `stdGaussianFin (card CanonicalJointSumIndex)`):
1. **rough**: `canonicalRoughErrorStd ∈ wienerChaosLE` ✅ DONE (`canonicalRoughErrorStd_mem_wienerChaosLE`,
   RoughErrorBound:1883). ⟹ Bonami ⟹ `∫|V_r|^p dμ_joint ≤ ((P.n+1)(p-1)²)^p (∫V_r²)^{p/2}`.
   `∫V_r²` uniform from `rough_error_variance`.
2. **smooth**: need `canonicalSmoothInteractionStd ∈ wienerChaosLE` (MISSING). The smooth interaction is
   the `j=k` part of `canonicalSiteCrossStd`; reuse `finite_indexed_wick_sum_mem_wienerChaosLE`
   (RoughErrorBound:916, PUBLIC) OR `canonicalSiteCrossStd_mem_wienerChaosLE` (PRIVATE → must build
   inside RoughErrorBound.lean). `∫V_s²` uniform from M2 (`canonicalSmoothInteraction_variance_le`).

## Reusable glue (build these)
- **G1 (bonami→moment)**: from `F ∈ wienerChaosLE n d` + `f =ᵐ F` (so `f` is the std rep): derive
  `∫|f|^p dμ_std ≤ ((d+1)(p-1)^{d/2})^p · (∫|f|²)^{p/2}`. Pure eLpNorm↔integral conversion
  (`eLpNorm_eq …`, `(eLpNorm f p).toReal^p = ∫|f|^p` for `f∈Lᵖ`; chaos ⟹ `f∈Lᵖ ∀p`). SELF-CONTAINED.
- **G2 (std→joint transfer)**: `∫|V_·|^p dμ_joint = ∫|V_·Std|^p dμ_std` via
  `canonicalJointMeasure_map_stdGaussian` + `integrable_map_equiv` + the `…Std_eq` rewrite
  (mirror `canonicalRoughError_sq_integrable`, RoughErrorBound:3920).
- **G3 (bridge)**: `∫V^{2m}dμ_GFF = ∫V_full^{2m}dμ_joint` from `integral_comp_canonicalSumConfig`
  + `canonicalFullInteractionJoint_eq_interactionFunctional`.

## G1 DONE + the precise smooth-chaos-membership recipe (2026-06-07)
- **G1 ✅** `chaosLE_moment_le` (Pphi2/NelsonEstimate/ChaosMoment.lean) — Bonami→moment-integral,
  axiom-clean. `bonami_nelson_chaosLE` is itself axiom-clean (OU/markov-semigroups fully proven).
- **Smooth chaos membership** (the next brick, MUST be inside RoughErrorBound.lean — private apparatus):
  `canonicalCrossTermStd_mem_wienerChaosLE (k j)(hjk : j ≤ k) : crossTermStd(k,j) ∈ wienerChaosLE … k`
  (RoughErrorBound:1647) WORKS for `j=k` (the diagonal). Recipe — mirror
  `canonicalRoughErrorStd_mem_wienerChaosLE` (1883-2010) but with single diagonal terms:
  1. `canonicalSmoothInteractionStd (T P ξ) := (1/P.n)•crossTermStd(P.n,P.n)ξ + ∑_m coeff_m•crossTermStd(m,m)ξ`.
  2. `canonicalSmoothInteractionStd_eq`: `…(equiv η) = canonicalSmoothInteraction η` — via
     `canonicalCrossTermStd_eq` (1639) [crossTermStd(k,j)(equiv η)=crossTerm(k,j)η] + re-derive M2a's
     diagonal decomposition INLINE (M2a lives downstream in InteractionVariance, unavailable here):
     `canonicalSmoothInteraction = a^d∑_x wickPoly`, `crossTerm(k,k)=a^d∑_x :φ_S^k:` (wickMonomial_zero),
     `wickPolynomial=(1/P.n)wickMon_{P.n}+∑coeff wickMon_m` ⟹ equal.
  3. `canonicalSmoothInteractionStd_mem_wienerChaosLE`: ∈ wienerChaosLE P.n. lead =
     `(1/P.n)•crossTermStd(P.n,P.n)` ∈ chaos via `canonicalCrossTermStd_mem_wienerChaosLE P.n P.n le_rfl`
     (degree P.n) + `Submodule.smul_mem`; per = `∑_m coeff_m•crossTermStd(m,m)` each ∈ wienerChaosLE m
     ⊆ wienerChaosLE P.n via `wienerChaosLE_mono (m≤P.n)` (1623) + `Submodule.sum_mem`/`smul_mem`. The
     toLp-of-sum bookkeeping: copy the `MemLp.coeFn_toLp`/`Lp.coeFn_finset_sum`/`Lp.coeFn_smul` pattern
     from the rough proof (1944-2010).
- **Then** (in ChaosMoment or a new file): `canonicalSmoothInteraction_Lp_le` and
  `canonicalRoughError_Lp_le` via G1 (`chaosLE_moment_le`) on the std reps + G2 std→joint transfer
  (mirror `canonicalRoughError_sq_integrable`, 3920, but `(·)^p` and the integral equality) +
  G3 bridge (`integral_comp_canonicalSumConfig`) + `(a+b)^{2m}≤2^{2m-1}(a^{2m}+b^{2m})` combine ⟹
  `∫V^{2m}dμ_GFF ≤ C_m` (the L2-for-V deliverable), using L1/M2/rough_error_variance for the L² bases.

## Status / next
- All deep ANALYTIC inputs done (L1 = `∫V²≤C`, M2 = smooth variance, rough_error_variance).
- OPEN crux: smooth chaos membership (step 2) + the Bonami applications + G1/G2/G3 assembly.
- This is the biggest remaining brick (ENNReal/chaos-heavy, partly inside private RoughErrorBound).
  Likely multi-session.

## Open question
Is there a "ordinary polynomial of degree ≤d ∈ wienerChaosLE d" lemma in gaussian-hilbert that would
let V skip the Wick-expansion apparatus? (Wick monomials ARE the chaos; an ordinary degree-≤d poly is a
finite combination of Hermite ≤d, hence in wienerChaosLE d.) If so, chaos membership is much cheaper.
Check `WienerChaos.lean` for monomial/polynomial-degree membership before building the canonical route.
