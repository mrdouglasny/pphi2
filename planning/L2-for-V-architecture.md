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
