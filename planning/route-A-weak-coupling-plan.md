# Route A — discharge u₄ non-Gaussianity at weak coupling (status machine)

**Decision 2026-06-07 (owner):** discharge "φ⁴₂ is non-Gaussian" via the **weak-coupling family**
`μ_g ∝ e^{−gV} μ_GFF` (small `g`, fixed mass/box), reusing the PROVEN `lattice_u4_neg_uniform`.
No dilation / no continuum rescaling (that was Route B; see `continuum-rescaling-plan.md` "REFINED
ANALYSIS"). This **re-states** the headline from "large mass" to "weak coupling at fixed mass",
which Gemini deep-think confirmed is the standard, complete non-triviality statement.

Branch: `route-a-weak-coupling` (off `l5-affine-bound`, which carries the u₄ engine; main's docs
merged in). Re-read this file each cycle; pick the next `todo` whose `deps` are `done`.

## What we already have (the engine — PROVEN, axiom-clean, on this branch)
- `lattice_u4_neg_uniform` (`U4AffineBound.lean`): `∃ g c > 0, ∀ N, u4(…,P,f₀,g) ≤ −c`. The `g` is
  small (existential), `f₀` the normalized constant test function, `mass` a free input. THIS is the
  weak-coupling negativity Route A consumes.
- `u4(…,P,f,g)` (`U4DerivativeClosedForm.lean`): `= m₄(g) − 3 m₂(g)²`, defined by integrals against
  `latticeGaussianMeasure` with weight `e^{−g·interactionFunctional}` — i.e. the connected 4-point of
  the coupling-`g` lattice Gibbs measure `μ_g`.
- The g=1 pipeline: `torusInteractingMeasure` (= `μ_1` pushed to the torus), `torus_interacting_*`
  (2nd-moment, tightness), `torusInteractingLimit_exists`, `torus_connectedFourPoint_tendsto`,
  `torusConnectedFourPoint_eq_u4_one`, and the headline `torus_pphi2_isInteracting_weakCoupling`
  (currently consuming the AXIOM `torus_weakCoupling_lattice_connectedFourPoint_strictNeg`).

## The load-bearing reuse trick (makes this tractable, not a rebuild)
The only `g`-dependent analytic inputs are the Nelson exp-moment bounds. For `g ≤ 1` they follow
from the proven `g=1` bounds **by Jensen** (concavity of `x ↦ x^g`, `0 < g ≤ 1`):
`∫ (e^{−2V})^g dμ_GFF ≤ (∫ e^{−2V} dμ_GFF)^g ≤ max(1, K)`. So `expMoment_two_le_uniform` and the
higher exp-moments transfer to the `g`-family with the SAME (or `max(1,·)`) constants, uniform in
`N` and in `g ∈ (0,1]`. ⇒ tightness + convergence re-run mechanically.

## Bricks

- [x] **A1. Coupling-`g` LATTICE measure + `isProbability`.**   status: done   deps: []   diff: ★
  `interactingLatticeMeasureCoupling … g := Z(g)⁻¹ • withDensity(e^{−g·V})` (`Z(g) = partitionFn(g)`),
  `CouplingMeasure.lean`. `interactingLatticeMeasureCoupling_isProbability` (g ≥ 0), plus helpers
  `expNegCoupling_integrable`, `partitionFn_pos_of_nonneg`. Axiom-clean. (Torus-level pushforward is
  folded into A4's measure def, not needed standalone.)
- [x] **A2. General-`g` lattice bridge.**   status: done   deps: [A1]   diff: ★
  `connectedFourPoint_interactingLatticeMeasureCoupling_eq_u4` (`= u4(…,g)`, g ≥ 0) +
  `integral_pow_interactingLatticeMeasureCoupling` (`= normalizedMoment(…,n,g)`), `CouplingMeasure.lean`.
  Axiom-clean. Generalizes the `g=1` `connectedFourPoint_interactingLatticeMeasure_eq_u4_one`.
- [x] **A3. `g`-family supporting-lemma chain (the real cost of A4/A5).**   status: done   deps: []   diff: ★★  (`expMoment_two_coupling_le`, `density_transfer_bound_coupling`, `CouplingMeasure.lean`)
  The g=1 second-moment/convergence proofs call a CHAIN of `g=1`-specific lemmas; each needs a
  coupling-`g` analog (the genuinely-new work, all enabled by the Jensen bound `∫(e^{−sV})^? ` already
  in `expMoment_le_rpow`/`partitionFn_ge_one`):
  - `partitionFunction_ge_one` (g=1) → use `partitionFn_ge_one` (already general `t ≥ 0`) ✅ exists.
  - `nelson_exponential_estimate` (g=1, `TorusInteractingLimit.lean:111`) → `…_coupling` (g ∈ (0,1]).
    Bridge via `expMoment_le_rpow` (`∫e^{−sV} ≤ (∫e^{−2V})^{s/2} ≤ K`, already proved, N-uniform).
  - `density_transfer_bound` (g=1) → `…_coupling`: `∫ X dμ_g ≤ (∫X² dμ_GFF)^{1/2}·√(∫e^{−2gV})/Z(g)`,
    Cauchy–Schwarz with the `e^{−gV}` density; the `Z(g)≥1` + g-Nelson keep it N-uniform.
  - higher-moment uniform inputs used by step-IV convergence (uniform integrability of `(ωf)⁴`).
- [x] **A4. `g`-family uniform 2nd moment + tightness + existence.**   status: done   deps: [A1, A3]   diff: ★★  (`TorusCouplingLimit.lean`, axiom-clean)
  `torusInteractingMeasureCoupling` (+`isProbability`), `latticeFourthMoment_sqrt_le` (g-free, factored),
  `nelson_exponential_estimate_coupling`, `torus_interacting_second_moment_uniform_coupling`,
  `torus_interacting_tightness_coupling`, `torusInteractingLimitCoupling_exists`.
- [x] **A5. `g`-family 4-point convergence.**   status: done   deps: [A3, A4]   diff: ★★★
  Mirror `torus_connectedFourPoint_tendsto` for `μ_g`: `u₄(μ_{g,N}) → u₄(μ_{g,∞})`. **Reuse map**
  (`TorusInteractingMoments.lean`): the generic helpers `limit_le_of_uniform_bound`, `sub_min_le_sq_div`
  are measure-agnostic → **reuse as-is**. Need coupling versions of the measure-specific bounds:
  `torus_interacting_fourth_moment_uniform_coupling`, `…_eighth_moment_uniform_coupling`,
  `torus_interacting_abs_pow_integrable_coupling` (each = the exact pushforward+`density_transfer_bound_coupling`
  +hypercontractivity pattern already used in A4; factor a general free-moment sqrt lemma
  `(∫(ωg)^{2m})^{1/2} ≤ (2m-1)^{m/2}Cg^{m/2}` to keep them short). Then thin wrappers
  `torus_interacting_{fourth,second}_moment_tendsto_coupling` + `torus_connectedFourPoint_tendsto_coupling`
  (delegating to the generic UI lemma). ~300 lines, mechanical.
- [x] **A6. Lattice negativity at a FIXED torus test function — DONE (axiom-clean).**   status: done   deps: [A2, A5]   diff: ★★★  (`TorusCouplingResult.lean`)
  Resolved exactly via the 4-homogeneity route below: `u4_smul` (homogeneity), `circleOne`/`torusOne`
  + `latticeTestFn_torusOne` (`= L² • (1/card)`, so `c_N = L²` *exactly*, no `inf` argument needed),
  `torusConnectedFourPoint_coupling_eq_u4` (pull-back), giving
  `torus_weakCoupling_connectedFourPoint_strictNeg`: `∀ N, torusConnectedFourPoint(μ_{g₀,N})(torusOne)
  = L⁸·u4(1/card,g₀) ≤ −L⁸c`, uniform.
  ⚠️ **Discovered 2026-06-07:** `lattice_u4_neg_uniform` is hardwired to the **N-dependent constant**
  lattice test function `1/card` (both the slope `leadingTerm_const_eq` and the `K`
  `u4Deriv2_abs_le_uniform` are stated only for it — chosen because `a^d·card = L²` makes the slope
  `s = 6(L⁶m⁸)⁻¹` exactly N-uniform). That constant is **not** `latticeTestFn L N f` of any fixed
  torus `f`, and A5's convergence needs a **fixed** torus `f`. This is the same fixed-test-function
  gap the original axiom never closed.
  **The tractable route (4-homogeneity).** `connectedFourPoint` (hence `u4`) is degree-4 homogeneous
  in the test function: `u4(c•f, g) = c⁴·u4(f, g)` (because `ω(c•f) = c·(ω f)`). For the **constant
  torus function** `f₀ ≡ c₀`, by symmetry `latticeTestFn L N f₀ = c_N • (fun _ => (card)⁻¹)`, so
  `u4(latticeTestFn L N f₀, g₀) = c_N⁴ · u4((card)⁻¹, g₀) ≤ c_N⁴·(−c)`. Hence the discharge reduces to:
  (i) the homogeneity lemma `u4 (c•f) g = c⁴·u4 f g` (easy: moment homogeneity); (ii)
  `latticeTestFn L N f₀ = c_N • (card)⁻¹` for the constant `f₀` (symmetry of `evalTorusAtSiteGJ` on
  constants); (iii) **`inf_N c_N > 0`** (so `c_N⁴·(−c) ≤ −c' < 0` uniformly) — a Riemann-sum /
  `evalTorusAtSiteGJ`-of-constant lower bound, the one real analytic sub-leaf. Then
  `torusConnectedFourPoint(μ_{g₀,N}) f₀ = u4(latticeTestFn f₀, g₀) ≤ −c'` uniformly (via the coupling
  analog of `torusConnectedFourPoint_eq_lattice`, also needed).
- [x] **A7. New headline — DONE (axiom-free).**   status: done   deps: [A5, A6]   diff: ★  (`TorusCouplingResult.lean`)
  `torus_pphi2_isInteractingStrict_weakCoupling`: `∃ g₀ ∈ (0,1], ∃ μ` (continuum limit of `μ_{g₀}`)
  `∧ TorusIsInteractingStrict μ` (so `TorusIsInteracting μ`). Assembled from A6 + A5 via
  `le_of_tendsto` (`torusConnectedFourPoint μ (torusOne) = lim ≤ −c' < 0`).
  **`#print axioms` ⟹ `[propext, Classical.choice, Quot.sound]` only.**

## STATUS (2026-06-07): ROUTE A COMPLETE — AXIOM-FREE
A1–A7 all done + axiom-clean. **φ⁴₂ on T² is proven non-Gaussian at weak coupling with NO project
axioms** — `torus_pphi2_isInteractingStrict_weakCoupling` (`TorusCouplingResult.lean`) does not use
`torus_weakCoupling_lattice_connectedFourPoint_strictNeg` and does not use the continuum dilation
(Route B). The A6 fixed-test-function gap (the original non-triviality core) was closed cleanly: the
constant `torusOne = 1⊗1` samples to `latticeTestFn = L²•(1/card)` *exactly* (`c_N = L²` constant),
so 4-homogeneity (`u4_smul`) transports the engine's constant-test-function negativity with a fixed
`L⁸` factor — no `inf_N` argument needed. The old `mass`-parametrized axiom/headline remain only as
the Route-B (`λ=1`/large-mass) target, still open.

## Net
A1/A2/A6/A7 are ★ (definitions + assembly). A3 is the one genuinely-new analytic lemma (Jensen
transfer) and is short. A4/A5 are ★★/★★★ mechanical mirrors of existing g=1 proofs with `g` carried
through. No dilation, no Wick-covariance, no `K=O(m⁻⁶)` clustering. Estimated: a few focused days.

## Statement change (owner-approved)
The headline moves from `∀ mass > m₀` (large mass) to `∃ g₀ > 0` (weak coupling), at a fixed mass.
This is the honest, standard non-triviality statement (deep-think 2026-06-07). The old
large-mass/`λ=1` axiom is NOT discharged by Route A — it needs Route B (continuum dilation) and is
left open / marked as such.
