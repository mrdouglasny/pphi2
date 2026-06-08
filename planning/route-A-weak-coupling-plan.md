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
- [ ] **A3. `g`-family supporting-lemma chain (the real cost of A4/A5).**   status: todo   deps: []   diff: ★★
  The g=1 second-moment/convergence proofs call a CHAIN of `g=1`-specific lemmas; each needs a
  coupling-`g` analog (the genuinely-new work, all enabled by the Jensen bound `∫(e^{−sV})^? ` already
  in `expMoment_le_rpow`/`partitionFn_ge_one`):
  - `partitionFunction_ge_one` (g=1) → use `partitionFn_ge_one` (already general `t ≥ 0`) ✅ exists.
  - `nelson_exponential_estimate` (g=1, `TorusInteractingLimit.lean:111`) → `…_coupling` (g ∈ (0,1]).
    Bridge via `expMoment_le_rpow` (`∫e^{−sV} ≤ (∫e^{−2V})^{s/2} ≤ K`, already proved, N-uniform).
  - `density_transfer_bound` (g=1) → `…_coupling`: `∫ X dμ_g ≤ (∫X² dμ_GFF)^{1/2}·√(∫e^{−2gV})/Z(g)`,
    Cauchy–Schwarz with the `e^{−gV}` density; the `Z(g)≥1` + g-Nelson keep it N-uniform.
  - higher-moment uniform inputs used by step-IV convergence (uniform integrability of `(ωf)⁴`).
- [ ] **A4. `g`-family uniform 2nd moment + tightness + existence.**   status: todo   deps: [A1, A3]   diff: ★★
  Mirror `torus_interacting_second_moment_uniform` (~70 lines) + `torus_interacting_tightness` for the
  torus pushforward of `interactingLatticeMeasureCoupling … g`, swapping in A3's `…_coupling` lemmas.
  Then `torusInteractingLimitCoupling_exists` from the generic `prokhorov_configuration` (mechanical
  mirror of `torusInteractingLimit_exists`). NB also needs a torus-level `μ_g` =
  `map torusEmbedLift (interactingLatticeMeasureCoupling)` def + `integral_pow` pushthrough
  (mirror `torusConnectedFourPoint_eq_lattice`).
- [ ] **A5. `g`-family 4-point convergence.**   status: todo   deps: [A3, A4]   diff: ★★★
  Mirror `torus_connectedFourPoint_tendsto` (the step-IV proof) for `μ_g`: `u₄(μ_{g,N}) → u₄(μ_{g,∞})`,
  threading `g` and using A3's uniform-integrability inputs. The largest brick (multi-day).
- [ ] **A6. Restate the discharge as a THEOREM.**   status: todo   deps: [A2, A5]   diff: ★
  `torus_weakCoupling_connectedFourPoint_strictNeg` (THEOREM, was axiom): from `lattice_u4_neg_uniform`
  + A2, `∃ g₀ c > 0, ∀ N, torusConnectedFourPoint(μ_{g₀,N}) f₀ ≤ −c`.
- [ ] **A7. New headline.**   status: todo   deps: [A5, A6]   diff: ★
  `torus_pphi2_isInteracting_weakCoupling'` : `∃ g₀ > 0, ∃ μ (continuum limit of μ_{g₀}),
  IsTorusPphi2Limit … ∧ TorusIsInteracting`. Assemble from A6 + A5 (`u₄(μ) = lim u₄(μ_{g₀,N}) ≤ −c`).
  Retire the old axiom + the `mass`-parametrized headline (or keep the old as a corollary, NOT proved,
  marked Route B / open).

## Net
A1/A2/A6/A7 are ★ (definitions + assembly). A3 is the one genuinely-new analytic lemma (Jensen
transfer) and is short. A4/A5 are ★★/★★★ mechanical mirrors of existing g=1 proofs with `g` carried
through. No dilation, no Wick-covariance, no `K=O(m⁻⁶)` clustering. Estimated: a few focused days.

## Statement change (owner-approved)
The headline moves from `∀ mass > m₀` (large mass) to `∃ g₀ > 0` (weak coupling), at a fixed mass.
This is the honest, standard non-triviality statement (deep-think 2026-06-07). The old
large-mass/`λ=1` axiom is NOT discharged by Route A — it needs Route B (continuum dilation) and is
left open / marked as such.
