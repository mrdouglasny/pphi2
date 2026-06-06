# Proof plan — `TorusIsInteracting` (the φ⁴₂ theory on T² is interacting)

**Target:** `∃ f, torusConnectedFourPoint L μ f < 0` (`TorusIsInteractingStrict`, which implies
`TorusIsInteracting` via `toInteracting`), for the genuine limit `μ` from `torusPphi2Limit_exists`
(`TorusNontriviality.lean`). I.e. the connected four-point `u₄(f) = ⟨φ(f)⁴⟩_μ − 3⟨φ(f)²⟩²_μ` is
strictly negative for some `f` — the theory is non-Gaussian = interacting.

Setting: **fixed** torus side `L` (compact, OS0–OS2 already proved here); lattice `(ℤ/Nℤ)²`,
`a = L/N → 0`; `P(φ) = λ:φ⁴:`, `λ > 0`, `m > 0`. Weak coupling (`λ` small) — see §Regime.

## Chosen route: perturbative leading order at weak coupling (NO cluster expansion)
Rationale: at **fixed finite volume** the φ⁴₂ correlations admit a **one-sided asymptotic Taylor
expansion** in `λ` at `0⁺`, with a remainder bound from Nelson hypercontractivity (the Wick power
`:φ⁴:` lies in every `Lᵖ(dμ_GFF)` in `d = 2`). The cluster expansion is needed **only** for the
infinite-volume `L → ∞` limit — which we do **not** take here. So the hard analytic input is a
remainder bound, not a polymer expansion. This is the minimal formalizable route.

> ⚠️ **Gemini-reviewed correction (2026-06-05): do NOT claim analyticity.** `λ ↦ ⟨φ(f)ⁿ⟩_λ` is
> **not analytic** at `λ=0` — the **Dyson instability** (`λ<0` ⟹ `−λφ⁴` unbounded below ⟹ the
> partition function diverges) forces radius of convergence **zero**. What is true and sufficient is
> an **asymptotic expansion from the right**: `u₄(λ) = −κλ∫(Cf)⁴ + R(λ)` with `|R(λ)| ≤ Kλ²` as
> `λ→0⁺`. The remainder is controlled by Hölder + Nelson: the Taylor remainder is
> `⟨φ(f)⁴·V²·e^{−λV}⟩/⟨e^{−λV}⟩`-type, split by Hölder into free-measure `Lᵖ` norms of `φ(f)⁴V²`
> (finite, `d=2`) times `‖e^{−λV}‖_q` (Nelson). **No analyticity, no cluster expansion.**

> 💡 **Gemini-reviewed simplification (consider): work in the continuum directly, drop the lattice.**
> In `d=2` fixed volume the continuum interaction `V = ∫_{T²}:φ⁴: dz` is *already* a well-defined
> `Lᵖ(dμ_GFF^{cont})` random variable (Wick ordering suffices; no UV cutoff needed for `V`). So one
> can define `dμ = Z⁻¹e^{−λV}dμ_GFF^{cont}` directly on the continuum torus GFF and apply the
> asymptotic expansion there — **bypassing the "uniform-in-`a`" steps III/IV entirely**. CAVEAT: the
> genuine measure we currently have (`torusPphi2Limit_exists`) is the *lattice* Prokhorov limit; this
> cleaner route needs either (a) identifying that limit with `Z⁻¹e^{−λV}dμ_GFF^{cont}`, or (b)
> re-basing the construction on the direct continuum measure. **Check what the continuum torus GFF +
> `:φ⁴:`-as-`Lᵖ` infra in pphi2 supports before choosing lattice-uniform vs continuum-direct.**

## Dual review (Gemini deep-think + Codex, 2026-06-05) — verdict: SOUND-WITH-CAVEATS
Both models independently agree: (i) leading term `−κλ∫(C_a f)⁴` is correct, negative,
Wick-ordering-invariant; (ii) **NOT analytic** — use a one-sided `λ→0⁺` asymptotic Taylor remainder
(Dyson instability / Borel-summable, radius 0); (iii) no cluster expansion at fixed `L`; (iv) hardest
step is III; (v) the perturbative route is the standard/cleanest for strict `u₄<0`. Refinements
folded into the steps below:
- **κ is convention-dependent** (Codex): `λ∫:φ⁴:` ⟹ `κ=4!`; pphi2's `InteractionPolynomial` fixes a
  `1/n` leading coefficient, so the Lean quartic likely gives **`κ=6`**. Pin against the repo
  convention (`Polynomial.lean`, `InteractingMeasure/LatticeAction.lean`, `WickPolynomial.lean`'s
  `x⁴−6cx²+3c²`) — step I/V.
- **Step III needs more than Nelson `Lᵖ` on `:φ⁴:`** (Codex): also uniform `E₀[e^{−pλV_a}]`, a
  partition-function lower bound `Z_λ ≥ c > 0`, and `V_a`-insertion moment bounds — all
  cutoff-uniform. Mechanism (Gemini): the remainder `⟨φ(f)⁴V²e^{−λV}⟩/⟨e^{−λV}⟩` split by Hölder
  into free `Lᵖ` norms × `‖e^{−λV}‖_q` (Nelson).
- **[Global]** (Codex): the `TorusNontriviality.lean` predicates are for arbitrary `μ`/`P`; the
  theorem must instantiate a specific `P_λ` (quartic) coupling family with `λ` small.
- **Divergence RESOLVED (infra check 2026-06-05): go LATTICE-UNIFORM.** Gemini floated a
  continuum-direct construction; Codex preferred lattice. A code check settles it: pphi2 is
  lattice-first — the interaction exists only as `interactionFunctional 2 N P (circleSpacing L N) mass`
  (lattice size `N` + spacing), `torusInteractingMeasure = (torusEmbedLift)_*(interactingLatticeMeasure)`,
  and there is **no continuum torus GFF measure / no continuum Wick `:φ⁴:` as an `Lᵖ` variable**.
  Continuum-direct would require building all of that (the construction pphi2 avoided). So use the
  lattice-uniform route — it reuses `torusInteractingMeasure`, `torusPphi2Limit_exists`, and the
  `NelsonEstimate/` lattice bounds (already the cutoff-uniform estimates step III needs).
- **Refs:** Simon *P(φ)₂* Thm V.3.1/V.3.3 (`e^{−λV}∈⋂ₚLᵖ`), Thm VIII.1.1 (asymptotic series);
  Glimm–Jaffe *Quantum Physics* Ch. 8 §8.6 (Wick/Nelson), Ch. 19 §19.1 (P(φ)₂ setup).

## The structure
`u₄^a(f; λ) = −κ·λ·∫_{T²} (C_a f)(z)⁴ dz + R_a(f; λ)`, where `C_a = (−Δ_a + m²)⁻¹` is the lattice
free covariance, `κ > 0` a combinatorial constant, `|R_a(f;λ)| ≤ K(f)·λ²` **uniformly in `a`**.
Since `∫(C_a f)⁴ > 0` strictly (4th power of a nonzero continuous function), for `λ` small enough
`u₄^a(f;λ) ≤ −(κλ/2)∫(C_a f)⁴ < 0` uniformly in `a`; passing to the limit gives `u₄(f) < 0`.

## Steps (status-machine; each a lemma + its obligation)
### Step I — Wick route pinned (2026-06-05), framework landed
**Decisive simplification (the Wick-orthogonality route).** `u₄(f) = ⟨:φ(f)⁴:⟩` (4th cumulant =
expectation of the Wick-ordered 4th power), so along the coupling family `μ_g`:
`u₄'(0) = −⟨:φ(f)⁴: · V⟩_free` (the `⟨:φ(f)⁴:⟩_free = 0` and disconnected terms vanish by Wick
orthogonality — automatically connected). With `V = a²∑_z :(1/4)φ(δ_z)⁴:`,
`u₄'(0) = −(1/4)·a²∑_z ⟨:φ(f)⁴::φ(δ_z)⁴:⟩ = −(1/4)·a²∑_z 4!(C_a f)(z)⁴ = −6∫(C_a f)⁴`.
- **Framework DONE** (`FieldRedefinition.lean`, sorry-free): the coupling family `μ_g`, `μ_0 = free`
  (`interactingMeasure_zero{,_smul}`), and the baseline `u₄(μ_0) = 0`
  (`connectedFourPoint_interactingMeasure_zero_smul`, composing the free-field anchor).
- **Sub-lemmas remaining (the core):**
  1. ✅ **DONE (2026-06-05). Smeared Wick inner product** `⟨:φ(f)ⁿ::φ(g)ᵐ:⟩ = δₘₙ·n!·⟨φfφg⟩ⁿ` for
     arbitrary smeared lattice fields — the Mehler/Wick kernel. Proved as
     `GaussianField.gff_wickPower_two_smeared_inner` (branch `smeared-wick-inner` in the
     `gaussian-field` checkout), **axiom-clean** (`propext, Classical.choice, Quot.sound`). Key
     realization (from the user's "2-D Gaussian subspace" framing): the heavy lifting
     `wickMonomial_pow_sum_expansion_of_totalDegree` is *already* general, so this is just an
     `ω`-linearity generalization of `gff_wickPower_two_site_inner` (`γⱼ(x)↦Γⱼ(f)=Σₓ f(x)γⱼ(x)`),
     **not** a from-scratch Mehler proof. `n=m=4` gives `4!⟨φfφg⟩⁴`. Added helpers: `gffSmearedCoeff`,
     `gffSmearedCovariance`, `omega_eval_smeared_eq_sum_gamma_xi`, `wickMonomial_at_smeared_eq_eigen_sum`.
     ✅ **PERSISTED**: pushed to `gaussian-field` main `0145126` (kernel + public covariance API),
     pphi2 re-pinned, full build green.
     ✅ **pphi2-side atom landed**: `Pphi2.wickFourth_smeared_vertex_inner`
     (`InteractingMeasure/SmearedWickVertex.lean`) — `∫ :φ(f)⁴::φ(δ_z)⁴: dμ_GFF = 24·(∑_x f(x) C(x,z))⁴`,
     axiom-clean, in the umbrella build. The atom of the vertex sum.
  2. **First-order coefficient** `u₄'(0) = −⟨:φ(f)⁴:·V⟩_free` — the explicit `e^{−gV}=1−gV+O(g²)`
     expansion (algebraic; the `O(g²)` is step III) or `hasDerivAt_integral_of_dominated…`.
     **[REMAINING — the hard analysis piece.]**
  3. ✅ **DONE (2026-06-05) via the public API.** The `(C_a f)(z) = ∑_x f(x) C(x,z)` operator object is
     exactly `GaussianField.gffSmearedCovariance f (Pi.single z 1)`, proved equal to `∑_x f(x)·
     gffPositionCovariance x z` by `gffSmearedCovariance_single_right` (pin `0145126`). The kernel's
     value `gffSmearedCovariance f g` rewrites to `∑_{x,y} f(x)g(y) C(x,y)` via
     `gffSmearedCovariance_eq_sum_position`, and the Wick constant `∑_j Γ_j(f)² = gffSmearedCovariance
     f f` via `gffSmearedCovariance_self`. So the `(C_a f)`/covariance plumbing is in place.
  Then step II (`∫(C_a f)⁴ > 0`) and the `a²∑_z = ∫` assembly. **Status: (1) smeared Wick kernel —
  the bottleneck — DONE & axiom-clean; (3) the `(C_a f)` covariance plumbing DONE via the public API.
  REMAINING (precise chain, in order):
  - ✅ **(2a) DONE (2026-06-05). `wickConstant`↔eigenbasis bridge.**
    `GaussianField.gffPositionCovariance_eq_covarianceGJ`: `gffPositionCovariance x y =
    covariance(latticeCovarianceGJ) δ_x δ_y` (both `= (a^d)⁻¹Σ_k λ_k⁻¹ e_k(x)e_k(y)`, via
    `lattice_covariance_GJ_eq_spectral`), pushed to `gaussian-field` `2345d14`. pphi2-side
    `Pphi2.wickConstant_eq_gffPositionCovariance` (`InteractingMeasure/WickConstantBridge.lean`):
    `wickConstant = gffPositionCovariance x x`, combining the bridge with `wickConstant_eq_variance` +
    `finLatticeDelta = Pi.single`. Both axiom-clean, umbrella green. The atom now plugs into `V`.
  - ✅ **(2b) DONE (2026-06-05), axiom-clean.** `Pphi2.wickFourth_interaction_inner_quartic`
    (`InteractingMeasure/InteractionFourPoint.lean`): `∫ :φ(f)⁴:·(a^d ∑_z wickPolynomial P
    (wickConstant)(φ_z)) dμ_GFF = 6·a^d·∑_z(C_a f)(z)⁴` for `P.n=4` — i.e. `⟨:φ(f)⁴:·V⟩_free =
    6∫(C_a f)⁴`, the first-order coefficient `−u₄'(0)`. Chain: per-term `wickFourth_smeared_site_inner`
    (`if 4=m then 24(C_a f)(z)⁴ else 0`) → per-vertex `wickFourth_wickPolynomial_inner` (degree-4
    weight of `P`) → `_quartic` (`P.n=4` ⟹ `1/4·24=6`; lower terms vanish, `↑m<4`) → site sum (pull
    `a^d·∑_z` out via `integrable_wickFourth_wickPolynomial`). Namespaces bridged via
    `wickMonomial_eq_root_local`. Prereqs all pushed/axiom-clean (incl.
    `GaussianField.integrable_wickMonomial_smeared_mul`, pin `d9cdd5e`).
  - **(2c) the differentiation** `u₄'(0)=−⟨:φ(f)⁴:V⟩` — **the hardest of step I; pure hard analysis,
    almost no existing infrastructure** (only the `g=0` baseline in `FieldRedefinition.lean`; the
    field-rescale lemma is a *symmetry*, not a derivative). Precise discharge chain (2026-06-05 scope):
    1. ✅ **Domination integrability DONE (2026-06-05), axiom-clean** —
       `InteractingMeasure/MomentIntegrability.lean`: `integrable_powMul_interaction`
       (`Integrable((ω f)ⁿ·V)`, `V=a^d∑_z wickPolynomial`). Chain: `pairing_memLp_lattice`
       (`ω f∈Lᵖ`) → `integrable_pow_pairing` (`(ω f)ⁿ`, `‖·‖^n` route, no `MemLp.pow` needed) →
       `integrable_pow_pairing_mul` (`(ω f)ⁿ(ω g)ᵐ`, AM–GM) → `integrable_powMul_wickMonomial`
       (`(ω f)ⁿ(ω δz)ˡ:（ω δz)ᵏ:`, **strong induction on Wick degree** with the `(ω δz)ˡ` factor
       carrying the recursion's `x·`) → `_wickPolynomial` → `_interaction`.
    2. **Moment derivative — the one-sided wall: ENABLER DONE (2026-06-05).** The obstruction was that
       Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le` is two-sided, but `e^{−gV}` is
       integrable-dominated only for `g≥0` (Dyson: `V→+∞`). ✅ **Resolved by a new general, axiom-clean,
       Mathlib-upstreamable lemma** `MeasureTheory.hasDerivWithinAt_Ici_integral_of_dominated_of_deriv_le`
       (`MathlibContrib/ParametricIntegralWithin.lean`): the **within-`Ici x₀` (right) derivative under
       the integral**, domination required only on `Ici x₀ ∩ ball x₀ ε`. Proof reuses the existing
       two-sided theorem via an **affine extension** of `F` across `x₀` (two-sided dominated), then
       restricts. Self-contained (Mathlib imports only). **REMAINING (instantiation, mechanical)**:
       apply it to `F g ω = (ω f)ⁿ e^{−gV(ω)}`, `F' g ω = −(ω f)ⁿ V e^{−gV}`, `x₀=0` — hypotheses:
       measurability, `F 0` integrable (`∫(ω f)ⁿ`), bound `|F' g|≤e^{εA}|(ω f)ⁿV|` integrable
       (**brick 1**, `integrable_powMul_interaction`, is exactly `F'` at `g=0`; `V≥−A` from
       `latticeInteraction_bounded_below`), within-deriv `HasDerivWithinAt (g↦e^{−gV}) (−Ve^{−gV})`.
       Gives `HasDerivWithinAt (g↦∫(ω f)ⁿe^{−gV}) (−∫(ω f)ⁿV) (Ici 0) 0`.
       ✅ **INSTANTIATION DONE (2026-06-06), axiom-clean** — `Pphi2.moment_hasDerivWithinAt`
       (`InteractingMeasure/MomentDerivative.lean`): exactly that, for `V = interactionFunctional`
       (`= a^d∑_z wickPolynomial(ω δ_z)`, bounded below). The hard differentiation core of 2c is done.
       Then bricks 3–5 (Z, quotient rule, cumulant→Wick) use existing `HasDerivWithinAt` calculus:
       ✅ **brick 3 DONE** `partitionFn_hasDerivWithinAt` (`Z'(0)=−∫V`, `n=0` case; `Z 0=1`);
       ✅ **brick 4 DONE** `normalizedMoment_hasDerivWithinAt` (`⟨φ(f)ⁿ⟩'(0)=−∫(ω f)ⁿV+(∫(ω f)ⁿ)(∫V)
       =−⟨(ω f)ⁿ;V⟩^c`, via `HasDerivWithinAt.div`+`Z 0=1`) — both axiom-clean
       (`InteractingMeasure/ConnectedCorrelatorDerivative.lean`). **Bricks 1–4 = the full differentiation
       machinery, DONE.**
       ✅ **brick 5 DONE (2026-06-05), axiom-clean** — `u4_hasDerivWithinAt`
       (`InteractingMeasure/U4Derivative.lean`): for the normalised-moment `u₄(g)=⟨φ(f)⁴⟩_g−3⟨φ(f)²⟩²_g`,
       `HasDerivWithinAt u₄ (−6·a^d·∑_z(C_a f)(z)⁴) (Ici 0) 0`. Combines brick 4 at `n=4,2` via the
       product rule, reduces via Isserlis (`connectedFourPoint_gaussianMeasure_eq_zero`) + variance bridge
       (`gff_wickPower_two_smeared_inner` at `n=m=1`), bridges to **2b**
       (`wickFourth_interaction_inner_quartic`). **STEP 2c (bricks 1–5) COMPLETE: `u₄'(0)=−6∫(C_a f)⁴`.**
       ✅ **STEP II DONE (2026-06-05), axiom-clean** (`U4Derivative.lean`): `quartic_kernel_sum_pos`
       (`C_a f≢0 ⟹ 0<∑(C_a f)⁴`), `u4_slope_neg` (`0<a ∧ C_a f≢0 ⟹ u₄'(0)<0`), and a concrete witness
       `exists_u4_slope_neg` (single-site `δ_{z₀}`, since `C_a δ_{z₀}(z₀)=gffPositionCovariance z₀ z₀
       =wickConstant>0`). **Steps I+II compose ⟹ ∃ f, the weak-coupling slope `u₄'(0)<0` strictly.**
       Remaining for the full axiom discharge: step III (the `O(g²)` Nelson remainder, cutoff-uniform)
       to conclude `u₄(g)<0` at small `g>0`, then the torus/continuum + `N`-uniformity framing of
       `torus_weakCoupling_lattice_connectedFourPoint_strictNeg` itself.
    2. **Moment derivative** `d/dg ∫(ω f)ⁿ e^{−gV} dμ_GFF |_{g=0} = −∫(ω f)ⁿ V dμ` via Mathlib
       `hasDerivAt_integral_of_dominated_loc_of_deriv_le`: `∂_g = −(ω f)ⁿ V e^{−gV}`, dominated by
       `e^{g₀A}·|(ω f)ⁿ V|` using `V ≥ −A` (`latticeInteraction_bounded_below`) on `g∈[0,g₀]`.
    3. **Partition function** `Z_g=∫e^{−gV}`, `Z_0=1` (prob. measure), `Z'(0)=−∫V`.
    4. **Ratio (quotient rule, `Z_0=1`)** `d/dg⟨(ω f)ⁿ⟩_g|_0 = −∫(ω f)ⁿV+(∫(ω f)ⁿ)(∫V) =
       −⟨(ω f)ⁿ;V⟩^c` (connected).
    5. **Cumulant→Wick algebra** `u₄'(0)=−⟨φ⁴;V⟩^c+6⟨φ²⟩₀⟨φ²;V⟩^c = −⟨:φ(f)⁴:V⟩` — reduces to
       Isserlis `⟨φ(f)⁴⟩_free=3⟨φ(f)²⟩²` (already have, `connectedFourPoint_gaussianMeasure_eq_zero`);
       this is the bridge to **2b's** `⟨:φ(f)⁴:V⟩=6∫(C_a f)⁴`. Gives `u₄'(0)=−6∫(C_a f)⁴<0`.
    Estimated ~300–500 lines; the genuinely hard analytic core, deserves dedicated focus (distinct from
    the now-complete *algebraic* steps 1/2a/2b/3).
  - then **step II** positivity (`∑_z(C_a f)(z)⁴>0` from `C` positive-definiteness — needs
    `gffSiteVariance > 0`, currently not packaged in the eigenbasis; provable via `eigenbasis_completeness`
    or the `wickConstant>0` bridge) and **step III** the Nelson `O(g²)` remainder (deepest).** The base
  measures match (`interactingLatticeMeasure` is built over
  `latticeGaussianMeasure`, exactly the kernel's measure), so no measure bridge is needed.

- [ ] **I. Leading-order coefficient.** `d/dλ u₄^a|_{λ=0}(f) = −κ ∫_{T²}(C_a f)(z)⁴ dz` with `κ > 0`.
  Wick/Isserlis on the free GFF: the O(λ) connected part of `⟨φ(f)⁴⟩` is the single-vertex tree
  with all four external legs `C_a f` attached to one `:φ⁴(z):` vertex; the `4!`-fold leg matching
  gives `u₄'(0) = −κ∫(C_a f)⁴`. **Wick ordering does NOT change this term** — the tadpole subtractions
  in `:φ⁴: = φ⁴ − 6cφ² + 3c²` only remove self-contractions at the vertex, but the connected 4-point
  uses all four vertex fields on external legs (no self-contraction), so they're untouched.
  ⚠️ **κ convention-dependent (pin it):** `λ∫:φ⁴:` ⟹ `κ=4!=24`; pphi2's `InteractionPolynomial` carries
  a `1/n` leading coeff (`(1/4):φ⁴:`) ⟹ `κ=6` if `λ` scales the whole interaction. Read off from
  `Polynomial.lean` / `InteractingMeasure/LatticeAction.lean` + `WickPolynomial.lean`; also fix the
  lattice normalization (`a²∑_z` vs `∫`). Sign negative regardless (from `e^{−λV}`).
  *Infra:* pphi2 Wick machinery (`WickMultivariate.lean`, `gffMultiWickMonomial_*`, proved Wick
  orthogonality). **Difficulty ★★** (combinatorics; the connected/cumulant bookkeeping is the bulk).
- [ ] **II. Strict positivity of the coefficient.** `∫_{T²}(C_a f)(z)⁴ dz > 0` for `f ≠ 0`. `C_a`
  positive-definite ⟹ `C_a f ≠ 0` (as a lattice function), `(C_a f)⁴ ≥ 0` pointwise with a point
  where it's positive ⟹ integral `> 0`. *Infra:* `massOperatorAsym_pos_def` / the torus propagator
  positivity. **Difficulty ★** (positivity of a 4th power).
- [ ] **III. Cutoff-uniform remainder bound.** `|R_a(f;λ)| ≤ K(f)·λ²` with `K(f)` independent of
  `a`, as `λ→0⁺`. **THE crux.** ⚠️ **NOT analyticity** (Dyson instability ⟹ radius 0; the series is
  asymptotic/Borel, dual-review-confirmed): a **one-sided positive-λ 2nd-order Taylor remainder**.
  Mechanism: the remainder is `⟨φ(f)⁴·V²·e^{−λV}⟩₀/⟨e^{−λV}⟩₀`-type; Hölder-split into free `Lᵖ`
  norms of `φ(f)⁴V²` (finite/cutoff-uniform, `d=2`) times `‖e^{−λV}‖_q` (Nelson). Codex caveat —
  beyond Nelson `Lᵖ` on `:φ⁴:`, the bound also needs: uniform `E₀[e^{−pλV_a}]`, a partition-function
  **lower bound** `Z_λ ≥ c>0`, and `V_a`-insertion moment bounds, all cutoff-uniform. **No cluster
  expansion** (fixed `L`; that's only for `L→∞`).
  *Infra:* `NelsonEstimate/` (hypercontractivity / polynomial-chaos) — currently aimed at the OS0
  exp-moment bound; the analyticity/Taylor-remainder use is **new work on the same estimates**.
  **Difficulty ★★★** (the genuine analytic core). *Cite:* Glimm–Jaffe *Quantum Physics* Ch. 8–9
  (fixed-volume `exp(−V) ∈ Lᵖ`, `V` form-bounded); Simon *P(φ)₂* Ch. V, VIII (perturbation series,
  Nelson bound, Borel summability) — confirm the exact statement of cutoff-uniform analyticity.
- [ ] **IV. 4th-moment convergence to the limit.** `⟨φ(f)⁴⟩_{μ_{φ n}} → ⟨φ(f)⁴⟩_μ` and the same for
  the 2nd moment, along the Prokhorov subsequence. Weak convergence (`torusInteractingLimit_exists`)
  gives only bounded-continuous observables; `(φ(f))⁴` is unbounded. Close the gap with **uniform
  integrability**: a cutoff-uniform `⟨|φ(f)|^{4+ε}⟩_a ≤ C` (Nelson) ⟹ Vitali ⟹ moment convergence.
  *Infra:* the uniform moment bounds behind `torus_interacting_tightness`. **Difficulty ★★.**
- [ ] **V. Assemble.** From III+IV: `u₄(f) = limₙ u₄^{a_n}(f) ≤ −(κλ/2)∫(C f)⁴ < 0` (II), using
  `∫(C_{a_n}f)⁴ → ∫(Cf)⁴ > 0` (propagator convergence, cf. `second_moment_asym_tendsto`-style).
  Conclude `TorusIsInteractingStrict L μ`, hence `TorusIsInteracting`. **Difficulty ★** (glue).

## Regime — CORRECTED (step-0 infra finding 2026-06-05): weak coupling = LARGE MASS
⚠️ pphi2 has **no tunable bare coupling**: `InteractionPolynomial.eval = (1/n)τⁿ + Σcoeffₘτᵐ` hardwires
the quartic coefficient to `1/n = 1/4` (`Polynomial.lean:42`); `interactionFunctional` carries no `λ`
(the `coupling` in `isPhi4` is unused/phantom). So the small-`λ` expansion is **not available on
pphi2's measure as-is**. The weak-coupling regime is realized instead as **large mass `m`** (effective
coupling `∼ 1/(4m²)`; `m` IS a free parameter): at large `m`, `C_a=(−Δ_a+m²)⁻¹` is small, the
single-vertex term dominates, higher orders are suppressed by extra propagator powers. **This reuses
`torusInteractingMeasure` (fixed coupling) — no new λ-family.** Note `u₄ → 0` as `m → ∞`, so the
target is `u₄(f) < 0` (small but strictly negative) for `m > m₀(L,f)`.
- **κ = 6 confirmed** from the encoding: leading term `= −4!·(1/4)·∫(C_a f)⁴ = −6∫(C_a f)⁴`.
- The expansion parameter is the propagator size `‖C_a‖ ∼ 1/m²` (perturbation in the interaction
  order, controlled by large `m`), NOT a bare `λ`. The leading single-vertex diagram is unchanged;
  the step-III remainder bound is now "`|R| ≤ K·‖C_a‖²`-type, small for large `m`" — re-examine the
  large-mass control (still Nelson + `Z` lower bound, but the small parameter is `1/m²`).
- Alternative (more infra): introduce a genuine `λ`-scaled interaction family
  `Z⁻¹exp(−λ·interactionFunctional)dμ_GFF` and prove for small `λ` — but that's a new measure family
  (+ its own tightness/limit), so prefer the large-mass realization on the existing measure.
- (Non-perturbative all-coupling via Lebowitz + uniform strict lower bound is the other alternative
  for step III, but formalizing Lebowitz — random currents — is harder than the large-mass remainder.)

## Hardest input / first action
**Step III** (cutoff-uniform one-sided Taylor remainder). The dual design pass (Gemini deep-think +
Codex, 2026-06-05) is **DONE** — verdict SOUND-WITH-CAVEATS, corrections folded in above (chiefly:
no analyticity ⟹ one-sided remainder; κ convention; the extra `Z_λ`/`e^{−pλV}`/`V`-moment inputs for
III). **First concrete actions:** (0) pin `κ` + the lattice normalization against
`InteractionPolynomial`/`WickPolynomial` and instantiate the specific `P_λ` family in
`TorusNontriviality.lean`; (1) step II (★ positivity); (2) step I (★★ Wick `O(λ)` coefficient). Then
the step-III analytic core. (Route fork resolved: **lattice-uniform** — pphi2 has no continuum-direct
infra; see the dual-review block.)

## Execution order — STEP IV IS THE FOUNDATION (step-0 finding 2026-06-05)
The genuine limit `μ` (`torusPphi2Limit_exists`) is exposed only via **weak convergence
(bounded-continuous test functions)** and a **t=1 MGF** (`IsTorusGaussianContinuumLimit.isGaussian`,
`torusGaussianLimit_isGaussian` — both give only `∫e^{ωf}=e^{½∫(ωf)²}`, not the full law). But
`u₄(f)` involves `∫(ωf)⁴` with `(ωf)⁴` **unbounded**. So **every moment statement is gated on
step IV** (4th-moment convergence `⟨(ωf)⁴⟩_{a_n} → ⟨(ωf)⁴⟩_μ`), including even the free base case
`u₄(free)=0`. ⟹ **Build step IV FIRST** — it is the shared prerequisite, not a late step.
- Step IV inputs (confirmed available): uniform `⟨|φ(f)|^{4+ε}⟩_a ≤ C` from the Nelson exp-moment
  bound (the OS0 estimate ⟹ all moments uniform) + Vitali/uniform-integrability ⟹ moment convergence.
- Free base case route (if wanted as a validation lemma): `weakLimit_centered_gaussianReal` +
  `pushforward_eval_gaussianReal` + `integral_pow4_gaussianReal` (`∫x⁴ dgaussianReal(0,v)=3v²`) —
  but it concerns the *free* limit (a different measure), so it validates the test rather than
  advancing the interacting `u₄<0`. Skip unless a sanity check is wanted.
- Confirmed infra for the other steps: `gffMultiWickMonomial` + orthogonality (step I Wick `O(λ)`),
  `second_moment_eq_covariance`/`lattice_second_moment_eq_inner` (the `C f` object, steps I/II/V),
  `NelsonEstimate/` (steps III, IV). All present; each step is a substantial multi-step proof.

**Revised order:** IV (moment access — foundation) → I (Wick leading term, free measure) → II
(positivity) → III (large-mass remainder, the crux) → V (assemble). No step lands sorry-free without
IV first. This is a focused multi-day implementation, fully scoped & dual-vetted; no quick increment.

### Step IV progress (2026-06-05)
- **IV.a DONE** — `TorusInteractingMoments.lean`, sorry-free & **axiom-clean**
  (`propext/Classical.choice/Quot.sound` only): `torus_interacting_fourth_moment_uniform`
  (`∫(ωf)⁴dμ_{P,N} ≤ C`, for `u₄`) and `torus_interacting_eighth_moment_uniform`
  (`∫(ωf)⁸dμ_{P,N} ≤ C`, gives **uniform integrability of `(ωf)⁴`**). Template: Cauchy–Schwarz
  density transfer + Nelson exp estimate + Gaussian hypercontractivity (`∫(ωg)^{2p} ≤ (2p−1)^p(∫(ωg)²)^p`).
- **IV.b CORE DONE** — `moment_tendsto_of_uniform` (`TorusInteractingMoments.lean`, sorry-free): the
  reusable ε/3 truncation lemma. Weak (bounded-cont) convergence + UI domination `F−min(F,M) ≤ G/M`
  + integrability + cutoff-uniform `∫G ≤ C` (both `νn` and `μ`) ⟹ `∫F ∂νn → ∫F ∂μ`. Tails `≤ C/M`
  uniform; middle converges weakly.
- **IV.b INSTANTIATION DONE** — all in `TorusInteractingMoments.lean`, sorry-free & axiom-clean:
  - `sub_min_le_sq_div` (the UI domination `y−min(y,M) ≤ y²/M`).
  - `torus_interacting_abs_pow_integrable` (`|ωf|^k` integrable under `torusInteractingMeasure`).
  - `limit_le_of_uniform_bound` (limit integrability + `∫F∂μ ≤ C` from a uniform bound — avoids the
    `x^k ≤ k!e^x` detour; truncation+MCT, the "bound side").
  - `torus_interacting_second_moment_tendsto`, `torus_interacting_fourth_moment_tendsto`
    (`⟨(ωf)²⟩_{μ_N}→⟨(ωf)²⟩_μ`, `⟨(ωf)⁴⟩_{μ_N}→⟨(ωf)⁴⟩_μ`).
  - `torus_connectedFourPoint_tendsto` (`u₄(μ_N) → u₄(μ)` — the step-IV⟹V bridge).

## ✅ STEP IV COMPLETE (2026-06-05)
The entire measure-theoretic foundation — moment access to the Prokhorov limit, the genuinely hard
part flagged as the prerequisite for everything — is **proved, sorry-free, axiom-clean**. Any uniform
strict lattice bound `u₄(μ_N) ≤ −c < 0` now passes to `u₄(μ) ≤ −c < 0` via
`torus_connectedFourPoint_tendsto`, giving `TorusIsInteractingStrict μ`.

**Remaining for `u₄ < 0`:** step I (Wick leading term `u₄'·(interaction) = −6∫(C_a f)⁴`) + step III
(large-mass remainder ⟹ uniform `u₄(μ_N) ≤ −c < 0` for `m > m₀`) → step V (apply the bridge). I and
III are independent of IV and of each other's measure theory (pure Wick combinatorics + Nelson
large-mass control).

## What this replaces
The honest, measure-genuine version of axiom 9 `continuumLimit_nonGaussian` (currently `∃μ` on the
δ₀-vacuous ℝ² predicate). Here `μ` actually exists (T², axiom-clean), and the statement is about it.
Infinite-volume/ℝ² interaction would additionally need the `L → ∞` cluster expansion (out of scope).

## Existing infra to reuse
- `torusPphi2Limit_exists`, `torusInteractingMeasure`, `torus_interacting_tightness` (proved).
- Wick: `WickMultivariate.lean`, `gffMultiWickMonomial_*` (the O(λ) computation).
- Nelson: `NelsonEstimate/` (steps III, IV — the uniform Lᵖ / hypercontractive bounds).
- Free covariance positivity + propagator convergence (steps II, V).
