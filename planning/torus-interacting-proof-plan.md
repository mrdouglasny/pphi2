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

## Regime
Weak coupling (`λ < λ₀(m,L)`). Honest and unavoidable: `u₄ ≠ 0` needs `λ > 0`, and the clean
remainder control is perturbative. (Non-perturbative all-`λ` single-phase via Lebowitz + a uniform
strict lower bound is an alternative for step III, but formalizing the Lebowitz inequality — random
currents / duplicated variables — is harder than the Nelson remainder bound. Prefer perturbative.)

## Hardest input / first action
**Step III** (cutoff-uniform one-sided Taylor remainder). The dual design pass (Gemini deep-think +
Codex, 2026-06-05) is **DONE** — verdict SOUND-WITH-CAVEATS, corrections folded in above (chiefly:
no analyticity ⟹ one-sided remainder; κ convention; the extra `Z_λ`/`e^{−pλV}`/`V`-moment inputs for
III). **First concrete actions:** (0) pin `κ` + the lattice normalization against
`InteractionPolynomial`/`WickPolynomial` and instantiate the specific `P_λ` family in
`TorusNontriviality.lean`; (1) step II (★ positivity); (2) step I (★★ Wick `O(λ)` coefficient). Then
the step-III analytic core. (Route fork resolved: **lattice-uniform** — pphi2 has no continuum-direct
infra; see the dual-review block.)

## What this replaces
The honest, measure-genuine version of axiom 9 `continuumLimit_nonGaussian` (currently `∃μ` on the
δ₀-vacuous ℝ² predicate). Here `μ` actually exists (T², axiom-clean), and the statement is about it.
Infinite-volume/ℝ² interaction would additionally need the `L → ∞` cluster expansion (out of scope).

## Existing infra to reuse
- `torusPphi2Limit_exists`, `torusInteractingMeasure`, `torus_interacting_tightness` (proved).
- Wick: `WickMultivariate.lean`, `gffMultiWickMonomial_*` (the O(λ) computation).
- Nelson: `NelsonEstimate/` (steps III, IV — the uniform Lᵖ / hypercontractive bounds).
- Free covariance positivity + propagator convergence (steps II, V).
