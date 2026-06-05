# Proof plan — `TorusIsInteracting` (the φ⁴₂ theory on T² is interacting)

**Target:** `∃ f, torusConnectedFourPoint L μ f < 0` (`TorusIsInteractingStrict`, which implies
`TorusIsInteracting` via `toInteracting`), for the genuine limit `μ` from `torusPphi2Limit_exists`
(`TorusNontriviality.lean`). I.e. the connected four-point `u₄(f) = ⟨φ(f)⁴⟩_μ − 3⟨φ(f)²⟩²_μ` is
strictly negative for some `f` — the theory is non-Gaussian = interacting.

Setting: **fixed** torus side `L` (compact, OS0–OS2 already proved here); lattice `(ℤ/Nℤ)²`,
`a = L/N → 0`; `P(φ) = λ:φ⁴:`, `λ > 0`, `m > 0`. Weak coupling (`λ` small) — see §Regime.

## Chosen route: perturbative leading order at weak coupling (NO cluster expansion)
Rationale: at **fixed finite volume** the φ⁴₂ correlations are analytic in `λ` near `0`, **uniformly
in the UV cutoff `a`**, purely from Nelson hypercontractivity (the Wick power `:φ⁴:` lies in every
`Lᵖ(dμ_GFF,a)` with `a`-uniform norm in `d = 2`). The cluster expansion is needed **only** for the
infinite-volume `L → ∞` limit — which we do **not** take here. So the hard analytic input is a
cutoff-uniform remainder bound, not a polymer expansion. This is the minimal formalizable route.

## The structure
`u₄^a(f; λ) = −κ·λ·∫_{T²} (C_a f)(z)⁴ dz + R_a(f; λ)`, where `C_a = (−Δ_a + m²)⁻¹` is the lattice
free covariance, `κ > 0` a combinatorial constant, `|R_a(f;λ)| ≤ K(f)·λ²` **uniformly in `a`**.
Since `∫(C_a f)⁴ > 0` strictly (4th power of a nonzero continuous function), for `λ` small enough
`u₄^a(f;λ) ≤ −(κλ/2)∫(C_a f)⁴ < 0` uniformly in `a`; passing to the limit gives `u₄(f) < 0`.

## Steps (status-machine; each a lemma + its obligation)
- [ ] **I. Leading-order coefficient.** `d/dλ u₄^a|_{λ=0}(f) = −κ ∫_{T²}(C_a f)(z)⁴ dz` with `κ > 0`.
  Wick/Isserlis on the free GFF: the O(λ) connected part of `⟨φ(f)⁴⟩` is the single-vertex tree
  with all four external legs `C_a f` attached to one `:φ⁴(z):` vertex; the `4!`-fold leg matching
  gives `κ = 4!` (with the `λ∫:φ⁴:` normalization; `κ = 1` with `λ/4!`). **Wick ordering does NOT
  change this term** — the tadpole subtractions in `:φ⁴: = φ⁴ − 6cφ² + 3c²` only remove
  self-contractions at the vertex, but the connected 4-point uses all four vertex fields on external
  legs (no self-contraction), so they're untouched. Pin `κ` precisely during formalization.
  *Infra:* pphi2 Wick machinery (`WickMultivariate.lean`, `gffMultiWickMonomial_*`, proved Wick
  orthogonality). **Difficulty ★★** (combinatorics; the connected/cumulant bookkeeping is the bulk).
- [ ] **II. Strict positivity of the coefficient.** `∫_{T²}(C_a f)(z)⁴ dz > 0` for `f ≠ 0`. `C_a`
  positive-definite ⟹ `C_a f ≠ 0` (as a lattice function), `(C_a f)⁴ ≥ 0` pointwise with a point
  where it's positive ⟹ integral `> 0`. *Infra:* `massOperatorAsym_pos_def` / the torus propagator
  positivity. **Difficulty ★** (positivity of a 4th power).
- [ ] **III. Cutoff-uniform remainder bound.** `|R_a(f;λ)| ≤ K(f)·λ²` with `K(f)` independent of
  `a`. **THE crux.** Route: analyticity of `λ ↦ ⟨φ(f)⁴⟩_λ` (and `⟨φ(f)²⟩_λ`) on a disk `|λ| < r₀`
  with `r₀, K` uniform in `a`, from the convergent Wick-ordered perturbation series — bounded by
  Nelson's hypercontractive estimates: `‖:φ⁴:(g)‖_{Lᵖ(μ_GFF,a)} ≤ C_p` uniformly in `a` (`d = 2`).
  Equivalently a uniform 2nd-order Taylor bound on `u₄^a(·;λ)`. **No cluster expansion** (fixed `L`).
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
**Step III** (cutoff-uniform remainder). Before formalizing: a Gemini/Codex design pass to pin the
exact cutoff-uniform analyticity statement and its minimal Nelson input (the prior deep-think on the
`S₂` direction already validated the analogous `S₂''(0) = 96∫(Cf)C³(Cf)` second-order structure and
the "fixed-volume ⟹ no cluster expansion" claim). Steps I, II are independently startable now.

## What this replaces
The honest, measure-genuine version of axiom 9 `continuumLimit_nonGaussian` (currently `∃μ` on the
δ₀-vacuous ℝ² predicate). Here `μ` actually exists (T², axiom-clean), and the statement is about it.
Infinite-volume/ℝ² interaction would additionally need the `L → ∞` cluster expansion (out of scope).

## Existing infra to reuse
- `torusPphi2Limit_exists`, `torusInteractingMeasure`, `torus_interacting_tightness` (proved).
- Wick: `WickMultivariate.lean`, `gffMultiWickMonomial_*` (the O(λ) computation).
- Nelson: `NelsonEstimate/` (steps III, IV — the uniform Lᵖ / hypercontractive bounds).
- Free covariance positivity + propagator convergence (steps II, V).
