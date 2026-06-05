# Plan — λ-scaled coupling family (option (c)): unblock the perturbative u₄ < 0

**Decision (user, 2026-06-05):** introduce a coupling-scaled family of interacting measures so the
clean `λ`-derivative is available, making step I (`u₄'(0)`) and step III (small-`λ` remainder)
tractable. This replaces pphi2's fixed-coupling (`1/4` quartic, no `λ`) obstruction.

The continuation of `torus-interacting-proof-plan.md`. **Step IV is DONE** (axiom-clean): the
moment-convergence machinery `torus_connectedFourPoint_tendsto` already passes any uniform strict
lattice bound `u₄(μ_{λ,N}) ≤ −c < 0` to the continuum limit ⟹ `TorusIsInteractingStrict μ_λ`.

## ⭐ Reframing (owner, 2026-06-05): field redefinition translates varying-`m` ↔ varying-`λ`
Don't build a fresh λ-family + re-derive Nelson/tightness. Instead use a **field-redefinition
theorem** `φ → c·φ` to translate the **existing, already-tunable `m` parameter** into the coupling.
- Scaling the field by `c` scales the free covariance by `c²` (precision by `1/c²`) and the quartic
  coupling by `c⁴` (`∫(cφ)⁴ = c⁴∫φ⁴`). In `d=2` the theory depends only on the dimensionless
  coupling `g = λ/m²`, so `(m,λ) ↔ (m',λ')` at equal `g` — varying `m` at fixed (hardwired) quartic
  *is* varying the effective coupling. The perturbative (small-`g`) regime = **large `m`**, reached
  via the field-redefinition theorem rather than a new measure family.
- **Existing pphi2 `mass_reparametrization_invariance` is NOT usable** — it's proved `:= h_limit`
  (the δ₀-vacuous artifact, works only because `IsPphi2Limit` ignores `P,mass`; memory
  `pphi2-existence-vacuous-delta0`). A **genuine** field-redefinition theorem must be established.
- **Building blocks present:** `map_smul ω t f : ω (t • f) = t · ω f` (test-fn/field linearity, used
  in `mgf_at_scaled`, `IRLimit/UniformExponentialMoment.lean`); GaussianField `gaussianReal_map_const_mul`
  / covariance-under-`smul` scaling. The genuine theorem = field-scaling pushforward on the
  *interacting* measure: `(c·)_* μ_int[T,λ] = μ_int[c·T, λ/c⁴]`-type, relating couplings via the
  covariance scale.
- ⚠️ **The exact `a`/`c`/`λ` powers and the `d=2` `(m,λ)`-scaling relation are error-prone** (the
  crux-2 covariance-`a`-power lesson, memory `gaussianfield-covariance-sqrt-convention`). **Vet the
  precise scaling with Gemini/Codex before committing.**

## The family
```
dμ_{λ,N} = Z_{λ,N}⁻¹ · exp(−λ · interactionFunctional 2 N P (circleSpacing L N) mass) dμ_{GFF,N},
           λ ∈ [0, λ₀],   μ_{1,N} = the existing torusInteractingMeasure.
```
At `λ=0`: free GFF. At `λ=1`: pphi2's current interacting measure. Weak coupling = small `λ`.

## Design facts (settled by the prior Gemini deep-think consults — memory `pphi2-u4-proof-route`)
- **u₄(0) = 0** (free field, Isserlis: `⟨φ(f)⁴⟩ = 3⟨φ(f)²⟩²`).
- **u₄'(0) = −⟨φ(f)⁴ ; V⟩^c_free = −6 ∫(C_a f)⁴ < 0.** The single `:φ⁴:` vertex with all four external
  legs `C_a f`; `κ = 4!·(1/4) = 6` (the `1/n` quartic coefficient). **Wick-ordering-invariant** (all
  legs external ⟹ no tadpole subtraction touches it). Strictly negative; `∫(C_a f)⁴ > 0` by Schur/
  positivity (step II).
- **u₄(λ) = −6λ∫(C_a f)⁴ + R(λ), |R(λ)| ≤ Kλ² uniformly in N** — a **one-sided Taylor** bound (NOT
  analyticity; Dyson). At **fixed volume L this needs only Nelson hypercontractivity, no cluster
  expansion**. So for `λ < λ₀(L,f)`, `u₄(μ_{λ,N}) ≤ −3λ∫(C_a f)⁴ < 0` uniformly in `N`.
- No sign subtlety at O(λ): unlike `S₂` (where the Wick counterterm `−6cφ²` flips the direction),
  the O(λ) connected 4-point is counterterm-insensitive.

## Step structure (revised for the λ-family)
- [ ] **C0. Define the λ-family** — `interactionFunctionalScaled`/the scaled lattice & torus measures,
  `Z_{λ,N}`. Key economy: for `λ ∈ [0,1]`, `|λ·V| ≤ |V|`, so the existing Nelson / tightness / moment
  / `density_transfer` bounds carry the extra `λ` **with the same proofs** (uniform in `λ` too).
  ⇒ reuse, don't re-derive. (Codex design pass pending — will pin the cleanest injection point.)
- [ ] **C1. λ-family limit exists** — `torusInteractingLimit_exists` analogue at small `λ` (tightness
  is *easier* at smaller `λ`; should generalize trivially).
- [ ] **I. u₄'(0) = −6∫(C_a f)⁴** — differentiate `⟨A⟩_{μ_λ} = Z_λ⁻¹∫A e^{−λV}dμ_GFF` at `λ=0`
  (`d/dλ⟨A⟩|₀ = −⟨A;V⟩^c_free`), Wick on the free GFF for the connected 5-correlator. Either
  differentiation-under-integral (Mathlib `hasDerivAt_integral_of_dominated…`, domination uniform via
  Nelson) or a finite-difference/Taylor-with-remainder formulation (TBD — Gemini Q2/Codex).
- [ ] **II. ∫(C_a f)⁴ > 0** for `f ≠ 0` (positivity of a 4th power; `C_a f ≠ 0` from `C_a` pos-def). ★
- [ ] **III. Uniform remainder** `|R(λ)| ≤ Kλ²` — bound `u₄''(λ)` (higher truncated correlators
  `⟨φ(f)⁴;V;V⟩_λ`) uniformly in `λ∈[0,λ₀]` and `N` via Hölder + Nelson; needs uniform `⟨V^k⟩`,
  `Z_λ ≥ c > 0`, uniform high `φ(f)` moments (have, IV.a-style). **The crux** (★★★).
- [ ] **V. Assemble** — `u₄(μ_{λ,N}) ≤ −c < 0` uniform ⟹ (step IV `torus_connectedFourPoint_tendsto`)
  `u₄(μ_λ) ≤ −c < 0` ⟹ `TorusIsInteractingStrict μ_λ` ⟹ `TorusIsInteracting μ_λ`.

## Open design questions (dual pass in progress)
- Gemini deep-think (timed out twice — prior consults cover the math; retry tight if needed): the
  cleanest **remainder** formulation (uniform `u₄''` Taylor vs differentiation-under-integral) and
  the minimal uniform-bound set.
- **Codex (running):** the Lean-implementation design — where to inject `λ`, which existing lemmas
  generalize to carry `λ∈[0,λ₀]` unchanged, differentiation-under-integral vs Taylor in Mathlib,
  whether to parameterize the existing functional by `λ` to avoid re-deriving infra. **Fold in when
  it returns.**

## Honest scope
Still a substantial subproject (C0/C1 plumbing + the I/III analytic core), but (c) makes I a *clean
λ-derivative* and III a *standard Taylor-remainder* (vs. the messier large-mass expansion of the
fixed-coupling measure). Step IV (done) means the continuum transfer is free.
