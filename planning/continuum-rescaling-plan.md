# Continuum rescaling-equivalence route to φ⁴₂ non-triviality

> ℹ️ **STATUS (2026-06-07): PROPOSED ALTERNATIVE, docs-only — not started.** This is route 2 of two
> *competing* routes to axiom 9 (`torus_weakCoupling_lattice_connectedFourPoint_strictNeg`, u₄ < 0).
> The **live** route with actual Lean code is route 1, the lattice affine-bound discharge on branch
> `l5-affine-bound` (L5 complete, L6F reduction). This continuum route is Gemini-vetted SOUND (below)
> but has no implementation. Don't pursue both — see [`../BRANCHES.md`](../BRANCHES.md) for the
> route-1-vs-route-2 decision.

A replacement for the lattice "mass-grade ∫V²" endgame (which is entangled with the 2D UV/log
divergence). Idea: the rescaling that **fails on the lattice** (`−Δ_a` is not scale-covariant) is
**clean in the continuum** (in 2D `φ` is dimensionless and `−Δ` is exactly scale-covariant). So prove
the equivalence in the continuum and use the lattice only to *construct* the continuum measures.

## Target
Axiom-free: the continuum φ⁴₂ theory on `T²` is non-Gaussian (`u₄ ≠ 0`) at the physical point
(`λ = 1`, large mass), via
- **(A)** a continuum-limit theorem for the family `μ_{λ,m,L₁,L₂}`,
- **(B)** a continuum **rescaling-equivalence** lemma relating different parameter points,
- **(C)** **weak-coupling `u₄ < 0`** (the engine already built),
with **(B)+(C) ⟹ physical `u₄ < 0`**.

## The equivalence (2D continuum)
Action `∫_{T²_L}[½(∇φ)² + ½ m²φ² + λ:φ⁴:]`. Mass dims `[φ]=0, [m²]=2, [λ]=2`. Two generators:
- **Dilation** `x ↦ x/s`: kinetic term invariant (2D), `m² ↦ s²m²`, `λ ↦ s²λ`, `L_i ↦ L_i/s`.
- **Field rescale** `φ ↦ cφ`: covariance `↦ c²·cov`, `u₄ ↦ c⁴·u₄`
  (`connectedFourPoint_map_const_smul`, proven), trades against `λ`.

Dimensionless invariants: `mL`, `λ/m²`, aspect ratio `L₁/L₂`. The physical point `(λ=1, m, L)` (large
`m`) has `λ/m² = 1/m²` small; dilating by `s = 1/m` gives
```
(λ=1, m, L)  ≅  (λ' = 1/m², m' = 1, L' = mL),     u₄(phys) = c⁴ · u₄(equiv).
```
i.e. **physical large-mass ≅ weak-coupling (`λ' = 1/m² → 0`) at unit mass on a torus `L' = mL`.**

## Bricks
1. **Family continuum construction** `μ_{λ,m,L₁,L₂}`: existence (subsequential limit), tightness,
   and 4-point convergence — generalize the existing `λ=1` machinery (`torusInteractingMeasure`,
   `torusInteractingLimit_exists`, `torus_connectedFourPoint_tendsto`) to general `λ` and two side
   lengths. (Nelson/tightness inputs look `λ`-uniform.)
2. **Continuum rescaling-equivalence lemma** for `u₄` (the genuinely new piece):
   `u₄(μ_{λ,m,L}; f) = c⁴ · u₄(μ_{λ',m',L'}; f∘dilation)`.
   - field-rescale half: `connectedFourPoint_map_const_smul` (proven) + the continuum pushforward
     `map (c•) μ_cont = μ_{c²·cov}` (Minlos/Cramér–Wold — the package has `CramerWold`,
     `Measure.ext_of_charFunDual`).
   - dilation half: torus diffeomorphism `x↦x/s` induces a configuration pushforward; equality of
     `u₄`s via the char-functional/second-moment transformation.
3. **Weak-coupling `u₄ < 0` in the continuum**: `lattice_u4_neg_uniform` (lattice `u₄(λ₀) < 0`,
   uniform in `N`) + brick 1's 4-point convergence ⟹ continuum `u₄(λ₀) < 0` for small `λ₀`.
4. **Assembly**: brick 2 maps physical `(λ=1, large m)` to the weak-coupling image; brick 3 gives the
   image `u₄ < 0`; `c⁴ > 0` ⟹ physical `u₄ < 0` ⟹ non-Gaussian.

## Already proven (the engine + supports)
`u₄'(0) = −6λ∑(C_a f)⁴ < 0`, `u₄ ∈ C²`, `|u₄''| ≤ K` uniform in `N`, affine bound ⟹ lattice
`u₄(λ₀) < 0` uniform in `N` (`lattice_u4_neg_uniform`); `λ=1` continuum 4-point convergence
(`torus_connectedFourPoint_tendsto`); field-rescale `u₄`-scaling (`connectedFourPoint_map_const_smul`);
covariance `mass⁻²` decay (`lattice_second_moment_le_mass_inv`, `gffPositionCovariance_abs_le_mass_inv`).

## VETTING VERDICT (Gemini deep-think, 2026-06): SOUND — crux resolved
- **Volume-uniformity holds via exponential clustering.** `u₄''(g) ∝ ⟨φ(f)⁴; V; V⟩_c` is *connected*;
  at the image mass `m'=1` the propagator decays `~e^{−|x−y|}`, so the two integrated vertex
  positions `z₁,z₂` are tied (by connectedness) to the fixed support of `f`. Hence
  `∫∫ dz₁dz₂ |⟨…⟩_c| = O(1)`, and `K` depends only on the support/amplitude of `f`, **independent of
  the torus volume `L'`** (once `L' >` supp `f`). Open subtlety 1 ⟹ resolved.
- **The test function transforms (the real subtlety) — and it works in our favor.** Under `x↦x/s`
  (`s=1/m`), `φ(f) = φ'(f')` with `f'(x') = m⁻²·f(x'/m)` (support area `∝ m²`, amplitude `∝ m⁻²`).
  Then **both** the slope `s'(f') ∝ (area)(amplitude)⁴ = m²·m⁻⁸ = m⁻⁶` **and** the bound
  `K'(f') ∝ m⁻⁶`. So the critical window `g'_crit = |s'|/(2K') ~ O(1)` is **constant in `m`**, while the
  actual coupling `λ' = 1/m² → 0` falls inside it for large `m`. The affine argument transports
  uniformly. Open subtlety 1 (residual) ⟹ resolved.
- **Wick ordering is covariant; the limit commutes with dilation.** `C_m(x,y) = C_{m'=1}(mx,my)`
  exactly (continuum), so `:φ⁴:_m ↦ :φ⁴:_{m'=1}` with **no** anomalous log-renormalization (we act on
  the *continuum* GFF, not the lattice). Open subtleties 2,3 ⟹ resolved.
- **Verdict:** "vastly superior to lattice mass-decay" — the continuum-scaling cleanly *factors* the
  proof into UV (lattice→continuum, already done, `N`-uniform) and IR (scaling, exact), avoiding the
  log-divergence nightmare of mass-grading `∫V²` on the lattice. No fatal gaps.

## OPEN SUBTLETIES — (now resolved by the vetting above; kept for the record)
1. **Scale-covariance of the quantitative bound / the large-torus image.** The image theory sits on
   `L' = mL → ∞` (infinite-volume direction). My lattice bound's constants `s = 6(L⁶m⁸)⁻¹`,
   `K(L,m)` are **not** dimensionless invariants; on the image (`m'=1`, `L'=mL`), a *crude* `|u₄''|`
   bound is **extensive** (`K' ~ Volume ~ (L')²`), which would break the affine condition
   `λ' ≤ s'/(2K')`. The *actual* `u₄(f)` for a fixed (compactly-supported) `f` is volume-independent
   by **clustering**, so the issue is bound-crudeness, not the truth. ⇒ The weak-coupling `u₄ < 0`
   must be stated with **volume-independent constants for a fixed test function** (exploit clustering),
   i.e. in dimensionless form depending only on `λ/m²`. Is `lattice_u4_neg_uniform` already
   `L`-uniform enough, or does it need a clustering refinement?
2. **Wick-ordering covariance.** The (renormalized) Wick subtraction must transform consistently under
   dilation + field rescale; in 2D (super-renormalizable) only the Wick constant renormalizes — check
   `:φ⁴:_{C}` ↦ `:φ⁴:_{C'}` is exactly the dilation image with no leftover.
3. **Does the continuum limit commute with rescaling?** Prove the equivalence *after* the limit (at
   the continuum measure level, where rescaling is clean) — confirm the dilation pushforward of the
   *continuum* `μ` equals the continuum `μ` of the dilated parameters (not just lattice-approximately).

## Why this is the right framing regardless
It relocates the hard step from "N-uniform mass-graded `∫V²` entangled with the 2D log-divergence"
(lattice grind, never clean) to **structural continuum scale-covariance**, and makes the proven
weak-coupling engine the load-bearing core. The main genuinely-new work is brick 2 (continuum
rescaling equivalence) and resolving open subtlety 1 (a `dimensionless`/clustering form of the
weak-coupling bound).

## REFINED ANALYSIS (2026-06-07) — the dilation is SOUND but mostly UNNECESSARY

Re-examined against the actual code + a fresh Gemini deep-think vetting. Three claims, all vetted
**Correct** (deep-think, 2026-06-07):

1. **Dilation equivalence (pure scale-covariance, `c=1` in 2D).** Define `(Uφ)(x') = φ(x'/m)`,
   `T²_L → T²_{mL}`. Then `U_* μ_{λ,m,L} = μ_{λ/m², 1, mL}` and, with `f'(x') = m⁻² f(x'/m)`,
   `u₄(μ_{λ,m,L}; f) = u₄(μ_{λ/m², 1, mL}; f')`. Crux: in `d=2` the massive propagator is *exactly*
   `C_m(x,y) = C_1(m(x−y))` (no `m^{d−2}` prefactor since `[φ]=0`), so `U_*GFF(m,L) = GFF(1,mL)`
   with **no field-strength rescale**; the `dx = m⁻²dx'` Jacobian becomes the new coupling
   `λ' = λ/m²`. Wick ordering intertwines exactly (the cutoff dilates with `U`, so the log-variance
   subtraction matches — no anomalous term). The plan's separate "field-rescale generator" is `c=1`
   here; the whole content is the dilation + the test-function transform.
2. **The `λ'_crit ~ O(1)` miracle (only needed to reach the physical `λ=1`/large-mass point).**
   Both `s(f') = 6∫(C₁f')⁴ = O(m⁻⁶)` and `K(f') = O(m⁻⁶)`, so `λ'_crit = 2s/K = O(1)` is bounded
   below uniformly in `m`, while the image coupling `λ' = 1/m² → 0` falls deep inside the window.
   `K` scaling via clustering: `|u₄''| ≤ C‖f'‖₁‖f'‖∞³` (the connected 6-point integrates to a
   *volume-independent* `C` by exponential clustering at unit mass / weak coupling), and
   `‖f'‖₁ = ‖f‖₁ = O(1)`, `‖f'‖∞ = m⁻²‖f‖∞`, so `K = O(m⁻⁶)`. Volume-independence (`L' = mL → ∞`)
   is genuine, not bound-crudeness, because of clustering.
3. **THE SHORTCUT — non-Gaussianity does NOT need the dilation at all.** "φ⁴₂ is non-Gaussian"
   only needs **one** interacting continuum measure with `u₄ ≠ 0`. We already have, rigorously and
   `N`-uniformly, the lattice weak-coupling negativity `lattice_u4_neg_uniform` (`u₄(μ_g) ≤ −c` for
   a small coupling `g > 0`, `μ_g ∝ e^{−gV}`, on `l5-affine-bound`). With a lattice→continuum
   4-point convergence for the `g`-family, the continuum `μ_{g, m, L}` (small `g`, **fixed** mass
   and box) has `u₄ < 0` and is a legitimate interacting φ⁴₂ theory. Deep-think: this is a complete,
   honest proof of non-triviality, mathematically on the same footing as the `λ=1` statement (they
   are the *same measure* in different coordinates, super-renormalizable ⟹ `Z=1`, single
   dimensionless parameter `g/m²`). **The dilation is needed ONLY to additionally phrase the result
   at the conventional `λ=1` / large-mass normalization.**

### The obstacle that makes this a real fork (not a free win)
`InteractionPolynomial` hard-codes the leading coefficient `a_n = 1/n` (= 1/4 for φ⁴) — there is
**no free `λ` in `P`**. That is *why* the current axiom
`torus_weakCoupling_lattice_connectedFourPoint_strictNeg` and the headline
`torus_pphi2_isInteracting_weakCoupling` are phrased over **`mass`** (`∀ mass > m₀`): with `λ` pinned
at `1/4`, weak dimensionless coupling `g = λ/m² = 1/(4m²)` is reachable only via large mass. The
free coupling knob that `lattice_u4_neg_uniform` actually uses is the **coupling family** parameter
`g` in `μ_g ∝ e^{−gV}` (separate from `P`). So:

### Two routes — a project-intent decision (the headline statement differs)
- **Route A (cheap, reuses proven work).** Re-state the discharge over the coupling family: build the
  continuum limit of `μ_{g₀}` (small `g₀`, fixed mass/box) and exhibit `u₄ < 0` from
  `lattice_u4_neg_uniform` + a `g`-family 4-point convergence. **No dilation, no Wick-covariance, no
  `K`-miracle.** Cost: generalize `torusInteractingMeasure`/`torusInteractingLimit_exists` to carry a
  coupling `g ≤ 1` (the Nelson/tightness inputs are *easier* at `g < 1`), and re-phrase the axiom +
  headline from `∀ mass > m₀` to `∃ g₀ > 0` (small coupling). Discharges non-Gaussianity outright.
  **Changes the theorem statement** (weak coupling at fixed mass, not large mass) — needs the owner's
  OK, but it is the standard non-triviality statement.
- **Route B (full, keeps the current statement).** Formalize the continuum dilation equivalence
  (claims 1–2) to bridge the proven weak-coupling `u₄ < 0` to the `λ=1`/large-mass axiom *as
  currently stated*. Mathematically sound (vetted) but multi-week: configuration pushforward between
  *different* tori `T²_L → T²_{mL}`, Wick-ordering covariance, the clustering `K = O(m⁻⁶)` bound, and
  the `μ_{λ,m,L}` family construction. Also yields the structural `(λ,m,L)`-equivalence as a result.

**Recommendation:** Route A for discharging non-Gaussianity (cheapest, honest, reuses the proven
engine); treat Route B / the dilation equivalence as an optional structural enrichment pursued
separately if the `λ=1` normalization or the full `(λ,m,L)` equivalence is wanted for its own sake.
The owner decides whether the headline may be re-stated at weak coupling (Route A) or must stay at
large mass / `λ=1` (Route B).
