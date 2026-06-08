# L5(ii) + L6F — the affine derivative bound and the final discharge

> ✅/⛔ **STATUS (2026-06-07): L5 complete and CONSUMED by Route A; the L6F endgame is SUBSUMED.**
> `lattice_u4_neg_uniform` (the L5 deliverable) is proved and is now the engine Route A reuses to
> prove T² non-Gaussianity **axiom-free** (`torus_pphi2_isInteractingStrict_weakCoupling`). Route A
> bypassed the L6F large-mass endgame entirely (coupling-family continuum limit + 4-homogeneity), so
> the "final discharge" planned here is no longer the path. See `route-A-weak-coupling-plan.md` and
> `L6F-mass-coupling-plan.md` (subsumed banner). Kept for the L5 derivation record.

After L1 + L2-for-V + **L3** (all axiom-clean, PR #46), the remaining wall. The consumer is
`exists_uniform_neg_of_uniform_affine_bound'` (`UniformBounds.lean`), which for `φ_N = u₄_N` needs,
with `s, K, g₀` **uniform in `N`**:

| Leaf | Statement | Status |
|------|-----------|--------|
| `h0` | `u₄_N(0) = 0` | ✅ `u4_at_zero` |
| `hcont` | `ContinuousOn u₄_N [0,g₀]` | ✅ `u4_continuousOn` |
| `hderiv` | `HasDerivAt u₄_N (deriv u₄_N t) t` on `(0,g₀)` | ✅ `u4_differentiableAt` (.hasDerivAt) |
| `hbound` | `deriv u₄_N t ≤ -s + K·t` on `(0,g₀)`, **uniform** | ⬜ **L5(ii)** |

So the ONLY remaining analytic content is `hbound`. NB `deriv u₄_N t` from `u4_differentiableAt`
is *abstract* (`DifferentiableAt.deriv`), so `hbound` first needs a **closed form** for `u₄'(t)`.

## STATUS (branch `l5-affine-bound`)

Done + axiom-clean this branch:
- `normalizedMoment_hasDerivAt` (L5a interior quotient rule), `partitionFn_hasDerivAt2` (Z'').
- `abs_interacting_moment_le` (`|⟨X⟩_t| ≤ ‖X‖_{L²}√K`), `memLp_pairing_pow_mul_interaction_pow`
  (`(ωf)ⁿVᵇ ∈ L²`) — the per-moment bound bricks.
- **Closed forms `u4`, `u4Deriv`, `u4Deriv2`** (defs) + `u4_hasDerivAt`, `u4_hasDerivAt2` — `u₄ ∈ C²`
  at interior `t` with explicit `u₄' = m₄'−6m₂m₂'`, `u₄'' = m₄''−6(m₂'²+m₂m₂'')`. `u4` unfolds
  definitionally to the discharge's `M₄/Z−3(M₂/Z)²`.

**L5c DONE** (`U4SecondDerivBound.lean`, all axiom-clean): `ratio_l2_bound` (workhorse),
`normalizedMoment_abs_le`, `normalizedMomentDeriv_abs_le`, `normalizedMomentDeriv2_abs_le`, and
**`u4Deriv2_abs_le_uniform`** — `|u₄''(g)| ≤ K` uniform in `N`, `g∈[0,1]`. Technique: decompose each
`m_n^{(k)}` at the *atom* level (`unfold; field_simp` with Gibbs defs as opaque atoms, never exposing
`exp` args to `ring`), bound each Gibbs ratio via `ratio_l2_bound` + L3 + Nelson.

`torusConnectedFourPoint_eq_lattice` (`TorusU4Pullback.lean`) — the L6F torus→lattice pull-back, done.

## L5(ii) brick sequence (the slog)

Notation: `m_n(t) = ⟨(ωf)ⁿ⟩_t = M_n(t)/Z(t)`, `M_n(t) = ∫(ωf)ⁿe^{-tV}dμ_GFF`, `Z(t)=∫e^{-tV}`.
`u₄(t) = m₄(t) − 3 m₂(t)²`. Free interacting moment of an observable `X`:
`⟨X⟩_t = (∫ X e^{-tV})/Z(t)`.

- **L5a — closed-form `u₄'(t)`.** General-`t` analog of `normalizedMoment_hasDerivWithinAt`
  (currently only `g=0`). Via `moment_hasDerivAt` (`M_n'(t) = -∫(ωf)ⁿVe^{-tV}`) and
  `partitionFn_hasDerivAt` (`Z'(t) = -∫Ve^{-tV}`), the quotient rule gives
  `m_n'(t) = -⟨(ωf)ⁿV⟩_t + ⟨(ωf)ⁿ⟩_t⟨V⟩_t = -Cov_t((ωf)ⁿ, V)` (connected).
  Then `u₄'(t) = m₄'(t) − 6 m₂(t) m₂'(t)`. Establish `deriv u₄_N t = ` this expression
  (`HasDerivAt.deriv` on the `u4_differentiableAt` witness, matched to the product/quotient rule).
  ~150–250 lines; mechanical but large.

- **L5b — `u₄''(t)` closed form + `C²`.** Differentiate `u₄'(t)` again (using `moment_hasDerivAt2`,
  `M_n''(t) = ∫(ωf)ⁿV²e^{-tV}`, plus product rule). `u₄''(t)` is a rational expression in the
  unnormalised moments `∫(ωf)^a V^b e^{-tV}` (a≤4, b≤2) and `Z(t)`. Foundation: `moment_hasDerivAt2`
  ✅ (done).

- **L5c — uniform bound `u₄''(t) ≤ K`.** Each normalised moment `⟨(ωf)^a V^b⟩_t` (a≤4, b≤2) is
  bounded uniformly in `N` and `t∈[0,g₀]` by **L4∘L3**:
  `⟨|(ωf)^a V^b|⟩_t ≤ ‖(ωf)^a V^b‖_{L²(μ_GFF)}·√K_Nelson` (`interacting_moment_le_L2_of_expBound`),
  and `‖(ωf)^a V^b‖²_{L²} = ∫(ωf)^{2a}V^{2b}dμ_GFF ≤ K₀` (`torus_free_product_moment_uniform`,
  b≥1; `torus_normConst_field_moment_uniform` for b=0). `Z(t) ≥ 1` (`partitionFn_ge_one`) keeps the
  denominators controlled. Assemble: finitely many uniformly-bounded moments ⟹ `u₄''(t) ≤ K`
  uniform. The largest single assembly in the project.

- **L5d — affine bound from `C²`.** `u₄'(t) = u₄'(0) + ∫₀ᵗ u₄''(r)dr ≤ u₄'(0) + K·t`. With
  `u₄'(0) = -6a^d∑(C_af)⁴ = -s` (`u4_hasDerivWithinAt`; `s` uniform via `leadingTerm_const_eq` =
  `(L^{3d}m⁸)⁻¹`), this is exactly `deriv u₄_N t ≤ -s + K·t`. (Alternatively bound
  `u₄'(t) - u₄'(0) ≤ K·t` directly via MVT on `u₄'` + `u₄'' ≤ K`.)

## L6F — final discharge (once the affine bound lands)

Remaining bricks (the affine bound itself + the framing):
1. **Affine bound** `deriv u₄ t ≤ -s + K·t` on `(0,g₀)`: from `u4_hasDerivAt2` (u₄'') + the uniform
   `u4Deriv2_abs_le_uniform` (|u₄''|≤K) via MVT/FTC on `u4Deriv`, plus `u4Deriv(0⁺) = -s` (connect
   the interior `u4Deriv` to the within-derivative `u4_hasDerivWithinAt` value `-6a²∑(C_af)⁴`).
2. `exists_uniform_neg_of_uniform_affine_bound'` with `s` (`leadingTerm_const_eq`, uniform `(L^{3d}m⁸)⁻¹`),
   `K`, `g₀` ⟹ `∃ g c>0, ∀N, u₄_N(g) ≤ -c`. (`h0`/`hcont`/`hderiv` = `u4_at_zero`/`u4_continuousOn`/
   `u4_differentiableAt`, all done.)
3. **Torus framing.** `torusConnectedFourPoint L (torusInteractingMeasure L N P mass hmass) f`
   `= connectedFourPoint (interactingLatticeMeasure ..) (latticeTestFn f)` via `torusEmbedLift`
   pushforward (`torusInteractingMeasure = map torusEmbedLift (interactingLatticeMeasure)`; mirror the
   second-moment pullback in `TorusInteractingMoments`). `connectedFourPoint(interactingLatticeMeasure)
   = u4(..g=1)`.
4. **mass ↔ g via field redefinition.** `connectedFourPoint_interactingMeasure_field_rescale`
   (`FieldRedefinition.lean`): `u₄` scales by `c⁴` under `ω↦c•ω`, and rescaling the free measure
   changes the mass (covariance `×c²`). So the mass-`m`/g=1 theory ≡ a reference theory at weak
   coupling `g(m)→0` as `m→∞`; `mass>m₀ ⟺ g<g₀`. Set `m₀` from `g₀` ⟹
   `torus_weakCoupling_lattice_connectedFourPoint_strictNeg`
   ⟹ `torus_pphi2_isInteracting_weakCoupling` axiom-free.

HONEST SCOPE: L5(ii) is several focused sessions (L5a closed form + L5c the big moment assembly are
the bulk). L6F is short once `s` and `K` are in hand. All the analytic inputs (L1, L2-for-V, L3, L4,
Nelson, leading term) are now proven and axiom-clean — L5 is *assembly + differentiation calculus*,
not new hard analysis.
