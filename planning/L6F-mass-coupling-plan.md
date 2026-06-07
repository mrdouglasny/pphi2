# L6F endgame — the mass↔g field redefinition (the last step of the discharge)

Branch `l5-affine-bound`. After L3 + L5 + the L6F **reduction**, the headline axiom
`torus_weakCoupling_lattice_connectedFourPoint_strictNeg` reduces (axiom-clean) to a single
inequality in the `u4` machinery. This doc plans the one remaining step.

## What is already proven (axiom-clean)

`torusConnectedFourPoint_eq_u4_one` (`TorusU4Pullback.lean`):
```
torusConnectedFourPoint L (torusInteractingMeasure L N P mass hmass) f
  = u4 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass P (latticeTestFn L N f) 1
```
So the discharge is equivalent to
```
(★)  ∃ m₀ > 0, ∀ mass > m₀, ∃ (f : TorusTestFunction L) (c : ℝ), 0 < c ∧
       ∀ N [NeZero N], u4 2 N (circleSpacing L N) mass … P (latticeTestFn L N f) 1 ≤ -c.
```

`lattice_u4_neg_uniform` (`U4AffineBound.lean`) gives, for the normalised-constant test function `f_c`:
```
∃ g c > 0, ∀ N, u4 2 N (circleSpacing L N) mass … P f_c g ≤ -c       (at the SMALL coupling g₀, FIXED mass)
```
where `g₀ = min 1 (s/(2K))`, `s = 6(L⁶m⁸)⁻¹` (uniform leading slope, `leadingTerm_const_eq` +
`torus_volume_eq`), `K` the uniform `|u₄''|` bound (`u4Deriv2_abs_le_uniform`).

**The gap:** (★) needs `u4` at the FULL coupling `g=1` and LARGE mass; `lattice_u4_neg_uniform`
delivers it at a SMALL coupling `g₀` and fixed mass. Bridging the two is the mass↔g field
redefinition.

## The physics: `g = 1/(4 mass²)`

For the fixed quartic `P`, the dimensionless coupling is `g ~ λ/mass²`. Large `mass` ⟺ small
effective coupling. The field rescaling `ω ↦ c•ω` (`c = mass`, say) normalises the GFF mass to a
reference value and rescales the interaction, exhibiting `u₄(g=1, mass) = c⁴ · u₄(g(mass), ref)` with
`g(mass) = 1/(4 mass²)`. Then `mass > m₀ := 1/(2√g₀)` ⟹ `g(mass) < g₀`, and the reference theory's
`u₄(g(mass)) < 0` (from `lattice_u4_neg_uniform`-style negativity, applied at the reference) gives
`u₄(g=1, mass) < 0`.

## The two missing ingredients

### (I) Field-rescale ⟹ covariance/mass identity  — **deferred / axiom-candidate**
```
map (fun ω => c • ω) (GaussianField.measure T) = GaussianField.measure (c • T)        (c ≠ 0)
```
i.e. rescaling the field scales the covariance operator by `c` (variance by `c²`). This is the
infinite-dimensional Gaussian-measure fact flagged **deferred** in `FieldRedefinition.lean:74-76`
("needs Cramér–Wold/Minlos uniqueness on `Configuration`; only available post-pushforward-to-ℝ;
possibly to be added as an axiom"). The moment-level consequence `connectedFourPoint` scales by `c⁴`
is already proved (`connectedFourPoint_map_const_smul`,
`connectedFourPoint_interactingMeasure_field_rescale`); what is missing is the **measure** identity
that ties the rescaled free measure to a different *mass*.

- **Route A (axiom):** add (I) as a vetted textbook axiom (standard Gaussian measure theory: the law
  of `c·X` is centered Gaussian with covariance `c²·Cov(X)`; cite Bogachev *Gaussian Measures* /
  Glimm–Jaffe). **Introducing an axiom is a needs-human decision** (axiom-management protocol).
  Then `AXIOM_AUDIT.md` + vetting (`deep_think_gemini` type-correctness/non-vacuity) per protocol.
- **Route B (prove it):** push the rescaling through the characteristic functional and use the
  existing Minlos/Cramér–Wold machinery (`gaussian-field` package). Larger; the project deliberately
  deferred this.

### (II) Dimensional scaling of the lattice GFF and the Wick interaction
To turn (I) into `g = 1/(4 mass²)` concretely on the lattice one needs:
- `latticeCovarianceGJ d N a mass` mass-scaling: how the covariance operator depends on `mass`
  (`≈ (−Δ_a + mass²)⁻¹` up to the sqrt convention; cf. the precision-inverts-covariance lemmas in
  `LeadingTerm.lean`). Identify the `c = c(mass)` that maps `mass` to a reference `mass₀`.
- `interactionFunctional d N P a mass` (Wick-ordered) under `ω ↦ c⁻¹•ω`: the Wick constant
  `wickConstant d N a mass` is mass-dependent (log-divergent in the continuum); track how `V`
  transforms, yielding the effective coupling `g(mass)`.

## Assembly once (I)+(II) are in hand
```
1.  c := c(mass), reference mass₀; (I) gives map (c•·) μ_{GFF,mass} = μ_{GFF,mass₀}.
2.  connectedFourPoint_interactingMeasure_field_rescale ⟹
      u4(g=1, mass) = c⁴ · u4(g(mass), mass₀)   with g(mass) = 1/(4 mass²).
3.  m₀ := 1/(2√g₀); mass > m₀ ⟹ g(mass) < g₀.
4.  lattice_u4_neg_uniform (at mass₀, applied at coupling g(mass) < g₀ via monotonicity of the
      affine bound, or re-run deriv_affine_bound at g(mass)) ⟹ u4(g(mass), mass₀) ≤ -c'.
5.  c⁴ > 0 ⟹ u4(g=1, mass) ≤ -c⁴ c' =: -c < 0, uniform in N.
6.  torusConnectedFourPoint_eq_u4_one + (★) ⟹ discharge.
```

Note step 4: `lattice_u4_neg_uniform` currently fixes `g₀ = min 1 (s/2K)`; to use it at an arbitrary
small `g < g₀` (here `g(mass)`), generalise it to `deriv_affine_bound_neg_of_continuousOn` evaluated
at the chosen `g` (all hypotheses — `u4_at_zero`, `u4_continuousOn`, `u4_hasDerivAt`, the affine
bound `hbound`, `hKg : K·g ≤ s/2`) already hold for any `g ≤ s/(2K)`.

## Honest scope
(I) is the crux and is a *standard* but infinite-dimensional Gaussian fact (deferred by design).
(II) is concrete dimensional analysis on the lattice covariance + Wick constant — a few focused days.
Everything else (the entire perturbative analysis L3+L5 and the L6F reduction) is proven and
axiom-clean. Recommended: Route A (vetted axiom for (I)) + (II), gated on a human OK for the axiom.
