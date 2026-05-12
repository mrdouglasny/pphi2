# Canonical 2-site Wick formula → S3 discharge — implementation plan

## Goal

Discharge the `sorry` in `canonicalCrossTerm_inner_eq_zero` at
`Pphi2/NelsonEstimate/RoughErrorBound.lean:407`:

```lean
lemma canonicalCrossTerm_inner_eq_zero
    (T : ℝ) (k j k' j' : ℕ) (_h : (k, j) ≠ (k', j')) :
    ∫ η, canonicalCrossTerm d N a mass T η k j *
         canonicalCrossTerm d N a mass T η k' j'
         ∂(canonicalJointMeasure d N) = 0 := by sorry
```

This is the S3 cross-term orthogonality, the analytical input that
`canonicalRoughError_l2_sq_eq` (the full L²-sq decomposition) consumes.

## Variance identification prerequisite — DONE (2026-05-12, commit `028584d`)

`FieldDecomposition.lean` now proves the on-site variance
identification lemmas axiom-free (Route B from
`canonical-variance-identification-discharge-plan.md` —
operator/Schwinger route via translation-invariant heat-kernel
diagonal + spectral trace):

1. ✅ `canonicalSmoothFieldFunction_self_moment_const` — smooth on-site
   variance is x-independent.
2. ✅ `canonicalSmoothFieldFunction_self_moment_eq_smoothWickConstant` —
   matches `smoothWickConstant d N a mass T`.
3. ✅ `canonicalRoughFieldFunction_self_moment_eq_roughWickConstant` —
   rough analogue.

(All four `#print axioms` to `[propext, Classical.choice, Quot.sound]`.)

So the canonical-side Wick monomials `wickMonomial j (smoothWickConstant T)
(canonicalSmoothFieldFunction η x)` now have **matched** Wick subtractions:
the value of `smoothWickConstant T` is the actual variance of
`canonicalSmoothFieldFunction η x`. The Janson 2-site formula applies
in its standard "diagonal Kronecker × n! × covariance^n" form.

This unblocks the S3 plan paths below.

## Why the gff lemma doesn't directly apply

`gaussian-field`'s `gff_wickPower_two_site_inner` (just proved, axiom-free) gives
the Janson–Hilbert 2-site formula for **the lattice GFF measure**:

```
∫ ω, wickMonomial n (gffSiteVariance x) (ω(δ_x)) *
     wickMonomial m (gffSiteVariance y) (ω(δ_y))
   ∂(latticeGaussianMeasure d N a mass ha hmass) =
 if n = m then n! * gffPositionCovariance(x, y)^n else 0
```

But `canonicalCrossTerm` is a function on `CanonicalJoint d N`, integrated
against `canonicalJointMeasure d N` — which is
`Measure.prod (Measure.pi gaussianReal 0 1) (Measure.pi gaussianReal 0 1)`,
**not** the lattice GFF measure. The smooth-/rough-field functions
`canonicalSmoothFieldFunction` and `canonicalRoughFieldFunction` are
linear combinations of the standard Gaussian coordinates `η.1`, `η.2`,
not GFF distributional evaluations `ω(δ_x)`.

We need a Janson 2-site formula adapted to the canonical setup.

## Three paths to S3

### Path A: Canonical-side stubs (fastest, defers the analytics)

Add **two new sorry'd lemmas** in pphi2 stating the analogous Janson
formulas for the canonical smooth and rough field functions:

```lean
lemma canonicalSmoothWickPower_two_site_inner
    (T : ℝ) (n m : ℕ) (x y : FinLatticeSites d N) :
    ∫ η_S : (Fin d → Fin N) → ℝ,
      wickMonomial n (smoothWickConstant d N a mass T)
        (canonicalSmoothFieldFunctionOfFst d N a mass T η_S x) *
      wickMonomial m (smoothWickConstant d N a mass T)
        (canonicalSmoothFieldFunctionOfFst d N a mass T η_S y)
      ∂(Measure.pi (fun _ : Fin d → Fin N => gaussianReal 0 1)) =
    if n = m then
      (n.factorial : ℝ) * (canonicalSmoothCovariance d N a mass T x y) ^ n
    else 0 := sorry

lemma canonicalRoughWickPower_two_site_inner
    (T : ℝ) (n m : ℕ) (x y : FinLatticeSites d N) :
    -- analogous, with rough field/covariance/Wick constant
    ... := sorry
```

Auxiliary defs:

```lean
noncomputable def canonicalSmoothFieldFunctionOfFst
    (d N : ℕ) [NeZero N] (a mass T : ℝ)
    (η_S : (Fin d → Fin N) → ℝ) (x : FinLatticeSites d N) : ℝ :=
  (Real.sqrt (a^d))⁻¹ * ∑ m, canonicalSmoothModeCoeff d N a mass T x m * η_S m

-- (and the rough counterpart)

noncomputable def canonicalSmoothCovariance (T : ℝ)
    (x y : FinLatticeSites d N) : ℝ :=
  ∑ m, canonicalSmoothModeCoeff d N a mass T x m *
       canonicalSmoothModeCoeff d N a mass T y m / latticeFourierProductNormSq N d m
  -- (or the equivalent in the smooth eigen-weight form)
```

Then **discharge `canonicalCrossTerm_inner_eq_zero`** by:
1. Square out: `cross(k, j) · cross(k', j') = a^{2d} · Σ_{x,y} smooth_j(x) · rough_{k-j}(x) · smooth_{j'}(y) · rough_{k'-j'}(y)`.
2. Apply `MeasureTheory.integral_prod_mul` (or `integral_fun_fst`,
   the in-repo pattern at `FieldDecomposition.lean:487`) to factorise
   each summand: smooth × rough → integral over μ_S × integral over μ_R.
3. Apply the two new lemmas; both sides give `if n = m then ... else 0`.
4. If `(k, j) ≠ (k', j')`, then either `j ≠ j'` (smooth side vanishes)
   or `k - j ≠ k' - j'` (rough side vanishes), so each summand is 0
   and the integral is 0.

Net effect: trades 1 pphi2 sorry (`canonicalCrossTerm_inner_eq_zero`)
for 2 cleaner sorries (the canonical-side 2-site formulas). The new
sorries are at the right granularity for either Path B or Path C
to discharge them, and they have axiom-free *statements* (no new
upstream axioms).

### Path B: Generalise the gff lemma (cleanest architecturally) — IN PROGRESS

**Status (2026-05-12):** primitives ready; the abstract Janson formula
itself is the next concrete chunk for Codex.

✅ `multiWickMonomial_pi_gaussianReal_inner` — landed in gaussian-field
at commit `269fbc2`, axiom-free. Direct multivariate Wick orthogonality
on `Π_j gaussianReal`:
```
∫ ∏_j :ξ_j^{α_j}:_1 · ∏_j :ξ_j^{β_j}:_1 ∂(Π_j gaussianReal 0 1)
  = δ_{α, β} · ∏_j α_j!
```

⬜ `janson_two_site_wick_power_inner` — to be added in
`gaussian-field/GaussianField/WickMultivariate.lean`. Statement:

```lean
theorem janson_two_site_wick_power_inner
    {ι : Type*} [Fintype ι]
    (γ_x γ_y : ι → ℝ) (n m : ℕ) :
    ∫ ξ : ι → ℝ,
      wickMonomial n (∑ j, (γ_x j)^2) (∑ j, γ_x j * ξ j) *
      wickMonomial m (∑ j, (γ_y j)^2) (∑ j, γ_y j * ξ j)
      ∂(Measure.pi (fun _ : ι => gaussianReal 0 1)) =
    if n = m then
      (n.factorial : ℝ) * (∑ j, γ_x j * γ_y j) ^ n
    else 0
```

This is the **abstract Janson formula**: applies to any Gaussian linear
functional in standard product Gaussians. The proof is the same
structure as `gff_wickPower_two_site_inner` (eigenbasis expansion +
`hermiteMulti_orthogonality` from gaussian-hilbert + multinomial
theorem), but without the GFF-specific machinery.

`gff_wickPower_two_site_inner` becomes a corollary:
- specialise with `γ_x j := gffEigenCoeff j x`, `γ_y j := gffEigenCoeff j y`
- use the GFF pushforward (`gffOrthonormalProj_pushforward_eq_stdGaussian`)
  to convert from `latticeGaussianMeasure` to `Measure.pi gaussianReal`

The two canonical-side formulas (Path A's sorries) become direct
specialisations.

This is the cleanest architectural fix: one generic lemma in
gaussian-field, three specialisations downstream. **Recommended path
for Codex, after the variance-identification prerequisite above is in
place.**

### Path C: Smooth-/rough-only-GFF pushforward identification

Construct a "smooth-only GFF" measure on `Configuration` whose
covariance is the smooth covariance (not the full GFF covariance), and
prove that its `gffOrthonormalProj` pushforward equals `Measure.pi
gaussianReal`. Apply `gff_wickPower_two_site_inner` to this
smooth-only-GFF and identify with `canonicalSmoothFieldFunction` via
the pushforward.

Cleaner conceptually but requires building the smooth-only-GFF from
scratch, which is more upstream work than Paths A or B. Probably
not worth it given Path B is straightforward.

## Recommendation

**Codex hand-off: Path B** in gaussian-field, then specialise twice
in pphi2.

1. **gaussian-field PR**: add `janson_two_site_wick_power_inner` (the
   abstract version) in `GaussianField/WickMultivariate.lean`; refactor
   `gff_wickPower_two_site_inner` as a corollary if convenient (or just
   add the abstract one and leave the GFF one as-is). Same proof
   structure as the existing GFF lemma, ~150-250 lines.

2. **pphi2 PR**: bump the gaussian-field pin, add the two
   canonical-side specialisations
   (`canonicalSmoothWickPower_two_site_inner` and the rough analogue,
   both ~10-line corollaries of the abstract formula), and use them +
   `MeasureTheory.integral_prod_mul` to discharge
   `canonicalCrossTerm_inner_eq_zero`.

This path keeps every step axiom-free: the abstract Janson formula is
provable by the same eigenbasis technique already used in the GFF
case; the canonical specialisations are immediate; the S3 discharge is
mechanical.

## Acceptance criteria

For the gaussian-field PR:
- `lake build` clean.
- `#print axioms janson_two_site_wick_power_inner` shows
  `[propext, Classical.choice, Quot.sound]`.
- `#print axioms gff_wickPower_two_site_inner` unchanged
  (still axiom-free).

For the pphi2 PR (after pin bump):
- `lake build` clean.
- `canonicalCrossTerm_inner_eq_zero` proved (no sorry).
- pphi2 sorry count drops by 1 (from 3 to 2).
- The remaining sorries are `canonicalCrossTerm_l2_sq_le` (S4, needs
  the diagonal piece + Glimm-Jaffe Phase B) and `rough_error_variance`
  (S5 assembly).
