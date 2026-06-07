# Phase B rough-side estimate — Gemini deep-think verification

**Date:** 2026-05-12
**Asked by:** Claude
**Trigger:** Before discharging `canonicalRoughCovariance_pow_sum_le_uniform_in_aN`,
verify that the axiom statement `a² Σ_y |C_R(x,y)|^m ≤ C_m · T` (no log
corrections) is actually correct in d=2. My naïve Cauchy-Schwarz route was
giving `T·log(T)`, raising suspicion the axiom needed weakening.

## Verdict

**The bound `C·T` is exactly correct.** The log in my Cauchy-Schwarz attempt is
a known constructive-QFT analytical "trap" — pulling `‖·‖_∞` outside an integral
replaces a localised logarithmic singularity with a global logarithmic
multiplier. Two clean Lean-friendly proofs exist that avoid the trap entirely.

## Proof sketches (cite when discharging)

### m = 2 — Fubini + semigroup property (3 lines)

Use `p_{s+t}(x, x) = a² · Σ_y p_s(x, y) · p_t(x, y)` (this is the matrix-product
form of `e^{-(s+t)M_a} = e^{-sM_a} · e^{-tM_a}` evaluated on the diagonal). Then:

```
a² · Σ_y C_R(x, y)²
  = a² · Σ_y (∫₀ᵀ p_s(x, y) ds) · (∫₀ᵀ p_t(x, y) dt)
  = ∫₀ᵀ ∫₀ᵀ (a² · Σ_y p_s(x, y) · p_t(x, y)) ds dt        [Fubini]
  = ∫₀ᵀ ∫₀ᵀ p_{s+t}(x, x) ds dt                             [semigroup]
  ≤ ∫₀ᵀ ∫₀ᵀ C(L) / (s + t) ds dt                            [d=2 trace bound]
  = (2 ln 2) · C(L) · T.
```

Recycles ONLY the upgraded heat-kernel diagonal bound `p_s(x, x) ≤ C(L)/s`.

### m ≥ 3 — Minkowski integral inequality

Commute the `ℓ^m_y` norm INSIDE the s-integral (this is the trick — Hölder
*outside* the integral is the trap):

```
‖C_R(x, ·)‖_{ℓ^m_y(a²)}
  = ‖∫₀ᵀ p_s(x, ·) ds‖_{ℓ^m_y(a²)}
  ≤ ∫₀ᵀ ‖p_s(x, ·)‖_{ℓ^m_y(a²)} ds                          [Minkowski integral ineq.]
```

Bound the inner ℓ^m via Hölder on the spatial sum:

```
‖p_s‖_{ℓ^m}^m = a² · Σ_y p_s(x, y)^m
              ≤ ‖p_s‖_∞^{m-1} · (a² · Σ_y p_s(x, y))
              = ‖p_s‖_∞^{m-1} · e^{-s · mass²}                 [stochastic normalisation]
              ≤ (C(L) / s)^{m-1}.
```

So `‖p_s‖_{ℓ^m} ≤ C^{1-1/m} · s^{1/m - 1}`. The s-integral converges:

```
∫₀ᵀ s^{1/m - 1} ds = m · T^{1/m}.
```

Raising to the m-th power gives `a² · Σ_y C_R(x, y)^m ≤ C(L)^{m-1} · m^m · T`.
**Linear in T, no logs, uniform in (a, N).**

### m = 1 — direct

The constant function on `(ℤ/Nℤ)^d` is the eigenvector of `M_a` with eigenvalue
`mass²` (since the lattice Laplacian annihilates constants). So
`a^d · Σ_y p_s(x, y) = e^{-s · mass²}`, and:

```
a^d · Σ_y C_R(x, y) = ∫₀ᵀ e^{-s · mass²} ds = (1 - e^{-T · mass²}) / mass² ≤ T.
```

## Cross-reference to Glimm-Jaffe

**Lemma 8.5.5** (*Quantum Physics: A Functional Integral Point of View*, 2nd ed.):
in d=2, the short-distance covariance kernel `C_1(x, y)` satisfies
`C_1 ∈ L^p(ℝ²)` for all `1 ≤ p < ∞` — the diagonal log singularity of
`C_R(x, y)` at `x = y` is L^p-integrable for all finite p, so it does not
contribute any log multiplier to the bulk linear-in-T scaling. The
T-parametrised analogue gives exactly `C_m · T` with `C_m` depending on
`(mass, L, m)`.

## Why my Cauchy-Schwarz route failed (record for future)

`Ĉ_R(k)² ≤ T · Ĉ_R(k)` is tight at low momenta (where `Ĉ_R(k) ≈ T`), but for
high momenta `Ĉ_R(k)² ≈ 1/λ_k²` (summable, gives O(1)) while my bound
overestimates as `T/λ_k` (sums to T·log → log divergence). The trap is not in
Plancherel — it's in the pointwise bound. The Fubini/semigroup route avoids it
entirely.

Likewise, the m≥3 Hölder route `‖·‖_m^m ≤ ‖·‖_∞^{m-2} · ‖·‖_2^2` evaluates the
log singularity at its absolute maximum (`x = y`, gives `log(T/a²)` —
introducing the lattice-spacing dependence that's supposed to be uniform!) and
tacks on a spurious polylog factor. Minkowski avoids this.

## Status

* Axiom statements as currently written in `CovarianceBoundsGJ.lean` are
  **correct as-is** — no statement tweaks needed.
* Deep-think strategy folded into the codex discharge brief (2026-05-12).
* Both axioms collapse onto a single new piece of infrastructure: the
  `(a, N)`-uniform `C(L)·(1 + 1/√t)` heat-kernel sum (upgrade of
  `heat_kernel_1d_bound`).
