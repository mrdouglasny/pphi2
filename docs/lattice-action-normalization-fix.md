# Lattice-Action Normalisation: Diagnosis and Fix Plan

*Drafted 2026-05-07. **Vetted by Gemini deep-think 2026-05-07** —
diagnosis confirmed correct; one minor arithmetic harmonisation and
two refinements to the cost / fix-options sections incorporated below.
See §0 for the verdict and §6 for the original questions sent.*

---

## §0. Vetting verdict (Gemini deep-think, 2026-05-07)

* **Q1 (rescaling derivation).** Confirmed. `α = a^{d/2}` for general
  `d`; `:φ_x^{2k}:_{\texttt{wickConstant}} = a^{dk} {:}\Phi(x_a)^{2k}{:}_{c_{\rm textbook}}`.
* **Q2 (Wick subtraction).** Confirmed. `c_a := G_a(0,0) = (1/L^d)\sum_k 1/λ_k`
  is the unique correct subtraction for the `a^d`-rescaled action.
* **Q3 (GRS conventions).** *Refined*: GRS-style "absorb `a^d` into
  the Hamiltonian sum" is internally consistent **only if** polynomial
  coefficients are correspondingly rescaled (`λ_k → a^{-d(k-1)} λ_k`,
  with the precise exponent depending on whether the `a^d` factor sits
  outside the lattice sum — see §1.4 below). pphi2 does *neither*
  rescaling, so it fell through the gap between two equivalent
  conventions.
* **Q4 (alternative fixes).** *Resolved*: (a) rescaling polynomial
  coefficients works mathematically but is "an ugly formalisation
  path" that breaks the lattice-spacing-independence of bare local
  potentials; (b) redefining the embedding **does not work** —
  `dμ_a^P → dμ_a^{GFF}` happens at the level of the lattice measure,
  before any embedding. **Rewriting the action is the only robust
  path.**
* **Q5 (uncertainties §5).** Confirmed. U1 dimensional analysis
  holds; U3 mixed-degree polynomials all vanish (`P = τ^4 + βτ^2`
  gives `a^{dk}`-different scalings for each term, all → 0); U6
  resolved as Q3 above.
* **Q7 (cost estimate).** *Revised upward*: Phase 2 (dynamical-cutoff
  Nelson) more realistic at **6–8 weeks** rather than 2–4. Reason:
  measure-theoretic friction in interactive theorem provers when
  splitting an integration domain into small-field / large-field
  subsets, bounding Gaussian tails on the latter, and recombining.
  Whether pphi2's existing `SmoothLowerBound.lean` /
  `RoughErrorBound.lean` infrastructure shortens this is still
  pending audit.

The original Gemini text is preserved in `docs/gemini_review.md`
(append a section there when this gets committed).

---

## The bug, in one sentence

Pphi2's lattice action `S(φ) = (1/2)⟨φ, M_aφ⟩` is missing the `a^d`
Riemann-sum prefactor on the kinetic term that Glimm–Jaffe / Simon use,
with the consequence that the Wick-subtracted interaction `V_a` is
`a^{dk}`-times smaller than the textbook one (where `2k = deg P` and
`d` is the spatial dimension) and **vanishes in the continuum limit**
for any `d ≥ 2` and `k ≥ 2`.

## Scoreboard

| Quantity | pphi2 today | Glimm–Jaffe / Simon / GRS textbook |
|---|---|---|
| Action `S(φ)` | `(1/2) ⟨φ, M_a φ⟩` (counting) | `(a^d / 2) ⟨φ, M_a φ⟩` (Riemann-sum) |
| `E[φ_x²]` (lattice variance) | `wickConstant ≈ (a²/(2π)) log(1/(am))` → `0` | `c_a ≈ (1/(2π)) log(1/(am))` → `∞` |
| `wickConstant ≤ m^{-2}` | True (each `λ_k ≥ m²`) | **False** (textbook `c_a` diverges) |
| `:P(φ_x):_{wickConstant}` typical size | `O(a^{dk})` | `O(c_a^k)` (textbook) |
| Integrated `V_a = a^d Σ_x :P(φ_x):` | `O(a^{dk}) → 0` for `d ≥ 2, k ≥ 2` | `O(1)` → nontrivial limit |
| Continuum limit measure | **free GFF** | interacting P(φ)₂ |
| `continuumLimit_nonGaussian` axiom (`Pphi2/ContinuumLimit/Convergence.lean:256`) | **False** under this normalisation | True, dischargeable |
| OS0–OS2 theorems for the limit | True (about the free GFF) | True (about the interacting measure) |

The OS0–OS2 theorems remain valid Lean statements either way — the
issue is that on pphi2's current normalisation they are theorems about
the free GFF, not about an interacting theory.

---

## 1. The diagnosis, walked through on `P(τ) = τ⁴` in `d = 2`

This section traces the bug end-to-end on a single running example.
The general case (any `P` of even degree `2k ≥ 4`, any `d ≥ 2`) follows
the same algebra with `4 → 2k`.

### 1.1 What pphi2 has now (5 facts pinned to file:line)

**F1.** `latticeGaussianMeasure` (`gaussian-field/Lattice/Covariance.lean:99`)
has covariance `(M_a^{-1} f, g)` in the **counting** inner product
`⟨f, g⟩ := Σ_x f(x) g(x)`. So the implicit lattice action is
`S(φ) = (1/2) ⟨φ, M_a φ⟩` with **no `a^d` prefactor**, where
`M_a := -Δ_a + m²` and the lattice eigenvalues
(`gaussian-field/Lattice/Laplacian.lean:657`) satisfy `m² ≤ λ_k ≤ 4d/a² + m²`.

**F2.** `wickConstant` (`Pphi2/WickOrdering/Counterterm.lean:58`) equals
`(M_a^{-1})_{xx} = (1/|Λ|) Σ_k 1/λ_k`. The bound
`wickConstant ≤ m^{-2}` (`wickConstant_le_inv_mass_sq`, line 80)
holds because each `1/λ_k ≤ 1/m²`.

**F3.** Riemann-sum estimate (Brillouin-zone integral, `d = 2`):

$$
\texttt{wickConstant} \;\approx\; \frac{a^2}{2\pi}\,\log\frac{1}{a m}.
$$

So `wickConstant → 0` as `a → 0`.

**F4.** Interaction (`Pphi2/InteractingMeasure/LatticeMeasure.lean:65`):

$$
V_a(\omega) \;=\; a^d \sum_x {:}P(\omega(\delta_x)){:}_{\texttt{wickConstant}}.
$$

The `a^d` Riemann-sum prefactor is on the *interaction*, but **not** on
the kinetic term in the action.

**F5.** Embedding (`gaussian-field/SmoothCircle/Restriction.lean:94`):
the circle restriction has the `√a`-per-dimension normalisation, so the
2D evaluation gives

$$
(\widetilde\iota_N \phi)(f) \;\approx\; a \sum_x \phi_x \, f(x_a),
\qquad x_a := x \cdot a.
$$

The propagator-convergence theorem
(`TorusContinuumLimit/TorusPropagatorConvergence.lean:490`) confirms

$$
\mathbb{E}\bigl[(\widetilde\iota_N \phi)(f)\,(\widetilde\iota_N \phi)(g)\bigr]
\;\xrightarrow[N \to \infty]{}\; \langle f,\,(-\Delta + m^2)^{-1}\, g\rangle_{T^2_L}.
$$

So the embedded free field has the **textbook** Green's function as its
2-point function. This is correct; it pins down the field rescaling.

### 1.2 The implicit field rescaling forced by F5

For the embedded 2-point function to match the textbook continuum
Green's function, pphi2's lattice field must be implicitly identified
with `α · Φ(x_a)`, where `Φ` is the textbook continuum field on `T²_L`
and `α` is some `a`-dependent rescaling. Determine `α`:

$$
\mathrm{Var}\bigl((\widetilde\iota_N \phi)(f)\bigr)
\;\overset{F5}{=}\; \sum_{x,y} \mathrm{eval}_x(f)\,\mathrm{eval}_y(f) \cdot G_a(x,y).
$$

If `φ_x = α \cdot Φ(x_a)`, then `G_a(x,y) = α² · G_{\rm textbook}(x_a, y_a)`.
Substituting `eval_x(f) ≈ a^{d/2} f(x_a)` (the embedding's volume-element
scaling — the `√a`-per-coordinate from `circleRestriction` gives `a^{d/2}`
in `d` dimensions) and the Riemann-sum
`Σ_{x,y} F(x_a, y_a) ≈ (1/a^{2d}) \iint F\,dx\,dy`:

$$
\mathrm{Var} \;\approx\; \alpha^2 \cdot a^{d} \cdot \frac{1}{a^{2d}} \cdot a^d \iint f(x) f(y)\, G_{\rm textbook}(x,y)\, dx\, dy
\;=\; \alpha^2 \cdot \langle f, G_{\rm textbook} f\rangle,
$$

where the leading `a^d` is from `eval_x · eval_y ≈ a^d f(x_a) f(y_a)`,
the `1/a^{2d}` is from converting the double sum to a double integral,
and the trailing `a^d` cancels one of the inverse factors via the
`G_a → a^{-d} G_{\rm textbook}` rescaling that comes out of the same
Riemann-sum analysis.

For this to equal `⟨f, G_{\rm textbook} f⟩` (which it must, by F5),
**we need `α = 1`** in the GJ-aligned setting. But pphi2's actual
`Var(φ_x) = wickConstant ≈ a^d · c_{\rm textbook}` (F3 generalised
to dimension `d`), which forces the identification

$$
\boxed{ \quad \phi_x \;=\; a^{d/2} \cdot \Phi(x_a) \quad \text{(implicit pphi2 vs. textbook)}.\quad }
$$

For `d = 2` this is `φ_x = a · Φ(x_a)`, the d=2 special case the
running example of §1 uses.

**Bottom line of §1.2**: pphi2's lattice field is *implicitly the
textbook field shrunk by a factor of* `a^{d/2}`. The propagator
convergence theorem (F5) forces this; there is no other consistent
reading.

### 1.3 Wick monomial under the rescaling

Plug `φ_x = a^{d/2} · Φ(x_a)` and `wickConstant = a^d · c_{\rm textbook}`
into

$$
{:}\tau^{2k}{:}_c \;=\; \sum_{j=0}^{k} \binom{2k}{2j}\,(2j-1)!!\,(-c)^{j}\,\tau^{2k-2j}.
$$

For each `j`, the term carries `(a^{d/2}\Phi)^{2k-2j} \cdot (a^d c_{\rm textbook})^j
= a^{d(k-j)+dj} \cdot \Phi^{2k-2j} \cdot c_{\rm textbook}^j = a^{dk} \cdot \Phi^{2k-2j} c_{\rm textbook}^j`.

The factor `a^{dk}` factors out uniformly:

$$
\boxed{ \quad {:}\phi_x^{2k}{:}_{\texttt{wickConstant}} \;=\; a^{dk} \cdot {:}\Phi(x_a)^{2k}{:}_{c_{\rm textbook}}. \quad }
$$

For our running example (`d = 2, 2k = 4`, i.e. `dk = 4`):
`:φ_x^4:_{wickConstant} = a^4 · :Φ(x_a)^4:_{c_{\rm textbook}}`.

### 1.4 The interaction vanishes

Combining F4 with §1.3:

$$
V_a^{\rm pphi2}(\phi) \;=\; a^d \sum_x {:}P(\phi_x){:}_{\texttt{wickConstant}}
\;=\; a^d \sum_x a^{dk} {:}P(\Phi_{x_a}){:}_{c_{\rm textbook}}
\;=\; a^{d(k+1)} \sum_x {:}P(\Phi_{x_a}){:}_{c_{\rm textbook}}.
$$

Riemann sum: `Σ_x F(x_a) ≈ (1/a^d) \int F\,dx`, so

$$
V_a^{\rm pphi2} \;\approx\; a^{d(k+1)} \cdot \frac{1}{a^d} \int_{T^d_L} {:}P(\Phi){:}_{c_{\rm textbook}}\,dx
\;=\; a^{dk} \cdot \int_{T^d_L} {:}P(\Phi){:}_{c_{\rm textbook}}\,dx.
$$

For our running example (`d = 2`, `2k = 4`):

$$
\boxed{ \quad V_a^{\rm pphi2} \;\approx\; a^{4} \cdot \int_{T^2_L} {:}\Phi^4{:}_{c_{\rm textbook}}\,dx \;\xrightarrow[a \to 0]{}\; 0. \quad }
$$

**Note on the comparison with Gemini's expression.** Gemini's vetting
quoted the slightly different expression `Σ_x :φ_x^{2k}:_{\texttt{wickConstant}}
≈ a^{d(k-1)} ∫ :Φ^{2k}: dx` — i.e., the lattice sum **without** the
`a^d` Riemann-sum prefactor that pphi2 puts in front of `V_a`.
Multiplying by that prefactor recovers `V_a^{\rm pphi2} = a^{dk}∫`,
matching the boxed formula above. Both expressions are correct and
equivalent; they refer to slightly different objects (raw lattice sum
vs. integrated interaction `V_a`).

### 1.5 Comparison with the textbook

The textbook Glimm–Jaffe interaction (with the `a^d` factor on the
kinetic term in the action) is

$$
V_a^{\rm GJ}(\Phi) \;=\; a^d \sum_x {:}P(\Phi_{x_a}){:}_{c_{\rm textbook}}
\;\approx\; \int_{T^d_L} {:}P(\Phi){:}_{c_{\rm textbook}}\,dx \;=\; O(1).
$$

So `V_a^{\rm pphi2} = a^{dk} · V_a^{\rm GJ}`. The textbook interaction
is `O(1)` in the continuum limit; pphi2's is `O(a^{dk}) → 0` for any
`d ≥ 1, k ≥ 1` (and for our case of interest `d ≥ 2, k ≥ 2`, the
exponent is at least `4`).

### 1.6 Therefore the limit is the free GFF

Because `V_a^{\rm pphi2} → 0` typically:
* `e^{-V_a^{\rm pphi2}} → 1` typically.
* `Z_a = E_{\mu^{\rm GFF}}[e^{-V_a^{\rm pphi2}}] → 1`.
* The interacting measure `dμ_a^P = (1/Z_a) e^{-V_a^{\rm pphi2}} dμ^{\rm GFF}_a → dμ^{\rm GFF}_a` weakly.
* The weak limit produced by `torusInteractingLimit_exists` is the same
  as the free-field weak limit, i.e. the free continuum GFF.

Routes A, B′, and pphi2N all use the same `latticeGaussianMeasure` and
`interactionFunctional` and so inherit this conclusion identically.

The axioms `pphi2_nontriviality` (`Pphi2/Main.lean:128`) and
`continuumLimit_nonGaussian` (`Pphi2/ContinuumLimit/Convergence.lean:256`)
assert the limit is non-Gaussian. Under the current normalisation those
are not just open — they are **false**.

---

## 2. The fix: align with Glimm–Jaffe

### 2.1 The change

Add the missing `a^d` factor to the kinetic term:

$$
\boxed{ \quad S^{\rm GJ}_a(\phi) \;:=\; \frac{a^d}{2}\,\langle \phi,\, M_a\, \phi\rangle_{\rm counting}, \qquad \texttt{Cov} \;=\; \frac{1}{a^d} M_a^{-1}. \quad }
$$

Equivalent rewrite in physical units: `S^{\rm GJ}_a(φ) = (1/2) Σ_x a^d φ_x · ((-Δ_a + m²)φ)_x`, the standard Riemann-sum discretisation
of `(1/2) ∫ ((∇φ)² + m²φ²) dx`. This is what Glimm–Jaffe Eq. (6.1.6),
Simon Ch. I, and GRS Eq. (1.2)–(1.3) all write.

### 2.2 Effects

* **Lattice variance**: `E[φ_x^2] = (1/a^d) · wickConstant_{\rm old} ≈ (1/(2π)) log(1/(am))`.
  Now log-divergent, matching the textbook.
* **Renamed Wick constant**: define
  `wickConstant^{\rm GJ} := (1/(a^d|Λ|)) Σ_k 1/λ_k = (1/L^d) Σ_k 1/λ_k`,
  i.e. the textbook `G_a(0,0)`.
* **Interaction**: `V_a = a^d Σ_x :P(φ_x):_{wickConstant^{\rm GJ}}` is
  unchanged in form, but `wickConstant^{\rm GJ}` is now the right
  subtraction for the new `φ_x` variance, and the integrated `V_a` is
  `O(1)`, converging to a nontrivial continuum interaction.
* **Embedding**: `circleRestriction` and `torusEmbedLift` are unchanged.
  Now the implicit identification is `φ_x = Φ(x_a)` directly (no `a` factor).
* **`wickConstant ≤ m^{-2}`**: becomes false. Replaced by the textbook
  asymptotic `wickConstant^{\rm GJ} ~ log(1/a)`.

### 2.3 Nelson's estimate now requires the textbook proof

The current proof of `nelson_exponential_estimate_lattice`
(`Pphi2/NelsonEstimate/NelsonEstimate.lean:73`) uses

$$
V_a \;\ge\; a^d |\Lambda| \cdot (-A) \;=\; -L^d A,
$$

with `A` the well-depth bound from `wickPolynomial_uniform_bounded_below`
applied to `c ∈ [0, m^{-2}]`. Under the fix this is invalid: now
`wickConstant^{\rm GJ} ~ log(1/a) → ∞`, so the well-depth bound `A`
diverges as well. The pointwise lower bound on `V_a` becomes
`-L^d · O((log(1/a))^k)` rather than `-L^d · A`.

The genuine proof is the **dynamical-cutoff / small-and-large field**
decomposition (Glimm–Jaffe Ch. 8, Simon Ch. I):

1. *Small-field event* `\{‖φ‖_∞ ≤ R\}`. On this event,
   `:P(φ_x):_{c_a} ≥ -O(R^{2k})`, so `V_a ≥ -L^d O(R^{2k})`.
2. *Large-field event has Gaussian tail*: by hypercontractivity of the
   GFF, `Pr(\|φ\|_∞ > R) ≤ \exp(-c R^2 / c_a)`. Choosing `R ~ √(c_a · log(...))`
   makes this small while keeping `R^{2k}` polylog-bounded.
3. *Combine*: on the small-field event use the polynomial bound; on the
   large-field event use the Gaussian tail. Show `\int e^{-2V_a} dμ^{\rm GFF}`
   is dominated by the small-field contribution.

The infrastructure for this (`Pphi2/NelsonEstimate/SmoothLowerBound.lean`,
`RoughErrorBound.lean`) exists in the codebase but **isn't currently
load-bearing** — the easy pointwise-bound proof short-circuits it. Under
the fix, those files become essential.

---

## 3. What this changes downstream

| File / theorem | Effect of the fix |
|---|---|
| `gaussian-field/Lattice/Covariance.lean:99` | Definition change: `latticeGaussianMeasure` now uses the `a^d`-rescaled covariance. Headline change. |
| `Pphi2/WickOrdering/Counterterm.lean` | `wickConstant` renamed/redefined; `wickConstant_le_inv_mass_sq` removed (false); `wickConstant_pos`, `wickConstant_antitone_mass` re-proved with the new asymptotics. |
| `Pphi2/NelsonEstimate/NelsonEstimate.lean:73` | Proof of `nelson_exponential_estimate_lattice` rewritten using `SmoothLowerBound.lean` + `RoughErrorBound.lean` infrastructure. The headline statement (`∃ K, ∫ e^{-2V_a} dμ^{\rm GFF} ≤ K` uniformly in `N`) is the same. |
| `Pphi2/InteractingMeasure/LatticeMeasure.lean:65` | `interactionFunctional` definition unchanged in form; `wickConstant` it consumes is now the textbook one. |
| `TorusContinuumLimit/TorusPropagatorConvergence.lean:490` | Statement (`embedded propagator → textbook Green's function`) unchanged, but proof needs the new normalisation in its lattice-side argument. |
| `TorusContinuumLimit/TorusInteractingLimit.lean` (`torus_interacting_tightness`, `torusInteractingLimit_exists`) | Cauchy–Schwarz density transfer is normalisation-independent (see §3.5); structurally the same with a different (Glimm–Jaffe Ch. 8) constant `K`. |
| `TorusContinuumLimit/TorusInteractingOS.lean` OS0–OS2 theorems | Unchanged; they consume an abstract uniform exponential moment bound which still holds. |
| `Pphi2/IRLimit/UniformExponentialMoment.lean` (Route B′) | Hypothesis re-checked with the new `K`. |
| PR #11 (`cylinderIR_uniform_second_moment` axiom-→-theorem conversion, merged 2026-05-03) | Survives: the derivation `x² ≤ 2·exp(\|x\|)` + scaling is dimension-independent. |
| PR #12 (HS / Fourier discharges, merged 2026-05-07) | Survives: HS / Plancherel are normalisation-independent. |
| `Pphi2/Main.lean` axioms `continuumLimit_nonGaussian`, `pphi2_nontriviality` | Become *true* and dischargeable (separately, after the fix lands). |
| Routes A, B′; pphi2N | Inherit the action change at the gaussian-field level; their respective `nelson_exponential_estimate_lattice` consumers re-route through the new proof. |

### 3.5 Cauchy–Schwarz density transfer is normalisation-agnostic

A natural concern (Gemini's closing question): how cleanly does the
existing CS density-transfer machinery separate the functional-analytic
bounds from the underlying lattice variance definitions? **Audited
result: the abstraction is clean, and the surgery is contained.**

The core lemma is `density_transfer_bound`
(`Pphi2/ContinuumLimit/Hypercontractivity.lean:1072`):

```lean
lemma density_transfer_bound
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (K : ℝ) (_hK_pos : 0 < K)
    (hK : ∫ ω, (Real.exp (-interactionFunctional ...))^2 ∂μ_GFF ≤ K)
    (hZ : 1 ≤ partitionFunction ...)
    (F : Configuration → ℝ)
    (hF_nn ...) (hF_meas ...) (hF_sq_int ...) :
    ∫ ω, F ω ∂μ_int ≤ K^(1/2) * (∫ ω, F ω ^ 2 ∂μ_GFF)^(1/2)
```

It consumes Nelson `K` and `Z ≥ 1` as **opaque numerical hypotheses**.
It does not reference `wickConstant`, eigenvalues, the action, or
`a^d` factors. The proof is pure functional analysis (Hölder p=q=2,
`withDensity` rewriting, `MemLp` plumbing). Normalisation-independent.

Three sites do touch lattice-specific machinery:

* **`partitionFunction_ge_one`** (`Hypercontractivity.lean`, ~line 1040).
  Uses Jensen + `\int V_a\,d\mu^{\rm GFF} = 0` (Wick polynomials are
  GFF-mean-zero). Both inputs hold under any normalisation; the proof
  is normalisation-agnostic in form, only the algebra of the centering
  changes. **Stable across the fix.**
* **`interactionFunctional_bounded_below`**
  (`Pphi2/InteractingMeasure/LatticeMeasure.lean:111`). Currently
  proves `\exists B,\, V_a \ge B` for fixed `a, N`, with `B` derived
  from `wickConstant \le m^{-2}`. Under the fix, the lemma still
  *holds* (the well-depth bound `A` becomes `a`-dependent but finite
  for each fixed `a`), but `B` no longer admits a uniform-in-N bound.
  Audit of the 12 call sites:
  * The CS proof's use (`density_transfer_bound:1127`) is for fixed
    `a, N` to get `\|bw\|_{L^2} < \infty`, **not** uniform-in-N. Survives.
  * Most other call sites are similarly fixed-`a` `MemLp` plumbing:
    `Pphi2/InteractingMeasure/Normalization.lean:79,143`,
    `Pphi2/ContinuumLimit/Tightness.lean:134`,
    and the parallel Asymtorus / TorusInteractingOS sites.
  * No call site I found uses *uniformity* of `B` in `N`. Uniform
    control passes through Nelson `K`. **Mechanical patches at most.**
* **`nelson_exponential_estimate_lattice`**
  (`Pphi2/NelsonEstimate/NelsonEstimate.lean:73`). The current proof
  factors through `interactionFunctional ≥ -L^d A` with constant `A`,
  which is the direct use of `wickConstant ≤ m^{-2}` and is uniform
  in `N`. Under the fix `A` diverges polylogarithmically. **This is
  Phase 2's entire mathematical content** (the dynamical-cutoff proof).
  Direct call sites of the bound elsewhere (`CovarianceSplit.lean:108`,
  `Hypercontractivity.lean:888`, `AsymTorusInteractingLimit.lean:90`,
  `NelsonEstimate.lean:100`) all need re-routing through the new proof.

**Net assessment**: ~95% of the OS chain — `torus_interacting_tightness`,
`torus_interacting_second_moment_uniform`, `torusInteractingLimit_exists`,
the OS0/OS1/OS2 theorems, the parallel `AsymTorus/` and IR-limit
machinery — depends only on the abstract `(K, Z ≥ 1)` interface.
Substantive work concentrates in:

1. `gaussian-field/Lattice/Covariance.lean` (one definition rescaled).
2. `Pphi2/WickOrdering/Counterterm.lean` (constants drop, get re-derived
   with new asymptotics).
3. `Pphi2/NelsonEstimate/NelsonEstimate.lean` and dependencies (real
   dynamical-cutoff proof).

Everything else inherits via the abstract interface. The Phase 1 + 2
estimate (§4) reflects this.

---

## 4. Plan

### Progress (as of 2026-05-08)

**Phase 0 (vetting): done.** **Phase 1 (action change): done** — landed on
`fix/lattice-action-normalization` and the corresponding gaussian-field
branch. **Phase 2 (Nelson's estimate proper): partial** — 7 of 11 Stage 1
axioms discharged. Combined axiom count: 35 (post-Stage 1) → 26 (current).

The remaining 4 Stage 1 axioms split into two clusters:

- **Cluster A (Nelson dynamical-cutoff)**: 4 axioms reducing to the same
  Glimm–Jaffe Ch. 8 estimate. Multi-week deliverable.
- **Cluster B (embedding-normalisation, asymmetric branch)**: 2 axioms
  awaiting an `evalAsymAtFinSiteGJ` refactor analogous to the symmetric
  `evalTorusAtSiteGJ`. ~1 week.

Discharged so far in Phase 2:

* `roughCovariance_sq_summable` (CovarianceSplit.lean) — proved theorem
  with `field_simp` + `a^d` rescale of original 30-line proof.
* `smoothVariance_le_log` (CovarianceSplit.lean) — proved with the trivial
  `C = (a^d)⁻¹ · mass⁻²` bound.
* `normalizedGaussianDensityMeasure_eq_normalizedQuadraticGaussianMeasure`
  (gaussian-field Density.lean) — density unfolding + `Finset.mul_sum`.
* `normalizedGaussianDensityMeasure_linearFourier` (gaussian-field
  Density.lean) — adapts the original 290-line bare-form Fourier proof via
  the new `integral_massEigenbasis_cexp_GJ` helper.
* `torus_propagator_convergence_GJ` (TorusPropagatorConvergence.lean) —
  discharged via the `(a^d)⁻¹ · (L/N)² = 1` cancellation between
  `evalTorusAtSiteGJ` and `latticeCovarianceGJ`.
* `torusEmbeddedTwoPoint_uniform_bound` (TorusPropagatorConvergence.lean)
  — Cluster B 1/2, same cancellation pattern. Proved via the helper
  `torusEmbeddedTwoPoint_le_seminorm_tight` which factors the explicit
  `mass⁻² · L² · C₀⁴ · p₀(f)²` bound.
* `torusEmbeddedTwoPoint_le_seminorm` (TorusInteractingOS.lean) — Cluster
  B 2/2 (symmetric branch). Discharged via the same tight helper, witness
  `mass⁻¹ · L · C₀² · rapidDecaySeminorm 0 f`.

Still axiomatised (6 in pphi2):

* Cluster A — `nelson_exponential_estimate_lattice` (NelsonEstimate.lean),
  `exponential_moment_bound` (Hypercontractivity.lean),
  `asymNelson_exponential_estimate`, `asymTorusInteracting_exponentialMomentBound`
  (AsymTorus/{AsymTorusInteractingLimit,AsymTorusOS}.lean).
* Cluster B asymmetric — `asymGaussian_second_moment_uniform_bound`,
  `asymGf_sub_norm_le_seminorm`. Discharge requires introducing
  `evalAsymAtFinSiteGJ := asymGeomSpacing • evalAsymAtFinSite` in the
  asym embedding (analog of the symmetric `evalTorusAtSiteGJ`), updating
  `asymTorusEmbedLift` to use it, and chasing the cancellation through
  the existing `asymLatticeTestFn_norm_sq_le` infrastructure.

The Cluster A four reduce to the same dynamical-cutoff Nelson estimate
(Glimm–Jaffe Ch. 8); `SmoothLowerBound.lean` and `RoughErrorBound.lean`
hold the scaffolded infrastructure.

### Phase 0 — vetting

**Done (2026-05-07)**: Gemini deep-think confirmed the diagnosis on Q1,
Q2, Q4, Q5; refined Q3, Q7. Verdict in §0. Codex search for an existing
Lean formalisation hitting the same trap: none found (Gemini Q6).
Audit of CS density-transfer machinery: §3.5.

### Phase 1 — gaussian-field action change (~1–2 weeks)

* `gaussian-field/Lattice/Covariance.lean:99` — rescale to
  `Cov = (1/a^d) M_a^{-1}`.
* `Pphi2/WickOrdering/Counterterm.lean` — redefine `wickConstant` to
  the GJ-aligned `(1/L^d) Σ_k 1/λ_k`, drop `wickConstant_le_inv_mass_sq`,
  re-prove `wickConstant_pos` and friends with the new (log-divergent)
  asymptotics.
* `Pphi2/InteractingMeasure/LatticeMeasure.lean:111` — leave
  `interactionFunctional_bounded_below` in place (still true for fixed
  `a, N`, just with a worse `a`-dependent `B`).
* Mechanical re-proofs across the 12 fixed-`a` consumers of
  `interactionFunctional_bounded_below`; no new mathematics.

### Phase 2 — Nelson's estimate proper (~6–8 weeks, revised)

* Wire `Pphi2/NelsonEstimate/SmoothLowerBound.lean` and
  `RoughErrorBound.lean` into a real dynamical-cutoff proof of
  `nelson_exponential_estimate_lattice`.
* This is the real constructive-QFT mathematical content (Glimm–Jaffe
  Ch. 8 / Simon Ch. I provide the textbook proof to follow).
* **Revision from initial 2–4-week estimate**: per Gemini's vet,
  measure-theoretic friction in Lean for splitting the integration
  domain into `\{‖φ‖_∞ \le R\}` vs `\{‖φ‖_∞ > R\}`, bounding Gaussian
  tails on the latter, and recombining the integrals dominates the
  cost. If the existing `SmoothLowerBound.lean` infrastructure shortens
  the small-field side, 6 weeks is achievable; otherwise budget 8.
  Worth investing in *reusable* `Mathlib`-style domain-splitting +
  Gaussian-tail-integration lemmas here, since the same friction
  appears for Phase 4 and any future O(N) mass-gap work.

### Phase 3 — propagation through routes (~1–2 weeks)

* Routes A, B, B′, and pphi2N inherit Phase 1 automatically (one
  `gaussian-field` definition).
* Re-check Cauchy–Schwarz density-transfer constants (per §3.5,
  the machinery itself is normalisation-agnostic; only the consumed
  `K` changes).
* Re-verify each route's headline OS theorem still compiles.

### Phase 4 — discharge `continuumLimit_nonGaussian` and `pphi2_nontriviality`

Multi-week separate work; only possible *after* Phases 1–2 since these
axioms become provable only when the interaction is genuine.

**Total to a real P(φ)₂ construction**: ~9–13 weeks (Phases 1–3).
Phase 4 is its own program.

---

## 5. Where I might be wrong

This diagnosis is a back-of-envelope scaling argument, not a Lean-checked
proof. The places it could go off — annotated post-vet (2026-05-07):

**U1. ✓ Resolved (Gemini Q1, Q5).** *Implicit field rescaling.* The
embedding's effective weight is `a^{d/2}` in `d` dimensions, and the
implicit identification is `φ_x = a^{d/2} Φ(x_a)`. The original draft
was correct in spirit (and pinned to `α = a` for `d = 2`); the §1.2
text now states the general formula explicitly.

**U2. — Standing.** *Riemann-sum-correctness of `wickConstant`.*
Gemini's vet confirms the leading scaling but the precise constant
(the `(1/(2π))` in `c_{\rm textbook} ≈ (1/(2π)) \log(1/(am))`) was
not independently verified. Standard Brillouin-zone calculation;
should be solid.

**U3. ✓ Resolved (Gemini Q5).** *Wick monomial homogeneity for
mixed-degree polynomials.* For `P(τ) = τ^4 + βτ^2` the two terms
scale as `a^{2d}` and `a^d` respectively (with the `a^d` Riemann-sum
prefactor included). Both → 0 as `a → 0`. The continuum limit is
**cleanly the free GFF regardless of `β`**; no `β`-dependent surviving
piece. So the conclusion of §1.6 holds for all `P` with `\deg P \ge 2`.

**U4. — Standing.** *Whether `V_a → 0` typically implies the limit is
the free GFF.* Pointwise + `L^2` vanishing both hold, so `e^{-V_a} \to 1`
in `L^2(\mu^{\rm GFF})`. Combined with `Z_a \to 1` this gives weak
convergence of the Boltzmann-weighted measure to `\mu^{\rm GFF}`.
Standard but not formally checked.

**U5. ✓ Resolved (§3.5 audit).** *Whether the propagator-convergence
theorem is normalisation-independent.* The *statement* is, and the
existing proof's lattice-side argument re-runs in the rescaled
normalisation with mechanical changes. Reviewed in the §3.5 audit
of the surrounding machinery.

**U6. ✓ Resolved (Gemini Q3).** *Whether "missing `a^d`" is the
textbook canonical convention.* GRS-style "absorb `a^d` into the
Hamiltonian" is internally consistent **only if** polynomial coefficients
are correspondingly rescaled `λ_k → a^{-d(k-1)} λ_k` (or equivalently
`a^{-dk}` if the explicit `a^d` prefactor of `V_a` is also dropped).
pphi2 does neither rescaling — falling between two equivalent
conventions. The fix (align with GJ's explicit `a^d` action) is the
robust path; alternative (rescale the polynomial coefficients) was
judged "ugly formalisation" by Gemini Q4(a).

**U7. — Standing, audit lighter than first feared (§3.5).**
*Effect on Routes A, B′, pphi2N specifically.* The diagnosis focuses
on Route B (torus). The conclusion that the same bug propagates to
Route A, B′, pphi2N is by structural reasoning ("they use the same
lattice action"). The §3.5 audit reduces this to a question of which
specific call sites use the `wickConstant ≤ m^{-2}` bound; only four
direct uses, all routed through `nelson_exponential_estimate_lattice`.
Worth a focused grep before Phase 1 lands.

---

## 6. Open questions for Gemini deep-think / Codex vetting

These were the questions sent to Gemini deep-think on 2026-05-07.
Verdict per question is in §0; full text is preserved here for
traceability.

**Q1 (most important).** Verify the rescaling derivation §1.2–1.4. Is

> *Pphi2's lattice field `φ_x` (with variance `wickConstant ≈ a^d · c_{\rm textbook}`) is implicitly identified with `a^{d/2} · Φ(x_a)` in the textbook continuum field, and consequently `:P(φ_x):_{wickConstant} = a^{d·k} · :P(Φ_{x_a}):_{c_{\rm textbook}}` for a monomial of degree `2k`.*

correct **dimensionally** (any `d`)? My derivation in §1 used `d = 2`
specifically and got `α = a` (so `a^{d/2} = a` when `d = 2`). **For
general `d`**, is it `α = a^{d/2}`? If so the conclusion `V_a^{\rm pphi2} \approx
a^{d \cdot k} · V_a^{\rm GJ}` (in the obvious extension) — please verify.

**Q2.** Is the textbook `c_a := G_a(0,0) = (1/L^d) Σ_k 1/λ_k` (with the
`a^d`-rescaled action) indeed the right Wick subtraction, in the sense
that `:P(φ_x):_{c_a}` has `O(1)`-typical fluctuation in the GFF, with
the usual `O(c_a^{k-1})` Gaussian-tail bounds, etc.? (This is a
textbook fact but worth pinning down explicitly because the conclusion
of the diagnosis depends on it.)

**Q3.** GRS-specifically: re-read Guerra–Rosen–Simon Eq. (1.2)–(1.3)
and §2 to check whether their lattice action has the `a^d` factor
absorbed somewhere else (into the field, into the polynomial, or
elsewhere). **If GRS uses the same action as pphi2 has now**, the bug
might not be in pphi2 but in the doc's claim that pphi2 should follow
Glimm–Jaffe — there's a real choice between two mathematically
equivalent normalisations, and pphi2 might be using the GRS one
internally consistently (with compensating rescalings elsewhere I
haven't found).

**Q4.** Are there alternative fixes that wouldn't require rewriting
the action? For example:

* (a) Rescale the polynomial coefficients of `P` by `a^{-2k_{\rm top}}`.
  Yields the same continuum theory? Easier to land in Lean?
* (b) Redefine the embedding so the embedded distribution carries the
  textbook field. Changes `torusEmbedLift` instead of `latticeGaussianMeasure`.
* If either is viable, it might be a smaller change with the same
  endpoint.

**Q5.** Sanity check the "uncertainties" in §5:

* U1: Does the embedding really carry `a^{1/2}` per coordinate? Does it
  give `a^{d/2}` total in `d` dimensions, or something else?
* U3: For mixed-degree polynomials like `P = τ^4 + ατ²`, is the limit
  theory under pphi2's normalisation cleanly free, or is it some
  `α`-mode-dependent thing? If the latter, that complicates the
  diagnosis.
* U6: re-check the textbook conventions (GJ vs Simon vs GRS) and pin
  down which one pphi2 should be aligned to.

**Q6.** Has any other Lean formalisation of constructive QFT (or even
just 2D Gaussian field theory at the Wick-polynomial level) made an
analogous choice, and if so, did it produce the trivial limit too?
(There's some discussion in the Mathlib4 community of formalising
random fields; would be useful to know if any of them have hit this.)

**Q7.** Is the cost estimate (§4) realistic? Specifically: how big is
the dynamical-cutoff Nelson-estimate proof in Lean, given the
infrastructure already in `Pphi2/NelsonEstimate/SmoothLowerBound.lean`
and `RoughErrorBound.lean`? Could be 2 weeks (if the existing
infrastructure is mostly ready) or 3 months (if it isn't).

---

## 7. References

* Glimm and Jaffe, *Quantum Physics: A Functional Integral Point of
  View*, Springer 1987.
   * §6.1: lattice approximation. Eq. (6.1.6) is the textbook
     discretised action with the `a^d` Riemann-sum factor — the
     convention this doc proposes pphi2 should align to.
   * Ch. 8: dynamical-cutoff proof of Nelson's estimate. Replaces the
     uniform-pointwise-bound argument.
* Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory*, Princeton 1974.
   * Ch. I: lattice approximation, Wick ordering, Nelson's estimate.
   * Cleanest Cauchy–Schwarz density-transfer exposition.
* Guerra, Rosen, Simon, "The P(φ)₂ Euclidean field theory as classical
  statistical mechanics," *Ann. Math.* 101 (1975), 111–259.
   * Eq. (1.2)–(1.3): the lattice-action convention. **Verify carefully
     against pphi2 — this is the most likely candidate for the
     reference pphi2 follows.**
* Nelson, "The free Markov field," *J. Funct. Anal.* 12 (1973),
  211–227. The hypercontractive estimate at the heart of Phase 2.
