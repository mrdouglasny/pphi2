# Lattice-Action Normalization: Bug Diagnosis + Fix Plan

*Drafted 2026-05-07 in response to the observation that pphi2's
`V_a` may vanish in the continuum limit. **Not yet vetted.** This
doc records the diagnosis, the proposed Glimm–Jaffe-aligned fix, and
a list of open questions for Gemini deep-think / Codex review before
any code changes are made.*

---

## TL;DR

Pphi2's lattice Gaussian measure uses the action
`S(φ) = (1/2) ⟨φ, (-Δ_a + m²) φ⟩` in the **counting** inner product
(no `a^d` Riemann-sum prefactor on the kinetic term), while the
interaction carries the prefactor `a^d` correctly:
`V_a(φ) = a^d · Σ_x :P(φ_x):_{wickConstant}`.

The Wick subtraction `wickConstant := (1/|Λ|) Σ_k 1/λ_k` is
**bounded by `m⁻²`**, not logarithmically divergent — it is the
field variance under pphi2's small-field action, *not* the textbook
Glimm–Jaffe Wick constant `c_{\rm textbook} = G_{\rm textbook}(0,0)
\sim \log(1/a)`.

A scaling argument (§3) shows pphi2's `\phi_x` is implicitly
identified with `a · \Phi(x_a)` (where `\Phi` is the textbook field),
and consequently
`V_a^{pphi2} = a^{2k_{\rm top}} \cdot V_a^{\rm GJ}` for a polynomial
of top degree `2k_{\rm top}`. In 2D with `P` of degree ≥ 4, this is
**`O(a^4)` smaller** than the textbook interaction.

The continuum limit of `V_a^{pphi2}` therefore vanishes; the limit
measure produced by `torusInteractingLimit_exists` and consumed by
`torusInteracting_satisfies_OS` is the **free Gaussian field**, not
the interacting P(φ)₂ theory. The OS0–OS2 theorems are still true —
the free GFF satisfies them — but the "interacting" P(φ)₂ measure
is not what pphi2 currently constructs.

The proposed fix (§5) is to align the lattice action with
Glimm–Jaffe by including the `a^d` Riemann-sum prefactor on the
kinetic term, restoring the textbook Wick constant
`c_a = G_a(0,0) \sim \log(1/a)` and the standard Glimm–Jaffe analysis.
This fix invalidates `wickConstant_le_inv_mass_sq` and the easy proof
of `nelson_exponential_estimate_lattice`, requiring the genuine
dynamical-cutoff argument (whose infrastructure already exists in
`Pphi2/NelsonEstimate/`).

---

## 1. The current normalization (what pphi2 does today)

### 1.1 The lattice GFF

`gaussian-field/Lattice/Covariance.lean:99` defines the lattice
Gaussian measure as `GaussianField.measure (latticeCovariance)`,
where `latticeCovariance` is the operator-square-root of the inverse
of the kinetic operator `M_a := (-Δ_a + m²)`. The covariance bilinear
form (`lattice_cross_moment`, line 119) is

$$
\mathbb{E}[\omega(f) \omega(g)] \;=\; \langle f,\, M_a^{-1}\, g\rangle_{\rm counting}
\;=\; \sum_{x, y} f(x)\, (M_a^{-1})_{xy}\, g(y).
$$

The inner product is the **counting inner product** — no `a^d` weight
per site. Equivalently, the lattice action is

$$
S^{\rm pphi2}(\phi) \;=\; \tfrac{1}{2}\,\langle \phi,\, M_a\, \phi\rangle_{\rm counting}
\;=\; \tfrac{1}{2}\sum_x \phi_x\,(M_a \phi)_x.
$$

The lattice eigenvalues (in `gaussian-field/Lattice/Laplacian.lean:657`)
are

$$
\lambda_k \;=\; \tfrac{4}{a^2} \sum_{i=1}^d \sin^2\!\left(\tfrac{\pi k_i}{N}\right) + m^2,
\qquad m^2 \;\le\; \lambda_k \;\le\; \tfrac{4d}{a^2} + m^2.
$$

### 1.2 The Wick constant

`Pphi2/WickOrdering/Counterterm.lean:58`:

$$
\texttt{wickConstant} \;:=\; \frac{1}{|\Lambda|} \sum_k \frac{1}{\lambda_k}.
$$

This equals the lattice covariance at coinciding sites in pphi2's
counting normalization: `wickConstant = (M_a^{-1})_{xx}`.

The bound `wickConstant ≤ m^{-2}` (`wickConstant_le_inv_mass_sq`,
line 80) follows because `λ_k ≥ m²` (zero mode is `m²`), so each
`1/λ_k ≤ 1/m²`, and the average of `|Λ|` such terms is `≤ 1/m²`.

### 1.3 The interaction

`Pphi2/InteractingMeasure/LatticeMeasure.lean:65`:

$$
V_a(\omega) \;=\; a^d \sum_x {:}P(\omega(\delta_x)){:}_{\texttt{wickConstant}}.
$$

The `a^d` prefactor is the Riemann-sum measure for the spatial integral.

### 1.4 The embedding

`gaussian-field/SmoothCircle/Restriction.lean:94` defines circle
restriction with the **`√a` per dimension** normalization:

$$
(r_N f)(k) \;=\; \sqrt{a}\, f(k\,a).
$$

The 2D embedding `eval_x` is a tensor of two such restrictions and
carries an effective `a` per pure tensor. So the embedded distribution
carries the weight

$$
(\widetilde\iota_N \phi)(f) \;=\; \sum_x \phi(x)\,\mathrm{eval}_x(f) \;\approx\; a \sum_x \phi(x)\, f(x_a).
$$

### 1.5 Embedded propagator agrees with textbook

`torus_propagator_convergence`
(`TorusContinuumLimit/TorusPropagatorConvergence.lean:490`):

$$
\mathbb{E}\bigl[(\widetilde\iota_N \phi)(f)\,(\widetilde\iota_N \phi)(g)\bigr]
\;\xrightarrow[N \to \infty]{}\; \langle f,\, (-\Delta + m^2)^{-1}\, g\rangle_{T^2_L}.
$$

So the **embedded free field** has the textbook continuum Green's
function as its 2-point function. This is good — it pins down the
identification of pphi2's lattice field with the textbook continuum
field.

---

## 2. Asymptotics of `wickConstant`

The bound `wickConstant ≤ m^{-2}` is correct but loose. Approximating
the average as a Riemann sum over the Brillouin zone:

$$
\frac{1}{|\Lambda|} \sum_k \frac{1}{\lambda_k}
\;\approx\; \frac{1}{|\Lambda|} \cdot \left(\frac{L}{2\pi}\right)^d \int_{|\mathbf{k}| < \pi/a} \frac{d^d \mathbf{k}}{\mathbf{k}^2 + m^2}.
$$

In 2D the integral gives `π·\log((π/a)^2/m^2)`, so

$$
\texttt{wickConstant}_{2D} \;\sim\; \frac{a^2}{2\pi} \log\frac{1}{a m} \;\xrightarrow[a \to 0]{}\; 0.
$$

This is much smaller than the textbook Wick constant
`c_{\rm textbook} = G_{\rm textbook}(0,0) \sim (1/2\pi) \log(1/(am))`,
which **diverges** logarithmically as `a → 0`.

The factor of `a^2` is the discrepancy: `wickConstant ≈ a^2 \cdot c_{\rm textbook}`.

---

## 3. Why the interaction vanishes — derivation

### 3.1 Implicit field identification

Consistency of §1.5 (embedded propagator → textbook Green's function)
forces the identification

$$
\phi_x \;\sim\; a \cdot \Phi(x_a),
$$

where `\Phi` is the textbook 2D continuum field on `T^2_L` and
`x_a := x \cdot a` is the physical position. Verification:
the embedded 2-point function is

$$
\mathrm{Var}\bigl((\widetilde\iota_N \phi)(f)\bigr) \;=\; \sum_{x,y} \mathrm{eval}_x(f)\,\mathrm{eval}_y(f) \cdot G_a^{\rm pphi2}(x,y).
$$

Substituting `eval_x(f) ≈ a · f(x_a)` and `\phi_x = a \Phi(x_a)` (so
`G_a^{\rm pphi2}(x, y) = a^2 \cdot G_{\rm textbook}(x_a, y_a)`):

$$
\mathrm{Var} \;\approx\; \sum_{x,y} (a f(x_a))(a f(y_a)) \cdot a^2 G_{\rm textbook}(x_a, y_a)
\;=\; a^4 \sum_{x,y} f(x_a) f(y_a) G_{\rm textbook}(x_a, y_a).
$$

Riemann sum: `Σ_x F(x_a) ≈ (1/a^2) \int F(x) dx`, so the double sum
is `≈ (1/a^4) \int\int f f' G dx dy`, giving

$$
\mathrm{Var} \;\approx\; \langle f, G_{\rm textbook} f\rangle. \quad\checkmark
$$

This is the propagator-convergence theorem, restated. The
identification `\phi_x = a \Phi(x_a)` is forced.

### 3.2 Wick polynomial under field rescaling

For a Wick monomial of degree `2k` with subtraction constant `c`,

$$
{:}\tau^{2k}{:}_c \;=\; \sum_{j=0}^{k} \binom{2k}{2j}\,(2j-1)!!\,(-c)^{j}\,\tau^{2k-2j}.
$$

Substituting `τ = aΦ` and `c = a^2 c_{\rm textbook}` (matching the
field rescaling and pphi2's wickConstant ≈ a²·c_textbook):

$$
{:}(a\Phi)^{2k}{:}_{a^2 c_{\rm textbook}}
\;=\; \sum_j \binom{2k}{2j}(2j-1)!!\,(-a^2 c_{\rm textbook})^j\,(a\Phi)^{2k-2j}
$$

Each term carries a factor `a^{2j} \cdot a^{2k - 2j} = a^{2k}`,
uniformly. Therefore

$$
{:}(a\Phi)^{2k}{:}_{a^2 c_{\rm textbook}} \;=\; a^{2k} \cdot {:}\Phi^{2k}{:}_{c_{\rm textbook}}.
$$

For a general polynomial `P(\tau) = \sum_{2k} a_{2k} \tau^{2k}`,

$$
{:}P(\phi_x){:}_{\texttt{wickConstant}} \;=\; \sum_{2k} a_{2k} \cdot a^{2k} \cdot {:}\Phi^{2k}_{x_a}{:}_{c_{\rm textbook}}.
$$

### 3.3 Interaction under the rescaling

$$
V_a^{\rm pphi2}(\phi) \;=\; a^d \sum_x {:}P(\phi_x){:}_{\texttt{wickConstant}}
\;=\; \sum_{2k} a_{2k} \cdot a^{d+2k} \sum_x {:}\Phi^{2k}_{x_a}{:}_{c_{\rm textbook}}.
$$

Riemann-sum interpretation: `Σ_x F(x_a) ≈ (1/a^d) \int F dx`, so

$$
V_a^{\rm pphi2}(\phi) \;\approx\; \sum_{2k} a_{2k} \cdot a^{2k} \cdot \int_{T^2_L} {:}\Phi^{2k}{:}_{c_{\rm textbook}}\, dx.
$$

For `2k > 0`: `a^{2k} \to 0` as `a \to 0`. The interaction vanishes.

### 3.4 Comparison with Glimm–Jaffe

The textbook Glimm–Jaffe interaction is

$$
V_a^{\rm GJ}(\Phi) \;=\; a^d \sum_x {:}P(\Phi_{x_a}){:}_{c_{\rm textbook}}
\;\approx\; \int_{T^2_L} {:}P(\Phi){:}_{c_{\rm textbook}}\, dx.
$$

This is `O(1)` in `a` and converges to a nontrivial random variable
in the continuum limit. The ratio:

$$
V_a^{\rm pphi2} \;=\; a^{2k_{\rm top}} \cdot V_a^{\rm GJ}.
$$

In 2D with `P` of top degree `2k_{\rm top} = 4`:
`V_a^{\rm pphi2} = a^4 \cdot V_a^{\rm GJ} \to 0`.

---

## 4. Consequences for the existing pphi2 theorems

### 4.1 What's still true

* The free-field measure `torusContinuumMeasure` and its OS0–OS2
  theorems are correct: they apply to a free Gaussian field whose
  2-point function is `(-Δ + m²)^{-1}` on `T^2_L`. The lattice→continuum
  free-field convergence is rigorous and its theorems are honest.
* `nelson_exponential_estimate_lattice` is still a valid Lean theorem
  — but its math content is uninteresting. It says
  `\int e^{-2 V_a} d\mu^{\rm GFF} \le K`, which is trivially true
  because `V_a \to 0` typically and `V_a \ge -L^2 A` worst-case.
* `torusInteractingLimit_exists` is still valid Lean — it produces a
  weak limit measure. But the limit is the same as the free-field
  limit (up to the Cauchy–Schwarz density transfer factor, which
  approaches 1 as `V_a → 0` and `Z_a → 1`).

### 4.2 What's misleading

* Calling the limit measure "the P(φ)₂ interacting measure" is wrong.
  It is the free GFF.
* `torusInteracting_satisfies_OS` proves OS0–OS2 *for that limit
  measure*, but does not distinguish it from the free GFF.
* `pphi2_nontriviality` and `continuumLimit_nonGaussian` (axioms in
  `Pphi2/Main.lean:128` and `Pphi2/ContinuumLimit/Convergence.lean:256`)
  are **false** under the current normalization — the limit *is*
  Gaussian and trivial.

### 4.3 What the route-A and route-B' analogs inherit

Route A (lattice → S'(ℝ²)) and Route B′ (asymmetric torus → cylinder
IR) use the same `latticeGaussianMeasure` and the same
`interactionFunctional`. They inherit the same bug. Pphi2N (O(N) LSM)
is built on the same lattice-action layer and inherits it as well.

The recently-merged PR #11 (`cylinderIR_uniform_second_moment`) and
PR #12 (HS / Fourier discharges) are mathematically correct as
*statements about the Gaussian limit*; they don't depend on the
interaction being nontrivial.

---

## 5. Proposed fix: align with Glimm–Jaffe

### 5.1 The action

Replace the lattice action with the Riemann-sum-correct version

$$
S^{\rm GJ}_a(\phi) \;=\; \tfrac{a^d}{2}\,\langle \phi,\, M_a\, \phi\rangle_{\rm counting}
\;=\; \tfrac{a^d}{2}\sum_{x} \phi_x (M_a \phi)_x,
$$

equivalently the Gaussian measure with covariance

$$
\bigl(\widetilde M_a^{\rm GJ}\bigr)^{-1} \;=\; \tfrac{1}{a^d} M_a^{-1}.
$$

Effects:

* The variance at a single site becomes
  `\mathbb{E}[\phi_x^2] = (1/a^d) \cdot (M_a^{-1})_{xx} = (1/a^d) \cdot \texttt{wickConstant}_{\rm old}`.
* In 2D this is `\sim (1/a^2) \cdot a^2 \log(1/a) / (2\pi) \sim \log(1/a) / (2\pi)`
  — the textbook log-divergent Wick constant.

### 5.2 The new wickConstant

Define

$$
\texttt{wickConstant}^{\rm GJ} \;:=\; \frac{1}{a^d \cdot |\Lambda|} \sum_k \frac{1}{\lambda_k}
\;=\; \frac{1}{L^d} \sum_k \frac{1}{\lambda_k}.
$$

This is the textbook `G_a(0, 0)`. In 2D it is
`\sim (1/(2\pi)) \log(1/(am))` — diverges as `a \to 0`.

### 5.3 Embedding stays the same

The circle restriction `r_N f = \sqrt{a} \cdot f(\cdot a)` and the
embedding `(ι_N \phi)(f) = \sum_x \phi_x \mathrm{eval}_x(f)` stay
unchanged.

After the action change, `\phi_x` itself has variance
`\sim \log(1/a)`, matching the textbook continuum-field variance at
a regularized point. The implicit identification with the textbook
field becomes `\phi_x = \Phi(x_a)` directly (no `a` factor), and the
interaction's `a^d \sum_x` Riemann-sum prefactor produces the
textbook `\int :P(\Phi):_{c_{\rm textbook}}\, dx` in the continuum.

### 5.4 The interaction definition stays the same

`interactionFunctional = a^d \sum_x :P(\omega(\delta_x)):_{wickConstant}`
remains correct. The `wickConstant` it uses is now the textbook one
(the new definition above), and the `\omega(\delta_x)` field has the
right textbook variance, so the Wick subtraction is the textbook one
and the integrated `V_a` is `O(1)` and converges to a nontrivial
continuum interaction.

### 5.5 Nelson's estimate becomes a real theorem

`wickConstant ≤ m^{-2}` becomes **false** (`wickConstant ≈ \log(1/a) \to \infty`).
The easy proof of `nelson_exponential_estimate_lattice` (uniform
pointwise bound `V_a ≥ -L^2 A`) is gone, because now `V_a` has
typical fluctuations of size `O(1)` and worst-case lower bounds that
grow polynomially in `\log(1/a)`.

The genuine Glimm–Jaffe argument is needed:

1. *Small-field bound*: `\Pr_{\mu^{\rm GFF}}(\|\phi\|_\infty \le R) ≥ 1 - O(e^{-R^2 / c_a})`
   for fluctuations of typical size `\sqrt{c_a}`.
2. *Wick polynomial bound on small fields*: for `|\phi(x)| \le R`,
   `:P(\phi):_{c_a} \ge -O(R^k + c_a^{k/2})`, giving
   `V_a \ge -L^d \cdot O(R^k + c_a^{k/2})` on the small-field event.
3. *Large-field event has double-exponential tail*: by hypercontractivity
   of the GFF, the event `\|\phi\|_\infty > R` has probability
   `\le e^{-c_2 R^2 / c_a}`, and on that event `V_a` could be very
   negative, but the Boltzmann weight `e^{-V_a}` is bounded by
   `e^{O(R^k \cdot |\Lambda|)}` which the small probability dominates.
4. *Combine*: `\int e^{-2 V_a} d\mu^{\rm GFF} \le e^{small-field bound} + (rare event contribution) \le K(P, L, m)`.

This is the "dynamical-cutoff / small-and-large field decomposition"
argument from Glimm–Jaffe Ch. 8 and Simon Ch. I.

The infrastructure in `Pphi2/NelsonEstimate/SmoothLowerBound.lean`
and `Pphi2/NelsonEstimate/RoughErrorBound.lean` already encodes this
machinery, but it is not currently load-bearing — the easy
pointwise-bound proof short-circuits it. With the new normalization,
those files would actually need to be wired into a proper proof.

### 5.6 Other downstream effects

* **`continuumLimit_nonGaussian` and `pphi2_nontriviality`** become
  *true* (in principle) and dischargeable — once the interaction is
  nontrivial, the connected 4-point function is nonzero, and the
  limit measure is non-Gaussian. Discharging these axioms is a
  separate piece of work but it becomes possible.
* **`torus_propagator_convergence`** is unchanged — only the *free*
  2-point function is involved, and the embedding adjusts so the
  same continuum limit `(-Δ + m²)^{-1}` is reached.
* **`torus_interacting_tightness`** (Cauchy–Schwarz density transfer)
  remains structurally the same: bound interacting moments by
  Gaussian moments times `\sqrt{K}` from Nelson's estimate. The new
  Nelson estimate is harder to prove but its conclusion has the same
  form, so the consumers don't change.
* **OS0, OS1, OS2 theorems** (`torusInteracting_os{0,1,2_translation,2_D4}`)
  retain their proofs. They use the existence of a uniform exponential
  moment bound — that bound is still true under the new Nelson estimate.
* **Routes A, B′, and pphi2N** all need the lattice-action change at
  the gaussian-field level, then their respective Nelson-estimate
  consumers need to be re-wired.

---

## 6. Phasing

### Phase 0 (now, before code) — vetting

**Open questions for Gemini deep-think / Codex review** (§7).
**No code changes** until the diagnosis and fix plan are validated.

### Phase 1 — gaussian-field action change

* Modify `gaussian-field/Lattice/Covariance.lean:99` to use the
  `a^d`-rescaled covariance.
* Update `lattice_cross_moment` and friends.
* Update `wickConstant` in `Pphi2/WickOrdering/Counterterm.lean`
  (move the definition to gaussian-field if appropriate, since it's
  inherently tied to the lattice covariance; or recompute it in
  pphi2 using the new lattice covariance).
* Drop or restate `wickConstant_le_inv_mass_sq` — it is no longer true.
* Update lemmas `wickConstant_pos`, `wickConstant_antitone_mass`, etc.
  with the new normalization.

Estimated cost: ~1–2 weeks; many small downstream re-proofs but no
new mathematics.

### Phase 2 — Nelson's estimate proper

* Wire `Pphi2/NelsonEstimate/SmoothLowerBound.lean` and
  `RoughErrorBound.lean` into a real proof of
  `nelson_exponential_estimate_lattice`.
* Glimm–Jaffe Ch. 8 / Simon Ch. I provides the textbook proof.
* Pphi2 has the infrastructure files already drafted but they are not
  currently consumed by the headline theorem.

Estimated cost: ~2–4 weeks of focused work; this is the real
constructive-QFT mathematical content of the project. The hardest
single piece in pphi2.

### Phase 3 — propagation through Routes A, B′, pphi2N

* Routes A and B′ inherit the action change automatically.
* Cauchy–Schwarz density transfer in `TorusInteractingLimit.lean`
  consumers still works.
* OS0–OS2 proofs in `TorusInteractingOS.lean` are mostly unchanged
  (they use the abstract uniform exponential moment bound, which
  remains true with a different `K`).
* `IRLimit/UniformExponentialMoment.lean` (Route B′) needs its
  exponential-moment hypothesis re-checked under the new `K`.
* PR #11's `cylinderIR_uniform_second_moment` derivation is
  scaling-invariant and survives.
* PR #12's HS / Fourier identities are normalization-independent
  and survive.

Estimated cost: ~1–2 weeks of mechanical updates after Phases 1–2.

### Phase 4 — discharge `continuumLimit_nonGaussian` and `pphi2_nontriviality`

With a nontrivial interaction, these axioms become provable from
the connected 4-point-function nonvanishing. Multi-week separate
work, but unblocked.

### Total estimated cost

~6–10 weeks of focused work to get from current state (free-field
limit) to a verified construction of the textbook P(φ)₂ in Lean.
Not counting Phase 4.

---

## 7. Open questions for Gemini deep-think / Codex vetting

Before any code changes, the following claims should be independently
checked.

**Q1.** Is the derivation of §3 (the implicit field identification
`\phi_x = a \Phi(x_a)` from propagator convergence) correct? Specifically:

* Does the embedding's `√a`-per-dimension factor (so `a` total in 2D)
  combined with the lattice covariance's `(M^{-1})_{xy}` give
  `\langle f, (-Δ + m^2)^{-1} g\rangle_{T^2_L}` in the continuum
  limit, *independently* of which scaling we use for `\phi_x`?
* Or does the propagator-convergence theorem already implicitly fix
  the field rescaling?

**Q2.** Is the Wick-polynomial rescaling in §3.2
(`:P(a\Phi):_{a^2 c} = a^{2k_{\rm top}} :P(\Phi):_c`) correct as a
universal fact about Wick polynomials and homogeneous monomials?

**Q3.** Under the proposed §5 fix:

* Is the textbook `wickConstant^{\rm GJ} = G_a(0,0)` indeed the right
  Wick subtraction for `:P(\phi):` to have the standard
  `O(1)` typical fluctuation?
* Does the Nelson-estimate proof from Glimm–Jaffe Ch. 8 / Simon Ch. I
  still apply to this normalization? (The standard one in Simon's
  notation has `S(\phi) = (1/2) \int (\nabla\phi)^2 + m^2 \phi^2 dx`
  — the natural action — which the lattice version with `a^d` weight
  approximates.)

**Q4.** Are there normalizations *between* pphi2's current and the
Glimm–Jaffe textbook that would also work? For example:

* Keep pphi2's action but rescale the polynomial coefficients of `P`
  by `a^{-2k_{\rm top}}` to compensate. Does this yield a sensible
  continuum theory?
* Keep pphi2's action but redefine the embedding so the embedded field
  carries the textbook scaling. Same question.

**Q5.** Has any other Lean formalisation of constructive QFT (or even
2D Gaussian field theory at the Wick-polynomial level) hit this
issue? Is there literature on the "right" Lean-friendly normalization
that we can cross-check?

**Q6.** Does this diagnosis explain anything that was previously
puzzling? E.g.:

* Was it surprising that pphi2's Nelson-estimate proof was so much
  easier than the textbook?
* Are there existing pphi2 results (cluster expansions, mass-gap
  bounds) that should have been hard but turned out trivial under
  the current normalization?

**Q7.** Is the cost estimate in §6 realistic, or is some piece (e.g.
the dynamical-cutoff Nelson-estimate proof) substantially more
involved than the rough estimate suggests?

---

## 8. Summary table

| Item | Current (broken) | Proposed (Glimm–Jaffe) |
|---|---|---|
| Lattice action `S` | `(1/2) ⟨φ, M_a φ⟩` (counting) | `(a^d / 2) ⟨φ, M_a φ⟩` (Riemann-sum) |
| Lattice variance `\mathbb{E}[\phi_x^2]` | `wickConstant ≈ a^d \cdot c_{\rm textbook}` (small) | `c_{\rm textbook} ≈ \log(1/(am))` (textbook) |
| `wickConstant ≤ m^{-2}` | True | **False** (`wickConstant \to \infty`) |
| Nelson's estimate proof | Uniform pointwise bound `V_a ≥ -L^2 A` (easy) | Dynamical cutoff / small-large-field decomposition (hard) |
| Continuum interaction `\lim V_a` | `0` (trivial) | `\int :P(\Phi):_{c_{\rm textbook}} dx` (nontrivial) |
| Limit measure | Free GFF | Interacting P(φ)₂ |
| `continuumLimit_nonGaussian` axiom | False | True (open, dischargeable) |
| `pphi2_nontriviality` axiom | False | True (open, dischargeable) |
| OS0, OS1, OS2 theorems | True (about free GFF) | True (about interacting measure) |

---

## 9. References

* Glimm and Jaffe, *Quantum Physics: A Functional Integral Point of
  View*, Springer 1987.
   * Ch. 6: OS axioms.
   * Ch. 8: Nelson's estimate via dynamical cutoff. The main reference
     for the textbook proof of the uniform exponential moment.
   * Ch. 19: Torus and infinite-volume limits.
* Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory*, Princeton 1974.
   * Ch. I: lattice approximation, Wick ordering, Nelson's estimate.
   * The cleanest exposition of the Cauchy–Schwarz density transfer.
* Guerra, Rosen, Simon, "The P(φ)₂ Euclidean field theory as classical
  statistical mechanics," *Ann. Math.* 101 (1975), 111–259.
   * The thermodynamic-limit and clustering-properties paper.
   * Cited by pphi2 in connection with `Bridge.lean`'s
     `schwinger_agreement` axiom.
* Nelson, "The free Markov field," *J. Funct. Anal.* 12 (1973),
  211–227.

For the lattice-action conventions specifically: Glimm–Jaffe Eq.
(6.1.6) for the standard discretization, Simon's Ch. I for the
Wick-constant convention, GRS Eq. (1.2)–(1.3) for the thermodynamic-
limit setup.
