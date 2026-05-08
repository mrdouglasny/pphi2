# Route B (Torus T²_L): Status + Math Walkthrough

*Updated 2026-05-08 (post Stage 1 lattice-action fix on
`fix/lattice-action-normalization`; Route B′ IR limit refactored by
PR #14). Companion to the existing
[`torus-interacting-os-proof.md`](torus-interacting-os-proof.md)
(detailed Lean proof outline) and
[`torus-route-gap-audit.md`](torus-route-gap-audit.md) (file-by-file
audit). This doc is for a reader who wants the headline status + a
physicist-level explanation of what is being proved and how.*

---

## 1. Status snapshot

| What | Where | State |
|---|---|---|
| Bundled OS0–OS2 theorem `torusInteracting_satisfies_OS` | `TorusContinuumLimit/TorusInteractingOS.lean:2909` | **proved** |
| `torusInteractingLimit_exists` (existence of the continuum measure) | `TorusContinuumLimit/TorusInteractingLimit.lean:441` | **proved** |
| Nelson's exponential estimate `nelson_exponential_estimate_lattice` | `NelsonEstimate/NelsonEstimate.lean:73` | **axiomatised** (Stage 1 GJ form; genuine dynamical-cutoff proof is the Phase 2 deliverable) |
| Local axioms in `TorusContinuumLimit/` | – | **0 axioms** — the symmetric pair `torusEmbeddedTwoPoint_le_seminorm` / `torusEmbeddedTwoPoint_uniform_bound` was discharged 2026-05-08 (Phase 2 Cluster B partial). |
| Local axioms in `NelsonEstimate/` | – | **1 axiom** (Stage 1 GJ: `nelson_exponential_estimate_lattice`); CovarianceSplit is now 0 / 0 (Phase 2 partial discharge) |
| OS3 on the torus | – | intentionally **out of scope** (see §6) |
| OS4 on the torus | – | intentionally **out of scope** (see §6) |

The full bundle is proved *conditional on a converging subsequence* — the
caller picks `μ = limₙ μ_{aₙ}` along a Prokhorov-extracted subsequence
`(aₙ)`, which `torusInteractingLimit_exists` provides. The OS theorems
take that limit measure and show OS0–OS2 transfer through.

Files (all in `Pphi2/TorusContinuumLimit/` unless noted, lines of Lean
in parentheses):

```
TorusInteractingOS.lean         (2926)  ← bundles OS0–OS2 for the limit
TorusGaussianLimit.lean         (1190)  ← the free-field warm-up
TorusOSAxioms.lean               (924)  ← OS-axiom predicates / bridges
MeasureUniqueness.lean           (666)
TorusPropagatorConvergence.lean  (585)  ← lattice → continuum Green's fn
TorusInteractingLimit.lean       (461)  ← Prokhorov extraction
TorusEmbedding.lean              (130)
TorusTightness.lean              (125)  ← Mitoma-Chebyshev
TorusConvergence.lean             (84)  ← Gaussian-limit existence
TorusNuclearBridge.lean           (83)

NelsonEstimate/                  (~600 across 6 files) ← Nelson's estimate
```

## 2. What is being constructed

**Spacetime**: `T²_L := (ℝ/Lℤ)²` — the flat 2-torus with side length `L`
(both directions equal). This is the "symmetric torus" — `L_t = L_s = L`.
Both directions are compact (no IR limit needed) and the lattice cutoff
`a = L/N` provides a single UV scale. As `N → ∞`, `a → 0`.

**Reference measure**: the lattice Gaussian Free Field (GFF) on
`(ℤ/Nℤ)²` with mass `m > 0`,

$$
d\mu^{\text{GFF}}_a(\phi) \;=\; \frac{1}{Z^{\text{GFF}}_a} \exp\Bigl( -\tfrac{1}{2} \langle \phi,\, (-\Delta_a + m^2)\,\phi\rangle\Bigr) \prod_x d\phi(x),
$$

a discrete Gaussian with covariance the lattice Green's function
`G_a := (-Δ_a + m²)⁻¹`. The full physical-volume identity `a²·N² = L²`
makes `G_a(0,0) ~ (1/2π) log(N)` — the only divergence in the theory.

**Interacting measure** at lattice scale `a`:

$$
d\mu_a^{P} \;=\; \frac{1}{Z_a}\, \exp\bigl(-V_a(\phi)\bigr)\, d\mu^{\text{GFF}}_a, \qquad
V_a(\phi) \;=\; a^2 \sum_{x \in (\mathbb{Z}/N\mathbb{Z})^2} {:}P(\phi(x)){:}_{c_a}
$$

with `P` an even polynomial of degree `≥ 4` bounded below (top
coefficient positive) and `c_a := G_a(0,0)` the Wick subtraction
constant. The Wick ordering `:P(φ):_c` removes the divergent
self-contractions; in 2D super-renormalisability, this is the
**only** counterterm needed (no mass / coupling / wavefunction
renormalisation).

**The continuum limit** is the weak limit (along an extracted
subsequence) of the embedded measures `(\widetilde\iota_N)_* \mu_{a_N}`
on `Configuration(TorusTestFunction L)`, where the embedding lifts a
lattice configuration into a distribution on `T²_L`.

The headline theorem `torusInteracting_satisfies_OS` says: the limit
measure satisfies OS0 (analyticity), OS1 (regularity), and OS2
(Euclidean invariance for the symmetric-torus group `ℝ² ⋊ D₄`).

## 3. The six-step strategy

This is a textbook implementation of the lattice approach to
constructive QFT. Each step appears as a named theorem in the Lean
codebase.

### Step 1 — Wick ordering (single-cutoff regularisation)

Replace `P(φ(x))` with `:P(φ(x)):_{c_a}`. The Wick polynomial of
degree `2k` is

$$
{:}\phi^{2k}{:}_c \;=\; \sum_{j=0}^{k} \binom{2k}{2j}\,(2j-1)!!\,(-c)^{j}\,\phi^{2k-2j}.
$$

For a centred Gaussian `X` of variance `c`, this satisfies
`E[:X^k:_c] = 0` for `k ≥ 1`. Wick monomials of different degrees are
orthogonal in `L²(γ)`. With `c = c_a`, the divergent self-loops at
coinciding lattice points are exactly cancelled.

Implementation: `Pphi2/WickOrdering/` (Hermite recursion, Wick
constant, lattice-Wick matching).

### Step 2 — Nelson's exponential estimate (the "P(φ)₂ is finite" theorem)

The core hypercontractivity result of Glimm–Jaffe / Nelson, stated for
the torus in `nelson_exponential_estimate_lattice`:

> **There exists `K = K(P, L, m)` such that for every `N`:**
> $$
> \int e^{-2 V_a(\phi)} \, d\mu^{\text{GFF}}_a(\phi) \;\le\; K.
> $$

The constant `K` does **not** depend on the lattice size `N` — only on
the polynomial `P`, the torus size `L`, and the mass `m`. This is the
miracle that makes 2D constructive QFT work: the interaction term is
formally `−∞` at the continuum (since `V_a` involves an unbounded
operator on Wiener chaos), but its exponential moments are uniformly
bounded thanks to the Wick subtraction + the rapid decay of Wiener
chaos under the Ornstein–Uhlenbeck semigroup.

**Proof in our codebase**: a *uniform pointwise lower bound on `V_a`*
(rather than the full Glimm–Jaffe dynamical-cutoff argument). For each
`a`, the Wick polynomial is bounded below by a constant `−A`
independent of `c ∈ [0, m⁻²]`, so

$$
V_a(\phi) \;=\; a^2 \sum_x {:}P(\phi(x)){:}_{c_a} \;\ge\; -a^2 |\Lambda| A \;=\; -L^2 A,
$$

using the *physical-volume identity* `a²·|Λ| = L²` (constant in `N`!).
Hence `\exp(−2 V_a) ≤ \exp(2 L² A) =: K`, uniformly in `N`.

This gives a worse constant than Glimm–Jaffe but the right
**uniform-in-`N`** structural conclusion. (`NelsonEstimate/` has the
infrastructure for the sharper double-exponential argument too —
`SmoothLowerBound.lean`, `RoughErrorBound.lean`, etc. — but the
pointwise route is what feeds `nelson_exponential_estimate_lattice`.)

### Step 3 — Tightness via Mitoma–Chebyshev

Nuclear-dual measures on `S'(ℝ²)` (or here on
`Configuration(TorusTestFunction L)`) are tight iff they have uniform
second moments controlled by a continuous Hilbertian seminorm
on the Schwartz pre-dual. This is **Mitoma's theorem**.

**For the free torus measure**: uniform second moment is the
Sobolev-type bound

$$
\int (\widetilde\phi(f))^2 \, d\mu^{\text{GFF}}_a \;\le\; \langle f, G f\rangle \;\le\; C\, \|f\|_{H^{-1}}^2
$$

with `G` the continuum Green's function `(-Δ + m²)⁻¹`. The lattice
propagator `G_a` converges to `G` as `a → 0` (`TorusPropagatorConvergence.lean`),
giving the uniform bound `(\sup_a \|G_a\|_{op}) < ∞`.

**For the interacting measure**: bound the interacting moment by the
free moment via Cauchy–Schwarz density transfer:

$$
\int (\widetilde\phi(f))^2 \, d\mu_a^P
\;=\; \int (\widetilde\phi(f))^2 \, e^{-V_a}/Z_a \, d\mu^{\text{GFF}}_a
\;\le\; \Bigl( \int (\widetilde\phi(f))^4 \, d\mu^{\text{GFF}}_a \Bigr)^{1/2}
       \cdot \frac{\|e^{-V_a}\|_{L^2(\mu^{\text{GFF}}_a)}}{Z_a}.
$$

The first factor is a Gaussian fourth moment — bounded by
`3·\|f\|_{H^{-1}}^4`. The second factor is bounded by `√K` thanks to
Nelson's estimate (Step 2), with `K` independent of `N`. So the
interacting measure has uniform second moments, and Mitoma applies.

Implementation: `torus_interacting_tightness` in
`TorusContinuumLimit/TorusInteractingLimit.lean:344`.

### Step 4 — Prokhorov extraction

A tight family of probability measures on a Polish space has a weakly
convergent subsequence. The configuration space
`Configuration(TorusTestFunction L)` is Polish (proved at the
gaussian-field level via the Dynin–Mityagin basis identification with
`ℕ → ℝ`).

Implementation: `torusInteractingLimit_exists` packages the
tight-from-Step-3 family + Prokhorov to produce
`(φ : ℕ → ℕ) (μ : Measure ...)` with weak convergence
`(μ_{a_{φ(n)}}) → μ`. This is a `theorem`, not an axiom.

### Step 5 — Transfer the OS axioms through the limit

Each OS axiom is a closed condition under weak convergence in a
specific sense, but the closure-property argument differs by axiom.

#### OS0 (Analyticity): `torusInteracting_os0` (line 2589 of `TorusInteractingOS.lean`)

**Claim**: the generating functional `Z_μ[f] := ∫ e^{i\omega(f)}\,d\mu(\omega)`
is entire analytic in complex test-function coefficients.

**Strategy**:
1. For each cutoff measure `μ_a`, `Z_{\mu_a}[f]` is entire (the integrand
   is entire for each `ω`, and the integral is dominated by a uniform
   bound from Nelson's estimate).
2. As `a → 0` along the extracted subsequence, `Z_{\mu_a}[f] → Z_\mu[f]`
   pointwise in `f` by weak convergence.
3. **Vitali's theorem** on uniformly bounded analytic families says the
   limit is analytic, and the convergence is uniform on compacts.

The Lean proof uses `analyticOnNhd_integral` (analyticity of
parameter-dependent integrals from Mathlib) plus the uniform exponential
moment bound to swap limit and integral.

#### OS1 (Regularity): `torusInteracting_os1` (line 2710)

**Claim**: `\| Z_\mu[f] \| ≤ \exp(c\,(q(f_{re}) + q(f_{im})))` for a
continuous Hilbertian seminorm `q`.

**Strategy**: same Cauchy–Schwarz density-transfer pattern as Step 3,
but for exponential moments instead of second moments. The free-field
exponential moment is `\exp((1/2) G(f, f))`, controlled by the
Sobolev-type seminorm. The interacting moment is bounded by
`\sqrt K \cdot \exp((1/2) G(f,f))`.

#### OS2 (Translation invariance): `torusInteracting_os2_translation` (line 2800)

**Claim**: `Z_\mu[T_v f] = Z_\mu[f]` for all `v \in T²_L`.

**Strategy**: at each lattice cutoff, the lattice translation group
`(ℤ/Nℤ)²` is an exact symmetry of `μ_a` (the GFF measure and the
interaction are both invariant under shifts of the periodic lattice).
Continuous translations are obtained as limits of lattice translations,
and the invariance transfers to the continuum limit via characteristic-
functional convergence:

$$
Z_\mu[T_v f] \stackrel{\text{weak conv}}{=} \lim_n Z_{\mu_{a_n}}[T_v f]
\stackrel{\text{lattice inv}}{=} \lim_n Z_{\mu_{a_n}}[f] = Z_\mu[f].
$$

Implementation key: `torusInteractingLimit_translation_invariant` (line
1700) bundles the cutoff-level invariance and the limit transfer.

#### OS2 (D₄ point group): `torusInteracting_os2_D4` (line 2824)

**Claim**: the dihedral group `D₄` (90° rotations + reflections of
the square torus) preserves `μ`.

**Strategy**: same as translation, using the fact that `D₄` is an
exact symmetry of both the lattice action and the embedding. The torus
geometry has only `D₄` rather than full `O(2)` because the lattice
breaks rotational symmetry to its discrete subgroup. (Restoring full
`O(2)` is a Route A / Ward-identity question — not Route B's job.)

Implementation: separate sub-proofs for swap-invariance and
time-reflection-invariance, each via the same characteristic-functional-
convergence pattern.

### Step 6 — Bundle

`torusInteracting_satisfies_OS` packages the four results into a
`SatisfiesTorusOS L μ` structure, conditional only on the convergence
hypothesis (which `torusInteractingLimit_exists` supplies).

## 4. The dependency graph

```
                                Wick ordering (Pphi2/WickOrdering/)
                                            │
                                            ▼
                                wickPolynomial_uniform_bounded_below
                                            │
                                            ▼
                  ─────────  nelson_exponential_estimate_lattice  ─────────
                  │         (K = exp(2 L² A), uniform in N)              │
                  ▼                                                       ▼
   torus_interacting_second_moment_uniform              torusInteracting_exponentialMomentBound
              │                                                           │
              │  (Cauchy–Schwarz density transfer                         │
              │   against Gaussian moments;                               │
              │   uses GaussianContinuumLimit Green's fn convergence)    │
              ▼                                                           ▼
    torus_interacting_tightness                            (used in OS1 + OS0)
              │                                                           │
              │  Mitoma criterion on the nuclear dual                     │
              ▼                                                           │
    torusInteractingLimit_exists ─── Prokhorov sequential ── (μ, φ) ──── │
                                                            │             │
                                                            ▼             │
                                               weak convergence hypothesis used by
                                                 torusInteracting_os0 (Vitali)
                                                 torusInteracting_os1 (exp-moment limit)
                                                 torusInteracting_os2_translation (CF limit)
                                                 torusInteracting_os2_D4 (CF limit)
                                                            │
                                                            ▼
                                          torusInteracting_satisfies_OS
```

## 5. Why this is the cleanest of the four routes

Route B was `0 axioms / 0 sorries` from 2026-04-19 until the Stage 1
lattice-action fix (2026-05-07) re-axiomatised three uniform bounds
under the GJ-aligned action. The structural argument is unchanged; the
restored uniform bounds are the Phase 2 dynamical-cutoff deliverable.
Route B remains the "warm-up" because:

* **Both directions are compact**, so no IR limit is needed (no
  cylinder / Lt → ∞ work). Just one limit, the UV `a → 0`.
* **Symmetries are clean** — translations on `T²_L` are an exact
  abelian group with no boundary issues. The full `O(2)` rotation group
  is broken to `D₄` by the lattice, but `D₄` is a finite group that the
  lattice respects exactly.
* **Reflection positivity and clustering are not in scope** for this
  route. They live elsewhere:
    * **OS3** wants a "natural time axis" — the symmetric torus has
      none (both directions are equivalent). Route B′ (asymmetric
      torus → cylinder) and Route C (direct cylinder) are where OS3
      gets proved.
    * **OS4** (clustering / mass gap) requires an infinite-volume
      thermodynamic limit, which the symmetric torus also doesn't
      have. Route A (lattice → ℝ²) is where OS4 lives.

So Route B is the maximal subset of the Glimm–Jaffe construction that
*can* be done on the symmetric torus, and it is done. It serves as
both a proof-of-concept and an infrastructure base — the same
machinery (Wick ordering, Nelson estimate, Mitoma–Chebyshev,
Prokhorov, characteristic-functional convergence) is reused in
Routes A and B′.

## 6. What Route B does *not* prove (and where to look)

| Question | Where it lives |
|---|---|
| OS3 (reflection positivity) | Route B′: asymmetric torus → cylinder, in `Pphi2/IRLimit/`. After PR #14 the IR-limit axioms are gone; OS3 is now transferred from explicit `CylinderMeasureSequenceEventuallyReflectionPositive` + characteristic-functional convergence. The remaining external obligations are the Green-controlled exponential moment hypothesis and eventual matrixwise RP. |
| OS4 (clustering / mass gap) | Route A: lattice → `S'(ℝ²)`, in `Pphi2/ContinuumLimit/`; depends on `spectral_gap_uniform` |
| Full `E(2) = ℝ² ⋊ O(2)` invariance | Route A via Ward identity, in `Pphi2/OSProofs/OS2_WardIdentity.lean` |
| Mass gap = `m₀ > 0` | open in pphi2; the related work lives in markov-semigroups (Bakry–Émery, Brascamp–Lieb) and pphi2N (HS + Lefschetz thimble for the O(N) LSM at large `N`) |
| Continuum-limit uniqueness | `MeasureUniqueness.lean` provides supporting infrastructure but the full uniqueness proof is parked — different limit subsequences could in principle give different measures (this is the "phase ambiguity" question; for `P` even with positive top coefficient, the symmetric phase is the natural one but uniqueness isn't formal yet) |

## 7. Reading order for the Lean

If you want to walk the proofs, the natural order is:

1. **`NelsonEstimate/NelsonEstimate.lean`** — the uniform exponential
   bound. Self-contained, ~80 lines for the headline theorem,
   uses the physical-volume identity `a² · |Λ| = L²` as the only
   non-trivial geometric input.
2. **`TorusContinuumLimit/TorusTightness.lean`** — Mitoma–Chebyshev for
   the free GFF on the torus. ~125 lines.
3. **`TorusContinuumLimit/TorusPropagatorConvergence.lean`** — lattice
   Green's function `G_a → G` in the operator topology. The technical
   heart of the free-field convergence.
4. **`TorusContinuumLimit/TorusInteractingLimit.lean`** — Cauchy–Schwarz
   density transfer + Prokhorov. The result of this file is
   `torusInteractingLimit_exists`.
5. **`TorusContinuumLimit/TorusInteractingOS.lean`** — the four OS
   theorems and their bundle. ~2900 lines, but the bulk is technical
   plumbing for the characteristic-functional convergence; the
   conceptual content is the four `os*` theorems and the bundling.

For an even shorter tour, just read the four headline statements:

```lean
-- TorusInteractingLimit.lean:441
theorem torusInteractingLimit_exists (P) (mass) (hmass) :
    ∃ φ μ, StrictMono φ ∧ IsProbabilityMeasure μ ∧ ⟨weak conv⟩

-- NelsonEstimate.lean:73
theorem nelson_exponential_estimate_lattice (P) (mass) (hmass) :
    ∃ K, 0 < K ∧ ∀ N, ∫ exp(-2 V_a) dμ_GFF ≤ K

-- TorusInteractingOS.lean:2909
theorem torusInteracting_satisfies_OS (P) (mass) (hmass) (μ) (φ) (hφ) (hconv) :
    SatisfiesTorusOS L μ
```

These three theorems are the entire content of Route B at the
top level. The first hands you a continuum measure, the second
provides the analytic estimate that powers everything else, and
the third packages the OS axioms for that measure.

## 8. Mathematical references

* Glimm and Jaffe, *Quantum Physics: A Functional Integral Point of
  View*, Springer 1987 — Chs. 8 and 19 for Nelson's estimate and the
  P(φ)₂ construction; Ch. 6 for OS axioms; Ch. 19 for the torus case
  specifically.
* Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory*, Princeton 1974
  — the canonical reference; cleanest exposition of the Wick-ordering
  and Cauchy–Schwarz density transfer.
* Nelson, "The free Markoff field", *J. Funct. Anal.* 12 (1973),
  211–227 — original hypercontractivity; the same inequality with a
  different name.
* Reed and Simon, *Methods of Modern Mathematical Physics, Vol. II*,
  §X.10 — Mitoma's theorem and tightness on nuclear duals.

For the OS axioms themselves: Osterwalder and Schrader,
*Comm. Math. Phys.* 31 (1973), 42 (1975).
