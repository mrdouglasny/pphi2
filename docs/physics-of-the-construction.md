# The physics of the P(φ)₂ construction

*A physicist's reading of what the formalization is doing. This is the expository companion to the
mathematical plans (`cylinder-master-plan.md`, `cyl-1a-bridge-plan.md`) and to the
`gibbs-variational` dependency. Draft — to be expanded.*

The whole construction is the rigorous version of one physical statement: **the Euclidean
P(φ)₂ functional integral defines a quantum field theory with a finite, intensive vacuum energy
density.** Everything technical — the exponential-moment bounds, the Boué–Dupuis drift, the
volume-uniformity, the moment-determinacy uniqueness — is a sharpening of that one sentence.

## 1. The object: a Euclidean QFT as a probability measure

We build a probability measure `μ` on field configurations `φ ∈ S'(ℝ²)` (tempered distributions),
formally

```
dμ(φ)  =  Z⁻¹ exp(−S(φ)) Dφ,    S(φ) = ∫ ( ½(∂φ)² + ½m²φ² + :P(φ): ) d²x,
```

with `P` a polynomial bounded below (e.g. `λφ⁴`) and `:·:` Wick ordering — the *only*
renormalization needed in two dimensions, a finite (logarithmically divergent) mass
counterterm. Splitting `S = S_free + ∫:P(φ):`, the measure is a **tilt of the Gaussian free
field** `μ_C` (covariance `C = (−Δ + m²)⁻¹`):

```
dμ  =  Z⁻¹ exp(−V) dμ_C,    V = ∫ :P(φ): ,    Z = ∫ exp(−V) dμ_C.
```

In the formalization this is literally `interactingLatticeMeasure = Z⁻¹ · μ_C.withDensity(exp(−V))`
on a finite lattice (`InteractingMeasure/LatticeMeasure.lean`), pushed to the continuum/torus.
`Z` is the **partition function**, and

```
log Z  =  −E_vac · |Λ|
```

where `|Λ|` is the spacetime volume and `E_vac` the **vacuum energy density**. The cylinder
`Λ = S¹(L_s) × ℝ(L_t)` has volume `L_s · L_t`; the infinite-volume limit is `L_t → ∞`.

## 2. Integrability = an energy–entropy (free-energy) argument

To make sense of `μ` we must control `Z` — show `V` is exponentially integrable against `μ_C` and
that `Z` stays bounded away from `0` and `∞`. The clean modern way to do this is **not** a cluster
expansion but a **variational (free-energy) principle**: the Gibbs / Donsker–Varadhan inequality
and its Gaussian specialization, the **Boué–Dupuis formula** (formalized in `gibbs-variational`,
`neg_log_integral_exp_neg_le`):

```
−log Z  =  −log ∫ e^{−V} dμ_C   ≤   inf_h [ ∫ V(· + h) dμ_C  +  ½‖h‖²_C⁻¹ ].
```

This is exactly a **free-energy minimization**, `F = −log Z = min (energy − entropy gain)`:

| Boué–Dupuis term | Thermodynamic / field-theory meaning |
|---|---|
| `½‖h‖²` (Cameron–Martin cost) | **classical free action** of a background field `φ_cl = h`: `∫ (½(∂φ_cl)² + ½m²φ_cl²)` — the kinetic + mass penalty for turning on a background |
| `∫ V(· + h) dμ_C` (shifted potential) | **interaction of the quantum fluctuations** `η` (the unshifted GFF) **with the background**: `⟨V(φ_cl + η)⟩_η` |
| the `inf_h` | the **saddle point / classical equations of motion** — choose the best background |

So Boué–Dupuis *is* the **background-field method**: write `φ = φ_cl + η`, pay the classical
action for the background, average the interaction over the fluctuation. The right-hand side is the
one-loop effective action evaluated around `φ_cl`, and the inequality says it upper-bounds the true
free energy. The drift `h` is the rigorous incarnation of the background field; choosing it to
**cancel the most singular Wick-ordered part of `V`** is the renormalization, done variationally
rather than diagrammatically. (Physicists know this same inequality as Peierls–Bogoliubov /
Gibbs–Bogoliubov–Feynman, the Feynman polaron variational bound, and the tree-level background-field
method — see the `gibbs-variational` README.)

The "entropy" half is literal: the Donsker–Varadhan dual `log ∫ e^f dμ = sup_ν (∫ f dν − KL(ν‖μ))`
trades the log-partition function against the **relative entropy** `KL(ν‖μ)`; the optimal tilt is
the Gibbs measure, and for a Gaussian the entropy cost of a shift is precisely the Cameron–Martin
norm. Integrability of the interacting measure is therefore an energy-vs-entropy balance, not a
combinatorial miracle.

## 3. Volume-uniformity = extensivity of the vacuum energy

The hard part of the infinite-volume (`L_t → ∞`) limit is **uniformity**: the bound on `Z^{1/|Λ|}`
must not degrade as the cylinder grows. Physically this is the demand that **`E_vac` be intensive** —
finite per unit volume, independent of how big the universe is. A bound that blew up with `L_t`
would say the vacuum energy *density* grows with the size of spacetime, a physical absurdity
signalling that the UV and IR regularizations failed to decouple.

The Boué–Dupuis formula delivers this through **locality**:

1. The interaction is **ultralocal**: `V = ∫_Λ :P(φ(x)): d²x` — the integrand at `x` depends only
   on the field at `x`.
2. Choose the background-field Ansatz `h(x)` to depend only on the fluctuations `η(y)` within a
   **finite physical radius** of `x`. Then both Boué–Dupuis terms become a single spatial integral
   of a **local energy-density operator** `H(x)`:
   ```
   ⟨S_eff[φ_cl, η]⟩  =  𝔼[ ∫_Λ H(x) d²x ]  =  ∫_Λ 𝔼[H(x)] d²x.
   ```
3. The free field `μ_C` is **translation-invariant** (periodic on `S¹`, stationary along `ℝ`), so
   `𝔼[H(x)] = C` is a **constant, intensive scalar**, independent of `x`.
4. Hence the integral is purely **extensive**:
   ```
   −log Z  ≤  C · |Λ|  =  C · (L_t · L_s).
   ```
   Dividing by the volume, the `L_t` **cancels exactly** — the per-volume bound is uniform in `L_t`.

The physics: because the interaction is strictly local, the UV divergences can be **screened
locally** — the cost of the local counterterm/background is paid pointwise, with no reference to the
total spacetime volume — and the local screening cost integrates up to a purely extensive total
energy. This is the content of the cylinder requirement **CYL-1a** (`MeasureHasGreenMomentBound`),
and the route to discharging it is `cyl-1a-bridge-plan.md`: whiten the lattice GFF to a standard
Gaussian, apply the finite-dimensional Boué–Dupuis bound with a local Wick-cancelling drift, and
read off the extensive (hence `L_t`-uniform) constant.

## 4. Uniqueness = moment-determinacy from finite vacuum fluctuations

Once the exponential moments are controlled, the limiting theory is **unique**: the measure is
determined by its Schwinger functions (correlation functions). Physically, finite exponential
moments mean the field has **sub-Gaussian tails** — the vacuum fluctuations are not too wild — and
this is exactly the Carleman condition that makes the moment problem *determinate*. A theory with
heavier tails could admit different measures with identical correlation functions; the Nelson /
Boué–Dupuis bound rules that out. Formally (`MeasureUniqueness.lean`, `measure_eq_of_moments`,
discharging `measure_determined_by_schwinger`): the finite exponential moment makes the generating
functional `Z[f] = ∫ e^{iφ(f)} dμ` **entire**, so it equals its Taylor series in the Schwinger
functions; equal correlation functions ⟹ equal generating functional ⟹ equal measure. No Gaussian
structure is used — only the finiteness of the vacuum fluctuations.

## 5. The dictionary

| Formalization | Physics |
|---|---|
| `Z = ∫ exp(−V) dμ_C` (partition function) | `exp(−E_vac |Λ|)`, vacuum energy |
| `neg_log_integral_exp_neg_le` (Boué–Dupuis) | variational free energy = background-field method |
| Cameron–Martin cost `½‖h‖²` | classical action of the background field |
| `∫ V(·+h) dμ_C` | fluctuation interaction in the background |
| drift `h` cancelling the Wick singularity | renormalization / local UV screening |
| `L_t`-uniform `MeasureHasGreenMomentBound` (CYL-1a) | intensive (extensive-total) vacuum energy |
| translation invariance of `μ_C` | `𝔼[H(x)]` constant ⟹ extensivity |
| `measure_eq_of_moments` (moment determinacy) | sub-Gaussian tails ⟹ Schwinger functions determine the theory |
| five OS axioms | reconstruction of a Wightman QFT with a mass gap |

---

*Status: initial draft. Natural extensions — the OS → Wightman reconstruction in physics terms
(mass gap = spectral gap of the transfer matrix = exponential clustering), and the rotation
anomaly `O(a²|log a|^p)` as the lattice artifact in OS2.*
