# Discharge plan — non-triviality (the limit is genuinely interacting, not free)

Covers axioms **11 `pphi2_nontriviality`** and **9 `continuumLimit_nonGaussian`**. These are the
"it's actually a QFT, and an interacting one" axioms — easy to underestimate, and the place a
construction can silently degenerate to the free field. **The two are very different in
difficulty** (my INDEX over-rated 11):

## 11. `pphi2_nontriviality` — `S₂(f,f) > 0` for `f ≠ 0` — ★★ (NOT ★★★)

This is **not** non-Gaussianity; it only says the limit measure is **not the delta at 0**: the
two-point function `∫(ωf)² dμ > 0` for every nonzero test function. Clean route:

1. **Free lower bound.** The free (GFF) two-point is `S₂^free(f,f) = ⟨f, (−Δ+m²)⁻¹ f⟩ = ‖f‖²_{H⁻¹}
   > 0` for `f ≠ 0` — a positive-definite quadratic form (have the GFF covariance
   `latticeCovarianceAsymGJ` / `GaussianField.covariance`; positivity from `massOperatorAsym_pos_def`
   inverted, and `second_moment_asym_tendsto → asymTorusContinuumGreen` for the continuum value).
2. **Interacting ≥ free.** For an **even** interaction (`:P(φ):`, `P` even — φ⁴ is), the Griffiths /
   GKS correlation inequality gives `S₂^int ≥ S₂^free`. pphi2 **already has FKG infrastructure**
   (GaussianField `Lattice/FKG.lean`, `gaussianDensity_fkg_lattice_condition`), which is the same
   family of correlation inequalities — reuse/extend it for the two-point domination.
3. Combine: `S₂^int(f,f) ≥ S₂^free(f,f) > 0`, and pass to the continuum limit (moment convergence,
   already used for the existence axioms).

**Difficulty ★★:** the free positivity is essentially in hand; the only real work is the
domination inequality (FKG/Griffiths, partly built) + the limit. No phase-transition or
weak-coupling caveat — `S₂ > 0` holds in **all** phases. Discharge alongside the existence/OS0–OS2
chain.

## 9. `continuumLimit_nonGaussian` — `S₄ − 3·S₂² ≠ 0` — ★★★ (the genuine mountain)

The **connected four-point function** (fourth cumulant / Ursell `u₄`) is nonzero in the limit.
For a Gaussian measure all `n≥3` cumulants vanish, so `u₄ ≠ 0` *is* the proof that the theory is
interacting. This is the hard, essential non-triviality.

### Routes
1. **Lebowitz inequality + strict lower bound** (the constructive-QFT standard). For even
   ferromagnetic `:P(φ):`, the Lebowitz inequality gives `u₄ ≤ 0`. Non-triviality = `u₄ < 0`
   strictly, bounded away from 0 uniformly in the cutoff so it survives `a→0`. The **uniform strict
   lower bound `|u₄| ≥ c > 0` is the crux** — this is what distinguishes "interacting" from
   "free up to the limit."
2. **Perturbative** (Simon Ch. VIII, named in the docstring): `u₄ = −cλ + O(λ²)` for small coupling
   `λ`, hence `u₄ ≠ 0` for `0 < λ` small. Cleaner but **weak-coupling only**, and requires a
   rigorous remainder bound (the `O(λ²)` must be controlled — Nelson/hypercontractive estimates).
3. **Super-renormalizability shortcut for `d=2`.** φ⁴₂ needs only Wick ordering (no coupling/field
   renormalization), so `u₄` stays `O(λ)` with no cancellation — the limit `u₄` is the limit of the
   lattice `u₄`, and lattice `u₄ ≠ 0` is a finite computation + the strict Lebowitz bound. This is
   the most promising route: it localizes the hard part to a **uniform lattice `u₄` bound**.

### ⚠ Caveat
Requires the coupling to be **nonzero** (`P` genuinely quartic, `λ > 0`) — for `P = 0` the limit
*is* Gaussian and `u₄ = 0`. The axiom quantifies over all `P`; it should carry "P nontrivial / even
with positive top coefficient." Route 2's lower bound is weak-coupling; routes 1/3 aim for all `λ`
in the single-phase regime.

### Infrastructure to build/reuse
- **Wick / cumulant machinery** — pphi2 + GaussianField have substantial Wick infrastructure
  (`WickMultivariate.lean`, `gffMultiWickMonomial_*`, the proved Wick orthogonality); `u₄` is a
  Wick-ordered 4-point, so the cumulant bookkeeping is largely there.
- **Lebowitz/GKS inequalities** — extend the FKG/correlation-inequality infrastructure
  (`Lattice/FKG.lean`) to the 4-point Lebowitz inequality. This is the main new piece.
- **Moment convergence** — `continuum_exponential_moment_bound` (axiom 6) + tightness give the
  `S₄, S₂` limits; the cumulant survives if the lattice bound is uniform.

**Recommended:** route 3 (super-renormalizable + uniform lattice `u₄` via Lebowitz), restricted to
even `P` with `λ > 0`. Do a Gemini/literature design pass on the *uniform strict* `u₄` bound first
(the survival-in-the-limit is the subtle part), as for crux-2.

## Status / sequencing
- [ ] **11 `pphi2_nontriviality`** (`S₂>0`) — ★★; free positivity (have) + 2-pt domination (FKG,
  partly have) + limit. Do with the existence/OS chain, all phases.
- [ ] **9 `continuumLimit_nonGaussian`** (`u₄≠0`) — ★★★; the genuine interacting content. Lebowitz
  4-pt inequality + uniform strict lattice bound + moment convergence. Even `P`, `λ>0`. Design pass
  first.

References: Simon *P(φ)₂* Ch. V (Griffiths/FKG, two-point domination), Ch. VIII (perturbation,
non-Gaussianity); Glimm–Jaffe Ch. 4 (correlation inequalities), Ch. 12–14 (cluster expansion);
Lebowitz (1974, the `u₄ ≤ 0` inequality).
