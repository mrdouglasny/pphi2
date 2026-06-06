# Discharge plan — non-triviality (the limit is genuinely interacting, not free)

Covers axioms **11 `pphi2_nontriviality`** and **9 `continuumLimit_nonGaussian`**. These are the
"it's actually a QFT, and an interacting one" axioms — easy to underestimate, and the place a
construction can silently degenerate to the free field. **The two are very different in
difficulty** (my INDEX over-rated 11):

## 11. `pphi2_nontriviality` — `S₂(f,f) > 0` for `f ≠ 0` — ★★ (NOT ★★★)

This is **not** non-Gaussianity; it only says the limit measure is **not the delta at 0**: the
two-point function `∫(ωf)² dμ > 0` for every nonzero test function. Clean route:

⚠️ **ROUTE CORRECTED 2026-06-04 (Gemini deep-think vetting — see memory `pphi2-s2-domination-direction`).**
The original route below (step 2: "Griffiths/FKG ⟹ `S₂^int ≥ S₂^free`") is **WRONG-DIRECTION** and
must not be formalized:
- **GKS/Griffiths does NOT give `S₂^int ≥ S₂^free`.** Adding a local `λφ⁴` term does not increase the
  ferromagnetic cross-couplings `J_{xy}φ_xφ_y`; it narrows the single-site measure, which *decreases*
  correlations. GKS II monotonicity is in the *cross-couplings*, not the single-site potential.
- **The direction depends on Wick ordering.** Non-Wick-ordered φ⁴: `S₂^int ≤ S₂^free` (Lebowitz
  monotone-decreasing in λ — Simon Cor IV.10). Wick-ordered at weak coupling: `S₂^int > S₂^free`
  *strictly*, but via the **counterterm** `:φ⁴: = φ⁴ − 6cφ²` (the `−6cφ²` enhances fluctuations) —
  `S₂''(0) = 96∫(Cf)C³(Cf) > 0` by Schur-product positivity of `C³`. **No global correlation
  inequality** gives the comparison for all λ.
- The proved `asymInteractingVariance_le_freeVariance` is the **upper** bound `S₂^int ≤ C·S₂^free`
  (Glimm–Jaffe Thm 10.3.1) — the *wrong* direction for a lower bound; it cannot supply nondegeneracy.

**Corrected route for `S₂^int(f,f) > 0` (non-degeneracy):**
1. **Free lower bound** (unchanged): `S₂^free(f,f) = ‖f‖²_{H⁻¹} > 0` for `f≠0` — in hand
   (`massOperatorAsym_pos_def`, `second_moment_asym_tendsto → asymTorusContinuumGreen`).
2. **Finite-lattice lower bound via GKS II decoupling**: drop the ferromagnetic kinetic couplings
   `J_{xy}=1/a² ≥ 0` (GKS II ⟹ `⟨φ_x²⟩_int` decreases when `J→0`), giving `⟨φ_x²⟩_int ≥` the
   *decoupled* single-site variance `v > 0`. Valid for `f ≥ 0`. **But `v → 0` as `a → 0`** — does not
   survive the continuum limit by itself.
3. **Continuum non-degeneracy** is genuinely hard — the constructive routes are (i) the
   **short-distance singularity** `S₂(x,y) ∼ −(2π)⁻¹ log|x−y|` (super-renormalizable ⟹ same leading
   singularity as free ⟹ not δ₀), or (ii) **Reeh–Schlieder** after the OS axioms via the **cluster
   expansion** (Simon Thm VI.1.2, Ch VII).

**Difficulty reassessed ★★ → ★★★** for the *continuum* lower bound (the finite-lattice/free parts are
in hand, but the surviving-the-limit lower bound needs cluster-expansion-grade machinery, not FKG).
Still holds in all phases (no weak-coupling caveat for non-degeneracy itself).

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
