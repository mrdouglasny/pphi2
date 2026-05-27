# Nelson bridge generalization (B-lean) — heterogeneous cutoff exp-moment bound

*2026-05-27. Plan for Phase-2 #3 (the Nelson cutoff exp-moment bound on the isotropic
`Z_Nt × Z_Ns` lattice), via **option B-lean**: generalize the shape-agnostic bridge engine
over the target lattice, and supply the heterogeneous polynomial-chaos setup as a single
vetted axiom (the analytic Glimm–Jaffe input), to be discharged later by porting the core.*

## The discovery that sets the scope

The square Nelson estimate `nelson_exponential_estimate_master` is a **fully-proved theorem,
0 axioms** (the one axiom in `NelsonEstimate/` — `nelson_exponential_estimate_master_bounded`,
the `a ≤ 1` compatibility wrapper — is *not* in its dependency chain). But it sits on
~15.5K lines of square-specific polynomial-chaos / Fourier / heat-kernel machinery
(`FieldDecomposition` 4.2K, `RoughErrorBound` 3.9K, `CovarianceBoundsGJ` 1.6K, …), all on
`Fin d → Fin N` Fourier modes. Re-deriving all of that for `Z_Nt × Z_Ns` is weeks — so B-lean.

## The traced chain (what calls what)

```
asymNelson_exponential_estimate (old, square-via-geomMean)         [to replace]
  := nelson_exponential_estimate_master (d:=2) ... (L := √(Lt·Ls))
nelson_exponential_estimate_master := polynomial_chaos_exp_moment_bridge          (theorem)
  := polynomial_chaos_exp_moment_bridge_bounded
       ← canonicalSmoothInteraction_lower_bound_at_cutoff_uniform   (RoughErrorBound:350, thm)
       ← canonicalRoughError_cutoff_tail_uniform                    (PolyChaosBridge:676, thm)
       ← degreePiecewiseTail_layerCake_lt_top                       (PolyChaosBridge:819, thm)
       ← polynomial_chaos_exp_moment_bridge_bounded_of_cutoffTail / _of_tail
            := expMoment_bound_of_cutoff_degree_tail                (RoughErrorBound:482)
                 := LatticeBridge.bridgeAxiom_of_varying_coupled_setup_real   (THE ENGINE)
```

## The engine is already 90% generic

`LatticeBridge.bridgeAxiom_of_varying_coupled_setup_real` (`LatticeBridge.lean:356`) signature:
```
{d} {P} {mass} {α} [MeasurableSpace α]
(a ha hmass) (N) [NeZero N]
(μ : Measure α) [IsProbabilityMeasure μ]                       -- generic source (joint) measure
(π : ℝ → α → Configuration (FinLatticeField d N))             -- synthesis (per cutoff M)
(hπ_meas)
(hpush : ∀ M, Measure.map (π M) μ = latticeGaussianMeasure d N a mass ha hmass)
(V_S E_R : ℝ → α → ℝ)                                          -- smooth/rough split — GENERIC fns
(hdecomp : ∀ M ξ, interactionFunctional d N P a mass (π M ξ) = V_S M ξ + E_R M ξ)
(hsmooth : ∀ M ξ, -(M/2) ≤ V_S M ξ)                            -- smooth lower bound — GENERIC
(ψ) (htail : ∀ M, 0<M → μ {ξ | E_R M ξ ≤ -(M/2)} ≤ ψ M)        -- rough tail — GENERIC
(hintegral : ∫⁻ M in Ioi 0, ψ M · ofReal(2 exp(2M)) < ⊤) :     -- layer-cake finiteness — GENERIC
  ∫ ω : Configuration (FinLatticeField d N),
    (exp(-interactionFunctional d N P a mass ω))² ∂(latticeGaussianMeasure d N ...) ≤ 1 + (…).toReal
```
**The split `(V_S, E_R)`, `hsmooth`, `htail`, `hintegral` are already plain functions/hypotheses
on a generic `α` — no `CanonicalJoint` baked in.** The proof is pure measure theory (layer-cake
over the pushforward). The ONLY lattice hard-wiring is the **target**:
`Configuration (FinLatticeField d N)`, `interactionFunctional d N P a mass`,
`latticeGaussianMeasure d N a mass ha hmass`, and (in the proof) `interactionFunctional_measurable`.

## B-lean — the plan

### Step 1 — generalize the engine over the target (proved, shared)

In `LatticeBridge.lean`, generalize `bridgeAxiom_of_setup_real`, `bridgeAxiom_of_coupled_setup_real`,
`bridgeAxiom_of_varying_coupled_setup_real` (and `bridgeAxiom_of_setup`) by replacing the target
triple with parameters:
```
{F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] …
(μ_GFF : Measure (Configuration F)) [IsProbabilityMeasure μ_GFF]
(V : Configuration F → ℝ) (hV_meas : Measurable V)
```
i.e. `Configuration (FinLatticeField d N) ⤳ Configuration F`,
`interactionFunctional d N P a mass ⤳ V`, `latticeGaussianMeasure … ⤳ μ_GFF`,
`interactionFunctional_measurable ⤳ hV_meas`. The proof is unchanged (measure-theoretic).
~475-line file; the change is type-parametric, **mechanical** (no new math).

### Step 2 — re-instantiate the square (recover the existing chain, 0 churn downstream)

Add thin square wrappers (or `set`-instantiate) `F := FinLatticeField d N`,
`V := interactionFunctional d N P a mass`, `μ_GFF := latticeGaussianMeasure d N …`,
`hV_meas := interactionFunctional_measurable …`, recovering the current
`bridgeAxiom_of_varying_coupled_setup_real` signature so `expMoment_bound_of_cutoff_degree_tail`
and everything above it compile unchanged.

### Step 3 — the heterogeneous Nelson estimate (the new content)

`asymNelson_exponential_estimate_iso Nt Ns … : ∃ K>0, ∀ (Nt,Ns,a) …,
  ∫ (exp(-interactionFunctionalAsym Nt Ns P a mass ω))² ∂(latticeGaussianMeasureAsym …) ≤ K`.

Apply the **generalized engine** with `F := AsymLatticeField Nt Ns`,
`V := interactionFunctionalAsym Nt Ns P a mass`, `μ_GFF := latticeGaussianMeasureAsym …`,
`hV_meas := interactionFunctionalAsym_measurable …`. This reduces the goal to supplying the
engine's chaos-setup hypotheses for the heterogeneous lattice:
`(α, μ, π, hπ_meas, hpush, V_S, E_R, hdecomp, hsmooth, htail, ψ, hintegral)`.

**Supply these as ONE vetted axiom** — the heterogeneous polynomial-chaos cutoff decomposition:
```
axiom asym_polynomial_chaos_cutoff_setup
    (P : InteractionPolynomial) (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ K > 0, ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
      (Nt : ℝ) * a = ? → (Ns : ℝ) * a = ? →   -- volume constraints (Lt, Ls or Lt·Ls)
      ∫ ω, (exp(-interactionFunctionalAsym Nt Ns P a mass ω))²
        ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) ≤ K
```
— i.e. **axiomatize the heterogeneous Nelson bound directly** (the cleanest: the engine then
isn't even needed for the heterogeneous side). OR, more finely (preferred for eventual discharge),
axiomatize the three analytic inputs `(hsmooth, htail, hintegral)` against a heterogeneous
`CanonicalJointAsym` that we DEFINE (synthesis `π` + `hpush` + `hdecomp` proved from the Phase-1b
heterogeneous DFT), and let the generalized engine produce the bound. The finer version isolates
the genuine Glimm–Jaffe debt (smooth lower bound + rough hypercontractive tail) and reuses the
proved layer-cake engine — but needs the heterogeneous synthesis/pushforward plumbing (a port of
the `FieldDecomposition` GFF=pushforward-of-joint identity, using the `Z_Nt×Z_Ns` DFT we already
built in Phase 1b).

**Decision for first pass:** axiomatize the heterogeneous Nelson bound directly (coarse axiom),
get Phase 3 closed, THEN refine to the finer chaos-setup axioms + generalized engine once the
heterogeneous synthesis/pushforward plumbing is ported. This keeps the engine generalization
(Step 1, the reusable win) while not blocking on the FieldDecomposition port.

### Step 4 — cutoff bound + Phase 3

Replace `asymNelson_exponential_estimate` by `asymNelson_exponential_estimate_iso` in the iso
analogue of `asymTorusInteractingMeasure_exponentialMomentBound_cutoff` (pushforward via
`asymTorusEmbedLiftIso` + `interactionFunctionalAsym_bounded_below`), with RHS
`K·exp(σ²)` and `σ² = second moment` (pieces 1+2 give `σ² → asymTorusContinuumGreen`). Then
Phase 3 assembles `MeasureHasGreenMomentBound`.

## Axiom hygiene

Per project policy: the new axiom(s) get a docstring (statement in English, reference
Glimm–Jaffe Ch. 8 / Simon §V, strategy = heterogeneous analogue of the proved square
`nelson_exponential_estimate_master`), a `deep_think_gemini` vet, an `AXIOM_AUDIT.md` entry, and
`(NOT VERIFIED)` until vetted. Mark in `status.md`. The square Nelson estimate being a proved
theorem is strong evidence the heterogeneous one is formalizable — the axiom is genuine debt,
to be discharged by Step-3-fine.

## Effort

- Step 1 (engine generalization): **moderate, mechanical** — type-parametrize ~4 theorems in a
  475-line file; the proofs are measure-theoretic and unchanged. Main risk: the instance bundle
  on `F` and a couple of measurability rewrites (`interactionFunctional_measurable ⤳ hV_meas`).
- Steps 2–4: **small** — re-instantiation + one axiom + the cutoff-bound port (mirror of the
  square `exponentialMomentBound_cutoff`, now over the iso embedding) + Phase-3 assembly.
- Step-3-fine (discharge the axiom): **large, later** — port the `FieldDecomposition` synthesis +
  `hpush`/`hdecomp` and the `RoughErrorBound`/`CovarianceBoundsGJ` analytic inputs to `Z_Nt×Z_Ns`.
