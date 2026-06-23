# Vetting — `asymInteracting_expMoment_volume_uniform`

Captured soundness-review records for `asymInteracting_expMoment_volume_uniform`
(`Pphi2/AsymTorus/AsymContinuumLimit.lean:621`). Linked from
[`../../AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md) and
[`../../planning/INDEX.md`](../../planning/INDEX.md) item 1.

---

```yaml
---
axiom: asymInteracting_expMoment_volume_uniform
file: Pphi2/AsymTorus/AsymContinuumLimit.lean:621
statement_hash: null    # not yet populated; required for L3 strictness
model: gemini-3.1-pro-preview
tool: mcp__gemini__deep_think_gemini
source_code: DT         # deep-think
date: 2026-05-27
questions: [typing, strength, non-vacuity, satisfiability]
verdict: SATISFIABLE
rating: Likely correct
discharged: false
superseded_by: null
---
```

**Axiom statement vetted (verbatim):**

```lean
/-- Volume-uniform interacting exponential-moment bound on the cylinder.

There exist constants `K > 0` and `C > 0` such that, for every cylinder geometry
`(Nt, Ns, a)` with fixed `Ls = Ns · a` and for every test function `f`,

  ∫ exp |⟨ω, f⟩| dμ_int(ω) ≤ K · exp(C · σ²(f))

where `μ_int` is the interacting asymmetric-torus measure and `σ²(f)` is the
free covariance.

Discharges the `hUnif` hypothesis of `routeBPrimeIso_cylinder_OS`, giving
`cylinderIso_OS_of_RP_OS2`. -/
axiom asymInteracting_expMoment_volume_uniform :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧ ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
      (a : ℝ) (ha : 0 < a) (hLs : Ns * a = Ls.val) (P : InteractionPolynomial)
      (mass : ℝ) (hmass : 0 < mass) (f : AsymTestFunction Nt Ns),
        ∫ ω, Real.exp |asymPairing ω f|
            ∂(asymInteractingMeasure Nt Ns a ha P mass hmass)
          ≤ K * Real.exp (C * asymFreeCovariance Nt Ns a ha mass hmass f f)
```

**Prompt (verbatim, condensed; for the full deep-think transcript see
[`../../AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md) 2026-05-27 entry):**

> The exact prompt and full reply from `mcp__gemini__deep_think_gemini`
> on 2026-05-27 are recorded inline in the project AXIOM_AUDIT.md at the
> "Discharge plan (cylinder shortcut)" entry. Summary of the question:
> "Is the stated `K · exp(C · σ²)` bound (with `∃ K, C > 0`, uniform in
> the time period `L` at fixed `Ls`) (a) correctly typed, (b) strong
> enough to discharge `routeBPrimeIso_cylinder_OS`, (c) non-vacuous,
> (d) actually true in infinite volume?"

**Reply (verbatim summary, captured 2026-05-27):**

> **Standard / Likely correct with the `C · σ²` exponent.**
>
> The original `C = 1` form (no `C` quantifier) is **false** in infinite
> volume: the interacting susceptibility can exceed `2/m²`, and the
> Cauchy–Schwarz prefactor `½p(2λ) − p(λ) > 0` by strict convexity, so
> the naive `Z⁻¹ · K_Nelson^{1/2}` cannot be volume-uniform.
>
> With **`∃ C > 0`** the statement is TRUE via:
> 1. Newman/Lee–Yang Gaussian-domination of the MGF (`K = 2`) — the
>    Newman class of the lattice partition function ensures the MGF
>    is dominated by the corresponding Gaussian MGF.
> 2. Interacting-variance domination by the free covariance through the
>    strict mass gap (`C = C₀/2`).
> 3. Uniform in `a` (lattice reflection-positivity / ferromagnetic
>    inequalities) and in `L` (fixed `Ls` ⟹ quasi-1D ⟹ Perron–Frobenius
>    mass gap, bounded susceptibility).
>
> References: Glimm–Jaffe Ch. 18–19; Simon Ch. V/VIII; Newman (1975);
> Glimm–Jaffe–Spencer.

**Reasoning digest:** *Likely correct* — the `∃ K, C > 0` form with the
`C · σ²` exponent is the only true volume-uniform form of the Nelson-style
exponential-moment bound for P(φ)₂. The `C = 1` form (originally stated) was
**false**; the corrected `∃ C` form (committed in the same revision) is
sound, with two independent routes (Newman/Lee–Yang + transfer-matrix gap)
both vetted.

**Conditions / follow-ups:**

- *Discharge architecture* (3 layers, per
  [`../../docs/asym-interacting-expmoment-volume-uniform-discharge-plan.md`](../../docs/asym-interacting-expmoment-volume-uniform-discharge-plan.md)):
  - **Layer A** = Newman MGF Gaussian-domination
    (`asymInteracting_mgf_gaussianDominated`, item 2 in `planning/INDEX.md`)
    — depends on the new
    [`lee-yang`](https://github.com/mrdouglasny/lee-yang) repo (Phase 1
    polynomial side done, measure side still to go).
  - **Layer B2** = interacting variance dominated by free variance. The
    torus statement `asymInteractingVariance_le_freeVariance_Lt_uniform`
    is now a theorem; active item 3 is the lattice Route-A input
    `asymInteractingVariance_le_freeVariance_lattice_Lt_uniform`. The
    remaining gap is the lattice Route-A finite-K/B5b/free-assembly closure.
  - **Layer C** = the ~50-line assembly here (this axiom).
- *Re-vet if strengthened*: any tightening of `C` to a specific functional
  form (e.g. `C = 1/(2m²)`) requires a fresh deep-think + literature pass;
  the current sound form is the qualified existential.
- *Statement-hash*: not yet populated; required to raise this record to L3
  (statement-hash freshness gate). Compute the hash once the statement
  stabilizes after the Layer-C assembly lands.

**Cross-references:**

- Live discharge plan: [`../../docs/asym-interacting-expmoment-volume-uniform-discharge-plan.md`](../../docs/asym-interacting-expmoment-volume-uniform-discharge-plan.md)
- Layer A plan: [`../../docs/asym-expmoment-discharge-via-lee-yang-vet-request.md`](../../docs/asym-expmoment-discharge-via-lee-yang-vet-request.md)
- Cyl-1a bridge plan: [`../../docs/cyl-1a-bridge-plan.md`](../../docs/cyl-1a-bridge-plan.md)
- Status: [`../../planning/INDEX.md`](../../planning/INDEX.md) item 1.
