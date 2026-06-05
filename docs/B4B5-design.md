# B4/B5 design — finite-volume Källén–Lehmann + the `1/a` cancellation

**Status: design pinned (Gemini gemini-3-pro, 2026-06-04). Not yet formalized.** This records
the cleanest route from the proved gap + Feynman–Kac dictionary to the Layer-B2 deliverable, and
isolates the one genuinely-deep remaining piece, so the formalization target is correct before
we write Lean (the same "derive + vet before formalizing" discipline that caught the `a`-power
error in crux-2).

## What's already proved (the inputs)
- `twoPoint_dictionary` : `∫A(ψ₀)B(ψ_t)dμ = Tr(M_A Tᵗ M_B T^{Nt−t})/Tr(T^Nt)`.
- Spectral gap on the normalized operator `T̂ = T/λ₀`: `‖T̂ v‖ ≤ γ‖v‖` for `v ⊥ Ω`, `γ<1`,
  **`γ independent of Nt`** (it is a single-slice spatial operator).
- `interacting_second_moment_eq_pathMeasure` : `∫(ωg)²dμ_int = ∫(Σ_t⟨g_t,ψ_t⟩)²dμ`.

## (1) Finite-Nt representation + Nt-uniformity — the correction

**The raw sum `Σ_{t,t'} Cov(Φ_t,Φ_{t'})` scales *linearly* in Nt; it is NOT Nt-uniform.** The
Nt-uniform object is the **time-averaged susceptibility** `χ := (1/Nt)Σ_{t,t'}Cov`. By cyclic
translation invariance of `μ`, `Σ_{t,t'}Cov = Nt·Σ_d ⟨Φ₀Φ_d⟩_c`, so `χ = Σ_d ⟨Φ₀Φ_d⟩_c`.

Spectral decomposition `T = Σ_k λ_k|e_k⟩⟨e_k|` (`e₀=Ω`), connected (vacuum-subtracted) two-point:
```
⟨Φ₀Φ_d⟩_c = Σ_{k>0} |⟨Ω|Φ|e_k⟩|² [ (λ_k/λ₀)^d + (λ_k/λ₀)^{Nt−d} ]   (Φ self-adjoint, leading)
```
The periodic wrap-around `(λ_k/λ₀)^{Nt−d}` is a *second* geometric series, convergent identically;
it does **not** spoil Nt-uniformity. Summing over `d` and using `λ_k/λ₀ ≤ γ`:
```
χ_Nt = Σ_d ⟨Φ₀Φ_d⟩_c ≤ ((1+γ)/(1−γ)) · Σ_{k>0}|⟨Ω|Φ|e_k⟩|²
     = ((1+γ)/(1−γ)) · ‖P₁ Φ Ω‖²,    P₁ = I − |Ω⟩⟨Ω|.
```
**For the fixed torus test function `f`,** the Nt that appears in `Σ_{t,t'} = Nt·Σ_d` is cancelled
by the `a`-normalization of the lattice test function (`asymLatticeTestFnIso = a • evalAtSite`,
so `g_t ∝ a`): the raw sum the axiom wants *is* effectively the averaged χ. This is where B5's
`1/a` enters — same square-root/cell-area bookkeeping as crux-2.

## (2) The clean intermediate lemma (formalize this — abstract, no φ⁴)

A general Hilbert-space lemma, the trace-ratio analogue of `VarianceBound.susceptibility_le`:

> `H` Hilbert, `T` self-adjoint, `TΩ=λ₀Ω`, `‖Tv‖≤γλ₀‖v‖` for `v⊥Ω` (`γ∈[0,1)`), `Φ` self-adjoint.
> With the periodic trace correlators `⟨Φ_t Φ_{t'}⟩ := Tr(…)/Tr(T^Nt)`,
> ```
> (1/Nt) Σ_{t,t'<Nt} (⟨Φ_t Φ_{t'}⟩ − ⟨Φ_t⟩⟨Φ_{t'}⟩) ≤ ((1+γ)/(1−γ)) · ‖P₁ Φ Ω‖².
> ```

Follows from spectral decomposition + geometric series (part 1). **Belongs in
`reflection-positivity`** (general, reusable; sits next to `susceptibility_le`). This is the
B4 engine and is genuinely formalizable from the gap + dictionary.

## (3) The deep remaining piece (B5 core) — single-slice stability

Bounding `‖P₁ Φ Ω‖²` by free-field quantities is **"a separate, deeper theorem of constructive
QFT"** (Gemini): the *interacting single-slice variance* `‖P₁ Φ Ω‖² = Var_Ω(Φ)` is bounded by
`C · Var_free,slice(Φ)`, with `C` independent of `a, Nt`. Heuristic `a`-scaling that must come out
exactly: gap `1−γ ∼ a²m²`, matrix element `‖P₁ΦΩ‖² ∼ a²⟨g,(−Δ_sp+m²)⁻¹g⟩`, product `a`-independent.

This single-slice stability is the Lt-**independent** strengthening of pphi2's existing B1 bound
`Var_int ≤ C(Lt)·Var_free` (Nelson/chessboard, Lt-DEPENDENT). **Likely addressable via the
existing Nelson-estimate / Gaussian-domination infrastructure** (`AsymNelson.lean`,
`AsymRoughCovarianceHigherP.lean`) applied to a single slice rather than the full volume — that
connection is the next thing to scope. The exact `a`-power bookkeeping deserves a dedicated
derivation pass (Gemini deep-think) before formalizing, as in crux-2.

## Route correction (2026-06-04, after starting B4): rank-1 projection, NOT eigenbasis

Gemini's part-(1) derivation uses the **full eigenbasis** `T=Σλ_k|e_k⟩⟨e_k|`. But pphi2 only
proves the **operator-norm gap** (`‖T̂v‖≤γ‖v‖` for `v⊥Ω`) + the ground vector `Ω` — *not* a full
eigendecomposition (which would need Mathlib's compact-self-adjoint spectral theorem, unbuilt).
The eigenbasis route is therefore the wrong target. **The correct route uses only the rank-1
ground projection `P₀=|Ω⟩⟨Ω|` and the norm gap:**
- `Ω` an eigenvector ⟹ `Ω^⊥` is `T`-invariant ⟹ with `T' := T(1−P₀)`, `P₀T'=T'P₀=0`, so
  `Tʲ = λ₀ʲ P₀ + T'ʲ` (clean operator algebra, no eigenbasis), and `‖T'ʲ v‖ ≤ (γλ₀)ʲ‖v‖`.
- The operator-power bound on `Ω^⊥`, `|⟪v,Tⁿv⟫| ≤ γⁿ‖v‖²` for `v⊥Ω`, **already exists** as
  `ReflectionPositivity.GappedTransfer.abs_inner_T_pow_le` (used by `susceptibility_le`). Reuse it.
- Trace split: `Tr(M_A Tᵗ M_B T^{Nt−t})/Tr(T^Nt)`, expand both `Tᵗ,T^{Nt−t}` via `λ₀ʲP₀+T'ʲ`. The
  `P₀P₀` term is the disconnected `⟨Ω|M_A|Ω⟩⟨Ω|M_B|Ω⟩` (up to `O(γ^Nt)` finite-volume corrections
  from `Tr(T'^Nt)`); the other three terms carry ≥1 factor `T'ʲ`, bounded by `γ^min(t,Nt−t)`.
  `Tr(T^Nt) ≥ λ₀^Nt` (T' positive). Feeds `geom_wrap_sum_le`.

The trace itself = pphi2's kernel-iterate `∫kPow(x,x)dx` (the sound finite-torus form). The
remaining work is the **kernel-iterate trace-ratio connected split** in this rank-1 picture —
which now needs no spectral theorem, only `P₀` + the existing power bound + the trace measure
theory. (B4 engine `averaged_susceptibility_bound` is done; this is the operator→engine bridge.)

## Formalization plan
1. **B4 (reflection-positivity):** ✅ the geometric engine (`geom_wrap_sum_le`,
   `averaged_susceptibility_bound`) is done. The remaining B4 piece is the rank-1 trace-split
   bridge above (uses `abs_inner_T_pow_le` + the trace, NO spectral theorem).
2. **B5a (pphi2):** the integral-operator form of `asymTransferOperatorCLM` (`(Tf) =ᵐ ∫k·f`, from
   `mulCLM_spec` + `convCLM_spec`) and `kPow asymTransferKernel = kernel of Tⁿ`, to feed the trace
   correlators into the abstract lemma.
3. **B5b (pphi2, the deep piece):** single-slice stability `‖P₁ΦΩ‖² ≤ C·Var_free,slice`, with the
   exact `a`-cancellation — scope against the Nelson/chessboard infra; vet the `a`-powers first.
4. Assemble + the torus→lattice pushforward (`asymTorusInteractingMeasureIso`) → discharge
   `asymInteractingVariance_le_freeVariance_Lt_uniform`.

## Parallel-investigation findings (2026-06-04, while B5a foundation builds)

**B5b (single-slice stability) is likely reachable from existing infrastructure — not a new
deep theorem.**
- The existing **B1** bound `asymTorusIso_interacting_second_moment_density_transfer`
  (`AsymContinuumLimit.lean`) already has the **exact same shape** as the B2 axiom
  (`∫(ωf)²dμ_int ≤ C·∫(ωg)²dμ_free`). The *only* difference is quantifier order: B1 fixes `Lt`
  then chooses `C = C(Lt)` (the Nelson/Gaussian-domination route, volume-dependent); B2 needs `C`
  chosen before `Lt` (uniform). The uniformity is exactly what the transfer-gap route supplies.
- The Nelson engine `asymNelson_exponential_estimate_iso` (`∃K, ∀ Nt Ns a, ∫exp(−2V)² ≤ K`) is
  **already uniform in `Nt`** (Gaussian domination / hypercontractivity). The single-slice
  stability `‖P₁ΦΩ‖² ≤ C·Var_free,slice` is the **`Ls`-fixed, single-time-slice specialization**
  (no `Lt` at all — one slice), so its constant is `Lt`-independent essentially by construction;
  `‖P₁ΦΩ‖² = Var_Ω(Φ)` is the variance in the ground-state (`|Ω|²`) measure, a fixed-volume
  spatial-`φ⁴` problem. Plan: specialize the Nelson/chessboard estimate to one slice.

**Trace bridge has Mathlib support to build on.** `Mathlib/Analysis/InnerProductSpace/Trace.lean`
exists (plus `Spectrum.lean`, `Positive.lean`). Need to confirm it covers trace-class operators /
traces of products (for the rank-1 `Tr` split), but it is not a total absence — the trace layer
above the integral-operator form (B5a, in progress) is not starting from zero.
