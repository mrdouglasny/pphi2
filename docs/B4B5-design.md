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

## Feasibility assessment — the trace bridge is HS, not full trace-class (2026-06-04)

After proving the operator↔kernel link (`asymTransferKernel_kPow_apply`), the trace bridge was
scoped definitively:

1. **Lt-uniformity is irreducibly the gap's job.** B1
   (`asymTorusIso_interacting_second_moment_density_transfer`) sets `C = 3·√K` with `K =
   asymNelson_exponential_estimate_iso` — the Nelson exp-moment over the **whole volume**, which
   grows with `Lt`. No reordering/patch makes B1's `C` uniform: the uniformity must come from the
   transfer-matrix gap (a geometric series in the time extent), so the trace bridge is necessary.
2. **Mathlib has no infinite-dim trace-class.** `InnerProductSpace/Trace.lean` is
   `[FiniteDimensional]` only (`LinearMap.trace`, `trace_eq_sum_inner`, `trace_rankOne`); our `T`
   is on infinite-dim `L²(ℝ^Ns)`. No `Schatten`/`HilbertSchmidt`/`TraceClass` files in Mathlib.
3. **Use Hilbert–Schmidt, not full trace-class.** The needed bound is `|Tr(C D)| ≤ ‖C‖_HS·‖D‖_HS`
   with `‖·‖_HS` = the `L²` norm of the kernel (concrete; the Gaussian transfer kernel is HS). The
   geometric decay then comes from `‖M_A T'^{a+1}‖_HS ≤ ‖M_A T'‖_HS·‖T'^a‖_op` with the gap
   `‖T'^j‖_op ≤ (γλ₀)^j`. This avoids general trace-class entirely.
4. **pphi2 has HS *compactness* but not the HS-norm/trace layer.** `GeneralResults/HilbertSchmidt`
   provides `integral_operator_l2_kernel_compact` + `isCompactOperator_of_basis_norm_summable`
   (used to build `T` and get `Ω` via Perron–Frobenius), but NOT `‖·‖_HS` as a norm with
   `Tr(CD) ≤ ‖C‖_HS‖D‖_HS`. So the remaining trace bridge = **build that HS-norm + trace-CS layer**
   on the existing HS infra, then the rank-1 split (`T = λ₀P₀ + T'`) + `connected_two_point_le` /
   `geom_wrap_sum_le` close it.

**Net remaining work for B2:** (i) HS-norm + trace-Cauchy–Schwarz layer (bounded, tractable —
the kernels are explicit Gaussians); (ii) the rank-1 trace split feeding the proved B4 engine;
(iii) B5b single-slice stability (≈ specialization of the existing Nelson estimate to one slice,
`Ls`-fixed). All hard *mathematical* inputs are proved; this is the operator-infrastructure tail.

## HS trace-bridge — concrete construction (start, 2026-06-04)

Key simplification: with `asymTransferKernel_kPow_apply` proved (`T^{m+1}` acts via the explicit
kernel `kPow m`), the trace bound needs **no abstract trace-class / HS-operator theory** — it is
**concrete Cauchy–Schwarz on explicit kernels over the product measure**. The "HS norm" is just the
`L²` norm of a kernel, computed directly.

### Target
The dictionary two-point is `(Z)⁻¹ ∫∫ A(x)·kPow_a(x,y)·B(y)·kPow_b(y,x) dx dy = Tr(M_A T^{a+1} M_B
T^{b+1})/Z` (`A = ⟨g_t,·⟩`, `B = ⟨g_{t'},·⟩` linear). Goal: the **connected** part `≤ γ^{a+b}·
(HS-norms)`, uniform — feeding `connected_two_point_le` / `geom_wrap_sum_le`.

### Brick sequence (each a concrete integral estimate)
1. **Rank-1 kernel split.** `Ω` is the top eigenvector (`asymGroundVector`, eigenvalue `λ₀`).
   Set `R_m(x,y) := kPow_m(x,y) − λ₀^{m+1} Ω(x)Ω(y)` (kernel of `T'^{m+1}`, `T' = T(1−P₀)`). Prove
   `kPow_m = λ₀^{m+1} ΩΩ + R_m` from `asymTransferKernel_kPow_apply` + `T Ω = λ₀ Ω`.
2. **Operator-norm decay of `R`.** `‖T'^{m+1} f‖₂ ≤ (γλ₀)^{m+1} ‖f‖₂` for the integral operator with
   kernel `R_m`, from the proved gap (`asymTransferNormalized_gap`). (This is just the gap, restated
   for the `R_m` integral operator via theorem 1.)
3. **Kernel Cauchy–Schwarz.** For the doubly-connected term,
   `|∫∫ A(x) R_a(x,y) B(y) R_b(y,x)| ≤ (∫∫ A(x)² R_a(x,y)² )^{1/2} (∫∫ B(y)² R_b(y,x)² )^{1/2}`
   (Mathlib `MeasureTheory.integral_mul_le_L2_norm_mul_L2_norm` / `inner_mul_le_norm_mul_norm` on
   `L²(volume×volume)`). Each factor `= ‖M_A R_a‖_HS`-type, finite by Gaussian decay of the kernel.
4. **HS ≤ op·HS submultiplicativity (concrete).** `‖M_A R_a‖_HS = ‖M_A T'^{a+1}‖_HS ≤ ‖M_A T'‖_HS ·
   ‖T'^a‖_op ≤ ‖M_A T'‖_HS·(γλ₀)^a` — gives the `γ^a` geometric decay. (Concrete: `∫ R_a(x,·)² =
   ‖T'^{a+1} (R_1(x,·)-ish)‖²`, bound by op-norm iteration.)
5. **The mixed `P₀·R` terms** (one disconnected leg): bounded by `λ₀^{a}·(stuff)·(γλ₀)^{b}` — the
   `Ω`-projection of `M_A`, i.e. `⟨Ω, M_A Ω⟩` and `‖P₁ M_B Ω‖`, exactly the `connected_two_point_le`
   shape; reuse it.
6. **Assemble + normalize.** `Tr(T^{Nt}) ≥ λ₀^{Nt}` (T' positive). The connected two-point `≤
   γ^{min(a,b)}·C(g_t,g_{t'})` with `C` an HS/`P₁`-norm; sum over `t,t'` via `geom_wrap_sum_le`.

### What Mathlib/pphi2 supply
- `MeasureTheory.Lp` `L²(volume×volume)` + Cauchy–Schwarz (brick 3) — Mathlib.
- `asymTransferKernel_kPow_apply`, `asymGroundVector`, `asymTransferNormalized_gap`,
  `transferGaussian` decay, `asymTransferWeight_memLp_two` (the kernels are `L²`) — pphi2, proved.
- `GeneralResults/HilbertSchmidt` (`integral_operator_l2_kernel_compact`) — the `L²`-kernel↔operator
  machinery to lean on for bricks 2/4.

**Difficulty:** ★★ (concrete integral estimates, no new abstract theory). Bricks 1–2 are short;
3–4 are the real work (the HS-decay via op-norm iteration); 5–6 reuse `connected_two_point_le`.
Recommended first: bricks 1+2 (rank-1 kernel split + R decay) — self-contained, build on the proved
operator↔kernel link.
