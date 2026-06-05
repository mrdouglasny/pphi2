# Layer B2 completion route — the asym variance bound (axiom 3)

Target: `asymInteractingVariance_le_freeVariance_Lt_uniform` (`AsymExpMomentDischarge.lean:206`).
This is the **lone genuinely-unblocked formalization thread** (confirmed by the 2026-06-04
plan-loop triage). All ingredient lemmas are **proved**; what remains is a large but well-defined
integration. This file pins the exact route so the next push starts from the plan, not a re-scope.

## What is proved (the ingredients)
- `interacting_second_moment_eq_pathMeasure` (AsymVarianceDischarge.lean:64) — the interacting
  second moment `= ∫ (slicePairing g ψ)² d(pathMeasure)`. **PROVED.**
- `twoPoint_dictionary` (reflection-positivity `TransferSystem.lean:756`) — for single-slice
  bounded `A,B`: `∫ A(ψ₀)·B(ψ_t) dμ_n = Z_n⁻¹ ∫∫ A(x)·kPow_{t−1}(x,y)·B(y)·kPow_{n−t−1}(y,x)`.
  **PROVED** (iterated Fubini). Carries integrability hyps `hAB`, `hSlice`.
- `asymTransferKernel_kPow_apply` (AsymTransferKernelOperator.lean) — `T^{m+1} f =ᵐ ∫ kPow_m · f`
  (kernel ↔ operator). **PROVED.**
- Operator bricks 0–2 (AsymTraceBridge.lean, this session) — `T^{m+1}Ω = λ₀^{m+1}Ω`; perp decay
  `‖T^{m+1}v‖ ≤ (γλ₀)^{m+1}‖v‖`; rank-1 split `‖T^{m+1}v − λ₀^{m+1}⟪Ω,v⟫Ω‖ ≤ (γλ₀)^{m+1}‖v‖`.
  Plus `asymGroundVector_norm_eq_one` (‖Ω‖=1). **PROVED, sorry-free.**
- `connected_susceptibility_le` / `connected_two_point_le` (reflection-positivity
  ConnectedTwoPoint.lean) — `Σ_d |⟪Ω,Φ Tᵈ Φ Ω⟫ − ⟪Ω,ΦΩ⟫²| ≤ ‖P₁ΦΩ‖²/(1−γ)`. **PROVED.**
- `averaged_susceptibility_bound` / `geom_wrap_sum_le` (reflection-positivity
  AveragedSusceptibility.lean) — the `Nt`-uniform forward+wrap geometric sum. **PROVED.**

## The 7-step assembly (each step a lemma with its obligation)
1. **Square expansion.** `slicePairing g ψ = Σ_t A_t(ψ_t)` with `A_t(s) := Σ_i (asymSliceEquiv g t i)·s i`
   a *linear* functional on the slice `S = SpatialField Ns`. So
   `(slicePairing)² = Σ_{t,t'} A_t(ψ_t)·A_{t'}(ψ_{t'})`, and
   `∫(slicePairing)² dμ = Σ_{t,t'} ∫ A_t(ψ_t)·A_{t'}(ψ_{t'}) dμ`.
   **Obligation:** integrability of each cross term against `pathMeasure` — `A_t` is *unbounded*
   (linear), so this is a Gaussian-tail moment bound, NOT free from `twoPoint_dictionary`'s bounded
   hypotheses. Need: the path measure has finite second moments of linear slice functionals
   (it is the pushforward of the interacting lattice measure, which has exp-moments via Nelson;
   or prove L² directly from the Gaussian-dominated slice structure).
2. **Cyclic reduction.** By translation invariance of `pathMeasure` (cyclic in `ZMod n`),
   `∫ A_t(ψ_t)·A_{t'}(ψ_{t'}) dμ = ∫ A_t(ψ_0)·A_{t'}(ψ_d) dμ` with `d = (t'−t) mod n`. **Obligation:**
   a `pathMeasure`-translation-invariance lemma (likely needs proving on `Ts.pathMeasure`; check
   TransferSystem for an existing shift-invariance lemma first).
3. **Apply the dictionary.** For `d ≠ 0`, `twoPoint_dictionary` turns each into the kernel form
   `Z⁻¹∫∫ A_t(x) kPow_{d−1}(x,y) A_{t'}(y) kPow_{n−d−1}(y,x)`. The diagonal `d=0` term is a
   single-slice second moment (handle separately — it is part of `Var_free`'s scale). **Obligation:**
   discharge `twoPoint_dictionary`'s `hAB`/`hSlice` for the *unbounded* linear `A_t` (the same
   Gaussian-tail integrability as step 1, at the split-density level).
4. **Kernel → operator.** Rewrite the kernel double-integral as operator inner products on
   `L2SpatialField Ns` via `asymTransferKernel_kPow_apply`:
   `∫∫ A(x) kPow_{d−1}(x,y) B(y) … = ⟪vₐ, T^{d−1} (M_? …)⟫`-type forms, identifying `A_t` with the
   L² vector `c_t = asymSliceEquiv g t` and the kernel composition with `T` powers. **Obligation:**
   the L²-pairing/Fubini bookkeeping (the kernels are the integral kernels of `T`).
5. **Connected bound.** Subtract the disconnected part (`⟪Ω,·Ω⟫⟪Ω,·Ω⟫`) and apply
   `connected_two_point_le` (bricks 0–2 are its un-normalised analogue) to get
   `|connected_d| ≤ (γλ₀-style)^d ‖P₁(c_t)‖‖P₁(c_{t'})‖` per separation `d`.
6. **Geometric sum.** Sum over `d` with `averaged_susceptibility_bound` / `geom_wrap_sum_le` →
   `Nt`-uniform (hence `Lt`-uniform at fixed `a`) bound `≤ C(a)·Σ_t ‖P₁ c_t‖²`.
7. **Identify with `C·Var_free`.** Show `Σ_t ‖P₁ c_t‖²` (+ the disconnected/diagonal pieces) is
   `≤ C · Var_free(g)`. **This is where the `1/a` cancellation lives** (the docstring warns a naive
   `1/(1−γ)·Var_free` is `a`-non-uniform and WRONG). `asymLatticeTestFnIso = a·evalAtSite` supplies
   the `a`-power; cross-check the **covariance square-root convention** (precision `a²Q`) — the
   `a`-scaling is the documented error-prone spot (crux-2). **Vet step 7's a-bookkeeping with
   Gemini/Codex before committing**, as for crux-2.

## Remaining (after the trace bound): B5b
- **B5b single-slice stability** ≈ Nelson-per-slice — the `d=0` diagonal term's bound. Smaller than
  the trace bridge; rides on the same slice-moment infrastructure built in step 1.

## Risk / size
Unblocked but **large** (≈ the size of the whole AsymTorus dictionary chain again). Highest-risk
steps: 1/3 (unbounded-functional Gaussian-tail integrability) and 7 (the `a`-power cancellation).
Steps 4–6 are mechanical given the proved operator/geometric lemmas. Not a few-edit win; budget a
focused multi-day pass. Do step 7's `a`-scaling design pass first (cheap insurance against a
crux-2-style factor error).
