# Strategy consult — uniform-in-N remainder for φ⁴₂ weak-coupling non-triviality on T²

Questions for Gemini deep-think (or Codex). Goal: vet the cleanest Lean 4 decomposition for the
one remaining lemma that closes the headline axiom
`torus_weakCoupling_lattice_connectedFourPoint_strictNeg`.

---

## Setup

Formalizing in Lean 4 / Mathlib the **weak-coupling non-triviality of φ⁴₂** on a **fixed torus T²**
(physical size `L`, lattice `N×N`, spacing `a = L/N`).

**Already proved, axiom-clean (Lean):**
- Coupling family `μ_g = Z_g⁻¹ e^{−gV} μ_GFF` on the finite lattice, where
  `V = a²·∑_x :P(φ(x)):_c` is the lattice interaction, `P` pure quartic `(1/4)φ⁴`, so
  `:φ⁴:_c = φ⁴ − 6cφ² + 3c²`.
- `u₄(g)(f) = ⟨φ(f)⁴⟩_g − 3⟨φ(f)²⟩²_g` (normalised-moment connected 4-point).
- `u₄(0) = 0` (Isserlis on the free GFF).
- `u₄'(0⁺) = −6·a²·∑_z (C_a f)(z)⁴ < 0` (first-order slope; `C_a = (−Δ_a + m²)⁻¹` the lattice
  covariance) — via differentiation-under-the-integral, the Wick algebra, and Isserlis.
- Hence `∃ g>0, u₄(g)<0` at **fixed N** (from the derivative sign / `o(g)` — no quantitative
  remainder yet).
- Quantitative interface lemma `deriv_affine_bound_neg`:
  `φ 0=0 ∧ φ'(t) ≤ −s + K·t on [0,g₀] ∧ K·g ≤ s/2 ⟹ φ g ≤ −(s/2)·g`.

**Structural facts available on the fixed torus (these make it tractable, unlike infinite volume):**
- `V ≥ −B` with `B = a²·(N² sites)·A = L²·A` **uniform in N** (since `a²N² = L²` fixed volume;
  `A ≤ const·mass⁻²` uniform via `wickConstant ≤ mass⁻²`). **[PROVED]**
- `⟨V⟩₀ = a²∑⟨:P:⟩₀ = 0` (Wick mean zero) ⟹ `Z_g = ⟨e^{−gV}⟩₀ ≥ e^{−g⟨V⟩₀} = 1` (Jensen); also
  `Z_g ≤ e^{gB}`. **[ingredients exist]**
- Nelson exponential estimate `∫ e^{−2V} dμ_GFF ≤ K` uniform in N. **[PROVED]**
- Polynomial-chaos / hypercontractivity `Lᵖ` bounds on `V` and on `φ(f)` under `μ_GFF`.
  **[infrastructure exists in `Pphi2/NelsonEstimate`]**

**Headline axiom (continuum torus, uniform in N):**
`∃ m₀>0, ∀ mass>m₀, ∃ f c>0, ∀ N: u₄(torusInteractingMeasure_N at this mass)(f) ≤ −c`.
The torus measure is the pushforward, under the lattice→torus embedding, of the actual interacting
lattice measure at coupling 1 / physical mass; `mass ↔ g` is the field-rescaling translation
(`u₄` scales by `rescale⁴`, large mass ⟺ small effective `g`).

**Goal:** upgrade "`∃ g, u₄(g)<0` at fixed N" to "`u₄(g) ≤ −c` uniformly in N for a single small `g`",
by supplying the uniform `s`, `K`, `g₀` that `deriv_affine_bound_neg` consumes.

---

## Questions

1. **Taylor / affine-derivative route.** Is the right target the affine derivative bound
   `u₄'(t) ≤ −s + K·t` on `[0,g₀]` with `s, K` uniform in N (equivalently `sup_{[0,g₀]}|u₄''| ≤ K`)?
   `u₄'(t)` involves normalised correlators `⟨(φf)ⁿ V^k⟩_t` (`n≤4`, `k≤2`). With `Z_t ≥ 1` and
   `e^{−tV} ≤ e^{tB}` (`B` uniform), each reduces to free moments `⟨|(φf)ⁿ V^k|⟩₀`. Are these
   uniformly bounded the right way (Cauchy–Schwarz/Hölder + uniform `Lᵖ` of `φ(f)` and of `V` via
   chaos)? **Pitfall check:** `V²` has degree-8 Wick chaos — is `‖V‖_{Lᵖ(μ_GFF)}` genuinely uniform
   in N on the fixed torus for the `p` needed (so `‖V‖_{L⁴}`, `‖V‖_{L⁸}` uniform)? What `p` is actually
   required?

2. **Simpler route?** Is there a cleaner one-sided argument than a two-sided `u₄''` bound — e.g. a
   convexity/monotonicity argument, or directly bounding the truncated correlator
   `⟨φ(f)⁴; V⟩^c_t` difference, exploiting `V ≥ −B`, `Z_t ≥ 1`, and the EXACT first-order term — that
   gives the affine `u₄'(t) ≤ −s + K·t` without ever forming the second derivative?

3. **Leading-term uniform lower bound (`s`).** The leading slope `6·a²·∑_z (C_a f)(z)⁴` must be
   bounded **below away from 0**, uniform in N. Is choosing `f` a fixed smooth test function and using
   `a²∑_z (C_a f)(z)⁴ → ∫_{T²}(C f)⁴ > 0` (Riemann-sum convergence of the lattice propagator) the clean
   route, or is there a cleaner uniform lower bound (e.g. project onto a single low mode / the lowest
   eigenvalue of `−Δ+m²` on T²)?

4. **Field-rescaling `mass↔g` translation.** Does it interact badly with the uniform-in-N estimate?
   The rescale factor `c` depends on `mass`, not `N`, so it should commute with "uniform in N" — please
   confirm, and flag any subtlety in how the rescaling changes the covariance `C_a` (hence `s`) and the
   interaction (hence `K`) as functions of N.

5. **Decomposition + references.** Please give the cleanest lemma-by-lemma decomposition (with the
   right `Lᵖ` exponents and where Cauchy–Schwarz/Hölder enters), flag the single hardest sub-lemma, and
   cite the specific bound in Simon *P(φ)₂* (Ch. V / VIII) or Glimm–Jaffe (Ch. 8–9, 19). Is the
   second-derivative-of-`u₄` route the standard one, or do practitioners use a cleaner identity for the
   coupling-derivative of the truncated 4-point?

---

## Pointers (Lean)

- `Pphi2/InteractingMeasure/U4Derivative.lean` — steps I–III + `deriv_affine_bound_neg`.
- `Pphi2/InteractingMeasure/{MomentDerivative,ConnectedCorrelatorDerivative,MomentIntegrability}.lean`.
- `Pphi2/InteractingMeasure/InteractionFourPoint.lean` — step 2b (`∫:φ(f)⁴:V = 6a²∑(C_a f)⁴`).
- `Pphi2/InteractingMeasure/FieldRedefinition.lean` — `mass↔g` field-rescaling, `connectedFourPoint`.
- `Pphi2/NelsonEstimate/` — `nelson_exponential_estimate`, chaos/hypercontractivity `Lᵖ` bounds.
- `Pphi2/TorusContinuumLimit/{TorusInteractingLimit,TorusNontriviality,TorusInteractingResult}.lean`
  — `torusInteractingMeasure`, `torusConnectedFourPoint`, the axiom.
- Memory: `pphi2-u4-proof-route`; plan: `planning/torus-interacting-proof-plan.md`.
