You are doing a careful mathematical and Lean-formalization review of a planned implementation of `rough_error_variance` for constructive φ⁴₂ on a 2D torus. The implementation will be done by Codex; we want to vet the plan before handing off.

== Project setting ==

`pphi2` is a Lean 4 formalization of constructive QFT on T². The goal is to discharge a textbook axiom `polynomial_chaos_exp_moment_bridge` (in `Pphi2/NelsonEstimate/PolynomialChaosBridge.lean`) which is the only research-level axiom on the T² interacting OS critical path. The discharge has multiple steps; this review is about the FIRST step, an L² bound on the "rough field error" of a Wick-polynomial interaction.

Lattice setup:
- Periodic lattice (ℤ/Nℤ)^d (we have d = 2), spacing a > 0, so |Λ| = N^d sites and physical period L = N · a.
- Free scalar mass m > 0, lattice covariance C(x,y) = (-Δ + m²)⁻¹.
- Heat-kernel UV cutoff at time T > 0 splits C = C_S + C_R:
  - C_S has eigenvalues (1 - exp(-T·λ_k))/λ_k (smooth, captures λ_k ≪ 1/T)
  - C_R has eigenvalues exp(-T·λ_k)/λ_k (rough, captures λ_k ≫ 1/T)
- Joint Gaussian measure on (φ_S, φ_R) with covariances C_S, C_R, independent.
- Wick-polynomial interaction with polynomial P of finite degree.

The rough error random variable:
  E_R(η) = a^d · Σ_x [:V(φ_S+φ_R)(x):_{c} − :V(φ_S)(x):_{c_S}]
where c = c_S + c_R is the on-site Wick constant (= C(x,x), translation-invariant), and c_S, c_R are the on-site smooth/rough Wick constants. By the binomial Wick identity, E_R reduces to a sum of products of smooth Wick monomials in φ_S and rough Wick monomials in φ_R, with at least one rough factor per term.

== Target theorem ==

```
theorem rough_error_variance
    {d : ℕ} (P : InteractionPolynomial)
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a) (h_vol : (N : ℝ) * a = L),
        ∫ η, (E_R(η))^2 ∂μ_joint ≤ K * <function of T>
```

Where `<function of T>` is one of:
  (i)  K · T                        (linear T)
  (ii) K · T · (1 + |log T|)^c      (T with polylog factor, c = deg P maybe)
  (iii) K · T^δ for fixed δ ∈ (0,1) (sub-linear T)

K must be uniform in (a, N) at fixed (L, mass, P), since the bridge axiom downstream consumes it that way (the dynamical cutoff picks T = T(M) and integrates over M; uniformity in (a, N) is essential for the continuum limit).

== Existing infrastructure (verified by us) ==

1. `wickMonomial_add_binomial` (Pphi2/NelsonEstimate/WickBinomial.lean:95) — full general-n binomial decomposition of Wick monomials, proven.

2. `roughCovariance_sq_summable` (CovarianceSplit.lean:203):
   `(1/|Λ|) · Σ_k C_R(k)² ≤ T · a^d · wickConstant ≤ T / mass²`
   This is uniform in (a, N) at fixed mass. Proven.

3. `heat_kernel_trace_bound` (HeatKernelBound.lean:278):
   `Σ_k exp(-t · λ_k) ≤ C/t` with C = |Λ|/mass²  — NOT (a, N)-uniform; the textbook (a, N)-uniform `C = O(L^d / mass²)` bound is stated as Phase 2 deliverable in the file's docstring.

4. `heat_kernel_1d_bound` (HeatKernelBound.lean:251):
   `Σ_{k} exp(-t · 4sin²(πk/N)/a²) ≤ C·(1 + 1/√t)` with C = N — trivial bound. Docstring says: "Constant C depends on L = a·N but NOT on N separately" — the textbook (a, N)-uniform version is the actual goal but not proven.

5. `smoothVariance_le_log_uniform` (CovarianceSplit.lean:112):
   `c_S = smoothWickConstant T ≤ smoothVarianceConstant · (1 + |log T|)` with `smoothVarianceConstant = (a^d)⁻¹ · mass⁻²` — NOT (a, N)-uniform. Docstring explicitly says: "trivial constant proof... constant C = (a^d)⁻¹·mass⁻² depending on a but uniform in T. The textbook tight bound C = O(1) (uniform in a) requires sharper Fourier estimates (Glimm–Jaffe Ch. 8) and is the real Phase 2 deliverable."

6. `gff_wickPower_two_site_inner` (being added in gaussian-field): `∫ :φ(x)^n: · :φ(y)^m: dμ_GFF = δ_{nm} · n! · C(x,y)^n` — assumed available.

7. NO L¹ or L^m bounds on rough covariance position-space sums (`Σ_y |C_R(x,y)|^m`).

== Codex's proposed plan structure ==

(S1) Pointwise binomial decomposition:
     E_R = a^d · Σ_x Σ_k Σ_{j=0}^{k-1} P.coeff k · C(k,j) · :φ_S(x)^j:_{c_S} · :φ_R(x)^{k-j}:_{c_R}

(S2) Reindex by (j, m) with m = k-j ≥ 1:
     E_R = Σ_{j ≥ 0, m ≥ 1} A(j,m) · M_{j,m}(η)
     M_{j,m}(η) = a^d · Σ_x :φ_S(x)^j:_{c_S} · :φ_R(x)^m:_{c_R}
     A(j,m) = P.coeff(j+m) · C(j+m, j)

(S3) Cross-term orthogonality on the joint measure (since (φ_S, φ_R) independent):
     ‖E_R‖²_L² = Σ_{j, m≥1} A(j,m)² · ‖M_{j,m}‖²_L²

(S4) Bound each ‖M_{j,m}‖²_L² via gff_wickPower_two_site_inner:
     ‖M_{j,m}‖²_L² = a^{2d} · Σ_{x,y} (j! · C_S(x,y)^j) · (m! · C_R(x,y)^m)
     - m=1: Cauchy-Schwarz on the rough side: √(Σ C_R²) · √(Σ C_S^{2j})  → claimed O(T)
     - m≥2: |C_R(x,y)|^m ≤ ‖C_R‖_∞^{m-2} · C_R(x,y)² → O(T) with ‖C_R‖_∞ factor

(S5) Sum over (j, m), absorb constants into K. Result: ‖E_R‖²_L² ≤ K · T.

== Gemini chat's 4 critiques + my 5th ==

(C1) The ∃K-after-(a,N)-binders signature lets K depend on (a, N), defeating uniformity. FIX: pull (a, N) inside ∀ binder — already in our target signature above.

(C2) S4's m=1 Cauchy-Schwarz gives O(√T)·O(...) which is O(T^{1/2}) for the variance, NOT O(T). The bound is too weak in the wrong direction.
FIX: Don't use C-S for m=1. Use heat-kernel L¹ bound `a^d Σ_y C_R(x,y) ≤ T` (because C_R = ∫_0^T p_t dt where p_t is heat kernel with `a^d Σ_y p_t(x,y) = 1`), and factor out bounded `‖C_S‖_∞^j`. This gives `O(L^d · T)` cleanly.

(C3) S4's m≥2 bound uses `‖C_R‖_∞`, but C_R(x,x) ~ log(1/a) carries the UV divergence in 2D, so `‖C_R‖_∞ → ∞` as a → 0. The bound blows up.
FIX: Don't use L^∞ on C_R. Instead, use the property that in the continuum (log|x|)^m is locally integrable, so the discrete L^m sum is bounded uniformly:
  `a^d Σ_y |C_R(x,y)|^m ≤ C_m · T` for all m ≥ 1
This is a NEW lemma not in the codebase.

(C4) The L^∞-bounded-C_S claim hides a polylog: `c_S ≈ A + B·|log T|`. So K can't be both T-independent AND make K·T a true upper bound. The variance is actually O(T · polylog(1/T)), not O(T).
FIX: Use form (ii) `K · T · (1 + |log T|)^c` or form (iii) `K · T^δ` (since T·polylog ≤ T^δ for any δ ∈ (0,1) at small enough T).

(C5, my addition) The current `smoothVariance_le_log_uniform` is not (a,N)-uniform either — its constant `(a^d)⁻¹·mass⁻²` blows up as a → 0. Same for the underlying `heat_kernel_trace_bound` whose constant has |Λ| in it. The (a,N)-uniform version is acknowledged as Phase 2 work in the codebase's own docstrings.

== Questions for you ==

Q1. Are Gemini chat's 4 critiques correct? In particular, validate or refute:
    (C1) — quantifier hygiene
    (C2) — m=1 needs L¹ heat-kernel argument, not C-S
    (C3) — m≥2 cannot use ‖C_R‖_∞; needs the L^m sum bound axiom
    (C4) — final bound must include polylog T factor or use T^δ

Q2. Is C5 (no a-uniform `‖C_S‖_∞` available yet) a real blocker? Specifically: can Codex still execute the Codex-plan algebraic structure (S1–S3) honestly today, treating the (a,N)-uniform L^p bounds as needed-from-upstream sorries — OR is there a circular dependency that means the whole plan is premature until the upstream bounds land?

Q3. What is the CORRECT form of the rough_error_variance bound? Pick one of:
    (i) K · T (linear)
    (ii) K · T · (1 + |log T|)^c with c = deg P (or deg P · something)
    (iii) K · T^δ for some explicit δ ∈ (0,1)
    Explain the math behind your choice (specifically: where does the polylog or sub-linear power come from, and is c = deg P or some other expression). Give a concrete recommendation Codex can encode.

Q4. List ALL the upstream a-uniform analytic bounds Codex would need, with explicit statements as Lean-style lemmas. Be exhaustive — we've already missed several rounds. For each, say whether it's standard textbook (with reference) and roughly how much work to prove (a few hours / days / weeks).

Q5. Given Q1-Q4, what's the RIGHT plan? Three options on the table:
    (a) Revise the codex plan with Gemini's 4 fixes + the new upstream sorries; hand to Codex; let upstream a-uniform bounds be parallel work.
    (b) Pause Codex; first do the upstream a-uniform bounds (smoothVariance, heat_kernel_trace, plus the new L¹ and L^m on C_R); only then write rough_error_variance.
    (c) Land a NON-uniform-in-a version first (using existing trivial bounds), with a-uniformity explicitly deferred to Phase 2 along with the upstream Glimm-Jaffe Fourier estimates.

Q6. Is there any other concern we've missed? In particular: is Wick orthogonality across DIFFERENT (j, m) pairs in M_{j,m} really clean (the φ_S ⊥ φ_R independence implies the joint measure factorizes, but I want a sanity check that distinct (j, m) give zero cross-expectation given that BOTH sides use Wick subtraction with their own per-site variance), and is gff_wickPower_two_site_inner the right helper or do we need something more general?

Be opinionated. Be specific. Reference Glimm-Jaffe Ch. 8 / Reed-Simon / Janson where appropriate. We trust your domain knowledge over surface intuition.

---

## Gemini reply (received 2026-05-10)

This is an exceptionally sharp mathematical and architectural review of the proposed implementation plan. You and Gemini have successfully identified that the original plan's analytical bounds (S4) collide fatally with the topological limits required for constructive QFT.

Here is the authoritative domain-expert evaluation of your questions, grounded in the standard textbook treatments of the P(Φ)₂ Euclidean field theory (Glimm-Jaffe Ch. 8, Simon's *The P(Φ)₂ Euclidean (Quantum) Field Theory*).

### Meta-Critique: A Fatal Swap in Your Definitions

Before answering the questions, there is a glaring mathematical contradiction in your prompt's preamble that will break the formalization if it exists in your codebase. You wrote:

- C_S has eigenvalues `(1−exp(−Tλ_k))/λ_k`.
- C_R has eigenvalues `exp(−Tλ_k)/λ_k`.

This is mathematically backward.

The operator `∫_0^T e^{−t(−Δ+m²)} dt` has eigenvalues `(1−e^{−Tλ})/λ`. For large λ (UV), this goes to `1/λ`, meaning it contains the entire `x→y` spatial singularity. **This is the rough covariance C_R.**

The operator `∫_T^∞ e^{−t(−Δ+m²)} dt` has eigenvalues `e^{−Tλ}/λ`. For large λ, this decays exponentially, suppressing high frequencies. **This is the smooth covariance C_S.**

If your Lean codebase literally defines C_S using the `(1−exp)` numerator, the physics are completely scrambled. The rest of this review assumes the standard mapping: C_S is the bounded IR piece, and C_R is the UV-divergent piece.

*[Editorial note 2026-05-10: this meta-critique is a typo in the prompt
above, **not** a bug in the codebase. `CovarianceSplit.lean:13–17`
defines roughCovariance with the `(1−exp)` numerator and
smoothCovariance with the `exp` numerator — matching Gemini's standard
mapping. All Q1–Q6 answers below assume the correct convention.]*

### Q1: Are Gemini's 4 critiques correct?

Yes, all four are 100% mathematically and architecturally correct.

**(C1) Quantifier Hygiene:** Absolutely critical. If `∃ K` comes after the `∀ (a, N)` binders, Lean's type theory will Skolemize K into a function `K(a,N)`. A proof could trivially set `K(a,N)` to absorb the `O(log(1/a))` UV divergence, completely destroying the continuum limit downstream. K must be bound as a macroscopic physical constant before the lattice parameters. Your target signature in the prompt gets this right.

**(C2) m=1 C-S trap:** Valid and fatal. Cauchy-Schwarz yields `∑ C_S^j C_R ≤ (∑ C_S^{2j})^{1/2} (∑ C_R²)^{1/2}`. Because `∑_y C_R² = O(T)`, this bounds the variance by `O(T^{1/2})`. In the Nelson multiscale expansion, `T ≪ 1`, so `T^{1/2} ≫ T`. Losing the linear decay breaks the Trotter product convergence. You must use the L^∞ × L^1 bound instead.

**(C3) m≥2 ‖C_R‖_∞ trap:** Valid and fatal. In d=2, the lattice Green's function evaluated at coincident points diverges: `C_R(x,x) ∼ log(T/a²)`. Factoring out `‖C_R‖_∞^{m−2}` injects an explicit `log(1/a)` divergence into your bound, destroying a-uniformity. You must rely on the fact that the continuum singularity `(−log|x|)^m` is locally integrable, meaning the discrete L^m sum over C_R scales gracefully as O(T).

**(C4) Polylog T trap:** Valid. The smooth covariance integrates IR modes down to time T, so `C_S(x,x) ∼ |log T|`. Hiding this in K forces K to depend on T, which violates the theorem's topological requirements for the cluster expansion.

### Q2: Is C5 (lack of a-uniform bounds) a real blocker?

It is a mathematical blocker for the final sorry-free theorem, but it is **NOT** an architectural blocker for Codex.

In large-scale Lean projects, `sorry`'d lemmas act as architectural firewalls. The algebraic Nelson Wick reduction (S1–S3) and the analytical Glimm-Jaffe bounding logic (S4–S5) are completely orthogonal.

Codex can and should execute the algebraic pipeline right now. If you force Codex to use the currently available non-uniform lemmas, you will permanently contaminate the theorem signatures downstream. If you pause the project to prove the Glimm-Jaffe Fourier estimates (weeks of work), the algebra team stalls. **Decouple the algebra from the analysis via targeted upstream axioms.**

### Q3: What is the CORRECT form of the bound?

**Recommendation: Form (ii) — `K · T · (1 + |log T|)^c` where c = deg(P) − 1.**

The Math:

The variance is a finite sum over `j ≥ 0, m ≥ 1` of cross-terms evaluating to:

```
E[M_{j,m}²] = a^{2d} · Σ_{x,y} j! · m! · C_S(x,y)^j · C_R(x,y)^m
```

We bound this via Hölder-style factoring:

```
a^{2d} · Σ_{x,y} C_S(x,y)^j · C_R(x,y)^m ≤
  ‖C_S‖_∞^j · a^d · Σ_x (a^d · Σ_y C_R(x,y)^m)
```

From the heat kernel, the rough covariance satisfies `a^d · Σ_y C_R(x,y)^m ≤ C_m · T` for all `m ≥ 1`.

The volume sum evaluates to `L^d`.

The smooth covariance satisfies `‖C_S‖_∞ ≤ A + B|log T|`.

Because we are bounding the error, `m ≥ 1`. Since the binomial expansion dictates `j + m ≤ deg(P)`, the highest power of φ_S is exactly `j = deg(P) − 1`.

Therefore, the exact upper bound scales as `T · (1 + |log T|)^{deg(P)−1}`. Form (ii) is a direct algebraic match for what pops out of the L^∞ bound. If you use Form (iii) (`T^δ`), you force Codex to prove a messy real-analysis calculus inequality (`T |log T|^c ≤ T^δ`) inside the Wick-algebra file, which invites hallucination loops. Let the downstream Nelson bridge handle the sub-linear fractional power.

### Q4: Exhaustive list of upstream a-uniform analytic bounds

Codex needs exactly **two** analytical sorry'd lemmas to close the proof cleanly. They belong in an upstream file like `CovarianceBounds.lean`. Both are standard textbook results (Glimm-Jaffe Thm 8.5.2) but require non-trivial lattice Fourier integration to prove.

(Note: C_S and C_R are strictly non-negative in position space, so absolute values are safely omitted).

```lean
-- 1. Uniform L^∞ bound on Smooth Covariance
/-- Textbook (a, N)-uniform bound on the smooth covariance. -/
lemma canonicalSmoothCovariance_uniform_bound
    {d : ℕ} (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ C > 0, ∀ (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a) (h_vol : (N : ℝ) * a = L)
      (T : ℝ) (hT : 0 < T) (x y),
        canonicalSmoothCovariance d N a mass T x y ≤ C * (1 + |Real.log T|) := sorry

-- 2. Uniform L^m bound on Rough Covariance
/-- Textbook (a, N)-uniform L^m bound on the rough covariance.
    Valid for all m ≥ 1. Cleanly unifies the m=1 and m≥2 cases into a single O(T) bound. -/
lemma canonicalRoughCovariance_Lm_bound
    {d : ℕ} (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) (m : ℕ) (hm : 1 ≤ m) :
    ∃ C > 0, ∀ (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a) (h_vol : (N : ℝ) * a = L)
      (T : ℝ) (hT : 0 < T) (x),
        a^d * ∑ y, (canonicalRoughCovariance d N a mass T x y) ^ m ≤ C * T := sorry
```

### Q5: The RIGHT Plan

**Proceed with Option (a):** Revise the plan with the 4 fixes + the 2 new upstream sorries.

1. Inject the 2 lemmas from Q4 into the codebase as `sorry`.
2. Revise the target signature to fix the quantifiers and use the `T · (1 + |log T|)^c` RHS.
3. Instruct Codex to execute S1–S3 exactly as originally planned.
4. **Rewrite S4 instructions:** Tell Codex: *"Do not case-split on m. For all `m ≥ 1`, factor out `‖C_S‖_∞^j` using `canonicalSmoothCovariance_uniform_bound`, and sum the remaining `C_R^m` strictly using `canonicalRoughCovariance_Lm_bound`."*

This guarantees the architecture works, completely solves the probability milestone, and securely quarantines the hard harmonic analysis for Phase 2.

### Q6: Wick Orthogonality Sanity Check & The Measure Theory Trap

Your mathematical intuition is flawless. For a cross-term corresponding to `(j,m)` and `(j′, m′)`:

```
E_μ[:φ_S^j: :φ_R^m: :φ_S^{j′}: :φ_R^{m′}:] =
  E_S[:φ_S^j: :φ_S^{j′}:] · E_R[:φ_R^m: :φ_R^{m′}:]
```

By `gff_wickPower_two_site_inner`, the smooth expectation is strictly 0 if `j ≠ j′`, and the rough expectation is 0 if `m ≠ m′`. Distinct pairs vanish perfectly.

**The Lean Trap:** Codex will expand the squared polynomial into a quadruple sum. To collapse this into the sum of squares, Codex must invoke the statistical independence of φ_S and φ_R to split the integral of the product into the product of the integrals. Lean's measure theory library does not do this automatically. It requires proving that the functions are `Integrable`, which will drown Codex in L^p typeclass subgoals.

**The Fix:** You must provide a "Wick Factorization" helper lemma (even as a `sorry` for Phase 2) so Codex doesn't have to fight Mathlib's measure theory to split the joint expectation:

```lean
/-- Factorization of independent Wick monomials over the joint measure. -/
lemma joint_wick_factorization {d N : ℕ} [NeZero N] (a mass T : ℝ)
    (j m j' m' : ℕ) (x y : FinLatticeSites d N) :
  ∫ η, (wickMonomial j c_S (canonicalSmoothFieldFunction d N a mass η x)) *
       (wickMonomial m c_R (canonicalRoughFieldFunction d N a mass η x)) *
       (wickMonomial j' c_S (canonicalSmoothFieldFunction d N a mass η y)) *
       (wickMonomial m' c_R (canonicalRoughFieldFunction d N a mass η y))
       ∂(canonicalJointMeasure d N a mass) =
  (∫ η_S, wickMonomial j c_S (φ_S x) * wickMonomial j' c_S (φ_S y) ∂μ_S) *
  (∫ η_R, wickMonomial m c_R (φ_R x) * wickMonomial m' c_R (φ_R y) ∂μ_R) := sorry
```

(Adjust the precise terms for `φ_S`, `μ_S` to match your `FieldDecomposition` API).

By giving Codex this factorization lemma + `gff_wickPower_two_site_inner` + the 2 analytic bounds, Steps S1–S5 become a pure algebraic manipulation puzzle, which LLMs are incredibly good at formalizing.
