# Cylinder construction — conditional inputs and their provability

*2026-05-27. A vetting map for the isotropic `Z_Nt × Z_Ns` cylinder construction
(`AsymTorus/AsymContinuumLimit.lean`). Lists every non-Mathlib input the cylinder
OS0–OS3 theorem rests on, with its exact statement, role, mathematical content,
references, and a provability verdict. The point is to let you check that each
input is (a) true and (b) formalizable, and to flag one input that is currently
**mis-stated** in Lean.*

---

## 0. Logical structure

The top-level theorem is

```
routeBPrimeIso_cylinder_OS
    (P mass hmass) (Knel hKnel_pos hKnel_uniform) (hRP) (hOS2)
  : ∃ ν, IsProbabilityMeasure ν ∧ (cylinder OS0 ∧ OS2-refl ∧ OS2-time ∧ OS2-space ∧ OS3)
```

Everything **below** the dotted line is a *theorem* (no axioms beyond the two isotropic
axioms + Mathlib's `propext/Choice/Quot.sound`). Everything **above** is an explicit
hypothesis whose provability we must vet.

```
                       routeBPrimeIso_cylinder_OS            (this file's subject)
                      /            |             \
       hKnel_uniform        hRP (OS3)        hOS2          ← 3 explicit hypotheses
         (§4 — FLAG)        (§5)             (§6)
            |
   asymTorusIso_cylinderUniformGreenBound                  ← builds the IR family + uniform Green bound
            |
   asymTorusIso_measureHasGreenMomentBound(_of_nelson)     ← MeasureHasGreenMomentBound = THEOREM (per Lt)
        /        |          \
  cutoff bound  UV limit   weakLimit_exponential_moment
  (Phase 2)     (tightness+Prokhorov)   (truncation+MCT)
      |
  asymNelson_exponential_estimate_iso
      |
  asymChaosCutoffDecomposition (§2)  +  wickConstantAsym_eq_variance (§1)
      |                                          + GaussianField.embed_l2_uniform_bound (§3, via routeBPrime)
```

`#print axioms` (2026-05-27, after §1 discharge):
- `asymTorusIso_measureHasGreenMomentBound` / `asymTorusIso_cylinderUniformGreenBound` /
  `routeBPrimeIso_cylinder_OS` (the conditional theorems):
  `[propext, Classical.choice, Quot.sound, asymChaosCutoffDecomposition]`
  (`routeBPrimeIso_cylinder_OS` additionally `+ GaussianField.embed_l2_uniform_bound`).
- `cylinderIso_OS_of_RP_OS2` (the §4-unconditional theorem): the above **+**
  `asymInteracting_expMoment_volume_uniform`.

So now: **two** project axioms (§2, §4), one upstream gaussian-field axiom (§3), and two remaining
hypotheses (§5 OS3, §6 OS2). §1 `wickConstantAsym_eq_variance` was discharged to a theorem (so it no
longer appears above); §4 was promoted from hypothesis to a vetted axiom.

---

## 1. `wickConstantAsym_eq_variance` — **DISCHARGED → theorem** (2026-05-27)

> **Update.** No longer an axiom. Proved in `AsymTorus/AsymWickVariance.lean` by the algebraic
> circulant route predicted below: `massOperatorAsym_translation_commute` +
> `spectralCovAsym_massOperator_eq` + shift isometry ⟹
> `covariance_spectralLatticeCovarianceAsym_translation_invariant` ⟹ the diagonal is constant =
> `(1/|Λ|)Σ_k λ_k⁻¹` (orthonormality of `massEigenvectorBasisAsym`), times the GJ `(a²)⁻¹` factor.
> `#print axioms wickConstantAsym_eq_variance = [propext, Classical.choice, Quot.sound]`. The
> original statement/justification is retained below for the record.

```lean
axiom wickConstantAsym_eq_variance (Nt Ns) [NeZero Nt] [NeZero Ns] (a mass) (ha : 0<a) (hmass : 0<mass)
    (x : AsymLatticeSites Nt Ns) :
    wickConstantAsym Nt Ns a mass =
    ⟪latticeCovarianceAsymGJ Nt Ns a mass ha hmass (asymLatticeDelta Nt Ns x),
      latticeCovarianceAsymGJ Nt Ns a mass ha hmass (asymLatticeDelta Nt Ns x)⟫
```

**Role.** Site variance `Var[ω(δ_x)] = wickConstantAsym` at every site `x`. Feeds the Wick
mean-zero chain → `partitionFunctionAsym_ge_one` (`Z ≥ 1`) → `density_transfer_bound_iso`.

**Math.** The spatial *average* of the diagonal already equals `wickConstantAsym` by eigenbasis
orthonormality (`Σ_x e_k(x)² = 1`). The only content is site-*independence* = translation
invariance of the diagonal of `(−Δ_a + m²)^{-1}`, which is **circulant** on the finite abelian
group `Z_Nt × Z_Ns`.

**Provability: HIGH (standard, unconditionally true).** Circulant-matrix diagonals are constant.
The square analogue `wickConstant_eq_variance` is *proved* (`ContinuumLimit/Hypercontractivity.lean`)
via the finite-dim Lebesgue-density representation + a volume-preserving lattice shift. Discharge
= port that, or derive site-independence algebraically from the DFT shift identities
(`cos_shift_sum`/`sin_shift_sum`). Deep-think vetted **Standard / Likely correct** (2026-05-27).

---

## 2. `asymChaosCutoffDecomposition` — **axiom** (`AsymTorus/AsymNelson.lean`)

```lean
axiom asymChaosCutoffDecomposition (P) (mass) (hmass) (Lt Ls) (hLt hLs) :
    ∃ ψ : ℝ → ℝ≥0∞, (∫⁻ M in Ioi 0, ψ M · ofReal(2 e^{2M}) < ⊤) ∧
      ∀ (Nt Ns) [NeZero][NeZero] (a) (ha), Nt·a=Lt → Ns·a=Ls →
        ∃ V_S E_R, (∀ M ω, V_a = V_S M ω + E_R M ω) ∧ (∀ M ω, -(M/2) ≤ V_S M ω) ∧
          (∀ M>0, μ_GFF{E_R M ≤ -(M/2)} ≤ ψ M)
```

**Role.** The Glimm–Jaffe dynamical-cutoff smooth/rough chaos decomposition. Feeds the proved
generic engine `bridgeAxiom_of_setup_real_generic` → `asymNelson_exponential_estimate_iso`
(`∫ e^{-2V} dμ_GFF ≤ K` at fixed `(Lt,Ls)`).

**Math.** `ψ` is super-exponentially small and **uniform in `(Nt,Ns,a)` at fixed volume `Lt·Ls`**.
This is the genuine analytic core of Nelson's estimate.

**Provability: MEDIUM (true; substantial port).** The square analogue is a *proved theorem*
(`nelson_exponential_estimate_master`, 0 axioms) sitting on ~15.5K lines of
`FieldDecomposition`/`RoughErrorBound`/`CovarianceBoundsGJ`. Discharge = port that machinery to
`Z_Nt × Z_Ns` using the Phase-1b heterogeneous DFT. Deep-think vetted **Standard / Likely
correct** (2026-05-27): uniformity at fixed volume confirmed (Simon V.12/V.15); the UV singularity
is isotropic so the rectangle adds no obstruction.

> **Note the scope:** this axiom gives `K` uniform in `(Nt,Ns,a)` *at fixed volume*. It says
> **nothing** about uniformity across different `Lt` (different volume). That is §4.

---

## 3. `GaussianField.embed_l2_uniform_bound` — **axiom** (`gaussian-field Cylinder/MethodOfImages.lean`)

```lean
axiom embed_l2_uniform_bound :
    ∃ q : Seminorm ℝ (CylinderTestFunction Ls), Continuous q ∧
      ∀ (Lt) [Fact (0<Lt)], 1 ≤ Lt → ∀ f,
        l2InnerProduct (cylinderToTorusEmbed Ls Lt f) (cylinderToTorusEmbed Ls Lt f) ≤ q f ^2
```

**Role.** Pulled in by `routeBPrime_cylinder_OS` (the IR tightness input). Bounds the `ℓ²` norm of
the cylinder→torus embedding **uniformly in `Lt ≥ 1`**, by a fixed continuous seminorm.

**Math.** Periodization of a rapidly decaying function: `‖embed(f)‖²` is controlled by Schwartz
seminorms of `f`, uniformly in the period. Proof sketch (in the docstring): pure-tensor
factorization through `l2InnerProduct_swap`/`l2InnerProduct_pure` + the periodization uniform
bound + DM-basis expansion. Reference: Stein–Weiss Ch. VII.

**Provability: HIGH (standard harmonic analysis).** Pre-existing gaussian-field axiom (not
introduced by this work); independent of the isotropic redesign. Discharge = the periodization
estimate, fully sketched.

---

## 4. The volume-uniform exp-moment input  **(corrected 2026-05-27 — now form (★))**

> **History.** The first cut of `asymTorusIso_cylinderUniformGreenBound` /
> `routeBPrimeIso_cylinder_OS` took the hypothesis
> `hKnel_uniform : ∀ L>0 …, ∫ e^{-2V_Λ} dμ_GFF ≤ Knel` (uniform Nelson `L²` across periods). **That
> form is FALSE** (see below), so the theorem was vacuous. It has been **replaced** by the
> interacting-moment form (★); the verdict below applies to (★).

The current hypothesis of both theorems:

```lean
(K : ℝ) (hK_pos : 0 < K)
(hUnif : ∀ (L : ℝ) [Fact (0 < L)] (Nt Ns) [NeZero][NeZero] (a) (ha), Nt·a = L → Ns·a = Ls → ∀ f,
    Integrable (e^{|ωf|}) (asymTorusInteractingMeasureIso L Ls Nt Ns a P mass ha hmass) ∧
    ∫ e^{|ωf|} ∂(asymTorusInteractingMeasureIso L Ls Nt Ns a P mass ha hmass)
      ≤ K · e^{∫ (ω·asymLatticeTestFnIso L Ls Nt Ns a f)² dμ_GFF})            -- (★)
```

i.e. the **interacting** exp-moment `∫ e^{|ωf|} dμ_int ≤ K·e^{σ²}`, uniform in the period `L` (the
`σ²` Green-control on the RHS is allowed to depend on `f`, `L`; only the prefactor `K` must be
uniform).

**Why the naive `∫ e^{-2V} ≤ Knel` form was FALSE (and is no longer used).**

`∫ e^{-2V_Λ} dμ_GFF` **grows exponentially in the volume `|Λ|`.** Heuristically the sites
decorrelate, so `∫ e^{-2V_Λ} ≈ ∏_{x∈Λ} E[e^{-2a²:P(φ_x):}]`, and each factor is `≥ 1` by Jensen
(Wick mean zero) and strictly `> 1` (Jensen is strict, `Var>0`). Hence `∫ e^{-2V_Λ} ≳ (1+ε)^{|Λ|}
→ ∞`. This is exactly the "linear lower bound" `V_Λ ≥ -c|Λ| ⟹ ∫ e^{-2V} ≤ e^{2c|Λ|}` of
Glimm–Jaffe Ch. 18 — a **volume-dependent** bound, never uniform.

**Why the construction nonetheless wants a uniform `Knel`.** The cutoff bound (Phase 2) reads
`∫ e^{|ωf|} dμ_int ≤ √(2 K_Nelson)·e^{σ²}`, where `K_Nelson = ∫ e^{-2V}` and the prefactor came
from `density_transfer_bound_iso` using only `Z⁻¹ ≤ 1` (`Z ≥ 1`). Since `K_Nelson ~ e^{c|Λ|}`, the
prefactor `√(2K_Nelson) ~ e^{c|Λ|/2}` is volume-dependent. **The `Z⁻¹ ≤ 1` step is the culprit:
it throws away the pressure.**

**The correct volume-uniform input.** What is actually true and uniform is the bound on the
**interacting** exponential moment:

```
∃ K, ∀ Λ (fixed Ls, any Lt),  ∫ e^{|ω f|} dμ_int,Λ ≤ K · e^{σ²_Λ(f)}      (★)
```

This holds because `μ_int = Z⁻¹ e^{-V} dμ_GFF` and the **pressure** `Z = ∫ e^{-V} ≥ e^{p|Λ|}` with
`p ≥ c/2` *cancels* the `K_Nelson ~ e^{c|Λ|}` growth:
`Z⁻¹ K_Nelson^{1/2} ≤ e^{-p|Λ|} e^{c|Λ|/2} = e^{(c/2-p)|Λ|}`, bounded iff `p ≥ c/2`.
The inequality `p ≥ c/2` ("pressure dominates the linear lower bound") is **the** deep
constructive-QFT input — `MomentBoundOS1.lean`'s docstring flags it precisely: *"these do not
cancel cleanly; volume-independent bounds require locality — cluster expansion (weak coupling),
correlation inequalities (GKS/FKG), or chessboard estimates (reflection positivity).
Glimm–Jaffe–Spencer-level."*

**Provability of (★): TRUE but DEEP.** The uniform finiteness of P(φ)₂ interacting exp-moments is
*the* central theorem of constructive P(φ)₂ (Glimm–Jaffe Ch. 18–19; Simon Ch. V, VIII;
Glimm–Jaffe–Spencer cluster expansion). It is comparable in difficulty to `spectral_gap_uniform`.

**Cylinder discharge shortcut (external review, 2026-05-27).** The full *spatial* cluster expansion
is **not** needed here. With `Ls` fixed and `L → ∞`, this is a **1D** thermodynamic limit — no phase
transition — and the transfer matrix `T = e^{-aH_{Ls}}` has a strictly isolated, non-degenerate
maximal eigenvalue by the infinite-dimensional Perron–Frobenius theorem. Hence the cylinder mass gap
`m₁ > 0` is *unconditional* and the susceptibility stays bounded as `L → ∞`. The bound is then
dischargeable via **chessboard estimates (Fröhlich–Simon–Spencer) + the transfer-matrix spectral
radius**, saving the bulk of a spatial-cluster-expansion formalization. (`spectral_gap_uniform` in
the square track is the analogous transfer-matrix-gap input.)

**Lean correction (applied 2026-05-27).** The hypothesis is now form (★) above. Internally a new
`asymTorusIso_measureHasGreenMomentBound_of_cutoff` threads the uniform `K` directly (the old
`_of_nelson` is kept as the `√(2·Knel)` specialization), so the weak-limit transfer
(`weakLimit_exponential_moment`) gives `MeasureHasGreenMomentBound … K 1 μ` with uniform `K`. The
per-`Lt` machinery is unchanged; only the *source* of the uniform constant moved from "uniform
Nelson `L²`" (false) to "uniform interacting moment" (true, deep). The assembly stays axiom-free
and isolates the one genuine cluster-expansion input as an honest, true hypothesis.

---

## 5. `hRP` — OS3 reflection positivity (`CylinderMeasureSequenceEventuallyReflectionPositive`)

```lean
(hRP : ∀ (Lt) (hLt) (μ),
    CylinderMeasureSequenceEventuallyReflectionPositive Ls
      (fun n => cylinderPullbackMeasure (Lt n) Ls (μ n)))
-- where the predicate is:  ∀ n f c, ∀ᶠ k in atTop, CylinderRPMatrixNonnegative Ls (νseq k) n f c
```

**Role.** OS3 (reflection positivity) of the cylinder-pullback measures, eventually in the IR
index. Feeds `routeBPrime_cylinder_OS`, which transfers it through the weak limit
(`cylinderMeasureReflectionPositive_of_tendsto_cf`).

**Math.** RP is preserved under: (i) the lattice measure (RP of `Z_Nt × Z_Ns` with the reflection
across a time hyperplane — a Gaussian/Markov-field RP, standard for nearest-neighbour actions),
(ii) the embedding pullback, (iii) the UV continuum limit, (iv) the IR weak limit. The lattice RP
is the Osterwalder–Seiler / Nelson reflection-positivity of the lattice transfer matrix.

**Provability: MEDIUM–HIGH (standard, but a separate development).** Lattice RP for reflection-
symmetric nearest-neighbour Gaussian + even interaction is textbook (Glimm–Jaffe Ch. 6, 10;
Osterwalder–Seiler). The pphi2 square track already has an RP layer (`OS3_RP_Lattice`,
`OS3_RP_Inheritance`). RP survives the UV and IR weak limits natively (closed condition,
non-strict inequality).

**Even-`Nt` requirement (external review, 2026-05-27) — now satisfied.** Lattice RP on a periodic
*time* torus `Z_Nt` needs `Nt` **even**, so the two reflection planes sit between sites and split
the torus into two equal halves (no fixed-site obstruction). The IR-family construction in
`asymTorusIso_cylinderUniformGreenBound` was updated to the exactly-isotropic sequence
`Nt_k = 2(n+1)(k+1)`, `Ns_k = 2(k+1)`, `a_k = Ls/(2(k+1))` — **both extents even** — keeping
`Lt n = (n+1)·Ls` and `a_k → 0`. So the family fed to the IR limit is OS3-ready.

**Caveat on the `hRP`/`hOS2` shape.** In `routeBPrimeIso_cylinder_OS` / `cylinderIso_OS_of_RP_OS2`
these are stated `∀ (Lt) (hLt) (μ), …` (all families). That is *over-strong*: a genuine OS3 proof
establishes RP for the **specific** even-`Nt`-derived family the construction produces, not for
arbitrary `μ`. The honest usage is to `obtain` the family from
`asymTorusIso_cylinderUniformGreenBound` and apply the proved `routeBPrime_cylinder_OS` with RP/OS2
for *that* family. A future refinement narrows the hypotheses to the constructed family (it is
left ∀-quantified now only because that family is `Classical.choose`-constructed and unnamed). This
input is *independent* of the moment bounds and belongs to the cyl-OS3 work-stream.

---

## 6. `hOS2` — Euclidean symmetry (`AsymTorusSequenceHasCylinderOS2Symmetry`)

```lean
(hOS2 : ∀ (Lt) (hLt) (μ), AsymTorusSequenceHasCylinderOS2Symmetry Ls Lt hLt μ)
-- predicate:  (∀ n, ∀ v f, ∫ e^{iω f} dμ = ∫ e^{iω (asymTorusTranslation v f)} dμ)
--           ∧ (∀ n, ∀ f,   ∫ e^{iω f} dμ = ∫ e^{iω (asymTorusTimeReflection f)} dμ)
```

**Role.** OS2 (Euclidean invariance): the torus measures are invariant under the `(time,space)`
translations and time reflection of the torus; `routeBPrime_cylinder_OS` pushes this to cylinder
time-translation, space-translation, and time-reflection invariance.

**Math.** The lattice measure on `Z_Nt × Z_Ns` is invariant under the **discrete** translation
group (the action and the Wick constant are translation-invariant — same circulant fact as §1) and
under the time reflection (the action is reflection-symmetric). The torus translations
`asymTorusTranslation` act through the embedding; invariance passes to the UV continuum limit by
characteristic-functional convergence.

**Provability: HIGH (standard, follows the §1 circulant structure).** Discrete translation +
reflection invariance of the lattice Gibbs measure is immediate from invariance of the action and
the homogeneous (site-independent) Wick ordering. Continuum rotation invariance (full OS2 on `ℝ²`)
would be harder (the lattice breaks rotations — the `OS2_WardIdentity` anomaly story), but the
**cylinder** OS2 only needs translations + time reflection, which the lattice has exactly. Left as
a hypothesis here because it is a separate (easy) development.

---

## 7. Summary verdict

| Input | Status | True? | Provability | Notes |
|---|---|---|---|---|
| §1 `wickConstantAsym_eq_variance` | **DISCHARGED → theorem** | ✅ | done | circulant diagonal; proved 2026-05-27 (`AsymWickVariance.lean`) |
| §2 `asymChaosCutoffDecomposition` | axiom | ✅ | **Medium** | port 15.5K-line square Nelson machinery |
| §3 `embed_l2_uniform_bound` | axiom (upstream) | ✅ | **High** | periodization, Stein–Weiss; pre-existing |
| §4 volume-uniformity (★) | **axiom** `asymInteracting_expMoment_volume_uniform` | ✅ (form `K·e^{C·σ²}`) | **Deep** (the real one) | DT-vetted with `∃C`; cluster-expansion / mass-gap |
| §5 `hRP` (OS3) | hypothesis | ✅ | Medium–High | lattice RP + weak-limit inheritance |
| §6 `hOS2` | hypothesis | ✅ | High | discrete translation/reflection invariance |

**The one genuinely deep input is §4** (the volume-uniform interacting exp-moment, ≡ pressure
dominates the linear lower bound, ≡ cluster expansion). Everything else is either a standard fact
or a mechanical port of already-proved square-track material.

**Status (2026-05-27):** §4 is the true interacting-moment form (★), a deep-think-vetted `axiom`
`asymInteracting_expMoment_volume_uniform`; `cylinderIso_OS_of_RP_OS2` gives cylinder
OS0/OS1/OS2/OS3 unconditional in §4 (only §5/§6 remain as hypotheses). **§1 has been discharged to a
theorem.** pphi2 on the branch: **21 raw / 19 real axioms**, 0 sorries. The two remaining isotropic
axioms are §2 `asymChaosCutoffDecomposition` (port of proved square Nelson machinery) and §4 (the
genuine cluster-expansion / transfer-matrix-gap result); plus the §5–§6 hypotheses (lattice RP +
symmetry — see `cylinder-os3-discharge-plan.md`).
