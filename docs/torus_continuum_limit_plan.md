# Torus Continuum Limit: OS Axioms Plan

## Goal

Prove OS axioms OS0–OS3 for **both** the Gaussian and interacting P(φ)₂
continuum limit measures on the torus T²_L. The torus approach isolates
the UV limit (a = L/N → 0) from IR issues by fixing the physical volume L.

**Current state (2026-03-03):**

| | Gaussian | Interacting |
|--|----------|-------------|
| Limit exists | PROVED (full sequence) | PROVED (subsequential) |
| OS0 (Analyticity) | sorry | not started |
| OS1 (Regularity) | sorry | not started |
| OS2 (Translation+D4) | PROVED | not started |
| OS3 (Reflection Positivity) | PROVED | not started |
| `SatisfiesTorusOS` | assembled (2 sorries) | not started |

7 files in `TorusContinuumLimit/`, 15 torus axioms, 2 sorries.

## Architecture

The OS axiom definitions (`SatisfiesTorusOS`) are measure-agnostic — they
apply to any probability measure on `Configuration(TorusTestFunction L)`.
The Gaussian and interacting cases share the same axiom bundle but have
different proof paths.

```
                        SatisfiesTorusOS L μ
                       (measure-agnostic bundle)
                      ╱                        ╲
    Gaussian proof path                  Interacting proof path
    ───────────────────                  ──────────────────────
    OS0: exp(-½Q) entire                 OS0: exponential moments
    OS1: ‖Z[J]‖ ≤ exp(c·q(J))           OS1: ‖Z[J]‖ ≤ exp(c·q(J))
    OS2: G_L invariance                  OS2: V_a invariance
    OS3: rp_closed_under_weak_limit      OS3: rp_closed_under_weak_limit
         + torusLattice_rp                    + interacting lattice RP
         + full sequence convergence          + subsequential convergence
```

## Phase 1: Complete Gaussian OS (fill 2 sorries)

### 1a. `torusGaussianLimit_os1` — OS1 (needs characteristic functional axiom)

The complex generating functional `Z[f_re, f_im] = ∫ exp(iω(f_re) - ω(f_im)) dμ`
satisfies `‖Z[f_re, f_im]‖ ≤ exp(c · (q(f_re) + q(f_im)))` for a continuous
seminorm `q` on the torus test function space.

For Gaussian μ with covariance G_L, the bound holds with `q(f) = G_L(f,f)` and
`c = ½`, since `|exp(-½ G_L(f_re+if_im, f_re+if_im))| ≤ exp(½ G_L(f_im,f_im))`.

### 1b. `torusGaussianLimit_os0` — OS0 (straightforward, uses char. func. axiom)

By `torusGaussianLimit_characteristic_functional`, `Z[Σ zᵢJᵢ]` =
`exp(-½ Σᵢⱼ zᵢzⱼ G(Jᵢ,Jⱼ))`. Re of this is a real-analytic function of
z ∈ ℝⁿ (composition of polynomial with exp).

## Phase 2: Interacting OS3 (Reflection Positivity)

OS3 is the easiest interacting axiom because `rp_closed_under_weak_limit`
is already proved and applies to any weak limit of RP measures.

### 2a. Interacting lattice RP

Need: `IsRP (torusInteractingMeasure L N P mass hmass) (torusConfigReflection L) (torusRP_admissible L)`

The interacting measure `dμ_P = (1/Z) e^{-V} dμ_{GFF}` is RP because:
- The GFF is RP (transfer matrix `H ≥ 0`)
- The Wick-ordered interaction `V = Σ_x :P(φ(x)):` decomposes as `V = V_+ + V_-`
  where `V_±` depend on the positive/negative time sites respectively
- The Boltzmann weight `e^{-V} = e^{-V_+} · e^{-V_-}` factors, preserving the
  RP structure

This is a new axiom (or provable from `torusLattice_rp` + interaction structure).

**Reference:** Glimm-Jaffe §6.3, Simon Ch. II.

### 2b. Thread subsequence through RP closure

`torusInteractingLimit_exists` gives `(φ, μ, StrictMono φ, IsProbabilityMeasure μ, weak convergence along φ)`.
Need to apply `rp_closed_under_weak_limit` with the subsequential measures
`fun n => torusInteractingMeasure L (φ n + 1) P mass hmass`.

This is a straightforward adaptation of `torusGaussianLimit_os3` —
the only difference is using subsequential convergence instead of full
sequence convergence.

## Phase 3: Interacting OS1 (Regularity)

`‖Z[f_re, f_im]‖ ≤ exp(c · (q(f_re) + q(f_im)))` for a continuous seminorm q.
For the interacting case, the bound follows from Nelson's hypercontractive estimate,
which controls exponential moments of the field. Needs an axiom for interacting
exponential moments (similar to `continuum_exponential_moments`).

## Phase 4: Interacting OS2 (Symmetry)

### 4a. Translation invariance

The lattice interaction is translation-invariant (`latticeAction_translation_invariant`
is proved). The lattice GFF is translation-invariant. Therefore the interacting
lattice measure is translation-invariant, and this transfers to the limit.

Two approaches:
1. **Direct:** Prove the interacting lattice generating functional is
   translation-invariant, then transfer by weak convergence.
2. **Via covariance:** If the limit measure is determined by its Schwinger
   functions, and the Schwinger functions inherit lattice translation
   invariance, then the limit is translation-invariant.

Approach 1 is cleaner. Need axiom or proof:
- `torusInteractingMeasure_translation_invariant`: `Z_P[T_v f] = Z_P[f]`
  for all lattice translation vectors v.

### 4b. D4 invariance

Similar to translation invariance: the lattice action is D4-invariant
(nearest-neighbor interactions are symmetric under the square lattice point group).

Need axiom or proof:
- `torusInteractingMeasure_D4_invariant`: `Z_P[σf] = Z_P[f]` for σ ∈ D4.

### 4c. Transfer to continuum

Weak convergence: if `Z_N[σf] = Z_N[f]` for all N, and `Z_N → Z` pointwise,
then `Z[σf] = Z[f]`. This is immediate from the convergence.

## Phase 5: Interacting OS0 (Analyticity)

This is the hardest axiom for the interacting case.

OS0 requires `Re(Z[Σ zᵢJᵢ])` to be real-analytic on ℝⁿ. For the Gaussian
this was trivial (exp of quadratic). For the interacting case, this requires
showing the measure has all exponential moments:

`∫ exp(c|ω(f)|) dμ < ∞` for all c > 0, f ∈ TorusTestFunction L.

On the finite torus, this should follow from:
1. The interacting measure has density `(1/Z) e^{-V}` w.r.t. the GFF
2. V is bounded below (proved: `latticeInteraction_bounded_below`)
3. The GFF has all Gaussian moments
4. On the torus, the interaction is a polynomial in finitely many
   Gaussian variables, so all moments are finite

The transfer to the continuum limit requires uniform moment bounds
(analogue of `continuum_exponential_moments`).

**Difficulty:** Medium-Hard. Needs Nelson-type estimates on the torus.

## Phase 6: Assembly

### 6a. `IsTorusInteractingContinuumLimit` predicate

Define a predicate for the interacting continuum limit, analogous to
`IsTorusGaussianContinuumLimit`. Should include:
- `IsProbabilityMeasure μ`
- Z₂ symmetry (inherited from the even polynomial P)
- Weak limit of interacting lattice measures

### 6b. `torusInteractingLimit_satisfies_OS`

Assemble OS0–OS3 for the interacting case.

### 6c. `torusInteractingOS_exists`

Master existence theorem:
```
theorem torusInteractingOS_exists (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ (μ : Measure (Configuration (TorusTestFunction L)))
      (_ : IsProbabilityMeasure μ),
      @SatisfiesTorusOS L hL μ ‹_›
```

## New Axioms Needed for Interacting OS

| Axiom | Difficulty | Phase |
|-------|-----------|-------|
| Interacting lattice RP | Easy-Med | 2a |
| Interacting exponential moments (torus) | Med | 3 |
| Interacting translation invariance (lattice) | Easy | 4a |
| Interacting D4 invariance (lattice) | Easy | 4b |
| Interacting exponential moments (continuum transfer) | Med-Hard | 5 |

Total: ~5 new axioms for the interacting case.

## Dependency Graph

```
Phase 1 (Gaussian sorries)         independent, do first
  ├─ 1a: OS1 (straightforward, uses char. func. axiom)
  └─ 1b: OS0 (straightforward, uses char. func. axiom)

Phase 2 (Interacting OS3)          needs: interacting lattice RP axiom
  ├─ 2a: interacting lattice RP
  └─ 2b: thread subsequence

Phase 3 (Interacting OS1)          needs exponential moment axiom

Phase 4 (Interacting OS2)          needs: lattice symmetry axioms
  ├─ 4a: translation invariance
  ├─ 4b: D4 invariance
  └─ 4c: transfer to limit

Phase 5 (Interacting OS0)          hardest, needs moment bounds
  └─ exponential moments

Phase 6 (Assembly)                 depends on all above
```

## Implementation Order

1. Fill Gaussian OS1 sorry (Phase 1a) — straightforward
2. Fill Gaussian OS0 sorry (Phase 1b) — straightforward
3. Add interacting lattice RP axiom + prove OS3 (Phase 2)
4. Prove interacting OS1 (Phase 3) — needs exponential moment axiom
5. Add symmetry axioms + prove OS2 (Phase 4)
6. Add moment axiom + prove OS0 (Phase 5)
7. Assembly + master theorem (Phase 6)

## Success Criteria

- `torusGaussianLimit_satisfies_OS` compiles with no sorry
- `torusInteractingLimit_satisfies_OS` compiles (with axioms, no sorry)
- `torusInteractingOS_exists` master theorem
- `lake build` passes
- Total new axiom count ≤ 4
