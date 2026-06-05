# Scope report — strengthening `IsPphi2Limit` to exclude δ₀

**Why** (see memory `pphi2-existence-vacuous-delta0`): `IsPphi2Limit μ P mass`
(`Embedding.lean:350`) has `_P, _mass` unused — its approximating sequence `ν : ℕ → Measure` is
free, so `ν k ≡ δ₀` satisfies every clause and `pphi2_limit_exists` proves existence with
`Measure.dirac 0`. The headline `pphi2_existence` is therefore witnessed by δ₀. This report maps
exactly what changes before touching the central predicate.

## The def change (recommended: minimal-append)
`continuumMeasure d N P a mass ha hmass` (`Embedding.lean:312`) = pushforward of the interacting
lattice measure — the honest `ν k`. It needs a **lattice size `N k`** and the IR coupling. Append
one conjunct to the existing body (keeps all 8 current clauses in place → minimal consumer churn):

```lean
def IsPphi2Limit (μ) (P) (mass) : Prop :=
  ∃ (a : ℕ → ℝ) (ν : ℕ → Measure FieldConfig2),
    (… the 8 existing clauses, UNCHANGED …) ∧
    (∃ (N : ℕ → ℕ),                                   -- NEW conjunct (appended)
      Filter.Tendsto N atTop atTop ∧
      Filter.Tendsto (fun k => (N k : ℝ) * a k) atTop atTop ∧
      ∀ k, ν k = continuumMeasure 2 (N k) P (a k) mass (ha_pos k) hmass)
```
Now `P, mass` are used; δ₀ ≠ `continuumMeasure 2 (N k) P (a k) mass` for `P ≠ 0`, so δ₀ is excluded.
(Alternative "clean-replace": drop `∃ ν` and substitute `continuumMeasure …` throughout — semantically
nicer but rewrites every destructure; not recommended for a first pass.)

## PRODUCERS that break (must now exhibit the coupled `continuumMeasure` sequence — δ₀/identity can't)
1. **`pphi2_limit_exists`** (`Convergence.lean:282`) — the δ₀ proof dies. **This is the intended
   break.** Becomes the genuine existence obligation (tightness/Prokhorov on the real interacting
   family). See "New obligations" — may be provable from existing infra, else 1 honest axiom.
2. **`IsPphi2ContinuumLimit.toIsPphi2Limit`** (`Bridge.lean:198`, `:= h`) — identity coercion on
   "identical bodies". Fix: **co-strengthen `IsPphi2ContinuumLimit`** with the same appended conjunct
   (it is the Bridge type-alias twin) so `:= h` still typechecks. (+1 co-edit, no proof work.)
3. **`mass_reparametrization_invariance`** (`Main.lean:270`, `:= h_limit`) — currently claims
   `IsPphi2Limit μ P mass → IsPphi2Limit μ (P.shiftQuadratic …) mass'` **by identity**, which only
   typechecks because P,mass are unused. **Another vacuous-predicate artifact.** Under the fix it
   breaks: a limit for `(P,mass)` is not *literally* one for the shifted params — the concrete
   `continuumMeasure` sequences differ. Needs either a real reparametrization lemma (the shifted
   lattice measure equals the original after the quadratic shift — plausibly true and provable from
   `interactingLatticeMeasure`'s definition) or restriction/removal. **Flag for the owner.**
4. **`mass_reparametrization_exists`** (`Main.lean:284`) — depends on (1)+(3); breaks transitively.
   Re-derivable once (1) and (3) are fixed.

## CONSUMERS needing a mechanical touch-up (append `, _htie` / extra binder to the destructure)
Exactly **3 sites** crack the predicate open with `rcases`; all others forward `h_limit`:
- `CharacteristicFunctional.lean:365` (`rcases h_limit with ⟨_a,_ν,…⟩`)
- `OS2_WardIdentity.lean:406`
- `OS2_WardIdentity.lean:770`
Each gets one extra trailing component in the pattern. No proof logic changes (the 8 old clauses are
untouched; the new conjunct is ignored with `_`).

## CONSUMERS unaffected (forward `h_limit` to a sub-lemma — stronger hyp passes straight through)
`pphi2_main` (Main.lean:94, via `continuumLimit_satisfies_fullOS`), and the ~9 AxiomInheritance
sites (126/142/164/239/254/330/357/375 + the forwards at 148/169/241/256/286/378) that pass
`h_limit` into `continuum_exponential_moment_bound` / `…_moments` / `…_clustering` /
`exponential_moment_schwartz_bound`. **No edits.** (The 3 destructure sites above are the only leaves.)

## New obligations / axioms introduced
- **One honest existence statement** replacing the δ₀ proof of `pphi2_limit_exists`: *there exists a
  coupled `(N_k, a_k)` with `a_k→0, N_k→∞, N_k a_k→∞` such that the embedded interacting measures
  `continuumMeasure 2 (N_k) P (a_k) mass` are tight and converge (moments/CF/bdd-cont, with RP & Z₂)
  to a limit μ.* **Check first whether this is PROVABLE** from existing infra before axiomatizing:
  `ContinuumLimit/Tightness.lean`, `ContinuumLimit/Convergence.lean`,
  `ContinuumLimit/SobolevProkhorovPlan.lean`, and the `TorusContinuumLimit/*` family
  (TorusTightness, TorusConvergence, TorusInteractingLimit, TorusInteractingOS) exist and may already
  supply tightness + Prokhorov extraction. If complete → **0 new axioms** (honest proof). If gaps →
  **1 clearly-labeled existence axiom** (honest debt, replacing a vacuous proof). **This is the one
  thing to verify before implementing.**

## Net effect
- Headline `pphi2_existence` stops being witnessed by δ₀ → becomes meaningful.
- `pphi2_nontriviality` can be restated `IsPphi2Limit μ P mass → ∀f≠0, S₂>0` — now TRUE (δ₀ gone) and
  about the real limit; conjoined interacting headline follows (closes coherence Gap A w/o uniqueness).
- 2 vacuous-predicate artifacts exposed for honest repair (reparam-invariance, δ₀ existence).
- Blast: 1 def edit + 1 twin def edit (Bridge), 3 mechanical destructure touch-ups, 2–4 producer
  repairs, and either 0 or 1 new axiom depending on the tightness-infra check.

## Recommended order
1. Verify the tightness/Prokhorov infra → decide 0 vs 1 axiom for honest existence (do this FIRST).
2. Append the conjunct to `IsPphi2Limit` + the twin `IsPphi2ContinuumLimit`.
3. Fix the 3 destructures (trailing `_`).
4. Repair `pphi2_limit_exists` (honest proof or labeled axiom) and the two reparam theorems.
5. Restate `pphi2_nontriviality` about the limit; add the conjoined interacting headline.
