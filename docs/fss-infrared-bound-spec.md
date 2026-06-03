# FSS infrared bound — spec & vetting record (for the `Ls → ∞` step, NOT B2)

**Status:** specification only. **Not yet a Lean axiom** — pphi2 has no field
Fourier-component layer (`φ̂(k)` as a random variable on `Configuration`), so the
statement below cannot yet be written in terms of pphi2's objects. This note saves
the vetted statement, citation, and proof strategy so it is drop-in once a
momentum-space layer exists.

**Where it belongs.** This is the tool for the **infinite-volume spatial limit
`Ls → ∞`**, where the spatial infrared (small spatial momentum `k_s → 0`) must be
controlled. It is **NOT** needed for Layer B2 (`Lt → ∞` at *fixed* `Ls`): at fixed
`Ls` the spatial momenta are discrete and gapped by the box (`|k_s| ≥ 2π/Ls > 0`),
so there is no spatial infrared problem; B2's only dangerous direction is time
(`Lt`), handled by the already-proved transfer-matrix mass gap. See
`layer-B2-discharge-plan.md` → "Step B design" for why B2 = B1 ⊕ gap ⊕ Feynman–Kac
bridge, with no FSS. This file is parked for the later `Ls → ∞` work.

---

## The statement (math)

For the reflection-positive lattice φ⁴₂ measure on the asym torus (single-site even
measure `exp(−λφ⁴ + bφ²)dφ`, nearest-neighbour kinetic term), the momentum-space
two-point function is dominated by the **free kinetic (massless) form**:

  `⟨φ̂(k) φ̂(−k)⟩_int  ≤  1 / (2 E(k))`   for every spatial momentum `k ≠ 0`,

where `E(k)` is the lattice kinetic dispersion (the spectral function of the
nearest-neighbour Laplacian, i.e. the `mass = 0` part of `massEigenvaluesAsym`).

## Vetting verdict (Gemini deep-think, 2026-06-03 — ranked #1 of candidates A/B/C)

- **Applies to φ⁴₂.** The single-site even measure is in the Simon–Griffiths
  (ferromagnetic-Ising-limit) class; lattice reflection positivity yields the
  Gaussian-domination inequality from which the infrared bound follows.
- **Dominates by the FREE covariance** (massless kinetic propagator), directly.
- **`Lt`- AND `a`-uniform by construction**: the Gaussian-domination proof factors
  the hopping (kinetic) expansion off the single-site measure, so the Wick
  log-divergent counterterm cancels out of the inequality. **Immune to the negative
  bare mass** — no `b ≤ 0` / convexity needed (this is what kills Brascamp–Lieb).
- **Limitation:** controls `k ≠ 0` only. The `k = 0` zero mode / susceptibility is
  NOT bounded by FSS — it must come from the mass gap. **Caveat for re-use:** the
  RHS `1/(2E(k))` is the *massless* propagator and diverges as `k → 0`, so FSS does
  not bound the *massive* free variance at small momentum; combine with the gap for
  the small-momentum / zero modes.

## References

- J. Fröhlich, B. Simon, T. Spencer, *Infrared bounds, phase transitions and
  continuous symmetry breaking*, Comm. Math. Phys. **50** (1976) 79–95.
- B. Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory*, Princeton UP 1974
  (Gaussian domination / correlation inequalities, single-site measure class).
- Glimm–Jaffe, *Quantum Physics*, 2nd ed. (reflection positivity & lattice
  approximation context).

## Proof strategy (for the eventual Lean proof, not an axiom forever)

1. **Gaussian domination**: `Z(h) := ∫ exp(½⟨φ, Δ φ⟩ + ⟨h, φ⟩…) ≤ Z(0)·exp(½⟨h,(−Δ)⁻¹h⟩)`
   for the RP measure, via reflection positivity + a chessboard/Cauchy–Schwarz
   estimate over the kinetic bonds (the single-site measure factors out).
2. Differentiate `Z(h)` twice at `h = 0` ⟹ `⟨φ̂(k)φ̂(−k)⟩ ≤ 1/(2E(k))` for `k ≠ 0`.
3. Uniformity in volume and `a` is automatic from step 1 (kinetic-only RHS).

## Drop-in Lean signature (once a Fourier layer exists)

Requires, not yet present in pphi2:
- a spatial (or full-lattice) **discrete Fourier transform** of the field,
  `fieldFourier : AsymLatticeSites Nt Ns → Configuration (AsymLatticeField Nt Ns) → ℂ`
  (or a real cos/sin basis), with Parseval connecting `∫(ω f)² dμ` to a momentum sum;
- the **free kinetic dispersion** `E(k)` exposed (available as the `mass = 0` case of
  `massEigenvaluesAsym Nt Ns a mass k`, modulo the `a`-normalisation).

Intended statement (schematic — finalize against the Fourier layer's API):

```lean
/-- Fröhlich–Simon–Spencer infrared bound / Gaussian domination for lattice φ⁴₂.
    The interacting momentum-space two-point function is dominated by the free
    (massless) kinetic propagator, uniformly in volume and lattice spacing.

    Reference: Fröhlich–Simon–Spencer, Comm. Math. Phys. 50 (1976) 79–95.
    Strategy: Gaussian domination via reflection positivity (chessboard over
    kinetic bonds; single-site measure factors out) ⟹ second-derivative bound.
    (NOT VERIFIED — vetted by Gemini deep-think 2026-06-03; for the Ls→∞ step.) -/
axiom fss_infrared_bound
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (k : AsymLatticeSites Nt Ns) (hk : k ≠ kZeroMode) :
    interactingFourierTwoPoint Nt Ns P a mass ha hmass k
      ≤ (2 * freeKineticDispersion Nt Ns a k)⁻¹
```

Until the Fourier layer lands, this stays a spec, not an `axiom`. Do **not** add a
free-floating momentum-space `axiom` to the build — it would have no consumer and
would not discharge B2.
