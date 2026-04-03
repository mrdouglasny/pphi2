/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# OS4: Exponential Clustering from the Spectral Gap

Derives the exponential clustering property (OS4) from the spectral gap
of the transfer matrix Hamiltonian.

## Main results

- `two_point_clustering_lattice` — exponential decay of the connected 2-point function
- `general_clustering_lattice` — exponential decay for general observables
- `clustering_uniform` — decay rate is uniform in the lattice spacing

## Mathematical background

The spectral gap `m_phys = E₁ - E₀ > 0` implies exponential clustering:

### Two-point function

Using the transfer matrix eigendecomposition:
```
⟨φ(t,x) φ(0,y)⟩ = (1/Z) Tr(T^{Nt-t} φ̂(x) T^t φ̂(y))
```
where φ̂(x) is the multiplication operator by ψ(x) on L²(ℝ^Ns).

The exponents `t` and `N_s - t` record a conventional transfer-matrix ordering along
the periodic chain; **upper bounds** on the connected correlator on the torus combine
forward and backward windings into the cyclic (geodesic) time distance `d_cyc` below.

Inserting a complete set of energy eigenstates |n⟩ with energies Eₙ between the
insertions (transfer-matrix / lattice Markov picture; cf. GRS Ann. Math. **101**
(1975), Part II, Ch. IV) yields schematically
```
⟨φ(t,x) φ(0,y)⟩ - ⟨φ(x)⟩⟨φ(y)⟩
  ≈ Σ_{n≥1} ⟨Ω|φ̂(x)|n⟩⟨n|φ̂(y)|Ω⟩ · e^{-(Eₙ-E₀) d_cyc a}
```
where `d_cyc` is the **geodesic** (cyclic) Euclidean-time distance on the periodic
time circle, in lattice units, i.e. `d_cyc = min(k, N_s - k)` for the relevant time
shift `k` between slices.

Since `Eₙ - E₀ ≥ m_phys = E₁ - E₀ > 0` for all `n ≥ 1`:
```
|⟨φ(t,x) φ(0,y)⟩ - ⟨φ(x)⟩⟨φ(y)⟩| ≤ C(x,y) · e^{-m_phys · d_cyc · a}
```

**Caution:** one should not read the bare label `t : Fin N_s` as a *directed*
winding length in the exponent; on a torus the natural single-exponential **upper**
bound is controlled by shortest arc length (`latticeEuclideanTimeSeparation` below).

### General observables

For bounded measurable `F`, `G` and the Euclidean time shift `τ_R` implemented
as `latticeConfigEuclideanTimeShift N_s R` on configurations:
```
|⟨F · (G ∘ τ_R)⟩ - ⟨F⟩⟨G⟩| ≤ C(F,G) · e^{-m_phys · d_cyc(R) · a}
```
with the same cyclic separation `d_cyc(R) = latticeEuclideanTimeSeparation N_s R`.
This matches the formal axioms; continuum OS4 (`|τ| → ∞` on ℝ²) is recovered only
after an infrared / continuum-limit step, not from the bare periodic `N_s` model alone.

## References

- Glimm-Jaffe, *Quantum Physics*, §6.2, §19.3
- Simon, *The P(φ)₂ Euclidean QFT*, §III.3, §IV.1
- Simon-Hoegh-Krohn (1972), "Hypercontractive semigroups and two dimensional
  self-coupled Bose fields"
- Guerra–Rosen–Simon, *Ann. Math.* 101 (1975), Part II (lattice Markov fields;
  see `refs/GRS1975-p2.md`)

## Reference alignment (finite torus vs. continuum texts)

- **GRS (1975), Simon, Glimm–Jaffe:** clustering and transfer-matrix estimates are
  usually stated for infinite `ℤ²` or continuum `ℝ²`, with decay in a large Euclidean
  separation `|τ|` (or the spatial analogue).
- **This repository’s lattice layer:** we work on the periodic `(ℤ/N_sℤ)²` torus.
  The axioms `two_point_clustering_from_spectral_gap` and
  `general_clustering_from_spectral_gap` therefore measure decay in the **cyclic**
  Euclidean-time separation `latticeEuclideanTimeSeparation`, i.e. geodesic distance
  on the time circle, **not** an unbounded `R : ℕ` without periodic reduction.
- **Comparison:** matching the textbook `e^{-m|τ|}` picture requires an infrared step
  (`N_s → ∞` at fixed physical separation, and/or the continuum limit package) so
  wrap-around is negligible; see `refs/GRS1975-p2.md` for the infinite-lattice setup
  in GRS Part II §IV (our `N_s` torus is a finite-volume periodic truncation).
-/

import Pphi2.TransferMatrix.SpectralGap
import Pphi2.InteractingMeasure.LatticeEuclideanTime
import Pphi2.InteractingMeasure.LatticeMeasure
import Pphi2.InteractingMeasure.Normalization
import Mathlib.Probability.Moments.Variance

noncomputable section

open GaussianField Real MeasureTheory

namespace Pphi2

variable (Ns : ℕ) [NeZero Ns]

/-! ## Euclidean-time shift (see `InteractingMeasure/LatticeEuclideanTime.lean`)

For `μ = interactingLatticeMeasure`, **`∫ G(τ_R ω) ∂μ = ∫ G ∂μ`** for integrable `G` is proved
as `interactingLatticeMeasure_expectation_configEuclideanTimeShift` in `OS2_WardIdentity.lean`
(specializing translation invariance). The clustering axiom below is therefore the usual
`Cov(F, G∘τ_R)` form relative to **translation-invariant** `μ`. -/

/-! ## Spectral gap clustering axioms

The clustering results from the spectral decomposition of the transfer matrix.
On the periodic `Ns × Ns` lattice, the relevant finite-volume separation is the
**cyclic Euclidean-time distance**
  `d_cyc(k) = latticeEuclideanTimeSeparation Ns k`
rather than an unbounded `R : ℕ`.

Insert a complete set of eigenstates `|n⟩` between φ̂(t,x) and φ̂(0,y):
  `⟨φ(t,x)φ(0,y)⟩ = Σₙ |⟨Ω|φ̂(x)|n⟩|² exp(-(Eₙ - E₀)d_cyc(t)a)`

Since `Eₙ - E₀ ≥ m_phys` for all `n ≥ 1`:
  `|⟨φ(t,x)φ(0,y)⟩ - ⟨φ(x)⟩⟨φ(y)⟩| ≤ C exp(-m_phys d_cyc(t) a)`

References: Reed-Simon IV Thm XIII.44; Glimm-Jaffe §6.2;
Simon P(φ)₂ Theory §III.3. -/

/-- Two-point clustering from spectral gap: the connected two-point function
decays exponentially at the rate of the mass gap.

**Finite-volume torus form.** The exponent uses the cyclic Euclidean-time
separation `latticeEuclideanTimeSeparation Ns t.val`, i.e.
`min(t.val, Ns - t.val)`, which is the genuine geodesic distance on the
periodic time circle. -/
axiom two_point_clustering_from_spectral_gap
    (Ns : ℕ) [NeZero Ns] (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (t x y : Fin Ns) :
    ∃ C : ℝ, 0 < C ∧
    let μ := interactingLatticeMeasure 2 Ns P a mass ha hmass
    let δtx : FinLatticeField 2 Ns := finLatticeDelta 2 Ns (![t, x])
    let δ0y : FinLatticeField 2 Ns := finLatticeDelta 2 Ns (![0, y])
    |(∫ ω : Configuration (FinLatticeField 2 Ns), ω δtx * ω δ0y ∂μ) -
     (∫ ω : Configuration (FinLatticeField 2 Ns), ω δtx ∂μ) *
     (∫ ω : Configuration (FinLatticeField 2 Ns), ω δ0y ∂μ)| ≤
      C * Real.exp
        (-massGap Ns P a mass ha hmass *
          (latticeEuclideanTimeSeparation Ns t.val : ℝ) * a)

/-- General clustering from spectral gap: connected correlators of bounded
observables decay exponentially with the mass gap rate.

The observable `G` is evaluated on the **time-translated configuration**
`latticeConfigEuclideanTimeShift Ns R ω`, so the left-hand side depends on `R`
as in the transfer-matrix / multiplicative ergodic picture
`⟨F · (τ_R G)⟩ − ⟨F⟩⟨G⟩`. The decay rate is measured against the cyclic
torus separation `latticeEuclideanTimeSeparation Ns R`. -/
axiom general_clustering_from_spectral_gap
    (Ns : ℕ) [NeZero Ns] (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∀ (F G : Configuration (FinLatticeField 2 Ns) → ℝ)
      (_hF : ∃ C, ∀ ω, |F ω| ≤ C) (_hG : ∃ C, ∀ ω, |G ω| ≤ C),
      ∃ (C_FG : ℝ), 0 ≤ C_FG ∧
      ∀ (R : ℕ),
        |(∫ ω, F ω * G (latticeConfigEuclideanTimeShift Ns R ω)
              ∂(interactingLatticeMeasure 2 Ns P a mass ha hmass)) -
         (∫ ω, F ω ∂(interactingLatticeMeasure 2 Ns P a mass ha hmass)) *
         (∫ ω, G ω ∂(interactingLatticeMeasure 2 Ns P a mass ha hmass))|
        ≤ C_FG * Real.exp
          (-massGap Ns P a mass ha hmass *
            (latticeEuclideanTimeSeparation Ns R : ℝ) * a)

/-! ## Two-point clustering on the lattice -/

/-- **Exponential clustering of the two-point function on the lattice.**

The connected two-point function decays exponentially with rate
equal to the mass gap:

  `|⟨φ(t,x) · φ(0,y)⟩ - ⟨φ(x)⟩ · ⟨φ(y)⟩| ≤ C · exp(-m_phys · d_cyc(t) · a)`

where `d_cyc(t) = latticeEuclideanTimeSeparation Ns t.val` is the cyclic
time separation on the periodic lattice and `m_phys = massGap … > 0`.

The constant C depends on x, y and the ground state overlaps
`⟨Ω|φ̂(x)|n⟩`, but is finite because φ̂(x) maps the domain of H
into L² (as a bounded perturbation of the free field). -/
theorem two_point_clustering_lattice
    (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    -- Sites x, y in the spatial direction; t is the time index (both in Fin Ns
    -- since we use an Ns × Ns square lattice)
    (t x y : Fin Ns) :
    ∃ C : ℝ, 0 < C ∧
    -- |⟨φ(t,x) · φ(0,y)⟩_c| ≤ C · exp(-m_phys · d_cyc(t) · a)
    -- Expressed via the interacting lattice measure and delta functions:
    let μ := interactingLatticeMeasure 2 Ns P a mass ha hmass
    -- δ_{(t,x)} and δ_{(0,y)} are the delta functions at the two sites
    let δtx : FinLatticeField 2 Ns := finLatticeDelta 2 Ns (![t, x])
    let δ0y : FinLatticeField 2 Ns := finLatticeDelta 2 Ns (![0, y])
    |(∫ ω : Configuration (FinLatticeField 2 Ns), ω δtx * ω δ0y ∂μ) -
     (∫ ω : Configuration (FinLatticeField 2 Ns), ω δtx ∂μ) *
     (∫ ω : Configuration (FinLatticeField 2 Ns), ω δ0y ∂μ)| ≤
      C * Real.exp
        (-massGap Ns P a mass ha hmass *
          (latticeEuclideanTimeSeparation Ns t.val : ℝ) * a) := by
  exact two_point_clustering_from_spectral_gap Ns P a mass ha hmass t x y

/-! ## General clustering on the lattice -/

/-- **Exponential clustering for general observables on the lattice.**

For observables F, G on configurations and time-translation by R:

  `|E_μ[F · G_R] - E_μ[F] · E_μ[G]| ≤ C(F,G) · exp(-m_phys · d_cyc(R) · a)`

where `G` is composed with `latticeConfigEuclideanTimeShift Ns R` (dual to
translating the lattice field in Euclidean time) and
`d_cyc(R) = latticeEuclideanTimeSeparation Ns R`.

This is the finite-volume torus analogue of clustering. The genuine infinite
separation OS4 statement only emerges after the IR / decompactification limit. -/
theorem general_clustering_lattice
    (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    -- For any bounded observables F, G and time separation R, the connected
    -- correlator decays exponentially at the rate of the mass gap:
    -- ∃ m > 0, ∀ bounded F G, ∀ R : ℕ,
    --   |∫ F(ω) · G(τ_R ω) dμ - (∫ F dμ)(∫ G dμ)| ≤ C(F,G) · exp(-m · R · a)
    ∃ (m : ℝ), 0 < m ∧ m ≤ massGap Ns P a mass ha hmass ∧
    ∀ (F G : Configuration (FinLatticeField 2 Ns) → ℝ)
      (_hF : ∃ C, ∀ ω, |F ω| ≤ C) (_hG : ∃ C, ∀ ω, |G ω| ≤ C),
      ∃ (C_FG : ℝ), 0 ≤ C_FG ∧
      ∀ (R : ℕ),
        |(∫ ω, F ω * G (latticeConfigEuclideanTimeShift Ns R ω)
              ∂(interactingLatticeMeasure 2 Ns P a mass ha hmass)) -
         (∫ ω, F ω ∂(interactingLatticeMeasure 2 Ns P a mass ha hmass)) *
         (∫ ω, G ω ∂(interactingLatticeMeasure 2 Ns P a mass ha hmass))|
        ≤ C_FG * Real.exp
          (-m * (latticeEuclideanTimeSeparation Ns R : ℝ) * a) := by
  refine ⟨massGap Ns P a mass ha hmass, massGap_pos Ns P a mass ha hmass, le_refl _, ?_⟩
  intro F G hF hG
  exact general_clustering_from_spectral_gap Ns P a mass ha hmass F G hF hG

/-! ## Uniform clustering

The exponential decay rate is bounded below uniformly in the lattice
spacing a. This ensures OS4 transfers to the continuum limit. -/

/-- **Uniform exponential clustering.**

The mass gap (exponential decay rate) is bounded below uniformly in a:

  `∃ m₀ > 0, ∀ a ∈ (0, a₀], mass gap ≥ m₀`

Combined with `general_clustering_lattice`, for each fixed `N_s` this yields a bound
of the form `|Cov(F, G∘τ_R)| ≤ C(F,G) · exp(-m₀ · d_cyc(R) · a)` uniformly for
`a` in the spectral-gap window, where `d_cyc(R) = latticeEuclideanTimeSeparation Ns R`.
In the continuum limit `a → 0`, the inherited OS4 statement is still phrased via
the continuum clustering functional (see the continuum OS layer), not by the bare
integer `R` alone.

This is the key input from `spectral_gap_uniform`. -/
theorem clustering_uniform (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ m₀ : ℝ, 0 < m₀ ∧ ∃ a₀ : ℝ, 0 < a₀ ∧
    ∀ (a : ℝ) (ha : 0 < a), a ≤ a₀ →
    m₀ ≤ massGap Ns P a mass ha hmass :=
  spectral_gap_uniform Ns P mass hmass

/-! ## Connected correlation functions

For the formal statement of OS4, we need connected (truncated)
correlation functions. -/

/-- The connected two-point function on the lattice:

  `G_c(f, g) = ∫ ω(f) · ω(g) dμ_a - (∫ ω(f) dμ_a) · (∫ ω(g) dμ_a)`

This measures the correlation between field evaluations at f and g
beyond what is explained by the individual expectations. -/
def connectedTwoPoint (d N : ℕ) [NeZero N]
    (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (f g : FinLatticeField d N) : ℝ :=
  let μ := interactingLatticeMeasure d N P a mass ha hmass
  (∫ ω : Configuration (FinLatticeField d N), ω f * ω g ∂μ) -
  (∫ ω : Configuration (FinLatticeField d N), ω f ∂μ) *
  (∫ ω : Configuration (FinLatticeField d N), ω g ∂μ)

/-- The connected two-point function is symmetric. -/
theorem connectedTwoPoint_symm (d N : ℕ) [NeZero N]
    (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (f g : FinLatticeField d N) :
    connectedTwoPoint d N P a mass ha hmass f g =
    connectedTwoPoint d N P a mass ha hmass g f := by
  -- Follows from commutativity of real multiplication under the integral
  simp only [connectedTwoPoint]
  congr 1
  · congr 1 with ω
    ring
  · ring

/-- The connected two-point function is positive semidefinite.

This is variance nonnegativity: `Var[ω(δ_x)] = E[ω(δ_x)²] - E[ω(δ_x)]² ≥ 0`.

Previously stated as an axiom invoking FKG, but it follows directly from
`ProbabilityTheory.variance_nonneg` combined with `variance_def'`. -/
theorem connectedTwoPoint_nonneg_delta (d N : ℕ) [NeZero N]
    (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (x : FinLatticeSites d N) :
    0 ≤ connectedTwoPoint d N P a mass ha hmass
      (finLatticeDelta d N x) (finLatticeDelta d N x) := by
  unfold connectedTwoPoint
  set μ := interactingLatticeMeasure d N P a mass ha hmass
  set δx := finLatticeDelta d N x
  -- The connected two-point function at (δx, δx) is Var[X] where X ω = ω δx.
  -- Var[X] = E[X²] - E[X]² = ∫ (ω δx)² dμ - (∫ ω δx dμ)² ≥ 0
  set X : Configuration (FinLatticeField d N) → ℝ := fun ω => ω δx
  haveI : IsProbabilityMeasure μ :=
    interactingLatticeMeasure_isProbability d N P a mass ha hmass
  -- Integrability from Normalization.lean
  have h_int : Integrable X μ := by
    have := field_all_moments_finite d N P a mass ha hmass x 1
    exact this.congr (ae_of_all μ (fun ω => by simp [X, δx, pow_one]))
  have h_int2 : Integrable (fun ω => X ω * X ω) μ := by
    have := field_second_moment_finite d N P a mass ha hmass x
    exact this.congr (ae_of_all μ (fun ω => by simp [X, δx, sq]))
  -- Key: 0 ≤ ∫ (X - E[X])² dμ = ∫ X² dμ - E[X]²
  set c := ∫ ω, X ω ∂μ
  -- We show ∫ X² dμ - c² = ∫ (X - c)² dμ ≥ 0
  have h_nonneg : 0 ≤ ∫ ω, (X ω - c) ^ 2 ∂μ :=
    integral_nonneg (fun ω => sq_nonneg (X ω - c))
  -- Key: 0 ≤ ∫ (X - E[X])² dμ = ∫ X² dμ - E[X]²
  set c := ∫ ω, X ω ∂μ
  -- Expand ∫ (X - c)² and use integral_nonneg
  have h_nonneg : 0 ≤ ∫ ω, (X ω - c) ^ 2 ∂μ :=
    integral_nonneg (fun ω => sq_nonneg (X ω - c))
  -- Compute ∫ (X - c)² by splitting into three integrals
  have h_int_cc : Integrable (fun _ : Configuration (FinLatticeField d N) => c * c) μ :=
    integrable_const _
  have h_int_cX : Integrable (fun ω => (-(2 * c)) * X ω) μ :=
    h_int.const_mul _
  -- Direct approach: show the difference using integral arithmetic
  have h_key : ∫ ω, (X ω - c) ^ 2 ∂μ =
      (∫ ω, X ω * X ω ∂μ) - c * c := by
    -- Express (X - c)² as sum of integrable parts
    have h_eq : ∀ ω, (X ω - c) ^ 2 = X ω * X ω - 2 * c * X ω + c * c := fun ω => by ring
    calc ∫ ω, (X ω - c) ^ 2 ∂μ
        = ∫ ω, (X ω * X ω - 2 * c * X ω + c * c) ∂μ := by
          congr 1 with ω; exact h_eq ω
      _ = ∫ ω, (X ω * X ω - 2 * c * X ω) ∂μ + ∫ ω, c * c ∂μ := by
          apply integral_add (h_int2.sub (h_int.const_mul _)) (integrable_const _)
      _ = (∫ ω, X ω * X ω ∂μ - ∫ ω, 2 * c * X ω ∂μ) + ∫ ω, c * c ∂μ := by
          congr 1; exact integral_sub h_int2 (h_int.const_mul _)
      _ = (∫ ω, X ω * X ω ∂μ - 2 * c * ∫ ω, X ω ∂μ) + ∫ ω, c * c ∂μ := by
          congr 1; congr 1; exact integral_const_mul _ _
      _ = (∫ ω, X ω * X ω ∂μ) - c * c := by
          simp [integral_const]; ring
  linarith

end Pphi2

end
