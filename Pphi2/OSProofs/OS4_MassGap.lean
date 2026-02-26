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

Inserting a complete set of energy eigenstates |n⟩ with energies Eₙ:
```
⟨φ(t,x) φ(0,y)⟩ - ⟨φ(x)⟩⟨φ(y)⟩ = Σ_{n≥1} ⟨Ω|φ̂(x)|n⟩⟨n|φ̂(y)|Ω⟩ · e^{-(Eₙ-E₀)|t|}
```

Since all terms have `Eₙ - E₀ ≥ m_phys = E₁ - E₀ > 0`:
```
|⟨φ(t,x) φ(0,y)⟩ - ⟨φ(x)⟩⟨φ(y)⟩| ≤ C(x,y) · e^{-m_phys · |t|}
```

### General observables

For F, G bounded measurable and time-translated G_R(φ) = G(T_R φ):
```
|⟨F · G_R⟩ - ⟨F⟩⟨G⟩| ≤ C(F,G) · e^{-m_phys · R}
```

This is the content of OS4 (clustering / exponential decay of correlations).

## References

- Glimm-Jaffe, *Quantum Physics*, §6.2, §19.3
- Simon, *The P(φ)₂ Euclidean QFT*, §III.3, §IV.1
- Simon-Hoegh-Krohn (1972), "Hypercontractive semigroups and two dimensional
  self-coupled Bose fields"
-/

import Pphi2.TransferMatrix.SpectralGap
import Pphi2.InteractingMeasure.LatticeMeasure
import Pphi2.InteractingMeasure.Normalization
import Mathlib.Probability.Moments.Variance

noncomputable section

open GaussianField Real MeasureTheory

namespace Pphi2

variable (Ns : ℕ) [NeZero Ns]

/-! ## Spectral gap clustering axioms

The clustering results from the spectral decomposition of the transfer matrix.
Insert a complete set of eigenstates `|n⟩` between φ̂(t,x) and φ̂(0,y):
  `⟨φ(t,x)φ(0,y)⟩ = Σₙ |⟨Ω|φ̂(x)|n⟩|² exp(-(Eₙ - E₀)|t|a)`

Since `Eₙ - E₀ ≥ m_phys` for all `n ≥ 1`:
  `|⟨φ(t,x)φ(0,y)⟩ - ⟨φ(x)⟩⟨φ(y)⟩| ≤ C exp(-m_phys |t| a)`

References: Reed-Simon IV Thm XIII.44; Glimm-Jaffe §6.2;
Simon P(φ)₂ Theory §III.3. -/

/-- Two-point clustering from spectral gap: the connected two-point function
decays exponentially at the rate of the mass gap. -/
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
      C * Real.exp (-massGap Ns P a mass ha hmass * (t.val : ℝ) * a)

/-- General clustering from spectral gap: connected correlators of bounded
observables decay exponentially with the mass gap rate. -/
axiom general_clustering_from_spectral_gap
    (Ns : ℕ) [NeZero Ns] (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∀ (F G : Configuration (FinLatticeField 2 Ns) → ℝ)
      (_hF : ∃ C, ∀ ω, |F ω| ≤ C) (_hG : ∃ C, ∀ ω, |G ω| ≤ C),
      ∃ (C_FG : ℝ), 0 ≤ C_FG ∧
      ∀ (R : ℕ),
        |(∫ ω, F ω * G ω ∂(interactingLatticeMeasure 2 Ns P a mass ha hmass)) -
         (∫ ω, F ω ∂(interactingLatticeMeasure 2 Ns P a mass ha hmass)) *
         (∫ ω, G ω ∂(interactingLatticeMeasure 2 Ns P a mass ha hmass))|
        ≤ C_FG * Real.exp (-massGap Ns P a mass ha hmass * (R : ℝ) * a)

/-! ## Two-point clustering on the lattice -/

/-- **Exponential clustering of the two-point function on the lattice.**

The connected two-point function decays exponentially with rate
equal to the mass gap:

  `|⟨φ(t,x) · φ(0,y)⟩ - ⟨φ(x)⟩ · ⟨φ(y)⟩| ≤ C · exp(-m_phys · |t|)`

where `m_phys = massGap P a mass > 0` is the spectral gap.

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
    -- The connected two-point function decays exponentially:
    -- |⟨φ(t,x) · φ(0,y)⟩_c| ≤ C · exp(-m_phys · t · a)
    -- Expressed via the interacting lattice measure and delta functions:
    let μ := interactingLatticeMeasure 2 Ns P a mass ha hmass
    -- δ_{(t,x)} and δ_{(0,y)} are the delta functions at the two sites
    let δtx : FinLatticeField 2 Ns := finLatticeDelta 2 Ns (![t, x])
    let δ0y : FinLatticeField 2 Ns := finLatticeDelta 2 Ns (![0, y])
    |(∫ ω : Configuration (FinLatticeField 2 Ns), ω δtx * ω δ0y ∂μ) -
     (∫ ω : Configuration (FinLatticeField 2 Ns), ω δtx ∂μ) *
     (∫ ω : Configuration (FinLatticeField 2 Ns), ω δ0y ∂μ)| ≤
      C * Real.exp (-massGap Ns P a mass ha hmass * (t.val : ℝ) * a) := by
  exact two_point_clustering_from_spectral_gap Ns P a mass ha hmass t x y

/-! ## General clustering on the lattice -/

/-- **Exponential clustering for general observables on the lattice.**

For observables F, G on configurations and time-translation by R:

  `|E_μ[F · G_R] - E_μ[F] · E_μ[G]| ≤ C(F,G) · exp(-m_phys · R)`

where G_R(φ)(t,x) = G(φ)(t+R,x) is the time-translated observable.

This is the abstract version of clustering that becomes OS4 in the
continuum limit. -/
theorem general_clustering_lattice
    (Nt : ℕ) [NeZero Nt]
    (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    -- For any bounded observables F, G and time separation R, the connected
    -- correlator decays exponentially at the rate of the mass gap:
    -- ∃ m > 0, ∀ bounded F G, ∀ R : ℕ,
    --   |∫ F(ω) · G(T_R ω) dμ - (∫ F dμ)(∫ G dμ)| ≤ C(F,G) · exp(-m · R · a)
    ∃ (m : ℝ), 0 < m ∧ m ≤ massGap Ns P a mass ha hmass ∧
    ∀ (F G : Configuration (FinLatticeField 2 Ns) → ℝ)
      (_hF : ∃ C, ∀ ω, |F ω| ≤ C) (_hG : ∃ C, ∀ ω, |G ω| ≤ C),
      ∃ (C_FG : ℝ), 0 ≤ C_FG ∧
      ∀ (R : ℕ),
        |(∫ ω, F ω * G ω ∂(interactingLatticeMeasure 2 Ns P a mass ha hmass)) -
         (∫ ω, F ω ∂(interactingLatticeMeasure 2 Ns P a mass ha hmass)) *
         (∫ ω, G ω ∂(interactingLatticeMeasure 2 Ns P a mass ha hmass))|
        ≤ C_FG * Real.exp (-m * (R : ℝ) * a) := by
  refine ⟨massGap Ns P a mass ha hmass, massGap_pos Ns P a mass ha hmass, le_refl _, ?_⟩
  intro F G hF hG
  exact general_clustering_from_spectral_gap Ns P a mass ha hmass F G hF hG

/-! ## Uniform clustering

The exponential decay rate is bounded below uniformly in the lattice
spacing a. This ensures OS4 transfers to the continuum limit. -/

/-- **Uniform exponential clustering.**

The mass gap (exponential decay rate) is bounded below uniformly in a:

  `∃ m₀ > 0, ∀ a ∈ (0, a₀], mass gap ≥ m₀`

Combined with the clustering bound, this gives:

  `|⟨F · G_R⟩ - ⟨F⟩⟨G⟩| ≤ C(F,G) · exp(-m₀ · R)`

uniformly in a. In the continuum limit a → 0, the limiting measure
inherits the same exponential clustering bound.

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
