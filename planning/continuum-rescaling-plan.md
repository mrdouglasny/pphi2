# Continuum rescaling-equivalence route to φ⁴₂ non-triviality

A replacement for the lattice "mass-grade ∫V²" endgame (which is entangled with the 2D UV/log
divergence). Idea: the rescaling that **fails on the lattice** (`−Δ_a` is not scale-covariant) is
**clean in the continuum** (in 2D `φ` is dimensionless and `−Δ` is exactly scale-covariant). So prove
the equivalence in the continuum and use the lattice only to *construct* the continuum measures.

## Target
Axiom-free: the continuum φ⁴₂ theory on `T²` is non-Gaussian (`u₄ ≠ 0`) at the physical point
(`λ = 1`, large mass), via
- **(A)** a continuum-limit theorem for the family `μ_{λ,m,L₁,L₂}`,
- **(B)** a continuum **rescaling-equivalence** lemma relating different parameter points,
- **(C)** **weak-coupling `u₄ < 0`** (the engine already built),
with **(B)+(C) ⟹ physical `u₄ < 0`**.

## The equivalence (2D continuum)
Action `∫_{T²_L}[½(∇φ)² + ½ m²φ² + λ:φ⁴:]`. Mass dims `[φ]=0, [m²]=2, [λ]=2`. Two generators:
- **Dilation** `x ↦ x/s`: kinetic term invariant (2D), `m² ↦ s²m²`, `λ ↦ s²λ`, `L_i ↦ L_i/s`.
- **Field rescale** `φ ↦ cφ`: covariance `↦ c²·cov`, `u₄ ↦ c⁴·u₄`
  (`connectedFourPoint_map_const_smul`, proven), trades against `λ`.

Dimensionless invariants: `mL`, `λ/m²`, aspect ratio `L₁/L₂`. The physical point `(λ=1, m, L)` (large
`m`) has `λ/m² = 1/m²` small; dilating by `s = 1/m` gives
```
(λ=1, m, L)  ≅  (λ' = 1/m², m' = 1, L' = mL),     u₄(phys) = c⁴ · u₄(equiv).
```
i.e. **physical large-mass ≅ weak-coupling (`λ' = 1/m² → 0`) at unit mass on a torus `L' = mL`.**

## Bricks
1. **Family continuum construction** `μ_{λ,m,L₁,L₂}`: existence (subsequential limit), tightness,
   and 4-point convergence — generalize the existing `λ=1` machinery (`torusInteractingMeasure`,
   `torusInteractingLimit_exists`, `torus_connectedFourPoint_tendsto`) to general `λ` and two side
   lengths. (Nelson/tightness inputs look `λ`-uniform.)
2. **Continuum rescaling-equivalence lemma** for `u₄` (the genuinely new piece):
   `u₄(μ_{λ,m,L}; f) = c⁴ · u₄(μ_{λ',m',L'}; f∘dilation)`.
   - field-rescale half: `connectedFourPoint_map_const_smul` (proven) + the continuum pushforward
     `map (c•) μ_cont = μ_{c²·cov}` (Minlos/Cramér–Wold — the package has `CramerWold`,
     `Measure.ext_of_charFunDual`).
   - dilation half: torus diffeomorphism `x↦x/s` induces a configuration pushforward; equality of
     `u₄`s via the char-functional/second-moment transformation.
3. **Weak-coupling `u₄ < 0` in the continuum**: `lattice_u4_neg_uniform` (lattice `u₄(λ₀) < 0`,
   uniform in `N`) + brick 1's 4-point convergence ⟹ continuum `u₄(λ₀) < 0` for small `λ₀`.
4. **Assembly**: brick 2 maps physical `(λ=1, large m)` to the weak-coupling image; brick 3 gives the
   image `u₄ < 0`; `c⁴ > 0` ⟹ physical `u₄ < 0` ⟹ non-Gaussian.

## Already proven (the engine + supports)
`u₄'(0) = −6λ∑(C_a f)⁴ < 0`, `u₄ ∈ C²`, `|u₄''| ≤ K` uniform in `N`, affine bound ⟹ lattice
`u₄(λ₀) < 0` uniform in `N` (`lattice_u4_neg_uniform`); `λ=1` continuum 4-point convergence
(`torus_connectedFourPoint_tendsto`); field-rescale `u₄`-scaling (`connectedFourPoint_map_const_smul`);
covariance `mass⁻²` decay (`lattice_second_moment_le_mass_inv`, `gffPositionCovariance_abs_le_mass_inv`).

## VETTING VERDICT (Gemini deep-think, 2026-06): SOUND — crux resolved
- **Volume-uniformity holds via exponential clustering.** `u₄''(g) ∝ ⟨φ(f)⁴; V; V⟩_c` is *connected*;
  at the image mass `m'=1` the propagator decays `~e^{−|x−y|}`, so the two integrated vertex
  positions `z₁,z₂` are tied (by connectedness) to the fixed support of `f`. Hence
  `∫∫ dz₁dz₂ |⟨…⟩_c| = O(1)`, and `K` depends only on the support/amplitude of `f`, **independent of
  the torus volume `L'`** (once `L' >` supp `f`). Open subtlety 1 ⟹ resolved.
- **The test function transforms (the real subtlety) — and it works in our favor.** Under `x↦x/s`
  (`s=1/m`), `φ(f) = φ'(f')` with `f'(x') = m⁻²·f(x'/m)` (support area `∝ m²`, amplitude `∝ m⁻²`).
  Then **both** the slope `s'(f') ∝ (area)(amplitude)⁴ = m²·m⁻⁸ = m⁻⁶` **and** the bound
  `K'(f') ∝ m⁻⁶`. So the critical window `g'_crit = |s'|/(2K') ~ O(1)` is **constant in `m`**, while the
  actual coupling `λ' = 1/m² → 0` falls inside it for large `m`. The affine argument transports
  uniformly. Open subtlety 1 (residual) ⟹ resolved.
- **Wick ordering is covariant; the limit commutes with dilation.** `C_m(x,y) = C_{m'=1}(mx,my)`
  exactly (continuum), so `:φ⁴:_m ↦ :φ⁴:_{m'=1}` with **no** anomalous log-renormalization (we act on
  the *continuum* GFF, not the lattice). Open subtleties 2,3 ⟹ resolved.
- **Verdict:** "vastly superior to lattice mass-decay" — the continuum-scaling cleanly *factors* the
  proof into UV (lattice→continuum, already done, `N`-uniform) and IR (scaling, exact), avoiding the
  log-divergence nightmare of mass-grading `∫V²` on the lattice. No fatal gaps.

## OPEN SUBTLETIES — (now resolved by the vetting above; kept for the record)
1. **Scale-covariance of the quantitative bound / the large-torus image.** The image theory sits on
   `L' = mL → ∞` (infinite-volume direction). My lattice bound's constants `s = 6(L⁶m⁸)⁻¹`,
   `K(L,m)` are **not** dimensionless invariants; on the image (`m'=1`, `L'=mL`), a *crude* `|u₄''|`
   bound is **extensive** (`K' ~ Volume ~ (L')²`), which would break the affine condition
   `λ' ≤ s'/(2K')`. The *actual* `u₄(f)` for a fixed (compactly-supported) `f` is volume-independent
   by **clustering**, so the issue is bound-crudeness, not the truth. ⇒ The weak-coupling `u₄ < 0`
   must be stated with **volume-independent constants for a fixed test function** (exploit clustering),
   i.e. in dimensionless form depending only on `λ/m²`. Is `lattice_u4_neg_uniform` already
   `L`-uniform enough, or does it need a clustering refinement?
2. **Wick-ordering covariance.** The (renormalized) Wick subtraction must transform consistently under
   dilation + field rescale; in 2D (super-renormalizable) only the Wick constant renormalizes — check
   `:φ⁴:_{C}` ↦ `:φ⁴:_{C'}` is exactly the dilation image with no leftover.
3. **Does the continuum limit commute with rescaling?** Prove the equivalence *after* the limit (at
   the continuum measure level, where rescaling is clean) — confirm the dilation pushforward of the
   *continuum* `μ` equals the continuum `μ` of the dilated parameters (not just lattice-approximately).

## Why this is the right framing regardless
It relocates the hard step from "N-uniform mass-graded `∫V²` entangled with the 2D log-divergence"
(lattice grind, never clean) to **structural continuum scale-covariance**, and makes the proven
weak-coupling engine the load-bearing core. The main genuinely-new work is brick 2 (continuum
rescaling equivalence) and resolving open subtlety 1 (a `dimensionless`/clustering form of the
weak-coupling bound).
