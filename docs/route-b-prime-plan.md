# Route B': Asymmetric Torus → Cylinder

## Overview

Route B' constructs the interacting P(φ)₂ measure on the cylinder
S¹_W × ℝ by taking limits of asymmetric tori T_{L,W} = (ℝ/Lℤ) × (ℝ/Wℤ)
with L → ∞ (time direction to infinity) and W fixed (spatial circle).

This extends Route B (symmetric torus, 0 axioms for OS0–OS2) to include
OS3 (reflection positivity) and the infinite-volume limit.

## Construction: Two Limits

### Step 1: UV limit (= Route B on asymmetric torus)

For each L, W > 0, construct the interacting measure on T_{L,W}:

  μ_{P,L,W} = weak limit of (ι_N)_* ((1/Z_N) exp(-V_N) dμ_{GFF,N})

where the lattice is (ℤ/N_L ℤ) × (ℤ/N_W ℤ) with spacing a = L/N_L = W/N_W
(or independent spacings a_L, a_W → 0).

Route B's proofs of OS0–OS2 apply verbatim to each asymmetric torus:
- The test function space C∞(S¹_L) ⊗̂ C∞(S¹_W) has the same NTP structure
- Nelson's estimate: a² N_L N_W = L W (physical volume), bounded
- Tightness, weak convergence, OS0–OS2 all transfer

The only modification: the DyninMityaginSpace basis depends on (L, W)
rather than a single L.

### Step 2: IR limit (L → ∞)

Take L → ∞ with W fixed. The torus measures {μ_{P,L,W} : L > 0} form
a projective system (restriction from T_{L',W} to T_{L,W} for L' > L
is consistent). Their projective limit is the cylinder measure μ_{P,W}.

Alternatively: embed T_{L,W} configurations into cylinder distributions
via restriction maps, and show tightness of the embedded measures.

**Tightness for L → ∞:**
- For test functions f supported in a time interval [-T, T] ⊂ ℝ:
  E_{μ_{P,L,W}}[(ωf)²] ≤ C · G_W(f,f) uniformly in L
  (the Green's function G_W on the cylinder is the L → ∞ limit of G_{L,W},
  and G_{L,W}(f,f) ≤ G_W(f,f) + O(exp(-mL)) for compactly supported f)
- Mitoma-Chebyshev gives tightness

**Convergence:**
- The characteristic functionals Z_{L,W}[f] converge to Z_W[f]
  for each compactly supported f (by the same approximation argument
  as Route B, using lattice translation invariance + continuity)

## OS Axioms on the Cylinder

### OS0–OS1: From Route B
Direct transfer from the torus (each torus measure satisfies OS0–OS1,
the limit inherits them).

### OS2: Translation + spatial rotation
- Spatial translations (along S¹_W): exact symmetry at each torus
- Time translations (along ℝ): from the L → ∞ limit
  (lattice time translations approximate continuous ones, same as Route B)
- Spatial reflection: exact lattice symmetry
- Time reflection Θ: t ↦ -t: exact lattice symmetry

### OS3: Reflection Positivity (NEW)
This is the main new result. For the cylinder S¹_W × ℝ:
- Time reflection Θ: (t, x) ↦ (-t, x)
- Positive-time test functions: supported in {t > 0}
- RP matrix: M_{ij} = Re(Z[f_i - Θf_j]) ≥ 0

**Proof from transfer matrix:**
At each lattice cutoff, the transfer matrix T = exp(-aH) is a positive
operator on L²(configurations of spatial lattice). The RP condition
at the lattice level follows from T being a positive operator:

  Σ_{ij} c_i c̄_j ∫ exp(-V(t>0)) exp(-V(t<0)) Θ(exp(-V(t<0))) dμ_GFF ≥ 0

This is proved in Route C's `OS3_RP_Lattice.lean` using the Laplace
factorization of the lattice Green's function.

The L → ∞ limit preserves RP (positive semidefiniteness is a closed condition).

### OS4: Clustering / Mass Gap
From the spectral gap of the transfer matrix:
- T has a unique ground state (Jentzsch/Perron-Frobenius)
- Spectral gap λ₀ - λ₁ > 0 gives exponential decay of correlations
- This transfers to the continuum limit as the physical mass gap

## What's Needed (Beyond Route B)

1. **Asymmetric torus infrastructure:** Generalize TorusTestFunction from
   NTP(SMC_L, SMC_L) to NTP(SMC_L, SMC_W) with possibly different L, W.
   Most Route B proofs carry over with minor parameter changes.

2. **IR limit (L → ∞):** Tightness + weak convergence of torus measures
   as L → ∞. Needs cylinder test function space + embedding maps.

3. **OS3 from transfer matrix:** Adapt `OS3_RP_Lattice.lean` (Route C)
   to the torus → cylinder setting. The lattice RP proof is already done;
   needs weak limit transfer.

4. **Transfer matrix / spectral gap:** For OS4 and the mass gap.
   Existing Route C infrastructure (`TransferMatrix/`) applies.

## Advantages

- **Reuses Route B:** All OS0–OS2 proofs (0 axioms) directly apply
- **Clean IR limit:** The L → ∞ limit is simpler than the UV limit
  (no renormalization, just volume growth)
- **Natural OS3:** The cylinder has the right geometry for RP
- **Modular:** UV limit (Route B) and IR limit (new) are independent

## References

- Glimm-Jaffe, *Quantum Physics*, Chapter 19 (finite → infinite volume)
- Simon, *The P(φ)₂ Euclidean QFT*, Chapter VIII (infinite volume limit)
- Guerra-Rosen-Simon (1975), "The P(φ)₂ Euclidean quantum field theory
  as classical statistical mechanics"
