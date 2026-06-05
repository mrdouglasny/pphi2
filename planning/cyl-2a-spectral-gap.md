# Discharge plan — CYL-2a: spectral gap + clustering (OS4)

Covers axioms **17 `spectral_gap_uniform`**, **16 `spectral_gap_lower_bound`**,
**14 `two_point_clustering_from_spectral_gap`**, **15 `general_clustering_from_spectral_gap`**.
Gates **OS4** (mass gap / clustering) — the property the compact torus could not give, and the
reason the cylinder is the gateway to OS reconstruction.

## Key insight: clustering rides on the B2 trace bridge

The two clustering axioms are **not** independent hard analytic work — they are the same
machinery as Layer B2's trace bridge:

- `two_point_clustering_from_spectral_gap` asks for `|⟨δ_{t,x} δ_{0,y}⟩ − ⟨δ⟩⟨δ⟩| ≤ C
  e^{−massGap·a·d_cyc}`. Via `twoPoint_dictionary` + the kernel↔operator link
  (`asymTransferKernel_kPow_apply`, **proved**), the connected lattice two-point equals the
  operator connected two-point `⟪Ω, M_{δ_x} Tᵈ M_{δ_y} Ω⟫ − ⟨…⟩⟨…⟩`, which is **exactly**
  `ReflectionPositivity.GappedTransfer.connected_two_point_le` (**proved**, reflection-positivity
  PR #3): `≤ γᵈ ‖P₁ M_{δ_x} Ω‖‖P₁ M_{δ_y} Ω‖` with `γ = e^{−massGap·a}`.
- `general_clustering_from_spectral_gap` is the same with bounded `F, G` → multiplication operators
  `M_F, M_G` (now genuinely bounded, so no Gaussian-tail subtlety) — again `connected_two_point_le`.

**So: once the B2 Hilbert–Schmidt trace bridge lands** (see `B4B5-design.md`), both clustering
axioms follow with little extra work — `connected_two_point_le` already produces the exponential
decay. Difficulty for 14/15 is ★★ **given** the B2 trace bridge; they should be discharged in the
same PR. (They are stated on the SQUARE `FinLatticeField 2 Ns`; the asym/square transfer operator
machinery is shared, but check the square instance has the same `kPow`↔operator lemma — port
`asymTransferKernel_kPow_apply` to the square if not.)

## The genuinely independent hard core: `spectral_gap_uniform` (17) — ★★★

This is the one real new mountain in CYL-2a. The **finite-`a`** gap is already PROVED
(`asymGappedTransfer'` / `asymTransferNormalized_gap`, with `γ < 1` from Perron–Frobenius/Jentzsch).
What remains is **uniformity as `a → 0`**: `∃ m₀>0, a₀>0, ∀ a≤a₀, m₀ ≤ massGap`, i.e. the
*physical* mass `m_phys = −log(λ₁/λ₀)/a` stays bounded below (as `a→0`, `λ₁/λ₀ → 1` but the
physical mass stays finite).

### ⚠ Honesty caveat (important — the axiom as stated is too strong)
φ⁴₂ has a **phase transition** at strong coupling (Glimm–Jaffe–Spencer): the `Z₂` symmetry breaks
and **the mass gap closes at the critical point**. So `spectral_gap_lower_bound`'s `c·mass ≤
massGap` for **all** `P` is **FALSE at criticality**, and `spectral_gap_uniform` for all `P` is
likewise false in the multiphase regime. Both axioms **need a regime hypothesis** — weak coupling
(small `λ`) or large bare mass `m` — under which the Wick-ordered interaction is a controlled
perturbation of the free gap `m`. The docstring already names the right tool (cluster expansion,
Glimm–Jaffe–Spencer), which **is** a weak-coupling method. **Action:** add a coupling-smallness /
single-phase hypothesis to the axiom statements before discharge (or restrict to the regime where
the construction is intended); discharging them verbatim (all `P`) is not possible.

### Discharge routes (regime-restricted), easiest first
1. **Continuum gap = limit of the lattice gap (fixed weak coupling).** The finite-`a` gap is
   proved; show `m_phys(a) = −log(λ₁(a)/λ₀(a))/a` converges to a positive limit as `a→0`. Needs:
   eigenvalue convergence `λ₀(a), λ₁(a)` (top two eigenvalues of the transfer operator) — leans on
   the compact-self-adjoint spectral theory already used for `asymGroundVector` (Jentzsch). The
   uniform *lower* bound on `λ₀/λ₁` separation as `a→0` is the crux; at weak coupling the gap is
   `≈ m + O(λ)` uniformly.
2. **Cluster expansion** (Glimm–Jaffe Ch. 18, Glimm–Jaffe–Spencer 1974) — the rigorous
   weak-coupling route giving gap + analyticity + uniqueness together. Heavy infrastructure
   (polymer/Mayer expansion); a major standalone project. Probably overkill if route 1 works for
   the gap alone.
3. **Perturbative lower bound** via the free gap `m` minus an interaction-norm bound — the spirit
   of `spectral_gap_lower_bound` (`m_phys ≥ c·m`). Tractable at weak coupling: `‖interaction part
   of H‖` bounded by the Nelson/hypercontractive estimates pphi2 already has (`asymNelson_*`),
   giving `m_phys ≥ m − Cλ > 0` for small `λ`.

**Recommended:** route 3 (perturbative lower bound using the existing Nelson estimates) for
`spectral_gap_lower_bound`, then route 1 (limit) for `spectral_gap_uniform`, **both under an
explicit weak-coupling hypothesis**. Vet the regime + the `a→0` eigenvalue argument with a
Gemini/Codex design pass first (as for crux-2 — the `a`-scaling of `m_phys` is error-prone).

## Existing infrastructure to reuse
- `asymGappedTransfer'`, `asymTransferNormalized_gap` (finite-`a` gap, proved).
- `AsymJentzsch.lean` (Perron–Frobenius: top eigenvalue simple, ground vector `Ω`).
- `connected_two_point_le` / `connected_susceptibility_le` (reflection-positivity, proved) — the
  clustering engine.
- `asymTransferKernel_kPow_apply` (proved) — the kernel↔operator link.
- `AsymNelson.lean` (hypercontractive/chaos bounds) — for the perturbative interaction-norm bound.

## Status / sequencing
- [ ] **17 `spectral_gap_uniform`** — ★★★, regime-restricted; needs the `a→0` eigenvalue-gap
  argument + weak-coupling hypothesis. Design pass first. **Independent of B2.**
- [ ] **16 `spectral_gap_lower_bound`** — ★★★→★★ at weak coupling (perturbative `m_phys ≥ m − Cλ`
  via Nelson). Do with 17.
- [ ] **14 `two_point_clustering`** — ★★ **given B2 trace bridge** (= `connected_two_point_le`).
- [ ] **15 `general_clustering`** — ★★ **given B2 trace bridge**. Do 14/15 in the B2 trace-bridge PR.

References: Glimm–Jaffe *Quantum Physics* Ch. 6.2, 18; Glimm–Jaffe–Spencer (1974, phase transition
+ cluster expansion); Simon *P(φ)₂* §III.3; Reed–Simon IV Thm XIII.44.
