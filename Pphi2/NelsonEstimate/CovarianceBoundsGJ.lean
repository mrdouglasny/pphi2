import Pphi2.NelsonEstimate.FieldDecomposition
import Pphi2.NelsonEstimate.HeatKernelBound

noncomputable section

namespace Pphi2

open GaussianField

/-- **Glimm-Jaffe Thm 8.5.2 (smooth-side, d=2).** Polylog `T` bound on
the smooth Wick constant, uniform in `(N, a)` at fixed `L = N · a`:

  `smoothWickConstant d N a mass T ≤ A + B · (1 + |log T|)`

with `A, B ≥ 0` depending only on `(mass, L)`. The `hd : d = 2`
restriction is essential: in `d ≥ 3` the smooth Wick constant diverges
as `T^{-1/2}` (power-law, not log), and the axiom is mathematically
false.

**References:** Glimm–Jaffe, *Quantum Physics: A Functional Integral
Point of View*, 2nd ed., Theorem 8.5.2 + Lemma 8.5.4 (lattice heat
kernel trace bound); Reed–Simon vol. II, Theorem XI.2 (heat kernel
trace).

**Vetting:** Gemini deep-think (DT 2026-05-12) — verdict **Standard**.
The 2026-05-12 vetting round caught a d=2 trap (the original draft
had `d : ℕ` quantified generically) and confirmed (a) correct typing,
(b) correct strength matching Glimm–Jaffe Thm 8.5.2, (c) non-vacuity,
(d) sufficiency for downstream S4 use. Full record at
`AXIOM_AUDIT.md` (2026-05-12 entry) and `docs/phase-B-textbook-axioms.md`.

**Discharge strategy:** tighten the existing `heat_kernel_1d_bound`
(currently with the trivial `C = N` constant) to the textbook
`(a, N)`-uniform `C(L)` form via `gaussian_sum_bound`
(`Pphi2/NelsonEstimate/HeatKernelBound.lean:204` — uniform Gaussian
sum estimate via `sin² ≥ (2/π)² · x²` on [0, π/2]). Propagate through
`heat_kernel_trace_bound` and the Schwinger integral
`c_S = ∫_T^∞ trace(e^{-t · M_a})/|Λ| dt`. Estimated ~500-800 lines /
2-3 weeks. Full plan: `docs/phase-B-textbook-axioms.md`. -/
theorem smoothWickConstant_le_log_uniform_in_aN
    {d : ℕ} (hd : d = 2) (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a)
        (_h_vol : (N : ℝ) * a = L)
        (T : ℝ) (_hT : 0 < T),
        smoothWickConstant d N a mass T ≤ A + B * (1 + |Real.log T|) :=
  smoothWickConstant_le_log_uniform_in_aN_proved hd mass L hL hmass

/-- **Glimm-Jaffe Thm 8.5.2 (rough-side, d=2).** Position-space `L^m`
site-sum bound for the canonical rough covariance, uniform in `(N, a)`
at fixed `L = N · a`:

  `a^d · Σ_y |C_R(x, y)|^m ≤ C_m · T`     for all `m ≥ 1`

with `C_m > 0` depending only on `(mass, L, m)`. The `hd : d = 2`
restriction is essential: for `d ≥ 3` the scaling becomes
`T^{m(1 − d/2) + d/2}`, which diverges at `m ≥ 3` for `d = 3` — the
linear-in-`T` bound asserted here is a magical d=2 property (the
exponent reduces to `m · 0 + 1 = 1`).

**References:** Glimm–Jaffe, *Quantum Physics*, 2nd ed., Theorem 8.5.2
+ Lemma 8.5.5 (rough covariance position-space estimates); Janson,
*Gaussian Hilbert Spaces*, Ch. 6 (hypercontractivity input).

**Vetting:** Gemini deep-think (DT 2026-05-12) — verdict **Standard**.
Same vetting round as the smooth-side axiom; caught the d=2 trap and
confirmed `|C_R|^m` (vs `C_R^m`) is the correct LHS for the m-odd case
and that per-`m` existential `C_m` (vs uniform in `m`) is sufficient
for the downstream S4 use, where `m` is fixed to `k - j` per cross-term.
Full record at `AXIOM_AUDIT.md` (2026-05-12 entry).

**Discharge strategy:**
* `m = 1`: directly from the Schwinger identity + heat-kernel
  probability normalisation `a^d · Σ_y p_t(x, y) = 1` (gives
  `a^d · Σ_y C_R(x, y) = ∫_0^T 1 dt = T`).
* `m = 2`: position-space rewrite of the existing
  `roughCovariance_sq_summable` via Plancherel + translation
  invariance.
* `m ≥ 3`: Hölder interpolation between `m = 2` and the L^∞ bound on
  off-diagonal `C_R(x, y)` (which decays Gaussian-exponentially in
  `|x − y|`, dominating the at-most-logarithmic coincident-points
  divergence in d=2).

Estimated ~300-500 lines / 1-2 weeks. Full plan:
`docs/phase-B-textbook-axioms.md`. -/
axiom canonicalRoughCovariance_pow_sum_le_uniform_in_aN
    {d : ℕ} (hd : d = 2) (mass L : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ C_m : ℝ, 0 < C_m ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (_ha : 0 < a)
        (_h_vol : (N : ℝ) * a = L)
        (T : ℝ) (_hT : 0 < T) (x : FinLatticeSites d N),
        a^d * ∑ y : FinLatticeSites d N,
          |canonicalRoughCovariance d N a mass T x y| ^ m ≤ C_m * T

end Pphi2
