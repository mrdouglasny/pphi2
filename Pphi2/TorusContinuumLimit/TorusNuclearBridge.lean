/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bridge: TorusTestFunction is Hilbert-Nuclear

Proves `IsHilbertNuclear (TorusTestFunction L)` via the chain:
1. `DyninMityaginSpace (TorusTestFunction L)` (gaussian-field, inferInstance)
2. `DyninMityaginSpace → NuclearSpace` (gaussian-field, Nuclear/NuclearSpace.lean)
3. `NuclearSpace → IsNuclear` (bridge: ‖·‖ = |·| for ℝ-valued CLFs)
4. `IsNuclear → IsHilbertNuclear` (bochner, Minlos/PietschBridge.lean)

Also provides `SeparableSpace` and `Nonempty` for Minlos theorem application.
-/

import Minlos.NuclearSpace
import Minlos.PietschBridge
import Minlos.Main
import Nuclear.NuclearSpace
import Torus.Restriction
import Mathlib.Topology.Separation.Basic

noncomputable section

open GaussianField

variable (L : ℝ) [Fact (0 < L)]

/-! ## NuclearSpace → IsNuclear bridge (same as OSforGFF) -/

/-- Convert gaussian-field's `NuclearSpace` to bochner's `IsNuclear`.
For ℝ-valued continuous linear functionals, `‖f x‖ = |f x|`. -/
private theorem nuclearSpace_to_isNuclear
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [hN : GaussianField.NuclearSpace E] : IsNuclear E := by
  intro p hp
  obtain ⟨q, hq_cont, hq_ge, f, c, hc_nn, hc_sum, hf_bnd, hdom⟩ :=
    hN.nuclear_dominance p hp
  refine ⟨q, hq_cont, hq_ge, f, c, hc_nn, hc_sum, fun n x => ?_, fun x => ?_⟩
  · rw [← Real.norm_eq_abs]; exact hf_bnd n x
  · have := hdom x; simp_rw [Real.norm_eq_abs] at this; exact this

/-! ## WithSeminorms reindexing -/

/-- Reindexing a seminorm family by an equivalence preserves `WithSeminorms`. -/
private theorem WithSeminorms.equiv
    {𝕜 E ι ι' : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E]
    {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) (e : ι' ≃ ι) :
    WithSeminorms (p ∘ e) := by
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf] at hp ⊢
  simp_rw [Function.comp_apply, hp]
  exact (Equiv.iInf_comp e).symm

/-! ## Main instances -/

/-- `TorusTestFunction L` is Hilbert-nuclear. -/
instance torusTestFunction_isHilbertNuclear :
    IsHilbertNuclear (TorusTestFunction L) := by
  sorry -- Chain: DyninMityaginSpace → NuclearSpace → IsNuclear → IsHilbertNuclear
  -- Needs: ℕ-indexed seminorms from Countable ι + WithSeminorms reindexing

instance torusTestFunction_separableSpace :
    TopologicalSpace.SeparableSpace (TorusTestFunction L) := by
  sorry -- from DyninMityaginSpace basis density

instance : Nonempty (TorusTestFunction L) := ⟨0⟩

end
