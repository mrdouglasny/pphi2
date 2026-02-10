/-
  Pphi2.OSAxioms
  Osterwalder-Schrader axioms for d=2 Euclidean QFT on the cylinder,
  using the generic QFTFramework axiom definitions.

  Reference: Osterwalder-Schrader (1975), Glimm-Jaffe Ch. 6.
-/
import Pphi2.Basic
import OSforGFF.OS_Axioms_Generic

noncomputable section

open MeasureTheory

/-! ## OS Axioms for measures on the cylinder ℝ × S¹_L

We state the Osterwalder-Schrader axioms via the generic QFTFramework
interface. The measure lives on FieldConfigurationTorus 2 L, and the
axioms are parametrized by pphi2Framework L.
-/

/-- Partial OS axiom bundle matching what P(Φ)₂ proves on the cylinder
    (all except clustering/ergodicity).
    DDJ Theorem 1.1 establishes OS1 (regularity), OS2 (invariance),
    and OS3 (reflection positivity). -/
structure SatisfiesDDJ_OS_generic (F : QFTFramework)
    (dμ : ProbabilityMeasure F.FieldConfig) : Prop where
  os1 : OS1_Regularity_generic F dμ       -- E5: regularity
  os2 : OS2_Invariance_generic F dμ       -- E1: Euclidean invariance
  os3 : OS3_ReflectionPositivity_generic F dμ  -- E2: reflection positivity

end
