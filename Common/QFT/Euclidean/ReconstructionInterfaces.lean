import Common.QFT.Euclidean.Formulations

/-!
# Backend-independent reconstruction interfaces

This file isolates a lesson from the Osterwalder-Schrader discussions:

- packaged Euclidean Schwinger data,
- the extra linear-growth input needed for reconstruction,
- and the reconstruction rule itself

should be recorded independently of any particular upstream implementation.

In particular, this keeps "OS + linear growth gives Wightman data" separate from
any specific library's concrete definitions of OS packages or Wightman
functions. Downstream projects can then specialize these interfaces to a chosen
backend without making the backend part of the ambient Euclidean layer.
-/

namespace Common.QFT.Euclidean

universe uParams uSchwinger uOS uWightman

/-- Parameter-indexed packaged Schwinger-function data. This is intentionally
minimal: some downstream projects already have a concrete family of packaged
Schwinger functions before deciding how to package OS or Wightman data. -/
class PackagedSchwingerFunctionModel
    (Params : Type uParams) (SchwingerFamily : Type uSchwinger) (params : Params) where
  schwingerFunctions : SchwingerFamily

/-- Explicit linear-growth input for a packaged Schwinger family, factored
through a chosen OS package.

The point is to keep the growth hypothesis visible in the type rather than hide
it behind a slogan like "OS implies Wightman". -/
class ReconstructionLinearGrowthModel
    (Params : Type uParams) (SchwingerFamily : Type uSchwinger)
    (OSPackage : Type uOS) (osSchwinger : OSPackage → SchwingerFamily)
    (LinearGrowth : OSPackage → Prop) (params : Params)
    [PackagedSchwingerFunctionModel Params SchwingerFamily params] where
  os_package : OSPackage
  os_package_eq :
    osSchwinger os_package =
      PackagedSchwingerFunctionModel.schwingerFunctions
        (Params := Params) (SchwingerFamily := SchwingerFamily) (params := params)
  linear_growth : LinearGrowth os_package

namespace ReconstructionLinearGrowthModel

variable {Params : Type uParams} {SchwingerFamily : Type uSchwinger}
variable {OSPackage : Type uOS} {osSchwinger : OSPackage → SchwingerFamily}
variable {LinearGrowth : OSPackage → Prop}

/-- Existential view of a linear-growth interface: there is a concrete OS
package matching the current Schwinger family together with a witness of the
named growth hypothesis. -/
theorem matching_package (params : Params)
    [PackagedSchwingerFunctionModel Params SchwingerFamily params]
    [ReconstructionLinearGrowthModel
      Params SchwingerFamily OSPackage osSchwinger LinearGrowth params] :
    ∃ OS : OSPackage,
      osSchwinger OS =
        PackagedSchwingerFunctionModel.schwingerFunctions
          (Params := Params) (SchwingerFamily := SchwingerFamily) (params := params) ∧
      Nonempty (LinearGrowth OS) := by
  let h :=
    (inferInstance :
      ReconstructionLinearGrowthModel
        Params SchwingerFamily OSPackage osSchwinger LinearGrowth params)
  refine ⟨h.os_package, h.os_package_eq, ⟨h.linear_growth⟩⟩

end ReconstructionLinearGrowthModel

/-- Backend-independent OS-to-Minkowski reconstruction rule. This is separated
from the Euclidean hypotheses it consumes so downstream projects can swap in a
different reconstruction backend without changing their Euclidean packaging. -/
class WightmanReconstructionModel
    (Params : Type uParams) (OSPackage : Type uOS)
    (LinearGrowth : OSPackage → Prop) (WightmanFamily : Type uWightman)
    (WickRotationPair : OSPackage → WightmanFamily → Prop) (params : Params) where
  wightman_reconstruction :
    ∀ OS : OSPackage, LinearGrowth OS → ∃ Wfn : WightmanFamily, WickRotationPair OS Wfn

/-- Abstract reconstruction theorem: matching linear-growth data plus a
reconstruction rule produces Wightman data for the chosen Schwinger family. -/
theorem wightmanExistsOfLinearGrowthAndReconstruction
    {SchwingerFamily : Type uSchwinger} {OSPackage : Type uOS}
    {LinearGrowth : OSPackage → Prop} {WightmanFamily : Type uWightman}
    {osSchwinger : OSPackage → SchwingerFamily}
    {WickRotationPair : OSPackage → WightmanFamily → Prop}
    (S : SchwingerFamily)
    (hlinear : ∃ OS : OSPackage,
      osSchwinger OS = S ∧ Nonempty (LinearGrowth OS))
    (hreconstruct : ∀ OS : OSPackage,
      LinearGrowth OS → ∃ Wfn : WightmanFamily, WickRotationPair OS Wfn) :
    ∃ Wfn : WightmanFamily,
      ∃ OS : OSPackage, osSchwinger OS = S ∧ WickRotationPair OS Wfn := by
  rcases hlinear with ⟨OS, hOS, hlg_nonempty⟩
  rcases hlg_nonempty with ⟨hlg⟩
  rcases hreconstruct OS hlg with ⟨Wfn, hWR⟩
  exact ⟨Wfn, OS, hOS, hWR⟩

/-- Build a reconstruction-model instance from an explicit reconstruction rule. -/
theorem wightmanReconstructionModel_nonempty_of_data
    {Params : Type uParams} {OSPackage : Type uOS}
    {LinearGrowth : OSPackage → Prop} {WightmanFamily : Type uWightman}
    {WickRotationPair : OSPackage → WightmanFamily → Prop}
    (params : Params)
    (hreconstruct : ∀ OS : OSPackage,
      LinearGrowth OS → ∃ Wfn : WightmanFamily, WickRotationPair OS Wfn) :
    Nonempty (WightmanReconstructionModel
      Params OSPackage LinearGrowth WightmanFamily WickRotationPair params) := by
  exact ⟨{ wightman_reconstruction := hreconstruct }⟩

end Common.QFT.Euclidean
