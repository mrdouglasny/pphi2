/-
Enumerate "significant" declarations in our own namespaces: theorems, defs,
axioms and structures that are not internal/auto-generated. Emits one
fully-qualified name per line with its kind, e.g. `thm Pphi2.pphi2_exists`.
Run: lake env lean scripts/BlueprintEnum.lean
-/
import Pphi2
import Pphi2.Main

open Lean

def ourNS : List String :=
  ["Pphi2", "Common", "GaussianField", "Nuclear", "SchwartzNuclear", "SmoothCircle",
   "Lattice", "HeatKernel", "Torus", "GeneralResults", "Minlos", "BochnerMinlos",
   "Bochner", "GaussianHilbert", "MarkovSemigroups", "HilleYosida", "SpectralPositivity",
   "GibbsVariational"]

partial def topNS : Name → Name
  | .str .anonymous s => .str .anonymous s
  | .str p _ => topNS p
  | .num p _ => topNS p
  | .anonymous => .anonymous

def isOurs (n : Name) : Bool :=
  ourNS.contains (toString (topNS n)) || n == `minlos_theorem

def kindOf : ConstantInfo → Option String
  | .thmInfo _ => some "thm"
  | .defnInfo _ => some "def"
  | .axiomInfo _ => some "axiom"
  | .inductInfo _ => some "struct"
  | _ => none

def badInfix : List String :=
  ["._", "match_", ".proof_", ".eq_", ".sizeOf_", ".below", ".brecOn",
   ".rec", ".recAux", ".casesOn", ".noConfusion", ".mk.inj",
   ".binductionOn", ".induct"]

#eval show CoreM Unit from do
  let env ← getEnv
  env.constants.forM fun n ci => do
    if !isOurs n then return
    if n.isInternal then return
    let s := toString n
    if badInfix.any (fun p => (s.splitOn p).length > 1) then return
    match kindOf ci with
    | none => return
    | some k => IO.println s!"{k} {n}"
