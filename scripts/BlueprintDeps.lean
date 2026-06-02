/-
Extract the *real* declaration-level dependency edges among a curated set of
"blueprint" declarations, by walking each declaration's transitive
used-constants closure (restricted to our own namespaces) in the compiled
environment. Run with:  lake env lean scripts/BlueprintDeps.lean
Output: lines `A -> B C D ...` giving, for each target A, the targets reachable
from A through our code (before transitive reduction, done in post-processing).
-/
import Pphi2
import Pphi2.Main

open Lean

namespace BlueprintDeps

/-- First name component, e.g. `Pphi2` from `Pphi2.foo.bar`. -/
def topNS : Name → Name
  | .str .anonymous s => .str .anonymous s
  | .str p _ => topNS p
  | .num p _ => topNS p
  | .anonymous => .anonymous

/-- Namespaces belonging to our own libraries (recurse only into these). -/
def ourNS : List String :=
  ["Pphi2", "Common", "GaussianField", "Nuclear", "SchwartzNuclear", "SmoothCircle",
   "Lattice", "HeatKernel", "Torus", "GeneralResults", "Minlos", "BochnerMinlos",
   "Bochner", "GaussianHilbert", "MarkovSemigroups", "HilleYosida", "SpectralPositivity",
   "GibbsVariational"]

def isOurs (n : Name) : Bool :=
  (ourNS.contains (toString (topNS n))) || n == `minlos_theorem

/-- Value expression of a declaration, if any (note: `ConstantInfo.value?`
    returns `none` for `thmInfo` in current Lean, so match explicitly). -/
def declValue? : ConstantInfo → Option Expr
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | .opaqueInfo o => some o.value
  | _ => none

/-- Constants directly referenced by a declaration (type + value). -/
def directDeps (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none => #[]
  | some ci =>
    let fromType := ci.type.getUsedConstants
    let fromVal := ((declValue? ci).map Expr.getUsedConstants).getD #[]
    fromType ++ fromVal

/-- Transitive closure restricted to our namespaces (prunes mathlib/core). -/
partial def closure (env : Environment) (start : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack : Array Name := (directDeps env start).filter isOurs
  for d in stack do seen := seen.insert d
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    for d in (directDeps env c).filter isOurs do
      if !seen.contains d then
        seen := seen.insert d
        stack := stack.push d
  return seen

end BlueprintDeps

open BlueprintDeps in
#eval show CoreM Unit from do
  let env ← getEnv
  -- Read target names from scripts/blueprint_targets.txt (one fully-qualified name per line).
  let raw ← IO.FS.readFile "scripts/blueprint_targets.txt"
  let targets : List Name :=
    (raw.splitOn "\n").filterMap (fun s =>
      let s := s.trim
      if s.isEmpty || s.startsWith "#" then none else some s.toName)
  let tset : NameSet := targets.foldl (·.insert ·) {}
  let mut missing : List Name := []
  for a in targets do
    if (env.find? a).isNone then missing := a :: missing
  if !missing.isEmpty then
    IO.println s!"# MISSING decls (not in env): {missing}"
  for a in targets do
    let reach := closure env a
    let edges := targets.filter (fun b => b != a && reach.contains b)
    let edgeStr := String.intercalate " " (edges.map toString)
    IO.println s!"{a} -> {edgeStr}"
