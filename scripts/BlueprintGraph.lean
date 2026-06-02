/-
Full blueprint graph extractor. Enumerates significant declarations in our own
namespaces and, for each, emits its *direct* in-set dependencies (constants
appearing in its type/value that are themselves enumerated). For the full set
the direct edges are accurate (intermediate lemmas are nodes too), so no
transitive closure/reduction is needed.

Output (TSV): `<kind>\t<fqName>\t<module>\t<dep1> <dep2> ...`
Run: lake env lean scripts/BlueprintGraph.lean > scripts/blueprint_graph.tsv
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

def badInfix : List String :=
  ["._", "match_", ".proof_", ".eq_", ".sizeOf_", ".below", ".brecOn",
   ".rec", ".recAux", ".casesOn", ".noConfusion", ".mk.inj", ".binductionOn", ".induct"]

def kindOf : ConstantInfo → Option String
  | .thmInfo _ => some "thm"
  | .defnInfo _ => some "def"
  | .axiomInfo _ => some "axiom"
  | .inductInfo _ => some "struct"
  | _ => none

def declValue? : ConstantInfo → Option Expr
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | .opaqueInfo o => some o.value
  | _ => none

def significant (n : Name) (ci : ConstantInfo) : Bool :=
  isOurs n && !n.isInternal && (kindOf ci).isSome &&
  !(badInfix.any (fun p => ((toString n).splitOn p).length > 1))

#eval show CoreM Unit from do
  let env ← getEnv
  -- pass 1: collect the node set (functional fold; forM closures can't mutate)
  let nodes : NameSet := env.constants.fold
    (fun s n ci => if significant n ci then s.insert n else s) {}
  -- pass 2: emit edges
  env.constants.forM fun n ci => do
    if !significant n ci then return
    let consts := ci.type.getUsedConstants ++ ((declValue? ci).map Expr.getUsedConstants).getD #[]
    let deps := consts.foldl (fun (s : NameSet) c =>
      if c != n && nodes.contains c then s.insert c else s) {}
    let modName := (env.getModuleFor? n).map toString |>.getD "?"
    let kind := (kindOf ci).getD "?"
    let depStr := String.intercalate " " (deps.toList.map toString)
    IO.println s!"{kind}\t{n}\t{modName}\t{depStr}"
