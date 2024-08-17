import Lean.Elab.Command
import Mathlib.Lean.Name
-- import Lean.Elab.Print
-- import Mathlib.Lean.Expr.Basic
-- import Batteries.Tactic.PrintDependents

open Lean Elab Command

namespace AutoBlueprint

abbrev excludedRootNames : NameSet := NameSet.empty
  |>.insert `Init
  |>.insert `Lean
  |>.insert `Qq
  |>.insert `ImportGraph
  |>.insert `ProofWidgets
  |>.insert `Std
  |>.insert `Aesop
  |>.insert `Batteries
  |>.insert `Mathlib
  |>.insert `AutoBlueprint

abbrev excludedConstNames (n : Name) : Bool :=
  n.isAuxLemma ||
  n.isImplementationDetail ||
  n.isInternalDetail ||
  n.isInternal ||
  n.isInternalOrNum ||
  n.isInaccessibleUserName ||
  n.isAnonymous ||
  n.isNum

end AutoBlueprint

open AutoBlueprint

namespace Lean.Environment

variable (env : Environment)

def userDefinedModules : SMap Name ModuleIdx := Id.run do
  let names := env.allImportedModuleNames.filter (!excludedRootNames.contains ·.getRoot)
  let mut smap := SMap.empty
  for n in names do
    let idx := (env.getModuleIdx? n).get!
    smap := smap.insert n idx
  return smap

end Lean.Environment

namespace AutoBlueprint

def createBlueprint : CommandElabM Unit := do
  let env ← getEnv
  let userModules := env.userDefinedModules

  for (n, idx) in userModules.toList do
    IO.println s!"{n} {idx}"

end AutoBlueprint
