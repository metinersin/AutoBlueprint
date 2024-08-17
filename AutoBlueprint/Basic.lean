import Lean.Elab.Command
import ImportGraph.RequiredModules
import Mathlib.Lean.Name
import AutoBlueprint.Lean.Declaration

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

def userDefinedConstants : ConstMap × ConstantInfoSet :=
  let modules := env.userDefinedModules
  let f (acc : ConstMap × ConstantInfoSet) (n : Name) (c : ConstantInfo)
      :  ConstMap × ConstantInfoSet :=
    match env.getModuleFor? n with
    | none => acc
    | some modName =>
      if modules.contains modName && not (excludedConstNames n) then
        (acc.1.insert n c, acc.2.insert c)
      else
        acc
  env.constants.fold f ({}, {})

end Lean.Environment

namespace AutoBlueprint

def getStream (fname : Option String) : IO IO.FS.Stream :=
  match fname with
  | some fname => do
    let handle ← IO.FS.Handle.mk fname IO.FS.Mode.write
    pure $ IO.FS.Stream.ofHandle handle
  | none => do
    let stream ← IO.getStdout
    pure stream

def createBlueprint (fname : Option String) : CommandElabM Unit := do
  let env ← getEnv

  let stream ← getStream fname

  -- user defined modules
  let userModules := env.userDefinedModules
  stream.putStrLn "User modules:"
  for (n, idx) in userModules.toList do
    stream.putStrLn s!"{n} {idx}"
  stream.putStrLn ""

  -- user defined constants
  let (constMap, constInfoSet) := env.userDefinedConstants
  stream.putStrLn "User constants:"
  for c in constInfoSet do
    stream.putStrLn s!"{c.name}"
  stream.putStrLn ""

  IO.println "Done!"

end AutoBlueprint
