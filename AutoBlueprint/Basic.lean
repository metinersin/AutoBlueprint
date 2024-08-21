import Lean.Elab.Command
import ImportGraph.RequiredModules
import Mathlib.Lean.Name
import Mathlib.Lean.Expr.Basic

import AutoBlueprint.Latex.Basic

open Lean Elab Command

namespace Lean.Name

abbrev builtinModuleRoots : NameSet := NameSet.empty
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

def isBuiltinModuleName (n : Name) : Bool := builtinModuleRoots.contains n.getRoot

abbrev isAutoConstant (n : Name) : Bool :=
  n.isAuxLemma ||
  n.isImplementationDetail ||
  n.isInternalDetail ||
  n.isInternal ||
  n.isInternalOrNum ||
  n.isInaccessibleUserName ||
  n.isAnonymous ||
  n.isNum

end Lean.Name

namespace Lean.NameSet

def containsAutoConstant (ns : NameSet) : Bool := Id.run do
  let mut result := false
  for n in ns do
    if n.isAutoConstant then
      result := True
      break
  return result

end Lean.NameSet

namespace AutoBlueprint

structure EnvironmentData where
  /--
  Current environment
  -/
  env : Environment

  /--
  Names of all imported modules.
  -/
  modules : NameSet := env.allImportedModuleNames.foldl (init := {}) .insert

  /--
  Names of all imported modules whose root name is not in `builtinModuleRoots`.
  -/
  userModules : NameSet :=
    modules.fold (init := {}) fun acc n =>
      if Name.isBuiltinModuleName n then acc else acc.insert n

  /--
  All constants currently avaliable in the environment as a `ConstMap`.
  -/
  constants : ConstMap := env.constants

  /--
  All constants as a dictionary where the key is the constant name and the value is the module in which the constant is defined.
  -/
  constantsAsNameModule : SMap Name Name :=
    env.constants.fold (init := {})
      fun (acc : SMap Name Name) (n : Name) _ =>
        acc.insert n (env.getModuleFor? n).get!

  /--
  All constants whose defining module is in `userModules`, as a `ConstMap`. This includes automatically generated constants.
  -/
  constantsInUserModules : ConstMap :=
    env.constants.fold (init := {})
      fun (acc : ConstMap) (n : Name) (c : ConstantInfo) =>
        match env.getModuleFor? n with
        | none => acc
        | some moduleName =>
          if userModules.contains moduleName then
            acc.insert n c
          else
            acc

  /--
  All constants explicitly written by the user (and hence whose defining module is in `userModules`) as a `ConstMap`.
  -/
  nonautoConstants : ConstMap :=
    constantsInUserModules.fold (init := {})
      fun (acc : ConstMap) (n : Name) (c : ConstantInfo) =>
        if Name.isAutoConstant n then
          acc
        else
          acc.insert n c

  /--
  All automatically generated constants whose defining module is in `userModules`, as a `ConstantInfoSet`.
  -/
  autoConstansInUserModules : ConstMap :=
    constantsInUserModules.fold (init := {})
      fun (acc : ConstMap) (n : Name) (c : ConstantInfo) =>
        if Name.isAutoConstant n then
          acc.insert n c
        else
          acc

namespace EnvironmentData

/--
All constants occurring in the given expression and whose defining module is in `userModules`.
-/
def usedConstantsFromUserModules (envData : EnvironmentData) (e : Expr) : NameSet :=
  e.foldConsts (init := {})
    fun (n : Name) (acc : NameSet) =>
      if envData.constantsInUserModules.contains n then
        acc.insert n
      else
        acc

/--
All constants whose defining module is in `userModules` and occurring in the type of the given constant.
-/
def firstOrderTypeDependencies (envData : EnvironmentData) (c : ConstantInfo) : NameSet :=
  envData.usedConstantsFromUserModules c.type

/--
All constants whose defining module is in `userModules` and occurring in the value of the given constant.
-/
def firstOrderValueDependencies (envData : EnvironmentData) (c : ConstantInfo) : NameSet :=
  match c with
  | ConstantInfo.axiomInfo _ => {}
  | ConstantInfo.opaqueInfo _ => {}
  | ConstantInfo.quotInfo _ => {}
  | ConstantInfo.defnInfo v => envData.usedConstantsFromUserModules v.value
  | ConstantInfo.thmInfo v => envData.usedConstantsFromUserModules v.value
  | ConstantInfo.ctorInfo _ => {}
  | ConstantInfo.inductInfo v =>
    v.ctors.foldl (init := {})
      fun acc n =>
        if envData.constantsInUserModules.contains n then
          acc.insert n
        else
          acc
  | ConstantInfo.recInfo _ => {}

/--
All constants whose defining module is in `userModules` and occurring in the type or value of the given constant.
-/
def firstOrderDependencies (envData : EnvironmentData) (c : ConstantInfo) : NameSet :=
  envData.firstOrderTypeDependencies c ++ envData.firstOrderValueDependencies c

/--
Replace an automatically generated name in `deps` with the first order dependencies of the corresponding constant.
-/
def expandDependencies (envData : EnvironmentData) (deps : NameSet)
    : NameSet := Id.run do
  let mut depsExpanded : NameSet := {}
  for n in deps do
    if n.isAutoConstant then
      let c := envData.constantsInUserModules.find! n
      let newDeps := envData.firstOrderDependencies c
      depsExpanded := depsExpanded ++ newDeps
    else
      depsExpanded := depsExpanded.insert n
  return depsExpanded

/--
All non-automatically generated constants whose defining module is in `userModules` and on which the type of `c` depends. This functions starts with `envData.firstOrderTypeDependencies c` and applies `expandDependencies` iteratively until no automatically generated constants are left.
-/
def typeDependenciesAsNameSet (envData : EnvironmentData) (c : ConstantInfo) : NameSet := Id.run do
  let mut deps := envData.firstOrderTypeDependencies c
  while deps.containsAutoConstant do
    deps := envData.expandDependencies deps
  return deps

/--
All non-automatically generated constants whose defining module is in `userModules` and on which the value of `c` depends. This functions starts with `envData.firstOrderValueDependencies c` and applies `expandDependencies` iteratively until no automatically generated constants are left.
-/
def valueDependenciesAsNameSet (envData : EnvironmentData) (c : ConstantInfo) : NameSet := Id.run do
  let mut deps := envData.firstOrderValueDependencies c
  while deps.containsAutoConstant do
    deps := envData.expandDependencies deps
  return deps

end EnvironmentData

inductive Kind where
  | defin
  | thm
  | other

namespace Kind

def toString : Kind → String
  | defin => "definition"
  | thm => "theorem"
  | other => "other"

instance : ToString Kind := ⟨toString⟩

def mkFromConstantInfo (c : ConstantInfo) : Kind :=
  if c.isThm then
    Kind.thm
  else if c.isDef then
    Kind.defin
  else
    Kind.other

end Kind

structure Decl where
  info : ConstantInfo

  name : Name := info.name

  kind : Kind := Kind.mkFromConstantInfo info

  type_deps : NameSet

  value_deps : NameSet

  typeSorryFree : Bool := !info.type.hasSorry

  valueSorryFree : Bool :=
    match info.value? with
    | none => true
    | some v => !v.hasSorry

  human_statement : String

  /--
  If it is something that requires a proof.
  -/
  human_proof : Option String

namespace Decl

def toLatex (d : Decl) : List LatexEnvironment :=
  let primaryLatexEnvironment : LatexEnvironment := {
    env_name := d.kind.toString,
    lean_name? := some d.name,
    leanok := d.typeSorryFree,
    uses := d.type_deps.toList.map Name.toString,
    content := d.human_statement
  }

  match d.human_proof with
  | none => [primaryLatexEnvironment]
  | some human_proof =>
    let proofLatexEnvironment : LatexEnvironment := {
      env_name := "proof",
      lean_name? := none,
      label? := none,
      leanok := d.valueSorryFree,
      uses := d.value_deps.toList.map Name.toString,
      content := human_proof
    }
    [primaryLatexEnvironment, proofLatexEnvironment]

end Decl

def EnvironmentData.summarize (envData : EnvironmentData) : Array Decl := Id.run do
  let mut result : Array Decl := #[]

  for (_, c) in (envData.nonautoConstants : SMap _ _) do
    let decl : Decl := {
      info := c,
      type_deps := envData.typeDependenciesAsNameSet c,
      value_deps := envData.valueDependenciesAsNameSet c,
      human_statement := "",
      human_proof := ""
    }
    result := result.push decl

  return result

end AutoBlueprint
