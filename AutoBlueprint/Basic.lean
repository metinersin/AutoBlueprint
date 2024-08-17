import Lean.Elab.Command
import ImportGraph.RequiredModules
import Mathlib.Lean.Name
import Mathlib.Lean.Expr.Basic

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

end Kind

structure Decl where
  name : Name
  kind : Kind
  type_deps : NameSet
  value_deps : NameSet

end AutoBlueprint

open AutoBlueprint

namespace Lean

namespace Expr

def getUsedConstNamesFrom (consts : ConstMap) (e : Expr) : Array Name :=
  let f (n : Name) (ns : Array Name) : Array Name :=
    if consts.contains n then ns.push n else ns
  e.foldConsts #[] f

def getUsedConstInfoFrom (consts : ConstMap) (e : Expr) : Array ConstantInfo :=
  let f (n : Name) (arr : Array ConstantInfo) : Array ConstantInfo :=
    match consts.find? n with
    | some c => arr.push c
    | none => arr
  e.foldConsts #[] f

def getUsedConstNamesFromAsSet (consts : ConstMap) (e : Expr) : NameSet :=
  let f (n : Name) (ns : NameSet) : NameSet :=
    if consts.contains n then ns.insert n else ns
  e.foldConsts {} f

end Expr

def ConstantInfo.quickCmp (c₁ c₂ : ConstantInfo) : Ordering :=
  Name.quickCmp c₁.name c₂.name

def ConstantInfoSet := RBTree ConstantInfo ConstantInfo.quickCmp

namespace ConstantInfoSet

def empty : ConstantInfoSet := mkRBTree ConstantInfo ConstantInfo.quickCmp
instance : EmptyCollection ConstantInfoSet := ⟨empty⟩
instance : Inhabited ConstantInfoSet := ⟨empty⟩

instance : Coe ConstantInfoSet (RBTree ConstantInfo ConstantInfo.quickCmp) := ⟨id⟩

instance : ForIn m ConstantInfoSet ConstantInfo where
  forIn := RBTree.forIn

def contains (s : ConstantInfoSet) (c : ConstantInfo) : Bool := RBMap.contains s c

end ConstantInfoSet

namespace ConstantInfo

def getTypeDependencies (consts : ConstMap) (c : ConstantInfo) : Array Name :=
  c.type.getUsedConstNamesFrom consts

def getTypeDependenciesAsSet (consts : ConstMap) (c : ConstantInfo) : NameSet :=
  c.type.getUsedConstNamesFromAsSet consts

def getValueDependencies (consts : ConstMap) (c : ConstantInfo) : Array Name :=
  let f (acc : Array Name) (n : Name) : Array Name := if consts.contains n then acc.push n else acc
  match c.value? with
  | some v => v.getUsedConstNamesFrom consts
  | none => match c with
    | .inductInfo val => val.ctors.foldl f #[]
    | .opaqueInfo val => val.value.getUsedConstNamesFrom consts
    | .ctorInfo val => if consts.contains val.name then #[val.name] else #[]
    | .recInfo val => val.all.foldl f #[]
    | _ => #[]

def getValueDependenciesAsSet (consts : ConstMap) (c : ConstantInfo) : NameSet :=
  let f (acc : NameSet) (n : Name) : NameSet := if consts.contains n then acc.insert n else acc
  match c.value? with
  | some v => v.getUsedConstNamesFromAsSet consts
  | none =>
    match c with
      | .inductInfo val => @RBTree.ofList Name Name.quickCmp val.ctors |>.fold f NameSet.empty
      | .opaqueInfo val => val.value.getUsedConstNamesFromAsSet consts
      | .ctorInfo val =>
        if consts.contains val.name then NameSet.empty.insert val.name
        else NameSet.empty
      | .recInfo val => @RBTree.ofList Name Name.quickCmp val.all |>.fold f NameSet.empty
      | _ => {}

def getDependencies (consts : ConstMap) (c : ConstantInfo) : Array Name :=
  getTypeDependencies consts c ++ getValueDependencies consts c

def getDependenciesAsSet (consts : ConstMap) (c : ConstantInfo) : NameSet :=
  getTypeDependenciesAsSet consts c ++ getValueDependenciesAsSet consts c

def getKind (c : ConstantInfo) : Kind :=
  if c.isThm then Kind.thm
  else if c.isDef then Kind.defin
  else Kind.other

end ConstantInfo

namespace Environment

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

  -- def getTypeDependencies (c : ConstantInfo) : Array Name :=
  --   c.getTypeDependencies env.userDefinedConstants.1

  -- def getTypeDependenciesAsSet (c : ConstantInfo) : NameSet :=
  --   c.getTypeDependenciesAsSet env.userDefinedConstants.1

  -- def getValueDependencies (c : ConstantInfo) : Array Name :=
  --   c.getValueDependencies env.userDefinedConstants.1

  -- def getValueDependenciesAsSet (c : ConstantInfo) : NameSet :=
  --   c.getValueDependenciesAsSet env.userDefinedConstants.1

  -- def getDependencies (c : ConstantInfo) : Array Name :=
  --   c.getDependencies env.userDefinedConstants.1

  -- def getDependenciesAsSet (c : ConstantInfo) : NameSet :=
  --   c.getDependenciesAsSet env.userDefinedConstants.1

end Environment

end Lean

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
  let userModulesList := userModules.toList

  stream.putStrLn s!"There are {userModulesList.length} user defined modules:"
  for (n, _) in userModules do
    stream.putStrLn s!"{n}"
  stream.putStrLn ""

  -- user defined constants
  let (constMap, constInfoSet) := env.userDefinedConstants
  let constInfoList := constInfoSet.toList

  stream.putStrLn s!"There are {constInfoList.length} user defined constants:"
  for c in constInfoSet do
    let kind := c.getKind
    stream.putStrLn s!"{kind}    {c.name}"
    let type_deps := c.getTypeDependencies constMap
    stream.putStrLn s!"Type dependencies: {type_deps}"
    let value_deps := c.getValueDependencies constMap
    stream.putStrLn s!"Value dependencies: {value_deps}"
    stream.putStrLn ""
  stream.putStrLn ""

  IO.println "Done!"

end AutoBlueprint
