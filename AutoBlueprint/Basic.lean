import Lean.Elab.Command
import ImportGraph.RequiredModules
import Mathlib.Lean.Name
import Mathlib.Lean.Expr.Basic

import AutoBlueprint.Latex.Basic

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
  human_statement : String
  human_proof : String

namespace Decl

def toLatex (d : Decl) : List LatexEnvironment :=
  let env : LatexEnvironment := {
    env_name := d.kind.toString,
    lean_name? := some d.name,
    leanok := true, -- TODO: do not hard code this
    uses := d.type_deps.toList.map Name.toString,
    content := d.human_statement
  }
  let proofEnv : LatexEnvironment := {
    env_name := "proof",
    lean_name? := none,
    label? := none,
    leanok := true, -- TODO: do not hard code this
    uses := d.value_deps.toList.map Name.toString,
    content := d.human_proof
  }
  [env, proofEnv]

end Decl

end AutoBlueprint

open AutoBlueprint

namespace Lean

namespace Expr

/--
Returns the constants used in the expression `e` that are in the given constant map.
-/
def getUsedConstNamesFrom (consts : ConstMap) (e : Expr) : Array Name :=
  let f (n : Name) (ns : Array Name) : Array Name :=
    if consts.contains n then ns.push n else ns
  e.foldConsts #[] f

/--
Returns the `ConstantInfo`'s of all constants used in the expression `e` that are in the given constant map.
-/
def getUsedConstInfoFrom (consts : ConstMap) (e : Expr) : Array ConstantInfo :=
  let f (n : Name) (arr : Array ConstantInfo) : Array ConstantInfo :=
    match consts.find? n with
    | some c => arr.push c
    | none => arr
  e.foldConsts #[] f

/--
Same as `getUsedConstNamesFrom`, but returns a `NameSet` instead of an `Array Name`.
-/
def getUsedConstNamesFromAsSet (consts : ConstMap) (e : Expr) : NameSet :=
  let f (n : Name) (ns : NameSet) : NameSet :=
    if consts.contains n then ns.insert n else ns
  e.foldConsts {} f

end Expr

def ConstantInfo.quickCmp (c₁ c₂ : ConstantInfo) : Ordering :=
  Name.quickCmp c₁.name c₂.name

/--
Similar to `NameSet`, but for `ConstantInfo` instead of `Name`.
-/
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

/--
Returns the constants used in the type of the constant `c` that are in the given constant map.
-/
def getTypeDependencies (consts : ConstMap) (c : ConstantInfo) : Array Name :=
  c.type.getUsedConstNamesFrom consts

/--
Same as `getTypeDependencies`, but returns a `NameSet` instead of an `Array Name`.
-/
def getTypeDependenciesAsSet (consts : ConstMap) (c : ConstantInfo) : NameSet :=
  c.type.getUsedConstNamesFromAsSet consts

/--
Returns the constants used in the value of the constant `c` that are in the given constant map.
-/
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

/--
Same as `getValueDependencies`, but returns a `NameSet` instead of an `Array Name`.
-/
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

/--
Returns the constants used in the type and value of the constant `c` that are in the given constant map.
-/
def getDependencies (consts : ConstMap) (c : ConstantInfo) : Array Name :=
  getTypeDependencies consts c ++ getValueDependencies consts c

/--
Same as `getDependencies`, but returns a `NameSet` instead of an `Array Name`.
-/
def getDependenciesAsSet (consts : ConstMap) (c : ConstantInfo) : NameSet :=
  getTypeDependenciesAsSet consts c ++ getValueDependenciesAsSet consts c

/--
Returns the kind of the constant `c` i.e, whether it is a definition, theorem, or something else. Do not rely on this function as it may be removed in the future.
-/
def getKind (c : ConstantInfo) : Kind :=
  if c.isThm then Kind.thm
  else if c.isDef then Kind.defin
  else Kind.other

def toDecl (cmap : ConstMap) (c : ConstantInfo) : Decl := {
  name := c.name
  kind := c.getKind
  type_deps := c.getTypeDependenciesAsSet cmap
  value_deps := c.getValueDependenciesAsSet cmap
  human_statement := ""
  human_proof := ""
}

end ConstantInfo

namespace Environment

variable (env : Environment)

/--
Returns a dictionary containing all the modules whose root name is not included in `excludedRootNames`.
-/
def userDefinedModules : SMap Name ModuleIdx := Id.run do
  let names := env.allImportedModuleNames.filter (!excludedRootNames.contains ·.getRoot)
  let mut smap := SMap.empty
  for n in names do
    let idx := (env.getModuleIdx? n).get!
    smap := smap.insert n idx
  return smap

/--
Returns a dictionary containing all the constants whose name is not included in `excludedConstNames` and whose module is in `userDefinedModules`.
-/
def userDefinedConsts : ConstMap × ConstantInfoSet :=
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

def userDefinedDecls : Array Decl :=
  let (constMap, constInfoSet) := env.userDefinedConsts
  sorry

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
  let (constMap, constInfoSet) := env.userDefinedConsts
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

  -- create the latex file
  stream.putStrLn "Creating the latex file...\n\n\n"
  for c in constInfoSet do
    stream.putStr (c.toDecl constMap).toLatex.toString

  IO.println "Done!"

end AutoBlueprint
