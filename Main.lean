import AutoBlueprint.Basic
import Lean.Elab.Frontend
import Lean.Util.SearchPath

open System
open Lean Core Environment
open Elab Command Parser
open Lean.ParserDescr


def setPath : IO Unit := do
  searchPathRef.set compile_time_search_path%

def main : IO Unit := do
  setPath

  for tmp in compile_time_search_path% do
    IO.println tmp.toString

  -- let env: Environment ← importModules
  --   (imports := #["AutoBlueprint"].map (λ str => { module := str.toName, runtimeOnly := false }))
  --   (opts := {})
  --   (trustLevel := 1)

  -- let decls := env.constants.toList.map (fun (n, c) => n)
  -- for decl in decls.take 5 do
  --   IO.println decl.toString

  return ()
