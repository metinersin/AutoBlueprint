import Mathlib.Lean.Name

open Lean

structure LatexEnvironment where
  env_name : String
  lean_name? : Option Name
  label? : Option String :=
    match lean_name? with
    | some n => some n.toString
    | none => none
  leanok : Bool
  uses : List String
  content : String
