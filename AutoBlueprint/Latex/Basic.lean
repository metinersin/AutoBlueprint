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

namespace LatexEnvironment

def toString (env : LatexEnvironment) : String :=
  "\\begin{" ++ env.env_name ++ "}\n" ++

    (match env.label? with
    | none => ""
    | some label => "\\label{" ++ label ++ "}\n") ++

    (match env.lean_name? with
    | none => ""
    | some lean_name => "\\lean{" ++ lean_name.toString ++ "}\n") ++

    (if env.leanok then "\\leanok\n" else "") ++

    "\\uses{" ++ (String.intercalate ", " env.uses) ++ "}\n" ++

    env.content ++ "\n" ++

    "\\end{" ++ env.env_name ++ "}\n"

instance : ToString LatexEnvironment where
  toString := toString

end LatexEnvironment
