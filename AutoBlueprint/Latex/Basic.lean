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

section

private def tabStr := "    "

private def tab (tabs : Nat) (s : String) : String :=
  (String.intercalate "" $ List.replicate tabs tabStr) ++ s

private def beginLine (env_name : String) : String :=
  "\\begin{" ++ env_name ++ "}\n"

private def endLine (env_name : String) : String :=
  "\\end{" ++ env_name ++ "}\n"

private def labelLine (label? : Option String) : String :=
  match label? with
  | none => ""
  | some label => "\\label{" ++ label ++ "}\n"

private def leanNameLine (lean_name? : Option Name) : String :=
  match lean_name? with
  | none => ""
  | some lean_name => "\\lean{" ++ lean_name.toString ++ "}\n"

private def leanokLine (leanok : Bool) : String :=
  if leanok then "\\leanok\n" else ""

private def usesLine (uses : List String) : String :=
  if uses.isEmpty then ""
  else "\\uses{" ++ (String.intercalate ", " uses) ++ "}\n"

end

def toString (env : LatexEnvironment) : String :=
  beginLine env.env_name ++
  (tab 1 $ labelLine env.label?) ++
  (tab 1 $ leanNameLine env.lean_name?) ++
  (tab 1 $ leanokLine env.leanok) ++
  (tab 1 $ usesLine env.uses) ++
  (tab 1 $ env.content ++ "\n") ++
  endLine env.env_name

instance : ToString LatexEnvironment where
  toString := toString

end LatexEnvironment
