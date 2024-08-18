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

-- private def tabStr := "    "

-- private def tab (tabs : Nat) (s : String) : String :=
--   (String.intercalate "" $ List.replicate tabs tabStr) ++ s

scoped instance : HMul Nat String String where
  hMul n s := "".intercalate $ List.replicate n s

private def indent (tabs : Nat) (s : String) (tabStr := "    ") : String := Id.run do
  let endsWithNewline := s.endsWith "\n"
  let mut lines := s.splitOn "\n"
  lines := if endsWithNewline then lines.take (lines.length - 1) else lines
  let mut s := lines |>.map (tabs * tabStr ++ ·)
                     |> "\n".intercalate
  s := if endsWithNewline then s ++ "\n" else s
  s

private def beginLine (env_name : String) (tabs : Nat := 0) : String :=
  indent tabs $ "\\begin{" ++ env_name ++ "}\n"

private def endLine (env_name : String) (tabs : Nat := 0) : String :=
  indent tabs $ "\\end{" ++ env_name ++ "}\n"

private def labelLine (label? : Option String) (tabs : Nat := 0) : String :=
  match label? with
  | none => ""
  | some label => indent tabs $ "\\label{" ++ label ++ "}\n"

private def leanNameLine (lean_name? : Option Name) (tabs : Nat := 0) : String :=
  match lean_name? with
  | none => ""
  | some lean_name => indent tabs $ "\\lean{" ++ lean_name.toString ++ "}\n"

private def leanokLine (leanok : Bool) (tabs : Nat := 0) : String :=
  if leanok then indent tabs $ "\\leanok\n" else ""

private def usesLine (uses : List String) (tabs : Nat := 0) : String :=
  if uses.isEmpty then ""
  else indent tabs $  "\\uses{" ++ (String.intercalate ", " uses) ++ "}\n"

private def contentLine (content : String) (tabs : Nat := 0) : String :=
  indent tabs $ content ++ if content.endsWith "\n" then "" else "\n"

end

def toString (env : LatexEnvironment) : String :=
  beginLine env.env_name ++
    labelLine env.label? (tabs := 1) ++
    leanNameLine env.lean_name? (tabs := 1) ++
    leanokLine env.leanok (tabs := 1) ++
    usesLine env.uses (tabs := 1) ++
    contentLine env.content (tabs := 1) ++
  endLine env.env_name

instance : ToString LatexEnvironment where
  toString := toString

end LatexEnvironment
