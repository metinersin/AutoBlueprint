import Lake
open Lake DSL

package "AutoBlueprint" where
  -- add package configuration options here

require "leanprover-community" / "mathlib"

lean_lib «AutoBlueprint» where
  -- add library configuration options here

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

@[default_target]
lean_exe "autoblueprint" where
  root := `Main
  supportInterpreter := true
