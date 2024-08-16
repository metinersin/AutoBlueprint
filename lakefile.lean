import Lake
open Lake DSL

package "AutoBlueprint" where
  -- add package configuration options here

lean_lib «AutoBlueprint» where
  -- add library configuration options here

@[default_target]
lean_exe "autoblueprint" where
  root := `Main
