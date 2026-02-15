import Lake
open Lake DSL

package «epluspiirrational» where
  -- add package configuration options here

lean_lib «EPlusPiIrrational» where
  -- add library configuration options here

@[default_target]
lean_exe «epluspiirrational» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
