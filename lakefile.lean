import Lake
open Lake DSL

require base from git
  "https://github.com/AeneasVerif/aeneas"@"main"/"backends/lean"

package «AvlVerification» where
  -- add package configuration options here

lean_lib «AvlVerification» where
  -- add library configuration options here

@[default_target]
lean_exe «avlverification» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
