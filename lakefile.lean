import Lake
open Lake DSL

require base from git
  "https://github.com/AeneasVerif/aeneas"@"main"/"backends/lean"

package «AvlVerification» where
  -- add package configuration options here

@[default_target]
lean_lib «AvlVerification» where
  -- add library configuration options here
