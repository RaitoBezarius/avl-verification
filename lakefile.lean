import Lake
open Lake DSL

require base from git
  "https://github.com/AeneasVerif/aeneas"@"main"/"backends/lean"

package «Verification» where
  -- add package configuration options here

@[default_target]
lean_lib «Verification» where
  -- add library configuration options here
