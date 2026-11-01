import Lake
open Lake DSL

package causalAtlasEngine where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.0-rc1"

@[default_target]
lean_lib Atlas
