import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "zklib"

require Zklib from git
  "https://github.com/Verified-zkEVM/ZKLib" @ "main"

package «Gaussian»

@[default_target]
lean_lib «Gaussian» where
