import Lake
open Lake DSL

package «ZKLib»


require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "zklib"

require Zklib from git
  "https://github.com/Verified-zkEVM/ZKLib" @ "main"
