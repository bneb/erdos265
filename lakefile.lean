import Lake
open Lake DSL

package "erdos265" where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «Erdos265» where
  srcDir := "src"
  roots := #[`Erdos265]
