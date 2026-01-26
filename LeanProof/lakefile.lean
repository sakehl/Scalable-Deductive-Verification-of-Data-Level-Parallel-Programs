import Lake
open Lake DSL

package «QuantifierLean» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.11.0-rc1"

@[default_target]
lean_lib «QuantifierLean» where
  -- add any library configuration options here
