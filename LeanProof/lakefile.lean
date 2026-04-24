import Lake
open Lake DSL

package «QuantifierLean» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`linter.unusedVariables, false⟩
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "5025874dc5f9f8dd1598190e60ef20dda7b42566"

@[default_target]
lean_lib «QuantifierLean» where
  -- add any library configuration options here
