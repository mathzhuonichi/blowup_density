import Lake

open Lake DSL

package MNS2Formalization where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

@[default_target]
lean_lib MNS2Formal where
  globs := #[`Formal.+]
