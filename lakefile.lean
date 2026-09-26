import Lake
open Lake DSL

package «Primus» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

@[default_target]
lean_lib «Primus» where
  globs := #[.andSubmodules `Primus]
