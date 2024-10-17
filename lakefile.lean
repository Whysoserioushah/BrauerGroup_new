import Lake
open Lake DSL

package "BrauerGroup" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
  -- add any additional package configuration options here

require InfiniteGaloisTheory from git "https://github.com/mbkybky/InfiniteGaloisTheory.git"

@[default_target]
lean_lib «BrauerGroup» where
  -- add any library configuration options here

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"
