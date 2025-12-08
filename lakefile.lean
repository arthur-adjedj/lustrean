import Lake
open Lake DSL

require "leanprover-community" / "LeanSearchClient" @ git "3591c3f664ac3719c4c86e4483e21e228707bfa2"

package "lustrean" where
  version := v!"0.1.0"

@[default_target]
lean_lib Lustrean where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

lean_lib Misc where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[test_driver]
lean_lib Test where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]
