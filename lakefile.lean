import Lake
open Lake DSL

require "leanprover-community" / "mathlib"

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
lean_lib LustreanTest where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]