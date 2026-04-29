import Lake
open Lake DSL

package «p-vs-np» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib PVsNpLib where
  srcDir := "lib"
  roots := #[`PVsNpLib]
