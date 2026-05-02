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

@[default_target]
lean_lib Proofs where
  srcDir := "proofs"
  roots := #[
    `p_subset_np.circuit_lifting.Proof,
    `p_versus_np.circuit_lower_bounds.Proof
  ]
