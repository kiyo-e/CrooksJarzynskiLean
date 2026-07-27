import Lake
open Lake DSL

package «crooks-jarzynski» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.32.0"

@[default_target]
lean_lib CrooksJarzynski
