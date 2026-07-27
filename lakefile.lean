import Lake
open Lake DSL

package «crooks-jarzynski» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.32.0"

require Physlib from git
  "https://github.com/leanprover-community/physlib.git" @
    "dd43e9e65791468c067d8e47222fde69951020ae"

@[default_target]
lean_lib CrooksJarzynski
