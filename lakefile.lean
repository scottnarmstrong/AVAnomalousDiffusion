import Lake
open Lake DSL

package «AVAnomalousDiffusion» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0-rc2"

/-- The Sobolev and ambient-space carriers used by the formalization, vendored from
<https://github.com/scottnarmstrong/CoarseGraining> at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4` (only the modules this project imports). -/
lean_lib «Homogenization» where
  globs := #[.submodules `Homogenization]

/-- The formalization: statements in `AVenhance.Statements`, proofs in `AVenhance.Proofs`,
supporting library in `AVenhance.Infra`. -/
@[default_target]
lean_lib «AVenhance» where
  globs := #[.andSubmodules `AVenhance]
  leanOptions := #[
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]

/-- Mathlib-only statement of the main theorem, with one intentional `sorry`. -/
@[default_target]
lean_lib «Challenge» where
  roots := #[`Challenge]

/-- The Challenge statement proved from the library. -/
@[default_target]
lean_lib «Solution» where
  roots := #[`Solution]
