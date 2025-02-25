import Lake
open Lake DSL

package «lean-training-data» {
  moreLeanArgs := #[
    "-Dlinter.unusedVariables=false",
    -- for supporting more lean versions, some usages in the code are deprecated
    -- a macro TODO is to make the code more future proof (e.g. name change of HashMap)
    "-Dlinter.deprecated=false"
  ]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.15.0"


require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4.git" @ "v4.15.0"


@[default_target]
lean_lib TrainingData where

lean_lib Examples where

lean_exe training_data where
  root := `scripts.training_data

lean_exe full_proof_training_data where
  root := `scripts.full_proof_training_data

lean_exe state_comments where
  root := `scripts.state_comments

lean_exe premises where
  root := `scripts.premises

lean_exe training_data_with_premises where
  root := `scripts.training_data_with_premises

lean_exe all_modules where
  root := `scripts.all_modules

lean_exe declarations where
  root := `scripts.declarations

lean_exe imports where
  root := `scripts.imports
