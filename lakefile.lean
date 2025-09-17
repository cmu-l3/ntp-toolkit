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

require «doc-gen4» from git "https://github.com/leanprover/doc-gen4.git" @ "v4.23.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.23.0"

@[default_target]
lean_lib TrainingData where

lean_lib temp where

lean_lib Examples where

@[default_target]
lean_exe training_data where
  root := `scripts.training_data
  supportInterpreter := true

@[default_target]
lean_exe full_proof_training_data where
  root := `scripts.full_proof_training_data
  supportInterpreter := true

@[default_target]
lean_exe state_comments where
  root := `scripts.state_comments
  supportInterpreter := true

@[default_target]
lean_exe premises where
  root := `scripts.premises
  supportInterpreter := true

@[default_target]
lean_exe training_data_with_premises where
  root := `scripts.training_data_with_premises
  supportInterpreter := true

@[default_target]
lean_exe add_imports where
  root := `scripts.add_imports
  supportInterpreter := true

@[default_target]
lean_exe all_modules where
  root := `scripts.all_modules
  supportInterpreter := true

@[default_target]
lean_exe declarations where
  root := `scripts.declarations
  supportInterpreter := true

@[default_target]
lean_exe imports where
  root := `scripts.imports
  supportInterpreter := true

@[default_target]
lean_exe update_hammer_blacklist where
  root := `scripts.update_hammer_blacklist
  supportInterpreter := true

@[default_target]
lean_exe add_premises where
  root := `scripts.add_premises
  supportInterpreter := true
