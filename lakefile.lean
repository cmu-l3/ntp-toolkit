import Lake
open Lake DSL

package «lean-training-data» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "a6276f4c6097675b1cf5ebd49b1146b735f38c02"

require leanPremiseSelection from git
  "https://github.com/JOSHCLUNE/lean-premise-selection.git" @ "0076d43fad5969b7087603e6216b2178a90a7512"

require QuerySMT from git
  "https://github.com/JOSHCLUNE/LeanSMTParser.git" @ "eeef5e95a9851736f279ae0680c981f2c527ca60"

require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "v4.16.0"

@[default_target]
lean_lib TrainingData where

lean_lib temp where

lean_lib Examples where

lean_exe training_data where
  root := `scripts.training_data
  supportInterpreter := true

lean_exe full_proof_training_data where
  root := `scripts.full_proof_training_data
  supportInterpreter := true

lean_exe state_comments where
  root := `scripts.state_comments
  supportInterpreter := true

lean_exe premises where
  root := `scripts.premises
  supportInterpreter := true

@[default_target]
lean_exe training_data_with_premises where
  root := `scripts.training_data_with_premises
  supportInterpreter := true

@[default_target]
lean_exe tactic_benchmark where
  root := `scripts.tactic_benchmark
  supportInterpreter := true

@[default_target]
lean_exe add_imports where
  root := `scripts.add_imports
  supportInterpreter := true

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
