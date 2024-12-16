import Lake
open Lake DSL

package «lean-training-data» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d7317655e2826dc1f1de9a0c138db2775c4bb841"

require QuerySMT from git
  "https://github.com/JOSHCLUNE/LeanSMTParser.git" @ "f128e9b4871f5d8da60145fee320f8a7f4abaf73"

require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "v4.13.0"

@[default_target]
lean_lib TrainingData where

lean_lib temp where

lean_lib Examples where

lean_exe training_data where
  root := `scripts.training_data

lean_exe full_proof_training_data where
  root := `scripts.full_proof_training_data

lean_exe state_comments where
  root := `scripts.state_comments

lean_exe premises where
  root := `scripts.premises

@[default_target]
lean_exe training_data_with_premises where
  root := `scripts.training_data_with_premises

@[default_target]
lean_exe tactic_benchmark where
  root := `scripts.tactic_benchmark

@[default_target]
lean_exe add_imports where
  root := `scripts.add_imports

lean_exe all_modules where
  root := `scripts.all_modules

@[default_target]
lean_exe declarations where
  root := `scripts.declarations

@[default_target]
lean_exe imports where
  root := `scripts.imports

@[default_target]
lean_exe update_hammer_blacklist where
  root := `scripts.update_hammer_blacklist
