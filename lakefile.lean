import Lake
open Lake DSL

package «lean-training-data» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "09d33efc68d3ad52db77b731d7253675395a14aa"

require QuerySMT from git
  "https://github.com/JOSHCLUNE/LeanSMTParser.git" @ "main"

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
