import Lake
open Lake DSL

package «lean-training-data» {
  -- add any package configuration options here
}

require htpi from git
  "https://github.com/hanwenzhu/HTPILeanPackage4.7.git" @ "8eeebaec8d7fa17b5fe9d97589839ca2560e3ce2"

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

