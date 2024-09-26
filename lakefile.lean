import Lake
open Lake DSL

package «lean-training-data» {
  -- add any package configuration options here
}

require hep_lean from git
  "https://github.com/hanwenzhu/HepLean-v4.7.git" @ "7448822afced644bd61f0bdcf4dc438f455f9890"

require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4.git" @ "a34d3c1f7b72654c08abe5741d94794db40dbb2e"

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

lean_exe declarations where
  root := `scripts.declarations

lean_exe all_modules where
  root := `scripts.all_modules

