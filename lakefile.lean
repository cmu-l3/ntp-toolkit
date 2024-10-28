import Lake
open Lake DSL

package «lean-training-data» {
  -- add any package configuration options here
}

require LeanCamCombi from git
  "https://github.com/YaelDillies/LeanCamCombi.git" @ "ef325f10fab9bfde5184048021dad23c94461e1d"



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
